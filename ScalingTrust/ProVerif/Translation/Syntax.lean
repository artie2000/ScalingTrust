/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Lean

/-!
# The syntax of the ProVerif fragment

Lean's parser, taught the fragment of ProVerif's input language (the manual,
Appendix A) that the translation covers, as syntax categories: terms, processes,
query facts, declarations and the whole model.  `parse` runs it on the text of a
model.

The keywords are non-reserved symbols, so declaring the categories adds only `==>`
and `<>` to Lean's tokens.  Lean's tokenizer reads the text, and `adapt` first
rewrites the two lexical conventions of ProVerif it does not share, keeping every
line in place: a comment `(* … *)`, which may nest, becomes blanks, and the `.`
that ends a declaration after the process `0` is separated from it, since Lean
reads `0.` as one number.
-/

declare_syntax_cat pv_term
declare_syntax_cat pv_proc (behavior := both)
declare_syntax_cat pv_fact (behavior := both)
declare_syntax_cat pv_decl (behavior := both)
declare_syntax_cat pv_model (behavior := both)

namespace ProVerif.Translation

open Lean

/-! ## Terms (Figure A.1)

An identifier is a variable, a free name or a constant, or `fail` in a rewrite rule.
A parenthesised list is a tuple, which the translation rejects unless it has one
element.  The enriched terms of the manual's §4.1.4 that the translation covers are
a restriction, a conditional that compares two terms, a term evaluation binding a
variable, and an event; each extends to the right as far as possible. -/

syntax ident : pv_term
syntax ident "(" pv_term,* ")" : pv_term
syntax "(" pv_term,* ")" : pv_term
syntax "new" ident (" : " ident)? "; " pv_term : pv_term
syntax "if" pv_term (" = " <|> " <> ") pv_term " then " pv_term (" else " pv_term)? : pv_term
syntax "let" ident (" : " ident)? " = " pv_term " in " pv_term (" else " pv_term)? : pv_term
syntax "event" ident ("(" pv_term,* ")")? "; " pv_term : pv_term

/-- `x, y : t`, or `x : t or fail` for a may-fail variable (manual §4.2.1). -/
syntax pv_binders := ident,+ " : " ident (&"or" &"fail")?
/-- `forall x : t, y : u;` -/
syntax pv_forall := &"forall" pv_binders,+ ";"
/-- A rewrite rule or an equation (Figure A.3). -/
syntax pv_rule := (pv_forall)? pv_term " = " pv_term
syntax pv_options := " [" (&"private" <|> &"data" <|> &"typeConverter"),* "]"

/-! ## Processes (Figure A.8)

The precedences are the manual's (§3.1.4): `|` binds most closely, then `if` and
`let`, and a prefix such as `!`, `new`, `in`, `out` and `event` extends to the right
as far as possible, so that `! P | Q` is `!(P | Q)`.  The process `0` is the numeral. -/

syntax num : pv_proc
syntax ident ("(" pv_term,* ")")? : pv_proc
syntax "(" pv_proc ")" : pv_proc
syntax:10 pv_proc:10 " | " pv_proc:11 : pv_proc
syntax "!" pv_proc : pv_proc
syntax (priority := high) "new" ident (" : " ident)? ("; " pv_proc)? : pv_proc
syntax "if" pv_term (" = " <|> " <> ") pv_term " then " pv_proc (" else " pv_proc)? : pv_proc
syntax "in" "(" pv_term ", " ident (" : " ident)? ")" ("; " pv_proc)? : pv_proc
syntax (priority := high) "out" "(" pv_term ", " pv_term ")" ("; " pv_proc)? : pv_proc
syntax "let" ident (" : " ident)? " = " pv_term (" in " pv_proc (" else " pv_proc)?)? : pv_proc
syntax (priority := high) "event" ident ("(" pv_term,* ")")? ("; " pv_proc)? : pv_proc

/-! ## Queries (Figure A.5)

A fact is `attacker(M)` or an event, possibly in parentheses; a query is a fact, or a
correspondence between two facts, or a fact followed by `==> false`. -/

syntax "attacker" "(" pv_term ")" : pv_fact
syntax "event" "(" ident ("(" pv_term,* ")")? ")" : pv_fact
syntax "(" pv_fact ")" : pv_fact
syntax "false" : pv_fact
syntax pv_query := pv_fact (" ==> " pv_fact)?
/-- The variables of a query, `x : t, y : u;`. -/
syntax pv_qvars := pv_binders,+ ";"

/-! ## Declarations (Figure A.2) -/

syntax "type" ident (pv_options)? "." : pv_decl
syntax "set" ident " = " (ident <|> num) "." : pv_decl
syntax "channel" ident,+ "." : pv_decl
syntax "free" ident,+ " : " ident (pv_options)? "." : pv_decl
syntax "const" ident,+ " : " ident (pv_options)? "." : pv_decl
syntax "fun" ident "(" ident,* ")" " : " ident (&"reduc" pv_rule (&"otherwise" pv_rule)*)?
  (pv_options)? "." : pv_decl
syntax "reduc" pv_rule (";" pv_rule)* (pv_options)? "." : pv_decl
syntax "equation" pv_rule (";" pv_rule)* (pv_options)? "." : pv_decl
syntax "event" ident ("(" ident,* ")")? "." : pv_decl
syntax "let" ident ("(" pv_binders,* ")")? " = " pv_proc "." : pv_decl
syntax "letfun" ident ("(" pv_binders,* ")")? " = " pv_term "." : pv_decl
syntax "query" (atomic(pv_qvars))? pv_query (";" pv_query)* (pv_options)? "." : pv_decl

/-- A model: declarations, then `process` and the main process. -/
syntax pv_decl* &"process" pv_proc : pv_model

/-! ## Parsing -/

/-- ProVerif's comments and its `0.` rewritten for Lean's tokenizer. -/
def adapt (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out := ""
  let mut depth := 0
  let mut i := 0
  let isIdChar (c : Char) := c.isAlphanum || c == '_' || c == '\''
  while i < cs.size do
    let c := cs[i]!
    let next := cs[i + 1]?
    if depth > 0 then
      if c == '(' && next == some '*' then
        depth := depth + 1; out := out ++ "  "; i := i + 2
      else if c == '*' && next == some ')' then
        depth := depth - 1; out := out ++ "  "; i := i + 2
      else
        out := out.push (if c == '\n' then c else ' '); i := i + 1
    else if c == '(' && next == some '*' then
      depth := 1; out := out ++ "  "; i := i + 2
    else if c.isDigit && !(i > 0 && isIdChar cs[i - 1]!) then
      let mut j := i
      while j < cs.size && cs[j]!.isDigit do
        out := out.push cs[j]!; j := j + 1
      if cs[j]? == some '.' then out := out.push ' '
      i := j
    else
      out := out.push c; i := i + 1
  return out

/-- Parse the text of a model. -/
def parse (env : Environment) (input : String) (fileName := "<input>") :
    Except String (TSyntax `pv_model) :=
  (⟨·⟩) <$> Parser.runParserCategory env `pv_model (adapt input) fileName

end ProVerif.Translation
