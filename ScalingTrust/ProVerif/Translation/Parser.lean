/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Std.Internal.Parsec
import ScalingTrust.ProVerif.Translation.Model

/-!
# Parsing ProVerif models

A lexer and a parser, with `Std.Internal.Parsec`, for the fragment of ProVerif's input
language (the manual, Appendix A) that the translation covers.  `Lexer.lex` reads the
text into tokens, each with the byte offset of its start: identifiers, numerals and
symbols, the longest symbol first, with whitespace and `(* … *)` comments, which may
nest, skipped.  ProVerif's reserved words are identifiers to the lexer and keywords to
the parser, which never takes one for a variable or a symbol of the model.  `parse`
reads the tokens into a `Model`, with the precedences of processes of the manual's
§3.1.4: `|` is the one infix form, left-associative, and a prefix such as `!`, `new`,
`in`, `out` or `event` extends to the right as far as possible, so that `! P | Q` is
`!(P | Q)`.  An error names the line and column of the token it is at.
-/

namespace ProVerif.Translation.Parser

open Std.Internal.Parsec

/-! ## Tokens -/

/-- A token: an identifier, which may be a reserved word, a numeral, a symbol, or the end
of the text. -/
inductive Tok where
  | ident (s : String)
  | num (n : Nat)
  | sym (s : String)
  | eof
  deriving DecidableEq, Inhabited

def Tok.print : Tok → String
  | .ident s | .sym s => s!"`{s}`"
  | .num n => s!"`{n}`"
  | .eof => "the end of the file"

/-- A token with the byte offset of its start. -/
structure Token where
  tok : Tok
  offset : Nat
  deriving DecidableEq, Inhabited

/-- ProVerif's reserved words, which are not identifiers (the manual's list in §3.1). -/
def keywords : List String :=
  ["among", "axiom", "channel", "choice", "clauses", "const", "def", "diff", "do", "elimtrue",
   "else", "equation", "equivalence", "event", "expand", "fail", "for", "forall", "foreach",
   "free", "fun", "get", "if", "implementation", "in", "inj-event", "insert", "lemma", "let",
   "letfun", "letproba", "new", "noninterf", "noselect", "not", "nounif", "or", "otherwise",
   "out", "param", "phase", "pred", "proba", "process", "proof", "public_vars", "putbegin",
   "query", "reduc", "restriction", "secret", "select", "set", "suchthat", "sync", "table",
   "then", "type", "weaksecret", "yield"]

/-! ## The lexer -/

namespace Lexer

open Std.Internal.Parsec.String (ws digits skipString)

/-- The symbols, the longest first, so that the first to match is the longest. -/
def symbols : List String :=
  ["==>", "<-R", "<->", "<=>", "<-", "<>", "<=", ">=", "&&", "||", "(", ")", "[", "]", ",", ";",
   ":", "=", ".", "|", "!", "<", ">", "+", "-", "*"]

def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'

def isIdentRest (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

/-- The byte offset of the current position. -/
def offset : String.Parser Nat := fun it => .success it it.2.offset.byteIdx

/-- Whether `s` is next, consuming it if so. -/
def optString (s : String) : String.Parser Bool :=
  attempt (skipString s *> pure true) <|> pure false

/-- The rest of a comment nested `depth` deep. -/
partial def comment (depth : Nat) : String.Parser Unit := do
  if depth == 0 then return
  if ← optString "(*" then comment (depth + 1)
  else if ← optString "*)" then comment (depth - 1)
  else
    discard (any <|> fail "unterminated comment")
    comment depth

/-- Skip whitespace and comments. -/
partial def trivia : String.Parser Unit := do
  ws
  if ← optString "(*" then
    comment 1
    trivia

def identTok : String.Parser Tok := do
  let c ← satisfy isIdentStart
  let rest ← manyChars (satisfy isIdentRest)
  return .ident (c.toString ++ rest)

def numTok : String.Parser Tok := .num <$> digits

def unexpectedChar : String.Parser Tok := do
  match ← peek? with
  | some c => fail s!"unexpected character `{c}`"
  | none => fail "unexpected end of input"

def symTok : String.Parser Tok :=
  symbols.foldr (fun s acc => attempt (skipString s *> pure (.sym s)) <|> acc) unexpectedChar

def token : String.Parser Token := do
  trivia
  let offset ← offset
  if ← isEof then return ⟨.eof, offset⟩
  let tok ← attempt identTok <|> attempt numTok <|> symTok
  return ⟨tok, offset⟩

/-- The tokens of the text, ending with `eof`. -/
partial def tokens (acc : Array Token) : String.Parser (Array Token) := do
  let t ← token
  if t.tok == .eof then return acc.push t else tokens (acc.push t)

/-- The tokens of `s`, or the offset and the message of a lexical error. -/
def lex (s : String) : Except (Nat × String) (Array Token) :=
  match tokens #[] ⟨s, s.startPos⟩ with
  | .success _ toks => .ok toks
  | .error it err => .error (it.2.offset.byteIdx, toString err)

end Lexer

/-! ## The parser's input -/

/-- The tokens and the index of the current one.  Past the end, the current token is the
final `eof`. -/
structure Cursor where
  toks : Array Token
  i : Nat

/-- The token at `it`. -/
def Cursor.token (it : Cursor) : Token := it.toks[it.i]?.getD default

instance : Input Cursor Token Nat where
  pos it := it.i
  next it := { it with i := it.i + 1 }
  curr it := it.token
  hasNext it := it.i < it.toks.size
  next' it _ := { it with i := it.i + 1 }
  curr' it _ := it.token

/-- A parser over the tokens. -/
abbrev P (α : Type) := Std.Internal.Parsec Cursor α

/-- The current token. -/
def peek : P Tok := fun it => .success it it.token.tok

/-- The index of the current token. -/
def index : P Nat := fun it => .success it it.i

/-- Fail at the token `i`. -/
def errorAt {α : Type} (i : Nat) (msg : String) : P α := fun it => .error { it with i } (.other msg)

/-- Fail at the current token, naming it. -/
def unexpected {α : Type} (expected : String) : P α := do
  fail s!"expected {expected}, found {(← peek).print}"

def advance : P Unit := skip

/-- The symbol `s`. -/
def sym (s : String) : P Unit := do
  if (← peek) == .sym s then advance else unexpected s!"`{s}`"

/-- The reserved word `k`. -/
def keyword (k : String) : P Unit := do
  if (← peek) == .ident k then advance else unexpected s!"`{k}`"

/-- Whether the symbol `s` is next, consuming it if so. -/
def optSym (s : String) : P Bool := do
  if (← peek) == .sym s then
    advance
    return true
  else
    return false

/-- Whether the reserved word `k` is next, consuming it if so. -/
def optKeyword (k : String) : P Bool := do
  if (← peek) == .ident k then
    advance
    return true
  else
    return false

/-- An identifier, which is not a reserved word. -/
def ident : P String := do
  match ← peek with
  | .ident s =>
    if keywords.contains s then unexpected "an identifier"
    else
      advance
      return s
  | _ => unexpected "an identifier"

/-- A type, which is any identifier: the built-in type `channel` is a reserved word. -/
def typeName : P Unit := do
  match ← peek with
  | .ident _ => advance
  | _ => unexpected "a type"

/-- An optional type, `: t`. -/
def skipType : P Unit := do
  if ← optSym ":" then typeName

partial def sepByCore {α : Type} (p : P α) (s : String) (acc : Array α) : P (Array α) := do
  if ← optSym s then sepByCore p s (acc.push (← p)) else return acc

/-- `p`, separated by the symbol `s`, at least once. -/
def sepBy1 {α : Type} (p : P α) (s : String) : P (Array α) := do
  sepByCore p s #[← p]

/-- `p`, separated by the symbol `s`, possibly none before the closing symbol `close`. -/
def sepBy {α : Type} (p : P α) (s close : String) : P (Array α) := do
  if (← peek) == .sym close then return #[] else sepBy1 p s

/-- An `else` branch. -/
def optElse {α : Type} (p : P α) : P (Option α) := do
  if ← optKeyword "else" then some <$> p else return none

/-! ## Terms (Figure A.1) and patterns

An identifier is a variable, a free name or a constant; `fail` occurs in rewrite rules.
A parenthesised list is a tuple, `(M)` being `M`.  The infix operators bind as in the
manual: `||` loosest, then `&&`, then `=` and `<>`, which do not chain.  The enriched terms
(manual §4.1.4) extend to the right as far as possible. -/

mutual

/-- A term: `atom`s joined by `||`. -/
partial def term : P Term := do
  let l ← andTerm
  if ← optSym "||" then return .app "||" #[l, ← term] else return l

partial def andTerm : P Term := do
  let l ← cmpTerm
  if ← optSym "&&" then return .app "&&" #[l, ← andTerm] else return l

partial def cmpTerm : P Term := do
  let l ← atom
  if ← optSym "=" then return .app "=" #[l, ← atom]
  else if ← optSym "<>" then return .app "<>" #[l, ← atom]
  else return l

/-- A term that is not an infix application. -/
partial def atom : P Term := do
  match ← peek with
  | .ident "new" =>
    advance
    let x ← ident
    skipType
    sym ";"
    return .new x (← term)
  | .ident "if" =>
    advance
    let c ← term
    keyword "then"
    let n ← term
    return .ite c n (← optElse term)
  | .ident "let" =>
    advance
    let p ← pattern
    sym "="
    let d ← term
    keyword "in"
    let n ← term
    return .let p d n (← optElse term)
  | .ident "event" =>
    advance
    let e ← ident
    let args ← optArgs
    sym ";"
    return .event e args (← term)
  | .ident "fail" =>
    advance
    return .fail
  | .ident "not" =>
    advance
    sym "("
    let m ← term
    sym ")"
    return .app "not" #[m]
  | .ident s =>
    if keywords.contains s then unexpected "a term"
    else
      advance
      if (← peek) == .sym "(" then return .app s (← args) else return .ident s
  | .sym "(" =>
    advance
    let ts ← sepBy term "," ")"
    sym ")"
    return if ts.size == 1 then ts[0]! else .tuple ts
  | .num _ => fail "numerals are not translated"
  | _ => unexpected "a term"

/-- `(M, …)` -/
partial def args : P (Array Term) := do
  sym "("
  let ts ← sepBy term "," ")"
  sym ")"
  return ts

/-- `(M, …)`, or nothing. -/
partial def optArgs : P (Array Term) := do
  if (← peek) == .sym "(" then args else return #[]

/-- A pattern: a variable with an optional type, `=M`, a tuple of patterns, `(p)` being
`p`, or a constructor applied to patterns. -/
partial def pattern : P Pat := do
  match ← peek with
  | .sym "(" =>
    advance
    let ps ← sepBy pattern "," ")"
    sym ")"
    return if ps.size == 1 then ps[0]! else .tuple ps
  | .sym "=" =>
    advance
    return .eq (← atom)
  | .ident s =>
    if keywords.contains s then unexpected "a pattern"
    else
      advance
      if (← peek) == .sym "(" then
        advance
        let ps ← sepBy pattern "," ")"
        sym ")"
        return .app s ps
      else
        skipType
        return .var s
  | _ => unexpected "a pattern"

end

/-! ## Processes (Figure A.8) -/

mutual

/-- A process: parallel compositions of simple processes, left-associative. -/
partial def proc : P Proc := do
  parallel (← simple)

partial def parallel (p : Proc) : P Proc := do
  if ← optSym "|" then parallel (.par p (← simple)) else return p

/-- A process that is not a parallel composition.  A prefix extends to the right as far as
possible; an absent continuation, `else` or `in` is `0`. -/
partial def simple : P Proc := do
  match ← peek with
  | .num 0 =>
    advance
    return .nil
  | .sym "(" =>
    advance
    let p ← proc
    sym ")"
    return p
  | .sym "!" =>
    advance
    return .repl (← proc)
  | .ident "new" =>
    advance
    let x ← ident
    skipType
    return .new x (← continuation)
  | .ident "if" =>
    advance
    let c ← term
    keyword "then"
    let p ← proc
    return .ite c p (← elseProc)
  | .ident "in" =>
    advance
    sym "("
    let c ← term
    sym ","
    let x ← pattern
    sym ")"
    return .inp c x (← continuation)
  | .ident "out" =>
    advance
    sym "("
    let c ← term
    sym ","
    let m ← term
    sym ")"
    return .out c m (← continuation)
  | .ident "let" =>
    advance
    let x ← pattern
    sym "="
    let d ← term
    if ← optKeyword "in" then
      let p ← proc
      return .let x d p (← elseProc)
    else
      return .let x d .nil .nil
  | .ident "event" =>
    advance
    let e ← ident
    let args ← optArgs
    return .event e args (← continuation)
  | .ident s =>
    if keywords.contains s then unexpected "a process"
    else
      advance
      return .call s (← optArgs)
  | _ => unexpected "a process"

/-- The process after `;`, `0` when there is none. -/
partial def continuation : P Proc := do
  if ← optSym ";" then proc else return .nil

partial def elseProc : P Proc := do
  if ← optKeyword "else" then proc else return .nil

end

/-! ## Declarations (Figure A.2) and queries (Figure A.5) -/

/-- `[private, data, …]`, or nothing. -/
def options : P (Array String) := do
  if ← optSym "[" then
    let ws ← sepBy option "," "]"
    sym "]"
    return ws
  else
    return #[]
where
  option : P String := do
    match ← peek with
    | .ident s =>
      if ["private", "data", "typeConverter"].contains s then
        advance
        return s
      else
        unexpected "an option"
    | _ => unexpected "an option"

/-- `x, y : t`, or `x : t or fail` for may-fail variables (manual §4.2.1). -/
def binders : P (Array (String × Bool)) := do
  let xs ← sepBy1 ident ","
  sym ":"
  typeName
  let mayFail ← if ← optKeyword "or" then do keyword "fail"; pure true else pure false
  return xs.map (·, mayFail)

/-- `forall x : t, y : u;`, or nothing. -/
def forallVars : P (Array (String × Bool)) := do
  if ← optKeyword "forall" then
    let bs ← sepBy1 binders ","
    sym ";"
    return bs.flatten
  else
    return #[]

/-- A rewrite rule, with the name of the destructor it is for. -/
def rule : P (String × Rule) := do
  let i ← index
  let vars ← forallVars
  let l ← atom
  sym "="
  let r ← term
  let .app g lhs := l | errorAt i "the left-hand side of a rewrite rule applies the destructor"
  return (g, { vars, lhs, rhs := r })

/-- The rules after `otherwise`. -/
partial def otherwise (acc : Array (String × Rule)) : P (Array (String × Rule)) := do
  if ← optKeyword "otherwise" then otherwise (acc.push (← rule)) else return acc

def equation : P Equation := do
  let i ← index
  let vars ← forallVars
  if let some (x, _) := vars.find? (·.2) then
    errorAt i s!"may-fail variable `{x}` in an equation"
  let l ← atom
  sym "="
  return { vars := vars.map (·.1), lhs := l, rhs := ← term }

/-- The rules of one destructor, declared at the token `i`: all for the same symbol, all of
its arity. -/
def dtor (i : Nat) (pub : Bool) (rules : Array (String × Rule)) : P Dtor := do
  let (name, first) := rules[0]!
  let arity := first.lhs.size
  for (g, r) in rules do
    unless g == name do errorAt i s!"a rule for `{g}` among the rules of `{name}`"
    unless r.lhs.size == arity do errorAt i s!"the rules of `{name}` differ in arity"
  return { name, arity, pub, rules := rules.map (·.2) }

/-- `(x : t, …)`, the parameters of a macro, which may not fail; or nothing. -/
def params (what : String) : P (Array String) := do
  if (← peek) != .sym "(" then return #[]
  let i ← index
  advance
  let bs ← sepBy binders "," ")"
  sym ")"
  let ps := bs.flatten
  if let some (x, _) := ps.find? (·.2) then
    errorAt i s!"may-fail parameter `{x}` of {what}"
  return ps.map (·.1)

mutual

/-- `attacker(M)` or an event, possibly in parentheses. -/
partial def fact : P Fact := do
  match ← peek with
  | .ident "attacker" =>
    advance
    sym "("
    let m ← term
    sym ")"
    return .attacker m
  | .ident "event" =>
    advance
    sym "("
    let e ← ident
    let args ← optArgs
    sym ")"
    return .event e args
  | .sym "(" =>
    advance
    let f ← fact
    sym ")"
    return f
  | .ident "false" => fail "`false` is not a fact"
  | _ => unexpected "a fact"

/-- The conclusion of a correspondence: a fact, or `false`, which makes the query ask that
its premise never holds. -/
partial def conclusion : P (Option Fact) := do
  match ← peek with
  | .ident "false" =>
    advance
    return none
  | .sym "(" =>
    advance
    let c ← conclusion
    sym ")"
    return c
  | _ => some <$> fact

end

/-- `F`, or `F ==> H`. -/
def query (vars : Array String) : P Query := do
  let premise ← fact
  let concl ← if ← optSym "==>" then conclusion else pure none
  return { vars, premise, conclusion := concl }

/-- `x : t, y : u;`, the variables of a query. -/
def qvars : P (Array String) := do
  let bs ← sepBy1 binders ","
  sym ";"
  return bs.flatten.map (·.1)

/-- A declaration, added to `m`. -/
def decl (m : Model) : P Model := do
  let i ← index
  match ← peek with
  | .ident "type" =>
    advance
    discard ident
    discard options
    sym "."
    return m
  | .ident "set" =>
    advance
    discard ident
    sym "="
    match ← peek with
    | .ident _ | .num _ => advance
    | _ => unexpected "a value"
    sym "."
    return m
  | .ident "channel" =>
    advance
    let xs ← sepBy1 ident ","
    sym "."
    return { m with frees := m.frees ++ xs.map (·, true) }
  | .ident "free" =>
    advance
    let xs ← sepBy1 ident ","
    sym ":"
    typeName
    let opts ← options
    sym "."
    return { m with frees := m.frees ++ xs.map (·, !opts.contains "private") }
  | .ident "const" =>
    advance
    let xs ← sepBy1 ident ","
    sym ":"
    typeName
    let opts ← options
    sym "."
    let cs := xs.map fun name =>
      { name, arity := 0, pub := !opts.contains "private",
        converter := opts.contains "typeConverter", data := opts.contains "data" : Ctor }
    return { m with ctors := m.ctors ++ cs }
  | .ident "fun" =>
    advance
    let name ← ident
    sym "("
    let ts ← sepBy typeName "," ")"
    sym ")"
    sym ":"
    typeName
    let rules ← if ← optKeyword "reduc" then do otherwise #[← rule] else pure #[]
    let opts ← options
    sym "."
    let pub := !opts.contains "private"
    if rules.isEmpty then
      let c : Ctor :=
        { name, arity := ts.size, pub, converter := opts.contains "typeConverter",
          data := opts.contains "data" }
      return { m with ctors := m.ctors.push c }
    let d ← dtor i pub rules
    unless d.name == name do errorAt i s!"the rules of `{name}` are for `{d.name}`"
    unless d.arity == ts.size do errorAt i s!"the rules of `{name}` do not have its arity"
    return { m with dtors := m.dtors.push d }
  | .ident "reduc" =>
    advance
    let rules ← sepBy1 rule ";"
    let opts ← options
    sym "."
    return { m with dtors := m.dtors.push (← dtor i (!opts.contains "private") rules) }
  | .ident "equation" =>
    advance
    let es ← sepBy1 equation ";"
    discard options
    sym "."
    return { m with equations := m.equations ++ es }
  | .ident "event" =>
    advance
    let e ← ident
    let n ← if ← optSym "(" then do
        let ts ← sepBy typeName "," ")"
        sym ")"
        pure ts.size
      else pure 0
    sym "."
    return { m with events := m.events.push (e, n) }
  | .ident "let" =>
    advance
    let name ← ident
    let params ← params "a process macro"
    sym "="
    let body ← proc
    sym "."
    return { m with macros := m.macros.push { name, params, body } }
  | .ident "letfun" =>
    advance
    let name ← ident
    let params ← params "a function macro"
    sym "="
    let body ← term
    sym "."
    return { m with fns := m.fns.push { name, params, body } }
  | .ident "query" =>
    advance
    let vars ← attempt qvars <|> pure #[]
    let qs ← sepBy1 (query vars) ";"
    discard options
    sym "."
    return { m with queries := m.queries ++ qs }
  | _ => unexpected "a declaration"

/-! ## Models -/

partial def decls (m : Model) : P Model := do
  if (← peek) == .ident "process" then return m else decls (← decl m)

/-- A model: declarations, then `process` and the main process, then the end of the text. -/
def model : P Model := do
  let m ← decls {}
  keyword "process"
  let main ← proc
  unless (← peek) == .eof do unexpected "the end of the file"
  return { m with main }

/-- The byte offsets at which the lines of `s` start. -/
def lineStarts (s : String) : Array Nat := Id.run do
  let mut starts := #[0]
  let mut off := 0
  for c in s.toList do
    off := off + c.utf8Size
    if c == '\n' then starts := starts.push off
  return starts

/-- `line:column` of the byte offset `off`, the line from 1 and the column from 0. -/
def position (starts : Array Nat) (off : Nat) : String :=
  let line := (starts.findIdx? (· > off)).getD starts.size
  s!"{line}:{off - starts[line - 1]!}"

/-- The model of the text, or an error with its line and column. -/
def parse (text : String) : Except String Model :=
  let starts := lineStarts text
  match Lexer.lex text with
  | .error (off, msg) => .error s!"{position starts off}: {msg}"
  | .ok toks =>
    match model ⟨toks, 0⟩ with
    | .success _ m => .ok m
    | .error it err => .error s!"{position starts it.token.offset}: {err}"

end ProVerif.Translation.Parser
