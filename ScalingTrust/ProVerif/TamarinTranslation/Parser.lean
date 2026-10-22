/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.Translation.Parser
import ScalingTrust.ProVerif.TamarinTranslation.Model

/-!
# Parsing Tamarin models

A lexer and a parser, with `Std.Internal.Parsec`, for the fragment of Tamarin's input
language (the manual's "Syntax description") that the translation covers, over the tokens
and the token parsers of `ProVerif.Translation.Parser`.  `Lexer.lex` reads the text into
tokens, each with the byte offset of its start: identifiers, numerals and symbols, the
longest symbol first, with whitespace, `/* … */` comments, which may nest, and `//`
comments skipped; the quoted formula of a lemma is its tokens between two `"`.  Tamarin's
keywords are identifiers to the lexer and keywords to the parser, which never takes one
for a variable or a symbol of the model.  `parse` reads the tokens into a `Model`; an
error names the line and column of the token it is at.
-/

namespace ProVerif.TamarinTranslation.Parser

open Std.Internal.Parsec
open ProVerif.Translation.Parser (Tok Token Cursor P peek index errorAt unexpected advance sym
  optSym sepBy sepBy1 lineStarts position)

/-- The keywords, which are not identifiers. -/
def keywords : List String :=
  ["theory", "begin", "end", "builtins", "functions", "equations", "rule", "let", "in", "lemma",
   "restriction", "axiom", "All", "Ex", "not", "last", "exists-trace", "all-traces"]

/-! ## The lexer -/

namespace Lexer

open Std.Internal.Parsec.String (ws skipString)
open ProVerif.Translation.Parser.Lexer (offset optString isIdentStart numTok unexpectedChar)

/-- The symbols, the longest first, so that the first to match is the longest. -/
def symbols : List String :=
  ["--[", "]->", "-->", "==>", "<=>", "<<", "(", ")", "[", "]", "<", ">", ",", ":", ".", "=",
   "@", "#", "~", "$", "!", "^", "*", "+", "/", "|", "&", "'", "\"", "-", "%"]

def isIdentRest (c : Char) : Bool := c.isAlphanum || c == '_'

/-- The rest of a comment nested `depth` deep. -/
partial def comment (depth : Nat) : String.Parser Unit := do
  if depth == 0 then return
  if ← optString "/*" then comment (depth + 1)
  else if ← optString "*/" then comment (depth - 1)
  else
    discard (any <|> fail "unterminated comment")
    comment depth

/-- The rest of a line comment. -/
partial def lineComment : String.Parser Unit := do
  match ← peek? with
  | none => return
  | some c =>
    if c == '\n' then return
    discard any
    lineComment

/-- Skip whitespace and comments. -/
partial def trivia : String.Parser Unit := do
  ws
  if ← optString "/*" then
    comment 1
    trivia
  else if ← optString "//" then
    lineComment
    trivia

def identTok : String.Parser Tok := do
  let c ← satisfy isIdentStart
  let rest ← manyChars (satisfy isIdentRest)
  return .ident (c.toString ++ rest)

/-- `exists-trace` and `all-traces`, the two keywords with a hyphen. -/
def traceQuantifier : String.Parser Tok :=
  attempt (skipString "exists-trace" *> pure (.ident "exists-trace")) <|>
    attempt (skipString "all-traces" *> pure (.ident "all-traces"))

def symTok : String.Parser Tok :=
  symbols.foldr (fun s acc => attempt (skipString s *> pure (.sym s)) <|> acc) unexpectedChar

def token : String.Parser Token := do
  trivia
  let offset ← offset
  if ← isEof then return ⟨.eof, offset⟩
  let tok ← attempt traceQuantifier <|> attempt identTok <|> attempt numTok <|> symTok
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

/-! ## Tokens -/

/-- An identifier, which is not a keyword. -/
def ident : P String := do
  match ← peek with
  | .ident s =>
    if keywords.contains s then unexpected "an identifier"
    else
      advance
      return s
  | _ => unexpected "an identifier"

/-- The keyword `k`. -/
def keyword (k : String) : P Unit := do
  if (← peek) == .ident k then advance else unexpected s!"`{k}`"

/-- Whether the keyword `k` is next, consuming it if so. -/
def optKeyword (k : String) : P Bool := do
  if (← peek) == .ident k then
    advance
    return true
  else
    return false

/-- A numeral. -/
def num : P Nat := do
  match ← peek with
  | .num n =>
    advance
    return n
  | _ => unexpected "a numeral"

/-- The identifiers inside a bracket `open … close`, if one is next: the attributes of a
declaration, which are read for their names only. -/
partial def attributes (open_ close : String) : P (Array String) := do
  if ← optSym open_ then inside #[] else return #[]
where
  inside (acc : Array String) : P (Array String) := do
    match ← peek with
    | .sym s =>
      advance
      if s == close then return acc else inside acc
    | .ident s =>
      advance
      inside (acc.push s)
    | .num _ =>
      advance
      inside acc
    | .eof => unexpected s!"`{close}`"

/-! ## Terms and facts -/

/-- A sort suffix, `:fresh`, `:pub`, `:msg` or `:node`, if one is next. -/
def sortSuffix (k : Kind) : P Kind := do
  if (← peek) != .sym ":" then return k
  advance
  match ← peek with
  | .ident "fresh" => advance; return .fresh
  | .ident "pub" => advance; return .pub
  | .ident "msg" => advance; return .msg
  | .ident "node" => advance; return .node
  | .ident "nat" => fail "natural numbers are not translated"
  | _ => unexpected "a sort"

/-- The pair of the terms, right-nested: `<a, b, c>` is `pair(a, pair(b, c))`, and
`<a>` is `a`. -/
def pairOf (ts : Array Term) : Term :=
  ts.pop.foldr (fun t acc => .app "pair" #[t, acc]) ts.back!

mutual

/-- A term: `atom`s joined by `^`, left-associative. -/
partial def term : P Term := do
  let t ← expTail (← atom)
  let next ← peek
  if next == .sym "*" || next == .sym "+" then
    fail "multiplication and multiset union are not translated"
  if next == .ident "XOR" then fail "exclusive or is not translated"
  return t

partial def expTail (l : Term) : P Term := do
  if ← optSym "^" then expTail (.app "^" #[l, ← atom]) else return l

/-- A term that is not an exponentiation: a sorted variable, a public constant, a pair,
a parenthesised term, or an identifier, applied or not. -/
partial def atom : P Term := do
  match ← peek with
  | .sym "~" =>
    advance
    if (← peek) == .sym "'" then fail "a fresh constant is not translated"
    return .var (← ident) .fresh
  | .sym "$" =>
    advance
    return .var (← ident) .pub
  | .sym "#" =>
    advance
    return .var (← ident) .node
  | .sym "%" => fail "natural numbers are not translated"
  | .sym "'" =>
    advance
    let c ← match ← peek with
      | .ident s => advance; pure s
      | .num n => advance; pure (toString n)
      | _ => unexpected "a public constant"
    sym "'"
    return .const c
  | .sym "<" =>
    advance
    let ts ← sepBy1 term ","
    sym ">"
    return pairOf ts
  | .sym "(" =>
    advance
    let t ← term
    sym ")"
    return t
  | .ident s =>
    if keywords.contains s then unexpected "a term"
    advance
    if (← peek) == .sym "(" then
      advance
      let args ← sepBy term "," ")"
      sym ")"
      return .app s args
    else
      return .var s (← sortSuffix .msg)
  | .num _ => fail "numerals are not translated"
  | _ => unexpected "a term"

end

/-- A fact, `F(M, …)` or `!F(M, …)`, its annotations skipped. -/
def fact : P Fact := do
  let persistent ← optSym "!"
  let name ← ident
  sym "("
  let args ← sepBy term "," ")"
  sym ")"
  discard (attributes "[" "]")
  return { name, persistent, args }

/-! ## Rules -/

/-- The bindings of a `let` block, up to `in`. -/
partial def letBindings (acc : Array (String × Kind × Term)) : P (Array (String × Kind × Term)) := do
  if ← optKeyword "in" then return acc
  let i ← index
  let .var x k ← atom | errorAt i "the left-hand side of a `let` binding is a variable"
  sym "="
  letBindings (acc.push (x, k, ← term))

/-- `(modulo …)`, if next. -/
def skipModulo : P Unit := do
  if (← peek) == .sym "(" then discard (attributes "(" ")")

/-- `rule Name: let … in [ … ] --[ … ]-> [ … ]`, the bindings substituted from the last
upwards. -/
def rule : P Rule := do
  keyword "rule"
  skipModulo
  let name ← ident
  discard (attributes "[" "]")
  sym ":"
  let binds ← if ← optKeyword "let" then letBindings #[] else pure #[]
  sym "["
  let premises ← sepBy fact "," "]"
  sym "]"
  let actions ← if ← optSym "-->" then pure #[] else do
    sym "--["
    let a ← sepBy fact "," "]->"
    sym "]->"
    pure a
  sym "["
  let conclusions ← sepBy fact "," "]"
  sym "]"
  if (← peek) == .ident "variants" then fail "rule variants are not translated"
  let subst (fs : Array Fact) : Array Fact :=
    binds.reverse.foldl (fun fs (x, k, t) => fs.map (Fact.subst x k t)) fs
  return { name, premises := subst premises, actions := subst actions,
           conclusions := subst conclusions }

/-! ## Formulas

The connectives bind as in the manual: `<=>` loosest, then `==>`, which is
right-associative, then `|`, then `&`, then `not`; a quantifier extends to the right as far
as possible.  `ns` holds the timepoint variables in scope, so that `i = j` between two of
them is an equality of timepoints and `=` between terms otherwise. -/

/-- A timepoint, `#i` or `i`, with an optional `:node`. -/
def timepoint : P String := do
  discard (optSym "#")
  let i ← ident
  if ← optSym ":" then keyword "node"
  return i

/-- A quantified variable: `~x`, `$x`, `#i`, or `x` with an optional sort. -/
def quantVar : P (String × Kind) := do
  match ← peek with
  | .sym "~" => advance; return (← ident, .fresh)
  | .sym "$" => advance; return (← ident, .pub)
  | .sym "#" => advance; return (← ident, .node)
  | .ident _ =>
    let x ← ident
    return (x, ← sortSuffix .msg)
  | _ => unexpected "a variable"

/-- The variables of a quantifier, up to `.`. -/
partial def quantVars (acc : Array (String × Kind)) : P (Array (String × Kind)) := do
  if ← optSym "." then return acc else quantVars (acc.push (← quantVar))

mutual

partial def formula (ns : List String) : P Formula := do
  let l ← impF ns
  if ← optSym "<=>" then return .iff l (← impF ns) else return l

partial def impF (ns : List String) : P Formula := do
  let l ← orF ns
  if ← optSym "==>" then return .imp l (← impF ns) else return l

partial def orF (ns : List String) : P Formula := do
  orTail ns (← andF ns)

partial def orTail (ns : List String) (l : Formula) : P Formula := do
  if ← optSym "|" then orTail ns (.or l (← andF ns)) else return l

partial def andF (ns : List String) : P Formula := do
  andTail ns (← negF ns)

partial def andTail (ns : List String) (l : Formula) : P Formula := do
  if ← optSym "&" then andTail ns (.and l (← negF ns)) else return l

partial def negF (ns : List String) : P Formula := do
  if ← optKeyword "not" then return .not (← negF ns) else atomF ns

/-- A quantifier, a parenthesised formula, `T`, `F`, or an atom. -/
partial def atomF (ns : List String) : P Formula := do
  match ← peek with
  | .sym "(" =>
    advance
    let φ ← formula ns
    sym ")"
    return φ
  | .ident "All" => quantifier ns false
  | .ident "Ex" => quantifier ns true
  | .ident "last" => fail "`last` is not translated"
  | .ident "T" => constant true
  | .ident "F" => constant false
  | .sym "!" =>
    let f ← fact
    sym "@"
    return .atom f (← timepoint)
  | .sym "#" =>
    advance
    let i ← ident
    timeAtom i
  | _ =>
    let i ← index
    let t ← term
    match ← peek with
    | .sym "@" =>
      advance
      let .app name args := t | errorAt i "a fact before `@`"
      return .atom { name, persistent := false, args } (← timepoint)
    | .sym "<" =>
      let .var j .msg := t | errorAt i "a timepoint before `<`"
      timeAtom j
    | .sym "<<" => fail "the subterm relation is not translated"
    | .sym "=" =>
      advance
      match t with
      | .var j .msg => if ns.contains j then return .teq j (← timepoint) else return .eq t (← term)
      | .var j .node => return .teq j (← timepoint)
      | _ => return .eq t (← term)
    | _ => unexpected "`@`, `<` or `=`"

/-- `i < j` or `i = j` after the timepoint `i`. -/
partial def timeAtom (i : String) : P Formula := do
  if ← optSym "<" then return .lt i (← timepoint)
  else if ← optSym "=" then return .teq i (← timepoint)
  else unexpected "`<` or `=`"

/-- `All vars. φ` or, when `ex`, `Ex vars. φ`. -/
partial def quantifier (ns : List String) (ex : Bool) : P Formula := do
  advance
  let vars ← quantVars #[]
  let nodes := (vars.filter fun v => v.2 == Kind.node).map (·.1)
  let body ← formula (nodes.toList ++ ns)
  return if ex then .ex vars body else .all vars body

/-- `T` or `F`, which may not be followed by arguments. -/
partial def constant (tt : Bool) : P Formula := do
  let i ← index
  advance
  if (← peek) == .sym "(" then errorAt i "a fact named `T` or `F` is not translated"
  return if tt then .tt else .ff

end

/-- A quoted formula. -/
def quoted : P Formula := do
  sym "\""
  let φ ← formula []
  sym "\""
  return φ

/-! ## Declarations and models -/

/-- A builtin's name, `diffie-hellman`, with its hyphens. -/
partial def builtinName (s : String) : P String := do
  if ← optSym "-" then builtinName (s ++ "-" ++ (← ident)) else return s

/-- `f/n`, with its attributes. -/
def function : P Function := do
  let name ← ident
  if (← peek) == .sym "(" then fail "a typed function declaration is not translated"
  sym "/"
  let arity ← num
  let attrs ← attributes "[" "]"
  return { name, arity, pub := !attrs.contains "private" }

def equation : P Equation := do
  let lhs ← term
  sym "="
  return { lhs, rhs := ← term }

/-- The equations after the first, which a trailing comma may end. -/
partial def equationsRest (acc : Array Equation) : P (Array Equation) := do
  if ← optSym "," then
    match ← peek with
    | .ident s => if keywords.contains s then return acc else equationsRest (acc.push (← equation))
    | .eof => return acc
    | _ => equationsRest (acc.push (← equation))
  else
    return acc

/-- A declaration, added to `m`. -/
def decl (m : Model) : P Model := do
  let i ← index
  match ← peek with
  | .ident "builtins" =>
    advance
    sym ":"
    let names ← sepBy1 (do builtinName (← ident)) ","
    return { m with builtins := m.builtins ++ names }
  | .ident "functions" =>
    advance
    sym ":"
    let fs ← sepBy1 function ","
    return { m with functions := m.functions ++ fs }
  | .ident "equations" =>
    advance
    discard (attributes "[" "]")
    sym ":"
    let es ← equationsRest #[← equation]
    return { m with equations := m.equations ++ es }
  | .ident "rule" => return { m with rules := m.rules.push (← rule) }
  | .ident "restriction" => restriction m
  | .ident "axiom" => restriction m
  | .ident "lemma" =>
    advance
    skipModulo
    let name ← ident
    let attrs ← attributes "[" "]"
    sym ":"
    let existsTrace ← if ← optKeyword "exists-trace" then pure true else do
      discard (optKeyword "all-traces")
      pure false
    let body ← quoted
    return { m with lemmas := m.lemmas.push { name, attrs, existsTrace, body } }
  | .ident s => errorAt i s!"`{s}` is not translated"
  | _ => unexpected "a declaration"
where
  /-- `restriction Name: "φ"`, or `axiom`, its older name. -/
  restriction (m : Model) : P Model := do
    advance
    let name ← ident
    discard (attributes "[" "]")
    sym ":"
    return { m with restrictions := m.restrictions.push { name, body := ← quoted } }

partial def decls (m : Model) : P Model := do
  if (← peek) == .ident "end" then return m else decls (← decl m)

/-- A model: `theory Name begin`, declarations, `end`, then the end of the text. -/
def model : P Model := do
  keyword "theory"
  let name ← ident
  keyword "begin"
  let m ← decls { name }
  keyword "end"
  unless (← peek) == .eof do unexpected "the end of the file"
  return m

/-- The model of the text, or an error with its line and column. -/
def parse (text : String) : Except String Model :=
  let starts := lineStarts text
  match Lexer.lex text with
  | .error (off, msg) => .error s!"{position starts off}: {msg}"
  | .ok toks =>
    match model ⟨toks, 0⟩ with
    | .success _ m => .ok m
    | .error it err => .error s!"{position starts it.token.offset}: {err}"

end ProVerif.TamarinTranslation.Parser
