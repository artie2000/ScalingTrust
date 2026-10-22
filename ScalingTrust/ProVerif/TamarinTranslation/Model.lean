/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/

/-!
# Tamarin models

A model as the translation reads it: the signature of a `.spthy` file, its rules, its
restrictions and its lemmas, with the printing of its terms, facts, rules and formulas
for the docstrings of the translation and the renaming of its identifiers.
`Parser.parse` reads a model off the text of a file.
-/

namespace ProVerif.TamarinTranslation

/-- The sort of a variable: a message `x`, a fresh name `~x`, a public name `$x` or a
timepoint `#i`. -/
inductive Kind where
  | msg
  | fresh
  | pub
  | node
  deriving DecidableEq, Repr, Inhabited

/-- A term: a variable with its sort, a public constant `'c'`, or an application; the
pair `<a, b>` is `pair(a, b)` and `a^b` is `^(a, b)`.  A bare identifier is a variable
until the translation finds it declared as a nullary function. -/
inductive Term where
  | var (x : String) (k : Kind)
  | const (c : String)
  | app (f : String) (args : Array Term)
  deriving Inhabited, Repr, BEq

/-- A fact: its name, whether it is persistent, `!F`, and its arguments.  `Fr`, `In`,
`Out`, `K`, `KU` and `KD` are reserved. -/
structure Fact where
  name : String
  persistent : Bool
  args : Array Term
  deriving Inhabited, Repr, BEq

/-- `rule Name: [ premises ] --[ actions ]-> [ conclusions ]`, its `let` bindings
substituted. -/
structure Rule where
  name : String
  premises : Array Fact
  actions : Array Fact
  conclusions : Array Fact
  deriving Repr, Inhabited

/-- A trace formula: the constants `T` and `F`, the atoms `F @ i`, `i < j`, `i = j` and
`t = t'`, the connectives and the quantifiers over sorted variables. -/
inductive Formula where
  | tt
  | ff
  | atom (f : Fact) (i : String)
  | lt (i j : String)
  | teq (i j : String)
  | eq (a b : Term)
  | not (φ : Formula)
  | and (φ ψ : Formula)
  | or (φ ψ : Formula)
  | imp (φ ψ : Formula)
  | iff (φ ψ : Formula)
  | all (vars : Array (String × Kind)) (φ : Formula)
  | ex (vars : Array (String × Kind)) (φ : Formula)
  deriving Inhabited, Repr

/-- `restriction Name: "φ"` -/
structure Restriction where
  name : String
  body : Formula
  deriving Repr

/-- `lemma Name [attrs]: all-traces "φ"` or `exists-trace "φ"`. -/
structure Lemma where
  name : String
  attrs : Array String
  existsTrace : Bool
  body : Formula
  deriving Repr

/-- `f/n`, with `[private]` or not. -/
structure Function where
  name : String
  arity : Nat
  pub : Bool
  deriving Repr

/-- `l = r` -/
structure Equation where
  lhs : Term
  rhs : Term
  deriving Repr, Inhabited

/-- A model: its name, its signature and its rules, restrictions and lemmas, in order. -/
structure Model where
  name : String := ""
  builtins : Array String := #[]
  functions : Array Function := #[]
  equations : Array Equation := #[]
  rules : Array Rule := #[]
  restrictions : Array Restriction := #[]
  lemmas : Array Lemma := #[]
  deriving Repr

/-! ## Printing, for the docstrings of the translation -/

def Kind.prefix : Kind → String
  | .msg => ""
  | .fresh => "~"
  | .pub => "$"
  | .node => "#"

/-- The components of a pair, right-nested: `<a, b, c>` is `pair(a, pair(b, c))`. -/
partial def Term.components : Term → Array Term
  | .app "pair" #[a, b] => #[a] ++ b.components
  | t => #[t]

partial def Term.print : Term → String
  | .var x k => k.prefix ++ x
  | .const c => s!"'{c}'"
  | .app "pair" #[a, b] => s!"<{", ".intercalate ((#[a] ++ b.components).map Term.print).toList}>"
  | .app "^" #[a, b] =>
    let r := match b with
      | .app "^" _ => s!"({b.print})"
      | _ => b.print
    s!"{a.print}^{r}"
  | .app f args =>
    if args.isEmpty then f else s!"{f}({", ".intercalate (args.map Term.print).toList})"

def Fact.print (f : Fact) : String :=
  let bang := if f.persistent then "!" else ""
  s!"{bang}{f.name}({", ".intercalate (f.args.map Term.print).toList})"

def printFacts (fs : Array Fact) : String :=
  if fs.isEmpty then "[]" else s!"[ {", ".intercalate (fs.map Fact.print).toList} ]"

def Rule.print (r : Rule) : String :=
  let arrow := if r.actions.isEmpty then "-->" else s!"--{printFacts r.actions}->"
  s!"rule {r.name}: {printFacts r.premises} {arrow} {printFacts r.conclusions}"

def Equation.print (e : Equation) : String := s!"{e.lhs.print} = {e.rhs.print}"

/-- A formula at the precedence `p` of its context: `<=>` is 0, `==>` 1, `|` 2, `&` 3,
`not` 4; a quantifier is parenthesised as an operand. -/
partial def Formula.printAt (p : Nat) : Formula → String
  | .tt => "T"
  | .ff => "F"
  | .atom f i => s!"{f.print} @ #{i}"
  | .lt i j => s!"#{i} < #{j}"
  | .teq i j => s!"#{i} = #{j}"
  | .eq a b => s!"{a.print} = {b.print}"
  | .not φ => s!"not({φ.printAt 0})"
  | .and φ ψ => paren (p > 3) s!"{φ.printAt 3} & {ψ.printAt 4}"
  | .or φ ψ => paren (p > 2) s!"{φ.printAt 2} | {ψ.printAt 3}"
  | .imp φ ψ => paren (p > 1) s!"{φ.printAt 2} ==> {ψ.printAt 1}"
  | .iff φ ψ => paren (p > 0) s!"{φ.printAt 1} <=> {ψ.printAt 1}"
  | .all vars φ => paren (p > 0) s!"All {printVars vars}. {φ.printAt 0}"
  | .ex vars φ => paren (p > 0) s!"Ex {printVars vars}. {φ.printAt 0}"
where
  paren (b : Bool) (s : String) : String := if b then s!"({s})" else s
  printVars (vars : Array (String × Kind)) : String :=
    " ".intercalate (vars.map fun (x, k) => k.prefix ++ x).toList

def Formula.print (φ : Formula) : String := φ.printAt 0

def Restriction.print (r : Restriction) : String := s!"restriction {r.name}: \"{r.body.print}\""

def Lemma.print (l : Lemma) : String :=
  let attrs := if l.attrs.isEmpty then "" else s!" [{", ".intercalate l.attrs.toList}]"
  let quant := if l.existsTrace then "exists-trace " else ""
  s!"lemma {l.name}{attrs}: {quant}\"{l.body.print}\""

/-! ## Substitution -/

/-- `t` for the variable `x` of sort `k`. -/
partial def Term.subst (x : String) (k : Kind) (t : Term) : Term → Term
  | .var y k' => if y == x && k' == k then t else .var y k'
  | .const c => .const c
  | .app f args => .app f (args.map (Term.subst x k t))

def Fact.subst (x : String) (k : Kind) (t : Term) (f : Fact) : Fact :=
  { f with args := f.args.map (Term.subst x k t) }

/-! ## The identifiers of a model, and renaming them -/

/-- The symbols every model has, which are not identifiers of it. -/
def builtinSymbols : List String := ["pair", "fst", "snd", "^"]

/-- Every identifier of a term: variables and declared symbols. -/
partial def Term.names : Term → Array String
  | .var x _ => #[x]
  | .const _ => #[]
  | .app f args => (if builtinSymbols.contains f then #[] else #[f]) ++ args.flatMap Term.names

def Fact.names (f : Fact) : Array String := #[f.name] ++ f.args.flatMap Term.names

def Rule.names (r : Rule) : Array String :=
  #[r.name] ++ (r.premises ++ r.actions ++ r.conclusions).flatMap Fact.names

partial def Formula.names : Formula → Array String
  | .tt | .ff => #[]
  | .atom f i => f.names ++ #[i]
  | .lt i j | .teq i j => #[i, j]
  | .eq a b => a.names ++ b.names
  | .not φ => φ.names
  | .and φ ψ | .or φ ψ | .imp φ ψ | .iff φ ψ => φ.names ++ ψ.names
  | .all vars φ | .ex vars φ => vars.map (·.1) ++ φ.names

/-- Every identifier of a model. -/
def Model.names (m : Model) : Array String :=
  m.functions.map (·.name) ++ m.equations.flatMap (fun e => e.lhs.names ++ e.rhs.names)
    ++ m.rules.flatMap Rule.names
    ++ m.restrictions.flatMap (fun r => #[r.name] ++ r.body.names)
    ++ m.lemmas.flatMap fun l => #[l.name] ++ l.body.names

partial def Term.rename (σ : String → String) : Term → Term
  | .var x k => .var (σ x) k
  | .const c => .const c
  | .app f args => .app (σ f) (args.map (Term.rename σ))

def Fact.rename (σ : String → String) (f : Fact) : Fact :=
  { f with name := σ f.name, args := f.args.map (Term.rename σ) }

def Rule.rename (σ : String → String) (r : Rule) : Rule where
  name := σ r.name
  premises := r.premises.map (Fact.rename σ)
  actions := r.actions.map (Fact.rename σ)
  conclusions := r.conclusions.map (Fact.rename σ)

partial def Formula.rename (σ : String → String) : Formula → Formula
  | .tt => .tt
  | .ff => .ff
  | .atom f i => .atom (f.rename σ) (σ i)
  | .lt i j => .lt (σ i) (σ j)
  | .teq i j => .teq (σ i) (σ j)
  | .eq a b => .eq (a.rename σ) (b.rename σ)
  | .not φ => .not (φ.rename σ)
  | .and φ ψ => .and (φ.rename σ) (ψ.rename σ)
  | .or φ ψ => .or (φ.rename σ) (ψ.rename σ)
  | .imp φ ψ => .imp (φ.rename σ) (ψ.rename σ)
  | .iff φ ψ => .iff (φ.rename σ) (ψ.rename σ)
  | .all vars φ => .all (vars.map fun (x, k) => (σ x, k)) (φ.rename σ)
  | .ex vars φ => .ex (vars.map fun (x, k) => (σ x, k)) (φ.rename σ)

/-- `m` with `σ` applied to every identifier. -/
def Model.rename (σ : String → String) (m : Model) : Model where
  name := m.name
  builtins := m.builtins
  functions := m.functions.map fun f => { f with name := σ f.name }
  equations := m.equations.map fun e => { lhs := e.lhs.rename σ, rhs := e.rhs.rename σ }
  rules := m.rules.map (Rule.rename σ)
  restrictions := m.restrictions.map fun r => { name := σ r.name, body := r.body.rename σ }
  lemmas := m.lemmas.map fun l => { l with name := σ l.name, body := l.body.rename σ }

end ProVerif.TamarinTranslation
