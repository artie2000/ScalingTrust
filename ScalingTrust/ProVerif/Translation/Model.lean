/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/

/-!
# ProVerif models

A model as the translation reads it, types erased: the free names, constructors,
events, equations and destructors a ProVerif file declares, its function and
process macros, its queries and its main process, with the printing of its terms
and queries for the docstrings of the translation and the renaming of its
identifiers.  `Parser.parse` reads a model off the text of a file.
-/

namespace ProVerif.Translation

mutual

/-- A term: an identifier, which is a variable, a free name, a constant or `true` or
`false`; an application; a tuple `(M₁, …, Mₙ)`, never of one term; `fail`, in rewrite
rules; or one of the enriched terms of the manual's §4.1.4, which evaluate with effects: a
restriction, a conditional on a boolean term, a term evaluation with a pattern and an
event.  An absent `else` is `fail` (Appendix B).  The comparisons `M = N` and `M <> N`
and the connectives `M && N`, `M || N` and `not(M)` are applications of `"="`, `"<>"`,
`"&&"`, `"||"` and `"not"`, which are not identifiers. -/
inductive Term where
  | ident (x : String)
  | app (f : String) (args : Array Term)
  | tuple (args : Array Term)
  | fail
  | new (x : String) (M : Term)
  | ite (c : Term) (N : Term) (N' : Option Term)
  | «let» (p : Pat) (d : Term) (N : Term) (N' : Option Term)
  | event (e : String) (args : Array Term) (M : Term)
  deriving Inhabited, Repr

/-- A pattern of `in` and `let` (manual §4.1.3): a variable, an equality test `=M`, a
tuple of patterns, or a data constructor applied to patterns. -/
inductive Pat where
  | var (x : String)
  | eq (M : Term)
  | tuple (ps : Array Pat)
  | app (f : String) (ps : Array Pat)
  deriving Inhabited, Repr

end

/-- `fun f(t₁, …, tₙ) : t` or `const c : t`, with its options. -/
structure Ctor where
  name : String
  arity : Nat
  pub : Bool
  /-- `[typeConverter]`: the identity, as under ProVerif's default `ignoreTypes = true`. -/
  converter : Bool
  /-- `[data]`: patterns may match on it, and its projections are destructors, public when
  it is (manual §4.1.2). -/
  data : Bool
  deriving Repr

/-- A rewrite rule `forall x₁ : t₁ [or fail], …; g(p₁, …, pₙ) = r`: its variables,
each marked if it may fail, its patterns and its right-hand side. -/
structure Rule where
  vars : Array (String × Bool)
  lhs : Array Term
  rhs : Term
  deriving Inhabited, Repr

/-- A destructor: `reduc` with rules separated by `;`, or `fun … reduc` with rules
separated by `otherwise`.  Either way the first rule that applies decides
(manual §4.2.1). -/
structure Dtor where
  name : String
  arity : Nat
  pub : Bool
  rules : Array Rule
  deriving Repr

/-- `equation forall x₁ : t₁, …; l = r` -/
structure Equation where
  vars : Array String
  lhs : Term
  rhs : Term
  deriving Repr

/-- A process of the fragment.  An `if` tests a boolean term; `in` and `let` bind a
pattern; an absent `else` and an absent `in` are `0`. -/
inductive Proc where
  | nil
  | call (p : String) (args : Array Term)
  | par (P Q : Proc)
  | repl (P : Proc)
  | new (x : String) (P : Proc)
  | ite (c : Term) (P Q : Proc)
  | inp (c : Term) (p : Pat) (P : Proc)
  | out (c m : Term) (P : Proc)
  | «let» (p : Pat) (d : Term) (P Q : Proc)
  | event (e : String) (args : Array Term) (P : Proc)
  deriving Inhabited, Repr

/-- A fact of a query. -/
inductive Fact where
  | attacker (m : Term)
  | event (e : String) (args : Array Term)
  deriving Repr

/-- `query x₁ : t₁, …; F ==> H`, or `query x₁ : t₁, …; F`, which asks that `F` never
holds, as does `F ==> false`. -/
structure Query where
  vars : Array String
  premise : Fact
  /-- `H`, or `none` when the query asks that the premise never holds. -/
  conclusion : Option Fact
  deriving Repr

/-- `let p(x₁ : t₁, …) = P.` -/
structure Macro where
  name : String
  params : Array String
  body : Proc
  deriving Repr

/-- `letfun f(x₁ : t₁, …) = M.`, a function macro (manual §4.2.3). -/
structure Fn where
  name : String
  params : Array String
  body : Term
  deriving Repr

/-- A model: its declarations, in order, and its main process. -/
structure Model where
  /-- The free names, each marked if public. -/
  frees : Array (String × Bool) := #[]
  ctors : Array Ctor := #[]
  /-- The events, with their arities. -/
  events : Array (String × Nat) := #[]
  equations : Array Equation := #[]
  dtors : Array Dtor := #[]
  /-- The function macros, in order: each may call only the earlier ones. -/
  fns : Array Fn := #[]
  macros : Array Macro := #[]
  queries : Array Query := #[]
  main : Proc := .nil
  deriving Repr

/-! ## Printing, for the docstrings of the translation -/

/-- An application, `f(a, b)`, or `f` when there are no arguments. -/
def printApp (f : String) (args : Array String) : String :=
  if args.isEmpty then f else s!"{f}({", ".intercalate args.toList})"

/-- Whether a term is an enriched one, printed in parentheses as an argument. -/
def Term.enriched : Term → Bool
  | .new .. | .ite .. | .let .. | .event .. => true
  | _ => false

/-- Whether a term is an infix comparison or connective, printed in parentheses as an
argument. -/
def Term.infix : Term → Bool
  | .app "=" _ | .app "<>" _ | .app "&&" _ | .app "||" _ => true
  | _ => false

mutual

partial def Term.print : Term → String
  | .ident x => x
  | .app "=" #[l, r] => s!"{l.arg} = {r.arg}"
  | .app "<>" #[l, r] => s!"{l.arg} <> {r.arg}"
  | .app "&&" #[l, r] => s!"{l.arg} && {r.arg}"
  | .app "||" #[l, r] => s!"{l.arg} || {r.arg}"
  | .app f args => s!"{f}({", ".intercalate (args.map Term.arg).toList})"
  | .tuple args => s!"({", ".intercalate (args.map Term.print).toList})"
  | .fail => "fail"
  | .new x M => s!"new {x}; {M.print}"
  | .ite c N N' => s!"if {c.print} then {N.print}{Term.orElse N'}"
  | .let p d N N' => s!"let {p.print} = {d.print} in {N.print}{Term.orElse N'}"
  | .event e args M => s!"event {printApp e (args.map Term.arg)}; {M.print}"

/-- A term as an argument or an operand. -/
partial def Term.arg (t : Term) : String :=
  if t.enriched || t.infix then s!"({t.print})" else t.print

partial def Term.orElse : Option Term → String
  | none => ""
  | some N' => s!" else {N'.print}"

partial def Pat.print : Pat → String
  | .var x => x
  | .eq M => s!"={M.arg}"
  | .tuple ps => s!"({", ".intercalate (ps.map Pat.print).toList})"
  | .app f ps => printApp f (ps.map Pat.print)

end

def Fn.print (f : Fn) : String :=
  s!"{printApp f.name f.params} = {f.body.print}"

def Fact.print : Fact → String
  | .attacker m => s!"attacker({m.print})"
  | .event e args => s!"event({printApp e (args.map Term.print)})"

def Query.print (q : Query) : String :=
  let vars := if q.vars.isEmpty then "" else s!"{", ".intercalate q.vars.toList}; "
  match q.conclusion with
  | none => s!"query {vars}{q.premise.print}"
  | some h => s!"query {vars}{q.premise.print} ==> {h.print}"

/-- A rule of the destructor `g`, as `g(p₁, …, pₙ) → r`. -/
def Rule.print (g : String) (r : Rule) : String :=
  s!"{(Term.app g r.lhs).print} → {r.rhs.print}"

/-! ## The identifiers of a model, and renaming them -/

mutual

/-- Every identifier of a term: symbols, operators and variables, bound or free. -/
partial def Term.names : Term → Array String
  | .ident x => #[x]
  | .app f args => #[f] ++ args.flatMap Term.names
  | .tuple args => args.flatMap Term.names
  | .fail => #[]
  | .new x M => #[x] ++ M.names
  | .ite c N N' => c.names ++ N.names ++ (N'.map Term.names).getD #[]
  | .let p d N N' => p.names ++ d.names ++ N.names ++ (N'.map Term.names).getD #[]
  | .event e args M => #[e] ++ args.flatMap Term.names ++ M.names

partial def Pat.names : Pat → Array String
  | .var x => #[x]
  | .eq M => M.names
  | .tuple ps => ps.flatMap Pat.names
  | .app f ps => #[f] ++ ps.flatMap Pat.names

end

/-- The variables a pattern binds, in order. -/
partial def Pat.vars : Pat → Array String
  | .var x => #[x]
  | .eq _ => #[]
  | .tuple ps | .app _ ps => ps.flatMap vars

/-- The terms of the equality tests of a pattern. -/
partial def Pat.tests : Pat → Array Term
  | .var _ => #[]
  | .eq M => #[M]
  | .tuple ps | .app _ ps => ps.flatMap tests

partial def Proc.names : Proc → Array String
  | .nil => #[]
  | .call p args => #[p] ++ args.flatMap Term.names
  | .par P Q => P.names ++ Q.names
  | .repl P => P.names
  | .new x P => #[x] ++ P.names
  | .ite c P Q => c.names ++ P.names ++ Q.names
  | .inp c p P => c.names ++ p.names ++ P.names
  | .out c m P => c.names ++ m.names ++ P.names
  | .let p d P Q => p.names ++ d.names ++ P.names ++ Q.names
  | .event e args P => #[e] ++ args.flatMap Term.names ++ P.names

def Fact.names : Fact → Array String
  | .attacker m => m.names
  | .event e args => #[e] ++ args.flatMap Term.names

def Rule.names (r : Rule) : Array String :=
  r.vars.map (·.1) ++ r.lhs.flatMap Term.names ++ r.rhs.names

/-- Every identifier of a model. -/
def Model.names (m : Model) : Array String :=
  m.frees.map (·.1) ++ m.ctors.map (·.name) ++ m.events.map (·.1)
    ++ m.equations.flatMap (fun e => e.vars ++ e.lhs.names ++ e.rhs.names)
    ++ m.dtors.flatMap (fun d => #[d.name] ++ d.rules.flatMap Rule.names)
    ++ m.fns.flatMap (fun f => #[f.name] ++ f.params ++ f.body.names)
    ++ m.macros.flatMap (fun p => #[p.name] ++ p.params ++ p.body.names)
    ++ m.queries.flatMap (fun q =>
      q.vars ++ q.premise.names ++ (q.conclusion.map Fact.names).getD #[])
    ++ m.main.names

mutual

partial def Term.rename (σ : String → String) : Term → Term
  | .ident x => .ident (σ x)
  | .app f args => .app (σ f) (args.map (Term.rename σ))
  | .tuple args => .tuple (args.map (Term.rename σ))
  | .fail => .fail
  | .new x M => .new (σ x) (M.rename σ)
  | .ite c N N' => .ite (c.rename σ) (N.rename σ) (N'.map (Term.rename σ))
  | .let p d N N' => .let (p.rename σ) (d.rename σ) (N.rename σ) (N'.map (Term.rename σ))
  | .event e args M => .event (σ e) (args.map (Term.rename σ)) (M.rename σ)

partial def Pat.rename (σ : String → String) : Pat → Pat
  | .var x => .var (σ x)
  | .eq M => .eq (M.rename σ)
  | .tuple ps => .tuple (ps.map (Pat.rename σ))
  | .app f ps => .app (σ f) (ps.map (Pat.rename σ))

end

partial def Proc.rename (σ : String → String) : Proc → Proc
  | .nil => .nil
  | .call p args => .call (σ p) (args.map (Term.rename σ))
  | .par P Q => .par (P.rename σ) (Q.rename σ)
  | .repl P => .repl (P.rename σ)
  | .new x P => .new (σ x) (P.rename σ)
  | .ite c P Q => .ite (c.rename σ) (P.rename σ) (Q.rename σ)
  | .inp c p P => .inp (c.rename σ) (p.rename σ) (P.rename σ)
  | .out c m P => .out (c.rename σ) (m.rename σ) (P.rename σ)
  | .let p d P Q => .let (p.rename σ) (d.rename σ) (P.rename σ) (Q.rename σ)
  | .event e args P => .event (σ e) (args.map (Term.rename σ)) (P.rename σ)

def Fact.rename (σ : String → String) : Fact → Fact
  | .attacker m => .attacker (m.rename σ)
  | .event e args => .event (σ e) (args.map (Term.rename σ))

def Rule.rename (σ : String → String) (r : Rule) : Rule where
  vars := r.vars.map fun (x, b) => (σ x, b)
  lhs := r.lhs.map (Term.rename σ)
  rhs := r.rhs.rename σ

/-- `m` with `σ` applied to every identifier. -/
def Model.rename (σ : String → String) (m : Model) : Model where
  frees := m.frees.map fun (a, pub) => (σ a, pub)
  ctors := m.ctors.map fun c => { c with name := σ c.name }
  events := m.events.map fun (e, n) => (σ e, n)
  equations := m.equations.map fun e =>
    { vars := e.vars.map σ, lhs := e.lhs.rename σ, rhs := e.rhs.rename σ }
  dtors := m.dtors.map fun d => { d with name := σ d.name, rules := d.rules.map (Rule.rename σ) }
  fns := m.fns.map fun f => { name := σ f.name, params := f.params.map σ, body := f.body.rename σ }
  macros := m.macros.map fun p =>
    { name := σ p.name, params := p.params.map σ, body := p.body.rename σ }
  queries := m.queries.map fun q =>
    { vars := q.vars.map σ, premise := q.premise.rename σ, conclusion := q.conclusion.map (Fact.rename σ) }
  main := m.main.rename σ

end ProVerif.Translation
