/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/

/-!
# ProVerif models

A model as the translation reads it, types erased: the free names, constructors,
events, equations and destructors a ProVerif file declares, its function and
process macros, its queries and its main process, with the printing of its terms
and queries for the docstrings of the translation.  `Parser.parse` reads a model
off the text of a file.
-/

namespace ProVerif.Translation

/-- A term: an identifier, which is a variable, a free name or a constant; an
application; `fail`, in rewrite rules; or one of the enriched terms of the manual's
§4.1.4, which evaluate with effects: a restriction, a conditional comparing two
terms, a term evaluation and an event.  An absent `else` is `fail` (Appendix B). -/
inductive Term where
  | ident (x : String)
  | app (f : String) (args : Array Term)
  | fail
  | new (x : String) (M : Term)
  | ite (l : Term) (eq : Bool) (r : Term) (N : Term) (N' : Option Term)
  | «let» (x : String) (d : Term) (N : Term) (N' : Option Term)
  | event (e : String) (args : Array Term) (M : Term)
  deriving Inhabited, Repr

/-- `fun f(t₁, …, tₙ) : t` or `const c : t`, with its options. -/
structure Ctor where
  name : String
  arity : Nat
  pub : Bool
  /-- `[typeConverter]`: the identity, as under ProVerif's default `ignoreTypes = true`. -/
  converter : Bool
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

/-- A process of the fragment.  An `if` compares two terms, with `=` or `<>`; an
absent `else` and an absent `in` are `0`. -/
inductive Proc where
  | nil
  | call (p : String) (args : Array Term)
  | par (P Q : Proc)
  | repl (P : Proc)
  | new (x : String) (P : Proc)
  | ite (l : Term) (eq : Bool) (r : Term) (P Q : Proc)
  | inp (c : Term) (x : String) (P : Proc)
  | out (c m : Term) (P : Proc)
  | «let» (x : String) (d : Term) (P Q : Proc)
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

partial def Term.print : Term → String
  | .ident x => x
  | .app f args => s!"{f}({", ".intercalate (args.map arg).toList})"
  | .fail => "fail"
  | .new x M => s!"new {x}; {M.print}"
  | .ite l eq r N N' =>
    s!"if {l.print} {if eq then "=" else "<>"} {r.print} then {N.print}{orElse N'}"
  | .let x d N N' => s!"let {x} = {d.print} in {N.print}{orElse N'}"
  | .event e args M => s!"event {printApp e (args.map arg)}; {M.print}"
where
  arg (t : Term) : String := if t.enriched then s!"({t.print})" else t.print
  orElse : Option Term → String
    | none => ""
    | some N' => s!" else {N'.print}"

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

end ProVerif.Translation
