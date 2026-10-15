/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib.Data.Fin.Tuple.Basic
import ScalingTrust.ProVerif.TraceSemantics.Term

/-!
# The syntax of ProVerif's calculus

The write-up's Definition "Source syntax" (`../Writeup/Semantics.tex`, §1.3), types
erased, over a signature `F` of constructors and a signature `G` of destructors.

* **Terms** are the first-order terms over `F` of the trace semantics.  Under `n`
  binders their variables are `ℕ ⊕ Fin n`: the created name `ν_k` is `.var (.inl k)` and
  the `i`-th bound variable `.var (.inr i)`.  Free names are nullary constructors, as in
  the trace semantics.
* **Expressions** apply constructors and destructors to expressions, or `fail`.
* **Processes** are indexed by their number of bound variables, as Mathlib's
  `BoundedFormula` is: `in`, `new` and `let` bind the last variable `Fin.last n`, and an
  environment extends with `Fin.snoc`.  A closed process is a `Process F G 0`.  `new`
  binds a variable where the survey binds a name; (Red Res) replaces it by a created
  name `ν_k`.
* **Rewrite rules** of destructors, the write-up's Definition "Destructors from rewrite
  rules": patterns over the free symbols of the theory, with ordinary variables and
  may-fail variables both indexed by `ℕ`, and right-hand sides `fail`, a may-fail
  variable, or a term over constructors and ordinary variables.
* A **model** is a theory, the constant `true`, the rules of each destructor and the
  public constructors and destructors; the write-up's Definition "Model" without the
  process, which the theorems take separately.

The semantics substitutes closed terms only, which never captures, so
`Process.subst` substitutes for the bound variables without renaming, shifting under a
binder.
-/

namespace ProVerif.Specification

open FirstOrder FirstOrder.Language ProVerif.TraceSemantics

variable {F G : Sig}

/-! ## Rewrite rules -/

/-- A pattern: an ordinary variable, a may-fail variable, `fail`, or a constructor
applied to patterns. -/
inductive Pat (F : Sig) : Type
  | var (x : ℕ)
  | mvar (u : ℕ)
  | fail
  | app {n : ℕ} (f : F n) (args : Fin n → Pat F)

namespace Pat

/-- The ordinary variables of a pattern. -/
def vars : Pat F → Finset ℕ
  | .var x => {x}
  | .mvar _ => ∅
  | .fail => ∅
  | .app _ args => Finset.univ.biUnion fun i => (args i).vars

/-- The may-fail variables of a pattern. -/
def mvars : Pat F → Finset ℕ
  | .var _ => ∅
  | .mvar u => {u}
  | .fail => ∅
  | .app _ args => Finset.univ.biUnion fun i => (args i).mvars

/-- Every symbol of the pattern is free in `T`. -/
def Free (T : Theory F) : Pat F → Prop
  | .var _ => True
  | .mvar _ => True
  | .fail => True
  | .app f args => T.free _ f = true ∧ ∀ i, (args i).Free T

end Pat

/-- The right-hand side of a rule: `fail`, a may-fail variable, or a term over
constructors and ordinary variables. -/
inductive Rhs (F : Sig) : Type
  | fail
  | mvar (u : ℕ)
  | term (M : F.lang.Term ℕ)

/-- The ordinary variables of a right-hand side. -/
def Rhs.vars : Rhs F → Finset ℕ
  | .fail => ∅
  | .mvar _ => ∅
  | .term M => M.varFinset

/-- The may-fail variables of a right-hand side. -/
def Rhs.mvars : Rhs F → Finset ℕ
  | .fail => ∅
  | .mvar u => {u}
  | .term _ => ∅

/-- A rewrite rule `g(p₁, …, pₙ) → q` of a destructor of arity `n`: patterns over the
free symbols of `T`, every variable of the right-hand side occurring in them. -/
structure Rule (T : Theory F) (n : ℕ) where
  /-- The patterns. -/
  pats : Fin n → Pat F
  /-- The right-hand side. -/
  rhs : Rhs F
  /-- Every pattern is over the free symbols. -/
  free : ∀ i, (pats i).Free T
  /-- Every ordinary variable of the right-hand side occurs in a pattern. -/
  vars : rhs.vars ⊆ Finset.univ.biUnion fun i => (pats i).vars
  /-- Every may-fail variable of the right-hand side occurs in a pattern. -/
  mvars : rhs.mvars ⊆ Finset.univ.biUnion fun i => (pats i).mvars

/-- A model: the theory, the constant `true`, the rules of each destructor, and the
public constructors and destructors. -/
structure Model (F G : Sig) extends Theory F where
  /-- The constant `true`, which `if` tests for. -/
  tt : F 0
  /-- The rules of each destructor, in order. -/
  dtor : ∀ {n : ℕ}, G n → List (Rule toTheory n)
  /-- The public constructors, including the public free names. -/
  pubFun : ∀ n, Set (F n)
  /-- The public destructors. -/
  pubDtor : ∀ n, Set (G n)

/-! ## Terms, expressions and processes -/

/-- A term under `n` binders. -/
abbrev Tm (F : Sig) (n : ℕ) : Type := F.lang.Term (ℕ ⊕ Fin n)

/-- An expression over the variables `α`. -/
inductive Expr (F G : Sig) (α : Type) : Type
  | term (M : F.lang.Term α)
  | ctor {n : ℕ} (f : F n) (args : Fin n → Expr F G α)
  | dtor {n : ℕ} (g : G n) (args : Fin n → Expr F G α)
  | fail

/-- A process under `n` binders. -/
inductive Process (F G : Sig) : ℕ → Type
  /-- `0` -/
  | nil {n : ℕ} : Process F G n
  /-- `out(N, M); P` -/
  | out {n : ℕ} (N M : Tm F n) (P : Process F G n) : Process F G n
  /-- `in(N, x); P` -/
  | inp {n : ℕ} (N : Tm F n) (P : Process F G (n + 1)) : Process F G n
  /-- `P | Q` -/
  | par {n : ℕ} (P Q : Process F G n) : Process F G n
  /-- `!P` -/
  | bang {n : ℕ} (P : Process F G n) : Process F G n
  /-- `new a; P` -/
  | new {n : ℕ} (P : Process F G (n + 1)) : Process F G n
  /-- `let x = D in P else Q` -/
  | let_ {n : ℕ} (D : Expr F G (ℕ ⊕ Fin n)) (P : Process F G (n + 1)) (Q : Process F G n) :
      Process F G n
  /-- `if M then P else Q` -/
  | ite {n : ℕ} (M : Tm F n) (P Q : Process F G n) : Process F G n
  /-- `event(M); P` -/
  | event {n : ℕ} (M : Tm F n) (P : Process F G n) : Process F G n

/-! ## Substitution for the bound variables -/

variable {n m : ℕ}

/-- A substitution `σ` for the bound variables, extended under a binder: the new
variable is sent to itself, and the others to `σ` shifted. -/
def liftSubst (σ : Fin n → Tm F m) : Fin (n + 1) → Tm F (m + 1) :=
  Fin.snoc (fun i => (σ i).relabel (Sum.map id Fin.castSucc)) (.var (.inr (Fin.last m)))

/-- Substitute for the bound variables of a term. -/
def Tm.subst (σ : Fin n → Tm F m) (M : Tm F n) : Tm F m :=
  Term.subst M (Sum.elim (fun k => .var (.inl k)) σ)

/-- Substitute for the bound variables of an expression. -/
def Expr.subst (σ : Fin n → Tm F m) : Expr F G (ℕ ⊕ Fin n) → Expr F G (ℕ ⊕ Fin m)
  | .term M => .term (Tm.subst σ M)
  | .ctor f args => .ctor f fun i => (args i).subst σ
  | .dtor g args => .dtor g fun i => (args i).subst σ
  | .fail => .fail

/-- Substitute for the bound variables of a process. -/
def Process.subst : {n m : ℕ} → (Fin n → Tm F m) → Process F G n → Process F G m
  | _, _, _, .nil => .nil
  | _, _, σ, .out N M P => .out (Tm.subst σ N) (Tm.subst σ M) (P.subst σ)
  | _, _, σ, .inp N P => .inp (Tm.subst σ N) (P.subst (liftSubst σ))
  | _, _, σ, .par P Q => .par (P.subst σ) (Q.subst σ)
  | _, _, σ, .bang P => .bang (P.subst σ)
  | _, _, σ, .new P => .new (P.subst (liftSubst σ))
  | _, _, σ, .let_ D P Q => .let_ (D.subst σ) (P.subst (liftSubst σ)) (Q.subst σ)
  | _, _, σ, .ite M P Q => .ite (Tm.subst σ M) (P.subst σ) (Q.subst σ)
  | _, _, σ, .event M P => .event (Tm.subst σ M) (P.subst σ)

/-- `P{M/x}`: substitute `M` for the last bound variable. -/
def Process.inst (P : Process F G (n + 1)) (M : Tm F n) : Process F G n :=
  P.subst (Fin.snoc (fun i => .var (.inr i)) M)

end ProVerif.Specification
