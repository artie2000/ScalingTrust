/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib.Data.Fin.Tuple.Basic
import ScalingTrust.ProVerif.TraceSemantics.Data

/-!
# The syntax of ProVerif's calculus

The write-up's Definition "Source syntax" (`../Writeup/Semantics.tex`, §2.1), types
erased, over a signature `F` of declared constructors and a signature `G` of declared
destructors.  The data symbols are built in: the constructors of the calculus are
`F.withData`, the declared ones with the tuples and the booleans, and its destructors
`Sig.withBuiltin G`, the declared ones with the projections of tuples and the boolean
destructors.

* **Terms** are the first-order terms over `F.withData` of the trace semantics.  Under `n`
  binders their variables are `ℕ ⊕ Fin n`: the created name `ν_k` is `.var (.inl k)` and
  the `i`-th bound variable `.var (.inr i)`.  Free names are nullary constructors, as in
  the trace semantics.
* **Expressions** apply constructors and destructors to expressions, or `fail`.
* **Processes** are indexed by their number of bound variables, as Mathlib's
  `BoundedFormula` is: `in`, `new` and `let` bind the last variable `Fin.last n`, and an
  environment extends with `Fin.snoc`.  A closed process is a `Process F G 0`.  `new`
  binds a variable where the survey binds a name; (Red Res) replaces it by a created
  name `ν_k`.
* **Rewrite rules** of destructors, the write-up's Definition "Rewrite rules": the
  arguments and the right-hand side are may-fail terms, a term over constructors and
  ordinary variables, a may-fail variable or `fail`, the arguments over the free symbols
  of the theory, the write-up's (R2).  Ordinary and may-fail variables are both indexed
  by `ℕ`.  The built-in destructors have the rules `Builtin.rules`: a projection the one
  rule `proj k i (tuple k (x₀, …)) → xᵢ`, the boolean destructors the survey's.
* A **model** is the theory of the declarations, the rules of each declared destructor,
  over the data symbols too, and the public constructors and destructors; the write-up's
  Definition "Model" without the process, which the theorems take separately.  Its
  messages, `Model.Msg`, are those of the theory with the data symbols, so `true` is
  `StdOps.tt` and the data symbols are free and public.

The semantics substitutes closed terms only, which never captures, so
`Process.subst` substitutes for the bound variables without renaming, shifting under a
binder.
-/

namespace ProVerif.Specification

open FirstOrder FirstOrder.Language ProVerif.TraceSemantics

variable {F G : Sig}

/-- The destructors built into every model: the projections of tuples, `proj k i` reading
the `i`-th component of a `k`-tuple, and the boolean destructors, the survey's `equal`,
`not`, `and` and `or` (§2.1), which ProVerif's `=`, `<>`, `not`, `&&` and `||` stand for
(manual, Appendix B). -/
inductive Builtin : ℕ → Type
  | proj (k : ℕ) (i : Fin k) : Builtin 1
  | equal : Builtin 2
  | not : Builtin 1
  | and : Builtin 2
  | or : Builtin 2

/-- A boolean destructor: a built-in one other than a projection. -/
def Builtin.IsBool : ∀ {n : ℕ}, Builtin n → Prop
  | _, .proj _ _ => False
  | _, _ => True

/-- The destructor symbols of a model: the declared ones and the built-in ones. -/
abbrev Sig.withBuiltin (G : Sig) : Sig := fun n => G n ⊕ Builtin n

/-! ## Rewrite rules -/

/-- Every symbol of the term is free in `T`. -/
def Term.Free (T : Theory F) : Term F → Prop
  | .var _ => True
  | .func f ts => T.free _ f = true ∧ ∀ i, Term.Free T (ts i)

/-- A may-fail term, the write-up's Definition "Rewrite rules": a term over constructors
and ordinary variables, a may-fail variable, or `fail`.  The arguments and the result of a
rule are may-fail terms. -/
inductive MayFail (F : Sig) : Type
  | term (M : Term F)
  | mvar (u : ℕ)
  | fail

namespace MayFail

/-- The ordinary variables. -/
def vars : MayFail F → Finset ℕ
  | .term M => M.varFinset
  | .mvar _ => ∅
  | .fail => ∅

/-- The may-fail variables. -/
def mvars : MayFail F → Finset ℕ
  | .term _ => ∅
  | .mvar u => {u}
  | .fail => ∅

/-- The term, if there is one, is over the free symbols of `T`. -/
def Free (T : Theory F) : MayFail F → Prop
  | .term M => Term.Free T M
  | .mvar _ => True
  | .fail => True

end MayFail

/-- A rewrite rule `g(U₁, …, Uₙ) → U` of a destructor of arity `n`: may-fail terms, the
arguments over the free symbols of `T`, the write-up's (R2), and every variable of the
right-hand side occurring in an argument. -/
structure Rule (T : Theory F) (n : ℕ) where
  /-- The arguments. -/
  args : Fin n → MayFail F
  /-- The right-hand side. -/
  rhs : MayFail F
  /-- Every argument is over the free symbols. -/
  free : ∀ i, (args i).Free T
  /-- Every ordinary variable of the right-hand side occurs in an argument. -/
  vars : rhs.vars ⊆ Finset.univ.biUnion fun i => (args i).vars
  /-- Every may-fail variable of the right-hand side occurs in an argument. -/
  mvars : rhs.mvars ⊆ Finset.univ.biUnion fun i => (args i).mvars

/-- The rule of the `i`-th projection of `k`-tuples, `proj k i (tuple k (x₀, …)) → xᵢ`, the
variables numbered by position. -/
def projRule (T : Theory F) (k : ℕ) (i : Fin k) : Rule T.withData 1 where
  args := ![.term (.func (.inr (.tuple k)) fun j => .var j)]
  rhs := .term (.var i)
  free j := by
    obtain rfl := Subsingleton.elim j 0
    exact ⟨rfl, fun _ => trivial⟩
  vars := by simp [MayFail.vars, Term.varFinset]
  mvars := by simp [MayFail.mvars]

/-- `true` as a may-fail term. -/
def MayFail.tt : MayFail F.withData := .term (.func (.inr .tt) ![])

/-- `false` as a may-fail term. -/
def MayFail.ff : MayFail F.withData := .term (.func (.inr .ff) ![])

/-- The rules of a built-in destructor: a projection reads a component, and the boolean
destructors have the survey's rules (§2.1, (2.5)), which are the manual's (Appendix B),
`u` a may-fail variable so that `and(false, fail)` is `false`:
`equal(x, x) → true; equal(x, y) → false`, `not(true) → false; not(x) → true`,
`and(true, u) → u; and(x, u) → false` and `or(true, u) → true; or(x, u) → u`. -/
def Builtin.rules (T : Theory F) : ∀ {n : ℕ}, Builtin n → List (Rule T.withData n)
  | _, .proj k i => [projRule T k i]
  | _, .equal =>
    [{ args := ![.term (.var 0), .term (.var 0)], rhs := .tt,
       free := Fin.forall_fin_two.2 ⟨trivial, trivial⟩,
       vars := by simp [MayFail.vars, MayFail.tt, Term.varFinset],
       mvars := by simp [MayFail.mvars, MayFail.tt] },
     { args := ![.term (.var 0), .term (.var 1)], rhs := .ff,
       free := Fin.forall_fin_two.2 ⟨trivial, trivial⟩,
       vars := by simp [MayFail.vars, MayFail.ff, Term.varFinset],
       mvars := by simp [MayFail.mvars, MayFail.ff] }]
  | _, .not =>
    [{ args := ![.tt], rhs := .ff,
       free := Fin.forall_fin_one.2 ⟨rfl, fun i => i.elim0⟩,
       vars := by simp [MayFail.vars, MayFail.ff, Term.varFinset],
       mvars := by simp [MayFail.mvars, MayFail.ff] },
     { args := ![.term (.var 0)], rhs := .tt,
       free := Fin.forall_fin_one.2 trivial,
       vars := by simp [MayFail.vars, MayFail.tt, Term.varFinset],
       mvars := by simp [MayFail.mvars, MayFail.tt] }]
  | _, .and =>
    [{ args := ![.tt, .mvar 0], rhs := .mvar 0,
       free := Fin.forall_fin_two.2 ⟨⟨rfl, fun i => i.elim0⟩, trivial⟩,
       vars := by simp [MayFail.vars],
       mvars := by simp [MayFail.mvars, MayFail.tt, Finset.subset_iff, Fin.exists_fin_two] },
     { args := ![.term (.var 0), .mvar 0], rhs := .ff,
       free := Fin.forall_fin_two.2 ⟨trivial, trivial⟩,
       vars := by simp [MayFail.vars, MayFail.ff, Term.varFinset],
       mvars := by simp [MayFail.mvars, MayFail.ff] }]
  | _, .or =>
    [{ args := ![.tt, .mvar 0], rhs := .tt,
       free := Fin.forall_fin_two.2 ⟨⟨rfl, fun i => i.elim0⟩, trivial⟩,
       vars := by simp [MayFail.vars, MayFail.tt, Term.varFinset],
       mvars := by simp [MayFail.mvars, MayFail.tt] },
     { args := ![.term (.var 0), .mvar 0], rhs := .mvar 0,
       free := Fin.forall_fin_two.2 ⟨trivial, trivial⟩,
       vars := by simp [MayFail.vars],
       mvars := by simp [MayFail.mvars, Finset.subset_iff, Fin.exists_fin_two] }]

/-- A rule of a boolean destructor has right-hand side `true`, `false` or a may-fail
variable among its arguments: the destructor yields a boolean or an argument. -/
theorem Builtin.rhs_of_mem_rules {T : Theory F} {n : ℕ} {b : Builtin n} (hb : b.IsBool)
    {r : Rule T.withData n} (hr : r ∈ b.rules T) :
    r.rhs = .tt ∨ r.rhs = .ff ∨ ∃ u, r.rhs = .mvar u ∧ ∃ i, r.args i = .mvar u := by
  rcases b with ⟨k, i⟩ | _ | _ | _ | _
  · exact hb.elim
  all_goals
    simp only [Builtin.rules, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [MayFail.tt, MayFail.ff, Fin.exists_fin_two]

/-- A model: the theory of the declarations, the rules of each declared destructor, and
the public constructors and destructors.  Its terms are over the declared constructors
and the data symbols, and its destructors the declared ones and the built-in ones. -/
structure Model (F G : Sig) extends Theory F where
  /-- The rules of each declared destructor, in order, over the data symbols too. -/
  dtor : ∀ {n : ℕ}, G n → List (Rule toTheory.withData n)
  /-- The public constructors, including the public free names. -/
  pubFun : ∀ n, Set (F n)
  /-- The public destructors. -/
  pubDtor : ∀ n, Set (G n)

/-- The messages of a model: those of its theory with the data symbols. -/
abbrev Model.Msg (A : Model F G) : Type := A.withData.Msg

/-- The rules of a destructor symbol: the declared ones, or the built-in one's. -/
def Model.rules (A : Model F G) : ∀ {n : ℕ}, Sig.withBuiltin G n → List (Rule A.withData n)
  | _, .inl g => A.dtor g
  | _, .inr b => b.rules A.toTheory

/-! ## Terms, expressions and processes -/

/-- A term under `n` binders, over the declared constructors and the data symbols. -/
abbrev Tm (F : Sig) (n : ℕ) : Type := F.withData.lang.Term (ℕ ⊕ Fin n)

/-- An expression over the variables `α`. -/
inductive Expr (F G : Sig) (α : Type) : Type
  | term (M : F.withData.lang.Term α)
  | ctor {n : ℕ} (f : F.withData n) (args : Fin n → Expr F G α)
  | dtor {n : ℕ} (g : Sig.withBuiltin G n) (args : Fin n → Expr F G α)
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
