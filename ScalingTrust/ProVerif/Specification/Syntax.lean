/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib.Data.Fin.Tuple.Basic
import ScalingTrust.ProVerif.TraceSemantics.Data

/-!
# The syntax of ProVerif's calculus

The write-up's Definitions "Source syntax", "Rewrite rules" and "Model"
(`../Writeup/Semantics.tex`, §2.1), types erased, over a signature `F` of declared
constructors, a signature `G` of declared destructors and a signature `Ev` of event
symbols.

* **Messages** are built from the constructors of the calculus, `Sig.cons F Ev`:
  the declared constructors, the event symbols and the data symbols, tuples and
  booleans.  An event `ev(M₁, …, Mₙ)` is thus a message, as the trace semantics records
  events as messages; the manual keeps event symbols out of terms and rewrite rules,
  which nothing here forbids.
* **Terms** are the first-order terms over the constructors of the calculus.  Under `n`
  binders their variables are `ℕ ⊕ Fin n`: the created name `ν_k` is `.var (.inl k)` and
  the `i`-th bound variable `.var (.inr i)`.  Free names are nullary constructors, as in
  the trace semantics.
* **Expressions** are the manual's process terms (§4.1.4, Appendix B) for the fragment
  without tables and patterns: a term, a constructor or destructor applied to
  expressions, `fail`, and the enriched forms `new a; D`, `if C then D₁ else D₂`,
  `let x = D in D₁ else D₂` and `event ev(D₁, …, Dₙ); D`.  A term is a leaf, so the
  write-up's `f(M₁, …, Mₙ)`, which its grammar derives both as a term and as an
  application, has two spellings here, `term (f(M₁, …, Mₙ))` and `ctor f (term Mᵢ)`;
  both are may-fail terms (`Expr.IsValue`), the values of expressions.
* **Processes** are indexed by their number of bound variables, as Mathlib's
  `BoundedFormula` is, and so are expressions: `in`, `new` and `let` bind the last
  variable `Fin.last n`, and an environment extends with `Fin.snoc`.  A closed process is
  a `Process F G Ev 0`.  `new` binds a variable where the manual binds a name; the step
  replaces it by a created name `ν_k`.  Every term position of a process holds an
  expression, as in the manual's Figure A.8.
* **Rewrite rules** of destructors, the write-up's Definition "Rewrite rules": the
  arguments and the right-hand side are may-fail terms, a term over constructors and
  ordinary variables, a may-fail variable or `fail`, every variable of the right-hand
  side occurring in an argument.  Ordinary and may-fail variables are both indexed by
  `ℕ`.  The built-in destructors have the rules `Builtin.rules`: a projection the one rule
  `proj k i (tuple k (x₀, …)) → xᵢ`, the boolean destructors the survey's.
* A **model** is the write-up's Definition "Model" without the process, which the
  theorems take separately: the equations, the rules of each declared destructor, and
  the public constructors and destructors, together with the two conditions of the
  write-up's §3 under which it instantiates the trace semantics, (R1) that no side of an
  equation is a variable and (R2) that the terms among the arguments of a rule are over
  the free symbols.  The theory of the trace semantics is derived from the equations,
  `Model.theory`, with the free symbols those at the root of no equation, the event
  symbols and the data symbols; its messages, `Model.Msg`, are those of the theory with
  the data symbols, so `true` is `StdOps.tt`.

The semantics substitutes closed terms only, which never captures, so
`Process.subst` substitutes for the bound variables without renaming, shifting under a
binder.
-/

namespace ProVerif.Specification

open FirstOrder FirstOrder.Language ProVerif.TraceSemantics

variable {F G Ev : Sig}

/-- `F` with the event symbols. -/
abbrev Sig.withEv (F Ev : Sig) : Sig := fun n => F n ⊕ Ev n

/-- The constructors of the calculus: the declared ones, the event symbols and the data
symbols. -/
abbrev Sig.cons (F Ev : Sig) : Sig := (Sig.withEv F Ev).withData

/-- The inclusion of `F` in `Sig.withEv F Ev`, as a map of languages. -/
def Sig.inclusionEv (F Ev : Sig) : F.lang →ᴸ (Sig.withEv F Ev).lang :=
  ⟨fun _ => Sum.inl, fun _ => id⟩

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

/-- A rewrite rule `g(U₁, …, Uₙ) → U` of a destructor of arity `n`: may-fail terms, every
variable of the right-hand side occurring in an argument. -/
structure Rule (F : Sig) (n : ℕ) where
  /-- The arguments. -/
  args : Fin n → MayFail F
  /-- The right-hand side. -/
  rhs : MayFail F
  /-- Every ordinary variable of the right-hand side occurs in an argument. -/
  vars : rhs.vars ⊆ Finset.univ.biUnion fun i => (args i).vars
  /-- Every may-fail variable of the right-hand side occurs in an argument. -/
  mvars : rhs.mvars ⊆ Finset.univ.biUnion fun i => (args i).mvars

/-- The rule of the `i`-th projection of `k`-tuples, `proj k i (tuple k (x₀, …)) → xᵢ`, the
variables numbered by position. -/
def projRule (F : Sig) (k : ℕ) (i : Fin k) : Rule F.withData 1 where
  args := ![.term (.func (.inr (.tuple k)) fun j => .var j)]
  rhs := .term (.var i)
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
`and(true, u) → u; and(x, u) → false` and `or(true, u) → true; or(x, u) → u`.  The manual's
§3.1.4 says instead that the second operand of `&&` and `||` is not evaluated when the first
decides; Appendix B takes precedence (the folder README's first principle), so both operands
are evaluated and the effects of the second run. -/
def Builtin.rules (F : Sig) : ∀ {n : ℕ}, Builtin n → List (Rule F.withData n)
  | _, .proj k i => [projRule F k i]
  | _, .equal =>
    [{ args := ![.term (.var 0), .term (.var 0)], rhs := .tt,
       vars := by simp [MayFail.vars, MayFail.tt, Term.varFinset],
       mvars := by simp [MayFail.mvars, MayFail.tt] },
     { args := ![.term (.var 0), .term (.var 1)], rhs := .ff,
       vars := by simp [MayFail.vars, MayFail.ff, Term.varFinset],
       mvars := by simp [MayFail.mvars, MayFail.ff] }]
  | _, .not =>
    [{ args := ![.tt], rhs := .ff,
       vars := by simp [MayFail.vars, MayFail.ff, Term.varFinset],
       mvars := by simp [MayFail.mvars, MayFail.ff] },
     { args := ![.term (.var 0)], rhs := .tt,
       vars := by simp [MayFail.vars, MayFail.tt, Term.varFinset],
       mvars := by simp [MayFail.mvars, MayFail.tt] }]
  | _, .and =>
    [{ args := ![.tt, .mvar 0], rhs := .mvar 0,
       vars := by simp [MayFail.vars],
       mvars := by simp [MayFail.mvars, MayFail.tt, Finset.subset_iff, Fin.exists_fin_two] },
     { args := ![.term (.var 0), .mvar 0], rhs := .ff,
       vars := by simp [MayFail.vars, MayFail.ff, Term.varFinset],
       mvars := by simp [MayFail.mvars, MayFail.ff] }]
  | _, .or =>
    [{ args := ![.tt, .mvar 0], rhs := .tt,
       vars := by simp [MayFail.vars, MayFail.tt, Term.varFinset],
       mvars := by simp [MayFail.mvars, MayFail.tt] },
     { args := ![.term (.var 0), .mvar 0], rhs := .mvar 0,
       vars := by simp [MayFail.vars],
       mvars := by simp [MayFail.mvars, Finset.subset_iff, Fin.exists_fin_two] }]

/-- A rule of a boolean destructor has right-hand side `true`, `false` or a may-fail
variable among its arguments: the destructor yields a boolean or an argument. -/
theorem Builtin.rhs_of_mem_rules {n : ℕ} {b : Builtin n} (hb : b.IsBool)
    {r : Rule F.withData n} (hr : r ∈ b.rules F) :
    r.rhs = .tt ∨ r.rhs = .ff ∨ ∃ u, r.rhs = .mvar u ∧ ∃ i, r.args i = .mvar u := by
  rcases b with ⟨k, i⟩ | _ | _ | _ | _
  · exact hb.elim
  all_goals
    simp only [Builtin.rules, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [MayFail.tt, MayFail.ff, Fin.exists_fin_two]

/-- The arguments of a built-in destructor's rules are over the data symbols, which are
free. -/
theorem Builtin.rules_free (T : Theory F) {n : ℕ} (b : Builtin n) {r : Rule F.withData n}
    (hr : r ∈ b.rules F) (i : Fin n) : (r.args i).Free T.withData := by
  revert i
  rcases b with ⟨k, j⟩ | _ | _ | _ | _
  · simp only [Builtin.rules, List.mem_singleton] at hr
    subst hr
    simp [projRule, MayFail.Free, Term.Free, Theory.withData]
  all_goals
    simp only [Builtin.rules, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
  all_goals
    simp [MayFail.Free, Term.Free, MayFail.tt, Theory.withData, Fin.forall_fin_two]

/-! ## Models -/

/-- A term is a variable. -/
def Term.IsVar : Term F → Prop
  | .var _ => True
  | .func _ _ => False

/-- `f` is at the root of no equation. -/
def RootFree (eqs : Set (Term F × Term F)) {n : ℕ} (f : F n) : Prop :=
  ∀ e ∈ eqs, ∀ ts, e.1 ≠ .func f ts ∧ e.2 ≠ .func f ts

/-- The condition (R1) of the write-up's §3: no side of an equation is a variable. -/
def R1 (eqs : Set (Term F × Term F)) : Prop := ∀ e ∈ eqs, ¬ Term.IsVar e.1 ∧ ¬ Term.IsVar e.2

open Classical in
/-- The theory of the trace semantics that equations between terms over the declared
constructors give, under (R1), on the constructors with the event symbols: the free symbols
are those at the root of no equation and the event symbols. -/
noncomputable def theoryOf (Ev : Sig) (eqs : Set (Term F × Term F)) (h : R1 eqs) :
    Theory (Sig.withEv F Ev) where
  E := (fun e : Term F × Term F =>
    ((Sig.inclusionEv F Ev).onTerm e.1, (Sig.inclusionEv F Ev).onTerm e.2)) '' eqs
  free _ f := match f with
    | .inl f => decide (RootFree eqs f)
    | .inr _ => true
  heads := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨h₁, h₂⟩ := h e he
    dsimp only
    constructor
    · rcases hl : e.1 with x | ⟨f, ts⟩
      · exact (h₁ (hl ▸ trivial)).elim
      · show decide (RootFree eqs f) = false
        exact decide_eq_false fun hf : RootFree eqs f => ((hf e he ts).1 hl).elim
    · rcases hr : e.2 with x | ⟨f, ts⟩
      · exact (h₂ (hr ▸ trivial)).elim
      · show decide (RootFree eqs f) = false
        exact decide_eq_false fun hf : RootFree eqs f => ((hf e he ts).2 hr).elim

/-- A model, the write-up's Definition "Model" without the process: the equations, the
rules of each declared destructor over the constructors of the calculus, and the public
constructors and destructors; with the two conditions of the write-up's §3 under which the
trace semantics is instantiated from it. -/
structure Model (F G Ev : Sig) where
  /-- The equations, between terms over the declared constructors. -/
  eqs : Set (Term F × Term F)
  /-- The rules of each declared destructor, in order. -/
  dtor : ∀ {n : ℕ}, G n → List (Rule (Sig.cons F Ev) n)
  /-- The public constructors, including the public free names. -/
  pubFun : ∀ n, Set (F n)
  /-- The public destructors. -/
  pubDtor : ∀ n, Set (G n)
  /-- (R1): no side of an equation is a variable. -/
  r1 : R1 eqs
  /-- (R2): the terms among the arguments of a rule are over the free symbols. -/
  r2 : ∀ {n : ℕ} (g : G n), ∀ r ∈ dtor g, ∀ i, (r.args i).Free (theoryOf Ev eqs r1).withData

/-- The theory of the trace semantics a model instantiates. -/
noncomputable def Model.theory (A : Model F G Ev) : Theory (Sig.withEv F Ev) :=
  theoryOf Ev A.eqs A.r1

/-- The messages of a model: those of its theory with the data symbols. -/
abbrev Model.Msg (A : Model F G Ev) : Type := A.theory.withData.Msg

/-- The rules of a destructor symbol: the declared ones, or the built-in one's. -/
def Model.rules (A : Model F G Ev) :
    ∀ {n : ℕ}, Sig.withBuiltin G n → List (Rule (Sig.cons F Ev) n)
  | _, .inl g => A.dtor g
  | _, .inr b => b.rules (Sig.withEv F Ev)

/-- The arguments of every rule of a model are over the free symbols, (R2). -/
theorem Model.rules_free (A : Model F G Ev) {n : ℕ} (g : Sig.withBuiltin G n)
    {r : Rule (Sig.cons F Ev) n} (hr : r ∈ A.rules g) (i : Fin n) :
    (r.args i).Free A.theory.withData := by
  cases g with
  | inl g => exact A.r2 g r hr i
  | inr b => exact Builtin.rules_free A.theory b hr i

/-! ## Terms, expressions and processes -/

/-- A term under `n` binders, over the constructors of the calculus. -/
abbrev Tm (F Ev : Sig) (n : ℕ) : Type := (Sig.cons F Ev).lang.Term (ℕ ⊕ Fin n)

/-- An expression under `n` binders. -/
inductive Expr (F G Ev : Sig) : ℕ → Type
  /-- A term. -/
  | term {n : ℕ} (M : Tm F Ev n) : Expr F G Ev n
  /-- `f(D₁, …, Dₖ)` -/
  | ctor {n k : ℕ} (f : Sig.cons F Ev k) (args : Fin k → Expr F G Ev n) : Expr F G Ev n
  /-- `g(D₁, …, Dₖ)` -/
  | dtor {n k : ℕ} (g : Sig.withBuiltin G k) (args : Fin k → Expr F G Ev n) : Expr F G Ev n
  /-- `fail` -/
  | fail {n : ℕ} : Expr F G Ev n
  /-- `new a; D` -/
  | new {n : ℕ} (D : Expr F G Ev (n + 1)) : Expr F G Ev n
  /-- `if C then D₁ else D₂` -/
  | ite {n : ℕ} (C D₁ D₂ : Expr F G Ev n) : Expr F G Ev n
  /-- `let x = D in D₁ else D₂` -/
  | let_ {n : ℕ} (D : Expr F G Ev n) (D₁ : Expr F G Ev (n + 1)) (D₂ : Expr F G Ev n) :
      Expr F G Ev n
  /-- `event ev(D₁, …, Dₖ); D` -/
  | event {n k : ℕ} (e : Ev k) (args : Fin k → Expr F G Ev n) (D : Expr F G Ev n) : Expr F G Ev n

/-- A term written as an expression: a term, or a constructor applied to terms. -/
inductive Expr.IsTerm {n : ℕ} : Expr F G Ev n → Prop
  | term (M : Tm F Ev n) : Expr.IsTerm (.term M)
  | ctor {k : ℕ} (f : Sig.cons F Ev k) {args : Fin k → Expr F G Ev n} :
      (∀ i, Expr.IsTerm (args i)) → Expr.IsTerm (.ctor f args)

theorem Expr.IsTerm.arg {n k : ℕ} {f : Sig.cons F Ev k} {args : Fin k → Expr F G Ev n}
    (h : (Expr.ctor f args).IsTerm) (i : Fin k) : (args i).IsTerm :=
  match h with
  | .ctor _ h => h i

/-- A may-fail term: a term or `fail`, the value of an expression. -/
def Expr.IsValue {n : ℕ} (D : Expr F G Ev n) : Prop := D.IsTerm ∨ D = .fail

/-- An effect-free expression: constructors and destructors applied to terms and `fail`,
without the enriched forms. -/
def Expr.Pure : ∀ {n : ℕ}, Expr F G Ev n → Prop
  | _, .term _ => True
  | _, .ctor _ args => ∀ i, Expr.Pure (args i)
  | _, .dtor _ args => ∀ i, Expr.Pure (args i)
  | _, .fail => True
  | _, _ => False

/-- A process under `n` binders. -/
inductive Process (F G Ev : Sig) : ℕ → Type
  /-- `0` -/
  | nil {n : ℕ} : Process F G Ev n
  /-- `out(N, M); P` -/
  | out {n : ℕ} (N M : Expr F G Ev n) (P : Process F G Ev n) : Process F G Ev n
  /-- `in(N, x); P` -/
  | inp {n : ℕ} (N : Expr F G Ev n) (P : Process F G Ev (n + 1)) : Process F G Ev n
  /-- `P | Q` -/
  | par {n : ℕ} (P Q : Process F G Ev n) : Process F G Ev n
  /-- `!P` -/
  | bang {n : ℕ} (P : Process F G Ev n) : Process F G Ev n
  /-- `new a; P` -/
  | new {n : ℕ} (P : Process F G Ev (n + 1)) : Process F G Ev n
  /-- `let x = D in P else Q` -/
  | let_ {n : ℕ} (D : Expr F G Ev n) (P : Process F G Ev (n + 1)) (Q : Process F G Ev n) :
      Process F G Ev n
  /-- `if C then P else Q` -/
  | ite {n : ℕ} (C : Expr F G Ev n) (P Q : Process F G Ev n) : Process F G Ev n
  /-- `event ev(D₁, …, Dₖ); P` -/
  | event {n k : ℕ} (e : Ev k) (args : Fin k → Expr F G Ev n) (P : Process F G Ev n) :
      Process F G Ev n

/-! ## Substitution for the bound variables -/

variable {n m : ℕ}

/-- A substitution `σ` for the bound variables, extended under a binder: the new
variable is sent to itself, and the others to `σ` shifted. -/
def liftSubst (σ : Fin n → Tm F Ev m) : Fin (n + 1) → Tm F Ev (m + 1) :=
  Fin.snoc (fun i => (σ i).relabel (Sum.map id Fin.castSucc)) (.var (.inr (Fin.last m)))

/-- Substitute for the bound variables of a term. -/
def Tm.subst (σ : Fin n → Tm F Ev m) (M : Tm F Ev n) : Tm F Ev m :=
  Term.subst M (Sum.elim (fun k => .var (.inl k)) σ)

/-- Substitute for the bound variables of an expression. -/
def Expr.subst : {n m : ℕ} → (Fin n → Tm F Ev m) → Expr F G Ev n → Expr F G Ev m
  | _, _, σ, .term M => .term (Tm.subst σ M)
  | _, _, σ, .ctor f args => .ctor f fun i => (args i).subst σ
  | _, _, σ, .dtor g args => .dtor g fun i => (args i).subst σ
  | _, _, _, .fail => .fail
  | _, _, σ, .new D => .new (D.subst (liftSubst σ))
  | _, _, σ, .ite C D₁ D₂ => .ite (C.subst σ) (D₁.subst σ) (D₂.subst σ)
  | _, _, σ, .let_ D D₁ D₂ => .let_ (D.subst σ) (D₁.subst (liftSubst σ)) (D₂.subst σ)
  | _, _, σ, .event e args D => .event e (fun i => (args i).subst σ) (D.subst σ)

/-- `D{M/x}`: substitute `M` for the last bound variable. -/
def Expr.inst (D : Expr F G Ev (n + 1)) (M : Tm F Ev n) : Expr F G Ev n :=
  D.subst (Fin.snoc (fun i => .var (.inr i)) M)

/-- Substitute for the bound variables of a process. -/
def Process.subst : {n m : ℕ} → (Fin n → Tm F Ev m) → Process F G Ev n → Process F G Ev m
  | _, _, _, .nil => .nil
  | _, _, σ, .out N M P => .out (N.subst σ) (M.subst σ) (P.subst σ)
  | _, _, σ, .inp N P => .inp (N.subst σ) (P.subst (liftSubst σ))
  | _, _, σ, .par P Q => .par (P.subst σ) (Q.subst σ)
  | _, _, σ, .bang P => .bang (P.subst σ)
  | _, _, σ, .new P => .new (P.subst (liftSubst σ))
  | _, _, σ, .let_ D P Q => .let_ (D.subst σ) (P.subst (liftSubst σ)) (Q.subst σ)
  | _, _, σ, .ite C P Q => .ite (C.subst σ) (P.subst σ) (Q.subst σ)
  | _, _, σ, .event e args P => .event e (fun i => (args i).subst σ) (P.subst σ)

/-- `P{M/x}`: substitute `M` for the last bound variable. -/
def Process.inst (P : Process F G Ev (n + 1)) (M : Tm F Ev n) : Process F G Ev n :=
  P.subst (Fin.snoc (fun i => .var (.inr i)) M)

theorem Expr.Pure.subst {σ : Fin n → Tm F Ev m} : ∀ {D : Expr F G Ev n}, D.Pure → (D.subst σ).Pure
  | .term _, _ => trivial
  | .ctor _ args, h => fun i => Expr.Pure.subst (D := args i) (h i)
  | .dtor _ args, h => fun i => Expr.Pure.subst (D := args i) (h i)
  | .fail, _ => trivial

end ProVerif.Specification
