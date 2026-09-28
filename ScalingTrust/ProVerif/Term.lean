/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.ModelTheory.Quotients

/-!
# Message algebras from constructors and equations

The survey's messages (§2.1, with equations §2.5.1), constructed from a signature and
a set of equations.

* The *constructors* are a signature `F : Sig`, giving the symbols of each arity, and
  raw terms are the terms of that first-order language (Mathlib's
  `FirstOrder.Language.Term`) whose variables are the names `ℕ`.  A fresh name is a
  variable; the free names of a protocol are constants.
* The *equations* `E` are pairs of terms, and messages `Msg T` are terms modulo the
  congruence `Eqv` they generate, so Lean's `=` on messages is the survey's `=_E`.
  Every instance of an equation is an equality of messages, `Theory.realize_eq`.
* A *destructor* is a Lean function on messages returning an `Option`, `none` being
  `fail`, defined by a `match` on `Msg.view` with one branch per rewrite rule in the
  survey's order and a final branch for failure.  A non-linear pattern is an equality
  test in its branch.

`Msg.view` shows a message's head symbol and arguments when the symbol is one the
theory declares *free*, and nothing otherwise.  The theory must justify that
declaration: every equation has a non-free symbol at the root of both sides
(`Theory.heads`), which makes the view invariant under `E` (`Theory.view_congr`).
Booleans are messages, since they can be sent; a condition is an ordinary Lean
proposition.  Types are ignored, as they are in the survey's semantics.

## Deviation from the formal semantics

The survey evaluates a destructor by matching its rules against the arguments
*modulo `E`* (p. 31): a rule applies when some term equal to the argument is an
instance of its left-hand side, and since several instances may give different
results, `D ⇓ U` is a relation.  Here a destructor is a function on the quotient,
defined by matching on the view, so it can only inspect the free symbols.  That is
the survey's condition for pattern-matching on data constructors (p. 35):
`f(M₁, …, Mₙ) =_E M'` exactly when `M'` is `f(M'₁, …, M'ₙ)` with `Mᵢ =_E M'ᵢ`.  Under
it, matching modulo `E` is matching on any representative, evaluation is a
function, and the two semantics agree.  A destructor whose pattern mentions an
equated symbol cannot be written; none occurs in the examples of the ProVerif
manual or in Noise Explorer's models.
-/

namespace ProVerif

open FirstOrder FirstOrder.Language

/-- A signature: the constructors of each arity. -/
abbrev Sig := ℕ → Type

/-- The first-order language with the constructors as function symbols. -/
abbrev Sig.lang (F : Sig) : Language := ⟨F, fun _ => Empty⟩

/-- Raw terms: the variables are the names. -/
abbrev Term (F : Sig) : Type := F.lang.Term ℕ

variable {F : Sig}

/-- Raw terms are the free structure, so `Term.realize σ` substitutes `σ`. -/
instance : F.lang.Structure (Term F) where
  funMap := Term.func
  RelMap r := r.elim

@[simp] theorem Term.funMap_eq {n : ℕ} (f : F n) (ts : Fin n → Term F) :
    Structure.funMap (L := F.lang) f ts = Term.func f ts := rfl

/-- The root of `t` is a symbol that `free` does not declare free. -/
def Term.Rigid (free : ∀ n, F n → Bool) : Term F → Prop
  | .var _ => False
  | .func f _ => free _ f = false

/-- An equational theory: the equations, and the symbols declared free, which no
equation has at its root. -/
structure Theory (F : Sig) where
  /-- The equations. -/
  E : Set (Term F × Term F)
  /-- The symbols that destructors may match on. -/
  free : ∀ n, F n → Bool
  /-- Both sides of every equation have a non-free root. -/
  heads : ∀ e ∈ E, e.1.Rigid free ∧ e.2.Rigid free

variable {T : Theory F}

/-- Equality modulo `E`: the least congruence containing every instance of an
equation. -/
inductive Eqv (T : Theory F) : Term F → Term F → Prop
  | refl (t) : Eqv T t t
  | symm {s t} : Eqv T s t → Eqv T t s
  | trans {r s t} : Eqv T r s → Eqv T s t → Eqv T r t
  | func {n} (f : F n) {a b : Fin n → Term F} : (∀ i, Eqv T (a i) (b i)) →
      Eqv T (.func f a) (.func f b)
  | ax {l r} : (l, r) ∈ T.E → ∀ σ : ℕ → Term F, Eqv T (l.realize σ) (r.realize σ)

/-- Terms modulo `E`. -/
def Theory.setoid (T : Theory F) : Setoid (Term F) := ⟨Eqv T, ⟨.refl, .symm, .trans⟩⟩

/-- The congruence respects the constructors, so the quotient is a structure. -/
instance : F.lang.Prestructure T.setoid where
  toStructure := inferInstance
  fun_equiv _ _ h := Eqv.func _ h
  rel_equiv := fun {_} {r} _ _ _ => r.elim

/-- Messages: terms modulo `E`. -/
abbrev Msg (T : Theory F) : Type := Quotient T.setoid

namespace Msg

/-- The name `n`. -/
def name (n : ℕ) : Msg T := ⟦.var n⟧

/-- Apply a constructor to messages. -/
abbrev app {n : ℕ} (f : F n) (ms : Fin n → Msg T) : Msg T :=
  Structure.funMap (L := F.lang) f ms

/-- Two-argument constructors, written with `![a, b]`. -/
theorem realize_func₂ (v : ℕ → Msg T) (f : F 2) (s t : Term F) :
    (Term.func f ![s, t]).realize v = app f ![s.realize v, t.realize v] := by
  rw [Term.realize_func]
  exact congrArg _ (funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩))

/-- Constants, written with `![]`. -/
theorem realize_func₀ (v : ℕ → Msg T) (f : F 0) :
    (Term.func (L := F.lang) f ![]).realize v = app f ![] := by
  rw [Term.realize_func]
  exact congrArg _ (funext fun i => i.elim0)

end Msg

/-- Every instance of an equation holds in the messages. -/
theorem Theory.realize_eq (T : Theory F) {l r : Term F} (h : (l, r) ∈ T.E) (v : ℕ → Msg T) :
    l.realize v = r.realize v := by
  have hv : v = fun n => ⟦(v n).out⟧ := funext fun n => (Quotient.out_eq _).symm
  rw [hv, Term.realize_quotient_mk', Term.realize_quotient_mk']
  exact Quotient.sound (Eqv.ax h _)

/-! ## Views -/

/-- What a destructor can see of a message: its head and arguments when the head is
a free symbol, and `other` otherwise. -/
inductive View (T : Theory F) : Type
  | name (n : ℕ)
  | app {n : ℕ} (f : F n) (args : Fin n → Msg T)
  | other

/-- The view of a raw term. -/
def Theory.view (T : Theory F) : Term F → View T
  | .var n => .name n
  | .func f ts => if T.free _ f then .app f fun i => ⟦ts i⟧ else .other

theorem Term.Rigid.view_realize {t : Term F} (h : t.Rigid T.free) (σ : ℕ → Term F) :
    T.view (t.realize σ) = .other := by
  cases t with
  | var => exact h.elim
  | func f ts => simp [Theory.view, show T.free _ f = false from h]

/-- Equal terms have the same view: the free symbols are free. -/
theorem Theory.view_congr {s t : Term F} (h : Eqv T s t) : T.view s = T.view t := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | func f h _ =>
    simp only [Theory.view]
    split_ifs
    · exact congrArg _ (funext fun i => Quotient.sound (h i))
    · rfl
  | ax hE σ => rw [(T.heads _ hE).1.view_realize, (T.heads _ hE).2.view_realize]

namespace Msg

/-- The view of a message. -/
def view : Msg T → View T := Quotient.lift T.view fun _ _ h => T.view_congr h

@[simp] theorem view_name (n : ℕ) : (name n : Msg T).view = .name n := rfl

@[simp] theorem view_app {n : ℕ} (f : F n) (ms : Fin n → Msg T) :
    (app f ms).view = if T.free _ f then .app f ms else .other := by
  have hm : ms = fun i => ⟦(ms i).out⟧ := funext fun i => (Quotient.out_eq _).symm
  rw [hm, app, funMap_quotient_mk']
  rfl

theorem name_inj {n m : ℕ} (h : (name n : Msg T) = name m) : n = m :=
  View.name.inj (congrArg view h)

end Msg

/-! ## Public operations -/

/-- The symbols and destructors the attacker may apply. -/
class Pub (T : Theory F) where
  /-- The public constructors. -/
  pubFun : ∀ n, Set (F n)
  /-- The public destructors, each of some arity. -/
  dtors : Set (Σ n, (Fin n → Msg T) → Option (Msg T))

/-- The attacker's operations, each giving the set of its results. -/
def Pub.ops (T : Theory F) [Pub T] : Set (Σ n, (Fin n → Msg T) → Set (Msg T)) :=
  (⋃ n, (fun f : F n => (⟨n, fun ms => {Msg.app f ms}⟩ : Σ n, (Fin n → Msg T) → Set (Msg T)))
    '' Pub.pubFun (T := T) n) ∪
  (fun d : Σ n, (Fin n → Msg T) → Option (Msg T) =>
    (⟨d.1, fun ms => {r | d.2 ms = some r}⟩ : Σ n, (Fin n → Msg T) → Set (Msg T)))
    '' Pub.dtors (T := T)

end ProVerif
