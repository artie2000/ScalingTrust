/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Quotient
import Mathlib.ModelTheory.Quotients

/-!
# Message algebras from ProVerif declarations

ProVerif's terms modulo its equational theory (manual, Appendix B; survey §2.1 and
§2.5.1), built from the declarations of a model, types erased:

* `free a` and `fun`/`const` declarations give a signature `F : Sig`, the free names
  being nullary constructors.  Raw terms are the terms of that first-order language
  (Mathlib's `FirstOrder.Language.Term`) whose variables, `Theory.Msg.name n`, are the
  nonces that `new` creates.
* `equation` declarations give a `Theory`: the equations `E`, and the symbols
  declared *free*, those at the root of no equation.  Messages `T.Msg` are terms
  modulo the congruence `Eqv` that `E` generates, so Lean's `=` on messages is
  ProVerif's `=_E`, and every instance of an equation is an equality of messages
  (`Theory.satisfies_msg`).
* A `reduc` declaration gives a destructor: a Lean function to `Option T.Msg`,
  `none` being `fail`, that matches on `Theory.Msg.view` with one branch per rewrite rule in
  order and a final `none`.  A nested pattern over a free symbol is a nested match, a
  repeated variable an equality test.  A rule may match `fail` (p. 14), with a may-fail
  variable as `and(x, u) → false` does (p. 17) or with the constant itself as the
  manual's `catchfail(fail) → c0` does (§4.2.1), so destructors take may-fail
  arguments, `Option T.Msg`; one whose rules do neither is written on messages and
  lifted by `liftFail`.
* Tuples and booleans are built in whatever a model declares: `Data.lean` adds their
  symbols to a signature and carries a theory across, so that the messages of a model
  are `T.withData.Msg`, with the standard operations `StdOps`.
* The public declarations give the attacker of the model, `Attacker.ofDecls` in
  `Security.lean`: the operations it may apply on the messages.

`Theory.Msg.view` shows a message's head symbol and arguments when the symbol is free, and
nothing otherwise; since every equation has a non-free symbol at the root of both
sides (`Theory.heads`), the view is invariant under `E` (`Theory.view_congr`).

A predicate on messages, such as "the secret occurs only under a hash", must be
invariant under `E`; `Theory.Satisfies.lift` gives one from any structure that satisfies the
equations, by the universal property of the quotient.

## Deviation from the formal semantics

The manual's Figure B.1, as the survey (p. 31), applies a rewrite rule when the
arguments are equal *modulo `E`* to an instance of its left-hand side, and since
several instances may give different results, rewriting is a relation.  Here a
destructor is a function on the quotient,
defined by matching on the view, so it can only inspect the free symbols.  That is
the survey's condition for pattern-matching on data constructors (p. 35):
`f(M₁, …, Mₙ) =_E M'` exactly when `M'` is `f(M'₁, …, M'ₙ)` with `Mᵢ =_E M'ᵢ`.  Under
it, matching modulo `E` is matching on any representative, evaluation is a
function, and the two semantics agree.  A destructor whose pattern mentions an
equated symbol cannot be written.
-/

namespace ProVerif.TraceSemantics

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

variable {M : Type} [F.lang.Structure M]

/-- Substituting, then evaluating, is evaluating in the composite valuation. -/
theorem Term.realize_realize (σ : ℕ → Term F) (v : ℕ → M) (t : Term F) :
    (t.realize σ).realize v = t.realize fun n => (σ n).realize v := by
  induction t with
  | var => rfl
  | func f ts ih => simp [Term.realize_func, ih]

/-- Two-argument constructors, written with `![a, b]`. -/
theorem Term.realize_func₂ (v : ℕ → M) (f : F 2) (s t : Term F) :
    (Term.func f ![s, t]).realize v =
      Structure.funMap (L := F.lang) f ![s.realize v, t.realize v] := by
  rw [Term.realize_func]
  exact congrArg _ (funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩))

/-- Constants, written with `![]`. -/
theorem Term.realize_func₀ (v : ℕ → M) (f : F 0) :
    (Term.func (L := F.lang) f ![]).realize v = Structure.funMap (L := F.lang) f ![] := by
  rw [Term.realize_func]
  exact congrArg _ (funext fun i => i.elim0)

/-- Constructors of any arity, as a composition, so that `comp_vecCons` and `comp_vecEmpty`
evaluate the arguments of a vector `![…]` one by one; the translated equation theorems
use the three. -/
theorem Term.realize_func_comp (v : ℕ → M) {n : ℕ} (f : F n) (ts : Fin n → Term F) :
    (Term.func f ts).realize v = Structure.funMap (L := F.lang) f (Term.realize v ∘ ts) :=
  Term.realize_func _ _ _

theorem comp_vecCons {α β : Type} {n : ℕ} (g : α → β) (a : α) (f : Fin n → α) :
    g ∘ Matrix.vecCons a f = Matrix.vecCons (g a) (g ∘ f) :=
  Fin.comp_cons g a f

theorem comp_vecEmpty {α β : Type} (g : α → β) : g ∘ (![] : Fin 0 → α) = ![] :=
  funext fun i => i.elim0

/-- `<|>` on `Option`, as a translated destructor with several rules chains them: the
first rule that applies decides. -/
theorem orElse_eq_some {α : Type} (a b : Option α) (c : α) :
    (a <|> b) = some c ↔ a = some c ∨ (a = none ∧ b = some c) := by
  cases a <;> simp

theorem join_eq_some {α : Type} (o : Option (Option α)) (c : α) :
    o.join = some c ↔ o = some (some c) := by
  cases o <;> simp

/-- The root of `t` is a symbol that `free` does not declare free. -/
def Term.Rigid (free : ∀ n, F n → Bool) : Term F → Prop
  | .var _ => False
  | .func f _ => free _ f = false

/-- An equational theory, from a model's `equation` declarations: the equations, and
the symbols declared free, which no equation has at its root. -/
structure Theory (F : Sig) where
  /-- The equations. -/
  E : Set (Term F × Term F)
  /-- The symbols that destructors may match on: in a translated model, every symbol
  at the root of no equation. -/
  free : ∀ n, F n → Bool
  /-- Both sides of every equation have a non-free root. -/
  heads : ∀ e ∈ E, e.1.Rigid free ∧ e.2.Rigid free

variable {T : Theory F}

/-- `M` satisfies the equations of `T`. -/
def Theory.Satisfies (T : Theory F) (M : Type) [F.lang.Structure M] : Prop :=
  ∀ e ∈ T.E, ∀ v : ℕ → M, e.1.realize v = e.2.realize v

/-- Equality modulo `E`: the least congruence containing every instance of an
equation. -/
inductive Eqv (T : Theory F) : Term F → Term F → Prop
  | refl (t) : Eqv T t t
  | symm {s t} : Eqv T s t → Eqv T t s
  | trans {r s t} : Eqv T r s → Eqv T s t → Eqv T r t
  | func {n} (f : F n) {a b : Fin n → Term F} : (∀ i, Eqv T (a i) (b i)) →
      Eqv T (.func f a) (.func f b)
  | ax {l r} : (l, r) ∈ T.E → ∀ σ : ℕ → Term F, Eqv T (l.realize σ) (r.realize σ)

/-- Equal terms evaluate equally in a structure satisfying the equations. -/
theorem Eqv.realize_eq (hM : T.Satisfies M) (v : ℕ → M) {s t : Term F} (h : Eqv T s t) :
    s.realize v = t.realize v := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | func f _ ih =>
    simp only [Term.realize_func]
    exact congrArg _ (funext ih)
  | ax hE σ =>
    rw [Term.realize_realize, Term.realize_realize]
    exact hM _ hE _

/-- Terms modulo `E`. -/
def Theory.setoid (T : Theory F) : Setoid (Term F) := ⟨Eqv T, ⟨.refl, .symm, .trans⟩⟩

/-- The congruence respects the constructors, so the quotient is a structure. -/
instance : F.lang.Prestructure T.setoid where
  toStructure := inferInstance
  fun_equiv _ _ h := Eqv.func _ h
  rel_equiv := fun {_} {r} _ _ _ => r.elim

/-- Messages: terms modulo `E`. -/
abbrev Theory.Msg (T : Theory F) : Type := Quotient T.setoid

namespace Theory.Msg

/-- The `n`-th nonce created by `new`. -/
def name (n : ℕ) : T.Msg := ⟦.var n⟧

/-- Apply a constructor to messages. -/
abbrev app {n : ℕ} (f : F n) (ms : Fin n → T.Msg) : T.Msg :=
  Structure.funMap (L := F.lang) f ms

theorem app_mk {n : ℕ} (f : F n) (ts : Fin n → Term F) :
    app f (fun i => (⟦ts i⟧ : T.Msg)) = ⟦.func f ts⟧ :=
  funMap_quotient_mk' (L := F.lang) T.setoid f ts

end Theory.Msg

/-- The universal property: a structure satisfying the equations receives the
messages, by evaluating any representative. -/
def Theory.Satisfies.lift (hM : T.Satisfies M) (v : ℕ → M) : T.Msg → M :=
  Quotient.lift (Term.realize v) fun _ _ h => h.realize_eq hM v

@[simp] theorem Theory.Satisfies.lift_app (hM : T.Satisfies M) (v : ℕ → M) {n : ℕ} (f : F n)
    (ms : Fin n → T.Msg) :
    hM.lift v (.app f ms) = Structure.funMap (L := F.lang) f fun i => hM.lift v (ms i) := by
  induction ms using Quotient.induction_on_pi with
  | h ts => exact (Msg.app_mk f ts).symm ▸ Term.realize_func _ _ _

/-- The messages satisfy the equations. -/
theorem Theory.satisfies_msg (T : Theory F) : T.Satisfies T.Msg := by
  intro e he v
  have hv : v = fun n => ⟦(v n).out⟧ := funext fun n => (Quotient.out_eq _).symm
  rw [hv, Term.realize_quotient_mk', Term.realize_quotient_mk']
  exact Quotient.sound (Eqv.ax he _)

/-! ## Views -/

/-- What a destructor can see of a message: its head and arguments when the head is
a free symbol, and `other` otherwise. -/
inductive View (T : Theory F) : Type
  | name (n : ℕ)
  | app {n : ℕ} (f : F n) (args : Fin n → T.Msg)
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

namespace Theory.Msg

/-- The view of a message. -/
def view : T.Msg → View T := Quotient.lift T.view fun _ _ h => T.view_congr h

@[simp] theorem view_app {n : ℕ} (f : F n) (ms : Fin n → T.Msg) :
    (app f ms).view = if T.free _ f then .app f ms else .other := by
  induction ms using Quotient.induction_on_pi with
  | h ts => rw [app_mk]; rfl

theorem name_inj {n m : ℕ} (h : (name n : T.Msg) = name m) : n = m :=
  View.name.inj (congrArg view h)

/-- A message whose view is `app f a` is `app f a`: the inversion principle behind
destructors. -/
theorem eq_app_of_view (m : T.Msg) {n : ℕ} {f : F n} {a : Fin n → T.Msg}
    (h : m.view = .app f a) : m = app f a := by
  induction m using Quotient.inductionOn with
  | h t =>
    cases t with
    | var k => cases h
    | func g ts =>
      change T.view (.func g ts) = _ at h
      simp only [Theory.view] at h
      split_ifs at h
      cases h
      exact (app_mk _ ts).symm

/-- `eq_app_of_view` with the arguments given one by one: how the graph theorem of a
translated destructor recovers an argument from its view. -/
theorem eq_app_of_view' (m : T.Msg) {n : ℕ} {f : F n} {a b : Fin n → T.Msg}
    (h : m.view = .app f a) (hb : ∀ i, a i = b i) : m = app f b :=
  (m.eq_app_of_view h).trans (congrArg _ (funext hb))

end Theory.Msg

/-! ## May-fail arguments -/

/-- A function of `n` arguments, lifted to may-fail arguments: it fails as soon as one
of them does.  Constructors evaluate this way (manual, Figure B.1; survey p. 26), and so
do destructors whose rules have neither a may-fail variable nor the pattern `fail`, since
`fail` never instantiates an ordinary variable (survey p. 20). -/
def liftFail {α β : Type} {n : ℕ} (f : (Fin n → α) → Option β) (a : Fin n → Option α) :
    Option β :=
  if h : ∀ i, (a i).isSome then f fun i => (a i).get (h i) else none

theorem liftFail_eq_some {α β : Type} {n : ℕ} {f : (Fin n → α) → Option β}
    {a : Fin n → Option α} {r : β} :
    liftFail f a = some r ↔ ∃ ms, (∀ i, a i = some (ms i)) ∧ f ms = some r := by
  unfold liftFail
  split_ifs with h
  · refine ⟨fun hr => ⟨_, fun i => (Option.some_get (h i)).symm, hr⟩, ?_⟩
    rintro ⟨ms, hms, hr⟩
    rwa [show (fun i => (a i).get (h i)) = ms from
      funext fun i => Option.some_injective _ ((Option.some_get _).trans (hms i))]
  · exact iff_of_false (by simp) fun ⟨ms, hms, _⟩ => h fun i => by rw [hms i]; rfl

/-- A constant has no argument that could fail. -/
theorem liftFail_zero {α β : Type} (f : (Fin 0 → α) → Option β) (a : Fin 0 → Option α) :
    liftFail f a = f fun i => i.elim0 := by
  rw [liftFail, dif_pos fun i => i.elim0]
  exact congrArg f (funext fun i => i.elim0)

end ProVerif.TraceSemantics
