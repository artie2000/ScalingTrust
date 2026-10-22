/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.TraceSemantics.Attack

/-!
# Queries

The properties that ProVerif's correspondence queries state, read on the attacks of a
process (manual §4.3.1).  A query `F₁ && … && Fₙ ==> H` has facts before its arrow and a
hypothesis `H` after it, built from facts with `&&`, `||`, `false` and nested
correspondences `F ==> H`; an event fact may be injective.  Its facts hold at *steps* of a
trace: an action fact at the step that performs the action, a knowledge fact at every step
after which the attacker knows the message, and `F before e` at the steps where `F` holds
and the event `e` has not yet occurred, which states a fact of a phase once phases are
compiled out.  The query holds of a trace when, for every substitution and every choice of
steps at which the facts before the arrow hold, some instance of the hypothesis is
witnessed by steps no later than the last of them: a fact at such a step, and a nested
correspondence by a step of its own fact, before which its hypothesis is witnessed in
turn.  An injective fact of the hypothesis must be witnessed by distinct steps for distinct
tuples of steps of the injective facts before the arrow.

The definitions are generic in the facts, so that the specification of ProVerif's calculus
states the same semantics for its own facts; `QFact` and `QFact.HoldsAt` are the facts of
the trace semantics, and `Proc.Satisfies` the property of a process.  For the basic queries,
one fact before the arrow and a fact or `false` after it, the property is `Proc.Corr` or
`Proc.Secret` of `Security.lean`.  A query is refuted on an attack by `Query.not_sat`, with
`Hyp.Refuted` saying that no witness of the hypothesis exists.
-/

namespace ProVerif.TraceSemantics

open Descriptive
open Attacker (derive)

variable {M : Type}

/-! ## Hypotheses and queries -/

/-- The hypothesis of a correspondence over the facts `Φ`: a fact, injective or not; a
conjunction; a disjunction; `false`; or a nested correspondence `F ==> H`, whose fact may be
injective. -/
inductive Hyp (Φ : Type) where
  | fact (inj : Bool) (F : Φ)
  | and (H₁ H₂ : Hyp Φ)
  | or (H₁ H₂ : Hyp Φ)
  | false
  | corr (inj : Bool) (F : Φ) (H : Hyp Φ)

/-- A query: the facts before the arrow, each marked if injective, and the hypothesis after
it. -/
structure Query (Φ : Type) where
  premise : List (Bool × Φ)
  concl : Hyp Φ

namespace Hyp

variable {Φ Ψ : Type}

def map (f : Φ → Ψ) : Hyp Φ → Hyp Ψ
  | .fact inj F => .fact inj (f F)
  | .and H₁ H₂ => .and (H₁.map f) (H₂.map f)
  | .or H₁ H₂ => .or (H₁.map f) (H₂.map f)
  | .false => .false
  | .corr inj F H => .corr inj (f F) (H.map f)

/-- The paths to the injective facts: `false` descends left in a conjunction or a
disjunction, `true` right, and into the hypothesis of a nested correspondence, whose own fact
is at the empty path. -/
def injPaths : Hyp Φ → List (List Bool)
  | .fact inj _ => if inj then [[]] else []
  | .and H₁ H₂ | .or H₁ H₂ =>
    H₁.injPaths.map (Bool.false :: ·) ++ H₂.injPaths.map (Bool.true :: ·)
  | .false => []
  | .corr inj _ H => (if inj then [[]] else []) ++ H.injPaths.map (Bool.true :: ·)

/-- The facts of a hypothesis, those of its nested correspondences included. -/
def facts : Hyp Φ → List Φ
  | .fact _ F => [F]
  | .and H₁ H₂ | .or H₁ H₂ => H₁.facts ++ H₂.facts
  | .false => []
  | .corr _ F H => F :: H.facts

end Hyp

def Query.map {Φ Ψ : Type} (f : Φ → Ψ) (q : Query Φ) : Query Ψ :=
  ⟨q.premise.map fun F => (F.1, f F.2), q.concl.map f⟩

/-- A witness of a hypothesis: a step for each fact, a side for each disjunction. -/
inductive Wit where
  | fact (j : ℕ)
  | and (w₁ w₂ : Wit)
  | orL (w : Wit)
  | orR (w : Wit)
  | corr (j : ℕ) (w : Wit)

/-- The step chosen for the fact at a path, if the witness has one there. -/
def Wit.pos : Wit → List Bool → Option ℕ
  | .fact j, [] => some j
  | .and w₁ _, false :: p => w₁.pos p
  | .and _ w₂, true :: p => w₂.pos p
  | .orL w, false :: p => w.pos p
  | .orR w, true :: p => w.pos p
  | .corr j _, [] => some j
  | .corr _ w, true :: p => w.pos p
  | _, _ => none

section sat

variable {A S : Type}

/-- The witness `w` shows the hypothesis `H` by step `d`, `holdsAt F i` saying that the
fact `F` holds at step `i`: a fact at a step no later than `d`, and a nested correspondence
at a step `j ≤ d` of its fact, before which its hypothesis is witnessed. -/
def Hyp.Sat (holdsAt : A → ℕ → Prop) : Hyp A → Wit → ℕ → Prop
  | .fact _ F, .fact j, d => j ≤ d ∧ holdsAt F j
  | .and H₁ H₂, .and w₁ w₂, d => H₁.Sat holdsAt w₁ d ∧ H₂.Sat holdsAt w₂ d
  | .or H₁ _, .orL w, d => H₁.Sat holdsAt w d
  | .or _ H₂, .orR w, d => H₂.Sat holdsAt w d
  | .corr _ F H, .corr j w, d => j ≤ d ∧ holdsAt F j ∧ H.Sat holdsAt w j
  | _, _, _ => False

/-- No witness shows `H` by step `d`: a fact holds at no step up to `d`, a side of a
conjunction or both sides of a disjunction are refuted, and a nested correspondence has its
hypothesis refuted at every step up to `d` at which its fact holds. -/
def Hyp.Refuted (holdsAt : A → ℕ → Prop) : Hyp A → ℕ → Prop
  | .fact _ F, d => ∀ j ≤ d, ¬ holdsAt F j
  | .and H₁ H₂, d => H₁.Refuted holdsAt d ∨ H₂.Refuted holdsAt d
  | .or H₁ H₂, d => H₁.Refuted holdsAt d ∧ H₂.Refuted holdsAt d
  | .false, _ => True
  | .corr _ F H, d => ∀ j ≤ d, holdsAt F j → H.Refuted holdsAt j

theorem Hyp.Refuted.not_sat {holdsAt : A → ℕ → Prop} {H : Hyp A} {d : ℕ}
    (h : H.Refuted holdsAt d) (w : Wit) : ¬ H.Sat holdsAt w d := by
  induction H generalizing w d with
  | fact inj F =>
    cases w with
    | fact j => exact fun ⟨hj, hF⟩ => h j hj hF
    | _ => exact id
  | and H₁ H₂ ih₁ ih₂ =>
    cases w with
    | and w₁ w₂ => exact fun ⟨h₁, h₂⟩ => h.elim (fun h => ih₁ h w₁ h₁) fun h => ih₂ h w₂ h₂
    | _ => exact id
  | or H₁ H₂ ih₁ ih₂ =>
    cases w with
    | orL w => exact ih₁ h.1 w
    | orR w => exact ih₂ h.2 w
    | _ => exact id
  | false => cases w <;> exact id
  | corr inj F H ih =>
    cases w with
    | corr j w => exact fun ⟨hj, hF, hH⟩ => ih (h j hj hF) w hH
    | _ => exact id

/-- A hypothesis none of whose facts holds at any step is refuted. -/
theorem Hyp.Refuted.of_facts {holdsAt : A → ℕ → Prop} {H : Hyp A}
    (h : ∀ F ∈ H.facts, ∀ j, ¬ holdsAt F j) (d : ℕ) : H.Refuted holdsAt d := by
  induction H generalizing d with
  | fact inj F => exact fun j _ => h F (List.mem_singleton.2 rfl) j
  | and H₁ H₂ ih₁ _ => exact .inl (ih₁ (fun F hF => h F (List.mem_append_left _ hF)) d)
  | or H₁ H₂ ih₁ ih₂ =>
    exact ⟨ih₁ (fun F hF => h F (List.mem_append_left _ hF)) d,
      ih₂ (fun F hF => h F (List.mem_append_right _ hF)) d⟩
  | false => trivial
  | corr inj F H ih => exact fun j _ hF => (h F List.mem_cons_self j hF).elim

namespace Query

variable (holdsAt : A → ℕ → Prop) (n : ℕ) (q : Query (S → A))

/-- The facts before the arrow hold under `σ` at the steps `ps`, within the `n` steps. -/
def Valid (σ : S) (ps : List ℕ) : Prop :=
  List.Forall₂ (fun (F : Bool × (S → A)) p => p ≤ n ∧ holdsAt (F.2 σ) p) q.premise ps

/-- The steps of the injective facts before the arrow. -/
def injPos (ps : List ℕ) : List ℕ :=
  ((q.premise.zip ps).filter (·.1.1)).map (·.2)

/-- A trace of `n` steps satisfies the query: for every `σ` and steps `ps` at which the facts
before the arrow hold, some `σ'` giving them the same instances has the hypothesis
witnessed by the last of the steps, and an injective fact of the hypothesis is witnessed at
distinct steps for distinct tuples of steps of the injective facts before the arrow. -/
def Sat : Prop :=
  ∃ w : (σ : S) → (ps : List ℕ) → q.Valid holdsAt n σ ps → Wit,
    (∀ σ ps (hv : q.Valid holdsAt n σ ps), ∃ σ' : S, (∀ F ∈ q.premise, F.2 σ' = F.2 σ) ∧
      (q.concl.map (· σ')).Sat holdsAt (w σ ps hv) (ps.foldr max 0)) ∧
    ∀ π ∈ q.concl.injPaths, ∀ σ₁ ps₁ (hv₁ : q.Valid holdsAt n σ₁ ps₁) σ₂ ps₂
      (hv₂ : q.Valid holdsAt n σ₂ ps₂) j, (w σ₁ ps₁ hv₁).pos π = some j →
        (w σ₂ ps₂ hv₂).pos π = some j → q.injPos ps₁ = q.injPos ps₂

/-- Satisfaction depends on the facts only through where they hold. -/
theorem sat_congr {holdsAt' : A → ℕ → Prop} (h : ∀ F i, holdsAt F i ↔ holdsAt' F i) :
    q.Sat holdsAt n ↔ q.Sat holdsAt' n := by
  have hv : ∀ σ ps, q.Valid holdsAt n σ ps ↔ q.Valid holdsAt' n σ ps := fun σ ps =>
    ⟨fun hv => hv.imp fun F p hp => ⟨hp.1, (h _ _).1 hp.2⟩,
      fun hv => hv.imp fun F p hp => ⟨hp.1, (h _ _).2 hp.2⟩⟩
  have hs : ∀ (H : Hyp A) (w : Wit) (d : ℕ), H.Sat holdsAt w d ↔ H.Sat holdsAt' w d := by
    intro H
    induction H with
    | fact inj F => intro w d; cases w <;> simp [Hyp.Sat, h]
    | and H₁ H₂ ih₁ ih₂ => intro w d; cases w <;> simp [Hyp.Sat, ih₁, ih₂]
    | or H₁ H₂ ih₁ ih₂ => intro w d; cases w <;> simp [Hyp.Sat, ih₁, ih₂]
    | false => intro w d; cases w <;> simp [Hyp.Sat]
    | corr inj F H ih => intro w d; cases w <;> simp [Hyp.Sat, h, ih]
  constructor
  · rintro ⟨w, h₁, h₂⟩
    refine ⟨fun σ ps hv' => w σ ps ((hv σ ps).2 hv'), fun σ ps hv' => ?_,
      fun π hπ σ₁ ps₁ hv₁ σ₂ ps₂ hv₂ j => h₂ π hπ σ₁ ps₁ _ σ₂ ps₂ _ j⟩
    obtain ⟨σ', hσ', hs'⟩ := h₁ σ ps ((hv σ ps).2 hv')
    exact ⟨σ', hσ', (hs _ _ _).1 hs'⟩
  · rintro ⟨w, h₁, h₂⟩
    refine ⟨fun σ ps hv' => w σ ps ((hv σ ps).1 hv'), fun σ ps hv' => ?_,
      fun π hπ σ₁ ps₁ hv₁ σ₂ ps₂ hv₂ j => h₂ π hπ σ₁ ps₁ _ σ₂ ps₂ _ j⟩
    obtain ⟨σ', hσ', hs'⟩ := h₁ σ ps ((hv σ ps).1 hv')
    exact ⟨σ', hσ', (hs _ _ _).2 hs'⟩

/-- The query fails of a trace of `n` steps when, under some `σ`, the facts before the arrow
hold at steps `ps` and no `σ'` giving them the same instances has the hypothesis witnessed
by the last of those steps. -/
theorem not_sat (σ : S) (ps : List ℕ) (hv : q.Valid holdsAt n σ ps)
    (h : ∀ σ', (∀ F ∈ q.premise, F.2 σ' = F.2 σ) →
      (q.concl.map (· σ')).Refuted holdsAt (ps.foldr max 0)) :
    ¬ q.Sat holdsAt n := by
  rintro ⟨w, hw, -⟩
  obtain ⟨σ', hσ', hs⟩ := hw σ ps hv
  exact (h σ' hσ').not_sat _ hs

end Query

end sat

/-! ## The facts of the trace semantics -/

/-- A fact of a query: an event executed, a message known to the attacker, a message
communicated on a channel, or a fact before the first occurrence of an event. -/
inductive QFact (M : Type) where
  | event (e : M)
  | knows (m : M)
  | mess (c m : M)
  | before (F : QFact M) (e : M)

/-- The facts of `Security.lean`, as facts of a query. -/
def Fact.toQ : Fact M → QFact M
  | .event e => .event e
  | .knows m => .knows m

theorem Fact.toQ_injective : Function.Injective (Fact.toQ (M := M)) := by
  rintro (_ | _) (_ | _) h <;> simp [toQ] at h <;> simp [h]

variable [Attacker M]

/-- The fact holds at step `i` of `t`, the `i`-th action being `t[i-1]`: an action fact when
that action is the action, a knowledge fact when the attacker knows the message after the
first `i` actions, and `F before e` when `F` holds and no action so far is the event `e`. -/
def QFact.HoldsAt (t : Trace M) : QFact M → ℕ → Prop
  | .event e, i => 0 < i ∧ t[i - 1]? = some (.event e)
  | .mess c m, i => 0 < i ∧ t[i - 1]? = some (.comm c m)
  | .knows m, i => m ∈ Trace.attackerKnowledge (derive ∅) (t.take i)
  | .before F e, i => F.HoldsAt t i ∧ Act.event e ∉ t.take i

/-- An event absent from `t` holds at no step. -/
theorem QFact.not_holdsAt_event {t : Trace M} {e : M} (h : Act.event e ∉ t) (j : ℕ) :
    ¬ (QFact.event e).HoldsAt t j :=
  fun hj => h (List.mem_iff_getElem?.2 ⟨_, hj.2⟩)

/-- The property that a query states of `P`: every attack satisfies the query, whose facts
are functions of a valuation of the query's variables `X`. -/
def Proc.Satisfies [Names M] (P : Proc M) {X : Type} (q : Query ((X → M) → QFact M)) : Prop :=
  ∀ t ∈ P.Attacks, q.Sat (QFact.HoldsAt t) t.length

/-! ## The basic queries

One fact before the arrow and a fact or `false` after it: `Proc.Corr` and `Proc.Secret`. -/

theorem Trace.attackerKnowledge_append (K : Set M) (t t' : Trace M) :
    (t ++ t').attackerKnowledge K = Trace.attackerKnowledge (t.attackerKnowledge K) t' :=
  List.foldl_append ..

/-- What the attacker knows after a prefix it knows after the trace. -/
theorem Trace.attackerKnowledge_take_subset (K : Set M) (t : Trace M) (i : ℕ) :
    Trace.attackerKnowledge K (t.take i) ⊆ t.attackerKnowledge K := by
  conv_rhs => rw [← List.take_append_drop i t]
  rw [attackerKnowledge_append]
  exact subset_attackerKnowledge _ _

/-- A fact holds after a trace exactly when, as a fact of a query, it holds at some step. -/
theorem Fact.holds_iff_holdsAt (t : Trace M) : ∀ F : Fact M,
    F.Holds t ↔ ∃ i ≤ t.length, F.toQ.HoldsAt t i
  | .event e => by
    simp only [Holds, toQ, QFact.HoldsAt, List.mem_iff_getElem?]
    constructor
    · rintro ⟨i, hi⟩
      have hlt := (List.getElem?_eq_some_iff.1 hi).1
      exact ⟨i + 1, by omega, Nat.succ_pos _, by simpa using hi⟩
    · rintro ⟨i, -, -, h⟩
      exact ⟨i - 1, h⟩
  | .knows m =>
    ⟨fun h => ⟨t.length, le_rfl, by simpa [Holds, toQ, QFact.HoldsAt] using h⟩,
      fun ⟨i, _, h⟩ => Trace.attackerKnowledge_take_subset _ _ _ h⟩

variable [Names M]

/-- `query F`, the query `F ==> false`: no instance of `F` holds after any attack. -/
theorem Proc.satisfies_false_iff (P : Proc M) {X : Type} (F : (X → M) → Fact M) :
    P.Satisfies ⟨[(false, fun σ => (F σ).toQ)], .false⟩ ↔
      ∀ σ, ∀ t ∈ P.Attacks, ¬ (F σ).Holds t := by
  constructor
  · rintro h σ t ht hF
    obtain ⟨i, hi, hF⟩ := (Fact.holds_iff_holdsAt t _).1 hF
    obtain ⟨w, hw, -⟩ := h t ht
    have hv : Query.Valid (QFact.HoldsAt t) t.length ⟨[(false, fun σ => (F σ).toQ)], .false⟩ σ [i] :=
      List.forall₂_cons.2 ⟨⟨hi, hF⟩, List.Forall₂.nil⟩
    obtain ⟨σ', -, hs⟩ := hw σ [i] hv
    cases w σ [i] hv <;> exact hs
  · intro h t ht
    refine ⟨fun _ _ _ => .fact 0, fun σ ps hv => ?_, fun π hπ => ?_⟩
    · obtain ⟨p, ps', ⟨hp, hF⟩, -, rfl⟩ := List.forall₂_cons_left_iff.1 hv
      exact absurd ((Fact.holds_iff_holdsAt t _).2 ⟨p, hp, hF⟩) (h σ t ht)
    · simp [Hyp.injPaths] at hπ

/-- `query attacker(M)`: secrecy. -/
theorem Proc.satisfies_secret_iff (P : Proc M) {X : Type} (s : (X → M) → M) :
    P.Satisfies ⟨[(false, fun σ => .knows (s σ))], .false⟩ ↔ ∀ σ, P.Secret (s σ) :=
  P.satisfies_false_iff fun σ => Fact.knows (s σ)

/-- `query F ==> H` with one fact on each side, neither injective: the correspondence of
`Security.lean`, when `P` is prefix-closed. -/
theorem Proc.satisfies_corr_iff {P : Proc M} (hP : P ∈ tree (Act M)) {X : Type}
    (F H : (X → M) → Fact M) :
    P.Satisfies ⟨[(false, fun σ => (F σ).toQ)], .fact false fun σ => (H σ).toQ⟩ ↔
      P.Corr F H := by
  constructor
  · intro h σ t ht hF
    obtain ⟨i, hi, hF⟩ := (Fact.holds_iff_holdsAt t _).1 hF
    obtain ⟨w, hw, -⟩ := h t ht
    have hv : Query.Valid (QFact.HoldsAt t) t.length
        ⟨[(false, fun σ => (F σ).toQ)], .fact false fun σ => (H σ).toQ⟩ σ [i] :=
      List.forall₂_cons.2 ⟨⟨hi, hF⟩, List.Forall₂.nil⟩
    obtain ⟨σ', hσ', hs⟩ := hw σ [i] hv
    refine ⟨σ', Fact.toQ_injective (hσ' _ (List.mem_singleton.2 rfl)), ?_⟩
    cases hw' : w σ [i] hv <;> simp only [hw', Hyp.map, Hyp.Sat] at hs
    obtain ⟨hj, hH⟩ := hs
    exact (Fact.holds_iff_holdsAt t _).2 ⟨_, by simp at hj; omega, hH⟩
  · intro h t ht
    have key : ∀ σ ps, Query.Valid (QFact.HoldsAt t) t.length
        ⟨[(false, fun σ => (F σ).toQ)], .fact false fun σ => (H σ).toQ⟩ σ ps →
        ∃ j, j ≤ ps.foldr max 0 ∧ ∃ σ', (H σ').toQ.HoldsAt t j ∧ F σ' = F σ := by
      intro σ ps hv
      obtain ⟨p, ps', ⟨hp, hF⟩, hnil, rfl⟩ := List.forall₂_cons_left_iff.1 hv
      obtain rfl := List.forall₂_nil_left_iff.1 hnil
      have hpre : t.take p ∈ P.Attacks :=
        Tree.mem_of_append (T := ⟨_, P.attacks_mem_tree hP⟩)
          (by rw [List.take_append_drop]; exact ht)
      have hF' : (F σ).Holds (t.take p) := by
        cases hFσ : F σ with
        | event e =>
          simp only [hFσ, Fact.toQ, QFact.HoldsAt] at hF
          exact List.mem_iff_getElem?.2 ⟨p - 1, by
            rw [List.getElem?_take_of_lt (by omega)]
            exact hF.2⟩
        | knows m => simpa [hFσ, Fact.toQ, QFact.HoldsAt, Fact.Holds] using hF
      obtain ⟨σ', hσ', hH⟩ := h σ _ hpre hF'
      obtain ⟨j, hj, hHj⟩ := (Fact.holds_iff_holdsAt _ _).1 hH
      have hjp : j ≤ p := hj.trans (List.length_take_le _ _)
      refine ⟨j, by simpa using hjp, σ', ?_, hσ'⟩
      cases hHσ : H σ' with
      | event e =>
        simp only [hHσ, Fact.toQ, QFact.HoldsAt] at hHj ⊢
        refine ⟨hHj.1, ?_⟩
        rw [List.getElem?_take_of_lt (by omega)] at hHj
        exact hHj.2
      | knows m =>
        simp only [hHσ, Fact.toQ, QFact.HoldsAt, List.take_take] at hHj ⊢
        rwa [min_eq_left hjp] at hHj
    refine ⟨fun σ ps hv => .fact (key σ ps hv).choose, fun σ ps hv => ?_, fun π hπ => ?_⟩
    · obtain ⟨hle, σ', hH', hσ'⟩ := (key σ ps hv).choose_spec
      refine ⟨σ', fun G hG => ?_, hle, hH'⟩
      rw [List.mem_singleton] at hG
      subst hG
      simp [hσ']
    · simp [Hyp.injPaths] at hπ

/-! ## Refuting a query -/

/-- A query with one fact before the arrow fails of the attack `t` in which an instance of
the fact holds at some step, when the hypothesis is refuted at every step under every `σ'`
giving the fact the same instance. -/
theorem Proc.not_satisfies_single {P : Proc M} {X : Type} {inj : Bool}
    {F : (X → M) → QFact M} {H : Hyp ((X → M) → QFact M)} {t : Trace M} (ht : t ∈ P.Attacks)
    (σ : X → M) (hF : ∃ i ≤ t.length, (F σ).HoldsAt t i)
    (h : ∀ σ', F σ' = F σ → ∀ d, (H.map (· σ')).Refuted (QFact.HoldsAt t) d) :
    ¬ P.Satisfies ⟨[(inj, F)], H⟩ := by
  obtain ⟨i, hi, hF⟩ := hF
  refine fun hP => Query.not_sat _ _ _ σ [i] ?_ ?_ (hP t ht)
  · exact List.forall₂_cons.2 ⟨⟨hi, hF⟩, .nil⟩
  · exact fun σ' hσ' => h σ' (hσ' _ (List.mem_singleton.2 rfl)) _

end ProVerif.TraceSemantics
