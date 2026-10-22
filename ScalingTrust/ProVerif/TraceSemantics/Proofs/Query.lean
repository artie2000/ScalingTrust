/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.TraceSemantics.Query

/-!
# Proving and refuting queries

* The basic queries, one fact before the arrow and a fact or `false` after it, are
  `Proc.Corr` and `Proc.Secret` of `Security.lean` (`Proc.satisfies_corr_iff`,
  `Proc.satisfies_secret_iff`), by `Fact.holds_iff_holdsAt`: a fact holds after a trace
  exactly when, as a fact of a query, it holds at some step.
* A query with one fact before the arrow is refuted on an attack by
  `Proc.not_satisfies_single`: an instance of the fact holds at some step, and
  `Hyp.Refuted` says that no witness of the hypothesis exists, which
  `Hyp.Refuted.of_facts` shows when none of its facts holds at any step, as
  `QFact.not_holdsAt_event` does of an event absent from the attack.
-/

namespace ProVerif.TraceSemantics

open Descriptive

variable {M : Type}

/-! ## Refuting a hypothesis -/

section

variable {A S : Type}

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

end

/-! ## The facts of the trace semantics, after a trace and at a step -/

theorem Fact.toQ_injective : Function.Injective (Fact.toQ (M := M)) := by
  rintro (_ | _) (_ | _) h <;> simp [toQ] at h <;> simp [h]

variable [Attacker M]

/-- An event absent from `t` holds at no step. -/
theorem QFact.not_holdsAt_event {t : Trace M} {e : M} (h : Act.event e ∉ t) (j : ℕ) :
    ¬ (QFact.event e).HoldsAt t j :=
  fun hj => h (List.mem_iff_getElem?.2 ⟨_, hj.2⟩)

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

/-! ## The basic queries

One fact before the arrow and a fact or `false` after it: `Proc.Corr` and `Proc.Secret`. -/

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

/-! ## Refuting a query on an attack -/

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
