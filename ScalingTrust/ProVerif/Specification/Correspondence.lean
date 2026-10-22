/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.Specification.Attacks

/-!
# The correspondence with the operational semantics

The theorems of the write-up's §3.2 about attacks and queries, for a model `A` and a
closed process `P₀`; Adequacy is `ProVerif.Specification.Adequacy`.

* **Attacks** (`attacks_sound`, `attacks_complete`), the write-up's Theorem "Attacks": a
  trace of the manual's semantics against an adversary is an attack of the trace
  semantics, and an attack is a trace of the manual's semantics against some adversary.
* **Knowledge** (`Model.knows_iff`): the attacker of the calculus knows a message after a
  trace exactly when the attacker of the trace semantics does, both starting from nothing
  and adding what is communicated on a channel they derive; so the instance of a query
  fact holds at a step of a trace exactly when it does in the trace semantics
  (`Model.satisfiedAt_iff`).
* **Secrecy** (`secret_iff`) and **Correspondences** (`corr_iff`): the properties of the
  trace semantics are secrecy as ProVerif checks it, `Model.Preserves`, and the write-up's
  correspondences, `Model.Satisfies`.

The write-up's hypothesis that `P₀` and the secret mention no created name is not
needed: a created name is a nonce index that the `new` step and `Proc.new` may both create.
-/

namespace ProVerif.Specification

open FirstOrder FirstOrder.Language ProVerif.TraceSemantics
open Attacker (derive)

variable {F G Ev : Sig} (A : Model F G Ev)

/-! ## Attacks -/

/-- `A₀`, the attacks on the denotation of `P₀`. -/
abbrev Model.attacks (P₀ : Process F G Ev 0) : Proc A.Msg :=
  (P₀.denote finZeroElim).Attacks

/-- What the attacker of the trace semantics knows after the attack `t`. -/
abbrev Model.known (t : Trace A.Msg) : Set A.Msg :=
  t.attackerKnowledge (derive ∅)

/-- A trace of the manual's semantics against an adversary is an attack. -/
theorem attacks_sound (P₀ Q : Process F G Ev 0) (hQ : A.Adversary Q) {t : Trace A.Msg}
    (ht : A.ManualTrace (.against P₀ Q) t) : t ∈ A.attacks P₀ := by
  obtain ⟨hr, hcl⟩ := ht
  have hr' : Runs A ⟨∅, {P₀} + {Q}⟩ t := by
    rw [Multiset.singleton_add, ← Multiset.insert_eq_cons]
    exact hr
  obtain ⟨t₀, t₁, s, h₀, h₁, hs₀, hs₁, hc⟩ := Runs.split hr' rfl
  refine ⟨⟨⟨![t₀, t₁], s, Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨hs₀, hs₁⟩, hc⟩,
    (Runs.nonces hr').1⟩, hcl⟩
  · rw [denote_eq_traces]
    exact h₀
  · refine Runs.enemy h₁ fun P hP => ?_
    rw [Multiset.mem_singleton] at hP
    exact hP ▸ Model.Adversary.advK ∅ hQ

/-- An attack is a trace of the manual's semantics against some adversary. -/
theorem attacks_complete (P₀ : Process F G Ev 0) {t : Trace A.Msg} (ht : t ∈ A.attacks P₀) :
    ∃ Q, A.Adversary Q ∧ A.ManualTrace (.against P₀ Q) t := by
  obtain ⟨⟨⟨f, s, hf, hs, hc⟩, hn⟩, hcl⟩ := ht
  have h₀ : Runs A ⟨∅, {P₀}⟩ (f 0) := by
    have := hf 0
    rw [denote_eq_traces] at this
    exact this
  obtain ⟨Q, hQ, hrun⟩ :=
    Enemy.process (show Enemy ∅ (f 1) from hf 1) finZeroElim (Set.empty_subset _)
  have h₁ : Runs A ⟨∅, {Q}⟩ (f 1) := by
    have := hrun finZeroElim (funext fun i => i.elim0) ∅ fun _ _ => Finset.notMem_empty _
    rwa [Process.subst_finZero] at this
  refine ⟨Q, hQ, ?_, hcl⟩
  have := runs_add hc h₀ h₁ (hs 0) (hs 1) hn (fun _ _ => Finset.notMem_empty _)
    fun _ _ => Finset.notMem_empty _
  rw [Finset.union_empty, Multiset.singleton_add, ← Multiset.insert_eq_cons] at this
  exact this

/-! ## Knowledge -/

/-- The knowledge of the attacker of the calculus after a trace, closed under derivation, is
the knowledge of the attacker of the trace semantics: both start from nothing and add what
is communicated on a channel they derive. -/
theorem Model.derive_knowledge (t : Trace A.Msg) :
    derive (A.knowledge t) = t.attackerKnowledge (derive ∅) := by
  suffices h : ∀ S : Set A.Msg,
      derive (t.foldl (fun K a => K ∪ {m | ∃ c, a = .comm c m ∧ A.Derives K c}) S) =
        t.attackerKnowledge (derive S) from h ∅
  induction t with
  | nil => exact fun _ => rfl
  | cons a t ih =>
    intro S
    have hX : {m | ∃ c, a = Act.comm c m ∧ A.Derives S c} =
        {m | ∃ c, a = Act.comm c m ∧ c ∈ derive S} :=
      Set.ext fun _ => by simp only [Set.mem_ofPred_eq, Model.derives_iff_derive]
    have hS : derive (S ∪ {m | ∃ c, a = Act.comm c m ∧ c ∈ derive S}) =
        derive (derive S ∪ {m | ∃ c, a = Act.comm c m ∧ c ∈ derive S}) :=
      le_antisymm (derive.monotone (Set.union_subset_union_left _ (derive.le_closure S)))
        (derive.closure_min (Set.union_subset (derive.monotone Set.subset_union_left)
          (Set.subset_union_right.trans (derive.le_closure _))) (derive.isClosed_closure _))
    simp only [Trace.attackerKnowledge, List.foldl_cons]
    rw [ih, hX, hS]
    rfl

/-- The attacker of the calculus knows `m` after the trace `t` exactly when the attacker of
the trace semantics does. -/
theorem Model.knows_iff (t : Trace A.Msg) (m : A.Msg) :
    A.Knows t m ↔ (Fact.knows m).Holds t := by
  rw [Model.Knows, Model.derives_iff_derive, Model.derive_knowledge]
  exact Iff.rfl

/-- The instance of a query fact holds at a step of a trace exactly when it does in the
trace semantics. -/
theorem Model.satisfiedAt_iff (t : Trace A.Msg) :
    ∀ (f : QFact A.Msg) (i : ℕ), A.SatisfiedAt t f i ↔ f.HoldsAt t i
  | .event _, _ => Iff.rfl
  | .mess _ _, _ => Iff.rfl
  | .knows m, i => A.knows_iff (t.take i) m
  | .before f _, i => Iff.and (Model.satisfiedAt_iff t f i) Iff.rfl

/-! ## Secrecy and correspondences -/

/-- Secrecy: `query attacker(M)` holds of the denotation exactly when `P₀` preserves the
secrecy of `M`, the attacker of the trace semantics knowing `M` after an attack exactly when
the attacker of the calculus knows it after a trace against some adversary. -/
theorem secret_iff (P₀ : Process F G Ev 0) (M : Tm F Ev 0) :
    (P₀.denote finZeroElim).Secret (Tm.msg A M) ↔ A.Preserves P₀ M := by
  constructor
  · intro h Q hQ t ht hk
    exact h t (attacks_sound A P₀ Q hQ ht) ((A.knows_iff t _).1 hk)
  · intro h t ht hk
    obtain ⟨Q, hQ, ht'⟩ := attacks_complete A P₀ ht
    exact h Q hQ t ht' ((A.knows_iff t _).2 hk)

/-- Correspondences: `P₀` satisfies the query `q` against `N_pub`-adversaries exactly when
its denotation satisfies the query with the facts instantiated, which is what the
translation of the query states: a trace of the manual's semantics against an adversary is
an attack and conversely, and the instance of a query fact holds at a step of a trace
exactly when it does in the trace semantics. -/
theorem corr_iff (P₀ : Process F G Ev 0) {X : Type} (q : Query (QueryFact F Ev X)) :
    A.Satisfies P₀ q ↔
      (P₀.denote (A := A) finZeroElim).Satisfies (q.map fun Fq (σ : X → A.Msg) => Fq.inst σ) := by
  constructor
  · intro h t ht
    obtain ⟨Q, hQ, ht'⟩ := attacks_complete A P₀ ht
    exact (Query.sat_congr _ _ _ (A.satisfiedAt_iff t)).1 (h Q hQ t ht')
  · intro h Q hQ t ht
    exact (Query.sat_congr _ _ _ (A.satisfiedAt_iff t)).2 (h t (attacks_sound A P₀ Q hQ ht))

end ProVerif.Specification
