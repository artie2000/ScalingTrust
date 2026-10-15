/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.Specification.Denotation

/-!
# The correspondence with the operational semantics

The theorems of the write-up's §2.2, for a model `A` and a closed process `P₀`.

* **Adequacy** (`denote_eq_traces`, `traces_add`): a closed process denotes its weak
  traces, and the weak traces of a union of multisets are the parallel composition of
  those of the parts.
* **Attacks** (`attacks_sound`, `attacks_complete`, `attacks_known`): a trace of the
  survey against an adversary has an attack of the trace semantics with the same
  created names and events in which the attacker knows whatever the trace outputs
  publicly; an attack has the same created names and events as a trace of the survey
  against some adversary; and whatever the attacker knows after an attack, some
  adversary outputs publicly at the end of such a trace.
* **Secrecy** (`secret_iff`) and **Correspondences** (`corr_iff`): the properties of the
  trace semantics are the survey's.  Both follow from the Attacks theorem.

Adequacy and the Attacks theorem are stated and not yet proved.  The write-up's
hypothesis that `P₀` and the secret mention no created name is not needed: a created
name is a nonce index that (Red Res) and `Proc.new` may both create.
-/

namespace ProVerif.Specification

open FirstOrder FirstOrder.Language ProVerif.TraceSemantics

variable {F G : Sig} (A : Model F G)

/-! ## Adequacy -/

/-- A closed process denotes its weak traces. -/
theorem denote_eq_traces (P : Process F G 0) :
    P.denote finZeroElim = Config.traces A ⟨∅, {P}⟩ := by
  sorry

/-- The weak traces of a union of multisets are the parallel composition of those of
its parts. -/
theorem traces_add (Ps Qs : Multiset (Process F G 0)) :
    Config.traces A ⟨∅, Ps + Qs⟩ =
      Proc.par (Config.traces A ⟨∅, Ps⟩) (Config.traces A ⟨∅, Qs⟩) := by
  sorry

/-! ## Attacks -/

/-- `A₀`, the attacks on the denotation of `P₀`. -/
abbrev Model.attacks (P₀ : Process F G 0) : Proc A.Msg :=
  (P₀.denote finZeroElim).Attacks A.alg.derive

/-- What the attacker knows after the attack `t`. -/
abbrev Model.known (t : Trace A.Msg) : Set A.Msg :=
  t.attackerKnowledge A.alg.derive (A.alg.derive ∅)

/-- The `new` and `event` actions of a trace: what a trace of the survey observes. -/
def obs {M : Type} (t : Trace M) : Trace M :=
  t.filter fun a => match a with | .new _ => true | .event _ => true | _ => false

theorem event_mem_obs {M : Type} {t : Trace M} {e : M} :
    Act.event e ∈ obs t ↔ Act.event e ∈ t := by
  simp [obs, List.mem_filter]

/-- (S): a trace of the survey against an adversary observes an attack in which the
attacker knows whatever the trace outputs publicly. -/
theorem attacks_sound (P₀ Q : Process F G 0) (hQ : A.Adversary Q) {t : Trace A.Msg}
    (ht : A.SurveyTrace (.against P₀ Q) t) :
    ∃ t' ∈ A.attacks P₀, obs t' = obs t ∧ ∀ m, A.OutputsPublicly t m → m ∈ A.known t' := by
  sorry

/-- (C): an attack is observed by a trace of the survey against some adversary. -/
theorem attacks_complete (P₀ : Process F G 0) {t : Trace A.Msg} (ht : t ∈ A.attacks P₀) :
    ∃ Q, A.Adversary Q ∧ ∃ t', A.SurveyTrace (.against P₀ Q) t' ∧ obs t' = obs t := by
  sorry

/-- (C): whatever the attacker knows after an attack, some adversary outputs publicly
at the last step of a trace observing the attack. -/
theorem attacks_known (hpub : A.Npub.Nonempty) (P₀ : Process F G 0) {t : Trace A.Msg}
    (ht : t ∈ A.attacks P₀) {m : A.Msg} (hm : m ∈ A.known t) :
    ∃ Q, A.Adversary Q ∧ ∃ t', A.SurveyTrace (.against P₀ Q) t' ∧ obs t' = obs t ∧
      ∃ a ∈ A.Npub, ∃ t'', t' = t'' ++ [Act.comm (Theory.Msg.app a ![]) m] := by
  sorry

/-! ## Secrecy and correspondences -/

/-- Secrecy: `query attacker(M)` holds of the denotation exactly when `P₀` preserves
the secrecy of `M` from `N_pub`. -/
theorem secret_iff (hpub : A.Npub.Nonempty) (P₀ : Process F G 0) (M : Tm F 0) :
    (P₀.denote finZeroElim).Secret A.alg.derive (Tm.msg A M) ↔ A.Preserves P₀ M := by
  constructor
  · intro h Q hQ t ht hout
    obtain ⟨t', ht', -, hk⟩ := attacks_sound A P₀ Q hQ ht
    exact h t' ht' (hk _ hout)
  · intro h t ht hk
    obtain ⟨Q, hQ, t', ht', -, a, ha, t'', rfl⟩ := attacks_known A hpub P₀ ht hk
    exact h Q hQ _ ht' ⟨a, ha, List.mem_append_right _ (List.mem_singleton.2 rfl)⟩

/-- Correspondences: `query F ==> event(H)` holds of the denotation exactly when `P₀`
satisfies `F ⇝ event(H)` against `N_pub`-adversaries, `N_pub` being nonempty if `F`
is an attacker fact. -/
theorem corr_iff (P₀ : Process F G 0) {X : Type} (Fq : QueryFact F X) (H : F.lang.Term X)
    (hpub : (∃ M, Fq = .attacker M) → A.Npub.Nonempty) :
    A.Satisfies P₀ Fq (.event H) ↔
      (P₀.denote finZeroElim).Corr A.alg.derive (fun σ => Fq.inst σ)
        fun σ => (QueryFact.event H).inst σ := by
  constructor
  · intro h σ t ht hF
    obtain ⟨Q, hQ, t', ht', hobs, hsat⟩ : ∃ Q, A.Adversary Q ∧ ∃ t',
        A.SurveyTrace (.against P₀ Q) t' ∧ obs t' = obs t ∧ Fq.Satisfied A t' σ := by
      cases Fq with
      | event M =>
        obtain ⟨Q, hQ, t', ht', hobs⟩ := attacks_complete A P₀ ht
        exact ⟨Q, hQ, t', ht', hobs, event_mem_obs.1 (by rw [hobs]; exact event_mem_obs.2 hF)⟩
      | attacker M =>
        obtain ⟨Q, hQ, t', ht', hobs, a, ha, t'', rfl⟩ :=
          attacks_known A (hpub ⟨M, rfl⟩) P₀ ht hF
        exact ⟨Q, hQ, _, ht', hobs, a, ha, List.mem_append_right _ (List.mem_singleton.2 rfl)⟩
    obtain ⟨σ', hσ', hH⟩ := h Q hQ t' ht' σ hsat
    exact ⟨σ', hσ', event_mem_obs.1 (by rw [← hobs]; exact event_mem_obs.2 hH)⟩
  · intro h Q hQ t ht σ hF
    obtain ⟨t', ht', hobs, hk⟩ := attacks_sound A P₀ Q hQ ht
    have hF' : (Fq.inst σ).Holds A.alg.derive t' := by
      cases Fq with
      | event M => exact event_mem_obs.1 (by rw [hobs]; exact event_mem_obs.2 hF)
      | attacker M => exact hk _ hF
    obtain ⟨σ', hσ', hH⟩ := h σ t' ht' hF'
    exact ⟨σ', hσ', event_mem_obs.1 (by rw [← hobs]; exact event_mem_obs.2 hH)⟩

end ProVerif.Specification
