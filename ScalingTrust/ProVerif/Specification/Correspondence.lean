/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.Specification.Attacks

/-!
# The correspondence with the operational semantics

The theorems of the write-up's §2.2 about attacks and queries, for a model `A` and a
closed process `P₀`; Adequacy is `ProVerif.Specification.Adequacy`.

* **Attacks** (`attacks_sound`, `attacks_complete`, `attacks_known`): a trace of the
  survey against an adversary is an attack of the trace semantics in which the attacker
  knows whatever the trace outputs publicly; an attack is a trace of the survey against
  some adversary; and whatever the attacker knows after an attack, some adversary outputs
  publicly at the last step of a trace of the survey with the same created names and
  events.  All three are stronger than the write-up's, which asks only for the same
  events.
* **Secrecy** (`secret_iff`) and **Correspondences** (`corr_iff`): the properties of the
  trace semantics are the survey's.

The write-up's hypothesis that `P₀` and the secret mention no created name is not
needed: a created name is a nonce index that (Red Res) and `Proc.new` may both create.
-/

namespace ProVerif.Specification

open FirstOrder FirstOrder.Language ProVerif.TraceSemantics

variable {F G : Sig} (A : Model F G)

/-! ## Attacks -/

/-- `A₀`, the attacks on the denotation of `P₀`. -/
abbrev Model.attacks (P₀ : Process F G 0) : Proc A.Msg :=
  (P₀.denote finZeroElim).Attacks A.alg.derive

/-- What the attacker knows after the attack `t`. -/
abbrev Model.known (t : Trace A.Msg) : Set A.Msg :=
  t.attackerKnowledge A.alg.derive (A.alg.derive ∅)

/-- (S): a trace of the survey against an adversary is an attack in which the attacker
knows whatever the trace outputs publicly. -/
theorem attacks_sound (P₀ Q : Process F G 0) (hQ : A.Adversary Q) {t : Trace A.Msg}
    (ht : A.SurveyTrace (.against P₀ Q) t) :
    t ∈ A.attacks P₀ ∧ ∀ m, A.OutputsPublicly t m → m ∈ A.known t := by
  obtain ⟨hr, hcl⟩ := ht
  have hr' : Runs A ⟨∅, {P₀} + {Q}⟩ t := by
    rw [Multiset.singleton_add, ← Multiset.insert_eq_cons]
    exact hr
  obtain ⟨t₀, t₁, s, h₀, h₁, hs₀, hs₁, hc⟩ := Runs.split hr' rfl
  refine ⟨⟨⟨⟨![t₀, t₁], s, Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨hs₀, hs₁⟩, hc⟩,
    (Runs.nonces hr').1⟩, hcl⟩, ?_⟩
  · rw [denote_eq_traces]
    exact h₀
  · refine Runs.enemy h₁ fun P hP => ?_
    rw [Multiset.mem_singleton] at hP
    exact hP ▸ Model.Adversary.advK ∅ hQ
  · rintro m ⟨a, ha, hm⟩
    exact mem_attackerKnowledge_of_comm
      (MsgAlgebra.app_mem_derive (A := A.alg) (ms := ![]) ha fun i => i.elim0) hm

/-- (C): an attack is a trace of the survey against some adversary. -/
theorem attacks_complete (P₀ : Process F G 0) {t : Trace A.Msg} (ht : t ∈ A.attacks P₀) :
    ∃ Q, A.Adversary Q ∧ A.SurveyTrace (.against P₀ Q) t := by
  obtain ⟨⟨⟨f, s, hf, hs, hc⟩, hn⟩, hcl⟩ := ht
  have h₀ : Runs A ⟨∅, {P₀}⟩ (f 0) := by
    have := hf 0
    rw [denote_eq_traces] at this
    exact this
  obtain ⟨Q, hQ, hrun⟩ :=
    Enemy.process (show Enemy A.alg.derive ∅ (f 1) from hf 1) finZeroElim (Set.empty_subset _)
  have h₁ : Runs A ⟨∅, {Q}⟩ (f 1) := by
    have := hrun finZeroElim (funext fun i => i.elim0) ∅ fun _ _ => Finset.notMem_empty _
    rwa [Process.subst_finZero] at this
  refine ⟨Q, hQ, ?_, hcl⟩
  have := runs_add hc h₀ h₁ (hs 0) (hs 1) hn (fun _ _ => Finset.notMem_empty _)
    fun _ _ => Finset.notMem_empty _
  rw [Finset.union_empty, Multiset.singleton_add, ← Multiset.insert_eq_cons] at this
  exact this

/-- (C): whatever the attacker knows after an attack, some adversary outputs publicly at
the last step of a trace of the survey with the same created names and events. -/
theorem attacks_known (hpub : A.Npub.Nonempty) (P₀ : Process F G 0) {t : Trace A.Msg}
    (ht : t ∈ A.attacks P₀) {m : A.Msg} (hm : m ∈ A.known t) :
    ∃ Q, A.Adversary Q ∧ ∃ t', A.SurveyTrace (.against P₀ Q) t' ∧ obs t' = obs t ∧
      ∃ a ∈ A.Npub, ∃ t'', t' = t'' ++ [Act.comm (Theory.Msg.app a ![]) m] := by
  obtain ⟨a, ha⟩ := hpub
  obtain ⟨⟨⟨f, s, hf, hs, hc⟩, hn⟩, hcl⟩ := ht
  -- The attack itself will not do, unlike in the two parts above: the trace semantics
  -- counts a message communicated between two components of the protocol, on a channel
  -- the attacker knows, as known, though no adversary received it.  So the attack is
  -- first turned into one in which the attacker intercepts and relays every such
  -- communication, which changes the protocol's trace only by splitting those
  -- communications into their two offers; then the attacker outputs `m` to itself.
  obtain ⟨s', t', hc', hcl', hsp, hen, -, hobs, hnonces, hknow⟩ := intercept hc (f 0) (f 1) (hs 0)
    (hs 1) hcl (show Enemy A.alg.derive ∅ (f 1) from hf 1) subset_rfl
  have h₀ : Runs A ⟨∅, {P₀}⟩ (s'.proj 0) := by
    refine Runs.commSplit hsp ?_
    have := hf 0
    rw [denote_eq_traces] at this
    exact this
  have hen' := Enemy.append_comm hen
    (MsgAlgebra.app_mem_derive (A := A.alg) (ms := ![]) ha fun i => i.elim0) (hknow hm)
  set s'' : TaggedTrace (Fin 2) A.Msg := s' ++ [(1, Act.comm (Theory.Msg.app a ![]) m)] with hs''
  have hc'' : s''.Comms (t' ++ [Act.comm (Theory.Msg.app a ![]) m]) :=
    TaggedTrace.Comms.append hc' (.cons 1 _ .nil)
  have hp0 : s''.proj 0 = s'.proj 0 := by
    simp [hs'', TaggedTrace.proj_append]
  have hp1 : s''.proj 1 = s'.proj 1 ++ [Act.comm (Theory.Msg.app a ![]) m] := by
    simp [hs'', TaggedTrace.proj_append]
  have ht'' : t' ++ [Act.comm (Theory.Msg.app a ![]) m] ∈ A.attacks P₀ := by
    refine ⟨⟨⟨![s''.proj 0, s''.proj 1], s'', Fin.forall_fin_two.2 ⟨?_, ?_⟩,
      Fin.forall_fin_two.2 ⟨rfl, rfl⟩, hc''⟩, ?_⟩,
      List.forall_mem_append.2 ⟨hcl', List.forall_mem_singleton.2 nofun⟩⟩
    · show s''.proj 0 ∈ P₀.denote finZeroElim
      rw [hp0, denote_eq_traces]
      exact h₀
    · show s''.proj 1 ∈ Enemy A.alg.derive ∅
      rw [hp1]
      exact hen'
    · rw [Trace.nonces_append, hnonces]
      simpa [Trace.nonces] using hn
  obtain ⟨Q, hQ, hsur⟩ := attacks_complete A P₀ ht''
  exact ⟨Q, hQ, _, hsur, by rw [obs_append, hobs, obs_comm]; exact List.append_nil _, a, ha, t',
    rfl⟩

/-! ## Secrecy and correspondences -/

/-- Secrecy: `query attacker(M)` holds of the denotation exactly when `P₀` preserves
the secrecy of `M` from `N_pub`. -/
theorem secret_iff (hpub : A.Npub.Nonempty) (P₀ : Process F G 0) (M : Tm F 0) :
    (P₀.denote finZeroElim).Secret A.alg.derive (Tm.msg A M) ↔ A.Preserves P₀ M := by
  constructor
  · intro h Q hQ t ht hout
    obtain ⟨ht', hk⟩ := attacks_sound A P₀ Q hQ ht
    exact h t ht' (hk _ hout)
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
        obtain ⟨Q, hQ, ht'⟩ := attacks_complete A P₀ ht
        exact ⟨Q, hQ, t, ht', rfl, hF⟩
      | attacker M =>
        obtain ⟨Q, hQ, t', ht', hobs, a, ha, t'', rfl⟩ :=
          attacks_known A (hpub ⟨M, rfl⟩) P₀ ht hF
        exact ⟨Q, hQ, _, ht', hobs, a, ha, List.mem_append_right _ (List.mem_singleton.2 rfl)⟩
    obtain ⟨σ', hσ', hH⟩ := h Q hQ t' ht' σ hsat
    exact ⟨σ', hσ', event_mem_obs.1 (by rw [← hobs]; exact event_mem_obs.2 hH)⟩
  · intro h Q hQ t ht σ hF
    obtain ⟨ht', hk⟩ := attacks_sound A P₀ Q hQ ht
    have hF' : (Fq.inst σ).Holds A.alg.derive t := by
      cases Fq with
      | event M => exact hF
      | attacker M => exact hk _ hF
    obtain ⟨σ', hσ', hH⟩ := h σ t ht' hF'
    exact ⟨σ', hσ', hH⟩

end ProVerif.Specification
