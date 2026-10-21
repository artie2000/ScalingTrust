/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.Specification.Attacks

/-!
# The correspondence with the operational semantics

The theorems of the write-up's §3.2 about attacks and queries, for a model `A` and a
closed process `P₀`; Adequacy is `ProVerif.Specification.Adequacy`.

* **Attacks** (`attacks_sound`, `attacks_complete`, `attacks_known`), the write-up's
  Theorem "Attacks": a trace of the manual's semantics against an adversary is an attack
  of the trace semantics, in which the attacker knows whatever the trace outputs publicly;
  an attack is a trace of the manual's semantics against some adversary; and whatever the
  attacker knows after an attack, some adversary outputs publicly at the last step of a
  trace with the same created names and events, given a public name to output it on.
* **Knowledge** (`Model.knows_iff`): the attacker of the calculus knows a message after a
  trace exactly when the attacker of the trace semantics does, both starting from nothing
  and adding what is communicated on a channel they derive; so a trace satisfies a query
  fact exactly when the fact of the trace semantics holds after it
  (`QueryFact.satisfied_iff`).
* **Secrecy** (`secret_iff`) and **Correspondences** (`corr_iff`): the properties of the
  trace semantics are the survey's secrecy and the write-up's correspondences between
  facts.

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

/-- A public name is derivable. -/
theorem Model.npub_mem_derive {a : F 0} (ha : a ∈ A.Npub) (S : Set A.Msg) :
    Theory.Msg.app (.inl (.inl a)) ![] ∈ derive S :=
  Attacker.app_mem_derive
    (Attacker.ofDecls_mem (⟨a, ha, rfl⟩ : Sum.inl a ∈ Sum.inl '' A.pubFun 0)) fun i => i.elim0

/-- A trace of the manual's semantics against an adversary is an attack in which the
attacker knows whatever the trace outputs publicly. -/
theorem attacks_sound (P₀ Q : Process F G Ev 0) (hQ : A.Adversary Q) {t : Trace A.Msg}
    (ht : A.ManualTrace (.against P₀ Q) t) :
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
    exact mem_attackerKnowledge_of_comm (A.npub_mem_derive ha _) hm

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

/-- Whatever the attacker knows after an attack, some adversary outputs publicly at the
last step of a trace of the manual's semantics with the same created names and events. -/
theorem attacks_known (hpub : A.Npub.Nonempty) (P₀ : Process F G Ev 0) {t : Trace A.Msg}
    (ht : t ∈ A.attacks P₀) {m : A.Msg} (hm : m ∈ A.known t) :
    ∃ Q, A.Adversary Q ∧ ∃ t', A.ManualTrace (.against P₀ Q) t' ∧ obs t' = obs t ∧
      ∃ a ∈ A.Npub, ∃ t'', t' = t'' ++ [Act.comm (Theory.Msg.app (.inl (.inl a)) ![]) m] := by
  obtain ⟨a, ha⟩ := hpub
  obtain ⟨⟨⟨f, s, hf, hs, hc⟩, hn⟩, hcl⟩ := ht
  -- The attack itself will not do, unlike in the two parts above: the trace semantics
  -- counts a message communicated between two components of the protocol, on a channel
  -- the attacker knows, as known, though no adversary received it.  So the attack is
  -- first turned into one in which the attacker intercepts and relays every such
  -- communication, which changes the protocol's trace only by splitting those
  -- communications into their two offers; then the attacker outputs `m` to itself.
  obtain ⟨s', t', hc', hcl', hsp, hen, -, hobs, hnonces, hknow⟩ := intercept hc (f 0) (f 1) (hs 0)
    (hs 1) hcl (show Enemy ∅ (f 1) from hf 1) subset_rfl
  have h₀ : Runs A ⟨∅, {P₀}⟩ (s'.proj 0) := by
    refine Runs.commSplit hsp ?_
    have := hf 0
    rw [denote_eq_traces] at this
    exact this
  have hen' := Enemy.append_comm hen (A.npub_mem_derive ha _) (hknow hm)
  set s'' : TaggedTrace (Fin 2) A.Msg :=
    s' ++ [(1, Act.comm (Theory.Msg.app (.inl (.inl a)) ![]) m)] with hs''
  have hc'' : s''.Comms (t' ++ [Act.comm (Theory.Msg.app (.inl (.inl a)) ![]) m]) :=
    TaggedTrace.Comms.append hc' (.cons 1 _ .nil)
  have hp0 : s''.proj 0 = s'.proj 0 := by
    simp [hs'', TaggedTrace.proj_append]
  have hp1 : s''.proj 1 = s'.proj 1 ++ [Act.comm (Theory.Msg.app (.inl (.inl a)) ![]) m] := by
    simp [hs'', TaggedTrace.proj_append]
  have ht'' : t' ++ [Act.comm (Theory.Msg.app (.inl (.inl a)) ![]) m] ∈ A.attacks P₀ := by
    refine ⟨⟨⟨![s''.proj 0, s''.proj 1], s'', Fin.forall_fin_two.2 ⟨?_, ?_⟩,
      Fin.forall_fin_two.2 ⟨rfl, rfl⟩, hc''⟩, ?_⟩,
      List.forall_mem_append.2 ⟨hcl', List.forall_mem_singleton.2 nofun⟩⟩
    · show s''.proj 0 ∈ P₀.denote finZeroElim
      rw [hp0, denote_eq_traces]
      exact h₀
    · show s''.proj 1 ∈ Enemy ∅
      rw [hp1]
      exact hen'
    · rw [Trace.nonces_append, hnonces]
      simpa [Trace.nonces] using hn
  obtain ⟨Q, hQ, hsur⟩ := attacks_complete A P₀ ht''
  exact ⟨Q, hQ, _, hsur, by rw [obs_append, hobs, obs_comm]; exact List.append_nil _, a, ha, t',
    rfl⟩

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

/-- A trace satisfies a query fact exactly when the fact of the trace semantics holds after
it. -/
theorem QueryFact.satisfied_iff {X : Type} (t : Trace A.Msg) (σ : X → A.Msg) :
    ∀ Fq : QueryFact F Ev X, Fq.Satisfied A t σ ↔ (Fq.inst σ).Holds t
  | .event _ _ => Iff.rfl
  | .attacker _ => A.knows_iff t _

/-! ## Secrecy and correspondences -/

/-- Secrecy: `query attacker(M)` holds of the denotation exactly when `P₀` preserves
the secrecy of `M` from `N_pub`, the survey's Definition 3.3. -/
theorem secret_iff (hpub : A.Npub.Nonempty) (P₀ : Process F G Ev 0) (M : Tm F Ev 0) :
    (P₀.denote finZeroElim).Secret (Tm.msg A M) ↔ A.Preserves P₀ M := by
  constructor
  · intro h Q hQ t ht hout
    obtain ⟨ht', hk⟩ := attacks_sound A P₀ Q hQ ht
    exact h t ht' (hk _ hout)
  · intro h t ht hk
    obtain ⟨Q, hQ, t', ht', -, a, ha, t'', rfl⟩ := attacks_known A hpub P₀ ht hk
    exact h Q hQ _ ht' ⟨a, ha, List.mem_append_right _ (List.mem_singleton.2 rfl)⟩

/-- Correspondences: `query F ==> H` holds of the denotation exactly when `P₀` satisfies
`F ⇝ H` against `N_pub`-adversaries: a trace of the manual's semantics against an adversary
is an attack and conversely, and the query facts are satisfied by a trace exactly when the
facts of the trace semantics hold after it. -/
theorem corr_iff (P₀ : Process F G Ev 0) {X : Type} (Fq Hq : QueryFact F Ev X) :
    A.Satisfies P₀ Fq Hq ↔
      (P₀.denote (A := A) finZeroElim).Corr (fun σ => Fq.inst σ) fun σ => Hq.inst σ := by
  constructor
  · intro h σ t ht hF
    obtain ⟨Q, hQ, ht'⟩ := attacks_complete A P₀ ht
    obtain ⟨σ', hσ', hH⟩ := h Q hQ t ht' σ ((QueryFact.satisfied_iff A t σ Fq).2 hF)
    exact ⟨σ', hσ', (QueryFact.satisfied_iff A t σ' Hq).1 hH⟩
  · intro h Q hQ t ht σ hF
    obtain ⟨σ', hσ', hH⟩ :=
      h σ t (attacks_sound A P₀ Q hQ ht).1 ((QueryFact.satisfied_iff A t σ Fq).1 hF)
    exact ⟨σ', hσ', (QueryFact.satisfied_iff A t σ' Hq).2 hH⟩

end ProVerif.Specification
