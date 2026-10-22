/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.TraceSemantics.Security

/-!
# Proving secrecy: the closed-set method

The closed-set method of Dutertre and Schneider, `Proc.secret_of_closed`: a set of
messages that is closed under derivation, that contains the names the attacker creates
and that the protocol never leaves as long as it receives only messages in it bounds
everything the attacker can ever know.  The set is indexed by the set `N` of the names
the protocol creates, so that it can keep them, and what is encrypted under them, from
the attacker; the attacker's names are the ones outside `N`.  What it means for a trace
and a process to stay in the set, `Trace.Bounded` and `Proc.Bounded`, does not involve
the attacker, and every constructor preserves it, so a translated process is proved
bounded by following its `do` block: `new` adds the name to `N`, `inp` adds the message
received to `S N`, and `out` asks that the message sent lie in `S N`.
-/

namespace ProVerif.TraceSemantics

open Attacker (derive)

variable {M : Type}

/-! ## Bounded traces and processes -/

/-- Dutertre and Schneider's condition on a user: every message sent or communicated
lies in `S` as long as every message received before it does. -/
def Trace.Bounded (S : Set M) : Trace M → Prop
  | [] => True
  | .inp _ m :: u => m ∈ S → Bounded S u
  | .out _ m :: u => m ∈ S ∧ Bounded S u
  | .comm _ m :: u => m ∈ S ∧ Bounded S u
  | _ :: u => Bounded S u

theorem Trace.Bounded.tail {S : Set M} {a : Act M} {u : Trace M} (h : Bounded S (a :: u))
    (ha : ∀ c m, a = .inp c m → m ∈ S) : u.Bounded S := by
  cases a <;> first | exact h (ha _ _ rfl) | exact h.2 | exact h

/-- In a closed bounded trace, every message communicated lies in `S`. -/
theorem Trace.Bounded.comm_mem {S : Set M} {t : Trace M} (hb : t.Bounded S) (hc : t.Closed)
    {c m : M} (h : Act.comm c m ∈ t) : m ∈ S := by
  induction t with
  | nil => simp at h
  | cons a t ih =>
    obtain ⟨ha, hc⟩ := List.forall_mem_cons.1 hc
    rcases List.mem_cons.1 h with rfl | h
    · exact hb.1
    · exact ih (hb.tail fun _ _ h' => (ha (h' ▸ .inp _ _)).elim) hc h

/-- Dutertre and Schneider's network lemma: a trace whose components are all bounded by
`S` is bounded by `S`. -/
theorem TaggedTrace.Comms.bounded {ι : Type} [DecidableEq ι] {S : Set M}
    {s : TaggedTrace ι M} {t : Trace M} (h : s.Comms t) (hP : ∀ i, (s.proj i).Bounded S) :
    t.Bounded S := by
  induction h with
  | nil => trivial
  | @cons s t i a _ ih =>
    have hi : Trace.Bounded S (a :: s.proj i) := by simpa using hP i
    have hP' (ha : ∀ c m, a = .inp c m → m ∈ S) (j : ι) : (s.proj j).Bounded S := by
      by_cases hij : i = j
      · exact hij ▸ hi.tail ha
      · simpa [hij] using hP j
    cases a with
    | inp c m => exact fun hm => ih (hP' fun _ _ h => (Act.inp.inj h).2 ▸ hm)
    | out c m => exact ⟨hi.1, ih (hP' nofun)⟩
    | comm c m => exact ⟨hi.1, ih (hP' nofun)⟩
    | new n => exact ih (hP' nofun)
    | event e => exact ih (hP' nofun)
  | @pair s t i j hij c m _ ih =>
    have hi : m ∈ S ∧ Trace.Bounded S (s.proj i) := by simpa [Trace.Bounded, hij.symm] using hP i
    have hj : m ∈ S → Trace.Bounded S (s.proj j) := by simpa [Trace.Bounded, hij] using hP j
    refine ⟨hi.1, ih fun k => ?_⟩
    by_cases hik : i = k
    · exact hik ▸ hi.2
    by_cases hjk : j = k
    · exact hjk ▸ hj hi.1
    · simpa [hik, hjk] using hP k

/-- `P` is bounded by the family `S`: every trace `u` of `P` is `Bounded (S N)` for every
`N` that satisfies `H` and contains the names `u` creates.  `H` is what the context of a
subprocess has established about `N`: that it contains the names created so far, and that
the messages received so far lie in `S N`. -/
def Proc.Bounded (S : Set ℕ → Set M) (H : Set ℕ → Prop) (P : Proc M) : Prop :=
  ∀ u ∈ P, ∀ N, H N → (∀ n ∈ u.nonces, n ∈ N) → u.Bounded (S N)

/-! Every constructor preserves boundedness, so a translated process is proved bounded by
following its `do` block: `new` adds the name to `N`, `inp` adds the message received to
`S N`, and `out` asks that the message sent lie in `S N`. -/

namespace Proc.Bounded

variable {S : Set ℕ → Set M} {H : Set ℕ → Prop}

theorem mono {H' : Set ℕ → Prop} (hH : ∀ N, H' N → H N) {P : Proc M} (h : P.Bounded S H) :
    P.Bounded S H' :=
  fun u hu N hN => h u hu N (hH N hN)

theorem nil : (Proc.nil : Proc M).Bounded S H := by
  rintro u (rfl : u = []) N _ _
  trivial

theorem out {c m : M} {P : Proc M} (hm : ∀ N, H N → m ∈ S N) (h : P.Bounded S H) :
    (Proc.out c m P).Bounded S H := by
  rintro u (rfl | ⟨u, hu, rfl⟩) N hN hn
  · trivial
  · exact ⟨hm N hN, h u hu N hN hn⟩

theorem event {e : M} {P : Proc M} (h : P.Bounded S H) : (Proc.event e P).Bounded S H := by
  rintro u (rfl | ⟨u, hu, rfl⟩) N hN hn
  · trivial
  · exact h u hu N hN hn

/-- The message received may be assumed to lie in `S N`. -/
theorem inp {c : M} {P : M → Proc M} (h : ∀ m, (P m).Bounded S fun N => H N ∧ m ∈ S N) :
    (Proc.inp c P).Bounded S H := by
  rintro u hu N hN hn
  obtain ⟨m, (rfl | ⟨u', hu', rfl⟩)⟩ := Set.mem_iUnion.1 hu
  · trivial
  · exact fun hm => h m u' hu' N ⟨hN, hm⟩ hn

/-- The name created may be assumed to lie in `N`. -/
theorem new [Names M] {P : M → Proc M}
    (h : ∀ n, (P (Names.nonce n)).Bounded S fun N => H N ∧ n ∈ N) : (Proc.new P).Bounded S H := by
  rintro u hu N hN hn
  obtain ⟨n, (rfl | ⟨u', ⟨hu', -⟩, rfl⟩)⟩ := Set.mem_iUnion.1 hu
  · trivial
  · exact h n u' hu' N ⟨hN, hn n List.mem_cons_self⟩ fun k hk => hn k (List.mem_cons_of_mem _ hk)

theorem merge {ι : Type} [DecidableEq ι] {P : ι → Proc M} (h : ∀ i, (P i).Bounded S H) :
    (Proc.merge P).Bounded S H := by
  rintro t ⟨⟨f, s, hf, hs, hst⟩, -⟩ N hN hn
  refine hst.bounded fun i => ?_
  rw [hs i]
  refine h i (f i) (hf i) N hN fun n hn' => hn n ?_
  rw [hst.nonces]
  rw [← hs i] at hn'
  exact (Trace.nonces_sublist (TaggedTrace.proj_sublist s i)).subset hn'

theorem par {P Q : Proc M} (hP : P.Bounded S H) (hQ : Q.Bounded S H) :
    (Proc.par P Q).Bounded S H :=
  merge (Fin.forall_fin_two.2 ⟨hP, hQ⟩)

theorem bang {P : Proc M} (h : P.Bounded S H) : P.bang.Bounded S H := merge fun _ => h

end Proc.Bounded

/-! ## The bound on the attacker's knowledge -/

section

variable [Attacker M]

/-- The attacker's knowledge stays within a closed set containing what it knew and every
message communicated. -/
theorem Trace.attackerKnowledge_subset {S K : Set M} (hS : derive.IsClosed S) (hK : K ⊆ S) :
    ∀ {t : Trace M}, (∀ c m, Act.comm c m ∈ t → m ∈ S) → t.attackerKnowledge K ⊆ S := by
  intro t
  induction t generalizing K with
  | nil => exact fun _ => hK
  | cons a t ih =>
    intro h
    exact ih (derive.closure_min (Set.union_subset hK fun m ⟨c, ha, _⟩ =>
      h c m (by subst ha; exact List.mem_cons_self)) hS) fun c m hm => h c m (List.mem_cons_of_mem _ hm)

end

section

variable [Names M] [Attacker M]

/-- The enemy is bounded by every closed set containing its knowledge and the names it
creates. -/
theorem Enemy.bounded {S : Set M} (hS : derive.IsClosed S) {K : Set M} {e : Trace M}
    (h : e ∈ Enemy K) (hK : K ⊆ S) (hn : ∀ n ∈ e.nonces, Names.nonce n ∈ S) :
    e.Bounded S := by
  induction h with
  | nil => trivial
  | inp c m _ _ ih => exact fun hm => ih (Set.insert_subset_iff.2 ⟨hm, hK⟩) hn
  | out c m _ hm _ ih => exact ⟨derive.closure_min hK hS hm, ih hK hn⟩
  | comm c m _ hm _ ih => exact ⟨derive.closure_min hK hS hm, ih hK hn⟩
  | new n _ _ ih =>
    exact ih (Set.insert_subset_iff.2 ⟨hn n List.mem_cons_self, hK⟩)
      fun k hk => hn k (List.mem_cons_of_mem _ hk)

/-- The closed-set method: if every `S N` is closed under derivation and contains the names
outside `N`, and `P` is bounded by `S`, then after any attack the attacker knows nothing
outside `S N`, for `N` the names the protocol created in it. -/
theorem Trace.attackerKnowledge_subset_of_bounded {P : Proc M} {S : Set ℕ → Set M}
    (hS : ∀ N, derive.IsClosed (S N)) (hn : ∀ N, ∀ n ∉ N, Names.nonce n ∈ S N)
    (hP : P.Bounded S fun _ => True) {t : Trace M} (ht : t ∈ P.Attacks) :
    ∃ N, t.attackerKnowledge (derive ∅) ⊆ S N := by
  obtain ⟨⟨⟨f, s, hf, hs, hts⟩, hnd⟩, hc⟩ := ht
  refine ⟨{n | n ∈ (f 0).nonces}, attackerKnowledge_subset (hS _)
    (derive.closure_min (Set.empty_subset _) (hS _)) fun c m hm =>
      (hts.bounded (Fin.forall_fin_two.2 ⟨?_, ?_⟩)).comm_mem hc hm⟩
  · rw [hs 0]
    exact hP _ (hf 0) _ trivial fun _ h => h
  · rw [hs 1]
    refine Enemy.bounded (hS _) (hf 1) (Set.empty_subset _) fun n hn' => hn _ n fun h => ?_
    rw [hts.nonces] at hnd
    rw [← hs 1] at hn'
    rw [← hs 0] at h
    exact TaggedTrace.proj_nonces_disjoint hnd (show (1 : Fin 2) ≠ 0 by decide) hn' h

theorem Proc.secret_of_closed {P : Proc M} {S : Set ℕ → Set M} (hS : ∀ N, derive.IsClosed (S N))
    (hn : ∀ N, ∀ n ∉ N, Names.nonce n ∈ S N) (hP : P.Bounded S fun _ => True) {s : M}
    (hs : ∀ N, s ∉ S N) : P.Secret s := fun _ ht hf =>
  let ⟨N, h⟩ := Trace.attackerKnowledge_subset_of_bounded hS hn hP ht
  hs N (h hf)

end

end ProVerif.TraceSemantics
