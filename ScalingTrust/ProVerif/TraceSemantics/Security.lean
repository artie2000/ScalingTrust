/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib.Order.Closure
import ScalingTrust.ProVerif.TraceSemantics.Process
import ScalingTrust.ProVerif.TraceSemantics.Term

/-!
# The attacker and the security properties

The attacker is a process, `Enemy derive K`: the traces a Dolev-Yao attacker knowing
`K` can perform.  It may receive on any channel it can derive, send anything it
can derive on any channel it can derive, and create names.  It may also send to
itself, a `comm` that needs no partner: the survey's Definition 3.2 counts an
adversary's output on a public channel whoever receives it, and so does
`Trace.attackerKnowledge`.  What it can derive from a set of messages is a closure
operator, `derive`, a parameter of everything here; for the messages of a translated
model it is `MsgAlgebra.derive`, at the end of this file.

An *attack* on `P` is a trace of `P | Enemy ∅` in which every communication was
completed; `P.Attacks` is the process of attacks.  The attacker starts from
nothing: the public free names are public constants, derivable from nothing.

What the attacker knows after a trace, `Trace.attackerKnowledge`, is read off its
communications: a message sent on a channel the attacker knew at the time becomes
known, whoever received it, since the attacker could have received it instead.  A
`Fact` of a query holds or not after an attack; `Proc.Secret` is `query attacker(s)`
and `Proc.Corr` is `query F ==> H`.  A prefix of an attack is an attack, so a property
of every attack is a property of every point of every attack.

Secrecy is proved by the closed-set method, `Proc.secret_of_closed`: a family of
derivation-closed sets, indexed by the names the protocol has created, that the protocol
never leaves (`Proc.Bounded`, proved by one rule per constructor) bounds the attacker's
knowledge.

Nothing here distinguishes public from private channels: a private channel is
a term the attacker cannot derive, on which it therefore makes no offers and
from which it learns nothing.
-/

namespace ProVerif.TraceSemantics

open Descriptive

section

variable {M : Type} [Names M] (derive : ClosureOperator (Set M))

/-- `Enemy derive K`: the attacker, knowing `K`, as a process. -/
inductive Enemy : Set M → Proc M
  | nil {K} : Enemy K []
  | inp {K e} (c m : M) : c ∈ derive K → e ∈ Enemy (insert m K) →
      Enemy K (.inp c m :: e) -- defeq abuse for `(.inp c m :: e) ∈ Enemy derive K`, etc.
  | out {K e} (c m : M) : c ∈ derive K → m ∈ derive K → e ∈ Enemy K →
      Enemy K (.out c m :: e)
  | comm {K e} (c m : M) : c ∈ derive K → m ∈ derive K → e ∈ Enemy K →
      Enemy K (.comm c m :: e)
  | new {K} {e : Trace M} (n : ℕ) : n ∉ e.nonces → e ∈ Enemy (insert (Names.nonce n) K) →
      Enemy K (.new n :: e)

/-- The enemy is prefix-closed: it can stop at any point. -/
theorem Enemy.mem_tree (K : Set M) : Enemy derive K ∈ tree (Act M) := by
  intro x a hx
  generalize ht : x ++ [a] = t at hx
  induction hx generalizing x with
  | nil => simp at ht
  | inp c m hc _ ih =>
    rcases x with _ | ⟨b, x⟩
    · exact .nil
    · obtain ⟨rfl, rfl⟩ := List.cons.inj ht
      exact .inp c m hc (ih rfl)
  | out c m hc hm _ ih =>
    rcases x with _ | ⟨b, x⟩
    · exact .nil
    · obtain ⟨rfl, rfl⟩ := List.cons.inj ht
      exact Enemy.out c m hc hm (ih rfl)
  | comm c m hc hm _ ih =>
    rcases x with _ | ⟨b, x⟩
    · exact .nil
    · obtain ⟨rfl, rfl⟩ := List.cons.inj ht
      exact Enemy.comm c m hc hm (ih rfl)
  | new n hn _ ih =>
    rcases x with _ | ⟨b, x⟩
    · exact .nil
    · obtain ⟨rfl, rfl⟩ := List.cons.inj ht
      exact .new n (fun h => hn ((Trace.nonces_sublist (List.sublist_append_left _ _)).subset h))
        (ih rfl)

/-- The attacks of `P`: the closed traces of `P | Enemy ∅`. -/
def Proc.Attacks (P : Proc M) : Proc M := {t ∈ P.par (Enemy derive ∅) | t.Closed}

/-- A prefix of an attack on a prefix-closed process is an attack. -/
theorem Proc.attacks_mem_tree {P : Proc M} (hP : P ∈ tree (Act M)) :
    P.Attacks derive ∈ tree (Act M) := fun _ _ ⟨ht, hc⟩ =>
  ⟨Tree.mem_of_append (T := ⟨_, Proc.par_mem_tree hP (Enemy.mem_tree derive ∅)⟩) ht,
    fun b hb => hc b (List.mem_append_left _ hb)⟩

/-- The attacker's knowledge after `t`, starting from `K`: a message communicated on a
channel the attacker knows at the time becomes known. -/
def Trace.attackerKnowledge (K : Set M) (t : Trace M) : Set M :=
  t.foldl (fun K a => derive (K ∪ {m | ∃ c, a = .comm c m ∧ c ∈ K})) K

/-- A fact of a query: an event, or the attacker's knowledge of a message. -/
inductive Fact (M : Type) where
  | event (e : M)
  | knows (m : M)

/-- Whether a fact holds after the trace `t`. -/
def Fact.Holds (t : Trace M) : Fact M → Prop
  | .event e => Act.event e ∈ t
  | .knows m => m ∈ t.attackerKnowledge derive (derive ∅)

/-- The correspondence that `query F ==> H` checks, for query facts `F` and `H` over the
variables `X`, written as functions of a valuation `σ : X → M`: in every attack in which an
instance `F σ` holds, `H σ'` holds for some `σ'` with `F σ' = F σ`, the survey's Def. 3.5
with `=` read as `=_E`.  For a prefix-closed `P` the attacks are prefix-closed, so `H σ'`
holds by the time `F σ` does. -/
def Proc.Corr (P : Proc M) {X : Type} (F H : (X → M) → Fact M) : Prop :=
  ∀ (σ : X → M), ∀ t ∈ P.Attacks derive, (F σ).Holds derive t →
    ∃ σ', F σ' = F σ ∧ (H σ').Holds derive t

/-- Secrecy of `s`, the property that `query attacker(s)` checks: in no attack does the
attacker come to know `s`.

The survey's secrecy (Defs. 3.2, 3.3) counts the outputs on a public free name.
Whatever the attacker knows it can relay on one, so `Secret` agrees with it when the
model has a public free name; without one, the survey's counts nothing.

`s` should contain no nonce: a nonce is identified by its index, which does not say
which `new` created it. -/
def Proc.Secret (P : Proc M) (s : M) : Prop :=
  ∀ t ∈ P.Attacks derive, ¬ (Fact.knows s).Holds derive t

/-! ## Bounding the attacker's knowledge

The closed-set method of Dutertre and Schneider: a set of messages that is closed under
derivation, that contains the names the attacker creates and that the protocol never
leaves as long as it receives only messages in it bounds everything the attacker can
ever know.  The set is indexed by the set `N` of the names the protocol creates, so that
it can keep them, and what is encrypted under them, from the attacker; the attacker's
names are the ones outside `N`. -/

variable {derive}

/-- Dutertre and Schneider's condition on a user: every message sent or communicated
lies in `S` as long as every message received before it does. -/
def Trace.Bounded (S : Set M) : Trace M → Prop
  | [] => True
  | .inp _ m :: u => m ∈ S → Bounded S u
  | .out _ m :: u => m ∈ S ∧ Bounded S u
  | .comm _ m :: u => m ∈ S ∧ Bounded S u
  | _ :: u => Bounded S u

omit [Names M] in
theorem Trace.Bounded.tail {S : Set M} {a : Act M} {u : Trace M} (h : Bounded S (a :: u))
    (ha : ∀ c m, a = .inp c m → m ∈ S) : u.Bounded S := by
  cases a <;> first | exact h (ha _ _ rfl) | exact h.2 | exact h

omit [Names M] in
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

omit [Names M] in
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

/-- The enemy is bounded by every closed set containing its knowledge and the names it
creates. -/
theorem Enemy.bounded {S : Set M} (hS : derive.IsClosed S) {K : Set M} {e : Trace M}
    (h : e ∈ Enemy derive K) (hK : K ⊆ S) (hn : ∀ n ∈ e.nonces, Names.nonce n ∈ S) :
    e.Bounded S := by
  induction h with
  | nil => trivial
  | inp c m _ _ ih => exact fun hm => ih (Set.insert_subset_iff.2 ⟨hm, hK⟩) hn
  | out c m _ hm _ ih => exact ⟨derive.closure_min hK hS hm, ih hK hn⟩
  | comm c m _ hm _ ih => exact ⟨derive.closure_min hK hS hm, ih hK hn⟩
  | new n _ _ ih =>
    exact ih (Set.insert_subset_iff.2 ⟨hn n List.mem_cons_self, hK⟩)
      fun k hk => hn k (List.mem_cons_of_mem _ hk)

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

omit [Names M] in
theorem mono {H' : Set ℕ → Prop} (hH : ∀ N, H' N → H N) {P : Proc M} (h : P.Bounded S H) :
    P.Bounded S H' :=
  fun u hu N hN => h u hu N (hH N hN)

omit [Names M] in
theorem nil : (Proc.nil : Proc M).Bounded S H := by
  rintro u (rfl : u = []) N _ _
  trivial

omit [Names M] in
theorem out {c m : M} {P : Proc M} (hm : ∀ N, H N → m ∈ S N) (h : P.Bounded S H) :
    (Proc.out c m P).Bounded S H := by
  rintro u (rfl | ⟨u, hu, rfl⟩) N hN hn
  · trivial
  · exact ⟨hm N hN, h u hu N hN hn⟩

omit [Names M] in
theorem event {e : M} {P : Proc M} (h : P.Bounded S H) : (Proc.event e P).Bounded S H := by
  rintro u (rfl | ⟨u, hu, rfl⟩) N hN hn
  · trivial
  · exact h u hu N hN hn

omit [Names M] in
/-- The message received may be assumed to lie in `S N`. -/
theorem inp {c : M} {P : M → Proc M} (h : ∀ m, (P m).Bounded S fun N => H N ∧ m ∈ S N) :
    (Proc.inp c P).Bounded S H := by
  rintro u hu N hN hn
  obtain ⟨m, (rfl | ⟨u', hu', rfl⟩)⟩ := Set.mem_iUnion.1 hu
  · trivial
  · exact fun hm => h m u' hu' N ⟨hN, hm⟩ hn

/-- The name created may be assumed to lie in `N`. -/
theorem new {P : M → Proc M}
    (h : ∀ n, (P (Names.nonce n)).Bounded S fun N => H N ∧ n ∈ N) : (Proc.new P).Bounded S H := by
  rintro u hu N hN hn
  obtain ⟨n, (rfl | ⟨u', ⟨hu', -⟩, rfl⟩)⟩ := Set.mem_iUnion.1 hu
  · trivial
  · exact h n u' hu' N ⟨hN, hn n List.mem_cons_self⟩ fun k hk => hn k (List.mem_cons_of_mem _ hk)

omit [Names M] in
theorem merge {ι : Type} [DecidableEq ι] {P : ι → Proc M} (h : ∀ i, (P i).Bounded S H) :
    (Proc.merge P).Bounded S H := by
  rintro t ⟨⟨f, s, hf, hs, hst⟩, -⟩ N hN hn
  refine hst.bounded fun i => ?_
  rw [hs i]
  refine h i (f i) (hf i) N hN fun n hn' => hn n ?_
  rw [hst.nonces]
  rw [← hs i] at hn'
  exact (Trace.nonces_sublist (TaggedTrace.proj_sublist s i)).subset hn'

omit [Names M] in
theorem par {P Q : Proc M} (hP : P.Bounded S H) (hQ : Q.Bounded S H) :
    (Proc.par P Q).Bounded S H :=
  merge (Fin.forall_fin_two.2 ⟨hP, hQ⟩)

omit [Names M] in
theorem bang {P : Proc M} (h : P.Bounded S H) : P.bang.Bounded S H := merge fun _ => h

end Proc.Bounded

omit [Names M] in
/-- The attacker's knowledge stays within a closed set containing what it knew and every
message communicated. -/
theorem Trace.attackerKnowledge_subset {S K : Set M} (hS : derive.IsClosed S) (hK : K ⊆ S) :
    ∀ {t : Trace M}, (∀ c m, Act.comm c m ∈ t → m ∈ S) → t.attackerKnowledge derive K ⊆ S := by
  intro t
  induction t generalizing K with
  | nil => exact fun _ => hK
  | cons a t ih =>
    intro h
    exact ih (derive.closure_min (Set.union_subset hK fun m ⟨c, ha, _⟩ =>
      h c m (by subst ha; exact List.mem_cons_self)) hS) fun c m hm => h c m (List.mem_cons_of_mem _ hm)

/-- The closed-set method: if every `S N` is closed under derivation and contains the names
outside `N`, and `P` is bounded by `S`, then after any attack the attacker knows nothing
outside `S N`, for `N` the names the protocol created in it. -/
theorem Trace.attackerKnowledge_subset_of_bounded {P : Proc M} {S : Set ℕ → Set M}
    (hS : ∀ N, derive.IsClosed (S N)) (hn : ∀ N, ∀ n ∉ N, Names.nonce n ∈ S N)
    (hP : P.Bounded S fun _ => True) {t : Trace M} (ht : t ∈ P.Attacks derive) :
    ∃ N, t.attackerKnowledge derive (derive ∅) ⊆ S N := by
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
    (hs : ∀ N, s ∉ S N) : P.Secret derive s := fun _ ht hf =>
  let ⟨N, h⟩ := Trace.attackerKnowledge_subset_of_bounded hS hn hP ht
  hs N (h hf)

/-! ## Attackers from public operations -/

/-- `S` is closed under each operation in `ops`, an operation of some arity on
may-fail arguments, `none` being `fail`.  An argument is either in `S` or `none`: the
attacker can always pass `fail`, which is an expression of the calculus. -/
def ClosedUnder (ops : Set (Σ n, (Fin n → Option M) → Option M)) (S : Set M) : Prop :=
  ∀ o ∈ ops, ∀ args : Fin o.1 → Option M, (∀ i m, args i = some m → m ∈ S) →
    ∀ r, o.2 args = some r → r ∈ S

/-- What an attacker that can apply the operations `ops` derives: ProVerif's
`attacker` predicate for a term algebra. -/
def deriveOfOps (ops : Set (Σ n, (Fin n → Option M) → Option M)) : ClosureOperator (Set M) :=
  ClosureOperator.ofCompletePred (ClosedUnder ops) fun _ h o ho args hargs r hr => by
    simp only [Set.sInf_eq_sInter, Set.mem_sInter] at hargs ⊢
    exact fun S hS => h S hS o ho args (fun i m hm => hargs i m hm S hS) r hr

end

/-! ## Message algebras

The Dolev-Yao model for the messages of an algebra: the nonces that `new` creates are
the names, and the attacker can apply exactly the public operations that the algebra
declares.
-/

section algebra

variable {F : Sig} {T : Theory F}

instance : Names T.Msg := ⟨⟨.name, fun _ _ => Theory.Msg.name_inj⟩⟩

/-- What the attacker can derive over the messages of `A`: the closure under its public
operations. -/
def MsgAlgebra.derive (A : MsgAlgebra F) : ClosureOperator (Set A.Msg) := deriveOfOps A.ops

/-- A public constructor applied to derivable messages is derivable; in particular a
public free name is derivable from nothing. -/
theorem MsgAlgebra.app_mem_derive {A : MsgAlgebra F} {n : ℕ} {f : F n} (hf : f ∈ A.pubFun n)
    {S : Set A.Msg} {ms : Fin n → A.Msg} (hms : ∀ i, ms i ∈ A.derive S) :
    .app f ms ∈ A.derive S := by
  have hS : ClosedUnder A.ops (A.derive S) := A.derive.isClosed_closure S
  exact hS _ (Or.inl (Set.mem_iUnion.2 ⟨n, f, hf, rfl⟩)) (fun i => some (ms i))
    (fun i m h => Option.some_injective _ h ▸ hms i) _
    ((liftFail_eq_some (f := fun as => some (Theory.Msg.app f as))).2 ⟨ms, fun _ => rfl, rfl⟩)

end algebra

end ProVerif.TraceSemantics
