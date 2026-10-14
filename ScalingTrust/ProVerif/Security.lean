/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib.Order.Closure
import ScalingTrust.ProVerif.Process
import ScalingTrust.ProVerif.Term

/-!
# The attacker and the security properties

The attacker is a process, `Enemy derive K`: the traces a Dolev-Yao attacker knowing
`K` can perform.  It may receive on any channel it can derive, send anything it
can derive on any channel it can derive, and create names.  What it can derive
from a set of messages is a closure operator, `derive`, a parameter of everything
here; for the messages of a translated model it is `MsgAlgebra.derive`, at the end
of this file.

An *attack* on `P` is a trace of `P | Enemy ∅` in which every communication was
completed; `P.Attacks` is the process of attacks.  The attacker starts from
nothing: the public free names are public constants, derivable from nothing.

What the attacker knows after a trace, `Trace.attackerKnowledge`, is read off its
communications: a message sent on a channel the attacker knew at the time becomes
known, whoever received it, since the attacker could have received it instead.  A
`Fact` of a query holds or not after each prefix of an attack; `Proc.Secret` is
`query attacker(s)` and `Proc.Corr` is `query F ==> H`.

Nothing here distinguishes public from private channels: a private channel is
a term the attacker cannot derive, on which it therefore makes no offers and
from which it learns nothing.
-/

namespace ProVerif

section

variable {M : Type} [Names M] (derive : ClosureOperator (Set M))

/-- `Enemy derive K`: the attacker, knowing `K`, as a process. -/
inductive Enemy : Set M → Proc M
  | nil {K} : Enemy K []
  | inp {K e} (c m : M) : c ∈ derive K → e ∈ Enemy (insert m K) →
      Enemy K (.inp c m :: e) -- defeq abuse for `(.inp c m :: e) ∈ Enemy derive K`, etc.
  | out {K e} (c m : M) : c ∈ derive K → m ∈ derive K → e ∈ Enemy K →
      Enemy K (.out c m :: e)
  | new {K} {e : Trace M} (n : ℕ) : n ∉ e.nonces → e ∈ Enemy (insert (Names.nonce n) K) →
      Enemy K (.new n :: e)

/-- The attacks of `P`: the closed traces of `P | Enemy ∅`. -/
def Proc.Attacks (P : Proc M) : Proc M := {t ∈ P.par (Enemy derive ∅) | t.Closed}

/-- The attacker's knowledge after `t`, starting from `K`: a message communicated on a
channel the attacker knows at the time becomes known. -/
def Trace.attackerKnowledge (K : Set M) (t : Trace M) : Set M :=
  t.foldl (fun K a => derive (K ∪ {m | ∃ c, a = .comm c m ∧ c ∈ K})) K

/-- A fact of a query: an event, or the attacker's knowledge of a message. -/
inductive Fact (M : Type) where
  | event (e : M)
  | knows (m : M)

/-- Whether a fact holds after the trace `l` of an attack. -/
def Fact.Holds (l : Trace M) : Fact M → Prop
  | .event e => Act.event e ∈ l
  | .knows m => m ∈ l.attackerKnowledge derive (derive ∅)

/-- The correspondence that `query F ==> H` checks: `Hyp` is the set of instances of `F`,
and `H f holds` the conclusion for the instance `f`, a predicate on which facts hold.
In every attack, whenever an instance of `F` holds, its conclusion holds of the facts
that hold then.  For `F ==> ⋁ⱼ ⋀ₖ Hⱼₖ`, `H f holds` is `∃ j σ, σF = f ∧ ∀ k, holds (σHⱼₖ)`
(the survey's Def. 3.5, with `=` read as `=_E`). -/
def Proc.Corr (P : Proc M) (Hyp : Set (Fact M)) (H : Fact M → (Fact M → Prop) → Prop) : Prop :=
  ∀ t ∈ P.Attacks derive, ∀ l : Trace M, l <+: t → ∀ f ∈ Hyp, f.Holds derive l →
    H f (Fact.Holds derive l)

/-- Secrecy of `s`, the property that `query attacker(s)` checks: the correspondence with
hypothesis `knows s` and conclusion `False`, so that in no attack does the attacker come
to know `s`.

The survey's secrecy (Defs. 3.2, 3.3) counts the outputs on a public free name.
Whatever the attacker knows it can relay on one, so `Secret` agrees with it when the
model has a public free name; without one, the survey's counts nothing.

`s` should contain no nonce: a nonce is identified by its index, which does not say
which `new` created it. -/
def Proc.Secret (P : Proc M) (s : M) : Prop := P.Corr derive {.knows s} fun _ _ => False

/-! ## Bounding the attacker's knowledge -/

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

/-- The enemy is bounded by every closed set containing its knowledge and every nonce. -/
theorem Enemy.bounded {S : Set M} (hS : derive.IsClosed S) (hn : ∀ n, Names.nonce n ∈ S)
    {K : Set M} {e : Trace M} (h : e ∈ Enemy derive K) (hK : K ⊆ S) : e.Bounded S := by
  induction h with
  | nil => trivial
  | inp c m _ _ ih => exact fun hm => ih (Set.insert_subset_iff.2 ⟨hm, hK⟩)
  | out c m _ hm _ ih => exact ⟨derive.closure_min hK hS hm, ih hK⟩
  | new n _ _ ih => exact ih (Set.insert_subset_iff.2 ⟨hn n, hK⟩)

omit [Names M] in
/-- Dutertre and Schneider's network lemma: in a closed trace whose components are all
bounded by `S`, every message communicated lies in `S`. -/
theorem TaggedTrace.Comms.comm_mem_of_bounded {ι : Type} [DecidableEq ι] {S : Set M}
    {s : TaggedTrace ι M} {t : Trace M} (h : s.Comms t) (hc : t.Closed)
    (hP : ∀ i, (s.proj i).Bounded S) {c m : M} (hm : Act.comm c m ∈ t) : m ∈ S := by
  induction h generalizing c m with
  | nil => simp at hm
  | cons i a _ ih =>
    obtain ⟨ha, hc⟩ := List.forall_mem_cons.1 hc
    rcases List.mem_cons.1 hm with rfl | hm
    · have := hP i
      simp [Trace.Bounded] at this
      exact this.1
    · refine ih hc (fun j => ?_) hm
      by_cases hij : i = j
      · have := hP j
        simp [hij] at this
        exact this.tail fun _ _ h => (ha (h ▸ .inp _ _)).elim
      · simpa [hij] using hP j
  | @pair s t i j hij c' m' _ ih =>
    obtain ⟨-, hc⟩ := List.forall_mem_cons.1 hc
    have hi : m' ∈ S ∧ Trace.Bounded S (TaggedTrace.proj s i) := by
      simpa [Trace.Bounded, hij.symm] using hP i
    have hj : m' ∈ S → Trace.Bounded S (TaggedTrace.proj s j) := by
      simpa [Trace.Bounded, hij] using hP j
    rcases List.mem_cons.1 hm with h | hm
    · exact (Act.comm.inj h).2 ▸ hi.1
    · refine ih hc (fun k => ?_) hm
      by_cases hik : i = k
      · exact hik ▸ hi.2
      by_cases hjk : j = k
      · exact hjk ▸ hj hi.1
      · simpa [hik, hjk] using hP k

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

/-- The closed-set method: if `S` is closed under derivation and contains every nonce, and
every trace of `P` is `Bounded S`, then at no point of an attack does the attacker know
anything outside `S`. -/
theorem Trace.attackerKnowledge_subset_of_bounded {P : Proc M} {S : Set M}
    (hS : derive.IsClosed S) (hn : ∀ n, Names.nonce n ∈ S) (hP : ∀ u ∈ P, u.Bounded S)
    {t l : Trace M} (ht : t ∈ P.Attacks derive) (hl : l <+: t) :
    l.attackerKnowledge derive (derive ∅) ⊆ S := by
  obtain ⟨⟨⟨f, s, hf, hs, hts⟩, -⟩, hc⟩ := ht
  refine attackerKnowledge_subset hS (derive.closure_min (Set.empty_subset S) hS) fun c m hm =>
    hts.comm_mem_of_bounded hc (fun i => ?_) (hl.subset hm)
  rw [hs i]
  fin_cases i
  · exact hP _ (hf 0)
  · exact Enemy.bounded hS hn (hf 1) (Set.empty_subset S)

theorem Proc.secret_of_closed {P : Proc M} {S : Set M} (hS : derive.IsClosed S)
    (hn : ∀ n, Names.nonce n ∈ S) (hP : ∀ u ∈ P, u.Bounded S) {s : M} (hs : s ∉ S) :
    P.Secret derive s := by
  rintro t ht l hl f (rfl : f = _) hf
  exact hs (Trace.attackerKnowledge_subset_of_bounded hS hn hP ht hl hf)

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

end ProVerif
