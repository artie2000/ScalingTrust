/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib.Order.Closure
import ScalingTrust.ProVerif.Process
import ScalingTrust.ProVerif.Term

/-!
# The attacker and the security properties

The attacker is a process, `Enemy K`: the traces a Dolev-Yao attacker knowing
`K` can perform.  It may receive on any channel it can derive, send anything it
can derive on any channel it can derive, and create names.  What it can derive
from a set of messages is a closure operator, `Attacker.derive`; for the messages
of a translated model it comes from the algebra, at the end of this file.

An *attack* on `P` is a trace of `P | Enemy ∅` in which every communication was
completed; `Attacks P` is the process of attacks.  The attacker starts from
nothing: the public free names are public constants, derivable from nothing.

What the attacker knows after a trace, `known`, is read off its communications:
a message sent on a channel the attacker knew at the time becomes known, whoever
received it, since the attacker could have received it instead.  A `Fact` of a
query holds or not after each prefix of an attack; `Secret` is
`query attacker(s)` and `Corr` is `query F ==> H`.

Nothing here distinguishes public from private channels: a private channel is
a term the attacker cannot derive, on which it therefore makes no offers and
from which it learns nothing.
-/

namespace ProVerif

/-- The attacker's deductive power. -/
class Attacker (M : Type) where
  derive : ClosureOperator (Set M)

open Attacker

variable {M : Type} [Attacker M] [Names M]

/-- `Enemy K`: the attacker, knowing `K`, as a process. -/
inductive Enemy : Set M → Proc M
  | nil {K} : Enemy K []
  | inp {K e} (c m : M) : c ∈ derive K → e ∈ Enemy (insert m K) →
      Enemy K (.inp c m :: e) -- defeq abuse for `(.inp c m :: e) ∈ Enemy K`, etc.
  | out {K e} (c m : M) : c ∈ derive K → m ∈ derive K → e ∈ Enemy K →
      Enemy K (.out c m :: e)
  | new {K e} (n : ℕ) : n ∉ nonces e → e ∈ Enemy (insert (Names.nonce n) K) →
      Enemy K (.new n :: e)

/-- The attacks of `P`: the closed traces of `P | Enemy ∅`. -/
def Attacks (P : Proc M) : Set (Trace M) := {t ∈ Proc.par P (Enemy ∅) | Closed t}

/-- The attacker's knowledge after `t`, starting from `K`: a message communicated on a
channel the attacker knows at the time becomes known. -/
def known (K : Set M) (t : Trace M) : Set M :=
  t.foldl (fun K a => derive (K ∪ {m | ∃ c, a = .comm c m ∧ c ∈ K})) K

/-- A fact of a query: an event, or the attacker's knowledge of a message. -/
inductive Fact (M : Type) where
  | event (e : M)
  | knows (m : M)

/-- Whether a fact holds after the trace `l` of an attack. -/
def Fact.Holds (l : Trace M) : Fact M → Prop
  | .event e => Act.event e ∈ l
  | .knows m => m ∈ known (derive ∅) l

/-- The correspondence that `query F ==> H` checks: `Hyp` is the set of instances of `F`,
and `H f holds` the conclusion for the instance `f`, a predicate on which facts hold.
In every attack, whenever an instance of `F` holds, its conclusion holds of the facts
that hold then.  For `F ==> ⋁ⱼ ⋀ₖ Hⱼₖ`, `H f holds` is `∃ j σ, σF = f ∧ ∀ k, holds (σHⱼₖ)`
(the survey's Def. 3.5, with `=` read as `=_E`). -/
def Corr (P : Proc M) (Hyp : Set (Fact M)) (H : Fact M → (Fact M → Prop) → Prop) : Prop :=
  ∀ t ∈ Attacks P, ∀ l, l <+: t → ∀ f ∈ Hyp, f.Holds l → H f (Fact.Holds l)

/-- Secrecy of `s`, the property that `query attacker(s)` checks: the correspondence with
hypothesis `knows s` and conclusion `False`, so that in no attack does the attacker come
to know `s`.

The survey's secrecy (Defs. 3.2, 3.3) counts the outputs on a public free name.
Whatever the attacker knows it can relay on one, so `Secret` agrees with it when the
model has a public free name; without one, the survey's counts nothing.

`s` should contain no nonce: a nonce is identified by its index, which does not say
which `new` created it. -/
def Secret (P : Proc M) (s : M) : Prop := Corr P {.knows s} fun _ _ => False

/-! ## Bounding the attacker's knowledge -/

/-- Dutertre and Schneider's condition on a user: on every prefix of `u` on which every
message received lies in `S`, every message sent or communicated lies in `S`. -/
def Bounded (S : Set M) (u : Trace M) : Prop :=
  ∀ l, l <+: u → (∀ c m, Act.inp c m ∈ l → m ∈ S) →
    ∀ c m, Act.out c m ∈ l ∨ Act.comm c m ∈ l → m ∈ S

omit [Attacker M] [Names M] in
theorem Bounded.tail {S : Set M} {a : Act M} {u : Trace M} (h : Bounded S (a :: u))
    (ha : ∀ c m, a = .inp c m → m ∈ S) : Bounded S u := by
  intro l ⟨r, hr⟩ hin c m hm
  refine h (a :: l) ⟨r, by rw [List.cons_append, hr]⟩ (fun c' m' h' => ?_) c m
    (hm.imp (List.mem_cons_of_mem a) (List.mem_cons_of_mem a))
  rcases List.mem_cons.1 h' with h' | h'
  · exact ha c' m' h'.symm
  · exact hin c' m' h'

omit [Attacker M] [Names M] in
theorem Bounded.head {S : Set M} {a : Act M} {u : Trace M} (h : Bounded S (a :: u)) {c m : M}
    (ha : a = .out c m ∨ a = .comm c m) : m ∈ S := by
  rcases ha with rfl | rfl
  · exact h [_] ⟨u, rfl⟩ (fun _ _ h' => by cases List.mem_singleton.1 h') _ _
      (Or.inl (List.mem_singleton_self _))
  · exact h [_] ⟨u, rfl⟩ (fun _ _ h' => by cases List.mem_singleton.1 h') _ _
      (Or.inr (List.mem_singleton_self _))

/-- In a closed trace of a `Bounded S` process against the enemy, every message
communicated lies in `S`, if `S` is closed under derivation and contains every nonce
and the enemy's initial knowledge. -/
theorem comm_mem_of_bounded {S : Set M} (hS : derive.IsClosed S) (hn : ∀ n, Names.nonce n ∈ S) :
    ∀ {s : List (Fin 2 × Act M)} {t : Trace M} {K : Set M}, t ∈ comms s → Closed t → K ⊆ S →
      Bounded S (proj 0 s) → proj 1 s ∈ Enemy K → ∀ c m, Act.comm c m ∈ t → m ∈ S := by
  intro s
  induction s using comms.induct with
  | case1 =>
    intro t K ht _ _ _ _ c m hm
    obtain rfl : t = [] := ht
    simp at hm
  | case2 i c m j c' m' s _ ih =>
    intro t K ht hc hK hP hE c₀ m₀ hm
    rw [comms.eq_2] at ht
    rcases ht with ⟨t₀, -, rfl⟩ | ⟨t₀, ⟨h₀, hij, rfl, rfl⟩, rfl⟩
    · exact (hc _ List.mem_cons_self (.out _ _)).elim
    have hc₀ : Closed t₀ := fun b hb => hc b (List.mem_cons_of_mem _ hb)
    simp at hP hE
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · have hmS : m ∈ S := hP.head (Or.inl rfl)
      generalize hp : proj 1 s = e at hE
      cases hE with
      | inp _ _ _ hE =>
        subst hp
        rcases List.mem_cons.1 hm with h | h
        · obtain ⟨rfl, rfl⟩ := Act.comm.inj h
          exact hmS
        · exact ih h₀ hc₀ (Set.insert_subset_iff.2 ⟨hmS, hK⟩) (hP.tail fun _ _ h => by cases h)
            hE c₀ m₀ h
    · generalize hp : proj 1 s = e at hE
      cases hE with
      | out _ _ _ hmK hE =>
        subst hp
        have hmS : m ∈ S := ClosureOperator.closure_min hK hS hmK
        rcases List.mem_cons.1 hm with h | h
        · obtain ⟨rfl, rfl⟩ := Act.comm.inj h
          exact hmS
        · refine ih h₀ hc₀ hK (hP.tail fun _ _ h => ?_) hE c₀ m₀ h
          obtain ⟨rfl, rfl⟩ := Act.inp.inj h
          exact hmS
    · exact absurd rfl hij
  | case3 i a s hne ih =>
    intro t K ht hc hK hP hE c₀ m₀ hm
    rw [comms.eq_3 _ _ _ hne] at ht
    obtain ⟨t₀, h₀, rfl⟩ := ht
    have hc₀ : Closed t₀ := fun b hb => hc b (List.mem_cons_of_mem _ hb)
    simp at hP hE
    fin_cases i
    · rcases List.mem_cons.1 hm with h | h
      · subst h
        exact hP.head (Or.inr rfl)
      · refine ih h₀ hc₀ hK (hP.tail fun _ _ ha => ?_) hE c₀ m₀ h
        subst ha
        exact (hc _ List.mem_cons_self (.inp _ _)).elim
    · generalize hp : proj 1 s = e at hE
      cases hE with
      | inp => exact (hc _ List.mem_cons_self (.inp _ _)).elim
      | out => exact (hc _ List.mem_cons_self (.out _ _)).elim
      | new n _ hE =>
        subst hp
        rcases List.mem_cons.1 hm with h | h
        · cases h
        · exact ih h₀ hc₀ (Set.insert_subset_iff.2 ⟨hn n, hK⟩) hP hE c₀ m₀ h

omit [Names M] in
/-- The attacker's knowledge stays within a closed set containing what it knew and every
message communicated. -/
theorem known_subset {S K : Set M} (hS : derive.IsClosed S) (hK : K ⊆ S) :
    ∀ {t : Trace M}, (∀ c m, Act.comm c m ∈ t → m ∈ S) → known K t ⊆ S := by
  intro t
  induction t generalizing K with
  | nil => exact fun _ => hK
  | cons a t ih =>
    intro h
    exact ih (ClosureOperator.closure_min (Set.union_subset hK fun m ⟨c, ha, _⟩ =>
      h c m (by subst ha; exact List.mem_cons_self)) hS) fun c m hm => h c m (List.mem_cons_of_mem _ hm)

/-- The closed-set method: if `S` is closed under derivation and contains every nonce, and
every trace of `P` is `Bounded S`, then at no point of an attack does the attacker know
anything outside `S`. -/
theorem known_subset_of_bounded {P : Proc M} {S : Set M} (hS : derive.IsClosed S)
    (hn : ∀ n, Names.nonce n ∈ S) (hP : ∀ u ∈ P, Bounded S u) {t l : Trace M}
    (ht : t ∈ Attacks P) (hl : l <+: t) : known (derive ∅) l ⊆ S := by
  obtain ⟨⟨⟨f, s, hf, hs, hts⟩, -⟩, hc⟩ := ht
  refine known_subset hS (ClosureOperator.closure_min (Set.empty_subset S) hS) fun c m hm =>
    comm_mem_of_bounded hS hn hts hc (Set.empty_subset S) ?_ ?_ c m (hl.subset hm)
  · rw [hs 0]
    exact hP _ (hf 0)
  · rw [hs 1]
    exact hf 1

theorem secret_of_closed {P : Proc M} {S : Set M} (hS : derive.IsClosed S)
    (hn : ∀ n, Names.nonce n ∈ S) (hP : ∀ u ∈ P, Bounded S u) {s : M} (hs : s ∉ S) :
    Secret P s := by
  rintro t ht l hl f (rfl : f = _) hf
  exact hs (known_subset_of_bounded hS hn hP ht hl hf)

/-! ## Attackers from public operations -/

/-- `S` is closed under each operation in `ops`, an operation of some arity on
may-fail arguments, `none` being `fail`.  An argument is either in `S` or `none`: the
attacker can always pass `fail`, which is an expression of the calculus. -/
def ClosedUnder (ops : Set (Σ n, (Fin n → Option M) → Option M)) (S : Set M) : Prop :=
  ∀ o ∈ ops, ∀ args : Fin o.1 → Option M, (∀ i m, args i = some m → m ∈ S) →
    ∀ r, o.2 args = some r → r ∈ S

/-- The attacker that can apply the public operations `ops`: ProVerif's
`attacker` predicate for a term algebra. -/
@[instance_reducible]
def Attacker.ofOps (ops : Set (Σ n, (Fin n → Option M) → Option M)) : Attacker M where
  derive := ClosureOperator.ofCompletePred (ClosedUnder ops) fun _ h o ho args hargs r hr => by
    simp only [Set.sInf_eq_sInter, Set.mem_sInter] at hargs ⊢
    exact fun S hS => h S hS o ho args (fun i m hm => hargs i m hm S hS) r hr

/-! ## Message algebras

The Dolev-Yao model for the messages of a theory: the nonces that `new` creates are
the algebra's names, and the attacker can apply exactly the public operations that
its `Pub` instance declares.
-/

section algebra

variable {F : Sig} {T : Theory F}

instance : Names (Msg T) := ⟨⟨Msg.name, fun _ _ => Msg.name_inj⟩⟩

instance [Pub T] : Attacker (Msg T) := .ofOps (Pub.ops T)

/-- A public constructor applied to derivable messages is derivable; in particular a
public free name is derivable from nothing. -/
theorem app_mem_derive [Pub T] {n : ℕ} {f : F n} (hf : f ∈ Pub.pubFun (T := T) n)
    {S : Set (Msg T)} {ms : Fin n → Msg T} (hms : ∀ i, ms i ∈ derive S) :
    Msg.app f ms ∈ derive S := by
  have hS : ClosedUnder (Pub.ops T) (derive S) :=
    (ClosureOperator.ofCompletePred_isClosed _ _ _).mp ((derive (M := Msg T)).isClosed_closure S)
  exact hS _ (Or.inl (Set.mem_iUnion.2 ⟨n, f, hf, rfl⟩)) (fun i => some (ms i))
    (fun i m h => Option.some_injective _ h ▸ hms i) _
    ((liftFail_eq_some (f := fun as => some (Msg.app f as))).2 ⟨ms, fun _ => rfl, rfl⟩)

end algebra

end ProVerif
