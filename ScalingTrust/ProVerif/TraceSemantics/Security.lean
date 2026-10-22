/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib.Order.Closure
import ScalingTrust.ProVerif.TraceSemantics.Data
import ScalingTrust.ProVerif.TraceSemantics.Process

/-!
# The attacker and the security properties

The attacker is a process, `Enemy K`: the traces a Dolev-Yao attacker knowing
`K` can perform.  It may receive on any channel it can derive, send anything it
can derive on any channel it can derive, and create names.  It may also send to
itself, a `comm` that needs no partner: the survey's Definition 3.2 counts an
adversary's output on a public channel whoever receives it, and so does
`Trace.attackerKnowledge`.  What it can derive from a set of messages is the closure
under its operations, `Attacker.derive`.  The operations are canonical for a type of
messages, declared along with its symbols, so they are an instance of the class
`Attacker`, from which everything here infers the closure.  A translated model builds its
instance from its public declarations with `Attacker.ofDecls`, at the end of this file,
which adds the standard operations, tuples and booleans (`StdOps`, in `Data.lean`).

An *attack* on `P` is a trace of `P | Enemy ∅` in which every communication was
completed; `P.Attacks` is the process of attacks.  The attacker starts from
nothing: the public free names are public constants, derivable from nothing.

What the attacker knows after a trace, `Trace.attackerKnowledge`, is read off its
communications: a message sent on a channel the attacker knew at the time becomes
known, whoever received it, since the attacker could have received it instead.  A
`Fact` of a query holds or not after an attack; `Proc.Secret` is `query attacker(s)`
and `Proc.Corr` is `query F ==> H`.  A prefix of an attack is an attack, so a property
of every attack is a property of every point of every attack.  The methods for proving
and refuting these properties are in `Proofs/`.

Nothing here distinguishes public from private channels: a private channel is
a term the attacker cannot derive, on which it therefore makes no offers and
from which it learns nothing.
-/

namespace ProVerif.TraceSemantics

open Descriptive

variable {M : Type}

/-! ## The attacker's operations

The attacker has the standard operations on messages, `StdOps`, along with the public
operations of the model; the whole is an `Attacker` instance, of which `Attacker.derive` is
the knowledge closure. -/

/-- `S` is closed under each operation in `ops`, an operation of some arity on
may-fail arguments, `none` being `fail`.  An argument is either in `S` or `none`: the
attacker can always produce `fail`, which the survey's clause (Rfail) gives it outright
(§3.2.2) and which `if false then true` with its `else` omitted evaluates to in the input
language (manual §4.1.4). -/
def ClosedUnder (ops : Set (Σ n, (Fin n → Option M) → Option M)) (S : Set M) : Prop :=
  ∀ o ∈ ops, ∀ args : Fin o.1 → Option M, (∀ i m, args i = some m → m ∈ S) →
    ∀ r, o.2 args = some r → r ∈ S

/-- What an attacker that can apply the operations `ops` derives: ProVerif's
`attacker` predicate for a term algebra. -/
def deriveOfOps (ops : Set (Σ n, (Fin n → Option M) → Option M)) : ClosureOperator (Set M) :=
  ClosureOperator.ofCompletePred (ClosedUnder ops) fun _ h o ho args hargs r hr => by
    simp only [Set.sInf_eq_sInter, Set.mem_sInter] at hargs ⊢
    exact fun S hS => h S hS o ho args (fun i m hm => hargs i m hm S hS) r hr

/-- The standard operations as operations on may-fail arguments: the tuple constructors,
the projections, and the booleans.  The boolean connectives yield only booleans, which the
attacker has, so they are not among them. -/
def StdOps.ops (M : Type) [StdOps M] : Set (Σ n, (Fin n → Option M) → Option M) :=
  Set.range (fun n : ℕ => (⟨n, liftFail fun a => some (tuple n a)⟩ :
      Σ n, (Fin n → Option M) → Option M)) ∪
  Set.range (fun p : Σ n, Fin n => (⟨1, liftFail fun a => (untuple p.1 (a 0)).map (· p.2)⟩ :
      Σ n, (Fin n → Option M) → Option M)) ∪
  {⟨0, fun _ => some tt⟩, ⟨0, fun _ => some ff⟩}

/-- The attacker's operations, canonical for a type of messages: each of some arity on
may-fail arguments, `none` being `fail`. -/
class Attacker (M : Type) where
  ops : Set (Σ n, (Fin n → Option M) → Option M)

/-- The attacker's knowledge closure: what it derives from a set of messages with its
operations, ProVerif's `attacker` predicate. -/
def Attacker.derive [Attacker M] : ClosureOperator (Set M) := deriveOfOps Attacker.ops

open Attacker (derive)

/-- A destructor among the attacker's operations, applied to derivable messages on which
it succeeds, yields a derivable message. -/
theorem Attacker.dtor_mem_derive [Attacker M] {n : ℕ} {f : (Fin n → M) → Option M}
    (hf : (⟨n, liftFail f⟩ : Σ n, (Fin n → Option M) → Option M) ∈ Attacker.ops)
    {S : Set M} {ms : Fin n → M} (hms : ∀ i, ms i ∈ derive S) {r : M} (h : f ms = some r) :
    r ∈ derive S := by
  have hS : ClosedUnder Attacker.ops (derive S) := derive.isClosed_closure S
  exact hS _ hf (fun i => some (ms i)) (fun i m h => Option.some_injective _ h ▸ hms i) _
    (liftFail_eq_some.2 ⟨ms, fun _ => rfl, h⟩)

/-! ## The attacker's knowledge -/

section knowledge

variable [Attacker M]

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
  | .knows m => m ∈ t.attackerKnowledge (derive ∅)

theorem Trace.subset_attackerKnowledge (K : Set M) :
    ∀ t : Trace M, K ⊆ t.attackerKnowledge K
  | [] => le_rfl
  | _ :: t =>
    (Set.subset_union_left.trans (derive.le_closure _)).trans (subset_attackerKnowledge _ t)

theorem Trace.attackerKnowledge_mono {K K' : Set M} (h : K ⊆ K') :
    ∀ t : Trace M, t.attackerKnowledge K ⊆ t.attackerKnowledge K'
  | [] => h
  | _ :: t =>
    attackerKnowledge_mono
      (derive.monotone (Set.union_subset_union h (by rintro m ⟨c, ha, hc⟩; exact ⟨c, ha, h hc⟩))) t

theorem Trace.isClosed_attackerKnowledge {K : Set M} (hK : derive.IsClosed K) :
    ∀ t : Trace M, derive.IsClosed (t.attackerKnowledge K)
  | [] => hK
  | _ :: t => isClosed_attackerKnowledge (derive.isClosed_closure _) t

theorem Trace.attackerKnowledge_append (K : Set M) (t t' : Trace M) :
    (t ++ t').attackerKnowledge K = Trace.attackerKnowledge (t.attackerKnowledge K) t' :=
  List.foldl_append ..

/-- What the attacker knows after a prefix it knows after the trace. -/
theorem Trace.attackerKnowledge_take_subset (K : Set M) (t : Trace M) (i : ℕ) :
    Trace.attackerKnowledge K (t.take i) ⊆ t.attackerKnowledge K := by
  conv_rhs => rw [← List.take_append_drop i t]
  rw [attackerKnowledge_append]
  exact subset_attackerKnowledge _ _

end knowledge

/-! ## The attacker as a process, and the security properties -/

section

variable [Names M] [Attacker M]

/-- `Enemy K`: the attacker, knowing `K`, as a process. -/
inductive Enemy : Set M → Proc M
  | nil {K} : Enemy K []
  | inp {K e} (c m : M) : c ∈ derive K → e ∈ Enemy (insert m K) →
      Enemy K (.inp c m :: e) -- defeq abuse for `(.inp c m :: e) ∈ Enemy K`, etc.
  | out {K e} (c m : M) : c ∈ derive K → m ∈ derive K → e ∈ Enemy K →
      Enemy K (.out c m :: e)
  | comm {K e} (c m : M) : c ∈ derive K → m ∈ derive K → e ∈ Enemy K →
      Enemy K (.comm c m :: e)
  | new {K} {e : Trace M} (n : ℕ) : n ∉ e.nonces → e ∈ Enemy (insert (Names.nonce n) K) →
      Enemy K (.new n :: e)

/-- The enemy is prefix-closed: it can stop at any point. -/
theorem Enemy.mem_tree (K : Set M) : Enemy K ∈ tree (Act M) := by
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
def Proc.Attacks (P : Proc M) : Proc M := {t ∈ P.par (Enemy ∅) | t.Closed}

/-- A prefix of an attack on a prefix-closed process is an attack. -/
theorem Proc.attacks_mem_tree {P : Proc M} (hP : P ∈ tree (Act M)) :
    P.Attacks ∈ tree (Act M) := fun _ _ ⟨ht, hc⟩ =>
  ⟨Tree.mem_of_append (T := ⟨_, Proc.par_mem_tree hP (Enemy.mem_tree ∅)⟩) ht,
    fun b hb => hc b (List.mem_append_left _ hb)⟩

/-- The correspondence that `query F ==> H` checks, for query facts `F` and `H` over the
variables `X`, written as functions of a valuation `σ : X → M`: in every attack in which an
instance `F σ` holds, `H σ'` holds for some `σ'` with `F σ' = F σ`, the survey's Def. 3.5
with `=` read as `=_E`.  For a prefix-closed `P` the attacks are prefix-closed, so `H σ'`
holds by the time `F σ` does. -/
def Proc.Corr (P : Proc M) {X : Type} (F H : (X → M) → Fact M) : Prop :=
  ∀ (σ : X → M), ∀ t ∈ P.Attacks, (F σ).Holds t → ∃ σ', F σ' = F σ ∧ (H σ').Holds t

/-- Secrecy of `s`, the property that `query attacker(s)` checks: in no attack does the
attacker come to know `s`, the reachability of the fact as ProVerif decides it, which the
specification's `Model.Preserves` states for the calculus; the survey's secrecy by an
output on a public free name (Defs. 3.2, 3.3) is not followed, for the reason given there.

`s` should contain no nonce: a nonce is identified by its index, which does not say
which `new` created it. -/
def Proc.Secret (P : Proc M) (s : M) : Prop :=
  ∀ t ∈ P.Attacks, ¬ (Fact.knows s).Holds t

end

/-! ## The messages of a model

The messages of a model are `T.withData.Msg`, for `T` the theory of its declarations.  The
nonces that `new` creates are the names, and the attacker's operations are the public
declarations, the constructors and free names not marked `[private]` and the public
destructors, with the standard operations.
-/

section model

variable {F : Sig} {T : Theory F}

instance : Names T.Msg := ⟨⟨.name, fun _ _ => Theory.Msg.name_inj⟩⟩

/-- The attacker of a model, from its declarations: the public constructors, including the
public free names, which fail when an argument does, the public destructors, each of some
arity on may-fail arguments, written as in `Term.lean`, and the standard operations. -/
@[instance_reducible]
def Attacker.ofDecls (pubFun : ∀ n, Set (F n))
    (pubDtors : Set (Σ n, (Fin n → Option T.withData.Msg) → Option T.withData.Msg)) :
    Attacker T.withData.Msg :=
  ⟨(⋃ n, (fun f : F n => (⟨n, liftFail fun as => some (.app (.inl f) as)⟩ :
    Σ n, (Fin n → Option T.withData.Msg) → Option T.withData.Msg)) '' pubFun n) ∪ pubDtors ∪
    StdOps.ops _⟩

/-- A public constructor is among the operations of `Attacker.ofDecls`. -/
theorem Attacker.ofDecls_mem {pubFun : ∀ n, Set (F n)}
    {pubDtors : Set (Σ n, (Fin n → Option T.withData.Msg) → Option T.withData.Msg)} {n : ℕ}
    {f : F n} (hf : f ∈ pubFun n) :
    (⟨n, liftFail fun as => some (.app (.inl f) as)⟩ :
      Σ n, (Fin n → Option T.withData.Msg) → Option T.withData.Msg) ∈
      (Attacker.ofDecls pubFun pubDtors).ops :=
  Or.inl (Or.inl (Set.mem_iUnion.2 ⟨n, f, hf, rfl⟩))

/-- A public destructor is among the operations of `Attacker.ofDecls`. -/
theorem Attacker.ofDecls_mem_dtor {pubFun : ∀ n, Set (F n)}
    {pubDtors : Set (Σ n, (Fin n → Option T.withData.Msg) → Option T.withData.Msg)}
    {o : Σ n, (Fin n → Option T.withData.Msg) → Option T.withData.Msg} (h : o ∈ pubDtors) :
    o ∈ (Attacker.ofDecls pubFun pubDtors).ops :=
  Or.inl (Or.inr h)

/-- A constructor among the attacker's operations, applied to derivable messages, is
derivable; in particular a public free name is derivable from nothing. -/
theorem Attacker.app_mem_derive [Attacker T.Msg] {n : ℕ} {f : F n}
    (hf : (⟨n, liftFail fun as => some (.app f as)⟩ :
      Σ n, (Fin n → Option T.Msg) → Option T.Msg) ∈ Attacker.ops)
    {S : Set T.Msg} {ms : Fin n → T.Msg} (hms : ∀ i, ms i ∈ derive S) :
    .app f ms ∈ derive S := by
  have hS : ClosedUnder Attacker.ops (derive S) := derive.isClosed_closure S
  exact hS _ hf (fun i => some (ms i)) (fun i m h => Option.some_injective _ h ▸ hms i) _
    ((liftFail_eq_some (f := fun as => some (Theory.Msg.app f as))).2 ⟨ms, fun _ => rfl, rfl⟩)

end model

end ProVerif.TraceSemantics
