/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib.Data.Multiset.AddSub
import ScalingTrust.ProVerif.TraceSemantics.Security

/-!
# Multiset rewriting as a process

The target of the translation of Tamarin models: a labelled multiset rewriting system
as a process of the trace semantics.  Facts are messages, a state is a multiset of them,
and a rule is the set of its instances, each a `Step`: the linear facts it consumes and
the persistent facts it requires, the messages it receives, the names it creates, its
action facts, the messages it sends and the facts it produces.  A step performs a
segment of the trace, `Step.segment`: it receives its inputs, creates its names,
performs one `event`, whose message is the tuple of its action facts, and sends its
outputs, all on one public channel; the network is the attacker of the trace semantics.
`Rules.proc` is the process of a system of rules, the prefixes of the traces of its
runs from the empty state.

The atoms of Tamarin's trace formulas read a trace by position: `ActionAt t i a` is
`a @ i`, the `i`-th action of `t` being the event of a step among whose action facts is
`a`, and `KnowsAt t i m` is `K(m) @ i`, read as the attacker being able to derive `m`
from what it has heard before the `i`-th action.
-/

namespace ProVerif.TamarinTranslation

open TraceSemantics

variable {M : Type}

/-- A list of messages as one message, the tuple of them. -/
def tupleOf [StdOps M] (l : List M) : M := StdOps.tuple l.length l.get

/-- What an instance of a rule does. -/
structure Step (M : Type) where
  /-- The linear facts of its premises, removed from the state. -/
  consumed : Multiset M := 0
  /-- The persistent facts of its premises, which must be in the state. -/
  persistent : List M := []
  /-- The messages of its `In` premises, in order. -/
  inputs : List M := []
  /-- The names of its `Fr` premises, in order. -/
  fresh : List ℕ := []
  /-- Its action facts, in order. -/
  actions : List M := []
  /-- The messages of its `Out` conclusions, in order. -/
  outputs : List M := []
  /-- The facts of its other conclusions, added to the state. -/
  produced : Multiset M := 0

/-- A rule, or a system of rules: the set of its instances. -/
abbrev Rules (M : Type) := Set (Step M)

/-- The event of a step: its action facts as one message. -/
def Step.event [StdOps M] (s : Step M) : M := tupleOf s.actions

/-- The actions of a step on the channel `c`, in order: it receives its inputs, creates
its names, performs its event and sends its outputs. -/
def Step.segment [StdOps M] (c : M) (s : Step M) : Trace M :=
  s.inputs.map (Act.inp c) ++ s.fresh.map Act.new ++ [Act.event s.event] ++
    s.outputs.map (Act.out c)

/-- A configuration: the names created so far and the state, the multiset of facts. -/
structure Config (M : Type) where
  names : Set ℕ := ∅
  state : Multiset M := 0

/-- The step `s` fires in `k`, reaching `k'`: the facts it consumes are in the state and
removed, the persistent facts it requires are in the state, the names it creates are
distinct and new, and the facts it produces are added. -/
structure Step.Fires (s : Step M) (k k' : Config M) : Prop where
  state : ∃ rest, k.state = s.consumed + rest ∧ k'.state = rest + s.produced
  persistent : ∀ f ∈ s.persistent, f ∈ k.state
  fresh : s.fresh.Nodup ∧ ∀ n ∈ s.fresh, n ∉ k.names
  names : k'.names = k.names ∪ {n | n ∈ s.fresh}

/-- The runs of `R` on the channel `c` from a configuration: steps of `R`, each firing
in the configuration the previous ones reached, and the trace they perform. -/
inductive Run [StdOps M] (c : M) (R : Rules M) : Config M → Trace M → Config M → Prop
  | nil (k : Config M) : Run c R k [] k
  | cons {k k' k'' : Config M} {s : Step M} {t : Trace M} : s ∈ R → s.Fires k k' →
      Run c R k' t k'' → Run c R k (s.segment c ++ t) k''

/-- The process of `R` on the channel `c`: the prefixes of the traces of its runs from
the empty configuration. -/
def Rules.proc [StdOps M] (c : M) (R : Rules M) : Proc M :=
  {t | ∃ t' k, Run c R {} t' k ∧ t <+: t'}

theorem Rules.proc_mem_tree [StdOps M] (c : M) (R : Rules M) :
    R.proc c ∈ Descriptive.tree (Act M) :=
  fun x a ⟨t', k, h, hp⟩ => ⟨t', k, h, (List.prefix_append x [a]).trans hp⟩

/-! ## The atoms of trace formulas -/

/-- `a @ i`: the `i`-th action of `t` is the event of a step among whose action facts
is `a`. -/
def ActionAt [StdOps M] (t : Trace M) (i : ℕ) (a : M) : Prop :=
  ∃ l : List M, t[i]? = some (Act.event (tupleOf l)) ∧ a ∈ l

/-- `K(m) @ i`: the attacker can derive `m` from what it has heard before the `i`-th
action of `t`. -/
def KnowsAt [Attacker M] (t : Trace M) (i : ℕ) (m : M) : Prop :=
  m ∈ Trace.attackerKnowledge (Attacker.derive ∅) (t.take i)

end ProVerif.TamarinTranslation
