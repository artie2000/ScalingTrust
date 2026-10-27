/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.TraceSemantics.Security

/-!
# Queries

The properties that ProVerif's correspondence queries state, read on the attacks of a
process (manual §4.3.1).  A query `F₁ && … && Fₙ ==> H` has facts before its arrow and a
hypothesis `H` after it, built from facts with `&&`, `||`, `false` and nested
correspondences `F ==> H`; an event fact may be injective.  Its facts hold at *steps* of a
trace: an action fact at the step that performs the action, a knowledge fact at every step
after which the attacker knows the message, an equality or a disequality of messages at
every step when it holds, and `F before e` at the steps where `F` holds and the event `e`
has not yet occurred, which states a fact of a phase once phases are compiled out.  An
injective `attacker(M)` before the arrow is the acquisition `learns`, which holds at the
one step at which the attacker comes to know the message, so that its executions are
counted as those of an event are.  The query holds of a trace when, for every substitution and every choice of
steps at which the facts before the arrow hold, some instance of the hypothesis is
witnessed by steps no later than the last of them: a fact at such a step, and a nested
correspondence by a step of its own fact, before which its hypothesis is witnessed in
turn.  An injective fact of the hypothesis must be witnessed by distinct steps for distinct
tuples of steps of the injective facts before the arrow.

The definitions are generic in the facts, so that the specification of ProVerif's calculus
states the same semantics for its own facts; `QFact` and `QFact.HoldsAt` are the facts of
the trace semantics, and `Proc.Satisfies` the property of a process.  `Proofs/Query.lean`
reduces the basic queries, one fact before the arrow and a fact or `false` after it, to
`Proc.Corr` and `Proc.Secret` of `Security.lean`, and refutes a query on an attack.
-/

namespace ProVerif.TraceSemantics

open Attacker (derive)

variable {M : Type}

/-! ## Hypotheses and queries -/

/-- The hypothesis of a correspondence over the facts `Φ`: a fact, injective or not; a
conjunction; a disjunction; `false`; or a nested correspondence `F ==> H`, whose fact may be
injective. -/
inductive Hyp (Φ : Type) where
  | fact (inj : Bool) (F : Φ)
  | and (H₁ H₂ : Hyp Φ)
  | or (H₁ H₂ : Hyp Φ)
  | false
  | corr (inj : Bool) (F : Φ) (H : Hyp Φ)

/-- A query: the facts before the arrow, each marked if injective, and the hypothesis after
it. -/
structure Query (Φ : Type) where
  premise : List (Bool × Φ)
  concl : Hyp Φ

namespace Hyp

variable {Φ Ψ : Type}

def map (f : Φ → Ψ) : Hyp Φ → Hyp Ψ
  | .fact inj F => .fact inj (f F)
  | .and H₁ H₂ => .and (H₁.map f) (H₂.map f)
  | .or H₁ H₂ => .or (H₁.map f) (H₂.map f)
  | .false => .false
  | .corr inj F H => .corr inj (f F) (H.map f)

/-- The paths to the injective facts: `false` descends left in a conjunction or a
disjunction, `true` right, and into the hypothesis of a nested correspondence, whose own fact
is at the empty path. -/
def injPaths : Hyp Φ → List (List Bool)
  | .fact inj _ => if inj then [[]] else []
  | .and H₁ H₂ | .or H₁ H₂ =>
    H₁.injPaths.map (Bool.false :: ·) ++ H₂.injPaths.map (Bool.true :: ·)
  | .false => []
  | .corr inj _ H => (if inj then [[]] else []) ++ H.injPaths.map (Bool.true :: ·)

/-- The facts of a hypothesis, those of its nested correspondences included. -/
def facts : Hyp Φ → List Φ
  | .fact _ F => [F]
  | .and H₁ H₂ | .or H₁ H₂ => H₁.facts ++ H₂.facts
  | .false => []
  | .corr _ F H => F :: H.facts

end Hyp

def Query.map {Φ Ψ : Type} (f : Φ → Ψ) (q : Query Φ) : Query Ψ :=
  ⟨q.premise.map fun F => (F.1, f F.2), q.concl.map f⟩

/-- A witness of a hypothesis: a step for each fact, a side for each disjunction. -/
inductive Wit where
  | fact (j : ℕ)
  | and (w₁ w₂ : Wit)
  | orL (w : Wit)
  | orR (w : Wit)
  | corr (j : ℕ) (w : Wit)

/-- The step chosen for the fact at a path, if the witness has one there. -/
def Wit.pos : Wit → List Bool → Option ℕ
  | .fact j, [] => some j
  | .and w₁ _, false :: p => w₁.pos p
  | .and _ w₂, true :: p => w₂.pos p
  | .orL w, false :: p => w.pos p
  | .orR w, true :: p => w.pos p
  | .corr j _, [] => some j
  | .corr _ w, true :: p => w.pos p
  | _, _ => none

section sat

variable {A S : Type}

/-- The witness `w` shows the hypothesis `H` by step `d`, `holdsAt F i` saying that the
fact `F` holds at step `i`: a fact at a step no later than `d`, and a nested correspondence
at a step `j ≤ d` of its fact, before which its hypothesis is witnessed. -/
def Hyp.Sat (holdsAt : A → ℕ → Prop) : Hyp A → Wit → ℕ → Prop
  | .fact _ F, .fact j, d => j ≤ d ∧ holdsAt F j
  | .and H₁ H₂, .and w₁ w₂, d => H₁.Sat holdsAt w₁ d ∧ H₂.Sat holdsAt w₂ d
  | .or H₁ _, .orL w, d => H₁.Sat holdsAt w d
  | .or _ H₂, .orR w, d => H₂.Sat holdsAt w d
  | .corr _ F H, .corr j w, d => j ≤ d ∧ holdsAt F j ∧ H.Sat holdsAt w j
  | _, _, _ => False

namespace Query

variable (holdsAt : A → ℕ → Prop) (n : ℕ) (q : Query (S → A))

/-- The facts before the arrow hold under `σ` at the steps `ps`, within the `n` steps. -/
def Valid (σ : S) (ps : List ℕ) : Prop :=
  List.Forall₂ (fun (F : Bool × (S → A)) p => p ≤ n ∧ holdsAt (F.2 σ) p) q.premise ps

/-- The steps of the injective facts before the arrow. -/
def injPos (ps : List ℕ) : List ℕ :=
  ((q.premise.zip ps).filter (·.1.1)).map (·.2)

/-- A trace of `n` steps satisfies the query: for every `σ` and steps `ps` at which the facts
before the arrow hold, some `σ'` giving them the same instances has the hypothesis
witnessed by the last of the steps, and an injective fact of the hypothesis is witnessed at
distinct steps for distinct tuples of steps of the injective facts before the arrow. -/
def Sat : Prop :=
  ∃ w : (σ : S) → (ps : List ℕ) → q.Valid holdsAt n σ ps → Wit,
    (∀ σ ps (hv : q.Valid holdsAt n σ ps), ∃ σ' : S, (∀ F ∈ q.premise, F.2 σ' = F.2 σ) ∧
      (q.concl.map (· σ')).Sat holdsAt (w σ ps hv) (ps.foldr max 0)) ∧
    ∀ π ∈ q.concl.injPaths, ∀ σ₁ ps₁ (hv₁ : q.Valid holdsAt n σ₁ ps₁) σ₂ ps₂
      (hv₂ : q.Valid holdsAt n σ₂ ps₂) j, (w σ₁ ps₁ hv₁).pos π = some j →
        (w σ₂ ps₂ hv₂).pos π = some j → q.injPos ps₁ = q.injPos ps₂

/-- Satisfaction depends on the facts only through where they hold. -/
theorem sat_congr {holdsAt' : A → ℕ → Prop} (h : ∀ F i, holdsAt F i ↔ holdsAt' F i) :
    q.Sat holdsAt n ↔ q.Sat holdsAt' n := by
  have hv : ∀ σ ps, q.Valid holdsAt n σ ps ↔ q.Valid holdsAt' n σ ps := fun σ ps =>
    ⟨fun hv => hv.imp fun F p hp => ⟨hp.1, (h _ _).1 hp.2⟩,
      fun hv => hv.imp fun F p hp => ⟨hp.1, (h _ _).2 hp.2⟩⟩
  have hs : ∀ (H : Hyp A) (w : Wit) (d : ℕ), H.Sat holdsAt w d ↔ H.Sat holdsAt' w d := by
    intro H
    induction H with
    | fact inj F => intro w d; cases w <;> simp [Hyp.Sat, h]
    | and H₁ H₂ ih₁ ih₂ => intro w d; cases w <;> simp [Hyp.Sat, ih₁, ih₂]
    | or H₁ H₂ ih₁ ih₂ => intro w d; cases w <;> simp [Hyp.Sat, ih₁, ih₂]
    | false => intro w d; cases w <;> simp [Hyp.Sat]
    | corr inj F H ih => intro w d; cases w <;> simp [Hyp.Sat, h, ih]
  constructor
  · rintro ⟨w, h₁, h₂⟩
    refine ⟨fun σ ps hv' => w σ ps ((hv σ ps).2 hv'), fun σ ps hv' => ?_,
      fun π hπ σ₁ ps₁ hv₁ σ₂ ps₂ hv₂ j => h₂ π hπ σ₁ ps₁ _ σ₂ ps₂ _ j⟩
    obtain ⟨σ', hσ', hs'⟩ := h₁ σ ps ((hv σ ps).2 hv')
    exact ⟨σ', hσ', (hs _ _ _).1 hs'⟩
  · rintro ⟨w, h₁, h₂⟩
    refine ⟨fun σ ps hv' => w σ ps ((hv σ ps).1 hv'), fun σ ps hv' => ?_,
      fun π hπ σ₁ ps₁ hv₁ σ₂ ps₂ hv₂ j => h₂ π hπ σ₁ ps₁ _ σ₂ ps₂ _ j⟩
    obtain ⟨σ', hσ', hs'⟩ := h₁ σ ps ((hv σ ps).1 hv')
    exact ⟨σ', hσ', (hs _ _ _).2 hs'⟩

end Query

end sat

/-! ## The facts of the trace semantics -/

/-- A fact of a query: an event executed, a message known to the attacker, a message
acquired by the attacker, which is `knows` at the first step at which it holds and
stands for an injective `attacker(M)` before the arrow, a message communicated on a
channel, an equality or a disequality of messages, or a fact before the first occurrence
of an event. -/
inductive QFact (M : Type) where
  | event (e : M)
  | knows (m : M)
  | learns (m : M)
  | mess (c m : M)
  | eq (m n : M)
  | ne (m n : M)
  | before (F : QFact M) (e : M)

/-- The facts of `Security.lean`, as facts of a query. -/
def Fact.toQ : Fact M → QFact M
  | .event e => .event e
  | .knows m => .knows m

variable [Attacker M]

/-- The fact holds at step `i` of `t`, the `i`-th action being `t[i-1]`: an action fact when
that action is the action, a knowledge fact when the attacker knows the message after the
first `i` actions, an acquisition when it knows the message after `i` actions and not
after `i - 1`, an equality or a disequality at every step when it holds of the messages,
and `F before e` when `F` holds and no action so far is the event `e`. -/
def QFact.HoldsAt (t : Trace M) : QFact M → ℕ → Prop
  | .event e, i => 0 < i ∧ t[i - 1]? = some (.event e)
  | .mess c m, i => 0 < i ∧ t[i - 1]? = some (.comm c m)
  | .knows m, i => m ∈ Trace.attackerKnowledge (derive ∅) (t.take i)
  | .learns m, i => m ∈ Trace.attackerKnowledge (derive ∅) (t.take i) ∧
      (i = 0 ∨ m ∉ Trace.attackerKnowledge (derive ∅) (t.take (i - 1)))
  | .eq m n, _ => m = n
  | .ne m n, _ => m ≠ n
  | .before F e, i => F.HoldsAt t i ∧ Act.event e ∉ t.take i

/-- The property that a query states of `P`: every attack satisfies the query, whose facts
are functions of a valuation of the query's variables `X`. -/
def Proc.Satisfies [Names M] (P : Proc M) {X : Type} (q : Query ((X → M) → QFact M)) : Prop :=
  ∀ t ∈ P.Attacks, q.Sat (QFact.HoldsAt t) t.length

end ProVerif.TraceSemantics
