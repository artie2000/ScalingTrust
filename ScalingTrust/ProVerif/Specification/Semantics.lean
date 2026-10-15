/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib.Data.Multiset.Basic
import ScalingTrust.ProVerif.Specification.Syntax
import ScalingTrust.ProVerif.TraceSemantics.Security

/-!
# The operational semantics of ProVerif's calculus

The write-up's §2.1, the semantics of Blanchet's survey (§2.4, §2.5.1, §3.1–3.3)
taken modulo `=_E`, and its Definition "Labelled semantics", as one step relation.

* **Messages.** The definitions are read on messages, `A.Msg`, terms modulo `E`: a
  closed term `M` denotes `Tm.msg A M`, and every `=_E` of the survey is an equality of
  messages.  In particular a rule's patterns are matched against messages, and a
  substitution `σ` with `σ p =_E u` is a `Pat.Matching` on messages.
* **Evaluation** `Eval A D u` of a closed expression to a may-fail message, `none` being
  `fail`: a destructor rewrites by the first of its rules that matches, and fails when
  none does, the survey's final rule `h(u⃗) → fail`.
* **Configurations** are a finite set `U` of created names and a multiset of closed
  processes.  The survey's `(N_pub, N_priv)` are the public and the private nullary
  constructors, fixed by the model, and the created names are `ν_k` for `k ∈ U`.
* **Steps** are labelled by `Option (Act A.Msg)`: `none` is a `τ`-step, (Red Nil), (Red
  Par), (Red Repl), (Red Eval) and (Red Cond); the other rules carry the action of the
  trace semantics.  The survey's reduction is a step whose label is not an offer: (Red
  I/O') is the step labelled `comm`, (Red Res) the step labelled `new`, and (Red Event)
  the step labelled `event`.  A trace of the survey is therefore a run whose labels are
  closed; the `out` and `inp` steps are the offers of a process to its environment.
* **Runs** `Runs A c t`: `c` performs the weak trace `t`, `τ`-steps elided.
* **The survey's definitions** 3.1–3.5 and the write-up's Definitions "Satisfaction" and
  "Correspondences between facts", for single query facts.
-/

namespace ProVerif.Specification

open FirstOrder FirstOrder.Language ProVerif.TraceSemantics

variable {F G : Sig}

/-- A closed term's message. -/
def Tm.msg (A : Model F G) (M : Tm F 0) : A.Msg := M.realize (Sum.elim Theory.Msg.name finZeroElim)

variable {A : Model F G} {n : ℕ}

/-! ## Destructors -/

/-- `θ, μ` is a matching of the may-fail message `u` against the pattern: ordinary
variables are sent to messages and may-fail variables to may-fail messages, and a
constructor pattern matches a message with that constructor at its root. -/
def Pat.Matching (θ : ℕ → A.Msg) (μ : ℕ → Option A.Msg) : Pat F → Option A.Msg → Prop
  | .var x, u => u = some (θ x)
  | .mvar v, u => u = μ v
  | .fail, u => u = none
  | .app f args, u => ∃ ms, u = some (Theory.Msg.app f ms) ∧ ∀ i, (args i).Matching θ μ (some (ms i))

/-- A right-hand side under a matching. -/
def Rhs.eval (θ : ℕ → A.Msg) (μ : ℕ → Option A.Msg) : Rhs F → Option A.Msg
  | .fail => none
  | .mvar u => μ u
  | .term M => some (M.realize θ)

/-- A matching of the arguments against the patterns of a rule. -/
def Rule.Matching (r : Rule A.toTheory n) (θ : ℕ → A.Msg) (μ : ℕ → Option A.Msg)
    (us : Fin n → Option A.Msg) : Prop :=
  ∀ i, (r.pats i).Matching θ μ (us i)

/-- The rules rewrite the arguments to `v`: the first rule that matches decides, and
the result is `fail` when none does. -/
inductive Rewrites : List (Rule A.toTheory n) → (Fin n → Option A.Msg) → Option A.Msg → Prop
  | nil (us) : Rewrites [] us none
  | head {r rs us θ μ} : r.Matching θ μ us → Rewrites (r :: rs) us (r.rhs.eval θ μ)
  | tail {r rs us v} : (¬ ∃ θ μ, r.Matching θ μ us) → Rewrites rs us v → Rewrites (r :: rs) us v

variable (A)

/-! ## Evaluation of expressions -/

/-- `D ⇓ u`, for a closed expression. -/
inductive Eval : Expr F G (ℕ ⊕ Fin 0) → Option A.Msg → Prop
  | term (M) : Eval (.term M) (some (Tm.msg A M))
  | fail : Eval .fail none
  | ctor {m : ℕ} (f : F m) {args us} : (∀ i, Eval (args i) (us i)) →
      Eval (.ctor f args) (liftFail (fun ms => some (Theory.Msg.app f ms)) us)
  | dtor {m : ℕ} (g : G m) {args us v} : (∀ i, Eval (args i) (us i)) →
      Rewrites (A.dtor g) us v → Eval (.dtor g args) v

/-! ## Reduction -/

/-- A configuration: the created names and the running processes. -/
structure Config (F G : Sig) where
  /-- The indices of the names created so far. -/
  names : Finset ℕ
  /-- The processes, a multiset. -/
  procs : Multiset (Process F G 0)

/-- The labelled steps, `none` being `τ`. -/
inductive Step : Config F G → Option (Act A.Msg) → Config F G → Prop
  /-- (Red Nil) -/
  | nil {U Ps} : Step ⟨U, .nil ::ₘ Ps⟩ none ⟨U, Ps⟩
  /-- (Red Par) -/
  | par {U Ps} (P Q) : Step ⟨U, .par P Q ::ₘ Ps⟩ none ⟨U, P ::ₘ Q ::ₘ Ps⟩
  /-- (Red Repl) -/
  | bang {U Ps} (P) : Step ⟨U, .bang P ::ₘ Ps⟩ none ⟨U, P ::ₘ .bang P ::ₘ Ps⟩
  /-- (Red Res): the created name is `ν_k` for a fresh `k`. -/
  | new {U Ps} (P) (k : ℕ) : k ∉ U →
      Step ⟨U, .new P ::ₘ Ps⟩ (some (.new k)) ⟨insert k U, P.inst (.var (.inl k)) ::ₘ Ps⟩
  /-- (Red I/O') -/
  | comm {U Ps} (N M Q N' P) : Tm.msg A N = Tm.msg A N' →
      Step ⟨U, .out N M Q ::ₘ .inp N' P ::ₘ Ps⟩ (some (.comm (Tm.msg A N) (Tm.msg A M)))
        ⟨U, Q ::ₘ P.inst M ::ₘ Ps⟩
  /-- (Red Eval 1), for any term of the value -/
  | eval₁ {U Ps} (D P Q M) : Eval A D (some (Tm.msg A M)) →
      Step ⟨U, .let_ D P Q ::ₘ Ps⟩ none ⟨U, P.inst M ::ₘ Ps⟩
  /-- (Red Eval 2) -/
  | eval₂ {U Ps} (D P Q) : Eval A D none → Step ⟨U, .let_ D P Q ::ₘ Ps⟩ none ⟨U, Q ::ₘ Ps⟩
  /-- (Red Cond 1') -/
  | cond₁ {U Ps} (M P Q) : Tm.msg A M = Theory.Msg.app A.tt ![] →
      Step ⟨U, .ite M P Q ::ₘ Ps⟩ none ⟨U, P ::ₘ Ps⟩
  /-- (Red Cond 2') -/
  | cond₂ {U Ps} (M P Q) : Tm.msg A M ≠ Theory.Msg.app A.tt ![] →
      Step ⟨U, .ite M P Q ::ₘ Ps⟩ none ⟨U, Q ::ₘ Ps⟩
  /-- (Red Event) -/
  | event {U Ps} (M P) : Step ⟨U, .event M P ::ₘ Ps⟩ (some (.event (Tm.msg A M))) ⟨U, P ::ₘ Ps⟩
  /-- An offer to send. -/
  | out {U Ps} (N M P) :
      Step ⟨U, .out N M P ::ₘ Ps⟩ (some (.out (Tm.msg A N) (Tm.msg A M))) ⟨U, P ::ₘ Ps⟩
  /-- An offer to receive any closed term. -/
  | inp {U Ps} (N P M) :
      Step ⟨U, .inp N P ::ₘ Ps⟩ (some (.inp (Tm.msg A N) (Tm.msg A M))) ⟨U, P.inst M ::ₘ Ps⟩

/-- `c` performs the weak trace `t`: its visible labels in order, `τ`-steps elided. -/
inductive Runs : Config F G → Trace A.Msg → Prop
  | nil (c) : Runs c []
  | tau {c c' t} : Step A c none c' → Runs c' t → Runs c t
  | act {c c' a t} : Step A c (some a) c' → Runs c' t → Runs c (a :: t)

/-- The weak traces of a configuration. -/
def Config.traces (c : Config F G) : Proc A.Msg := {t | Runs A c t}

/-! ## The survey's definitions -/

/-- The public names: the public nullary constructors. -/
def Model.Npub : Set (F 0) := A.pubFun 0

/-- Every symbol of the term is public, and no created name occurs. -/
def Model.PubTerm : Tm F n → Prop
  | .var (.inl _) => False
  | .var (.inr _) => True
  | .func f ts => f ∈ A.pubFun _ ∧ ∀ i, Model.PubTerm (ts i)

/-- Every symbol of the expression is public, and no created name occurs. -/
def Model.PubExpr : Expr F G (ℕ ⊕ Fin n) → Prop
  | .term M => A.PubTerm M
  | .ctor f args => f ∈ A.pubFun _ ∧ ∀ i, Model.PubExpr (args i)
  | .dtor g args => g ∈ A.pubDtor _ ∧ ∀ i, Model.PubExpr (args i)
  | .fail => True

/-- An `N_pub`-adversary, the survey's Definition 3.1: its names and symbols are public
and it has no event. -/
def Model.Adversary : ∀ {n : ℕ}, Process F G n → Prop
  | _, .nil => True
  | _, .out N M P => A.PubTerm N ∧ A.PubTerm M ∧ Model.Adversary P
  | _, .inp N P => A.PubTerm N ∧ Model.Adversary P
  | _, .par P Q => Model.Adversary P ∧ Model.Adversary Q
  | _, .bang P => Model.Adversary P
  | _, .new P => Model.Adversary P
  | _, .let_ D P Q => A.PubExpr D ∧ Model.Adversary P ∧ Model.Adversary Q
  | _, .ite M P Q => A.PubTerm M ∧ Model.Adversary P ∧ Model.Adversary Q
  | _, .event _ _ => False

/-- The configuration `C_Q` of the protocol `P₀` against the adversary `Q`. -/
def Config.against (P₀ Q : Process F G 0) : Config F G := ⟨∅, {P₀, Q}⟩

/-- A trace of the survey from `c`: a run whose labels are closed, the survey's
reduction having no rule for an offer. -/
def Model.SurveyTrace (c : Config F G) (t : Trace A.Msg) : Prop := Runs A c t ∧ t.Closed

/-- The trace outputs `m` publicly, the survey's Definition 3.2: a communication on a
public name carries it. -/
def Model.OutputsPublicly (t : Trace A.Msg) (m : A.Msg) : Prop :=
  ∃ a ∈ A.Npub, Act.comm (Theory.Msg.app a ![]) m ∈ t

/-- `P₀` preserves the secrecy of the closed term `M` from `N_pub`, the survey's
Definition 3.3. -/
def Model.Preserves (P₀ : Process F G 0) (M : Tm F 0) : Prop :=
  ∀ Q, A.Adversary Q → ∀ t, A.SurveyTrace (.against P₀ Q) t → ¬ A.OutputsPublicly t (Tm.msg A M)

/-- A query fact over the variables `X`: `event(M)` or `attacker(M)` with `M` a term
over constructors, free names and `X`. -/
inductive QueryFact (F : Sig) (X : Type) : Type
  | event (M : F.lang.Term X)
  | attacker (M : F.lang.Term X)

/-- The trace satisfies the instance of the query fact under `σ`, the write-up's
Definition "Satisfaction". -/
def QueryFact.Satisfied {X : Type} (t : Trace A.Msg) (σ : X → A.Msg) : QueryFact F X → Prop
  | .event M => Act.event (M.realize σ) ∈ t
  | .attacker M => A.OutputsPublicly t (M.realize σ)

variable {A}

/-- The instance of a query fact under `σ`, as a fact of the trace semantics. -/
def QueryFact.inst {X : Type} (σ : X → A.Msg) : QueryFact F X → Fact A.Msg
  | .event M => .event (M.realize σ)
  | .attacker M => .knows (M.realize σ)

variable (A)

/-- `P₀` satisfies `F ⇝ H` against `N_pub`-adversaries, the write-up's Definition
"Correspondences between facts" for single facts: in every trace of the survey in which
`F σ` is satisfied, some `H σ'` with `F σ' = F σ` is. -/
def Model.Satisfies (P₀ : Process F G 0) {X : Type} (Fq Hq : QueryFact F X) : Prop :=
  ∀ Q, A.Adversary Q → ∀ t, A.SurveyTrace (.against P₀ Q) t → ∀ σ : X → A.Msg,
    Fq.Satisfied A t σ → ∃ σ' : X → A.Msg, Fq.inst σ' = Fq.inst σ ∧ Hq.Satisfied A t σ'

end ProVerif.Specification
