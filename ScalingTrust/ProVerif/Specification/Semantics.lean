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
  Since the semantics is modulo `E` but a process is a term, (Red I/O') and (Red Eval 1)
  substitute any term of the message received or of the value.
* **Runs** `Runs A c t`: `c` performs the weak trace `t`, `τ`-steps elided.  A run of a
  union of two multisets interleaves runs of each with communications between them
  (`Runs.split`), and conversely (`runs_add`).
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
  /-- (Red I/O'), the input receiving any term of the message -/
  | comm {U Ps} (N M Q N' P M') : Tm.msg A N = Tm.msg A N' → Tm.msg A M' = Tm.msg A M →
      Step ⟨U, .out N M Q ::ₘ .inp N' P ::ₘ Ps⟩ (some (.comm (Tm.msg A N) (Tm.msg A M)))
        ⟨U, Q ::ₘ P.inst M' ::ₘ Ps⟩
  /-- (Red Eval 1), the variable receiving any term of the value -/
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

/-- The `τ`-steps. -/
abbrev TauStar : Config F G → Config F G → Prop :=
  Relation.ReflTransGen fun c c' => Step A c none c'

/-! ### Steps of processes beside others

A step of some processes is a step of them beside any others, and a step of a union
of two multisets is a step of one side or a communication between them.  The created
names matter only to (Red Res), whose new name must be fresh for them.
-/

variable {A}

theorem add_cons' {α : Type} (a : α) (s t : Multiset α) : s + a ::ₘ t = a ::ₘ (s + t) := by
  rw [add_comm, Multiset.cons_add, add_comm]

/-- The top of a multiset is on one side of a union. -/
theorem cons_eq_add {α : Type} {a : α} {R Ps Qs : Multiset α} (h : a ::ₘ R = Ps + Qs) :
    (∃ Ps', Ps = a ::ₘ Ps' ∧ R = Ps' + Qs) ∨ ∃ Qs', Qs = a ::ₘ Qs' ∧ R = Ps + Qs' := by
  classical
  have ha : a ∈ Ps + Qs := h ▸ Multiset.mem_cons_self a R
  rcases Multiset.mem_add.1 ha with ha | ha
  · refine Or.inl ⟨Ps.erase a, (Multiset.cons_erase ha).symm, ?_⟩
    rw [← Multiset.cons_inj_right a, h, ← Multiset.cons_add, Multiset.cons_erase ha]
  · refine Or.inr ⟨Qs.erase a, (Multiset.cons_erase ha).symm, ?_⟩
    rw [← Multiset.cons_inj_right a, h, ← add_cons', Multiset.cons_erase ha]

/-- A step creates a name, or keeps the created names. -/
theorem Step.names_eq {U U' : Finset ℕ} {Ps Ps' : Multiset (Process F G 0)}
    {l : Option (Act A.Msg)} (h : Step A ⟨U, Ps⟩ l ⟨U', Ps'⟩) :
    (∃ k, l = some (.new k) ∧ k ∉ U ∧ U' = insert k U) ∨
      (∀ k, l ≠ some (.new k)) ∧ U = U' := by
  cases h
  case new P k hk => exact Or.inl ⟨k, rfl, hk, rfl⟩
  all_goals exact Or.inr ⟨fun _ => nofun, rfl⟩

/-- A step is a step from any created names its new name, if any, is fresh for. -/
theorem Step.rename {U U' : Finset ℕ} {Ps Ps' : Multiset (Process F G 0)}
    {l : Option (Act A.Msg)} (h : Step A ⟨U, Ps⟩ l ⟨U', Ps'⟩) (V : Finset ℕ)
    (hl : ∀ k, l = some (.new k) → k ∉ V) :
    (∀ k, l ≠ some (.new k)) ∧ Step A ⟨V, Ps⟩ l ⟨V, Ps'⟩ ∨
      ∃ k, l = some (.new k) ∧ Step A ⟨V, Ps⟩ l ⟨insert k V, Ps'⟩ := by
  cases h
  case new P k hk => exact Or.inr ⟨k, rfl, .new P k (hl k rfl)⟩
  all_goals exact Or.inl ⟨fun _ => nofun, by constructor <;> assumption⟩

/-- A step of some processes is a step of them beside others, whose created names its
new name, if any, is fresh for. -/
theorem Step.add {U U' U₁ : Finset ℕ} {Ps Ps' : Multiset (Process F G 0)}
    {l : Option (Act A.Msg)} (h : Step A ⟨U, Ps⟩ l ⟨U', Ps'⟩) (Qs : Multiset (Process F G 0))
    (hl : ∀ k, l = some (.new k) → k ∉ U₁) :
    Step A ⟨U ∪ U₁, Ps + Qs⟩ l ⟨U' ∪ U₁, Ps' + Qs⟩ := by
  cases h
  case new P k hk =>
    simp only [Multiset.cons_add, Finset.insert_union]
    exact .new P k fun h => (Finset.mem_union.1 h).elim hk (hl k rfl)
  all_goals (simp only [Multiset.cons_add]; constructor <;> assumption)

theorem Step.add_left {U U₀ U' : Finset ℕ} {Qs Qs' : Multiset (Process F G 0)}
    {l : Option (Act A.Msg)} (h : Step A ⟨U, Qs⟩ l ⟨U', Qs'⟩) (Ps : Multiset (Process F G 0))
    (hl : ∀ k, l = some (.new k) → k ∉ U₀) :
    Step A ⟨U₀ ∪ U, Ps + Qs⟩ l ⟨U₀ ∪ U', Ps + Qs'⟩ := by
  have := h.add Ps hl
  rwa [Finset.union_comm, Finset.union_comm U', add_comm Qs, add_comm Qs'] at this

theorem Step.out_inv {U : Finset ℕ} {Ps : Multiset (Process F G 0)} {c m : A.Msg}
    {c' : Config F G} (h : Step A ⟨U, Ps⟩ (some (.out c m)) c') :
    ∃ N M P R, Ps = .out N M P ::ₘ R ∧ Tm.msg A N = c ∧ Tm.msg A M = m ∧ c' = ⟨U, P ::ₘ R⟩ := by
  cases h
  exact ⟨_, _, _, _, rfl, rfl, rfl, rfl⟩

theorem Step.inp_inv {U : Finset ℕ} {Ps : Multiset (Process F G 0)} {c m : A.Msg}
    {c' : Config F G} (h : Step A ⟨U, Ps⟩ (some (.inp c m)) c') :
    ∃ N P M R, Ps = .inp N P ::ₘ R ∧ Tm.msg A N = c ∧ Tm.msg A M = m ∧
      c' = ⟨U, P.inst M ::ₘ R⟩ := by
  cases h
  exact ⟨_, _, _, _, rfl, rfl, rfl, rfl⟩

/-- An output and an input of the same message meet in a communication. -/
theorem Step.out_inp {U V W : Finset ℕ} {Ps Ps' Qs Qs' : Multiset (Process F G 0)} {c m : A.Msg}
    (h₀ : Step A ⟨U, Ps⟩ (some (.out c m)) ⟨U, Ps'⟩)
    (h₁ : Step A ⟨V, Qs⟩ (some (.inp c m)) ⟨V, Qs'⟩) :
    Step A ⟨W, Ps + Qs⟩ (some (.comm c m)) ⟨W, Ps' + Qs'⟩ := by
  obtain ⟨N, M, P, R, rfl, hN, hM, hP⟩ := h₀.out_inv
  obtain ⟨N', P', M', R', rfl, hN', hM', hQ⟩ := h₁.inp_inv
  obtain rfl := (Config.mk.inj hP).2
  obtain rfl := (Config.mk.inj hQ).2
  subst hN hM
  rw [Multiset.cons_add, Multiset.cons_add, add_cons', add_cons']
  exact .comm N M P N' P' M' hN'.symm hM'

/-- A step of a union of two multisets is a step of one side, or a communication
between them. -/
theorem Step.add_cases {c c' : Config F G} {l : Option (Act A.Msg)} (h : Step A c l c')
    {U : Finset ℕ} {Ps Qs : Multiset (Process F G 0)} (hc : c = ⟨U, Ps + Qs⟩) :
    (∃ U' Ps', c' = ⟨U', Ps' + Qs⟩ ∧ Step A ⟨U, Ps⟩ l ⟨U', Ps'⟩) ∨
    (∃ U' Qs', c' = ⟨U', Ps + Qs'⟩ ∧ Step A ⟨U, Qs⟩ l ⟨U', Qs'⟩) ∨
    (∃ c m Ps' Qs', l = some (.comm c m) ∧ c' = ⟨U, Ps' + Qs'⟩ ∧
      Step A ⟨U, Ps⟩ (some (.out c m)) ⟨U, Ps'⟩ ∧ Step A ⟨U, Qs⟩ (some (.inp c m)) ⟨U, Qs'⟩) ∨
    (∃ c m Ps' Qs', l = some (.comm c m) ∧ c' = ⟨U, Ps' + Qs'⟩ ∧
      Step A ⟨U, Ps⟩ (some (.inp c m)) ⟨U, Ps'⟩ ∧ Step A ⟨U, Qs⟩ (some (.out c m)) ⟨U, Qs'⟩) := by
  cases h
  case comm N M Q N' P M' hN hM =>
    obtain ⟨rfl, hR⟩ := Config.mk.inj hc
    rcases cons_eq_add hR with ⟨Ps', rfl, hR'⟩ | ⟨Qs', rfl, hR'⟩ <;>
      rcases cons_eq_add hR' with ⟨Ps'', rfl, rfl⟩ | ⟨Qs'', rfl, rfl⟩
    · exact Or.inl ⟨_, Q ::ₘ P.inst M' ::ₘ Ps'', by simp only [Multiset.cons_add],
        .comm N M Q N' P M' hN hM⟩
    · refine Or.inr (Or.inr (Or.inl ⟨Tm.msg A N, Tm.msg A M, Q ::ₘ Ps', P.inst M' ::ₘ Qs'', rfl,
        by rw [Multiset.cons_add, add_cons'], .out N M Q, ?_⟩))
      rw [hN, ← hM]
      exact .inp N' P M'
    · refine Or.inr (Or.inr (Or.inr ⟨Tm.msg A N, Tm.msg A M, P.inst M' ::ₘ Ps'', Q ::ₘ Qs', rfl,
        by rw [Multiset.cons_add, add_cons']; exact congrArg _ (Multiset.cons_swap _ _ _), ?_,
        .out N M Q⟩))
      rw [hN, ← hM]
      exact .inp N' P M'
    · exact Or.inr (Or.inl ⟨_, Q ::ₘ P.inst M' ::ₘ Qs'', by simp only [add_cons'],
        .comm N M Q N' P M' hN hM⟩)
  all_goals
    obtain ⟨rfl, hR⟩ := Config.mk.inj hc
    rcases cons_eq_add hR with ⟨Ps', rfl, rfl⟩ | ⟨Qs', rfl, rfl⟩
    · refine Or.inl ⟨?_, ?_, ?eq, ?st⟩
      case st =>
        first
          | exact .nil | exact .par _ _ | exact .bang _ | exact .new _ _ (by assumption)
          | exact .eval₁ _ _ _ _ (by assumption) | exact .eval₂ _ _ _ (by assumption)
          | exact .cond₁ _ _ _ (by assumption) | exact .cond₂ _ _ _ (by assumption)
          | exact .event _ _ | exact .out _ _ _ | exact .inp _ _ _
      case eq => first | rfl | simp only [Multiset.cons_add]
    · refine Or.inr (Or.inl ⟨?_, ?_, ?eq, ?st⟩)
      case st =>
        first
          | exact .nil | exact .par _ _ | exact .bang _ | exact .new _ _ (by assumption)
          | exact .eval₁ _ _ _ _ (by assumption) | exact .eval₂ _ _ _ (by assumption)
          | exact .cond₁ _ _ _ (by assumption) | exact .cond₂ _ _ _ (by assumption)
          | exact .event _ _ | exact .out _ _ _ | exact .inp _ _ _
      case eq => first | rfl | simp only [add_cons']

/-! ### Runs -/

theorem Runs.tauStar {c c' : Config F G} {t : Trace A.Msg} (h : TauStar A c c')
    (hr : Runs A c' t) : Runs A c t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hr
  | head hs _ ih => exact .tau hs ih

/-- A run with a first action: `τ`-steps, the action, and a run. -/
theorem Runs.cons {c : Config F G} {a : Act A.Msg} {t : Trace A.Msg} (h : Runs A c (a :: t)) :
    ∃ c₁ c₂, TauStar A c c₁ ∧ Step A c₁ (some a) c₂ ∧ Runs A c₂ t := by
  generalize ht : a :: t = t' at h
  induction h with
  | nil => cases ht
  | tau hs _ ih =>
    obtain ⟨c₁, c₂, h₁, h₂, h₃⟩ := ih ht
    exact ⟨c₁, c₂, .head hs h₁, h₂, h₃⟩
  | act hs hr =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj ht
    exact ⟨_, _, .refl, hs, hr⟩

/-- The names a run creates are distinct and fresh. -/
theorem Runs.nonces {c : Config F G} {t : Trace A.Msg} (h : Runs A c t) :
    t.nonces.Nodup ∧ ∀ k ∈ t.nonces, k ∉ c.names := by
  induction h with
  | nil => simp [Trace.nonces]
  | @tau c c' t hs _ ih =>
    obtain ⟨U, Ps⟩ := c
    obtain ⟨U', Ps'⟩ := c'
    rcases hs.names_eq with ⟨k, hk, -, -⟩ | ⟨-, rfl⟩
    · cases hk
    · exact ih
  | @act c c' a t hs _ ih =>
    obtain ⟨U, Ps⟩ := c
    obtain ⟨U', Ps'⟩ := c'
    rcases hs.names_eq with ⟨k, hk, hkU, rfl⟩ | ⟨hl, rfl⟩
    · obtain rfl := Option.some.inj hk
      simp only [Trace.nonces]
      refine ⟨List.nodup_cons.2 ⟨fun h => ih.2 k h (Finset.mem_insert_self k U), ih.1⟩, ?_⟩
      intro k' hk'
      rcases List.mem_cons.1 hk' with rfl | hk'
      · exact hkU
      · exact fun h => ih.2 k' hk' (Finset.mem_insert_of_mem h)
    · cases a <;> first | exact (hl _ rfl).elim | simpa [Trace.nonces] using ih

/-- A run from some created names is a run from fewer. -/
theorem Runs.mono {c : Config F G} {t : Trace A.Msg} (h : Runs A c t) {U : Finset ℕ}
    (hU : U ⊆ c.names) : Runs A ⟨U, c.procs⟩ t := by
  induction h generalizing U with
  | nil => exact .nil _
  | @tau c c' t hs _ ih =>
    obtain ⟨U₁, Ps₁⟩ := c
    obtain ⟨U₂, Ps₂⟩ := c'
    rcases hs.names_eq with ⟨k, hk, -, -⟩ | ⟨-, rfl⟩
    · cases hk
    · rcases hs.rename U (fun _ h => nomatch h) with ⟨-, hs'⟩ | ⟨k, hk, -⟩
      · exact .tau hs' (ih hU)
      · cases hk
  | @act c c' a t hs _ ih =>
    obtain ⟨U₁, Ps₁⟩ := c
    obtain ⟨U₂, Ps₂⟩ := c'
    rcases hs.names_eq with ⟨k, hk, hkU, rfl⟩ | ⟨hl, rfl⟩
    · obtain rfl := Option.some.inj hk
      have hk' : ∀ k', (some (Act.new k) : Option (Act A.Msg)) = some (.new k') → k' ∉ U :=
          fun k' hk' h => by
        obtain rfl := Act.new.inj (Option.some.inj hk')
        exact hkU (hU h)
      rcases hs.rename U hk' with ⟨hl, -⟩ | ⟨k', hk', hs'⟩
      · exact (hl k rfl).elim
      · obtain rfl := Act.new.inj (Option.some.inj hk')
        exact .act hs' (ih (Finset.insert_subset_insert k hU))
    · rcases hs.rename U (fun k hk => (hl k hk).elim) with ⟨-, hs'⟩ | ⟨k, hk, -⟩
      · exact .act hs' (ih hU)
      · exact (hl k hk).elim

/-- `τ`-steps of some processes are `τ`-steps of them beside others. -/
theorem TauStar.add {U U₁ : Finset ℕ} {Ps : Multiset (Process F G 0)} {c : Config F G}
    (h : TauStar A ⟨U, Ps⟩ c) (Qs : Multiset (Process F G 0)) :
    ∃ Ps', c = ⟨U, Ps'⟩ ∧ TauStar A ⟨U ∪ U₁, Ps + Qs⟩ ⟨U ∪ U₁, Ps' + Qs⟩ := by
  induction h with
  | refl => exact ⟨Ps, rfl, .refl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨Ps', rfl, ih⟩ := ih
    obtain ⟨U'', Ps''⟩ := c
    rcases hbc.names_eq with ⟨k, hk, -, -⟩ | ⟨-, rfl⟩
    · cases hk
    · exact ⟨Ps'', rfl, ih.tail (hbc.add Qs fun _ h => nomatch h)⟩

theorem TauStar.add_left {U U₀ : Finset ℕ} {Qs : Multiset (Process F G 0)} {c : Config F G}
    (h : TauStar A ⟨U, Qs⟩ c) (Ps : Multiset (Process F G 0)) :
    ∃ Qs', c = ⟨U, Qs'⟩ ∧ TauStar A ⟨U₀ ∪ U, Ps + Qs⟩ ⟨U₀ ∪ U, Ps + Qs'⟩ := by
  obtain ⟨Qs', rfl, h'⟩ := h.add (U₁ := U₀) Ps
  exact ⟨Qs', rfl, by rwa [Finset.union_comm, add_comm Qs, add_comm Qs'] at h'⟩

/-! ### Runs of a union

A run of a union of two multisets interleaves runs of each, with communications
between them, and conversely; the names created by the two must be distinct.
-/

/-- Runs of two multisets, interleaved and with communications between them, are a run
of their union. -/
theorem runs_add {s : TaggedTrace (Fin 2) A.Msg} {t : Trace A.Msg} (hc : s.Comms t) :
    ∀ {U₀ U₁ : Finset ℕ} {Ps Qs : Multiset (Process F G 0)} {t₀ t₁ : Trace A.Msg},
      Runs A ⟨U₀, Ps⟩ t₀ → Runs A ⟨U₁, Qs⟩ t₁ → s.proj 0 = t₀ → s.proj 1 = t₁ →
      t.nonces.Nodup → (∀ k ∈ t₀.nonces, k ∉ U₁) → (∀ k ∈ t₁.nonces, k ∉ U₀) →
      Runs A ⟨U₀ ∪ U₁, Ps + Qs⟩ t := by
  induction hc with
  | nil => exact fun _ _ _ _ _ _ _ => .nil _
  | @cons s t i a hc ih =>
    intro U₀ U₁ Ps Qs t₀ t₁ h₀ h₁ hs₀ hs₁ hn hd₀ hd₁
    have hn' : t.nonces.Nodup := hn.sublist (Trace.nonces_sublist (List.sublist_cons_self a t))
    have hmem : ∀ j, ∀ k ∈ (s.proj j).nonces, k ∈ t.nonces := fun j k hk => by
      rw [hc.nonces]
      exact (Trace.nonces_sublist (List.filter_sublist.map _)).subset hk
    fin_cases i
    · simp at hs₀ hs₁
      subst hs₀ hs₁
      obtain ⟨c₁, c₂, hτ, hst, hr⟩ := h₀.cons
      obtain ⟨Ps₂, rfl, hτ'⟩ := hτ.add (U₁ := U₁) Qs
      obtain ⟨U₃, Ps₃⟩ := c₂
      have hfr : ∀ k, some a = some (.new k) → k ∉ U₁ := fun k hk => by
        obtain rfl := Option.some.inj hk
        exact hd₀ k (by simp [Trace.nonces])
      refine Runs.tauStar hτ' (.act (hst.add Qs hfr) (ih hr h₁ rfl rfl hn' ?_ ?_))
      · exact fun k hk => hd₀ k ((Trace.nonces_sublist (List.sublist_cons_self a _)).subset hk)
      · rcases hst.names_eq with ⟨k₀, hk₀, -, rfl⟩ | ⟨-, rfl⟩
        · obtain rfl := Option.some.inj hk₀
          intro k hk hkU
          rcases Finset.mem_insert.1 hkU with rfl | hkU
          · simp only [Trace.nonces, List.nodup_cons] at hn
            exact hn.1 (hmem 1 k hk)
          · exact hd₁ k hk hkU
        · exact hd₁
    · simp at hs₀ hs₁
      subst hs₀ hs₁
      obtain ⟨c₁, c₂, hτ, hst, hr⟩ := h₁.cons
      obtain ⟨Qs₂, rfl, hτ'⟩ := hτ.add_left (U₀ := U₀) Ps
      obtain ⟨U₃, Qs₃⟩ := c₂
      have hfr : ∀ k, some a = some (.new k) → k ∉ U₀ := fun k hk => by
        obtain rfl := Option.some.inj hk
        exact hd₁ k (by simp [Trace.nonces])
      refine Runs.tauStar hτ' (.act (hst.add_left Ps hfr) (ih h₀ hr rfl rfl hn' ?_ ?_))
      · rcases hst.names_eq with ⟨k₀, hk₀, -, rfl⟩ | ⟨-, rfl⟩
        · obtain rfl := Option.some.inj hk₀
          intro k hk hkU
          rcases Finset.mem_insert.1 hkU with rfl | hkU
          · simp only [Trace.nonces, List.nodup_cons] at hn
            exact hn.1 (hmem 0 k hk)
          · exact hd₀ k hk hkU
        · exact hd₀
      · exact fun k hk => hd₁ k ((Trace.nonces_sublist (List.sublist_cons_self a _)).subset hk)
  | @pair s t i j hij c m hc ih =>
    intro U₀ U₁ Ps Qs t₀ t₁ h₀ h₁ hs₀ hs₁ hn hd₀ hd₁
    have hn' : t.nonces.Nodup := by simpa [Trace.nonces] using hn
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simp at hs₀ hs₁
      subst hs₀ hs₁
      obtain ⟨c₁, c₂, hτ₀, hst₀, hr₀⟩ := h₀.cons
      obtain ⟨Ps₂, rfl, hτ₀'⟩ := hτ₀.add (U₁ := U₁) Qs
      obtain ⟨U₂, Ps₃⟩ := c₂
      rcases hst₀.names_eq with ⟨k, hk, -, -⟩ | ⟨-, rfl⟩
      · cases hk
      obtain ⟨c₁', c₂', hτ₁, hst₁, hr₁⟩ := h₁.cons
      obtain ⟨Qs₂, rfl, hτ₁'⟩ := hτ₁.add_left (U₀ := U₀) Ps₂
      obtain ⟨U₃, Qs₃⟩ := c₂'
      rcases hst₁.names_eq with ⟨k, hk, -, -⟩ | ⟨-, rfl⟩
      · cases hk
      refine Runs.tauStar hτ₀' (Runs.tauStar hτ₁'
        (.act (hst₀.out_inp hst₁) (ih hr₀ hr₁ rfl rfl hn' ?_ ?_)))
      · exact fun k hk => hd₀ k ((Trace.nonces_sublist (List.sublist_cons_self _ _)).subset hk)
      · exact fun k hk => hd₁ k ((Trace.nonces_sublist (List.sublist_cons_self _ _)).subset hk)
    · simp at hs₀ hs₁
      subst hs₀ hs₁
      obtain ⟨c₁, c₂, hτ₀, hst₀, hr₀⟩ := h₀.cons
      obtain ⟨Ps₂, rfl, hτ₀'⟩ := hτ₀.add (U₁ := U₁) Qs
      obtain ⟨U₂, Ps₃⟩ := c₂
      rcases hst₀.names_eq with ⟨k, hk, -, -⟩ | ⟨-, rfl⟩
      · cases hk
      obtain ⟨c₁', c₂', hτ₁, hst₁, hr₁⟩ := h₁.cons
      obtain ⟨Qs₂, rfl, hτ₁'⟩ := hτ₁.add_left (U₀ := U₀) Ps₂
      obtain ⟨U₃, Qs₃⟩ := c₂'
      rcases hst₁.names_eq with ⟨k, hk, -, -⟩ | ⟨-, rfl⟩
      · cases hk
      have hst := hst₁.out_inp (W := U₀ ∪ U₁) hst₀
      rw [add_comm Qs₂, add_comm Qs₃] at hst
      refine Runs.tauStar hτ₀' (Runs.tauStar hτ₁' (.act hst (ih hr₀ hr₁ rfl rfl hn' ?_ ?_)))
      · exact fun k hk => hd₀ k ((Trace.nonces_sublist (List.sublist_cons_self _ _)).subset hk)
      · exact fun k hk => hd₁ k ((Trace.nonces_sublist (List.sublist_cons_self _ _)).subset hk)
    · exact absurd rfl hij

/-- A run of a union of two multisets interleaves runs of each, with communications
between them. -/
theorem Runs.split {c : Config F G} {t : Trace A.Msg} (h : Runs A c t) :
    ∀ {U : Finset ℕ} {Ps Qs : Multiset (Process F G 0)}, c = ⟨U, Ps + Qs⟩ →
      ∃ (t₀ t₁ : Trace A.Msg) (s : TaggedTrace (Fin 2) A.Msg), Runs A ⟨U, Ps⟩ t₀ ∧
        Runs A ⟨U, Qs⟩ t₁ ∧ s.proj 0 = t₀ ∧ s.proj 1 = t₁ ∧ s.Comms t := by
  induction h with
  | nil c =>
    rintro U Ps Qs rfl
    exact ⟨[], [], [], .nil _, .nil _, rfl, rfl, .nil⟩
  | tau hs _ ih =>
    rintro U Ps Qs rfl
    rcases hs.add_cases rfl with ⟨U', Ps', rfl, hs'⟩ | ⟨U', Qs', rfl, hs'⟩ |
      ⟨_, _, _, _, h, -⟩ | ⟨_, _, _, _, h, -⟩
    · rcases hs'.names_eq with ⟨k, hk, -, -⟩ | ⟨-, rfl⟩
      · cases hk
      · obtain ⟨t₀, t₁, s, r₀, r₁, hs₀, hs₁, hc⟩ := ih rfl
        exact ⟨t₀, t₁, s, .tau hs' r₀, r₁, hs₀, hs₁, hc⟩
    · rcases hs'.names_eq with ⟨k, hk, -, -⟩ | ⟨-, rfl⟩
      · cases hk
      · obtain ⟨t₀, t₁, s, r₀, r₁, hs₀, hs₁, hc⟩ := ih rfl
        exact ⟨t₀, t₁, s, r₀, .tau hs' r₁, hs₀, hs₁, hc⟩
    · cases h
    · cases h
  | act hs _ ih =>
    rintro U Ps Qs rfl
    rcases hs.add_cases rfl with ⟨U', Ps', rfl, hs'⟩ | ⟨U', Qs', rfl, hs'⟩ |
      ⟨ch, m, Ps', Qs', hl, rfl, h₀, h₁⟩ | ⟨ch, m, Ps', Qs', hl, rfl, h₀, h₁⟩
    · obtain ⟨t₀, t₁, s, r₀, r₁, hs₀, hs₁, hc⟩ := ih rfl
      have hU : U ⊆ U' := by
        rcases hs'.names_eq with ⟨k, -, -, rfl⟩ | ⟨-, rfl⟩
        · exact Finset.subset_insert k U
        · exact le_rfl
      exact ⟨_ :: t₀, t₁, (0, _) :: s, .act hs' r₀, r₁.mono hU, by simp [hs₀], by simp [hs₁],
        hc.cons 0 _⟩
    · obtain ⟨t₀, t₁, s, r₀, r₁, hs₀, hs₁, hc⟩ := ih rfl
      have hU : U ⊆ U' := by
        rcases hs'.names_eq with ⟨k, -, -, rfl⟩ | ⟨-, rfl⟩
        · exact Finset.subset_insert k U
        · exact le_rfl
      exact ⟨t₀, _ :: t₁, (1, _) :: s, r₀.mono hU, .act hs' r₁, by simp [hs₀], by simp [hs₁],
        hc.cons 1 _⟩
    · obtain rfl := Option.some.inj hl
      obtain ⟨t₀, t₁, s, r₀, r₁, hs₀, hs₁, hc⟩ := ih rfl
      exact ⟨.out ch m :: t₀, .inp ch m :: t₁, (0, .out ch m) :: (1, .inp ch m) :: s, .act h₀ r₀,
        .act h₁ r₁, by simp [hs₀], by simp [hs₁], hc.pair (by decide) ch m⟩
    · obtain rfl := Option.some.inj hl
      obtain ⟨t₀, t₁, s, r₀, r₁, hs₀, hs₁, hc⟩ := ih rfl
      exact ⟨.inp ch m :: t₀, .out ch m :: t₁, (1, .out ch m) :: (0, .inp ch m) :: s, .act h₀ r₀,
        .act h₁ r₁, by simp [hs₀], by simp [hs₁], hc.pair (by decide) ch m⟩

variable (A)

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
