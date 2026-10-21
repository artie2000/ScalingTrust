/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib.Data.Multiset.Basic
import ScalingTrust.ProVerif.Specification.Syntax
import ScalingTrust.ProVerif.TraceSemantics.Security

/-!
# The operational semantics of ProVerif's calculus

The write-up's §2.2, the semantics of the ProVerif manual (Appendix B, Figures B.1 and
B.2) for the fragment of Definition "Source syntax", read modulo `=_E`, and the write-up's
Definition "Labelled semantics" (§3.2), as two step relations: on term configurations and
on process configurations.

* **Messages.** The definitions are read on messages, `A.Msg`, terms over the constructors
  of the calculus modulo `E`: a closed term `M` denotes `Tm.msg A M`, and every `=_E` of
  the manual is an equality of messages; `true` is `StdOps.tt`.  In particular a rule's
  arguments are matched against may-fail messages: a substitution `σ` with `σ U =_E u` is a
  pair of valuations under which `U` has the value `u`, `Rule.Matching`.  The **value** of
  a may-fail term, `Val A V u`: a term has its message, a constructor applied to terms the
  application of their messages, and `fail` has `none`.
* **Term steps** `TStep A U D l U' D'`, Figure B.1: a term configuration is a finite set
  `U` of created names and a closed expression.  A constructor applied to may-fail terms
  one of which is `fail` yields `fail`, and applied to terms is a term already; a
  destructor rewrites by the first of its rules that matches, to any term of the result,
  and fails when none does, the manual's rules being complete; `new` creates a
  name; `if` and `let` act on the value of their first expression, `if fail` failing and
  `let … = fail` taking the `else` branch; `event ev(U₁, …, Uₖ)` executes the event of the
  arguments' messages, and fails when one of them is `fail`; and the context rule
  evaluates the condition of `if`, the expression of `let`, and the arguments of a
  constructor, a destructor or an event from left to right, one constructor here per
  context of the manual's `C_t`.  A step is labelled `none` for `τ`, or `new k` or
  `event m`, the manual's labels, the event `ev(M₁, …, Mₖ)` being recorded as the message
  `ev(M₁, …, Mₖ)`.
* **Configurations** are a finite set `U` of created names and a multiset of closed
  processes.  The manual's `N_pub` and `N_priv` are the public and the private nullary
  declared constructors, fixed by the model, and the created names are `ν_k` for `k ∈ U`.
* **Steps** `Step A c l c'`, Figure B.2, labelled by `Option (Act A.Msg)`: `none` is a
  `τ`-step, Nil, Par, Repl, the two rules of `if` and the two of `let`; `new` and
  `event` carry the action of the trace semantics; a communication, between an output and
  an input whose channels and message are terms, carries `comm`; and the `out` and `inp`
  steps are the offers of a process to its environment, which the manual has no rule for.
  The context rule lifts a term step of the channel of an output, of its message once the
  channel is a may-fail term, of the channel of an input, of the condition of `if`, of the
  expression of `let` and of an argument of `event`, those before it being may-fail terms,
  the manual's `C_t` for processes.  A process whose may-fail term is `fail` where a
  message is needed, as `out(fail, M)`, `if fail` or `event ev(fail)`, has no step: it
  blocks.  A trace of the manual is a run whose labels are closed.  Since the semantics is
  modulo `E` but a process is a term, a communication and `let` substitute any term of the
  message received or of the value, and the rewrite of a destructor yields any term of its
  result.
* **Runs** `Runs A c t`: `c` performs the weak trace `t`, `τ`-steps elided.  A run of a
  union of two multisets interleaves runs of each with communications between them
  (`Runs.split`), and conversely (`runs_add`).  A run of a term configuration,
  `TRuns A U D t U' D'`, is lifted through a context of expressions (`TRuns.lift`) or of
  processes (`Runs.ctx`); a run of the arguments of a `k`-ary context, `ArgRuns`, through
  the context (`ArgRuns.lift`, `Runs.argCtx`).
* **The survey's definitions** 3.1–3.5, to which the manual refers for the adversary and
  the properties of queries, and the write-up's Definitions "Deduction, knowledge",
  "Satisfaction" and "Correspondences between facts", for single query facts, over the
  manual's semantics: an adversary may use `new`, `if` and `let` inside its terms, and an
  attacker fact is satisfied when the attacker knows the term, as the manual reads it
  (§4.3.1): derives it, by the public constructors and destructors, from what was
  communicated on channels it could derive.
-/

namespace ProVerif.Specification

open FirstOrder FirstOrder.Language ProVerif.TraceSemantics

noncomputable section

variable {F G Ev : Sig}

/-- The environment of a process under `n` binders: created names are nonces. -/
abbrev env {A : Model F G Ev} {n : ℕ} (xs : Fin n → A.Msg) : ℕ ⊕ Fin n → A.Msg :=
  Sum.elim Theory.Msg.name xs

/-- A closed term's message. -/
def Tm.msg (A : Model F G Ev) (M : Tm F Ev 0) : A.Msg := M.realize (env finZeroElim)

section subst

variable {A : Model F G Ev} {n m : ℕ}

theorem realize_liftSubst (σ : Fin n → Tm F Ev m) (xs : Fin m → A.Msg) (a : A.Msg)
    (i : Fin (n + 1)) : (liftSubst σ i).realize (env (Fin.snoc xs a)) =
      Fin.snoc (α := fun _ => A.Msg) (fun j => (σ j).realize (env xs)) a i := by
  induction i using Fin.lastCases with
  | last => simp [liftSubst]
  | cast j =>
    simp only [liftSubst, Fin.snoc_castSucc, Term.realize_relabel]
    congr 1
    funext x
    cases x <;> simp

theorem Tm.realize_subst (σ : Fin n → Tm F Ev m) (M : Tm F Ev n) (xs : Fin m → A.Msg) :
    (Tm.subst σ M).realize (env xs) = M.realize (env fun i => (σ i).realize (env xs)) := by
  rw [Tm.subst, Term.realize_subst]
  congr 1
  funext x
  cases x <;> simp

end subst

variable {A : Model F G Ev} {n : ℕ}

/-! ## Destructors -/

/-- The value of a may-fail term under a valuation `θ` of the ordinary variables, into
messages, and `μ` of the may-fail variables, into may-fail messages: the write-up's `Uθ`. -/
def MayFail.eval (θ : ℕ → A.Msg) (μ : ℕ → Option A.Msg) : MayFail (Sig.cons F Ev) → Option A.Msg
  | .term M => some (M.realize θ)
  | .mvar u => μ u
  | .fail => none

theorem MayFail.eval_tt (θ : ℕ → A.Msg) (μ : ℕ → Option A.Msg) :
    MayFail.eval θ μ .tt = some StdOps.tt := by
  rw [MayFail.tt, MayFail.eval, Theory.Msg.tt_def, Term.realize_func]
  exact congrArg (fun v : Fin 0 → A.Msg =>
    some (Structure.funMap (L := (Sig.cons F Ev).lang) (Sum.inr Data.tt) v))
    (funext fun i => i.elim0)

theorem MayFail.eval_ff (θ : ℕ → A.Msg) (μ : ℕ → Option A.Msg) :
    MayFail.eval θ μ .ff = some StdOps.ff := by
  rw [MayFail.ff, MayFail.eval, Theory.Msg.ff_def, Term.realize_func]
  exact congrArg (fun v : Fin 0 → A.Msg =>
    some (Structure.funMap (L := (Sig.cons F Ev).lang) (Sum.inr Data.ff) v))
    (funext fun i => i.elim0)

/-- `θ, μ` match the arguments `us` against the rule: each argument of the rule has the
value given.  So a term accepts only a message, `fail` only `fail`, and a may-fail variable
anything. -/
def Rule.Matching (r : Rule (Sig.cons F Ev) n) (θ : ℕ → A.Msg) (μ : ℕ → Option A.Msg)
    (us : Fin n → Option A.Msg) : Prop :=
  ∀ i, (r.args i).eval θ μ = us i

/-- The rules rewrite the arguments to `v`: the first rule that matches decides, and
the result is `fail` when none does. -/
inductive Rewrites :
    List (Rule (Sig.cons F Ev) n) → (Fin n → Option A.Msg) → Option A.Msg → Prop
  | nil (us) : Rewrites [] us none
  | head {r rs us θ μ} : r.Matching θ μ us → Rewrites (r :: rs) us (r.rhs.eval θ μ)
  | tail {r rs us v} : (¬ ∃ θ μ, r.Matching θ μ us) → Rewrites rs us v → Rewrites (r :: rs) us v

variable (A)

/-! ## Values and term steps -/

/-- The value of a may-fail term: a term has its message, a constructor applied to terms
the application of their messages, and `fail` has `none`. -/
inductive Val : Expr F G Ev 0 → Option A.Msg → Prop
  | term (M : Tm F Ev 0) : Val (.term M) (some (Tm.msg A M))
  | ctor {k : ℕ} (f : Sig.cons F Ev k) {args : Fin k → Expr F G Ev 0} {ms : Fin k → A.Msg} :
      (∀ i, Val (args i) (some (ms i))) → Val (.ctor f args) (some (Theory.Msg.app f ms))
  | fail : Val .fail none

variable {A}

theorem Val.isTerm {V : Expr F G Ev 0} {u : Option A.Msg} (h : Val A V u) :
    ∀ m, u = some m → V.IsTerm := by
  induction h with
  | term M => exact fun _ _ => .term M
  | ctor f _ ih => exact fun _ _ => .ctor f fun i => ih i _ rfl
  | fail => exact fun _ h => nomatch h

theorem Val.isValue {V : Expr F G Ev 0} {u : Option A.Msg} (h : Val A V u) : V.IsValue := by
  cases h with
  | term M => exact Or.inl (.term M)
  | ctor f hargs => exact Or.inl (.ctor f fun i => (hargs i).isTerm _ rfl)
  | fail => exact Or.inr rfl

theorem Expr.IsTerm.val {V : Expr F G Ev 0} (h : V.IsTerm) : ∃ m, Val A V (some m) := by
  induction h with
  | term M => exact ⟨_, .term M⟩
  | ctor f _ ih => exact ⟨_, .ctor f fun i => (ih i).choose_spec⟩

theorem Expr.IsValue.val {V : Expr F G Ev 0} (h : V.IsValue) : ∃ u, Val A V u := by
  rcases h with h | rfl
  · obtain ⟨m, hm⟩ := h.val (A := A)
    exact ⟨_, hm⟩
  · exact ⟨_, .fail⟩

theorem Val.eq {V : Expr F G Ev 0} {u u' : Option A.Msg} (h : Val A V u) (h' : Val A V u') :
    u = u' := by
  induction h generalizing u' with
  | term M => cases h'; rfl
  | ctor f _ ih =>
    cases h' with
    | ctor _ hargs' =>
      exact congrArg (fun ms => some (Theory.Msg.app _ ms))
        (funext fun i => Option.some.inj (ih i (hargs' i)))
  | fail => cases h'; rfl

/-- Only `fail` has the value `fail`. -/
theorem Val.eq_fail {V : Expr F G Ev 0} {u : Option A.Msg} (h : Val A V u) (hu : u = none) :
    V = .fail := by
  subst hu
  cases h
  rfl

variable (A)

/-- The steps of term configurations, the manual's Figure B.1: `none` is a `τ`-step, and
the labels are `new k` and `event m`.  Lean makes the created names `U` a parameter,
since every rule reads them from the same variable, so an `@` pattern on a constructor
omits them. -/
inductive TStep :
    Finset ℕ → Expr F G Ev 0 → Option (Act A.Msg) → Finset ℕ → Expr F G Ev 0 → Prop
  /-- A constructor applied to may-fail terms one of which is `fail` yields `fail`. -/
  | ctor_fail {U : Finset ℕ} {k : ℕ} (f : Sig.cons F Ev k) {args : Fin k → Expr F G Ev 0}
      (i : Fin k) : (∀ j, (args j).IsValue) → args i = .fail →
      TStep U (.ctor f args) none U .fail
  /-- A destructor applied to may-fail terms rewrites by the first of its rules that
  matches, to any term of the result. -/
  | dtor {U : Finset ℕ} {k : ℕ} (g : Sig.withBuiltin G k) {args : Fin k → Expr F G Ev 0}
      {us : Fin k → Option A.Msg} (M : Tm F Ev 0) : (∀ i, Val A (args i) (us i)) →
      Rewrites (A.rules g) us (some (Tm.msg A M)) → TStep U (.dtor g args) none U (.term M)
  /-- A destructor applied to may-fail terms fails when no rule matches. -/
  | dtor_fail {U : Finset ℕ} {k : ℕ} (g : Sig.withBuiltin G k) {args : Fin k → Expr F G Ev 0}
      {us : Fin k → Option A.Msg} : (∀ i, Val A (args i) (us i)) →
      Rewrites (A.rules g) us none → TStep U (.dtor g args) none U .fail
  /-- `new a; D` creates the name `ν_k` for a fresh `k`. -/
  | new {U : Finset ℕ} (D : Expr F G Ev 1) (k : ℕ) : k ∉ U →
      TStep U (.new D) (some (.new k)) (insert k U) (D.inst (.var (.inl k)))
  | ite₁ {U : Finset ℕ} {C : Expr F G Ev 0} (D₁ D₂ : Expr F G Ev 0) :
      Val A C (some StdOps.tt) → TStep U (.ite C D₁ D₂) none U D₁
  | ite₂ {U : Finset ℕ} {C : Expr F G Ev 0} {m : A.Msg} (D₁ D₂ : Expr F G Ev 0) :
      Val A C (some m) → m ≠ StdOps.tt → TStep U (.ite C D₁ D₂) none U D₂
  | ite_fail {U : Finset ℕ} (D₁ D₂ : Expr F G Ev 0) : TStep U (.ite .fail D₁ D₂) none U .fail
  /-- The variable receives any term of the value. -/
  | let₁ {U : Finset ℕ} {D : Expr F G Ev 0} {m : A.Msg} (M' : Tm F Ev 0) (D₁ : Expr F G Ev 1)
      (D₂ : Expr F G Ev 0) : Val A D (some m) → Tm.msg A M' = m →
      TStep U (.let_ D D₁ D₂) none U (D₁.inst M')
  | let₂ {U : Finset ℕ} (D₁ : Expr F G Ev 1) (D₂ : Expr F G Ev 0) :
      TStep U (.let_ .fail D₁ D₂) none U D₂
  /-- `event ev(M₁, …, Mₖ); D` executes the event `ev(M₁, …, Mₖ)`. -/
  | event {U : Finset ℕ} {k : ℕ} (e : Ev k) {args : Fin k → Expr F G Ev 0} {ms : Fin k → A.Msg}
      (D : Expr F G Ev 0) : (∀ i, Val A (args i) (some (ms i))) →
      TStep U (.event e args D) (some (.event (Theory.Msg.app (.inl (.inr e)) ms))) U D
  /-- An event one of whose arguments is `fail` fails. -/
  | event_fail {U : Finset ℕ} {k : ℕ} (e : Ev k) {args : Fin k → Expr F G Ev 0} (i : Fin k)
      (D : Expr F G Ev 0) : (∀ j, (args j).IsValue) → args i = .fail →
      TStep U (.event e args D) none U .fail
  /-- The context `f(U₁, …, Uᵢ₋₁, _, Dᵢ₊₁, …, Dₖ)`: the arguments are evaluated from left
  to right. -/
  | ctor_ctx {U U' : Finset ℕ} {l : Option (Act A.Msg)} {k : ℕ} (f : Sig.cons F Ev k)
      {args : Fin k → Expr F G Ev 0} (i : Fin k) {D' : Expr F G Ev 0} :
      (∀ j, j < i → (args j).IsValue) → TStep U (args i) l U' D' →
      TStep U (.ctor f args) l U' (.ctor f (Function.update args i D'))
  /-- The context `g(U₁, …, Uᵢ₋₁, _, Dᵢ₊₁, …, Dₖ)`. -/
  | dtor_ctx {U U' : Finset ℕ} {l : Option (Act A.Msg)} {k : ℕ} (g : Sig.withBuiltin G k)
      {args : Fin k → Expr F G Ev 0} (i : Fin k) {D' : Expr F G Ev 0} :
      (∀ j, j < i → (args j).IsValue) → TStep U (args i) l U' D' →
      TStep U (.dtor g args) l U' (.dtor g (Function.update args i D'))
  /-- The context `if _ then D₁ else D₂`. -/
  | ite_ctx {U U' : Finset ℕ} {l : Option (Act A.Msg)} {C C' : Expr F G Ev 0}
      (D₁ D₂ : Expr F G Ev 0) : TStep U C l U' C' → TStep U (.ite C D₁ D₂) l U' (.ite C' D₁ D₂)
  /-- The context `let x = _ in D₁ else D₂`. -/
  | let_ctx {U U' : Finset ℕ} {l : Option (Act A.Msg)} {D D' : Expr F G Ev 0}
      (D₁ : Expr F G Ev 1) (D₂ : Expr F G Ev 0) :
      TStep U D l U' D' → TStep U (.let_ D D₁ D₂) l U' (.let_ D' D₁ D₂)
  /-- The context `event ev(U₁, …, Uᵢ₋₁, _, Dᵢ₊₁, …, Dₖ); D`. -/
  | event_ctx {U U' : Finset ℕ} {l : Option (Act A.Msg)} {k : ℕ} (e : Ev k)
      {args : Fin k → Expr F G Ev 0} (i : Fin k) {D' : Expr F G Ev 0} (D : Expr F G Ev 0) :
      (∀ j, j < i → (args j).IsValue) → TStep U (args i) l U' D' →
      TStep U (.event e args D) l U' (.event e (Function.update args i D') D)

variable {A}

/-- A term step is a `τ`-step, creates a name, or executes an event. -/
theorem TStep.label {U U' : Finset ℕ} {D D' : Expr F G Ev 0} {l : Option (Act A.Msg)}
    (h : TStep A U D l U' D') :
    l = none ∨ (∃ k, l = some (.new k)) ∨ ∃ m, l = some (.event m) := by
  induction h <;> first
    | exact Or.inl rfl | exact Or.inr (Or.inl ⟨_, rfl⟩) | exact Or.inr (Or.inr ⟨_, rfl⟩)
    | assumption

/-- A may-fail term has no step. -/
theorem TStep.not_value {U U' : Finset ℕ} {D D' : Expr F G Ev 0} {l : Option (Act A.Msg)}
    (h : TStep A U D l U' D') : ¬ D.IsValue := by
  induction h
  case ctor_fail f args i hv hi =>
    rintro (h | h)
    · have h' := h.arg i
      rw [hi] at h'
      exact nomatch h'
    · exact nomatch h
  case ctor_ctx f args i D' hv _ ih =>
    rintro (h | h)
    · exact ih (Or.inl (h.arg i))
    · exact nomatch h
  all_goals
    rintro (h | h)
    · exact nomatch h
    · exact nomatch h

/-- A term step creates a name, or keeps the created names. -/
theorem TStep.names_eq {U U' : Finset ℕ} {D D' : Expr F G Ev 0} {l : Option (Act A.Msg)}
    (h : TStep A U D l U' D') :
    (∃ k, l = some (.new k) ∧ k ∉ U ∧ U' = insert k U) ∨
      (∀ k, l ≠ some (.new k)) ∧ U = U' := by
  induction h <;> first
    | exact Or.inr ⟨fun _ => nofun, rfl⟩ | exact Or.inl ⟨_, rfl, ‹_›, rfl⟩ | assumption

/-- A term step is a step from any created names its new name, if any, is fresh for. -/
theorem TStep.rename {U U' : Finset ℕ} {D D' : Expr F G Ev 0} {l : Option (Act A.Msg)}
    (h : TStep A U D l U' D') (V : Finset ℕ) (hl : ∀ k, l = some (.new k) → k ∉ V) :
    (∀ k, l ≠ some (.new k)) ∧ TStep A V D l V D' ∨
      ∃ k, l = some (.new k) ∧ TStep A V D l (insert k V) D' := by
  induction h generalizing V
  case new D k hk => exact Or.inr ⟨k, rfl, .new D k (hl k rfl)⟩
  case ctor_ctx f args i D' hv _ ih =>
    rcases ih V hl with ⟨hl', hs⟩ | ⟨k, hk, hs⟩
    · exact Or.inl ⟨hl', .ctor_ctx f i hv hs⟩
    · exact Or.inr ⟨k, hk, .ctor_ctx f i hv hs⟩
  case dtor_ctx g args i D' hv _ ih =>
    rcases ih V hl with ⟨hl', hs⟩ | ⟨k, hk, hs⟩
    · exact Or.inl ⟨hl', .dtor_ctx g i hv hs⟩
    · exact Or.inr ⟨k, hk, .dtor_ctx g i hv hs⟩
  case ite_ctx D₁ D₂ _ ih =>
    rcases ih V hl with ⟨hl', hs⟩ | ⟨k, hk, hs⟩
    · exact Or.inl ⟨hl', .ite_ctx D₁ D₂ hs⟩
    · exact Or.inr ⟨k, hk, .ite_ctx D₁ D₂ hs⟩
  case let_ctx D₁ D₂ _ ih =>
    rcases ih V hl with ⟨hl', hs⟩ | ⟨k, hk, hs⟩
    · exact Or.inl ⟨hl', .let_ctx D₁ D₂ hs⟩
    · exact Or.inr ⟨k, hk, .let_ctx D₁ D₂ hs⟩
  case event_ctx e args i D' D hv _ ih =>
    rcases ih V hl with ⟨hl', hs⟩ | ⟨k, hk, hs⟩
    · exact Or.inl ⟨hl', .event_ctx e i D hv hs⟩
    · exact Or.inr ⟨k, hk, .event_ctx e i D hv hs⟩
  all_goals exact Or.inl ⟨fun _ => nofun, by constructor <;> assumption⟩

/-- A term step is a term step from more created names, which its new name, if any, is
fresh for. -/
theorem TStep.add {U U' : Finset ℕ} {D D' : Expr F G Ev 0} {l : Option (Act A.Msg)}
    (h : TStep A U D l U' D') (V : Finset ℕ) (hl : ∀ k, l = some (.new k) → k ∉ V) :
    TStep A (U ∪ V) D l (U' ∪ V) D' := by
  induction h generalizing V
  case new D k hk =>
    rw [Finset.insert_union]
    exact .new D k fun h => (Finset.mem_union.1 h).elim hk (hl k rfl)
  case ctor_ctx f args i D' hv _ ih => exact .ctor_ctx f i hv (ih V hl)
  case dtor_ctx g args i D' hv _ ih => exact .dtor_ctx g i hv (ih V hl)
  case ite_ctx D₁ D₂ _ ih => exact .ite_ctx D₁ D₂ (ih V hl)
  case let_ctx D₁ D₂ _ ih => exact .let_ctx D₁ D₂ (ih V hl)
  case event_ctx e args i D' D hv _ ih => exact .event_ctx e i D hv (ih V hl)
  all_goals (constructor <;> assumption)

/-! ## Reduction -/

/-- A configuration: the created names and the running processes. -/
structure Config (F G Ev : Sig) where
  /-- The indices of the names created so far. -/
  names : Finset ℕ
  /-- The processes, a multiset. -/
  procs : Multiset (Process F G Ev 0)

variable (A)

/-- The labelled steps of configurations, the manual's Figure B.2, `none` being `τ`. -/
inductive Step : Config F G Ev → Option (Act A.Msg) → Config F G Ev → Prop
  /-- `0` -/
  | nil {U Ps} : Step ⟨U, .nil ::ₘ Ps⟩ none ⟨U, Ps⟩
  /-- `P | Q` -/
  | par {U Ps} (P Q) : Step ⟨U, .par P Q ::ₘ Ps⟩ none ⟨U, P ::ₘ Q ::ₘ Ps⟩
  /-- `!P` -/
  | bang {U Ps} (P) : Step ⟨U, .bang P ::ₘ Ps⟩ none ⟨U, P ::ₘ .bang P ::ₘ Ps⟩
  /-- `new a; P`: the created name is `ν_k` for a fresh `k`. -/
  | new {U Ps} (P) (k : ℕ) : k ∉ U →
      Step ⟨U, .new P ::ₘ Ps⟩ (some (.new k)) ⟨insert k U, P.inst (.var (.inl k)) ::ₘ Ps⟩
  /-- A communication, the input receiving any term of the message. -/
  | comm {U Ps} {N M : Expr F G Ev 0} (Q) {N' : Expr F G Ev 0} (P) (M' : Tm F Ev 0) {c m : A.Msg} :
      Val A N (some c) → Val A M (some m) → Val A N' (some c) → Tm.msg A M' = m →
      Step ⟨U, .out N M Q ::ₘ .inp N' P ::ₘ Ps⟩ (some (.comm c m)) ⟨U, Q ::ₘ P.inst M' ::ₘ Ps⟩
  /-- `let x = M in P else Q`, the variable receiving any term of the value -/
  | eval₁ {U Ps} {D : Expr F G Ev 0} {m : A.Msg} (M' : Tm F Ev 0) (P Q) :
      Val A D (some m) → Tm.msg A M' = m →
      Step ⟨U, .let_ D P Q ::ₘ Ps⟩ none ⟨U, P.inst M' ::ₘ Ps⟩
  /-- `let x = fail in P else Q` -/
  | eval₂ {U Ps} (P Q) : Step ⟨U, .let_ .fail P Q ::ₘ Ps⟩ none ⟨U, Q ::ₘ Ps⟩
  /-- `if M then P else Q` with `M =_E true` -/
  | cond₁ {U Ps} {C : Expr F G Ev 0} (P Q) : Val A C (some StdOps.tt) →
      Step ⟨U, .ite C P Q ::ₘ Ps⟩ none ⟨U, P ::ₘ Ps⟩
  /-- `if M then P else Q` with `M ≠_E true` -/
  | cond₂ {U Ps} {C : Expr F G Ev 0} {m : A.Msg} (P Q) : Val A C (some m) → m ≠ StdOps.tt →
      Step ⟨U, .ite C P Q ::ₘ Ps⟩ none ⟨U, Q ::ₘ Ps⟩
  /-- `event ev(M₁, …, Mₖ); P` -/
  | event {U Ps} {k : ℕ} (e : Ev k) {args : Fin k → Expr F G Ev 0} {ms : Fin k → A.Msg} (P) :
      (∀ i, Val A (args i) (some (ms i))) →
      Step ⟨U, .event e args P ::ₘ Ps⟩ (some (.event (Theory.Msg.app (.inl (.inr e)) ms)))
        ⟨U, P ::ₘ Ps⟩
  /-- An offer to send. -/
  | out {U Ps} {N M : Expr F G Ev 0} (P) {c m : A.Msg} : Val A N (some c) → Val A M (some m) →
      Step ⟨U, .out N M P ::ₘ Ps⟩ (some (.out c m)) ⟨U, P ::ₘ Ps⟩
  /-- An offer to receive any closed term. -/
  | inp {U Ps} {N : Expr F G Ev 0} (P) (M : Tm F Ev 0) {c : A.Msg} : Val A N (some c) →
      Step ⟨U, .inp N P ::ₘ Ps⟩ (some (.inp c (Tm.msg A M))) ⟨U, P.inst M ::ₘ Ps⟩
  /-- The context `out(_, M); P`. -/
  | out_ctx₁ {U U' Ps l} {N N'} (M P) : TStep A U N l U' N' →
      Step ⟨U, .out N M P ::ₘ Ps⟩ l ⟨U', .out N' M P ::ₘ Ps⟩
  /-- The context `out(U, _); P`. -/
  | out_ctx₂ {U U' Ps l} (N) {M M'} (P) : N.IsValue → TStep A U M l U' M' →
      Step ⟨U, .out N M P ::ₘ Ps⟩ l ⟨U', .out N M' P ::ₘ Ps⟩
  /-- The context `in(_, x); P`. -/
  | inp_ctx {U U' Ps l} {N N'} (P) : TStep A U N l U' N' →
      Step ⟨U, .inp N P ::ₘ Ps⟩ l ⟨U', .inp N' P ::ₘ Ps⟩
  /-- The context `if _ then P else Q`. -/
  | ite_ctx {U U' Ps l} {C C'} (P Q) : TStep A U C l U' C' →
      Step ⟨U, .ite C P Q ::ₘ Ps⟩ l ⟨U', .ite C' P Q ::ₘ Ps⟩
  /-- The context `let x = _ in P else Q`. -/
  | let_ctx {U U' Ps l} {D D'} (P Q) : TStep A U D l U' D' →
      Step ⟨U, .let_ D P Q ::ₘ Ps⟩ l ⟨U', .let_ D' P Q ::ₘ Ps⟩
  /-- The context `event ev(U₁, …, Uᵢ₋₁, _, Dᵢ₊₁, …, Dₖ); P`. -/
  | event_ctx {U U' Ps l} {k : ℕ} (e : Ev k) {args : Fin k → Expr F G Ev 0} (i : Fin k)
      {D' : Expr F G Ev 0} (P) : (∀ j, j < i → (args j).IsValue) → TStep A U (args i) l U' D' →
      Step ⟨U, .event e args P ::ₘ Ps⟩ l ⟨U', .event e (Function.update args i D') P ::ₘ Ps⟩

/-- `c` performs the weak trace `t`: its visible labels in order, `τ`-steps elided. -/
inductive Runs : Config F G Ev → Trace A.Msg → Prop
  | nil (c) : Runs c []
  | tau {c c' t} : Step A c none c' → Runs c' t → Runs c t
  | act {c c' a t} : Step A c (some a) c' → Runs c' t → Runs c (a :: t)

/-- The weak traces of a configuration. -/
def Config.traces (c : Config F G Ev) : Proc A.Msg := {t | Runs A c t}

/-- The `τ`-steps. -/
abbrev TauStar : Config F G Ev → Config F G Ev → Prop :=
  Relation.ReflTransGen fun c c' => Step A c none c'

/-- The term configuration performs the weak trace `t` and reaches the other, `τ`-steps
elided. -/
inductive TRuns : Finset ℕ → Expr F G Ev 0 → Trace A.Msg → Finset ℕ → Expr F G Ev 0 → Prop
  | nil (U D) : TRuns U D [] U D
  | tau {U D U' D' t U'' D''} : TStep A U D none U' D' → TRuns U' D' t U'' D'' →
      TRuns U D t U'' D''
  | act {U D U' D' a t U'' D''} : TStep A U D (some a) U' D' → TRuns U' D' t U'' D'' →
      TRuns U D (a :: t) U'' D''

/-- The arguments of a `k`-ary context perform the weak trace `t` and reach the others,
`τ`-steps elided: one argument steps at a time, those before it being may-fail terms. -/
inductive ArgRuns {k : ℕ} :
    Finset ℕ → (Fin k → Expr F G Ev 0) → Trace A.Msg → Finset ℕ → (Fin k → Expr F G Ev 0) → Prop
  | nil (U args) : ArgRuns U args [] U args
  | tau {U args} (i : Fin k) {U' D' t U'' args''} : (∀ j, j < i → (args j).IsValue) →
      TStep A U (args i) none U' D' → ArgRuns U' (Function.update args i D') t U'' args'' →
      ArgRuns U args t U'' args''
  | act {U args} (i : Fin k) {U' D' a t U'' args''} : (∀ j, j < i → (args j).IsValue) →
      TStep A U (args i) (some a) U' D' → ArgRuns U' (Function.update args i D') t U'' args'' →
      ArgRuns U args (a :: t) U'' args''

/-! ### Steps of processes beside others

A step of some processes is a step of them beside any others, and a step of a union
of two multisets is a step of one side or a communication between them.  The created
names matter only to the creation of a name, which must be fresh for them.
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
theorem Step.names_eq {U U' : Finset ℕ} {Ps Ps' : Multiset (Process F G Ev 0)}
    {l : Option (Act A.Msg)} (h : Step A ⟨U, Ps⟩ l ⟨U', Ps'⟩) :
    (∃ k, l = some (.new k) ∧ k ∉ U ∧ U' = insert k U) ∨
      (∀ k, l ≠ some (.new k)) ∧ U = U' := by
  cases h
  case new P k hk => exact Or.inl ⟨k, rfl, hk, rfl⟩
  all_goals first | exact Or.inr ⟨fun _ => nofun, rfl⟩ | exact TStep.names_eq ‹_›

/-- A step is a step from any created names its new name, if any, is fresh for. -/
theorem Step.rename {U U' : Finset ℕ} {Ps Ps' : Multiset (Process F G Ev 0)}
    {l : Option (Act A.Msg)} (h : Step A ⟨U, Ps⟩ l ⟨U', Ps'⟩) (V : Finset ℕ)
    (hl : ∀ k, l = some (.new k) → k ∉ V) :
    (∀ k, l ≠ some (.new k)) ∧ Step A ⟨V, Ps⟩ l ⟨V, Ps'⟩ ∨
      ∃ k, l = some (.new k) ∧ Step A ⟨V, Ps⟩ l ⟨insert k V, Ps'⟩ := by
  cases h
  case new P k hk => exact Or.inr ⟨k, rfl, .new P k (hl k rfl)⟩
  case out_ctx₁ hs =>
    rcases hs.rename V hl with ⟨hl', hs'⟩ | ⟨k, hk, hs'⟩
    · exact Or.inl ⟨hl', .out_ctx₁ _ _ hs'⟩
    · exact Or.inr ⟨k, hk, .out_ctx₁ _ _ hs'⟩
  case out_ctx₂ hN hs =>
    rcases hs.rename V hl with ⟨hl', hs'⟩ | ⟨k, hk, hs'⟩
    · exact Or.inl ⟨hl', .out_ctx₂ _ _ hN hs'⟩
    · exact Or.inr ⟨k, hk, .out_ctx₂ _ _ hN hs'⟩
  case inp_ctx hs =>
    rcases hs.rename V hl with ⟨hl', hs'⟩ | ⟨k, hk, hs'⟩
    · exact Or.inl ⟨hl', .inp_ctx _ hs'⟩
    · exact Or.inr ⟨k, hk, .inp_ctx _ hs'⟩
  case ite_ctx hs =>
    rcases hs.rename V hl with ⟨hl', hs'⟩ | ⟨k, hk, hs'⟩
    · exact Or.inl ⟨hl', .ite_ctx _ _ hs'⟩
    · exact Or.inr ⟨k, hk, .ite_ctx _ _ hs'⟩
  case let_ctx hs =>
    rcases hs.rename V hl with ⟨hl', hs'⟩ | ⟨k, hk, hs'⟩
    · exact Or.inl ⟨hl', .let_ctx _ _ hs'⟩
    · exact Or.inr ⟨k, hk, .let_ctx _ _ hs'⟩
  case event_ctx hv hs =>
    rcases hs.rename V hl with ⟨hl', hs'⟩ | ⟨k, hk, hs'⟩
    · exact Or.inl ⟨hl', .event_ctx _ _ _ hv hs'⟩
    · exact Or.inr ⟨k, hk, .event_ctx _ _ _ hv hs'⟩
  all_goals exact Or.inl ⟨fun _ => nofun, by constructor <;> assumption⟩

/-- A step of some processes is a step of them beside others, whose created names its
new name, if any, is fresh for. -/
theorem Step.add {U U' U₁ : Finset ℕ} {Ps Ps' : Multiset (Process F G Ev 0)}
    {l : Option (Act A.Msg)} (h : Step A ⟨U, Ps⟩ l ⟨U', Ps'⟩) (Qs : Multiset (Process F G Ev 0))
    (hl : ∀ k, l = some (.new k) → k ∉ U₁) :
    Step A ⟨U ∪ U₁, Ps + Qs⟩ l ⟨U' ∪ U₁, Ps' + Qs⟩ := by
  cases h
  case new P k hk =>
    simp only [Multiset.cons_add, Finset.insert_union]
    exact .new P k fun h => (Finset.mem_union.1 h).elim hk (hl k rfl)
  all_goals
    simp only [Multiset.cons_add]
    first
      | exact .out_ctx₁ _ _ (TStep.add ‹_› U₁ hl) | exact .out_ctx₂ _ _ ‹_› (TStep.add ‹_› U₁ hl)
      | exact .inp_ctx _ (TStep.add ‹_› U₁ hl) | exact .ite_ctx _ _ (TStep.add ‹_› U₁ hl)
      | exact .let_ctx _ _ (TStep.add ‹_› U₁ hl)
      | exact .event_ctx _ _ _ ‹_› (TStep.add ‹_› U₁ hl)
      | (constructor <;> assumption)

theorem Step.add_left {U U₀ U' : Finset ℕ} {Qs Qs' : Multiset (Process F G Ev 0)}
    {l : Option (Act A.Msg)} (h : Step A ⟨U, Qs⟩ l ⟨U', Qs'⟩) (Ps : Multiset (Process F G Ev 0))
    (hl : ∀ k, l = some (.new k) → k ∉ U₀) :
    Step A ⟨U₀ ∪ U, Ps + Qs⟩ l ⟨U₀ ∪ U', Ps + Qs'⟩ := by
  have := h.add Ps hl
  rwa [Finset.union_comm, Finset.union_comm U', add_comm Qs, add_comm Qs'] at this

theorem Step.out_inv {U : Finset ℕ} {Ps : Multiset (Process F G Ev 0)} {c m : A.Msg}
    {c' : Config F G Ev} (h : Step A ⟨U, Ps⟩ (some (.out c m)) c') :
    ∃ N M P R, Ps = .out N M P ::ₘ R ∧ Val A N (some c) ∧ Val A M (some m) ∧
      c' = ⟨U, P ::ₘ R⟩ := by
  cases h
  case out => exact ⟨_, _, _, _, rfl, ‹_›, ‹_›, rfl⟩
  all_goals rcases TStep.label ‹_› with h | ⟨_, h⟩ | ⟨_, h⟩ <;> cases h

theorem Step.inp_inv {U : Finset ℕ} {Ps : Multiset (Process F G Ev 0)} {c m : A.Msg}
    {c' : Config F G Ev} (h : Step A ⟨U, Ps⟩ (some (.inp c m)) c') :
    ∃ N P M R, Ps = .inp N P ::ₘ R ∧ Val A N (some c) ∧ Tm.msg A M = m ∧
      c' = ⟨U, P.inst M ::ₘ R⟩ := by
  cases h
  case inp => exact ⟨_, _, _, _, rfl, ‹_›, rfl, rfl⟩
  all_goals rcases TStep.label ‹_› with h | ⟨_, h⟩ | ⟨_, h⟩ <;> cases h

/-- An output and an input of the same message meet in a communication. -/
theorem Step.out_inp {U V W : Finset ℕ} {Ps Ps' Qs Qs' : Multiset (Process F G Ev 0)}
    {c m : A.Msg} (h₀ : Step A ⟨U, Ps⟩ (some (.out c m)) ⟨U, Ps'⟩)
    (h₁ : Step A ⟨V, Qs⟩ (some (.inp c m)) ⟨V, Qs'⟩) :
    Step A ⟨W, Ps + Qs⟩ (some (.comm c m)) ⟨W, Ps' + Qs'⟩ := by
  obtain ⟨N, M, P, R, rfl, hN, hM, hP⟩ := h₀.out_inv
  obtain ⟨N', P', M', R', rfl, hN', hM', hQ⟩ := h₁.inp_inv
  obtain rfl := (Config.mk.inj hP).2
  obtain rfl := (Config.mk.inj hQ).2
  rw [Multiset.cons_add, Multiset.cons_add, add_cons', add_cons']
  exact .comm P P' M' hN hM hN' hM'

/-- A step of a union of two multisets is a step of one side, or a communication
between them. -/
theorem Step.add_cases {c c' : Config F G Ev} {l : Option (Act A.Msg)} (h : Step A c l c')
    {U : Finset ℕ} {Ps Qs : Multiset (Process F G Ev 0)} (hc : c = ⟨U, Ps + Qs⟩) :
    (∃ U' Ps', Step A ⟨U, Ps⟩ l ⟨U', Ps'⟩ ∧ c' = ⟨U', Ps' + Qs⟩) ∨
    (∃ U' Qs', Step A ⟨U, Qs⟩ l ⟨U', Qs'⟩ ∧ c' = ⟨U', Ps + Qs'⟩) ∨
    (∃ c m Ps' Qs', l = some (.comm c m) ∧ c' = ⟨U, Ps' + Qs'⟩ ∧
      Step A ⟨U, Ps⟩ (some (.out c m)) ⟨U, Ps'⟩ ∧ Step A ⟨U, Qs⟩ (some (.inp c m)) ⟨U, Qs'⟩) ∨
    (∃ c m Ps' Qs', l = some (.comm c m) ∧ c' = ⟨U, Ps' + Qs'⟩ ∧
      Step A ⟨U, Ps⟩ (some (.inp c m)) ⟨U, Ps'⟩ ∧ Step A ⟨U, Qs⟩ (some (.out c m)) ⟨U, Qs'⟩) := by
  cases h
  case comm N M Q N' P M' ch m hN hM hN' hM' =>
    obtain ⟨rfl, hR⟩ := Config.mk.inj hc
    subst hM'
    rcases cons_eq_add hR with ⟨Ps', rfl, hR'⟩ | ⟨Qs', rfl, hR'⟩ <;>
      rcases cons_eq_add hR' with ⟨Ps'', rfl, rfl⟩ | ⟨Qs'', rfl, rfl⟩
    · exact Or.inl ⟨_, Q ::ₘ P.inst M' ::ₘ Ps'', .comm Q P M' hN hM hN' rfl,
        by simp only [Multiset.cons_add]⟩
    · exact Or.inr (Or.inr (Or.inl ⟨ch, Tm.msg A M', Q ::ₘ Ps', P.inst M' ::ₘ Qs'', rfl,
        by rw [Multiset.cons_add, add_cons'], .out Q hN hM, .inp P M' hN'⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ch, Tm.msg A M', P.inst M' ::ₘ Ps'', Q ::ₘ Qs', rfl,
        by rw [Multiset.cons_add, add_cons']; exact congrArg _ (Multiset.cons_swap _ _ _),
        .inp P M' hN', .out Q hN hM⟩))
    · exact Or.inr (Or.inl ⟨_, Q ::ₘ P.inst M' ::ₘ Qs'', .comm Q P M' hN hM hN' rfl,
        by simp only [add_cons']⟩)
  all_goals
    obtain ⟨rfl, hR⟩ := Config.mk.inj hc
    rcases cons_eq_add hR with ⟨Ps', rfl, rfl⟩ | ⟨Qs', rfl, rfl⟩
    · exact Or.inl ⟨_, _, by
        first
          | exact .out_ctx₁ _ _ ‹_› | exact .out_ctx₂ _ _ ‹_› ‹_› | exact .inp_ctx _ ‹_›
          | exact .ite_ctx _ _ ‹_› | exact .let_ctx _ _ ‹_› | exact .event_ctx _ _ _ ‹_› ‹_›
          | exact .eval₂ _ _ | exact .cond₂ _ _ ‹_› ‹_› | (constructor <;> assumption),
        by first | rfl | simp only [Multiset.cons_add]⟩
    · exact Or.inr (Or.inl ⟨_, _, by
        first
          | exact .out_ctx₁ _ _ ‹_› | exact .out_ctx₂ _ _ ‹_› ‹_› | exact .inp_ctx _ ‹_›
          | exact .ite_ctx _ _ ‹_› | exact .let_ctx _ _ ‹_› | exact .event_ctx _ _ _ ‹_› ‹_›
          | exact .eval₂ _ _ | exact .cond₂ _ _ ‹_› ‹_› | (constructor <;> assumption),
        by first | rfl | simp only [add_cons']⟩)

/-! ### Runs -/

theorem Runs.tauStar {c c' : Config F G Ev} {t : Trace A.Msg} (h : TauStar A c c')
    (hr : Runs A c' t) : Runs A c t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hr
  | head hs _ ih => exact .tau hs ih

/-- A run with a first action: `τ`-steps, the action, and a run. -/
theorem Runs.cons {c : Config F G Ev} {a : Act A.Msg} {t : Trace A.Msg} (h : Runs A c (a :: t)) :
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
theorem Runs.nonces {c : Config F G Ev} {t : Trace A.Msg} (h : Runs A c t) :
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
theorem Runs.mono {c : Config F G Ev} {t : Trace A.Msg} (h : Runs A c t) {U : Finset ℕ}
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
theorem TauStar.add {U U₁ : Finset ℕ} {Ps : Multiset (Process F G Ev 0)} {c : Config F G Ev}
    (h : TauStar A ⟨U, Ps⟩ c) (Qs : Multiset (Process F G Ev 0)) :
    ∃ Ps', c = ⟨U, Ps'⟩ ∧ TauStar A ⟨U ∪ U₁, Ps + Qs⟩ ⟨U ∪ U₁, Ps' + Qs⟩ := by
  induction h with
  | refl => exact ⟨Ps, rfl, .refl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨Ps', rfl, ih⟩ := ih
    obtain ⟨U'', Ps''⟩ := c
    rcases hbc.names_eq with ⟨k, hk, -, -⟩ | ⟨-, rfl⟩
    · cases hk
    · exact ⟨Ps'', rfl, ih.tail (hbc.add Qs fun _ h => nomatch h)⟩

theorem TauStar.add_left {U U₀ : Finset ℕ} {Qs : Multiset (Process F G Ev 0)} {c : Config F G Ev}
    (h : TauStar A ⟨U, Qs⟩ c) (Ps : Multiset (Process F G Ev 0)) :
    ∃ Qs', c = ⟨U, Qs'⟩ ∧ TauStar A ⟨U₀ ∪ U, Ps + Qs⟩ ⟨U₀ ∪ U, Ps + Qs'⟩ := by
  obtain ⟨Qs', rfl, h'⟩ := h.add (U₁ := U₀) Ps
  exact ⟨Qs', rfl, by rwa [Finset.union_comm, add_comm Qs, add_comm Qs'] at h'⟩

/-! ### Runs of term configurations -/

theorem TRuns.append {U U' U'' : Finset ℕ} {D D' D'' : Expr F G Ev 0} {t t' : Trace A.Msg}
    (h : TRuns A U D t U' D') (h' : TRuns A U' D' t' U'' D'') :
    TRuns A U D (t ++ t') U'' D'' := by
  induction h with
  | nil => exact h'
  | tau hs _ ih => exact .tau hs (ih h')
  | act hs _ ih => exact .act hs (ih h')

theorem Trace.nonces_append {M : Type} :
    ∀ l₁ l₂ : Trace M, Trace.nonces (l₁ ++ l₂) = l₁.nonces ++ l₂.nonces
  | [], _ => rfl
  | a :: l₁, l₂ => by cases a <;> simp [Trace.nonces, Trace.nonces_append l₁ l₂]

/-- A run of a term configuration only creates names. -/
theorem TRuns.subset {U U' : Finset ℕ} {D D' : Expr F G Ev 0} {t : Trace A.Msg}
    (h : TRuns A U D t U' D') : U ⊆ U' := by
  induction h with
  | nil => exact subset_rfl
  | tau hs _ ih =>
    rcases hs.names_eq with ⟨k, hk, -, -⟩ | ⟨-, rfl⟩
    · cases hk
    · exact ih
  | act hs _ ih =>
    rcases hs.names_eq with ⟨k, -, -, rfl⟩ | ⟨-, rfl⟩
    · exact (Finset.subset_insert k _).trans ih
    · exact ih

/-- The names a run of a term configuration creates are fresh for those created before. -/
theorem TRuns.fresh {U U' : Finset ℕ} {D D' : Expr F G Ev 0} {t : Trace A.Msg}
    (h : TRuns A U D t U' D') : ∀ k ∈ t.nonces, k ∉ U := by
  induction h with
  | nil => simp [Trace.nonces]
  | tau hs _ ih =>
    rcases hs.names_eq with ⟨k, hk, -, -⟩ | ⟨-, rfl⟩
    · cases hk
    · exact ih
  | @act U D U₁ D₁ a t U₂ D₂ hs _ ih =>
    rcases hs.names_eq with ⟨k, hk, hkU, rfl⟩ | ⟨hl, rfl⟩
    · obtain rfl := Option.some.inj hk
      intro k' hk'
      simp only [Trace.nonces] at hk'
      rcases List.mem_cons.1 hk' with rfl | hk'
      · exact hkU
      · exact fun h => ih k' hk' (Finset.mem_insert_of_mem h)
    · cases a <;> first | exact (hl _ rfl).elim | simpa [Trace.nonces] using ih

theorem ArgRuns.append {k : ℕ} {U U' U'' : Finset ℕ} {args args' args'' : Fin k → Expr F G Ev 0}
    {t t' : Trace A.Msg} (h : ArgRuns A U args t U' args') (h' : ArgRuns A U' args' t' U'' args'') :
    ArgRuns A U args (t ++ t') U'' args'' := by
  induction h with
  | nil => exact h'
  | tau i hv hs _ ih => exact .tau i hv hs (ih h')
  | act i hv hs _ ih => exact .act i hv hs (ih h')

/-- A run of the arguments only creates names. -/
theorem ArgRuns.subset {k : ℕ} {U U' : Finset ℕ} {args args' : Fin k → Expr F G Ev 0}
    {t : Trace A.Msg} (h : ArgRuns A U args t U' args') : U ⊆ U' := by
  induction h with
  | nil => exact subset_rfl
  | tau i hv hs _ ih =>
    rcases hs.names_eq with ⟨k, hk, -, -⟩ | ⟨-, rfl⟩
    · cases hk
    · exact ih
  | act i hv hs _ ih =>
    rcases hs.names_eq with ⟨k, -, -, rfl⟩ | ⟨-, rfl⟩
    · exact (Finset.subset_insert k _).trans ih
    · exact ih

/-- The names a run of the arguments creates are fresh for those created before. -/
theorem ArgRuns.fresh {k : ℕ} {U U' : Finset ℕ} {args args' : Fin k → Expr F G Ev 0}
    {t : Trace A.Msg} (h : ArgRuns A U args t U' args') : ∀ k ∈ t.nonces, k ∉ U := by
  induction h with
  | nil => simp [Trace.nonces]
  | tau i hv hs _ ih =>
    rcases hs.names_eq with ⟨k, hk, -, -⟩ | ⟨-, rfl⟩
    · cases hk
    · exact ih
  | @act U args i U₁ D₁ a t U₂ args₂ hv hs _ ih =>
    rcases hs.names_eq with ⟨k, hk, hkU, rfl⟩ | ⟨hl, rfl⟩
    · obtain rfl := Option.some.inj hk
      intro k' hk'
      simp only [Trace.nonces] at hk'
      rcases List.mem_cons.1 hk' with rfl | hk'
      · exact hkU
      · exact fun h => ih k' hk' (Finset.mem_insert_of_mem h)
    · cases a <;> first | exact (hl _ rfl).elim | simpa [Trace.nonces] using ih

/-- A run of the `i`-th argument, those before it being may-fail terms, is a run of the
arguments. -/
theorem TRuns.argRuns {k : ℕ} {args : Fin k → Expr F G Ev 0} {i : Fin k}
    (hv : ∀ j, j < i → (args j).IsValue) {U U' : Finset ℕ} {D D' : Expr F G Ev 0}
    {t : Trace A.Msg} (h : TRuns A U D t U' D') (hD : args i = D) :
    ArgRuns A U args t U' (Function.update args i D') := by
  induction h generalizing args with
  | nil U D =>
    rw [← hD, Function.update_eq_self]
    exact .nil _ _
  | @tau U D U₁ D₁ t U₂ D₂ hs _ ih =>
    refine .tau i hv (hD ▸ hs) ?_
    have := ih (args := Function.update args i D₁)
      (fun j hj => by rw [Function.update_of_ne (ne_of_lt hj)]; exact hv j hj)
      (Function.update_self ..)
    rwa [Function.update_idem] at this
  | @act U D U₁ D₁ a t U₂ D₂ hs _ ih =>
    refine .act i hv (hD ▸ hs) ?_
    have := ih (args := Function.update args i D₁)
      (fun j hj => by rw [Function.update_of_ne (ne_of_lt hj)]; exact hv j hj)
      (Function.update_self ..)
    rwa [Function.update_idem] at this

/-- A context of expressions: a term step of the expression in the hole is a term step of
the whole. -/
def TStep.IsCtx (A : Model F G Ev) (C : Expr F G Ev 0 → Expr F G Ev 0) : Prop :=
  ∀ {U U' : Finset ℕ} {D D' : Expr F G Ev 0} {l : Option (Act A.Msg)},
    TStep A U D l U' D' → TStep A U (C D) l U' (C D')

/-- A context of processes: a term step of the expression in the hole is a step of the
process. -/
def Step.IsCtx (A : Model F G Ev) (C : Expr F G Ev 0 → Process F G Ev 0) : Prop :=
  ∀ {U U' : Finset ℕ} {D D' : Expr F G Ev 0} {l : Option (Act A.Msg)},
    TStep A U D l U' D' → Step A ⟨U, {C D}⟩ l ⟨U', {C D'}⟩

/-- A run of a term configuration is a run of it in a context of expressions. -/
theorem TRuns.lift {C : Expr F G Ev 0 → Expr F G Ev 0} (hC : TStep.IsCtx A C) {U U' : Finset ℕ}
    {D D' : Expr F G Ev 0} {t : Trace A.Msg} (h : TRuns A U D t U' D') :
    TRuns A U (C D) t U' (C D') := by
  induction h with
  | nil => exact .nil _ _
  | tau hs _ ih => exact .tau (hC hs) ih
  | act hs _ ih => exact .act (hC hs) ih

/-- A run of a term configuration, then a run of the process in a context of processes,
is a run of the process from the start. -/
theorem Runs.ctx {C : Expr F G Ev 0 → Process F G Ev 0} (hC : Step.IsCtx A C) {U U' : Finset ℕ}
    {D D' : Expr F G Ev 0} {t t' : Trace A.Msg} (h : TRuns A U D t U' D')
    (hr : Runs A ⟨U', {C D'}⟩ t') : Runs A ⟨U, {C D}⟩ (t ++ t') := by
  induction h with
  | nil => exact hr
  | tau hs _ ih => exact .tau (hC hs) (ih hr)
  | act hs _ ih => exact .act (hC hs) (ih hr)

/-- A `k`-ary context of expressions: a term step of an argument, those before it being
may-fail terms, is a term step of the whole. -/
def TStep.IsArgCtx (A : Model F G Ev) {k : ℕ} (H : (Fin k → Expr F G Ev 0) → Expr F G Ev 0) :
    Prop :=
  ∀ {U U' : Finset ℕ} {args : Fin k → Expr F G Ev 0} {i : Fin k} {D' : Expr F G Ev 0}
    {l : Option (Act A.Msg)}, (∀ j, j < i → (args j).IsValue) → TStep A U (args i) l U' D' →
    TStep A U (H args) l U' (H (Function.update args i D'))

/-- A `k`-ary context of processes: a term step of an argument, those before it being
may-fail terms, is a step of the process. -/
def Step.IsArgCtx (A : Model F G Ev) {k : ℕ} (C : (Fin k → Expr F G Ev 0) → Process F G Ev 0) :
    Prop :=
  ∀ {U U' : Finset ℕ} {args : Fin k → Expr F G Ev 0} {i : Fin k} {D' : Expr F G Ev 0}
    {l : Option (Act A.Msg)}, (∀ j, j < i → (args j).IsValue) → TStep A U (args i) l U' D' →
    Step A ⟨U, {C args}⟩ l ⟨U', {C (Function.update args i D')}⟩

/-- A run of the arguments is a run of them in a `k`-ary context of expressions. -/
theorem ArgRuns.lift {k : ℕ} {H : (Fin k → Expr F G Ev 0) → Expr F G Ev 0}
    (hH : TStep.IsArgCtx A H) {U U' : Finset ℕ} {args args' : Fin k → Expr F G Ev 0}
    {t : Trace A.Msg} (h : ArgRuns A U args t U' args') : TRuns A U (H args) t U' (H args') := by
  induction h with
  | nil => exact .nil _ _
  | tau i hv hs _ ih => exact .tau (hH hv hs) ih
  | act i hv hs _ ih => exact .act (hH hv hs) ih

/-- A run of the arguments, then a run of the process in a `k`-ary context of processes,
is a run of the process from the start. -/
theorem Runs.argCtx {k : ℕ} {C : (Fin k → Expr F G Ev 0) → Process F G Ev 0}
    (hC : Step.IsArgCtx A C) {U U' : Finset ℕ} {args args' : Fin k → Expr F G Ev 0}
    {t t' : Trace A.Msg} (h : ArgRuns A U args t U' args') (hr : Runs A ⟨U', {C args'}⟩ t') :
    Runs A ⟨U, {C args}⟩ (t ++ t') := by
  induction h with
  | nil => exact hr
  | tau i hv hs _ ih => exact .tau (hC hv hs) (ih hr)
  | act i hv hs _ ih => exact .act (hC hv hs) (ih hr)

/-! ### Runs of a union

A run of a union of two multisets interleaves runs of each, with communications
between them, and conversely; the names created by the two must be distinct.
-/

/-- Runs of two multisets, interleaved and with communications between them, are a run
of their union. -/
theorem runs_add {s : TaggedTrace (Fin 2) A.Msg} {t : Trace A.Msg} (hc : s.Comms t) :
    ∀ {U₀ U₁ : Finset ℕ} {Ps Qs : Multiset (Process F G Ev 0)} {t₀ t₁ : Trace A.Msg},
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
theorem Runs.split {c : Config F G Ev} {t : Trace A.Msg} (h : Runs A c t) :
    ∀ {U : Finset ℕ} {Ps Qs : Multiset (Process F G Ev 0)}, c = ⟨U, Ps + Qs⟩ →
      ∃ (t₀ t₁ : Trace A.Msg) (s : TaggedTrace (Fin 2) A.Msg), Runs A ⟨U, Ps⟩ t₀ ∧
        Runs A ⟨U, Qs⟩ t₁ ∧ s.proj 0 = t₀ ∧ s.proj 1 = t₁ ∧ s.Comms t := by
  induction h with
  | nil c =>
    rintro U Ps Qs rfl
    exact ⟨[], [], [], .nil _, .nil _, rfl, rfl, .nil⟩
  | tau hs _ ih =>
    rintro U Ps Qs rfl
    rcases hs.add_cases rfl with ⟨U', Ps', hs', rfl⟩ | ⟨U', Qs', hs', rfl⟩ |
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
    rcases hs.add_cases rfl with ⟨U', Ps', hs', rfl⟩ | ⟨U', Qs', hs', rfl⟩ |
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

/-- The public names: the public nullary declared constructors. -/
def Model.Npub : Set (F 0) := A.pubFun 0

/-- A constructor of the calculus is public: a public declared one, or a data symbol; the
event symbols are private. -/
def Model.Public : ∀ {n : ℕ}, Sig.cons F Ev n → Prop
  | _, .inl (.inl f) => f ∈ A.pubFun _
  | _, .inl (.inr _) => False
  | _, .inr _ => True

/-- A destructor of the calculus is public: a public declared one, or a built-in one. -/
def Model.PublicDt : ∀ {n : ℕ}, Sig.withBuiltin G n → Prop
  | _, .inl g => g ∈ A.pubDtor _
  | _, .inr _ => True

/-- Every symbol of the term is public, and no created name occurs. -/
def Model.PubTerm : Tm F Ev n → Prop
  | .var (.inl _) => False
  | .var (.inr _) => True
  | .func f ts => A.Public f ∧ ∀ i, Model.PubTerm (ts i)

/-- Every symbol of the expression is public, no created name occurs, and it has no
event. -/
def Model.PubExpr : ∀ {n : ℕ}, Expr F G Ev n → Prop
  | _, .term M => A.PubTerm M
  | _, .ctor f args => A.Public f ∧ ∀ i, Model.PubExpr (args i)
  | _, .dtor g args => A.PublicDt g ∧ ∀ i, Model.PubExpr (args i)
  | _, .fail => True
  | _, .new D => Model.PubExpr D
  | _, .ite C D₁ D₂ => Model.PubExpr C ∧ Model.PubExpr D₁ ∧ Model.PubExpr D₂
  | _, .let_ D D₁ D₂ => Model.PubExpr D ∧ Model.PubExpr D₁ ∧ Model.PubExpr D₂
  | _, .event _ _ _ => False

/-- An `N_pub`-adversary, the survey's Definition 3.1 over the manual's terms: its names
and symbols are public and it has no event, inside its terms too; it may use `new`, `if`
and `let` there. -/
def Model.Adversary : ∀ {n : ℕ}, Process F G Ev n → Prop
  | _, .nil => True
  | _, .out N M P => A.PubExpr N ∧ A.PubExpr M ∧ Model.Adversary P
  | _, .inp N P => A.PubExpr N ∧ Model.Adversary P
  | _, .par P Q => Model.Adversary P ∧ Model.Adversary Q
  | _, .bang P => Model.Adversary P
  | _, .new P => Model.Adversary P
  | _, .let_ D P Q => A.PubExpr D ∧ Model.Adversary P ∧ Model.Adversary Q
  | _, .ite C P Q => A.PubExpr C ∧ Model.Adversary P ∧ Model.Adversary Q
  | _, .event _ _ _ => False

/-- The configuration `C_Q` of the protocol `P₀` against the adversary `Q`. -/
def Config.against (P₀ Q : Process F G Ev 0) : Config F G Ev := ⟨∅, {P₀, Q}⟩

/-- A trace of the manual's semantics from `c`: a run whose labels are closed, the
manual's transition relation having no rule for an offer. -/
def Model.ManualTrace (c : Config F G Ev) (t : Trace A.Msg) : Prop := Runs A c t ∧ t.Closed

/-- The trace outputs `m` publicly, the survey's Definition 3.2: a communication on a
public name carries it. -/
def Model.OutputsPublicly (t : Trace A.Msg) (m : A.Msg) : Prop :=
  ∃ a ∈ A.Npub, Act.comm (Theory.Msg.app (.inl (.inl a)) ![]) m ∈ t

/-- `P₀` preserves the secrecy of the closed term `M` from `N_pub`, the survey's
Definition 3.3. -/
def Model.Preserves (P₀ : Process F G Ev 0) (M : Tm F Ev 0) : Prop :=
  ∀ Q, A.Adversary Q → ∀ t, A.ManualTrace (.against P₀ Q) t → ¬ A.OutputsPublicly t (Tm.msg A M)

/-- The attacker derives `m` from the messages `S`: the Dolev–Yao deduction of the write-up's
Definition "Deduction, knowledge", applying the public constructors and, by the manual's
rewriting, the public destructors to what it has, as the survey's adversary does (§3.1). -/
inductive Model.Derives (S : Set A.Msg) : A.Msg → Prop
  | mem {m : A.Msg} : m ∈ S → Model.Derives S m
  | ctor {k : ℕ} (f : Sig.cons F Ev k) {ms : Fin k → A.Msg} : A.Public f →
      (∀ i, Model.Derives S (ms i)) → Model.Derives S (Theory.Msg.app f ms)
  | dtor {k : ℕ} (g : Sig.withBuiltin G k) {us : Fin k → Option A.Msg} {m : A.Msg} :
      A.PublicDt g → (∀ i m', us i = some m' → Model.Derives S m') →
      Rewrites (A.rules g) us (some m) → Model.Derives S m

/-- The attacker's knowledge after the trace `t`: nothing at first, the public names being
public nullary symbols, and then every message communicated on a channel it could derive at
the time, since it intercepts every message on a channel it has (survey §3.1), whoever
received the message. -/
def Model.knowledge (t : Trace A.Msg) : Set A.Msg :=
  t.foldl (fun K a => K ∪ {m | ∃ c, a = .comm c m ∧ A.Derives K c}) ∅

/-- The attacker knows `m` after the trace `t`: it derives `m` from its knowledge. -/
def Model.Knows (t : Trace A.Msg) (m : A.Msg) : Prop := A.Derives (A.knowledge t) m

/-- A query fact over the variables `X`: `event(ev(M₁, …, Mₖ))` or `attacker(M)` with the
`Mᵢ` and `M` terms over constructors, free names and `X`. -/
inductive QueryFact (F Ev : Sig) (X : Type) : Type
  | event {k : ℕ} (e : Ev k) (args : Fin k → (Sig.cons F Ev).lang.Term X)
  | attacker (M : (Sig.cons F Ev).lang.Term X)

/-- The trace satisfies the instance of the query fact under `σ`, the write-up's
Definition "Satisfaction": an attacker fact when the attacker knows the term, as the manual
reads it on either side of a correspondence (§4.3.1), and an event fact when the event is
executed. -/
def QueryFact.Satisfied {X : Type} (t : Trace A.Msg) (σ : X → A.Msg) : QueryFact F Ev X → Prop
  | .event e args =>
    Act.event (Theory.Msg.app (.inl (.inr e)) fun i => (args i).realize σ) ∈ t
  | .attacker M => A.Knows t (M.realize σ)

variable {A}

/-- The instance of a query fact under `σ`, as a fact of the trace semantics. -/
def QueryFact.inst {X : Type} (σ : X → A.Msg) : QueryFact F Ev X → Fact A.Msg
  | .event e args => .event (Theory.Msg.app (.inl (.inr e)) fun i => (args i).realize σ)
  | .attacker M => .knows (M.realize σ)

variable (A)

/-- `P₀` satisfies `F ⇝ H` against `N_pub`-adversaries, the write-up's Definition
"Correspondences between facts" for single facts: in every trace of the manual in which
`F σ` is satisfied, some `H σ'` with `F σ' = F σ` is. -/
def Model.Satisfies (P₀ : Process F G Ev 0) {X : Type} (Fq Hq : QueryFact F Ev X) : Prop :=
  ∀ Q, A.Adversary Q → ∀ t, A.ManualTrace (.against P₀ Q) t → ∀ σ : X → A.Msg,
    Fq.Satisfied A t σ → ∃ σ' : X → A.Msg, Fq.inst σ' = Fq.inst σ ∧ Hq.Satisfied A t σ'

end

end ProVerif.Specification
