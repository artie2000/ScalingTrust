/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.Specification.Semantics

/-!
# The denotation in the trace semantics

The write-up's Definition "Translation" and its Lemma "Evaluation".

* A destructor denotes the function of the write-up's Definition "Destructors from
  rewrite rules", `Model.dtorFun`: the right-hand side of the first rule with a
  matching, or `fail`.  Two matchings against a rule give the same right-hand side
  (`Rule.Matching.eval_eq`), so the matching chosen does not matter.
* `Model.alg` is the message algebra of the model, with which the trace semantics
  defines the attacker: the public constructors and the functions of the public
  destructors.
* An expression under `n` binders is evaluated in an environment `env xs` with
  `xs : Fin n → A.Msg`, the created name `ν_k` being the nonce `Theory.Msg.name k`;
  `eval_iff` is the Evaluation lemma, that the survey's evaluation of a closed
  expression is total and its value is the expression's denotation.
* A process under `n` binders denotes, for each environment, a process of the trace
  semantics, `Process.denote`; `in`, `new` and `let` extend the environment with
  `Fin.snoc`.  Substitution commutes with denotation, `Process.denote_inst`: `P{M/x}`
  denotes what `P` denotes in the environment extended by the message of `M`.
-/

namespace ProVerif.Specification

open FirstOrder FirstOrder.Language ProVerif.TraceSemantics

variable {F G : Sig} {A : Model F G} {n m : ℕ}

/-! ## Destructors as functions -/

/-- Evaluation depends only on the variables of the term. -/
theorem realize_eq_of_varFinset {α M : Type} [F.lang.Structure M] [DecidableEq α]
    {v w : α → M} : ∀ {t : F.lang.Term α}, (∀ x ∈ t.varFinset, v x = w x) →
      t.realize v = t.realize w
  | .var x, h => h x (by simp [Term.varFinset])
  | .func f ts, h => by
    simp only [Term.realize_func]
    congr 1
    funext i
    refine realize_eq_of_varFinset fun x hx => h x ?_
    simp only [Term.varFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, hx⟩

/-- Two matchings of `u` against a pattern over the free symbols agree on its
variables. -/
theorem Pat.Matching.eq_of_mem {θ θ' : ℕ → A.Msg} {μ μ' : ℕ → Option A.Msg} :
    ∀ {p : Pat F} {u : Option A.Msg}, p.Free A.toTheory → p.Matching θ μ u →
      p.Matching θ' μ' u → (∀ x ∈ p.vars, θ x = θ' x) ∧ ∀ v ∈ p.mvars, μ v = μ' v
  | .var x, _, _, h, h' => by
    refine ⟨fun y hy => ?_, by simp [Pat.mvars]⟩
    rw [Pat.vars, Finset.mem_singleton] at hy
    subst hy
    exact Option.some_injective _ (h.symm.trans h')
  | .mvar v, _, _, h, h' => by
    refine ⟨by simp [Pat.vars], fun w hw => ?_⟩
    rw [Pat.mvars, Finset.mem_singleton] at hw
    subst hw
    exact h.symm.trans h'
  | .fail, _, _, _, _ => ⟨by simp [Pat.vars], by simp [Pat.mvars]⟩
  | .app f args, u, hf, ⟨ms, hu, h⟩, ⟨ms', hu', h'⟩ => by
    obtain rfl : ms = ms' := by
      have := congrArg Theory.Msg.view (Option.some_injective _ (hu.symm.trans hu'))
      simpa [hf.1] using this
    simp only [Pat.vars, Pat.mvars, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨fun x ⟨i, hi⟩ => (Pat.Matching.eq_of_mem (hf.2 i) (h i) (h' i)).1 x hi,
      fun v ⟨i, hi⟩ => (Pat.Matching.eq_of_mem (hf.2 i) (h i) (h' i)).2 v hi⟩

/-- Two matchings against the patterns of a rule give the same right-hand side. -/
theorem Rule.Matching.eval_eq {r : Rule A.toTheory n} {us : Fin n → Option A.Msg}
    {θ θ' : ℕ → A.Msg} {μ μ' : ℕ → Option A.Msg} (h : r.Matching θ μ us)
    (h' : r.Matching θ' μ' us) : r.rhs.eval θ μ = r.rhs.eval θ' μ' := by
  cases hr : r.rhs with
  | fail => rfl
  | mvar v =>
    have hv : v ∈ r.rhs.mvars := by simp [hr, Rhs.mvars]
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (r.mvars hv)
    exact (Pat.Matching.eq_of_mem (r.free i) (h i) (h' i)).2 v hi
  | term M =>
    simp only [Rhs.eval]
    congr 1
    refine realize_eq_of_varFinset fun x hx => ?_
    have hx : x ∈ r.rhs.vars := by simp [hr, Rhs.vars, hx]
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (r.vars hx)
    exact (Pat.Matching.eq_of_mem (r.free i) (h i) (h' i)).1 x hi

open Classical in
/-- The right-hand side under a matching of the arguments against the rule, if there is
one. -/
noncomputable def Rule.apply (r : Rule A.toTheory n) (us : Fin n → Option A.Msg) :
    Option (Option A.Msg) :=
  if h : ∃ θ μ, r.Matching θ μ us then some (r.rhs.eval h.choose h.choose_spec.choose) else none

theorem Rule.apply_eq_some {r : Rule A.toTheory n} {us : Fin n → Option A.Msg}
    {θ : ℕ → A.Msg} {μ : ℕ → Option A.Msg} (h : r.Matching θ μ us) :
    r.apply us = some (r.rhs.eval θ μ) := by
  have h' : ∃ θ μ, r.Matching θ μ us := ⟨θ, μ, h⟩
  rw [Rule.apply, dif_pos h']
  exact congrArg some (Rule.Matching.eval_eq h'.choose_spec.choose_spec h)

theorem Rule.apply_eq_none {r : Rule A.toTheory n} {us : Fin n → Option A.Msg}
    (h : ¬ ∃ θ μ, r.Matching θ μ us) : r.apply us = none := by
  rw [Rule.apply, dif_neg h]

/-- The destructor the rules of `g` define: the first rule with a matching decides, and
the result is `fail` when none has one. -/
noncomputable def Model.dtorFun (g : G n) (us : Fin n → Option A.Msg) : Option A.Msg :=
  ((A.dtor g).findSome? (·.apply us)).join

/-- The rules rewrite to the value of the destructor they define. -/
theorem rewrites_iff {rs : List (Rule A.toTheory n)} {us : Fin n → Option A.Msg}
    {v : Option A.Msg} : Rewrites rs us v ↔ (rs.findSome? (·.apply us)).join = v := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | head hm => simp [Rule.apply_eq_some hm]
    | tail hn _ ih => simp [Rule.apply_eq_none hn, ih]
  · rintro rfl
    induction rs with
    | nil => exact .nil us
    | cons r rs ih =>
      by_cases h : ∃ θ μ, r.Matching θ μ us
      · obtain ⟨θ, μ, hm⟩ := h
        simpa [Rule.apply_eq_some hm] using Rewrites.head (rs := rs) hm
      · simpa [Rule.apply_eq_none h] using Rewrites.tail h ih

/-- The message algebra of the model: its theory, its public constructors, and the
functions of its public destructors. -/
noncomputable abbrev Model.alg (A : Model F G) : MsgAlgebra F where
  toTheory := A.toTheory
  pubFun := A.pubFun
  pubDtors := ⋃ n, (fun g : G n => (⟨n, A.dtorFun g⟩ :
    Σ n, (Fin n → Option A.Msg) → Option A.Msg)) '' A.pubDtor n

/-! ## Expressions -/

/-- The value of an expression in the environment `env`, `none` being `fail`. -/
noncomputable def Expr.denote {α : Type} (env : α → A.Msg) : Expr F G α → Option A.Msg
  | .term M => some (M.realize env)
  | .ctor f args => liftFail (fun ms => some (Theory.Msg.app f ms)) fun i => (args i).denote env
  | .dtor g args => A.dtorFun g fun i => (args i).denote env
  | .fail => none

theorem Eval.denote_eq {D : Expr F G (ℕ ⊕ Fin 0)} {v : Option A.Msg} (h : Eval A D v) :
    v = D.denote (env finZeroElim) := by
  induction h with
  | term M => rfl
  | fail => rfl
  | ctor f _ ih =>
    simp only [Expr.denote]
    congr 1
    funext i
    exact ih i
  | dtor g _ hr ih =>
    rw [← rewrites_iff.1 hr]
    show Model.dtorFun g _ = Model.dtorFun g _
    congr 1
    funext i
    exact ih i

theorem eval_denote : ∀ D : Expr F G (ℕ ⊕ Fin 0), Eval A D (D.denote (env finZeroElim))
  | .term M => .term M
  | .fail => .fail
  | .ctor f args => .ctor f fun i => eval_denote (args i)
  | .dtor g args => .dtor g (fun i => eval_denote (args i)) (rewrites_iff.2 rfl)

/-- The Evaluation lemma: a closed expression evaluates exactly to its denotation. -/
theorem eval_iff {D : Expr F G (ℕ ⊕ Fin 0)} {v : Option A.Msg} :
    Eval A D v ↔ v = D.denote (env finZeroElim) :=
  ⟨Eval.denote_eq, fun h => h ▸ eval_denote D⟩

/-! ## Processes -/

open Classical in
/-- The process of the trace semantics that a process under `n` binders denotes in the
environment `xs`. -/
noncomputable def Process.denote : {n : ℕ} → Process F G n → (Fin n → A.Msg) → Proc A.Msg
  | _, .nil, _ => Proc.nil
  | _, .out N M P, xs => Proc.out (N.realize (env xs)) (M.realize (env xs)) (P.denote xs)
  | _, .inp N P, xs => Proc.inp (N.realize (env xs)) fun a => P.denote (Fin.snoc xs a)
  | _, .par P Q, xs => Proc.par (P.denote xs) (Q.denote xs)
  | _, .bang P, xs => Proc.bang (P.denote xs)
  | _, .new P, xs => Proc.new fun a => P.denote (Fin.snoc xs a)
  | _, .let_ D P Q, xs =>
    match D.denote (env xs) with
    | some a => P.denote (Fin.snoc xs a)
    | none => Q.denote xs
  | _, .ite M P Q, xs =>
    if M.realize (env xs) = Theory.Msg.app A.tt ![] then P.denote xs else Q.denote xs
  | _, .event M P, xs => Proc.event (M.realize (env xs)) (P.denote xs)

/-! ## Substitution -/

theorem Expr.denote_subst (σ : Fin n → Tm F m) (xs : Fin m → A.Msg) :
    ∀ D : Expr F G (ℕ ⊕ Fin n),
      (D.subst σ).denote (env xs) = D.denote (env fun i => (σ i).realize (env xs))
  | .term M => by simp only [Expr.subst, Expr.denote, Tm.realize_subst]
  | .ctor f args => by
    simp only [Expr.subst, Expr.denote]
    congr 1
    funext i
    exact Expr.denote_subst σ xs (args i)
  | .dtor g args => by
    simp only [Expr.subst, Expr.denote]
    congr 1
    funext i
    exact Expr.denote_subst σ xs (args i)
  | .fail => rfl

theorem Process.denote_subst :
    ∀ {n m : ℕ} (σ : Fin n → Tm F m) (P : Process F G n) (xs : Fin m → A.Msg),
      (P.subst σ).denote xs = P.denote fun i => (σ i).realize (env xs)
  | _, _, _, .nil, _ => rfl
  | _, _, σ, .out N M P, xs => by
    simp only [Process.subst, Process.denote, Tm.realize_subst, Process.denote_subst σ P xs]
  | _, _, σ, .inp N P, xs => by
    have h : (fun a => (P.subst (liftSubst σ)).denote (Fin.snoc xs a)) =
        fun a => P.denote (Fin.snoc (α := fun _ => A.Msg) (fun i => (σ i).realize (env xs)) a) :=
        funext fun a => by
      rw [Process.denote_subst (liftSubst σ) P (Fin.snoc xs a)]
      congr 1
      funext i
      exact realize_liftSubst σ xs a i
    simp only [Process.subst, Process.denote, Tm.realize_subst, h]
  | _, _, σ, .par P Q, xs => by
    simp only [Process.subst, Process.denote, Process.denote_subst σ P xs,
      Process.denote_subst σ Q xs]
  | _, _, σ, .bang P, xs => by
    simp only [Process.subst, Process.denote, Process.denote_subst σ P xs]
  | _, _, σ, .new P, xs => by
    have h : (fun a => (P.subst (liftSubst σ)).denote (Fin.snoc xs a)) =
        fun a => P.denote (Fin.snoc (α := fun _ => A.Msg) (fun i => (σ i).realize (env xs)) a) :=
        funext fun a => by
      rw [Process.denote_subst (liftSubst σ) P (Fin.snoc xs a)]
      congr 1
      funext i
      exact realize_liftSubst σ xs a i
    simp only [Process.subst, Process.denote, h]
  | _, _, σ, .let_ D P Q, xs => by
    have h : (fun a => (P.subst (liftSubst σ)).denote (Fin.snoc xs a)) =
        fun a => P.denote (Fin.snoc (α := fun _ => A.Msg) (fun i => (σ i).realize (env xs)) a) :=
        funext fun a => by
      rw [Process.denote_subst (liftSubst σ) P (Fin.snoc xs a)]
      congr 1
      funext i
      exact realize_liftSubst σ xs a i
    simp only [Process.subst, Process.denote, Expr.denote_subst, Process.denote_subst σ Q xs]
    cases D.denote (env fun i => (σ i).realize (env xs)) with
    | none => rfl
    | some a => exact congrFun h a
  | _, _, σ, .ite M P Q, xs => by
    simp only [Process.subst, Process.denote, Process.denote_subst σ P xs,
      Process.denote_subst σ Q xs]
    rw [Tm.realize_subst]
  | _, _, σ, .event M P, xs => by
    simp only [Process.subst, Process.denote, Tm.realize_subst, Process.denote_subst σ P xs]

/-- `P{M/x}` denotes what `P` denotes in the environment extended by `M`'s message. -/
theorem Process.denote_inst (P : Process F G (n + 1)) (M : Tm F n) (xs : Fin n → A.Msg) :
    (P.inst M).denote xs = P.denote (Fin.snoc xs (M.realize (env xs))) := by
  rw [Process.inst, Process.denote_subst]
  congr 1
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp

end ProVerif.Specification
