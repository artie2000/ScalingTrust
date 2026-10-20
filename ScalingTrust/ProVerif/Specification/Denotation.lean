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
  (`Rule.Matching.eval_eq`), so the matching chosen does not matter.  A projection
  denotes the standard operation of the trace semantics, `Model.dtorFun_proj`, and a
  boolean destructor yields `true`, `false` or an argument, `Model.dtorFun_bool`.
* The attacker of the model is the `Attacker` instance of its messages, built by
  `Attacker.ofDecls` from the public constructors and the functions of the public
  declared destructors; so its operations are the standard ones besides, which
  `Model.Public` and `Model.PublicDt` count as public, as they do the boolean
  destructors, which add nothing to what it derives (`Model.dtorFun_mem_derive`).
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

/-- Two valuations under which a term over the free symbols has the same value agree on
its variables: free constructors are injective on messages. -/
theorem Term.Free.realize_inj {θ θ' : ℕ → A.Msg} :
    ∀ {M : Term F.withData}, Term.Free A.withData M → M.realize θ = M.realize θ' →
      ∀ x ∈ M.varFinset, θ x = θ' x
  | .var x, _, h, y, hy => by
    simp only [Term.varFinset, Finset.mem_singleton] at hy
    subst hy
    simpa using h
  | .func f ts, hf, h, x, hx => by
    rw [Term.realize_func, Term.realize_func] at h
    have hts : (fun i => (ts i).realize θ) = fun i => (ts i).realize θ' := by
      have := congrArg Theory.Msg.view h
      simp only [Theory.Msg.view_app, hf.1, if_true] at this
      simpa using this
    simp only [Term.varFinset, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
    obtain ⟨i, hi⟩ := hx
    exact Term.Free.realize_inj (hf.2 i) (congrFun hts i) x hi

/-- Two pairs of valuations giving a may-fail term over the free symbols the same value
agree on its variables. -/
theorem MayFail.Free.eval_inj {θ θ' : ℕ → A.Msg} {μ μ' : ℕ → Option A.Msg} :
    ∀ {U : MayFail F.withData}, U.Free A.withData → U.eval θ μ = U.eval θ' μ' →
      (∀ x ∈ U.vars, θ x = θ' x) ∧ ∀ v ∈ U.mvars, μ v = μ' v
  | .term _, hM, h =>
    ⟨Term.Free.realize_inj hM (Option.some_injective _ h), by simp [MayFail.mvars]⟩
  | .mvar v, _, h => by
    refine ⟨by simp [MayFail.vars], fun w hw => ?_⟩
    rw [MayFail.mvars, Finset.mem_singleton] at hw
    subst hw
    exact h
  | .fail, _, _ => ⟨by simp [MayFail.vars], by simp [MayFail.mvars]⟩

/-- Two matchings against the arguments of a rule give the same right-hand side. -/
theorem Rule.Matching.eval_eq {r : Rule A.withData n} {us : Fin n → Option A.Msg}
    {θ θ' : ℕ → A.Msg} {μ μ' : ℕ → Option A.Msg} (h : r.Matching θ μ us)
    (h' : r.Matching θ' μ' us) : r.rhs.eval θ μ = r.rhs.eval θ' μ' := by
  have agree := fun i => MayFail.Free.eval_inj (r.free i) ((h i).trans (h' i).symm)
  cases hr : r.rhs with
  | fail => rfl
  | mvar v =>
    have hv : v ∈ r.rhs.mvars := by simp [hr, MayFail.mvars]
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (r.mvars hv)
    exact (agree i).2 v hi
  | term M =>
    simp only [MayFail.eval]
    congr 1
    refine realize_eq_of_varFinset fun x hx => ?_
    have hx : x ∈ r.rhs.vars := by simp [hr, MayFail.vars, hx]
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (r.vars hx)
    exact (agree i).1 x hi

open Classical in
/-- The right-hand side under a matching of the arguments against the rule, if there is
one. -/
noncomputable def Rule.apply (r : Rule A.withData n) (us : Fin n → Option A.Msg) :
    Option (Option A.Msg) :=
  if h : ∃ θ μ, r.Matching θ μ us then some (r.rhs.eval h.choose h.choose_spec.choose) else none

theorem Rule.apply_eq_some {r : Rule A.withData n} {us : Fin n → Option A.Msg}
    {θ : ℕ → A.Msg} {μ : ℕ → Option A.Msg} (h : r.Matching θ μ us) :
    r.apply us = some (r.rhs.eval θ μ) := by
  have h' : ∃ θ μ, r.Matching θ μ us := ⟨θ, μ, h⟩
  rw [Rule.apply, dif_pos h']
  exact congrArg some (Rule.Matching.eval_eq h'.choose_spec.choose_spec h)

theorem Rule.apply_eq_none {r : Rule A.withData n} {us : Fin n → Option A.Msg}
    (h : ¬ ∃ θ μ, r.Matching θ μ us) : r.apply us = none := by
  rw [Rule.apply, dif_neg h]

/-- The destructor the rules of `g` define: the first rule with a matching decides, and
the result is `fail` when none has one. -/
noncomputable def Model.dtorFun (g : Sig.withBuiltin G n) (us : Fin n → Option A.Msg) :
    Option A.Msg :=
  ((A.rules g).findSome? (·.apply us)).join

/-- The rules rewrite to the value of the destructor they define. -/
theorem rewrites_iff {rs : List (Rule A.withData n)} {us : Fin n → Option A.Msg}
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

/-- A projection denotes the standard operation: the `i`-th component of a `k`-tuple. -/
theorem Model.dtorFun_proj (k : ℕ) (i : Fin k) (us : Fin 1 → Option A.Msg) :
    A.dtorFun (.inr (.proj k i)) us =
      liftFail (fun a => (StdOps.untuple k (a 0)).map (· i)) us := by
  have hrhs (θ : ℕ → A.Msg) (μ : ℕ → Option A.Msg) :
      (projRule A.toTheory k i).rhs.eval θ μ = some (θ i) := rfl
  have harg (θ : ℕ → A.Msg) (μ : ℕ → Option A.Msg) :
      ((projRule A.toTheory k i).args 0).eval θ μ =
        some (StdOps.tuple k fun j => θ j) := rfl
  simp only [Model.dtorFun, Model.rules, Builtin.rules, List.findSome?_cons, List.findSome?_nil]
  rcases h0 : us 0 with _ | m
  · rw [Rule.apply_eq_none, liftFail]
    · rw [dif_neg]
      · rfl
      · exact fun h => by simpa [h0] using h 0
    · rintro ⟨θ, μ, hm⟩
      have := hm 0
      rw [harg, h0] at this
      cases this
  · rcases hu : StdOps.untuple k m with _ | a
    · rw [Rule.apply_eq_none, liftFail]
      · rw [dif_pos fun j => by rw [Subsingleton.elim j 0, h0]; rfl]
        simp [h0, hu]
      · rintro ⟨θ, μ, hm⟩
        have := hm 0
        rw [harg, h0] at this
        rw [← Option.some_injective _ this, StdOps.untuple_tuple] at hu
        cases hu
    · obtain rfl := StdOps.tuple_untuple hu
      have hm : (projRule A.toTheory k i).Matching
          (fun n => if h : n < k then a ⟨n, h⟩ else a i) (fun _ => none) us := fun j => by
        rw [Subsingleton.elim j 0, harg, h0]
        congr 2
        funext j
        simp
      rw [Rule.apply_eq_some hm, hrhs, liftFail]
      rw [dif_pos fun j => by rw [Subsingleton.elim j 0, h0]; rfl]
      simp [h0, hu]

/-- The attacker of the model, `Attacker.ofDecls` from its public declarations: its
public constructors and free names, the functions of its public destructors, and the
standard operations. -/
noncomputable instance Model.attacker (A : Model F G) : Attacker A.Msg :=
  Attacker.ofDecls A.pubFun (⋃ n, (fun g : G n => (⟨n, A.dtorFun (.inl g)⟩ :
    Σ n, (Fin n → Option A.Msg) → Option A.Msg)) '' A.pubDtor n)

/-- A public constructor applied to derivable messages is derivable; a data symbol is
public. -/
theorem Model.app_mem_derive {f : F.withData n} (hf : A.Public f) {S : Set A.Msg}
    {ms : Fin n → A.Msg} (hms : ∀ i, ms i ∈ Attacker.derive S) :
    Theory.Msg.app f ms ∈ Attacker.derive S := by
  have hS : ClosedUnder Attacker.ops (Attacker.derive S) := Attacker.derive.isClosed_closure S
  rcases f with f | d
  · exact Attacker.app_mem_derive (Attacker.ofDecls_mem hf) hms
  cases d with
  | tuple _ =>
    exact hS _ (Or.inr (Or.inl (Or.inl ⟨n, rfl⟩))) (fun i => some (ms i))
      (fun i m h => Option.some_injective _ h ▸ hms i) _
      ((liftFail_eq_some (f := fun a => some (StdOps.tuple n a))).2 ⟨ms, fun _ => rfl, rfl⟩)
  | tt =>
    rw [show ms = ![] from funext fun i => i.elim0]
    exact hS _ (Or.inr (Or.inr (Or.inl rfl))) (fun i => i.elim0) (fun i => i.elim0) _ rfl
  | ff =>
    rw [show ms = ![] from funext fun i => i.elim0]
    exact hS _ (Or.inr (Or.inr (Or.inr rfl))) (fun i => i.elim0) (fun i => i.elim0) _ rfl

/-- A destructor yields `some r` by the right-hand side of one of its rules under a
matching of the arguments. -/
theorem Model.dtorFun_eq_some {g : Sig.withBuiltin G n} {us : Fin n → Option A.Msg} {r : A.Msg}
    (h : A.dtorFun g us = some r) :
    ∃ ρ ∈ A.rules g, ∃ θ μ, ρ.Matching θ μ us ∧ ρ.rhs.eval θ μ = some r := by
  have hrw : Rewrites (A.rules g) us (some r) := rewrites_iff.2 h
  clear h
  generalize hv : some r = v at hrw
  generalize A.rules g = rs at hrw ⊢
  induction hrw with
  | nil => cases hv
  | head hm => exact ⟨_, List.mem_cons.2 (Or.inl rfl), _, _, hm, rfl⟩
  | tail _ _ ih =>
    obtain ⟨ρ, hρ, θ, μ, hm, he⟩ := ih hv
    exact ⟨ρ, List.mem_cons.2 (Or.inr hρ), θ, μ, hm, he⟩

/-- A boolean destructor yields `true`, `false` or one of its arguments. -/
theorem Model.dtorFun_bool {b : Builtin n} (hb : b.IsBool) {us : Fin n → Option A.Msg}
    {r : A.Msg} (h : A.dtorFun (.inr b) us = some r) :
    r = StdOps.tt ∨ r = StdOps.ff ∨ ∃ i, us i = some r := by
  obtain ⟨ρ, hρ, θ, μ, hm, he⟩ := A.dtorFun_eq_some h
  rcases Builtin.rhs_of_mem_rules hb hρ with h' | h' | ⟨u, h', i, hi⟩
  · rw [h', MayFail.eval_tt] at he
    exact Or.inl (Option.some_injective _ he).symm
  · rw [h', MayFail.eval_ff] at he
    exact Or.inr (Or.inl (Option.some_injective _ he).symm)
  · rw [h'] at he
    exact Or.inr (Or.inr ⟨i, by rw [← hm i, hi]; exact he⟩)

/-- A public destructor applied to derivable arguments yields a derivable message: the
function of a public declared destructor is among the attacker's operations, a projection
is the standard projection, and a boolean destructor yields `true`, `false` or an
argument, so that the attacker needs no operation for it. -/
theorem Model.dtorFun_mem_derive {g : Sig.withBuiltin G n} (hg : A.PublicDt g) {S : Set A.Msg}
    {us : Fin n → Option A.Msg} (hus : ∀ i m, us i = some m → m ∈ Attacker.derive S)
    {r : A.Msg} (hr : A.dtorFun g us = some r) : r ∈ Attacker.derive S := by
  have hS : ClosedUnder Attacker.ops (Attacker.derive S) := Attacker.derive.isClosed_closure S
  rcases g with g | b
  · exact hS _ (Or.inl (Or.inr (Set.mem_iUnion.2 ⟨n, g, hg, rfl⟩))) us hus r hr
  rcases b with ⟨k, i⟩ | _ | _ | _ | _
  · refine hS ⟨1, A.dtorFun (.inr (.proj k i))⟩ (Or.inr (Or.inl (Or.inr ⟨⟨k, i⟩, ?_⟩))) us hus r hr
    exact congrArg _ (funext fun us => (A.dtorFun_proj k i us).symm)
  all_goals
    rcases A.dtorFun_bool (by trivial) hr with rfl | rfl | ⟨i, hi⟩
    · rw [Theory.Msg.tt_def]
      exact A.app_mem_derive (by trivial) fun i => i.elim0
    · rw [Theory.Msg.ff_def]
      exact A.app_mem_derive (by trivial) fun i => i.elim0
    · exact hus i r hi

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
    if M.realize (env xs) = StdOps.tt then P.denote xs else Q.denote xs
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
