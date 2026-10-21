/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.Specification.Semantics

/-!
# The denotation in the trace semantics

The write-up's Definition "Translation".

* A destructor denotes the function of the write-up's Definition "Destructors from
  rewrite rules", `Model.dtorFun`: the right-hand side of the first rule with a
  matching, or `fail`.  Two matchings against a rule give the same right-hand side
  (`Rule.Matching.eval_eq`), by (R2), so the matching chosen does not matter.  A
  projection denotes the standard operation of the trace semantics, `Model.dtorFun_proj`,
  and a boolean destructor yields `true`, `false` or an argument, `Model.dtorFun_bool`.
* The attacker of the model is the `Attacker` instance of its messages, built by
  `Attacker.ofDecls` from the public constructors and the functions of the public
  declared destructors; so its operations are the standard ones besides, which
  `Model.Public` and `Model.PublicDt` count as public, as they do the boolean
  destructors, which add nothing to what it derives (`Model.dtorFun_mem_derive`).  The
  deduction of the calculus, `Model.Derives`, is derivation in the trace semantics
  (`Model.derives_iff_derive`).
* An expression under `n` binders denotes, in an environment `env xs` with
  `xs : Fin n → A.Msg`, a computation in the continuation monad of the trace
  semantics with a may-fail message as its result, `Expr.denote`, as the translator
  emits it: the arguments of a constructor, a destructor or an event are run from left to
  right (`seqFin`), `new` is `Proc.fresh`, `event` is `Proc.emit` of the event message and
  `if` and `let` are case analyses on the result of their first expression.  A may-fail
  term denotes `pure` of its value (`Val.denote`), and running the arguments before the
  `i`-th, which are may-fail terms, reaches the `i`-th (`seqFin_run_update`).
* A process under `n` binders denotes, for each environment, a process of the trace
  semantics, `Process.denote`, running the computations of its expressions with the
  rest of the process as the continuation, and `Proc.nil` where the manual's rules
  block; `in`, `new` and `let` extend the environment with `Fin.snoc`.  Substitution
  commutes with denotation, `Process.denote_inst`: `P{M/x}` denotes what `P` denotes in
  the environment extended by the message of `M`.
-/

namespace ProVerif.Specification

open FirstOrder FirstOrder.Language ProVerif.TraceSemantics

noncomputable section

variable {F G Ev : Sig} {A : Model F G Ev} {n m : ℕ}

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
    ∀ {M : Term (Sig.cons F Ev)}, Term.Free A.theory.withData M → M.realize θ = M.realize θ' →
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
    ∀ {U : MayFail (Sig.cons F Ev)}, U.Free A.theory.withData → U.eval θ μ = U.eval θ' μ' →
      (∀ x ∈ U.vars, θ x = θ' x) ∧ ∀ v ∈ U.mvars, μ v = μ' v
  | .term _, hM, h =>
    ⟨Term.Free.realize_inj hM (Option.some_injective _ h), by simp [MayFail.mvars]⟩
  | .mvar v, _, h => by
    refine ⟨by simp [MayFail.vars], fun w hw => ?_⟩
    rw [MayFail.mvars, Finset.mem_singleton] at hw
    subst hw
    exact h
  | .fail, _, _ => ⟨by simp [MayFail.vars], by simp [MayFail.mvars]⟩

/-- Two matchings against the arguments of a rule whose terms are over the free symbols
give the same right-hand side. -/
theorem Rule.Matching.eval_eq {r : Rule (Sig.cons F Ev) n}
    (hfree : ∀ i, (r.args i).Free A.theory.withData) {us : Fin n → Option A.Msg}
    {θ θ' : ℕ → A.Msg} {μ μ' : ℕ → Option A.Msg} (h : r.Matching θ μ us)
    (h' : r.Matching θ' μ' us) : r.rhs.eval θ μ = r.rhs.eval θ' μ' := by
  have agree := fun i => MayFail.Free.eval_inj (hfree i) ((h i).trans (h' i).symm)
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
def Rule.apply (r : Rule (Sig.cons F Ev) n) (us : Fin n → Option A.Msg) :
    Option (Option A.Msg) :=
  if h : ∃ θ μ, r.Matching θ μ us then some (r.rhs.eval h.choose h.choose_spec.choose) else none

theorem Rule.apply_eq_some {r : Rule (Sig.cons F Ev) n}
    (hfree : ∀ i, (r.args i).Free A.theory.withData) {us : Fin n → Option A.Msg}
    {θ : ℕ → A.Msg} {μ : ℕ → Option A.Msg} (h : r.Matching θ μ us) :
    r.apply us = some (r.rhs.eval θ μ) := by
  have h' : ∃ θ μ, r.Matching θ μ us := ⟨θ, μ, h⟩
  rw [Rule.apply, dif_pos h']
  exact congrArg some (Rule.Matching.eval_eq hfree h'.choose_spec.choose_spec h)

theorem Rule.apply_eq_none {r : Rule (Sig.cons F Ev) n} {us : Fin n → Option A.Msg}
    (h : ¬ ∃ θ μ, r.Matching θ μ us) : r.apply us = none := by
  rw [Rule.apply, dif_neg h]

/-- The destructor the rules of `g` define: the first rule with a matching decides, and
the result is `fail` when none has one. -/
def Model.dtorFun (g : Sig.withBuiltin G n) (us : Fin n → Option A.Msg) : Option A.Msg :=
  ((A.rules g).findSome? (·.apply us)).join

/-- Rules whose terms are over the free symbols rewrite to the value of the destructor they
define. -/
theorem rewrites_iff {rs : List (Rule (Sig.cons F Ev) n)}
    (hrs : ∀ r ∈ rs, ∀ i, (r.args i).Free A.theory.withData) {us : Fin n → Option A.Msg}
    {v : Option A.Msg} : Rewrites rs us v ↔ (rs.findSome? (·.apply us)).join = v := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | head hm => simp [Rule.apply_eq_some (hrs _ (List.mem_cons_self ..)) hm]
    | tail hn _ ih => simp [Rule.apply_eq_none hn, ih fun r hr => hrs r (List.mem_cons_of_mem _ hr)]
  · rintro rfl
    induction rs with
    | nil => exact .nil us
    | cons r rs ih =>
      by_cases h : ∃ θ μ, r.Matching θ μ us
      · obtain ⟨θ, μ, hm⟩ := h
        simpa [Rule.apply_eq_some (hrs _ (List.mem_cons_self ..)) hm] using
          Rewrites.head (rs := rs) hm
      · simpa [Rule.apply_eq_none h] using
          Rewrites.tail h (ih fun r hr => hrs r (List.mem_cons_of_mem _ hr))

/-- The rules of a destructor of the model rewrite to the value of the destructor's
function. -/
theorem Model.rewrites_iff (g : Sig.withBuiltin G n) {us : Fin n → Option A.Msg}
    {v : Option A.Msg} : Rewrites (A.rules g) us v ↔ A.dtorFun g us = v :=
  _root_.ProVerif.Specification.rewrites_iff fun _ hr i => A.rules_free g hr i

/-- A projection denotes the standard operation: the `i`-th component of a `k`-tuple. -/
theorem Model.dtorFun_proj (k : ℕ) (i : Fin k) (us : Fin 1 → Option A.Msg) :
    A.dtorFun (.inr (.proj k i)) us =
      liftFail (fun a => (StdOps.untuple k (a 0)).map (· i)) us := by
  have hrhs (θ : ℕ → A.Msg) (μ : ℕ → Option A.Msg) :
      (projRule (Sig.withEv F Ev) k i).rhs.eval θ μ = some (θ i) := rfl
  have harg (θ : ℕ → A.Msg) (μ : ℕ → Option A.Msg) :
      ((projRule (Sig.withEv F Ev) k i).args 0).eval θ μ =
        some (StdOps.tuple k fun j => θ j) := rfl
  have hfree := Builtin.rules_free A.theory (.proj k i) (List.mem_singleton.2 rfl)
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
      have hm : (projRule (Sig.withEv F Ev) k i).Matching
          (fun n => if h : n < k then a ⟨n, h⟩ else a i) (fun _ => none) us := fun j => by
        rw [Subsingleton.elim j 0, harg, h0]
        congr 2
        funext j
        simp
      rw [Rule.apply_eq_some hfree hm, hrhs, liftFail]
      rw [dif_pos fun j => by rw [Subsingleton.elim j 0, h0]; rfl]
      simp [h0, hu]

/-- The attacker of the model, `Attacker.ofDecls` from its public declarations: its
public constructors and free names, the functions of its public destructors, and the
standard operations. -/
instance Model.attacker (A : Model F G Ev) : Attacker A.Msg :=
  Attacker.ofDecls (fun n => Sum.inl '' A.pubFun n)
    (⋃ n, (fun g : G n => (⟨n, A.dtorFun (.inl g)⟩ :
      Σ n, (Fin n → Option A.Msg) → Option A.Msg)) '' A.pubDtor n)

/-- A public constructor applied to derivable messages is derivable; a data symbol is
public. -/
theorem Model.app_mem_derive {f : Sig.cons F Ev n} (hf : A.Public f) {S : Set A.Msg}
    {ms : Fin n → A.Msg} (hms : ∀ i, ms i ∈ Attacker.derive S) :
    Theory.Msg.app f ms ∈ Attacker.derive S := by
  have hS : ClosedUnder Attacker.ops (Attacker.derive S) := Attacker.derive.isClosed_closure S
  rcases f with (f | e) | d
  · exact Attacker.app_mem_derive
      (Attacker.ofDecls_mem (⟨f, hf, rfl⟩ : Sum.inl f ∈ Sum.inl '' A.pubFun n)) hms
  · exact hf.elim
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
  have hrw : Rewrites (A.rules g) us (some r) := (A.rewrites_iff g).2 h
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

/-- The attacker's deduction of the calculus is derivation in the trace semantics: the
public constructors and destructors, the standard operations among them, are the operations
of `Model.attacker`. -/
theorem Model.derives_iff_derive {S : Set A.Msg} {m : A.Msg} :
    A.Derives S m ↔ m ∈ Attacker.derive S := by
  constructor
  · intro h
    induction h with
    | mem hm => exact Attacker.derive.le_closure S hm
    | ctor f hf _ ih => exact A.app_mem_derive hf ih
    | dtor g hg _ hrw ih => exact A.dtorFun_mem_derive hg ih ((A.rewrites_iff g).1 hrw)
  · intro h
    refine Attacker.derive.closure_min (fun m hm => Model.Derives.mem hm) ?_ h
    show ClosedUnder Attacker.ops {m | A.Derives S m}
    rintro o ((ho | hd) | hs) args hargs r hr
    · obtain ⟨n, _, ⟨f, hf, rfl⟩, rfl⟩ := Set.mem_iUnion.1 ho
      dsimp only at hr
      obtain ⟨ms, hms, hr⟩ := liftFail_eq_some.1 hr
      obtain rfl := Option.some_injective _ hr
      exact Model.Derives.ctor _ hf fun i => hargs i _ (hms i)
    · obtain ⟨n, g, hg, rfl⟩ := Set.mem_iUnion.1 hd
      dsimp only at hr
      exact Model.Derives.dtor (.inl g) hg hargs ((A.rewrites_iff _).2 hr)
    · rcases hs with (⟨n, rfl⟩ | ⟨⟨k, i⟩, rfl⟩) | rfl | rfl <;> dsimp only at hr
      · obtain ⟨ms, hms, hr⟩ := liftFail_eq_some.1 hr
        obtain rfl := Option.some_injective _ hr
        rw [Set.mem_ofPred_eq, Theory.Msg.tuple_def]
        exact Model.Derives.ctor (.inr (.tuple n)) trivial fun i => hargs i _ (hms i)
      · exact Model.Derives.dtor (.inr (.proj k i)) trivial hargs
          ((A.rewrites_iff _).2 ((A.dtorFun_proj k i args).trans hr))
      · obtain rfl := Option.some_injective _ hr
        rw [Set.mem_ofPred_eq, Theory.Msg.tt_def]
        exact Model.Derives.ctor (.inr .tt) trivial fun i => i.elim0
      · obtain rfl := Option.some_injective _ hr
        rw [Set.mem_ofPred_eq, Theory.Msg.ff_def]
        exact Model.Derives.ctor (.inr .ff) trivial fun i => i.elim0

/-! ## Expressions -/

/-- Run the computations `cs 0, …, cs (k - 1)` in that order, collecting their results. -/
def seqFin {m : Type → Type} [Monad m] {α : Type} : {k : ℕ} → (Fin k → m α) → m (Fin k → α)
  | 0, _ => pure finZeroElim
  | _ + 1, cs => do
    let u ← cs 0
    let us ← seqFin fun i => cs i.succ
    pure (Fin.cons (α := fun _ => α) u us)

theorem seqFin_pure {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type} :
    ∀ {k : ℕ} (us : Fin k → α), seqFin (fun i => (pure (us i) : m α)) = pure us
  | 0, us => by
    rw [seqFin]
    exact congrArg pure (funext fun i => i.elim0)
  | k + 1, us => by
    show (pure (us 0) >>= fun u => seqFin (fun i => (pure (us i.succ) : m α)) >>=
      fun us' => pure (Fin.cons (α := fun _ => α) u us')) = pure us
    rw [pure_bind, seqFin_pure (fun i => us i.succ), pure_bind]
    exact congrArg pure (Fin.cons_self_tail us)

/-- A computation of the continuation monad run with a continuation, in the answer type
(`ContT.run` lands in `Id`). -/
abbrev Cont.runWith {r α : Type} (c : Cont r α) (κ : α → r) : r := c.run κ

theorem Cont.runWith_pure {r α : Type} (a : α) (κ : α → r) : Cont.runWith (pure a) κ = κ a := rfl

theorem Cont.runWith_bind {r α β : Type} (c : Cont r α) (f : α → Cont r β) (κ : β → r) :
    Cont.runWith (c >>= f) κ = Cont.runWith c fun a => Cont.runWith (f a) κ := rfl

theorem Proc.pure_inj {M α : Type} {u u' : α} (h : (pure u : Cont (Proc M) α) = pure u') :
    u = u' := by
  have := congrArg (fun c : Cont (Proc M) α => Cont.runWith c fun x => {t : Trace M | x = u}) h
  simp only [Cont.runWith_pure] at this
  exact ((Set.ext_iff.1 this []).1 trivial).symm

theorem update_succ {α : Type} {k : ℕ} (cs : Fin (k + 1) → α) (j : Fin k) (c : α) :
    (fun j' : Fin k => Function.update cs j.succ c j'.succ) =
      Function.update (fun j' => cs j'.succ) j c := funext fun j' => by
  by_cases h : j' = j
  · subst h
    simp
  · rw [Function.update_of_ne h, Function.update_of_ne fun h' => h (Fin.succ_injective _ h')]

/-- Running the computations with `c` at position `i`, those before `i` being `pure`, is
running `c` and then the computations with its result at position `i`. -/
theorem seqFin_run_update {r α : Type} :
    ∀ {k : ℕ} (cs : Fin k → Cont r α) (i : Fin k), (∀ j, j < i → ∃ u, cs j = pure u) →
      ∀ (c : Cont r α) (K : (Fin k → α) → r),
        Cont.runWith (seqFin (Function.update cs i c)) K =
          Cont.runWith c fun u => Cont.runWith (seqFin (Function.update cs i (pure u))) K
  | 0, _, i, _, _, _ => i.elim0
  | k + 1, cs, i, hv, c, K => by
    induction i using Fin.cases with
    | zero =>
      have ht : ∀ c', (fun j : Fin k => Function.update cs 0 c' j.succ) = fun j => cs j.succ :=
        fun c' => funext fun j => Function.update_of_ne (Fin.succ_ne_zero j) _ _
      show Cont.runWith (Function.update cs 0 c 0 >>= fun u =>
          seqFin (fun j => Function.update cs 0 c j.succ) >>=
            fun us => pure (Fin.cons (α := fun _ => α) u us)) K =
        Cont.runWith c fun u => Cont.runWith (Function.update cs 0 (pure u) 0 >>= fun u' =>
          seqFin (fun j => Function.update cs 0 (pure u) j.succ) >>=
            fun us => pure (Fin.cons (α := fun _ => α) u' us)) K
      simp only [Function.update_self, ht, Cont.runWith_bind, Cont.runWith_pure]
    | succ j =>
      obtain ⟨u₀, hu₀⟩ := hv 0 (Fin.succ_pos j)
      have h0 : ∀ c', Function.update cs j.succ c' 0 = pure u₀ := fun c' => by
        rw [Function.update_of_ne (Fin.succ_ne_zero j).symm, hu₀]
      show Cont.runWith (Function.update cs j.succ c 0 >>= fun u =>
          seqFin (fun j' => Function.update cs j.succ c j'.succ) >>=
            fun us => pure (Fin.cons (α := fun _ => α) u us)) K =
        Cont.runWith c fun u => Cont.runWith (Function.update cs j.succ (pure u) 0 >>= fun u' =>
          seqFin (fun j' => Function.update cs j.succ (pure u) j'.succ) >>=
            fun us => pure (Fin.cons (α := fun _ => α) u' us)) K
      simp only [h0, update_succ, Cont.runWith_bind, Cont.runWith_pure]
      exact seqFin_run_update (fun j' => cs j'.succ) j
        (fun j' hj' => hv j'.succ (Fin.succ_lt_succ_iff.2 hj')) c fun us => K (Fin.cons u₀ us)

/-- The message of the event `ev(M₁, …, Mₖ)` from the may-fail messages of its arguments:
`fail` when one of them is `fail`. -/
def eventMsg (e : Ev n) (us : Fin n → Option A.Msg) : Option A.Msg :=
  liftFail (fun ms => some (Theory.Msg.app (.inl (.inr e)) ms)) us

open Classical in
/-- The computation of an expression under `n` binders in the environment `xs`, with a
may-fail message as its result, `none` being `fail`: the arguments of a constructor, a
destructor or an event run from left to right, `new` is `Proc.fresh`, `event` is
`Proc.emit` of the event message, and `if` and `let` are case analyses on the result of
their first expression. -/
def Expr.denote : {n : ℕ} → Expr F G Ev n → (Fin n → A.Msg) → Cont (Proc A.Msg) (Option A.Msg)
  | _, .term M, xs => pure (some (M.realize (env xs)))
  | _, .ctor f args, xs => do
    let us ← seqFin fun i => (args i).denote xs
    pure (liftFail (fun ms => some (Theory.Msg.app f ms)) us)
  | _, .dtor g args, xs => do
    let us ← seqFin fun i => (args i).denote xs
    pure (A.dtorFun g us)
  | _, .fail, _ => pure none
  | _, .new D, xs => do
    let a ← Proc.fresh
    D.denote (Fin.snoc xs a)
  | _, .ite C D₁ D₂, xs => do
    match ← C.denote xs with
    | some c => if c = StdOps.tt then D₁.denote xs else D₂.denote xs
    | none => pure none
  | _, .let_ D D₁ D₂, xs => do
    match ← D.denote xs with
    | some a => D₁.denote (Fin.snoc xs a)
    | none => D₂.denote xs
  | _, .event e args D, xs => do
    let us ← seqFin fun i => (args i).denote xs
    match eventMsg e us with
    | some m =>
      Proc.emit m
      D.denote xs
    | none => pure none

/-- A may-fail term denotes `pure` of its value. -/
theorem Val.denote {V : Expr F G Ev 0} {u : Option A.Msg} (h : Val A V u) :
    V.denote finZeroElim = pure u := by
  induction h with
  | term M => rfl
  | @ctor k f args ms _ ih =>
    have hargs : (fun i => (args i).denote finZeroElim) = fun i => pure (some (ms i)) := funext ih
    simp only [Expr.denote]
    rw [hargs, seqFin_pure, pure_bind]
    exact congrArg pure
      ((liftFail_eq_some (f := fun ms => some (Theory.Msg.app f ms))).2 ⟨_, fun _ => rfl, rfl⟩)
  | fail => rfl

/-! ## Processes

The continuations of the expressions of a process: what the process does with the
may-fail messages they yield.  Where the manual's rules block on `fail`, they give
`Proc.nil`.
-/

/-- After the channel and the message of an output: the offer, then `P`. -/
def outK (P : Proc A.Msg) : Option A.Msg → Option A.Msg → Proc A.Msg
  | some c, some m => Proc.out c m P
  | _, _ => Proc.nil

/-- After the channel of an input: receive, then `P` on the message. -/
def inpK (P : A.Msg → Proc A.Msg) : Option A.Msg → Proc A.Msg
  | some c => Proc.inp c P
  | none => Proc.nil

/-- After the expression of `let`: `P` on the value, or `Q`. -/
def letK (P : A.Msg → Proc A.Msg) (Q : Proc A.Msg) : Option A.Msg → Proc A.Msg
  | some a => P a
  | none => Q

open Classical in
/-- After the condition of `if`: `P` on `true`, `Q` on another message. -/
def iteK (P Q : Proc A.Msg) : Option A.Msg → Proc A.Msg
  | some c => if c = StdOps.tt then P else Q
  | none => Proc.nil

/-- After the arguments of an event: the event, then `P`. -/
def eventK (e : Ev n) (P : Proc A.Msg) (us : Fin n → Option A.Msg) : Proc A.Msg :=
  match eventMsg e us with
  | some m => Proc.event m P
  | none => Proc.nil

/-- The process of the trace semantics that a process under `n` binders denotes in the
environment `xs`: the computations of its expressions run with the rest of the process as
the continuation. -/
def Process.denote : {n : ℕ} → Process F G Ev n → (Fin n → A.Msg) → Proc A.Msg
  | _, .nil, _ => Proc.nil
  | _, .out N M P, xs =>
    Cont.runWith (N.denote xs) fun c => Cont.runWith (M.denote xs) (outK (P.denote xs) c)
  | _, .inp N P, xs => Cont.runWith (N.denote xs) (inpK fun a => P.denote (Fin.snoc xs a))
  | _, .par P Q, xs => Proc.par (P.denote xs) (Q.denote xs)
  | _, .bang P, xs => Proc.bang (P.denote xs)
  | _, .new P, xs => Proc.new fun a => P.denote (Fin.snoc xs a)
  | _, .let_ D P Q, xs =>
    Cont.runWith (D.denote xs) (letK (fun a => P.denote (Fin.snoc xs a)) (Q.denote xs))
  | _, .ite C P Q, xs => Cont.runWith (C.denote xs) (iteK (P.denote xs) (Q.denote xs))
  | _, .event e args P, xs =>
    Cont.runWith (seqFin fun i => (args i).denote xs) (eventK e (P.denote xs))

/-! ## Substitution -/

theorem Expr.denote_subst :
    ∀ {n m : ℕ} (σ : Fin n → Tm F Ev m) (D : Expr F G Ev n) (xs : Fin m → A.Msg),
      (D.subst σ).denote xs = D.denote fun i => (σ i).realize (env xs)
  | _, _, σ, .term M, xs => by simp only [Expr.subst, Expr.denote, Tm.realize_subst]
  | _, _, σ, .ctor f args, xs => by
    simp only [Expr.subst, Expr.denote]
    congr 2
    funext i
    exact Expr.denote_subst σ (args i) xs
  | _, _, σ, .dtor g args, xs => by
    simp only [Expr.subst, Expr.denote]
    congr 2
    funext i
    exact Expr.denote_subst σ (args i) xs
  | _, _, _, .fail, _ => rfl
  | _, _, σ, .new D, xs => by
    simp only [Expr.subst, Expr.denote]
    congr 1
    funext a
    rw [Expr.denote_subst (liftSubst σ) D (Fin.snoc xs a)]
    congr 1
    funext i
    exact realize_liftSubst σ xs a i
  | _, _, σ, .ite C D₁ D₂, xs => by
    simp only [Expr.subst, Expr.denote]
    rw [Expr.denote_subst σ C xs, Expr.denote_subst σ D₁ xs, Expr.denote_subst σ D₂ xs]
  | _, _, σ, .let_ D D₁ D₂, xs => by
    simp only [Expr.subst, Expr.denote]
    rw [Expr.denote_subst σ D xs, Expr.denote_subst σ D₂ xs]
    congr 1
    funext u
    cases u with
    | none => rfl
    | some a =>
      show (D₁.subst (liftSubst σ)).denote (Fin.snoc xs a) = _
      rw [Expr.denote_subst (liftSubst σ) D₁ (Fin.snoc xs a)]
      congr 1
      funext i
      exact realize_liftSubst σ xs a i
  | _, _, σ, .event e args D, xs => by
    simp only [Expr.subst, Expr.denote]
    rw [Expr.denote_subst σ D xs]
    congr 2
    funext i
    exact Expr.denote_subst σ (args i) xs

/-- `D{M/x}` denotes what `D` denotes in the environment extended by `M`'s message. -/
theorem Expr.denote_inst (D : Expr F G Ev (n + 1)) (M : Tm F Ev n) (xs : Fin n → A.Msg) :
    (D.inst M).denote xs = D.denote (Fin.snoc xs (M.realize (env xs))) := by
  rw [Expr.inst, Expr.denote_subst]
  congr 1
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp

theorem Process.denote_subst :
    ∀ {n m : ℕ} (σ : Fin n → Tm F Ev m) (P : Process F G Ev n) (xs : Fin m → A.Msg),
      (P.subst σ).denote xs = P.denote fun i => (σ i).realize (env xs)
  | _, _, _, .nil, _ => rfl
  | _, _, σ, .out N M P, xs => by
    simp only [Process.subst, Process.denote, Expr.denote_subst, Process.denote_subst σ P xs]
  | _, _, σ, .inp N P, xs => by
    have h : (fun a => (P.subst (liftSubst σ)).denote (Fin.snoc xs a)) =
        fun a => P.denote (Fin.snoc (α := fun _ => A.Msg) (fun i => (σ i).realize (env xs)) a) :=
        funext fun a => by
      rw [Process.denote_subst (liftSubst σ) P (Fin.snoc xs a)]
      congr 1
      funext i
      exact realize_liftSubst σ xs a i
    simp only [Process.subst, Process.denote, Expr.denote_subst, h]
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
    simp only [Process.subst, Process.denote, Expr.denote_subst, Process.denote_subst σ Q xs, h]
  | _, _, σ, .ite C P Q, xs => by
    simp only [Process.subst, Process.denote, Expr.denote_subst, Process.denote_subst σ P xs,
      Process.denote_subst σ Q xs]
  | _, _, σ, .event e args P, xs => by
    simp only [Process.subst, Process.denote, Expr.denote_subst, Process.denote_subst σ P xs]

/-- `P{M/x}` denotes what `P` denotes in the environment extended by `M`'s message. -/
theorem Process.denote_inst (P : Process F G Ev (n + 1)) (M : Tm F Ev n) (xs : Fin n → A.Msg) :
    (P.inst M).denote xs = P.denote (Fin.snoc xs (M.realize (env xs))) := by
  rw [Process.inst, Process.denote_subst]
  congr 1
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp

end

end ProVerif.Specification
