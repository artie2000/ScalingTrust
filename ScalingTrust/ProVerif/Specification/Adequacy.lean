/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.Specification.Denotation
import ScalingTrust.ProVerif.Specification.Invariance

/-!
# Adequacy

The write-up's Theorem "Adequacy": a closed process denotes its weak traces
(`denote_eq_traces`), and the weak traces of a union of multisets are the parallel
composition of those of the parts (`traces_add`); and its Lemma "Expressions", the
adequacy of the computation of an expression (`TRuns.mem_run`, `TRuns.mem_run_val`,
`Expr.sound`).

* **Expressions.** A run of a term configuration is a trace of the computation of the
  expression with any continuation, and a run to a may-fail term followed by a trace of
  the continuation on its value is a trace of the computation (`TStep.mem_run` for one
  step, then by induction on the run).  Conversely a trace of the computation with a
  continuation is a run of the expression, followed by a trace of the continuation on
  the value reached if the run reaches one (`Expr.sound`, by induction on the
  expression under binders instantiated by closed terms, as for processes below).  The
  arguments of a constructor, a destructor or an event are the one case that is not
  structural: the auxiliary induction `seqFin_sound` is on the arguments left to
  evaluate, yielding a run of the arguments (`ArgRuns`), and `seqFin_run_update` of
  `Denotation` reads the computation of the argument being evaluated off the sequence.
* **Processes.** A process in a context `C`, a process with an expression in one term
  position, runs its expression first, by the context rule, then steps on the may-fail
  term reached (`Runs.ctx_split`, from `Step.singleton`, which inverts the step of one
  process by cases).  So `Runs.ctx_mem` and `Runs.ctx_of_mem` reduce the two directions
  of Adequacy for `out`, `in`, `let` and `if` to the expression lemmas and to the steps
  on may-fail terms (`Runs.out_values` and the like); `Runs.args_split`,
  `Runs.argCtx_mem` and `Runs.argCtx_of_mem` do the same for the arguments of `event`.
* The process part is proved for a process under binders instantiated by closed terms,
  by induction on the process: `denote_of_runs` reads the denotation off a run, and
  `runs_of_denote` builds a run from a trace of the denotation.  Instantiating the last
  variable after substituting for the others is, modulo `E`, substituting for all at
  once (`subst_inst_eqv`, `Expr.subst_inst_eqv`), which the invariance of runs under
  equality modulo `E` turns into an equality of runs.  Replication is the case that is
  not structural: a run of `!P` unfolds it finitely often, so it is a run of finitely
  many copies of `P` (`Runs.bang_unfold`, `Runs.of_replicate`), and a trace of
  `Proc.bang P` is a trace of finitely many copies in parallel (`mem_bang_iff`).
* **Effect-free expressions** reduce by `τ`-steps to a may-fail term, whose value is what
  their computation returns (`Expr.Pure.reduces`), the write-up's Lemma "Evaluation".
-/

namespace ProVerif.Specification

open FirstOrder FirstOrder.Language ProVerif.TraceSemantics

variable {F G Ev : Sig} {A : Model F G Ev} {n m k : ℕ}

/-! ## Terms of messages and substitution -/

theorem realize_var_eq : ∀ t : F.lang.Term ℕ, t.realize (M := TraceSemantics.Term F) Term.var = t
  | .var _ => rfl
  | .func f ts => by
    simp only [Term.realize_func, Term.funMap_eq]
    congr 1
    funext i
    exact realize_var_eq (ts i)

/-- Every message is the message of a closed term. -/
theorem msg_surjective (a : A.Msg) : ∃ M : Tm F Ev 0, Tm.msg A M = a := by
  induction a using Quotient.inductionOn with
  | h t =>
    refine ⟨t.relabel Sum.inl, ?_⟩
    show (t.relabel Sum.inl).realize (env finZeroElim) = ⟦t⟧
    rw [Term.realize_relabel,
      show env (A := A) finZeroElim ∘ Sum.inl = fun i => (⟦Term.var i⟧ : A.Msg) from rfl,
      Term.realize_quotient_mk', realize_var_eq]

theorem Tm.msg_subst (σ : Fin n → Tm F Ev 0) (N : Tm F Ev n) :
    Tm.msg A (Tm.subst σ N) = N.realize (env fun i => Tm.msg A (σ i)) :=
  Tm.realize_subst σ N finZeroElim

theorem Expr.denote_subst_msg (σ : Fin n → Tm F Ev 0) (D : Expr F G Ev n) :
    (D.subst σ).denote finZeroElim = D.denote fun i => Tm.msg A (σ i) :=
  Expr.denote_subst σ D finZeroElim

theorem msgs_snoc (σ : Fin n → Tm F Ev 0) (M : Tm F Ev 0) :
    (fun i => Tm.msg A (Fin.snoc (α := fun _ => Tm F Ev 0) σ M i)) =
      Fin.snoc (α := fun _ => A.Msg) (fun i => Tm.msg A (σ i)) (Tm.msg A M) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp

theorem term_subst_var {α : Type} : ∀ t : F.lang.Term α, t.subst Term.var = t
  | .var _ => rfl
  | .func f ts => by
    simp only [Term.subst]
    congr 1
    funext i
    exact term_subst_var (ts i)

theorem Tm.subst_var (M : Tm F Ev n) : Tm.subst (fun i => .var (.inr i)) M = M := by
  rw [Tm.subst, show (Sum.elim (fun k => (.var (.inl k) : Tm F Ev n)) fun i => .var (.inr i)) =
    Term.var from funext fun x => by cases x <;> rfl]
  exact term_subst_var M

theorem liftSubst_var :
    liftSubst (fun i => (.var (.inr i) : Tm F Ev n)) = fun i => .var (.inr i) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [liftSubst]
  | cast j => simp [liftSubst, Term.relabel]

theorem Expr.subst_var : ∀ {n : ℕ} (D : Expr F G Ev n), D.subst (fun i => .var (.inr i)) = D
  | _, .term M => by rw [Expr.subst, Tm.subst_var]
  | _, .ctor f args => by
    simp only [Expr.subst]
    congr 1
    funext i
    exact Expr.subst_var (args i)
  | _, .dtor g args => by
    simp only [Expr.subst]
    congr 1
    funext i
    exact Expr.subst_var (args i)
  | _, .fail => rfl
  | _, .new D => by rw [Expr.subst, liftSubst_var, Expr.subst_var D]
  | _, .ite C D₁ D₂ => by rw [Expr.subst, Expr.subst_var C, Expr.subst_var D₁, Expr.subst_var D₂]
  | _, .let_ D D₁ D₂ => by
    rw [Expr.subst, Expr.subst_var D, liftSubst_var, Expr.subst_var D₁, Expr.subst_var D₂]
  | _, .event e args D => by
    simp only [Expr.subst]
    rw [Expr.subst_var D]
    congr 1
    funext i
    exact Expr.subst_var (args i)

theorem finZero_eq_var : (finZeroElim : Fin 0 → Tm F Ev 0) = fun i => .var (.inr i) :=
  funext fun i => i.elim0

theorem Expr.subst_finZero (D : Expr F G Ev 0) : D.subst finZeroElim = D := by
  rw [finZero_eq_var]
  exact Expr.subst_var D

theorem Process.subst_var :
    ∀ {n : ℕ} (P : Process F G Ev n), P.subst (fun i => .var (.inr i)) = P
  | _, .nil => rfl
  | _, .out N M P => by rw [Process.subst, Expr.subst_var, Expr.subst_var, Process.subst_var P]
  | _, .inp N P => by rw [Process.subst, Expr.subst_var, liftSubst_var, Process.subst_var P]
  | _, .par P Q => by rw [Process.subst, Process.subst_var P, Process.subst_var Q]
  | _, .bang P => by rw [Process.subst, Process.subst_var P]
  | _, .new P => by rw [Process.subst, liftSubst_var, Process.subst_var P]
  | _, .let_ D P Q => by
    rw [Process.subst, Expr.subst_var, liftSubst_var, Process.subst_var P, Process.subst_var Q]
  | _, .ite C P Q => by
    rw [Process.subst, Expr.subst_var, Process.subst_var P, Process.subst_var Q]
  | _, .event e args P => by
    simp only [Process.subst]
    rw [Process.subst_var P]
    congr 1
    funext i
    exact Expr.subst_var (args i)

theorem Process.subst_finZero (P : Process F G Ev 0) : P.subst finZeroElim = P := by
  rw [finZero_eq_var]
  exact Process.subst_var P

/-- Substituting twice is, modulo `E`, substituting the composite. -/
theorem Tm.subst_subst_eqv (N : Tm F Ev n) {σ : Fin n → Tm F Ev m} {τ : Fin m → Tm F Ev k}
    {ρ : Fin n → Tm F Ev k} (h : ∀ i, Tm.Eqv A (Tm.subst τ (σ i)) (ρ i)) :
    Tm.Eqv A (Tm.subst τ (Tm.subst σ N)) (Tm.subst ρ N) := fun xs => by
  have hf : (fun i => (σ i).realize (env fun j => (τ j).realize (env xs))) =
      fun i => (ρ i).realize (env xs) := funext fun i => by rw [← h i xs, Tm.realize_subst]
  rw [Tm.realize_subst, Tm.realize_subst, Tm.realize_subst, hf]

theorem liftSubst_subst_eqv {σ : Fin n → Tm F Ev m} {τ : Fin m → Tm F Ev k}
    {ρ : Fin n → Tm F Ev k} (h : ∀ i, Tm.Eqv A (Tm.subst τ (σ i)) (ρ i)) (i : Fin (n + 1)) :
    Tm.Eqv A (Tm.subst (liftSubst τ) (liftSubst σ i)) (liftSubst ρ i) := fun xs => by
  obtain ⟨ys, a, rfl⟩ : ∃ ys a, xs = Fin.snoc ys a := ⟨_, _, (Fin.snoc_init_self xs).symm⟩
  have h1 : (fun j => (liftSubst τ j).realize (env (Fin.snoc ys a))) =
      Fin.snoc (α := fun _ => A.Msg) (fun j => (τ j).realize (env ys)) a :=
    funext fun j => realize_liftSubst τ ys a j
  have hf : (fun j => (σ j).realize (env fun j' => (τ j').realize (env ys))) =
      fun j => (ρ j).realize (env ys) := funext fun j => by rw [← h j ys, Tm.realize_subst]
  rw [Tm.realize_subst, h1, realize_liftSubst, realize_liftSubst, hf]

theorem Expr.subst_subst_eqv : ∀ {n m k : ℕ} (D : Expr F G Ev n) {σ : Fin n → Tm F Ev m}
    {τ : Fin m → Tm F Ev k} {ρ : Fin n → Tm F Ev k},
    (∀ i, Tm.Eqv A (Tm.subst τ (σ i)) (ρ i)) → Expr.Eqv A ((D.subst σ).subst τ) (D.subst ρ)
  | _, _, _, .term M, _, _, _, h => .term (Tm.subst_subst_eqv M h)
  | _, _, _, .ctor f args, _, _, _, h => .ctor f fun i => Expr.subst_subst_eqv (args i) h
  | _, _, _, .dtor g args, _, _, _, h => .dtor g fun i => Expr.subst_subst_eqv (args i) h
  | _, _, _, .fail, _, _, _, _ => .fail
  | _, _, _, .new D, _, _, _, h => .new (Expr.subst_subst_eqv D (liftSubst_subst_eqv h))
  | _, _, _, .ite C D₁ D₂, _, _, _, h =>
    .ite (Expr.subst_subst_eqv C h) (Expr.subst_subst_eqv D₁ h) (Expr.subst_subst_eqv D₂ h)
  | _, _, _, .let_ D D₁ D₂, _, _, _, h =>
    .let_ (Expr.subst_subst_eqv D h) (Expr.subst_subst_eqv D₁ (liftSubst_subst_eqv h))
      (Expr.subst_subst_eqv D₂ h)
  | _, _, _, .event e args D, _, _, _, h =>
    .event e (fun i => Expr.subst_subst_eqv (args i) h) (Expr.subst_subst_eqv D h)

theorem Process.subst_subst_eqv : ∀ {n m k : ℕ} (P : Process F G Ev n) {σ : Fin n → Tm F Ev m}
    {τ : Fin m → Tm F Ev k} {ρ : Fin n → Tm F Ev k},
    (∀ i, Tm.Eqv A (Tm.subst τ (σ i)) (ρ i)) → Process.Eqv A ((P.subst σ).subst τ) (P.subst ρ)
  | _, _, _, .nil, _, _, _, _ => .nil
  | _, _, _, .out N M P, _, _, _, h =>
    .out (Expr.subst_subst_eqv N h) (Expr.subst_subst_eqv M h) (Process.subst_subst_eqv P h)
  | _, _, _, .inp N P, _, _, _, h =>
    .inp (Expr.subst_subst_eqv N h) (Process.subst_subst_eqv P (liftSubst_subst_eqv h))
  | _, _, _, .par P Q, _, _, _, h =>
    .par (Process.subst_subst_eqv P h) (Process.subst_subst_eqv Q h)
  | _, _, _, .bang P, _, _, _, h => .bang (Process.subst_subst_eqv P h)
  | _, _, _, .new P, _, _, _, h => .new (Process.subst_subst_eqv P (liftSubst_subst_eqv h))
  | _, _, _, .let_ D P Q, _, _, _, h =>
    .let_ (Expr.subst_subst_eqv D h) (Process.subst_subst_eqv P (liftSubst_subst_eqv h))
      (Process.subst_subst_eqv Q h)
  | _, _, _, .ite C P Q, _, _, _, h =>
    .ite (Expr.subst_subst_eqv C h) (Process.subst_subst_eqv P h) (Process.subst_subst_eqv Q h)
  | _, _, _, .event e args P, _, _, _, h =>
    .event e (fun i => Expr.subst_subst_eqv (args i) h) (Process.subst_subst_eqv P h)

theorem liftSubst_inst_eqv (σ : Fin n → Tm F Ev 0) (M : Tm F Ev 0) (i : Fin (n + 1)) :
    Tm.Eqv A (Tm.subst (Fin.snoc (fun i => .var (.inr i)) M) (liftSubst σ i))
      (Fin.snoc (α := fun _ => Tm F Ev 0) σ M i) := by
  induction i using Fin.lastCases with
  | last =>
    intro xs
    simp only [liftSubst, Fin.snoc_last, Tm.subst, Term.subst, Sum.elim_inr]
  | cast j =>
    intro xs
    simp only [liftSubst, Fin.snoc_castSucc, Tm.realize_subst, Term.realize_relabel]
    congr 1
    funext x
    cases x <;> simp

/-- Instantiating the last variable after substituting for the others is, modulo `E`,
substituting for all at once. -/
theorem subst_inst_eqv (P : Process F G Ev (n + 1)) (σ : Fin n → Tm F Ev 0) (M : Tm F Ev 0) :
    Process.Eqv A ((P.subst (liftSubst σ)).inst M) (P.subst (Fin.snoc σ M)) :=
  Process.subst_subst_eqv P (liftSubst_inst_eqv σ M)

theorem Expr.subst_inst_eqv (D : Expr F G Ev (n + 1)) (σ : Fin n → Tm F Ev 0) (M : Tm F Ev 0) :
    Expr.Eqv A ((D.subst (liftSubst σ)).inst M) (D.subst (Fin.snoc σ M)) :=
  Expr.subst_subst_eqv D (liftSubst_inst_eqv σ M)

/-! ## Steps of a single process -/

/-- The step one process can make, by cases on it. -/
def StepOf (U : Finset ℕ) (l : Option (Act A.Msg)) (c' : Config F G Ev) :
    Process F G Ev 0 → Prop
  | .nil => l = none ∧ c' = ⟨U, 0⟩
  | .out N M P =>
    (∃ c m, Val A N (some c) ∧ Val A M (some m) ∧ l = some (.out c m) ∧ c' = ⟨U, {P}⟩) ∨
    (∃ U' N', TStep A U N l U' N' ∧ c' = ⟨U', {.out N' M P}⟩) ∨
    (N.IsValue ∧ ∃ U' M', TStep A U M l U' M' ∧ c' = ⟨U', {.out N M' P}⟩)
  | .inp N P =>
    (∃ c M, Val A N (some c) ∧ l = some (.inp c (Tm.msg A M)) ∧ c' = ⟨U, {P.inst M}⟩) ∨
    (∃ U' N', TStep A U N l U' N' ∧ c' = ⟨U', {.inp N' P}⟩)
  | .par P Q => l = none ∧ c' = ⟨U, P ::ₘ {Q}⟩
  | .bang P => l = none ∧ c' = ⟨U, P ::ₘ {.bang P}⟩
  | .new P => ∃ k, k ∉ U ∧ l = some (.new k) ∧ c' = ⟨insert k U, {P.inst (.var (.inl k))}⟩
  | .let_ D P Q =>
    (∃ m M', Val A D (some m) ∧ Tm.msg A M' = m ∧ l = none ∧ c' = ⟨U, {P.inst M'}⟩) ∨
    (D = .fail ∧ l = none ∧ c' = ⟨U, {Q}⟩) ∨
    (∃ U' D', TStep A U D l U' D' ∧ c' = ⟨U', {.let_ D' P Q}⟩)
  | .ite C P Q =>
    (Val A C (some StdOps.tt) ∧ l = none ∧ c' = ⟨U, {P}⟩) ∨
    (∃ m, Val A C (some m) ∧ m ≠ StdOps.tt ∧ l = none ∧ c' = ⟨U, {Q}⟩) ∨
    (∃ U' C', TStep A U C l U' C' ∧ c' = ⟨U', {.ite C' P Q}⟩)
  | .event e args P =>
    (∃ ms, (∀ i, Val A (args i) (some (ms i))) ∧
      l = some (.event (Theory.Msg.app (.inl (.inr e)) ms)) ∧ c' = ⟨U, {P}⟩) ∨
    (∃ i U' D', (∀ j, j < i → (args j).IsValue) ∧ TStep A U (args i) l U' D' ∧
      c' = ⟨U', {.event e (Function.update args i D') P}⟩)

theorem Step.singleton {c c' : Config F G Ev} {l : Option (Act A.Msg)} (h : Step A c l c')
    {U : Finset ℕ} {X : Process F G Ev 0} (hc : c = ⟨U, {X}⟩) : StepOf U l c' X := by
  cases h
  case comm =>
    obtain ⟨rfl, hX⟩ := Config.mk.inj hc
    exact absurd ((Multiset.singleton_eq_cons_iff _).1 hX.symm).2 Multiset.cons_ne_zero
  all_goals
    obtain ⟨rfl, hX⟩ := Config.mk.inj hc
    obtain ⟨rfl, rfl⟩ := (Multiset.singleton_eq_cons_iff _).1 hX.symm
    dsimp only [StepOf]
  case nil => exact ⟨rfl, rfl⟩
  case par => exact ⟨rfl, rfl⟩
  case bang => exact ⟨rfl, rfl⟩
  case new P k hk => exact ⟨k, hk, rfl, rfl⟩
  case eval₁ M' P Q hD hM' => exact Or.inl ⟨_, M', hD, hM', rfl, rfl⟩
  case eval₂ => exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  case cond₁ P Q hC => exact Or.inl ⟨hC, rfl, rfl⟩
  case cond₂ P Q hC hm => exact Or.inr (Or.inl ⟨_, hC, hm, rfl, rfl⟩)
  case event e P hargs => exact Or.inl ⟨_, hargs, rfl, rfl⟩
  case out P hN hM => exact Or.inl ⟨_, _, hN, hM, rfl, rfl⟩
  case inp P M c hN => exact Or.inl ⟨c, M, hN, rfl, rfl⟩
  case out_ctx₁ hs => exact Or.inr (Or.inl ⟨_, _, hs, rfl⟩)
  case out_ctx₂ hN hs => exact Or.inr (Or.inr ⟨hN, _, _, hs, rfl⟩)
  case inp_ctx hs => exact Or.inr ⟨_, _, hs, rfl⟩
  case ite_ctx hs => exact Or.inr (Or.inr ⟨_, _, hs, rfl⟩)
  case let_ctx hs => exact Or.inr (Or.inr ⟨_, _, hs, rfl⟩)
  case event_ctx hv hs => exact Or.inr ⟨_, _, _, hv, hs, rfl⟩

theorem Step.zero {c c' : Config F G Ev} {l : Option (Act A.Msg)} (h : Step A c l c')
    {U : Finset ℕ} (hc : c = ⟨U, 0⟩) : False := by
  cases h <;> exact Multiset.cons_ne_zero (Config.mk.inj hc).2

theorem Runs.zero {c : Config F G Ev} {t : Trace A.Msg} (h : Runs A c t) {U : Finset ℕ}
    (hc : c = ⟨U, 0⟩) : t = [] := by
  cases h with
  | nil => rfl
  | tau hs => exact (hs.zero hc).elim
  | act hs => exact (hs.zero hc).elim

/-- A step of some processes is a step of them beside others. -/
theorem Step.frame {U U' : Finset ℕ} {Ps Ps' : Multiset (Process F G Ev 0)}
    {l : Option (Act A.Msg)} (h : Step A ⟨U, Ps⟩ l ⟨U', Ps'⟩) (Qs : Multiset (Process F G Ev 0)) :
    Step A ⟨U, Ps + Qs⟩ l ⟨U', Ps' + Qs⟩ := by
  rcases h.names_eq with ⟨k, rfl, hk, rfl⟩ | ⟨hl, rfl⟩
  · simpa [Finset.insert_union] using h.add Qs (U₁ := U) fun k' hk' => by
      obtain rfl := Act.new.inj (Option.some.inj hk')
      exact hk
  · simpa using h.add Qs (U₁ := U) fun k hk => (hl k hk).elim

/-- A run is a run beside idle processes. -/
theorem Runs.add_right {c : Config F G Ev} {t : Trace A.Msg} (h : Runs A c t)
    (Qs : Multiset (Process F G Ev 0)) : Runs A ⟨c.names, c.procs + Qs⟩ t := by
  induction h with
  | nil c => exact .nil _
  | @tau c c' t hs _ ih =>
    obtain ⟨U, Ps⟩ := c
    obtain ⟨U', Ps'⟩ := c'
    exact .tau (hs.frame Qs) ih
  | @act c c' a t hs _ ih =>
    obtain ⟨U, Ps⟩ := c
    obtain ⟨U', Ps'⟩ := c'
    exact .act (hs.frame Qs) ih

/-! ## Replication -/

/-- A run beside `!P` unfolds it finitely often, so is a run beside that many copies
of `P`. -/
theorem Runs.bang_unfold {c : Config F G Ev} {t : Trace A.Msg} (h : Runs A c t)
    {P : Process F G Ev 0} : ∀ {U : Finset ℕ} {Ps : Multiset (Process F G Ev 0)},
      c = ⟨U, Ps + {.bang P}⟩ → ∃ n, Runs A ⟨U, Ps + Multiset.replicate n P⟩ t := by
  induction h with
  | nil c =>
    rintro U Ps rfl
    exact ⟨0, .nil _⟩
  | tau hs _ ih =>
    rintro U Ps rfl
    rcases hs.add_cases rfl with ⟨U', Ps', hs', rfl⟩ | ⟨U', Qs', hs', rfl⟩ |
      ⟨_, _, _, _, h, -⟩ | ⟨_, _, _, _, h, -⟩
    · obtain ⟨n, hn⟩ := ih rfl
      exact ⟨n, .tau (hs'.frame _) hn⟩
    · obtain ⟨-, h⟩ := Step.singleton hs' rfl
      obtain ⟨rfl, rfl⟩ := Config.mk.inj h
      obtain ⟨n, hn⟩ := ih (by rw [add_cons', Multiset.cons_add])
      refine ⟨n + 1, ?_⟩
      rwa [Multiset.replicate_succ, add_cons', ← Multiset.cons_add]
    · cases h
    · cases h
  | act hs _ ih =>
    rintro U Ps rfl
    rcases hs.add_cases rfl with ⟨U', Ps', hs', rfl⟩ | ⟨U', Qs', hs', rfl⟩ |
      ⟨_, _, _, _, -, -, -, hs'⟩ | ⟨_, _, _, _, -, -, -, hs'⟩
    · obtain ⟨n, hn⟩ := ih rfl
      exact ⟨n, .act (hs'.frame _) hn⟩
    · obtain ⟨h, -⟩ := Step.singleton hs' rfl
      cases h
    · obtain ⟨h, -⟩ := Step.singleton hs' rfl
      cases h
    · obtain ⟨h, -⟩ := Step.singleton hs' rfl
      cases h

/-- A run of finitely many copies of `P` is a run of `!P`. -/
theorem Runs.of_replicate {U : Finset ℕ} {P : Process F G Ev 0} {t : Trace A.Msg} :
    ∀ {n : ℕ}, Runs A ⟨U, Multiset.replicate n P⟩ t → Runs A ⟨U, {.bang P}⟩ t := by
  suffices h : ∀ n, Runs A ⟨U, Multiset.replicate n P + {.bang P}⟩ t →
      Runs A ⟨U, {.bang P}⟩ t from fun {n} hn => h n (hn.add_right _)
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro h
    have hs : Step A ⟨U, Multiset.replicate n P + {.bang P}⟩ none
        ⟨U, Multiset.replicate n P + (P ::ₘ {.bang P})⟩ := by
      have := (Step.bang P (A := A) (U := U) (Ps := 0)).add_left (Multiset.replicate n P)
        (U₀ := U) fun _ h => nomatch h
      rwa [Finset.union_self] at this
    refine ih (.tau hs ?_)
    rwa [Multiset.replicate_succ, Multiset.cons_add, ← add_cons'] at h

/-- `n` copies of a process in parallel. -/
def iterPar {M : Type} : ℕ → Proc M → Proc M
  | 0, _ => Proc.nil
  | n + 1, P => Proc.par P (iterPar n P)

theorem Proc.par_mono {M : Type} {P P' Q Q' : Proc M} (hP : P ⊆ P') (hQ : Q ⊆ Q') :
    Proc.par P Q ⊆ Proc.par P' Q' := by
  rintro t ⟨⟨f, s, hf, hs, hc⟩, hn⟩
  refine ⟨⟨f, s, fun i => ?_, hs, hc⟩, hn⟩
  fin_cases i
  · exact hP (hf 0)
  · exact hQ (hf 1)

theorem iterPar_subset_bang {M : Type} {P : Proc M} (hP : [] ∈ P) :
    ∀ n, iterPar n P ⊆ Proc.bang P
  | 0 => fun t ht => by
    obtain rfl := Set.mem_singleton_iff.1 ht
    exact ⟨⟨fun _ => [], [], fun _ => hP, fun _ => rfl, .nil⟩, List.nodup_nil⟩
  | n + 1 => by
    rw [Proc.bang_eq]
    exact Proc.par_mono subset_rfl (iterPar_subset_bang hP n)

theorem mem_iterPar_of_merge {M : Type} {P : Proc M} :
    ∀ (n : ℕ) {f : ℕ → Trace M} {s : TaggedTrace ℕ M} {t : Trace M}, (∀ i, f i ∈ P) →
      s.Interleaves f → s.Comms t → t.nonces.Nodup → (∀ p ∈ s, p.1 < n) → t ∈ iterPar n P
  | 0, f, s, t, _, _, hc, _, hlt => by
    obtain rfl : s = [] := List.eq_nil_iff_forall_not_mem.2 fun p hp => Nat.not_lt_zero _ (hlt p hp)
    cases hc
    rfl
  | n + 1, f, s, t, hf, hs, hc, hn, hlt => by
    obtain ⟨t', s₂, h1, h2, h3, h4⟩ := hc.split
    have hn' : t'.nonces.Nodup := by
      rw [h1.nonces]
      rw [hc.nonces] at hn
      exact hn.sublist (Trace.nonces_sublist s.dec_sublist)
    refine ⟨⟨![f 0, t'], s₂, Fin.forall_fin_two.2 ⟨hf 0, mem_iterPar_of_merge n (f := f ∘ Nat.succ)
      (fun i => hf _) (fun i => (s.proj_dec i).trans (hs (i + 1))) h1 hn' fun p hp => ?_⟩,
      Fin.forall_fin_two.2 ⟨h3.trans (hs 0), h4⟩, h2⟩, hn⟩
    obtain ⟨⟨_ | i, a⟩, hq, hpq⟩ := List.mem_filterMap.1 hp
    · cases hpq
    · obtain rfl := Option.some.inj hpq
      exact Nat.lt_of_succ_lt_succ (hlt _ hq)

/-- A trace of `!P` is a trace of finitely many copies of `P` in parallel. -/
theorem mem_bang_iff {M : Type} {P : Proc M} (hP : [] ∈ P) {t : Trace M} :
    t ∈ Proc.bang P ↔ ∃ n, t ∈ iterPar n P := by
  refine ⟨fun ⟨⟨f, s, hf, hs, hc⟩, hn⟩ => ?_, fun ⟨n, hn⟩ => iterPar_subset_bang hP n hn⟩
  have : ∀ s : TaggedTrace ℕ M, ∃ n, ∀ p ∈ s, p.1 < n := fun s => by
    induction s with
    | nil => exact ⟨0, fun _ h => (List.not_mem_nil h).elim⟩
    | cons p s ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨max (p.1 + 1) n, fun q hq => ?_⟩
      rcases List.mem_cons.1 hq with rfl | hq
      · exact lt_max_of_lt_left (Nat.lt_succ_self _)
      · exact lt_max_of_lt_right (hn q hq)
  obtain ⟨n, hlt⟩ := this s
  exact ⟨n, mem_iterPar_of_merge n hf hs hc hn hlt⟩

/-! ## Expressions: the empty trace -/

theorem nil_mem_seqFin_run : ∀ {k : ℕ} {cs : Fin k → Cont (Proc A.Msg) (Option A.Msg)},
    (∀ i (κ : Option A.Msg → Proc A.Msg), (∀ u, [] ∈ κ u) → [] ∈ Cont.runWith (cs i) κ) →
    ∀ {K : (Fin k → Option A.Msg) → Proc A.Msg}, (∀ us, [] ∈ K us) →
      [] ∈ Cont.runWith (seqFin cs) K
  | 0, _, _, K, hK => by
    rw [seqFin]
    exact hK _
  | k + 1, cs, hcs, K, hK => by
    rw [seqFin]
    simp only [Cont.runWith_bind, Cont.runWith_pure]
    exact hcs 0 _ fun u => nil_mem_seqFin_run (fun i => hcs i.succ) fun us => hK _

open Classical in
/-- The computation of an expression may stop at once. -/
theorem nil_mem_run : ∀ {n : ℕ} (D : Expr F G Ev n) (xs : Fin n → A.Msg)
    {κ : Option A.Msg → Proc A.Msg}, (∀ u, [] ∈ κ u) → [] ∈ Cont.runWith (D.denote xs) κ
  | _, .term M, xs, κ, hκ => hκ _
  | _, .ctor f args, xs, κ, hκ => by
    simp only [Expr.denote, Cont.runWith_bind, Cont.runWith_pure]
    exact nil_mem_seqFin_run (fun i κ' hκ' => nil_mem_run (args i) xs hκ') fun us => hκ _
  | _, .dtor g args, xs, κ, hκ => by
    simp only [Expr.denote, Cont.runWith_bind, Cont.runWith_pure]
    exact nil_mem_seqFin_run (fun i κ' hκ' => nil_mem_run (args i) xs hκ') fun us => hκ _
  | _, .fail, _, κ, hκ => hκ _
  | _, .new D, xs, κ, hκ => by
    show [] ∈ Proc.new fun a => Cont.runWith (D.denote (Fin.snoc xs a)) κ
    exact Set.mem_iUnion.2 ⟨0, Set.mem_insert _ _⟩
  | _, .ite C D₁ D₂, xs, κ, hκ => by
    simp only [Expr.denote, Cont.runWith_bind]
    refine nil_mem_run C xs fun u => ?_
    cases u with
    | none => exact hκ _
    | some c =>
      show [] ∈ Cont.runWith (if c = StdOps.tt then D₁.denote xs else D₂.denote xs) κ
      split_ifs
      · exact nil_mem_run D₁ xs hκ
      · exact nil_mem_run D₂ xs hκ
  | _, .let_ D D₁ D₂, xs, κ, hκ => by
    simp only [Expr.denote, Cont.runWith_bind]
    refine nil_mem_run D xs fun u => ?_
    cases u with
    | none => exact nil_mem_run D₂ xs hκ
    | some a => exact nil_mem_run D₁ (Fin.snoc xs a) hκ
  | _, .event e args D, xs, κ, hκ => by
    simp only [Expr.denote, Cont.runWith_bind]
    refine nil_mem_seqFin_run (fun i κ' hκ' => nil_mem_run (args i) xs hκ') fun us => ?_
    rcases hm : eventMsg e us with _ | m <;> dsimp only
    · exact hκ _
    · exact Set.mem_insert _ _

/-! ## Expressions: runs are traces of the computation -/

theorem denote_update {k : ℕ} (args : Fin k → Expr F G Ev n) (i : Fin k) (D : Expr F G Ev n)
    (xs : Fin n → A.Msg) :
    (fun j => (Function.update args i D j).denote xs) =
      Function.update (fun j => (args j).denote xs) i (D.denote xs) := funext fun j => by
  by_cases h : j = i
  · subst h
    simp
  · simp [Function.update_of_ne h]

/-- The computations of arguments with `D` at position `i`, those before `i` being may-fail
terms: `D` runs first, and the rest with its result. -/
theorem seqFin_run_args {k : ℕ} {args : Fin k → Expr F G Ev 0} {i : Fin k}
    (hv : ∀ j, j < i → (args j).IsValue) (D : Expr F G Ev 0)
    (K : (Fin k → Option A.Msg) → Proc A.Msg) :
    Cont.runWith (seqFin fun j => (Function.update args i D j).denote finZeroElim) K =
      Cont.runWith (D.denote finZeroElim) fun u =>
        Cont.runWith (seqFin (Function.update (fun j => (args j).denote finZeroElim) i (pure u)))
          K := by
  rw [denote_update]
  exact seqFin_run_update _ i (fun j hj => let ⟨u, hu⟩ := (hv j hj).val; ⟨u, Val.denote hu⟩)
    (D.denote finZeroElim) K

theorem seqFin_run_args_self {k : ℕ} {args : Fin k → Expr F G Ev 0} {i : Fin k}
    (hv : ∀ j, j < i → (args j).IsValue) (K : (Fin k → Option A.Msg) → Proc A.Msg) :
    Cont.runWith (seqFin fun j => (args j).denote finZeroElim) K =
      Cont.runWith ((args i).denote finZeroElim) fun u =>
        Cont.runWith (seqFin (Function.update (fun j => (args j).denote finZeroElim) i (pure u)))
          K := by
  have := seqFin_run_args hv (args i) K
  rwa [Function.update_eq_self] at this

/-- The computations of may-fail terms are `pure` of their values. -/
theorem denote_values {k : ℕ} {Vs : Fin k → Expr F G Ev 0} {us : Fin k → Option A.Msg}
    (hV : ∀ i, Val A (Vs i) (us i)) :
    (fun i => (Vs i).denote finZeroElim) = fun i => pure (us i) :=
  funext fun i => Val.denote (hV i)

theorem liftFail_app_eq_some (f : Sig.cons F Ev k) {us : Fin k → Option A.Msg}
    {ms : Fin k → A.Msg} (h : ∀ i, us i = some (ms i)) :
    liftFail (fun ms => some (Theory.Msg.app f ms)) us = some (Theory.Msg.app f ms) :=
  liftFail_eq_some.2 ⟨ms, h, rfl⟩

theorem eventMsg_eq_some {e : Ev k} {us : Fin k → Option A.Msg} {ms : Fin k → A.Msg}
    (h : ∀ i, us i = some (ms i)) :
    eventMsg (A := A) e us = some (Theory.Msg.app (.inl (.inr e)) ms) :=
  liftFail_eq_some.2 ⟨ms, h, rfl⟩

theorem eventMsg_eq_none {e : Ev k} {us : Fin k → Option A.Msg} {i : Fin k} (h : us i = none) :
    eventMsg (A := A) e us = none := by
  rw [eventMsg, liftFail, dif_neg]
  intro h'
  simpa [h] using h' i

/-- A step of a term configuration, then a trace of the computation reached, is a trace
of the computation. -/
theorem TStep.mem_run {U U' : Finset ℕ} {D D' : Expr F G Ev 0} {l : Option (Act A.Msg)}
    (h : TStep A U D l U' D') : ∀ {κ : Option A.Msg → Proc A.Msg} {t : Trace A.Msg},
      t ∈ Cont.runWith (D'.denote finZeroElim) κ → (∀ k, l = some (.new k) → k ∉ t.nonces) →
      l.toList ++ t ∈ Cont.runWith (D.denote finZeroElim) κ := by
  induction h with
  | @ctor_fail k f args i hv hi =>
    intro κ t ht _
    choose us hus using fun j => (hv j).val
    have hi' : us i = none := (hus i).eq (by rw [hi]; exact .fail)
    show t ∈ Cont.runWith ((Expr.ctor f args).denote finZeroElim) κ
    simp only [Expr.denote]
    rw [denote_values hus, seqFin_pure]
    simp only [Cont.runWith_bind, Cont.runWith_pure]
    rw [liftFail, dif_neg fun h => by simpa [hi'] using h i]
    exact ht
  | @dtor k g args us M hargs hr =>
    intro κ t ht _
    show t ∈ Cont.runWith ((Expr.dtor g args).denote finZeroElim) κ
    simp only [Expr.denote]
    rw [denote_values hargs, seqFin_pure]
    simp only [Cont.runWith_bind, Cont.runWith_pure]
    rw [show A.dtorFun g us = some (Tm.msg A M) from (A.rewrites_iff g).1 hr]
    exact ht
  | @dtor_fail k g args us hargs hr =>
    intro κ t ht _
    show t ∈ Cont.runWith ((Expr.dtor g args).denote finZeroElim) κ
    simp only [Expr.denote]
    rw [denote_values hargs, seqFin_pure]
    simp only [Cont.runWith_bind, Cont.runWith_pure]
    rw [show A.dtorFun g us = none from (A.rewrites_iff g).1 hr]
    exact ht
  | @new D k hk =>
    intro κ t ht hfr
    rw [Expr.denote_inst] at ht
    show Act.new k :: t ∈ Proc.new fun a => Cont.runWith (D.denote (Fin.snoc finZeroElim a)) κ
    exact Set.mem_iUnion.2 ⟨k, Or.inr ⟨t, ⟨ht, hfr k rfl⟩, rfl⟩⟩
  | @ite₁ C D₁ D₂ hC =>
    intro κ t ht _
    show t ∈ Cont.runWith ((Expr.ite C D₁ D₂).denote finZeroElim) κ
    simp only [Expr.denote, Cont.runWith_bind, Val.denote hC, Cont.runWith_pure, if_true]
    exact ht
  | @ite₂ C m D₁ D₂ hC hm =>
    intro κ t ht _
    show t ∈ Cont.runWith ((Expr.ite C D₁ D₂).denote finZeroElim) κ
    simp only [Expr.denote, Cont.runWith_bind, Val.denote hC, Cont.runWith_pure]
    split_ifs with h
    · exact absurd h hm
    · exact ht
  | @ite_fail D₁ D₂ =>
    intro κ t ht _
    exact ht
  | @let₁ D m M' D₁ D₂ hD hM' =>
    intro κ t ht _
    rw [Expr.denote_inst] at ht
    show t ∈ Cont.runWith ((Expr.let_ D D₁ D₂).denote finZeroElim) κ
    simp only [Expr.denote, Cont.runWith_bind, Val.denote hD, Cont.runWith_pure]
    rw [show M'.realize (env finZeroElim) = m from hM'] at ht
    exact ht
  | @let₂ D₁ D₂ =>
    intro κ t ht _
    exact ht
  | @event k e args ms D hargs =>
    intro κ t ht _
    show Act.event (Theory.Msg.app (.inl (.inr e)) ms) :: t ∈
      Cont.runWith ((Expr.event e args D).denote finZeroElim) κ
    simp only [Expr.denote, Cont.runWith_bind]
    rw [denote_values hargs, seqFin_pure]
    simp only [Cont.runWith_pure, eventMsg_eq_some fun _ => rfl]
    exact Or.inr ⟨t, ht, rfl⟩
  | @event_fail k e args i D hv hi =>
    intro κ t ht _
    choose us hus using fun j => (hv j).val
    have hi' : us i = none := (hus i).eq (by rw [hi]; exact .fail)
    show t ∈ Cont.runWith ((Expr.event e args D).denote finZeroElim) κ
    simp only [Expr.denote, Cont.runWith_bind]
    rw [denote_values hus, seqFin_pure]
    simp only [Cont.runWith_pure, eventMsg_eq_none hi']
    exact ht
  | @ctor_ctx U' l k f args i D' hv hs ih =>
    intro κ t ht hfr
    simp only [Expr.denote, Cont.runWith_bind, Cont.runWith_pure] at ht ⊢
    rw [seqFin_run_args hv] at ht
    rw [seqFin_run_args_self hv]
    exact ih ht hfr
  | @dtor_ctx U' l k g args i D' hv hs ih =>
    intro κ t ht hfr
    simp only [Expr.denote, Cont.runWith_bind, Cont.runWith_pure] at ht ⊢
    rw [seqFin_run_args hv] at ht
    rw [seqFin_run_args_self hv]
    exact ih ht hfr
  | @ite_ctx U' l C C' D₁ D₂ hs ih =>
    intro κ t ht hfr
    simp only [Expr.denote, Cont.runWith_bind] at ht ⊢
    exact ih ht hfr
  | @let_ctx U' l D D' D₁ D₂ hs ih =>
    intro κ t ht hfr
    simp only [Expr.denote, Cont.runWith_bind] at ht ⊢
    exact ih ht hfr
  | @event_ctx U' l k e args i D' D hv hs ih =>
    intro κ t ht hfr
    simp only [Expr.denote, Cont.runWith_bind] at ht ⊢
    rw [seqFin_run_args hv] at ht
    rw [seqFin_run_args_self hv]
    exact ih ht hfr

/-- A run of a term configuration is a trace of the computation with any continuation
that may stop at once. -/
theorem TRuns.mem_run {U U' : Finset ℕ} {D D' : Expr F G Ev 0} {t : Trace A.Msg}
    (h : TRuns A U D t U' D') {κ : Option A.Msg → Proc A.Msg} (hκ : ∀ u, [] ∈ κ u) :
    t ∈ Cont.runWith (D.denote finZeroElim) κ := by
  induction h with
  | nil U D => exact nil_mem_run D finZeroElim hκ
  | tau hs _ ih => exact hs.mem_run ih fun _ h => nomatch h
  | @act U D U₁ D₁ a t U₂ D₂ hs hr ih =>
    refine hs.mem_run ih fun k hk hmem => ?_
    obtain rfl := Option.some.inj hk
    rcases hs.names_eq with ⟨k', hk', -, rfl⟩ | ⟨hl, -⟩
    · obtain rfl := Act.new.inj (Option.some.inj hk')
      exact hr.fresh k hmem (Finset.mem_insert_self k U)
    · exact hl k rfl

/-- A run of a term configuration to a may-fail term, then a trace of the continuation on
its value, is a trace of the computation. -/
theorem TRuns.mem_run_val {U U' : Finset ℕ} {D V : Expr F G Ev 0} {t : Trace A.Msg}
    (h : TRuns A U D t U' V) : ∀ {u : Option A.Msg} {κ : Option A.Msg → Proc A.Msg}
      {t₂ : Trace A.Msg}, Val A V u → t₂ ∈ κ u → (∀ k ∈ t₂.nonces, k ∉ U') →
      t ++ t₂ ∈ Cont.runWith (D.denote finZeroElim) κ := by
  induction h with
  | nil U D =>
    intro u κ t₂ hV ht₂ _
    rw [Val.denote hV, Cont.runWith_pure]
    exact ht₂
  | tau hs _ ih =>
    intro u κ t₂ hV ht₂ hfr
    exact hs.mem_run (ih hV ht₂ hfr) fun _ h => nomatch h
  | @act U D U₁ D₁ a t U₂ D₂ hs hr ih =>
    intro u κ t₂ hV ht₂ hfr
    refine hs.mem_run (ih hV ht₂ hfr) fun k hk hmem => ?_
    obtain rfl := Option.some.inj hk
    rcases hs.names_eq with ⟨k', hk', -, rfl⟩ | ⟨hl, -⟩
    · obtain rfl := Act.new.inj (Option.some.inj hk')
      have hmem' : k ∈ Trace.nonces (t ++ t₂) := hmem
      rw [Trace.nonces_append] at hmem'
      rcases List.mem_append.1 hmem' with h | h
      · exact hr.fresh k h (Finset.mem_insert_self k U)
      · exact hfr k h (hr.subset (Finset.mem_insert_self k U))
    · exact hl k rfl

/-- A run of the arguments is a trace of their computations in order, with any
continuation that may stop at once. -/
theorem ArgRuns.mem_run {U U' : Finset ℕ} {args args' : Fin k → Expr F G Ev 0} {t : Trace A.Msg}
    (h : ArgRuns A U args t U' args') {K : (Fin k → Option A.Msg) → Proc A.Msg}
    (hK : ∀ us, [] ∈ K us) : t ∈ Cont.runWith (seqFin fun i => (args i).denote finZeroElim) K := by
  induction h with
  | nil U args => exact nil_mem_seqFin_run (fun i κ hκ => nil_mem_run (args i) finZeroElim hκ) hK
  | tau i hv hs _ ih =>
    rw [seqFin_run_args hv] at ih
    rw [seqFin_run_args_self hv]
    exact hs.mem_run ih fun _ h => nomatch h
  | @act U args i U₁ D₁ a t U₂ args₂ hv hs hr ih =>
    rw [seqFin_run_args hv] at ih
    rw [seqFin_run_args_self hv]
    refine hs.mem_run ih fun k hk hmem => ?_
    obtain rfl := Option.some.inj hk
    rcases hs.names_eq with ⟨k', hk', -, rfl⟩ | ⟨hl, -⟩
    · obtain rfl := Act.new.inj (Option.some.inj hk')
      exact hr.fresh k hmem (Finset.mem_insert_self k U)
    · exact hl k rfl

/-- A run of the arguments to may-fail terms, then a trace of the continuation on their
values, is a trace of their computations in order. -/
theorem ArgRuns.mem_run_val {U U' : Finset ℕ} {args Vs : Fin k → Expr F G Ev 0} {t : Trace A.Msg}
    (h : ArgRuns A U args t U' Vs) : ∀ {us : Fin k → Option A.Msg}
      {K : (Fin k → Option A.Msg) → Proc A.Msg} {t₂ : Trace A.Msg},
      (∀ i, Val A (Vs i) (us i)) → t₂ ∈ K us → (∀ k ∈ t₂.nonces, k ∉ U') →
      t ++ t₂ ∈ Cont.runWith (seqFin fun i => (args i).denote finZeroElim) K := by
  induction h with
  | nil U args =>
    intro us K t₂ hV ht₂ _
    rw [denote_values hV, seqFin_pure, Cont.runWith_pure]
    exact ht₂
  | tau i hv hs _ ih =>
    intro us K t₂ hV ht₂ hfr
    have := ih hV ht₂ hfr
    rw [seqFin_run_args hv] at this
    rw [seqFin_run_args_self hv]
    exact hs.mem_run this fun _ h => nomatch h
  | @act U args i U₁ D₁ a t U₂ args₂ hv hs hr ih =>
    intro us K t₂ hV ht₂ hfr
    have := ih hV ht₂ hfr
    rw [seqFin_run_args hv] at this
    rw [seqFin_run_args_self hv]
    refine hs.mem_run this fun k hk hmem => ?_
    obtain rfl := Option.some.inj hk
    rcases hs.names_eq with ⟨k', hk', -, rfl⟩ | ⟨hl, -⟩
    · obtain rfl := Act.new.inj (Option.some.inj hk')
      have hmem' : k ∈ Trace.nonces (t ++ t₂) := hmem
      rw [Trace.nonces_append] at hmem'
      rcases List.mem_append.1 hmem' with h | h
      · exact hr.fresh k h (Finset.mem_insert_self k U)
      · exact hfr k h (hr.subset (Finset.mem_insert_self k U))
    · exact hl k rfl

/-! ## Expressions: traces of the computation are runs -/

/-- The traces of the computation of a closed expression with a continuation decompose as
its runs: a run of the expression, then, if a may-fail term is reached, a trace of the
continuation on its value, whose created names are fresh. -/
def Expr.Sound (A : Model F G Ev) (D : Expr F G Ev 0) : Prop :=
  ∀ (κ : Option A.Msg → Proc A.Msg) (U : Finset ℕ) (t : Trace A.Msg),
    t ∈ Cont.runWith (D.denote finZeroElim) κ → (∀ k ∈ t.nonces, k ∉ U) →
    ∃ t₁ t₂ U' D', t = t₁ ++ t₂ ∧ TRuns A U D t₁ U' D' ∧ (∀ k ∈ t₂.nonces, k ∉ U') ∧
      (t₂ = [] ∨ ∃ u, Val A D' u ∧ t₂ ∈ κ u)

theorem Expr.IsValue.sound {V : Expr F G Ev 0} (hV : V.IsValue) : Expr.Sound A V := by
  intro κ U t ht hU
  obtain ⟨u, hu⟩ := hV.val
  rw [Val.denote hu, Cont.runWith_pure] at ht
  exact ⟨[], t, U, V, rfl, .nil _ _, hU, Or.inr ⟨u, hu, ht⟩⟩

/-- The traces of the computations of the arguments, run in order, the first `i` being
may-fail terms: the auxiliary induction of `Expr.sound`, on the arguments left to
evaluate. -/
theorem seqFin_sound {K : (Fin k → Option A.Msg) → Proc A.Msg} :
    ∀ (r i : ℕ), i + r = k → ∀ (args : Fin k → Expr F G Ev 0),
      (∀ j : Fin k, (j : ℕ) < i → (args j).IsValue) → (∀ j, Expr.Sound A (args j)) →
      ∀ {U : Finset ℕ} {t : Trace A.Msg},
        t ∈ Cont.runWith (seqFin fun j => (args j).denote finZeroElim) K →
        (∀ k ∈ t.nonces, k ∉ U) →
        ∃ t₁ t₂ U' args', t = t₁ ++ t₂ ∧ ArgRuns A U args t₁ U' args' ∧
          (∀ k ∈ t₂.nonces, k ∉ U') ∧
          (t₂ = [] ∨ ∃ us, (∀ j, Val A (args' j) (us j)) ∧ t₂ ∈ K us)
  | 0, i, hi, args, hv, _, U, t, ht, hU => by
    have hval : ∀ j, (args j).IsValue := fun j => hv j (by omega)
    choose us hus using fun j => (hval j).val
    rw [denote_values hus, seqFin_pure, Cont.runWith_pure] at ht
    exact ⟨[], t, U, args, rfl, .nil _ _, hU, Or.inr ⟨us, hus, ht⟩⟩
  | r + 1, i, hi, args, hv, hs, U, t, ht, hU => by
    have hik : i < k := by omega
    have hv' : ∀ j, j < (⟨i, hik⟩ : Fin k) → (args j).IsValue := fun j hj => hv j hj
    rw [seqFin_run_args_self hv'] at ht
    obtain ⟨t₁, t₂, U₁, D', rfl, h₁, hfr, h₂⟩ := hs ⟨i, hik⟩ _ _ _ ht hU
    have h₁' : ArgRuns A U args t₁ U₁ (Function.update args ⟨i, hik⟩ D') := h₁.argRuns hv' rfl
    rcases h₂ with rfl | ⟨u, hu, ht₂⟩
    · exact ⟨t₁, [], U₁, Function.update args ⟨i, hik⟩ D', rfl, h₁', hfr, Or.inl rfl⟩
    · have hargs' : ∀ j : Fin k, (j : ℕ) < i + 1 → (Function.update args ⟨i, hik⟩ D' j).IsValue :=
        fun j hj => by
          by_cases h : j = ⟨i, hik⟩
          · subst h
            rw [Function.update_self]
            exact hu.isValue
          · have : (j : ℕ) ≠ i := fun h' => h (Fin.ext h')
            rw [Function.update_of_ne h]
            exact hv j (by omega)
      have hs' : ∀ j, Expr.Sound A (Function.update args ⟨i, hik⟩ D' j) := fun j => by
        by_cases h : j = ⟨i, hik⟩
        · subst h
          rw [Function.update_self]
          exact hu.isValue.sound
        · rw [Function.update_of_ne h]
          exact hs j
      have ht₂' : t₂ ∈ Cont.runWith (seqFin fun j =>
          (Function.update args ⟨i, hik⟩ D' j).denote finZeroElim) K := by
        rw [denote_update, Val.denote hu]
        exact ht₂
      obtain ⟨t₃, t₄, U₂, args'', rfl, h₃, hfr', h₄⟩ :=
        seqFin_sound r (i + 1) (by omega) _ hargs' hs' ht₂' hfr
      exact ⟨t₁ ++ t₃, t₄, U₂, args'', (List.append_assoc _ _ _).symm, h₁'.append h₃, hfr', h₄⟩

theorem TRuns.tau_end {U : Finset ℕ} {D D' D'' : Expr F G Ev 0} {t : Trace A.Msg} {U' : Finset ℕ}
    (h : TRuns A U D t U' D') (hs : TStep A U' D' none U' D'') : TRuns A U D t U' D'' := by
  have := h.append (.tau hs (.nil _ _))
  rwa [List.append_nil] at this

/-! ### The `k`-ary contexts -/

theorem isArgCtx_ctor (f : Sig.cons F Ev k) : TStep.IsArgCtx A (Expr.ctor f) :=
  fun hv hs => .ctor_ctx f _ hv hs

theorem isArgCtx_dtor (g : Sig.withBuiltin G k) : TStep.IsArgCtx A (Expr.dtor g) :=
  fun hv hs => .dtor_ctx g _ hv hs

theorem isArgCtx_event (e : Ev k) (D : Expr F G Ev 0) :
    TStep.IsArgCtx A fun args => .event e args D :=
  fun hv hs => .event_ctx e _ D hv hs

theorem Step.isArgCtx_event (e : Ev k) (P : Process F G Ev 0) :
    Step.IsArgCtx A fun args => .event e args P :=
  fun hv hs => Step.event_ctx (Ps := 0) e _ P hv hs

/-- The may-fail terms `Vs` reached by the arguments: either all are terms, and the
constructor applied to them is a term with the application of their messages as its value,
or one is `fail`. -/
theorem Val.ctor_or_fail {Vs : Fin k → Expr F G Ev 0} {us : Fin k → Option A.Msg}
    (hV : ∀ i, Val A (Vs i) (us i)) (f : Sig.cons F Ev k) :
    (∃ ms, (∀ i, us i = some (ms i)) ∧ Val A (.ctor f Vs) (some (Theory.Msg.app f ms))) ∨
      ∃ i, us i = none ∧ Vs i = .fail := by
  by_cases hall : ∀ i, (us i).isSome
  · refine Or.inl ⟨fun i => (us i).get (hall i), fun i => (Option.some_get (hall i)).symm,
      .ctor f fun i => ?_⟩
    have := hV i
    rwa [← Option.some_get (hall i)] at this
  · obtain ⟨i, hi⟩ := not_forall.1 hall
    have hi' : us i = none := Option.not_isSome_iff_eq_none.1 hi
    exact Or.inr ⟨i, hi', (hV i).eq_fail hi'⟩

/-- A trace of the computation of an expression, instantiated by closed terms, with a
continuation is a run of the expression, then a trace of the continuation on the may-fail
term reached. -/
theorem Expr.sound : ∀ {n : ℕ} (D : Expr F G Ev n) (σ : Fin n → Tm F Ev 0), Expr.Sound A (D.subst σ)
  | _, .term M, σ => Expr.IsValue.sound (V := (Expr.term M).subst σ) (Or.inl (.term _))
  | _, .fail, σ => Expr.IsValue.sound (V := Expr.fail.subst σ) (Or.inr rfl)
  | _, @Expr.ctor _ _ _ _ k f args, σ => by
    intro κ U t ht hU
    simp only [Expr.subst, Expr.denote, Cont.runWith_bind, Cont.runWith_pure] at ht
    obtain ⟨t₁, t₂, U', args', rfl, h₁, hfr, h₂⟩ := seqFin_sound (A := A) _ 0 (Nat.zero_add _) _
      (fun j hj => absurd hj (Nat.not_lt_zero _)) (fun j => Expr.sound (args j) σ) ht hU
    have h₁' := h₁.lift (isArgCtx_ctor f)
    rcases h₂ with rfl | ⟨us, hus, ht₂⟩
    · exact ⟨t₁, [], U', .ctor f args', rfl, h₁', hfr, Or.inl rfl⟩
    rcases Val.ctor_or_fail hus f with ⟨ms, hms, hV⟩ | ⟨i, hi, hfail⟩
    · refine ⟨t₁, t₂, U', .ctor f args', rfl, h₁', hfr, Or.inr ⟨_, hV, ?_⟩⟩
      rwa [liftFail_app_eq_some f hms] at ht₂
    · refine ⟨t₁, t₂, U', .fail, rfl,
        h₁'.tau_end (.ctor_fail f i (fun j => (hus j).isValue) hfail), hfr,
        Or.inr ⟨none, .fail, ?_⟩⟩
      rwa [liftFail, dif_neg fun h => by simpa [hi] using h i] at ht₂
  | _, @Expr.dtor _ _ _ _ k g args, σ => by
    intro κ U t ht hU
    simp only [Expr.subst, Expr.denote, Cont.runWith_bind, Cont.runWith_pure] at ht
    obtain ⟨t₁, t₂, U', args', rfl, h₁, hfr, h₂⟩ := seqFin_sound (A := A) _ 0 (Nat.zero_add _) _
      (fun j hj => absurd hj (Nat.not_lt_zero _)) (fun j => Expr.sound (args j) σ) ht hU
    have h₁' := h₁.lift (isArgCtx_dtor g)
    rcases h₂ with rfl | ⟨us, hus, ht₂⟩
    · exact ⟨t₁, [], U', .dtor g args', rfl, h₁', hfr, Or.inl rfl⟩
    generalize hv : A.dtorFun g us = v at ht₂
    cases v with
    | none =>
      exact ⟨t₁, t₂, U', .fail, rfl, h₁'.tau_end (.dtor_fail g hus ((A.rewrites_iff g).2 hv)), hfr,
        Or.inr ⟨none, .fail, ht₂⟩⟩
    | some m =>
      obtain ⟨M, rfl⟩ := msg_surjective m
      exact ⟨t₁, t₂, U', .term M, rfl, h₁'.tau_end (.dtor g M hus ((A.rewrites_iff g).2 hv)), hfr,
        Or.inr ⟨_, .term M, ht₂⟩⟩
  | _, .new D, σ => by
    intro κ U t ht hU
    simp only [Expr.subst] at ht ⊢
    have hnew : t ∈ Proc.new fun a =>
        Cont.runWith ((D.subst (liftSubst σ)).denote (Fin.snoc finZeroElim a)) κ := ht
    obtain ⟨k, hnew⟩ := Set.mem_iUnion.1 hnew
    rcases hnew with rfl | ⟨t', ⟨hin, hk⟩, rfl⟩
    · exact ⟨[], [], U, _, rfl, .nil _ _, hU, Or.inl rfl⟩
    have hkU : k ∉ U := hU k (by simp [Trace.nonces])
    have hU' : ∀ k' ∈ Trace.nonces t', k' ∉ insert k U := fun k' hk' h => by
      rcases Finset.mem_insert.1 h with rfl | h
      · exact hk hk'
      · exact hU k' (by simp [Trace.nonces, hk']) h
    have ht'' : t' ∈ Cont.runWith ((D.subst (Fin.snoc σ (.var (.inl k)))).denote finZeroElim) κ := by
      rw [Expr.denote_subst_msg, msgs_snoc]
      dsimp only at hin
      rw [Expr.denote_subst] at hin
      have : (fun i => (liftSubst σ i).realize (env (Fin.snoc finZeroElim (Names.nonce k)))) =
          Fin.snoc (α := fun _ => A.Msg) (fun i => Tm.msg A (σ i)) (Tm.msg A (.var (.inl k))) :=
        funext fun i => realize_liftSubst σ finZeroElim (Names.nonce k) i
      rw [this] at hin
      exact hin
    obtain ⟨t₁, t₂, U', D', rfl, h₁, hfr, h₂⟩ :=
      Expr.sound D (Fin.snoc σ (.var (.inl k))) _ _ _ ht'' hU'
    obtain ⟨E', h₁', hE'⟩ := h₁.eqv (Expr.subst_inst_eqv D σ (.var (.inl k))).symm
    refine ⟨Act.new k :: t₁, t₂, U', E', rfl, .act (.new _ k hkU) h₁', hfr, ?_⟩
    rcases h₂ with rfl | ⟨u, hu, ht₂⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨u, hE'.val hu, ht₂⟩
  | _, .ite C D₁ D₂, σ => by
    intro κ U t ht hU
    simp only [Expr.subst, Expr.denote, Cont.runWith_bind] at ht
    simp only [Expr.subst]
    obtain ⟨t₁, t₂, U₁, C', rfl, h₁, hfr, h₂⟩ := Expr.sound C σ _ _ _ ht hU
    have h₁' := h₁.lift (TStep.ite_ctx (A := A) (D₁.subst σ) (D₂.subst σ) : TStep.IsCtx A _)
    rcases h₂ with rfl | ⟨u, hu, ht₂⟩
    · exact ⟨t₁, [], U₁, _, rfl, h₁', hfr, Or.inl rfl⟩
    cases u with
    | none =>
      obtain rfl := hu.eq_fail rfl
      exact ⟨t₁, t₂, U₁, .fail, rfl, h₁'.tau_end (.ite_fail _ _), hfr, Or.inr ⟨none, .fail, ht₂⟩⟩
    | some c =>
      dsimp only at ht₂
      split_ifs at ht₂ with hc
      · subst hc
        obtain ⟨t₃, t₄, U₂, D', rfl, h₃, hfr', h₄⟩ := Expr.sound D₁ σ _ _ _ ht₂ hfr
        exact ⟨t₁ ++ t₃, t₄, U₂, D', (List.append_assoc _ _ _).symm,
          h₁'.append (.tau (.ite₁ _ _ hu) h₃), hfr', h₄⟩
      · obtain ⟨t₃, t₄, U₂, D', rfl, h₃, hfr', h₄⟩ := Expr.sound D₂ σ _ _ _ ht₂ hfr
        exact ⟨t₁ ++ t₃, t₄, U₂, D', (List.append_assoc _ _ _).symm,
          h₁'.append (.tau (.ite₂ _ _ hu hc) h₃), hfr', h₄⟩
  | _, .let_ D D₁ D₂, σ => by
    intro κ U t ht hU
    simp only [Expr.subst, Expr.denote, Cont.runWith_bind] at ht
    simp only [Expr.subst]
    obtain ⟨t₁, t₂, U₁, D', rfl, h₁, hfr, h₂⟩ := Expr.sound D σ _ _ _ ht hU
    have h₁' := h₁.lift (TStep.let_ctx (A := A) (D₁.subst (liftSubst σ)) (D₂.subst σ) :
      TStep.IsCtx A _)
    rcases h₂ with rfl | ⟨u, hu, ht₂⟩
    · exact ⟨t₁, [], U₁, _, rfl, h₁', hfr, Or.inl rfl⟩
    cases u with
    | none =>
      obtain rfl := hu.eq_fail rfl
      obtain ⟨t₃, t₄, U₂, D'', rfl, h₃, hfr', h₄⟩ := Expr.sound D₂ σ _ _ _ ht₂ hfr
      exact ⟨t₁ ++ t₃, t₄, U₂, D'', (List.append_assoc _ _ _).symm,
        h₁'.append (.tau (.let₂ _ _) h₃), hfr', h₄⟩
    | some a =>
      obtain ⟨M, rfl⟩ := msg_surjective a
      have ht₂' : t₂ ∈ Cont.runWith ((D₁.subst (Fin.snoc σ M)).denote finZeroElim) κ := by
        rw [Expr.denote_subst_msg, msgs_snoc]
        dsimp only at ht₂
        rw [Expr.denote_subst] at ht₂
        have : (fun i => (liftSubst σ i).realize (env (Fin.snoc finZeroElim (Tm.msg A M)))) =
            Fin.snoc (α := fun _ => A.Msg) (fun i => Tm.msg A (σ i)) (Tm.msg A M) :=
          funext fun i => realize_liftSubst σ finZeroElim (Tm.msg A M) i
        rw [this] at ht₂
        exact ht₂
      obtain ⟨t₃, t₄, U₂, D'', rfl, h₃, hfr', h₄⟩ := Expr.sound D₁ (Fin.snoc σ M) _ _ _ ht₂' hfr
      obtain ⟨E', h₃', hE'⟩ := h₃.eqv (Expr.subst_inst_eqv D₁ σ M).symm
      refine ⟨t₁ ++ t₃, t₄, U₂, E', (List.append_assoc _ _ _).symm,
        h₁'.append (.tau (.let₁ M _ _ hu rfl) h₃'), hfr', ?_⟩
      rcases h₄ with rfl | ⟨u, hu, ht₄⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨u, hE'.val hu, ht₄⟩
  | _, @Expr.event _ _ _ _ k e args D, σ => by
    intro κ U t ht hU
    simp only [Expr.subst, Expr.denote, Cont.runWith_bind] at ht
    simp only [Expr.subst]
    obtain ⟨t₁, t₂, U₁, args', rfl, h₁, hfr, h₂⟩ := seqFin_sound (A := A) _ 0 (Nat.zero_add _) _
      (fun j hj => absurd hj (Nat.not_lt_zero _)) (fun j => Expr.sound (args j) σ) ht hU
    have h₁' := h₁.lift (isArgCtx_event e (D.subst σ))
    rcases h₂ with rfl | ⟨us, hus, ht₂⟩
    · exact ⟨t₁, [], U₁, _, rfl, h₁', hfr, Or.inl rfl⟩
    rcases Val.ctor_or_fail hus (.inl (.inr e)) with ⟨ms, hms, -⟩ | ⟨i, hi, hfail⟩
    · have hms' : ∀ j, Val A (args' j) (some (ms j)) := fun j => by rw [← hms j]; exact hus j
      rw [eventMsg_eq_some hms] at ht₂
      change t₂ ∈ Proc.event (Theory.Msg.app (.inl (.inr e)) ms)
        (Cont.runWith ((D.subst σ).denote finZeroElim) κ) at ht₂
      rcases ht₂ with rfl | ⟨t₃, ht₃, rfl⟩
      · exact ⟨t₁, [], U₁, _, rfl, h₁', hfr, Or.inl rfl⟩
      obtain ⟨t₄, t₅, U₂, D', rfl, h₃, hfr', h₄⟩ :=
        Expr.sound D σ _ _ _ ht₃ (by simpa [Trace.nonces] using hfr)
      exact ⟨t₁ ++ Act.event (Theory.Msg.app (.inl (.inr e)) ms) :: t₄, t₅, U₂, D',
        (List.append_assoc t₁ (Act.event _ :: t₄) t₅).symm,
        h₁'.append (.act (.event e _ hms') h₃), hfr', h₄⟩
    · rw [eventMsg_eq_none hi] at ht₂
      exact ⟨t₁, t₂, U₁, .fail, rfl,
        h₁'.tau_end (.event_fail e i _ (fun j => (hus j).isValue) hfail), hfr,
        Or.inr ⟨none, .fail, ht₂⟩⟩

/-! ## Effect-free expressions -/

/-- Arguments that each reduce by `τ`-steps reduce in order. -/
theorem args_reduce {U : Finset ℕ} {args Vs : Fin k → Expr F G Ev 0} {us : Fin k → Option A.Msg}
    (hr : ∀ i, TRuns A U (args i) [] U (Vs i)) (hV : ∀ i, Val A (Vs i) (us i)) :
    ArgRuns A U args [] U Vs := by
  suffices h : ∀ i : ℕ, i ≤ k →
      ArgRuns A U args [] U fun j : Fin k => if (j : ℕ) < i then Vs j else args j by
    have := h k le_rfl
    simpa only [Fin.is_lt, if_true] using this
  intro i
  induction i with
  | zero => exact fun _ => by simpa using ArgRuns.nil U args
  | succ i ih =>
    intro hi
    have hik : i < k := hi
    have hv : ∀ j, j < (⟨i, hik⟩ : Fin k) →
        ((fun j : Fin k => if (j : ℕ) < i then Vs j else args j) j).IsValue := fun j hj => by
      simp only [show (j : ℕ) < i from hj, if_true]
      exact (hV j).isValue
    have h2 : Function.update (fun j : Fin k => if (j : ℕ) < i then Vs j else args j) ⟨i, hik⟩
        (Vs ⟨i, hik⟩) = fun j : Fin k => if (j : ℕ) < i + 1 then Vs j else args j :=
      funext fun j => by
        by_cases h : j = ⟨i, hik⟩
        · subst h
          simp
        · have : (j : ℕ) ≠ i := fun h' => h (Fin.ext h')
          rw [Function.update_of_ne h]
          by_cases hj : (j : ℕ) < i
          · simp [hj, Nat.lt_succ_of_lt hj]
          · simp [hj, show ¬ (j : ℕ) < i + 1 by omega]
    have := (hr ⟨i, hik⟩).argRuns hv (by simp)
    rw [h2] at this
    exact (ih (Nat.le_of_succ_le hi)).append this

/-- An effect-free expression, instantiated by closed terms, reduces by `τ`-steps to a
may-fail term, whose value its computation returns. -/
theorem Expr.Pure.reduces_subst : ∀ {n : ℕ} {D : Expr F G Ev n}, D.Pure →
    ∀ (σ : Fin n → Tm F Ev 0) (U : Finset ℕ), ∃ V u, TRuns A U (D.subst σ) [] U V ∧ Val A V u ∧
      (D.subst σ).denote finZeroElim = pure u
  | _, .term M, _, σ, U => ⟨_, _, .nil _ _, .term _, rfl⟩
  | _, .fail, _, σ, U => ⟨_, _, .nil _ _, .fail, rfl⟩
  | _, @Expr.ctor _ _ _ _ k f args, h, σ, U => by
    have hargs : ∀ i, ∃ V u, TRuns A U ((args i).subst σ) [] U V ∧ Val A V u ∧
        ((args i).subst σ).denote finZeroElim = pure u :=
      fun i => Expr.Pure.reduces_subst (h i) σ U
    choose Vs us hr hV hd using hargs
    have hd' : (fun i => ((args i).subst σ).denote finZeroElim) = fun i => pure (us i) := funext hd
    have hr' := (args_reduce hr hV).lift (isArgCtx_ctor f)
    rcases Val.ctor_or_fail hV f with ⟨ms, hms, hV'⟩ | ⟨i, hi, hfail⟩
    · refine ⟨_, _, hr', hV', ?_⟩
      simp only [Expr.subst, Expr.denote]
      rw [hd', seqFin_pure, pure_bind, liftFail_app_eq_some f hms]
    · refine ⟨.fail, none, hr'.tau_end (.ctor_fail f i (fun j => (hV j).isValue) hfail), .fail, ?_⟩
      simp only [Expr.subst, Expr.denote]
      rw [hd', seqFin_pure, pure_bind, liftFail, dif_neg fun h => by simpa [hi] using h i]
  | _, @Expr.dtor _ _ _ _ k g args, h, σ, U => by
    have hargs : ∀ i, ∃ V u, TRuns A U ((args i).subst σ) [] U V ∧ Val A V u ∧
        ((args i).subst σ).denote finZeroElim = pure u :=
      fun i => Expr.Pure.reduces_subst (h i) σ U
    choose Vs us hr hV hd using hargs
    have hd' : (fun i => ((args i).subst σ).denote finZeroElim) = fun i => pure (us i) := funext hd
    have hr' := (args_reduce hr hV).lift (isArgCtx_dtor g)
    rcases hv : A.dtorFun g us with _ | m
    · refine ⟨.fail, none, hr'.tau_end (.dtor_fail g hV ((A.rewrites_iff g).2 hv)), .fail, ?_⟩
      simp only [Expr.subst, Expr.denote]
      rw [hd', seqFin_pure, pure_bind, hv]
    · obtain ⟨M, rfl⟩ := msg_surjective m
      refine ⟨.term M, _, hr'.tau_end (.dtor g M hV ((A.rewrites_iff g).2 hv)), .term M, ?_⟩
      simp only [Expr.subst, Expr.denote]
      rw [hd', seqFin_pure, pure_bind, hv]

/-- An effect-free closed expression reduces by `τ`-steps to a may-fail term, whose value
its computation returns. -/
theorem Expr.Pure.reduces {D : Expr F G Ev 0} (h : D.Pure) (U : Finset ℕ) :
    ∃ V u, TRuns A U D [] U V ∧ Val A V u ∧ D.denote finZeroElim = pure u := by
  have := Expr.Pure.reduces_subst (A := A) h finZeroElim U
  rwa [Expr.subst_finZero] at this

/-! ## Processes in a context -/

/-- A context of processes whose steps from an expression that is not a may-fail term are
the term steps of the expression. -/
def Step.CtxInv (A : Model F G Ev) (C : Expr F G Ev 0 → Process F G Ev 0) : Prop :=
  ∀ {U : Finset ℕ} {l : Option (Act A.Msg)} {c' : Config F G Ev} {D : Expr F G Ev 0},
    ¬ D.IsValue → Step A ⟨U, {C D}⟩ l c' → ∃ U' D', TStep A U D l U' D' ∧ c' = ⟨U', {C D'}⟩

/-- A run of a process in a context is a run of its expression, then a run of the process
on the may-fail term reached, if one is. -/
theorem Runs.ctx_split {C : Expr F G Ev 0 → Process F G Ev 0} (hC : Step.CtxInv A C)
    {c : Config F G Ev} {t : Trace A.Msg} (h : Runs A c t) :
    ∀ {U : Finset ℕ} {D : Expr F G Ev 0}, c = ⟨U, {C D}⟩ →
      ∃ t₁ t₂ U' D', t = t₁ ++ t₂ ∧ TRuns A U D t₁ U' D' ∧ Runs A ⟨U', {C D'}⟩ t₂ ∧
        (t₂ = [] ∨ D'.IsValue) := by
  induction h with
  | nil c =>
    rintro U D rfl
    exact ⟨[], [], U, D, rfl, .nil _ _, .nil _, Or.inl rfl⟩
  | @tau c c' t hs hr ih =>
    rintro U D rfl
    by_cases hD : D.IsValue
    · exact ⟨[], t, U, D, rfl, .nil _ _, .tau hs hr, Or.inr hD⟩
    · obtain ⟨U₁, D₁, hs', rfl⟩ := hC hD hs
      obtain ⟨t₁, t₂, U', D', rfl, h₁, h₂, h₃⟩ := ih rfl
      exact ⟨t₁, t₂, U', D', rfl, .tau hs' h₁, h₂, h₃⟩
  | @act c c' a t hs hr ih =>
    rintro U D rfl
    by_cases hD : D.IsValue
    · exact ⟨[], a :: t, U, D, rfl, .nil _ _, .act hs hr, Or.inr hD⟩
    · obtain ⟨U₁, D₁, hs', rfl⟩ := hC hD hs
      obtain ⟨t₁, t₂, U', D', rfl, h₁, h₂, h₃⟩ := ih rfl
      exact ⟨a :: t₁, t₂, U', D', rfl, .act hs' h₁, h₂, h₃⟩

/-- A run of a process in a context is a trace of the computation of its expression with
the process as the continuation, if the runs of the process on may-fail terms are its
traces. -/
theorem Runs.ctx_mem {C : Expr F G Ev 0 → Process F G Ev 0} (hC : Step.CtxInv A C)
    {κ : Option A.Msg → Proc A.Msg} (hκ : ∀ u, [] ∈ κ u)
    (hval : ∀ {U' : Finset ℕ} {V : Expr F G Ev 0} {u : Option A.Msg} {t₂ : Trace A.Msg},
      Val A V u → Runs A ⟨U', {C V}⟩ t₂ → t₂ ∈ κ u)
    {U : Finset ℕ} {D : Expr F G Ev 0} {t : Trace A.Msg} (h : Runs A ⟨U, {C D}⟩ t) :
    t ∈ Cont.runWith (D.denote finZeroElim) κ := by
  obtain ⟨t₁, t₂, U', D', rfl, h₁, h₂, h₃⟩ := h.ctx_split hC rfl
  rcases h₃ with rfl | hD'
  · rw [List.append_nil]
    exact h₁.mem_run hκ
  · obtain ⟨u, hu⟩ := hD'.val
    exact h₁.mem_run_val hu (hval hu h₂) (Runs.nonces h₂).2

/-- A trace of the computation of an expression with a process as the continuation is a
run of the process in the context, if the traces of the process on may-fail terms are its
runs. -/
theorem Runs.ctx_of_mem {C : Expr F G Ev 0 → Process F G Ev 0} (hC : Step.IsCtx A C)
    {κ : Option A.Msg → Proc A.Msg}
    (hval : ∀ {U' : Finset ℕ} {V : Expr F G Ev 0} {u : Option A.Msg} {t₂ : Trace A.Msg},
      Val A V u → t₂ ∈ κ u → (∀ k ∈ t₂.nonces, k ∉ U') → Runs A ⟨U', {C V}⟩ t₂)
    {U : Finset ℕ} {D : Expr F G Ev 0} {t : Trace A.Msg}
    (ht : t ∈ Cont.runWith (D.denote finZeroElim) κ) (hU : ∀ k ∈ t.nonces, k ∉ U) :
    Runs A ⟨U, {C D}⟩ t := by
  obtain ⟨t₁, t₂, U', D', rfl, h₁, hfr, h₂⟩ := Expr.sound D finZeroElim _ _ _
    (by rw [Expr.subst_finZero]; exact ht) hU
  rw [Expr.subst_finZero] at h₁
  refine Runs.ctx hC h₁ ?_
  rcases h₂ with rfl | ⟨u, hu, ht₂⟩
  · exact .nil _
  · exact hval hu ht₂ hfr

/-- A `k`-ary context of processes whose steps from arguments that are not all may-fail
terms are the term steps of the first argument that is not one. -/
def Step.ArgCtxInv (A : Model F G Ev) (C : (Fin k → Expr F G Ev 0) → Process F G Ev 0) : Prop :=
  ∀ {U : Finset ℕ} {l : Option (Act A.Msg)} {c' : Config F G Ev} {args : Fin k → Expr F G Ev 0}
    {i : Fin k}, (∀ j, j < i → (args j).IsValue) → ¬ (args i).IsValue →
    Step A ⟨U, {C args}⟩ l c' →
    ∃ U' D', TStep A U (args i) l U' D' ∧ c' = ⟨U', {C (Function.update args i D')}⟩

/-- Among arguments not all may-fail terms there is a first that is not one. -/
theorem exists_first_not_value {args : Fin k → Expr F G Ev 0} (h : ¬ ∀ j, (args j).IsValue) :
    ∃ i, (∀ j, j < i → (args j).IsValue) ∧ ¬ (args i).IsValue := by
  obtain ⟨i₀, hi₀⟩ := not_forall.1 h
  obtain ⟨i, hi, hmin⟩ := wellFounded_lt.has_min {j : Fin k | ¬ (args j).IsValue} ⟨i₀, hi₀⟩
  exact ⟨i, fun j hj => by_contra fun hv => hmin j hv hj, hi⟩

/-- A run of a process in a `k`-ary context is a run of its arguments, then a run of the
process on the may-fail terms reached, if they all are. -/
theorem Runs.args_split {C : (Fin k → Expr F G Ev 0) → Process F G Ev 0} (hC : Step.ArgCtxInv A C)
    {c : Config F G Ev} {t : Trace A.Msg} (h : Runs A c t) :
    ∀ {U : Finset ℕ} {args : Fin k → Expr F G Ev 0}, c = ⟨U, {C args}⟩ →
      ∃ t₁ t₂ U' args', t = t₁ ++ t₂ ∧ ArgRuns A U args t₁ U' args' ∧
        Runs A ⟨U', {C args'}⟩ t₂ ∧ (t₂ = [] ∨ ∀ j, (args' j).IsValue) := by
  induction h with
  | nil c =>
    rintro U args rfl
    exact ⟨[], [], U, args, rfl, .nil _ _, .nil _, Or.inl rfl⟩
  | @tau c c' t hs hr ih =>
    rintro U args rfl
    by_cases hall : ∀ j, (args j).IsValue
    · exact ⟨[], t, U, args, rfl, .nil _ _, .tau hs hr, Or.inr hall⟩
    · obtain ⟨i, hv, hi⟩ := exists_first_not_value hall
      obtain ⟨U₁, D₁, hs', rfl⟩ := hC hv hi hs
      obtain ⟨t₁, t₂, U', args', rfl, h₁, h₂, h₃⟩ := ih rfl
      exact ⟨t₁, t₂, U', args', rfl, .tau i hv hs' h₁, h₂, h₃⟩
  | @act c c' a t hs hr ih =>
    rintro U args rfl
    by_cases hall : ∀ j, (args j).IsValue
    · exact ⟨[], a :: t, U, args, rfl, .nil _ _, .act hs hr, Or.inr hall⟩
    · obtain ⟨i, hv, hi⟩ := exists_first_not_value hall
      obtain ⟨U₁, D₁, hs', rfl⟩ := hC hv hi hs
      obtain ⟨t₁, t₂, U', args', rfl, h₁, h₂, h₃⟩ := ih rfl
      exact ⟨a :: t₁, t₂, U', args', rfl, .act i hv hs' h₁, h₂, h₃⟩

/-- A run of a process in a `k`-ary context is a trace of the computations of its
arguments with the process as the continuation, if the runs of the process on may-fail
terms are its traces. -/
theorem Runs.argCtx_mem {C : (Fin k → Expr F G Ev 0) → Process F G Ev 0} (hC : Step.ArgCtxInv A C)
    {K : (Fin k → Option A.Msg) → Proc A.Msg} (hK : ∀ us, [] ∈ K us)
    (hval : ∀ {U' : Finset ℕ} {Vs : Fin k → Expr F G Ev 0} {us : Fin k → Option A.Msg}
      {t₂ : Trace A.Msg}, (∀ i, Val A (Vs i) (us i)) → Runs A ⟨U', {C Vs}⟩ t₂ → t₂ ∈ K us)
    {U : Finset ℕ} {args : Fin k → Expr F G Ev 0} {t : Trace A.Msg} (h : Runs A ⟨U, {C args}⟩ t) :
    t ∈ Cont.runWith (seqFin fun i => (args i).denote finZeroElim) K := by
  obtain ⟨t₁, t₂, U', args', rfl, h₁, h₂, h₃⟩ := h.args_split hC rfl
  rcases h₃ with rfl | hall
  · rw [List.append_nil]
    exact h₁.mem_run hK
  · choose us hus using fun j => (hall j).val
    exact h₁.mem_run_val hus (hval hus h₂) (Runs.nonces h₂).2

/-- A trace of the computations of arguments with a process as the continuation is a run
of the process in the `k`-ary context, if the traces of the process on may-fail terms are
its runs. -/
theorem Runs.argCtx_of_mem {C : (Fin k → Expr F G Ev 0) → Process F G Ev 0}
    (hC : Step.IsArgCtx A C) {K : (Fin k → Option A.Msg) → Proc A.Msg}
    (hval : ∀ {U' : Finset ℕ} {Vs : Fin k → Expr F G Ev 0} {us : Fin k → Option A.Msg}
      {t₂ : Trace A.Msg}, (∀ i, Val A (Vs i) (us i)) → t₂ ∈ K us → (∀ k ∈ t₂.nonces, k ∉ U') →
      Runs A ⟨U', {C Vs}⟩ t₂)
    {args : Fin k → Expr F G Ev 0} (hs : ∀ j, Expr.Sound A (args j)) {U : Finset ℕ}
    {t : Trace A.Msg} (ht : t ∈ Cont.runWith (seqFin fun j => (args j).denote finZeroElim) K)
    (hU : ∀ k ∈ t.nonces, k ∉ U) : Runs A ⟨U, {C args}⟩ t := by
  obtain ⟨t₁, t₂, U', args', rfl, h₁, hfr, h₂⟩ := seqFin_sound (A := A) _ 0 (Nat.zero_add _) args
    (fun j hj => absurd hj (Nat.not_lt_zero _)) hs ht hU
  refine Runs.argCtx hC h₁ ?_
  rcases h₂ with rfl | ⟨us, hus, ht₂⟩
  · exact .nil _
  · exact hval hus ht₂ hfr

/-! ### The six contexts -/

theorem isCtx_out₁ (M : Expr F G Ev 0) (P : Process F G Ev 0) :
    Step.IsCtx A fun N => .out N M P := fun hs => Step.out_ctx₁ (Ps := 0) M P hs

theorem isCtx_out₂ {N : Expr F G Ev 0} (hN : N.IsValue) (P : Process F G Ev 0) :
    Step.IsCtx A fun M => .out N M P := fun hs => Step.out_ctx₂ (Ps := 0) N P hN hs

theorem isCtx_inp (P : Process F G Ev 1) : Step.IsCtx A fun N => .inp N P :=
  fun hs => Step.inp_ctx (Ps := 0) P hs

theorem isCtx_let (P : Process F G Ev 1) (Q : Process F G Ev 0) :
    Step.IsCtx A fun D => .let_ D P Q := fun hs => Step.let_ctx (Ps := 0) P Q hs

theorem isCtx_ite (P Q : Process F G Ev 0) : Step.IsCtx A fun C => .ite C P Q :=
  fun hs => Step.ite_ctx (Ps := 0) P Q hs

theorem ctxInv_out₁ (M : Expr F G Ev 0) (P : Process F G Ev 0) :
    Step.CtxInv A fun N => .out N M P := by
  intro U l c' N hN hs
  rcases hs.singleton rfl with ⟨_, _, hN', -⟩ | ⟨U', N', hs', rfl⟩ | ⟨hN', -⟩
  · exact (hN hN'.isValue).elim
  · exact ⟨U', N', hs', rfl⟩
  · exact (hN hN').elim

theorem ctxInv_out₂ {N : Expr F G Ev 0} (hN : N.IsValue) (P : Process F G Ev 0) :
    Step.CtxInv A fun M => .out N M P := by
  intro U l c' M hM hs
  rcases hs.singleton rfl with ⟨_, _, -, hM', -⟩ | ⟨_, _, hs', -⟩ | ⟨-, U', M', hs', rfl⟩
  · exact (hM hM'.isValue).elim
  · exact (hs'.not_value hN).elim
  · exact ⟨U', M', hs', rfl⟩

theorem ctxInv_inp (P : Process F G Ev 1) : Step.CtxInv A fun N => .inp N P := by
  intro U l c' N hN hs
  rcases hs.singleton rfl with ⟨_, _, hN', -⟩ | ⟨U', N', hs', rfl⟩
  · exact (hN hN'.isValue).elim
  · exact ⟨U', N', hs', rfl⟩

theorem ctxInv_let (P : Process F G Ev 1) (Q : Process F G Ev 0) :
    Step.CtxInv A fun D => .let_ D P Q := by
  intro U l c' D hD hs
  rcases hs.singleton rfl with ⟨_, _, hD', -⟩ | ⟨rfl, -⟩ | ⟨U', D', hs', rfl⟩
  · exact (hD hD'.isValue).elim
  · exact (hD (Or.inr rfl)).elim
  · exact ⟨U', D', hs', rfl⟩

theorem ctxInv_ite (P Q : Process F G Ev 0) : Step.CtxInv A fun C => .ite C P Q := by
  intro U l c' C hC hs
  rcases hs.singleton rfl with ⟨hC', -⟩ | ⟨_, hC', -⟩ | ⟨U', C', hs', rfl⟩
  · exact (hC hC'.isValue).elim
  · exact (hC hC'.isValue).elim
  · exact ⟨U', C', hs', rfl⟩

theorem argCtxInv_event (e : Ev k) (P : Process F G Ev 0) :
    Step.ArgCtxInv A fun args => .event e args P := by
  intro U l c' args i hv hi hs
  rcases hs.singleton rfl with ⟨_, hms, -, -⟩ | ⟨i', U', D', hv', hs', rfl⟩
  · exact (hi (hms i).isValue).elim
  · obtain rfl : i' = i := by
      rcases lt_trichotomy i' i with h | h | h
      · exact (hs'.not_value (hv i' h)).elim
      · exact h
      · exact (hi (hv' i h)).elim
    exact ⟨U', D', hs', rfl⟩

/-! ### Steps on may-fail terms -/

theorem Runs.out_values {U : Finset ℕ} {V W : Expr F G Ev 0} {u v : Option A.Msg}
    (hV : Val A V u) (hW : Val A W v) {P : Process F G Ev 0} {t : Trace A.Msg}
    (h : Runs A ⟨U, {.out V W P}⟩ t) :
    t = [] ∨ ∃ c m t', u = some c ∧ v = some m ∧ t = .out c m :: t' ∧ Runs A ⟨U, {P}⟩ t' := by
  cases h with
  | nil => exact Or.inl rfl
  | tau hs _ =>
    rcases hs.singleton rfl with ⟨_, _, -, -, h, -⟩ | ⟨_, _, hs', -⟩ | ⟨-, _, _, hs', -⟩
    · cases h
    · exact (hs'.not_value hV.isValue).elim
    · exact (hs'.not_value hW.isValue).elim
  | act hs hr =>
    rcases hs.singleton rfl with ⟨c, m, hN, hM, h, rfl⟩ | ⟨_, _, hs', -⟩ | ⟨-, _, _, hs', -⟩
    · obtain rfl := Option.some.inj h
      exact Or.inr ⟨c, m, _, hV.eq hN, hW.eq hM, rfl, hr⟩
    · exact (hs'.not_value hV.isValue).elim
    · exact (hs'.not_value hW.isValue).elim

theorem Runs.inp_value {U : Finset ℕ} {V : Expr F G Ev 0} {u : Option A.Msg} (hV : Val A V u)
    {P : Process F G Ev 1} {t : Trace A.Msg} (h : Runs A ⟨U, {.inp V P}⟩ t) :
    t = [] ∨ ∃ c M t', u = some c ∧ t = .inp c (Tm.msg A M) :: t' ∧
      Runs A ⟨U, {P.inst M}⟩ t' := by
  cases h with
  | nil => exact Or.inl rfl
  | tau hs _ =>
    rcases hs.singleton rfl with ⟨_, _, -, h, -⟩ | ⟨_, _, hs', -⟩
    · cases h
    · exact (hs'.not_value hV.isValue).elim
  | act hs hr =>
    rcases hs.singleton rfl with ⟨c, M, hN, h, rfl⟩ | ⟨_, _, hs', -⟩
    · obtain rfl := Option.some.inj h
      exact Or.inr ⟨c, M, _, hV.eq hN, rfl, hr⟩
    · exact (hs'.not_value hV.isValue).elim

theorem Runs.let_value {U : Finset ℕ} {V : Expr F G Ev 0} {u : Option A.Msg} (hV : Val A V u)
    {P : Process F G Ev 1} {Q : Process F G Ev 0} {t : Trace A.Msg}
    (h : Runs A ⟨U, {.let_ V P Q}⟩ t) :
    (∃ m M', u = some m ∧ Tm.msg A M' = m ∧ Runs A ⟨U, {P.inst M'}⟩ t) ∨
      (u = none ∧ Runs A ⟨U, {Q}⟩ t) := by
  cases h with
  | nil =>
    cases u with
    | none => exact Or.inr ⟨rfl, .nil _⟩
    | some m =>
      obtain ⟨M, hM⟩ := msg_surjective m
      exact Or.inl ⟨m, M, rfl, hM, .nil _⟩
  | tau hs hr =>
    rcases hs.singleton rfl with ⟨m, M', hD, hM, -, rfl⟩ | ⟨rfl, -, rfl⟩ | ⟨_, _, hs', -⟩
    · exact Or.inl ⟨m, M', hV.eq hD, hM, hr⟩
    · exact Or.inr ⟨hV.eq .fail, hr⟩
    · exact (hs'.not_value hV.isValue).elim
  | act hs _ =>
    rcases hs.singleton rfl with ⟨_, _, -, -, h, -⟩ | ⟨-, h, -⟩ | ⟨_, _, hs', -⟩
    · cases h
    · cases h
    · exact (hs'.not_value hV.isValue).elim

theorem Runs.ite_value {U : Finset ℕ} {V : Expr F G Ev 0} {u : Option A.Msg} (hV : Val A V u)
    {P Q : Process F G Ev 0} {t : Trace A.Msg} (h : Runs A ⟨U, {.ite V P Q}⟩ t) :
    (∃ c, u = some c ∧ ((c = StdOps.tt ∧ Runs A ⟨U, {P}⟩ t) ∨
      (c ≠ StdOps.tt ∧ Runs A ⟨U, {Q}⟩ t))) ∨ (u = none ∧ t = []) := by
  cases h with
  | nil =>
    cases u with
    | none => exact Or.inr ⟨rfl, rfl⟩
    | some c =>
      refine Or.inl ⟨c, rfl, ?_⟩
      by_cases hc : c = StdOps.tt
      · exact Or.inl ⟨hc, .nil _⟩
      · exact Or.inr ⟨hc, .nil _⟩
  | tau hs hr =>
    rcases hs.singleton rfl with ⟨hC, -, rfl⟩ | ⟨m, hC, hm, -, rfl⟩ | ⟨_, _, hs', -⟩
    · exact Or.inl ⟨_, hV.eq hC, Or.inl ⟨rfl, hr⟩⟩
    · exact Or.inl ⟨m, hV.eq hC, Or.inr ⟨hm, hr⟩⟩
    · exact (hs'.not_value hV.isValue).elim
  | act hs _ =>
    rcases hs.singleton rfl with ⟨-, h, -⟩ | ⟨_, -, -, h, -⟩ | ⟨_, _, hs', -⟩
    · cases h
    · cases h
    · exact (hs'.not_value hV.isValue).elim

theorem Runs.event_values {U : Finset ℕ} {e : Ev k} {Vs : Fin k → Expr F G Ev 0}
    {us : Fin k → Option A.Msg} (hV : ∀ i, Val A (Vs i) (us i)) {P : Process F G Ev 0}
    {t : Trace A.Msg} (h : Runs A ⟨U, {.event e Vs P}⟩ t) :
    t = [] ∨ ∃ ms t', (∀ i, us i = some (ms i)) ∧
      t = .event (Theory.Msg.app (.inl (.inr e)) ms) :: t' ∧ Runs A ⟨U, {P}⟩ t' := by
  cases h with
  | nil => exact Or.inl rfl
  | tau hs _ =>
    rcases hs.singleton rfl with ⟨_, -, h, -⟩ | ⟨i, _, _, -, hs', -⟩
    · cases h
    · exact (hs'.not_value (hV i).isValue).elim
  | act hs hr =>
    rcases hs.singleton rfl with ⟨ms, hms, h, rfl⟩ | ⟨i, _, _, -, hs', -⟩
    · obtain rfl := Option.some.inj h
      exact Or.inr ⟨ms, _, fun i => (hV i).eq (hms i), rfl, hr⟩
    · exact (hs'.not_value (hV i).isValue).elim

/-! ### The continuations -/

theorem nil_mem_outK (P : Proc A.Msg) (u v : Option A.Msg) : [] ∈ outK P u v := by
  cases u <;> cases v <;> first | exact Set.mem_insert _ _ | rfl

theorem mem_outK {P : Proc A.Msg} {u v : Option A.Msg} {t : Trace A.Msg} (h : t ∈ outK P u v) :
    t = [] ∨ ∃ c m t', u = some c ∧ v = some m ∧ t = .out c m :: t' ∧ t' ∈ P := by
  cases u with
  | none => exact Or.inl (Set.mem_singleton_iff.1 h)
  | some c =>
    cases v with
    | none => exact Or.inl (Set.mem_singleton_iff.1 h)
    | some m =>
      rcases h with rfl | ⟨t', ht', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨c, m, t', rfl, rfl, rfl, ht'⟩

theorem nil_mem_inpK (P : A.Msg → Proc A.Msg) (u : Option A.Msg) : [] ∈ inpK P u := by
  cases u with
  | none => rfl
  | some c => exact Set.mem_iUnion.2 ⟨Theory.Msg.name 0, Set.mem_insert _ _⟩

open Classical in
theorem nil_mem_iteK {P Q : Proc A.Msg} (hP : [] ∈ P) (hQ : [] ∈ Q) (u : Option A.Msg) :
    [] ∈ iteK P Q u := by
  cases u with
  | none => rfl
  | some c =>
    show [] ∈ if c = StdOps.tt then P else Q
    split_ifs
    · exact hP
    · exact hQ

theorem nil_mem_eventK (e : Ev k) (P : Proc A.Msg) (us : Fin k → Option A.Msg) :
    [] ∈ eventK e P us := by
  unfold eventK
  cases eventMsg e us with
  | none => rfl
  | some m => exact Set.mem_insert _ _

theorem mem_eventK {e : Ev k} {P : Proc A.Msg} {us : Fin k → Option A.Msg} {t : Trace A.Msg}
    (h : t ∈ eventK e P us) :
    t = [] ∨ ∃ ms t', (∀ i, us i = some (ms i)) ∧
      t = .event (Theory.Msg.app (.inl (.inr e)) ms) :: t' ∧ t' ∈ P := by
  unfold eventK at h
  rcases hm : eventMsg e us with _ | m
  · rw [hm] at h
    exact Or.inl (Set.mem_singleton_iff.1 h)
  · rw [hm] at h
    obtain ⟨ms, hms, hm'⟩ := liftFail_eq_some.1 hm
    obtain rfl := Option.some.inj hm'
    rcases h with rfl | ⟨t', ht', rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨ms, t', hms, rfl, ht'⟩

/-! ## The denotation and the runs -/

theorem nil_mem_denote : ∀ {n : ℕ} (P : Process F G Ev n) (xs : Fin n → A.Msg), [] ∈ P.denote xs
  | _, .nil, _ => rfl
  | _, .out N M P, xs => by
    simp only [Process.denote]
    exact nil_mem_run N xs fun c => nil_mem_run M xs fun m => nil_mem_outK _ c m
  | _, .inp N P, xs => by
    simp only [Process.denote]
    exact nil_mem_run N xs fun c => nil_mem_inpK _ c
  | _, .par P Q, xs => ⟨⟨![[], ([] : Trace A.Msg)], [], Fin.forall_fin_two.2 ⟨nil_mem_denote P xs,
      nil_mem_denote Q xs⟩, fun i => by fin_cases i <;> rfl, .nil⟩, List.nodup_nil⟩
  | _, .bang P, xs => ⟨⟨fun _ => [], [], fun _ => nil_mem_denote P xs, fun _ => rfl, .nil⟩,
      List.nodup_nil⟩
  | _, .new _, _ => Set.mem_iUnion.2 ⟨0, Set.mem_insert _ _⟩
  | _, .let_ D P Q, xs => by
    simp only [Process.denote]
    refine nil_mem_run D xs fun u => ?_
    cases u with
    | none => exact nil_mem_denote Q xs
    | some a => exact nil_mem_denote P (Fin.snoc xs a)
  | _, .ite C P Q, xs => by
    simp only [Process.denote]
    exact nil_mem_run C xs fun u => nil_mem_iteK (nil_mem_denote P xs) (nil_mem_denote Q xs) u
  | _, .event e args P, xs => by
    simp only [Process.denote]
    exact nil_mem_seqFin_run (fun i κ hκ => nil_mem_run (args i) xs hκ) fun us =>
      nil_mem_eventK _ _ us

theorem nonces_cons_subset {M : Type} (a : Act M) (t : Trace M) :
    t.nonces ⊆ Trace.nonces (a :: t) :=
  (Trace.nonces_sublist (List.sublist_cons_self a t)).subset

theorem denote_args_subst (σ : Fin n → Tm F Ev 0) (args : Fin k → Expr F G Ev n) :
    (fun i => (args i).denote fun i => Tm.msg A (σ i)) =
      fun i => ((args i).subst σ).denote finZeroElim :=
  funext fun i => (Expr.denote_subst_msg σ (args i)).symm

open Classical in
/-- A trace of a run is a trace of the denotation. -/
theorem denote_of_runs : ∀ {n : ℕ} (P : Process F G Ev n) (σ : Fin n → Tm F Ev 0) {U : Finset ℕ}
    {t : Trace A.Msg}, Runs A ⟨U, {P.subst σ}⟩ t → t ∈ P.denote fun i => Tm.msg A (σ i)
  | _, .nil, σ, U, t, h => by
    simp only [Process.subst] at h
    obtain rfl : t = [] := by
      cases h with
      | nil => rfl
      | tau hs hr =>
        obtain ⟨-, rfl⟩ := Step.singleton hs rfl
        exact Runs.zero hr rfl
      | act hs _ =>
        obtain ⟨h, -⟩ := Step.singleton hs rfl
        cases h
    exact nil_mem_denote _ _
  | _, .out N M P, σ, U, t, h => by
    simp only [Process.subst] at h
    simp only [Process.denote]
    rw [← Expr.denote_subst_msg σ N, ← Expr.denote_subst_msg σ M]
    refine Runs.ctx_mem (C := fun N' => .out N' (M.subst σ) (P.subst σ)) (ctxInv_out₁ _ _)
      (fun u => nil_mem_run _ _ fun v => nil_mem_outK _ u v) (fun hV h₂ => ?_) h
    refine Runs.ctx_mem (C := fun M' => .out _ M' (P.subst σ)) (ctxInv_out₂ hV.isValue _)
      (fun v => nil_mem_outK _ _ v) (fun hW h₃ => ?_) h₂
    rcases Runs.out_values hV hW h₃ with rfl | ⟨c, m, t', rfl, rfl, rfl, hr⟩
    · exact nil_mem_outK _ _ _
    · exact Or.inr ⟨t', denote_of_runs P σ hr, rfl⟩
  | _, .inp N P, σ, U, t, h => by
    simp only [Process.subst] at h
    simp only [Process.denote]
    rw [← Expr.denote_subst_msg σ N]
    refine Runs.ctx_mem (C := fun N' => .inp N' (P.subst (liftSubst σ))) (ctxInv_inp _)
      (fun u => nil_mem_inpK _ u) (fun hV h₂ => ?_) h
    rcases Runs.inp_value hV h₂ with rfl | ⟨c, M, t', rfl, rfl, hr⟩
    · exact nil_mem_inpK _ _
    · refine Set.mem_iUnion.2 ⟨Tm.msg A M, Or.inr ⟨_, ?_, rfl⟩⟩
      have := denote_of_runs P (Fin.snoc σ M) (Runs.eqv hr (.cons (subst_inst_eqv P σ M) .zero))
      rw [msgs_snoc] at this
      exact this
  | _, .par P Q, σ, U, t, h => by
    simp only [Process.subst] at h
    cases h with
    | nil => exact nil_mem_denote _ _
    | tau hs hr =>
      obtain ⟨-, rfl⟩ := Step.singleton hs rfl
      obtain ⟨t₀, t₁, s, h₀, h₁, hs₀, hs₁, hc⟩ :=
        Runs.split hr (congrArg _ (Multiset.singleton_add _ _).symm)
      exact ⟨⟨![t₀, t₁], s, Fin.forall_fin_two.2 ⟨denote_of_runs P σ h₀, denote_of_runs Q σ h₁⟩,
        Fin.forall_fin_two.2 ⟨hs₀, hs₁⟩, hc⟩, (Runs.nonces hr).1⟩
    | act hs _ =>
      obtain ⟨h, -⟩ := Step.singleton hs rfl
      cases h
  | _, .bang P, σ, U, t, h => by
    simp only [Process.subst] at h
    have h0 : ({Process.bang (P.subst σ)} : Multiset (Process F G Ev 0)) =
        0 + {Process.bang (P.subst σ)} := (zero_add _).symm
    rw [h0] at h
    obtain ⟨k, hk⟩ := Runs.bang_unfold h rfl
    rw [zero_add] at hk
    refine (mem_bang_iff (nil_mem_denote P _)).2 ⟨k, ?_⟩
    clear h
    induction k generalizing t with
    | zero =>
      rw [Multiset.replicate_zero] at hk
      obtain rfl := Runs.zero hk rfl
      rfl
    | succ k ih =>
      rw [Multiset.replicate_succ, ← Multiset.singleton_add] at hk
      obtain ⟨t₀, t₁, s, h₀, h₁, hs₀, hs₁, hc⟩ := Runs.split hk rfl
      exact ⟨⟨![t₀, t₁], s, Fin.forall_fin_two.2 ⟨denote_of_runs P σ h₀, ih _ h₁⟩,
        Fin.forall_fin_two.2 ⟨hs₀, hs₁⟩, hc⟩, (Runs.nonces hk).1⟩
  | _, .new P, σ, U, t, h => by
    simp only [Process.subst] at h
    cases h with
    | nil => exact nil_mem_denote _ _
    | tau hs _ =>
      obtain ⟨_, _, h, -⟩ := Step.singleton hs rfl
      cases h
    | act hs hr =>
      obtain ⟨k, hk, h, rfl⟩ := Step.singleton hs rfl
      obtain rfl := Option.some.inj h
      have hr' := Runs.eqv hr (.cons (subst_inst_eqv P σ (.var (.inl k))) .zero)
      have hm := denote_of_runs P (Fin.snoc σ _) hr'
      rw [msgs_snoc] at hm
      simp only [Process.denote]
      exact Set.mem_iUnion.2 ⟨k, Or.inr ⟨_, ⟨hm, fun hk' =>
        (Runs.nonces hr').2 k hk' (Finset.mem_insert_self k U)⟩, rfl⟩⟩
  | _, .let_ D P Q, σ, U, t, h => by
    simp only [Process.subst] at h
    simp only [Process.denote]
    rw [← Expr.denote_subst_msg σ D]
    refine Runs.ctx_mem (C := fun D' => .let_ D' (P.subst (liftSubst σ)) (Q.subst σ))
      (ctxInv_let _ _) (fun u => ?_) (fun hV h₂ => ?_) h
    · cases u with
      | none => exact nil_mem_denote Q _
      | some a => exact nil_mem_denote P _
    · rcases Runs.let_value hV h₂ with ⟨m, M', rfl, hM, hr⟩ | ⟨rfl, hr⟩
      · have := denote_of_runs P (Fin.snoc σ M')
          (Runs.eqv hr (.cons (subst_inst_eqv P σ M') .zero))
        rw [msgs_snoc, hM] at this
        exact this
      · exact denote_of_runs Q σ hr
  | _, .ite C P Q, σ, U, t, h => by
    simp only [Process.subst] at h
    simp only [Process.denote]
    rw [← Expr.denote_subst_msg σ C]
    refine Runs.ctx_mem (C := fun C' => .ite C' (P.subst σ) (Q.subst σ)) (ctxInv_ite _ _)
      (fun u => nil_mem_iteK (nil_mem_denote P _) (nil_mem_denote Q _) u) (fun hV h₂ => ?_) h
    rcases Runs.ite_value hV h₂ with ⟨c, rfl, ⟨hc, hr⟩ | ⟨hc, hr⟩⟩ | ⟨rfl, rfl⟩
    · show _ ∈ if c = StdOps.tt then _ else _
      rw [if_pos hc]
      exact denote_of_runs P σ hr
    · show _ ∈ if c = StdOps.tt then _ else _
      rw [if_neg hc]
      exact denote_of_runs Q σ hr
    · rfl
  | _, .event e args P, σ, U, t, h => by
    simp only [Process.subst] at h
    simp only [Process.denote]
    rw [denote_args_subst]
    refine Runs.argCtx_mem (C := fun args' => .event e args' (P.subst σ)) (argCtxInv_event _ _)
      (fun us => nil_mem_eventK _ _ us) (fun hV h₂ => ?_) h
    rcases Runs.event_values hV h₂ with rfl | ⟨ms, t', hms, rfl, hr⟩
    · exact nil_mem_eventK _ _ _
    · unfold eventK
      rw [eventMsg_eq_some hms]
      exact Or.inr ⟨t', denote_of_runs P σ hr, rfl⟩

theorem nonces_proj_subset {ι : Type} [DecidableEq ι] {s : TaggedTrace ι A.Msg} {t : Trace A.Msg}
    (hc : s.Comms t) (i : ι) : (s.proj i).nonces ⊆ t.nonces := by
  rw [hc.nonces]
  exact (Trace.nonces_sublist (List.filter_sublist.map _)).subset

open Classical in
/-- A trace of the denotation is a trace of a run, from any created names it avoids. -/
theorem runs_of_denote : ∀ {n : ℕ} (P : Process F G Ev n) (σ : Fin n → Tm F Ev 0) {U : Finset ℕ}
    {t : Trace A.Msg}, t ∈ P.denote (fun i => Tm.msg A (σ i)) → (∀ k ∈ t.nonces, k ∉ U) →
    Runs A ⟨U, {P.subst σ}⟩ t
  | _, .nil, σ, U, t, ht, _ => by
    obtain rfl := Set.mem_singleton_iff.1 ht
    exact .nil _
  | _, .out N M P, σ, U, t, ht, hU => by
    simp only [Process.denote] at ht
    simp only [Process.subst]
    rw [← Expr.denote_subst_msg σ N, ← Expr.denote_subst_msg σ M] at ht
    refine Runs.ctx_of_mem (C := fun N' => .out N' (M.subst σ) (P.subst σ)) (isCtx_out₁ _ _)
      (fun hV ht₂ hfr => ?_) ht hU
    refine Runs.ctx_of_mem (C := fun M' => .out _ M' (P.subst σ)) (isCtx_out₂ hV.isValue _)
      (fun hW ht₃ hfr' => ?_) ht₂ hfr
    rcases mem_outK ht₃ with rfl | ⟨c, m, t', rfl, rfl, rfl, ht'⟩
    · exact .nil _
    · exact .act (.out _ hV hW)
        (runs_of_denote P σ ht' fun k hk => hfr' k (nonces_cons_subset _ _ hk))
  | _, .inp N P, σ, U, t, ht, hU => by
    simp only [Process.denote] at ht
    simp only [Process.subst]
    rw [← Expr.denote_subst_msg σ N] at ht
    refine Runs.ctx_of_mem (C := fun N' => .inp N' (P.subst (liftSubst σ))) (isCtx_inp _)
      (@fun U' V u t₂ hV ht₂ hfr => ?_) ht hU
    cases u with
    | none => exact (Set.mem_singleton_iff.1 ht₂).symm ▸ .nil _
    | some c =>
      obtain ⟨a, ht₂⟩ := Set.mem_iUnion.1 ht₂
      rcases ht₂ with rfl | ⟨t', ht', rfl⟩
      · exact .nil _
      · obtain ⟨M, rfl⟩ := msg_surjective a
        have hr := runs_of_denote P (Fin.snoc σ M) (by rw [msgs_snoc]; exact ht') fun k hk =>
          hfr k (nonces_cons_subset _ _ hk)
        exact .act (.inp _ M hV) (Runs.eqv hr (.cons (subst_inst_eqv P σ M).symm .zero))
  | _, .par P Q, σ, U, t, ht, hU => by
    simp only [Process.denote] at ht
    simp only [Process.subst]
    obtain ⟨⟨f, s, hf, hs, hc⟩, hn⟩ := ht
    have hsub : ∀ i k, k ∈ (f i).nonces → k ∉ U := fun i k hk =>
      hU k (nonces_proj_subset hc i (hs i ▸ hk))
    have h₀ := runs_of_denote P σ (hf 0) (hsub 0)
    have h₁ := runs_of_denote Q σ (hf 1) (hsub 1)
    have := runs_add hc h₀ h₁ (hs 0) (hs 1) hn (hsub 0) (hsub 1)
    rw [Finset.union_self, Multiset.singleton_add] at this
    exact .tau (.par _ _) this
  | _, .bang P, σ, U, t, ht, hU => by
    simp only [Process.denote] at ht
    simp only [Process.subst]
    obtain ⟨k, hk⟩ := (mem_bang_iff (nil_mem_denote P _)).1 ht
    refine Runs.of_replicate (n := k) ?_
    clear ht
    induction k generalizing t with
    | zero =>
      obtain rfl := Set.mem_singleton_iff.1 hk
      exact .nil _
    | succ k ih =>
      obtain ⟨⟨f, s, hf, hs, hc⟩, hn⟩ := hk
      have hsub : ∀ i k, k ∈ (f i).nonces → k ∉ U := fun i k hk =>
        hU k (nonces_proj_subset hc i (hs i ▸ hk))
      have h₀ := runs_of_denote P σ (hf 0) (hsub 0)
      have h₁ := ih _ (hsub 1) (hf 1)
      have := runs_add hc h₀ h₁ (hs 0) (hs 1) hn (hsub 0) (hsub 1)
      rwa [Finset.union_self, Multiset.singleton_add, ← Multiset.replicate_succ] at this
  | _, .new P, σ, U, t, ht, hU => by
    simp only [Process.denote] at ht
    simp only [Process.subst]
    obtain ⟨k, ht⟩ := Set.mem_iUnion.1 ht
    rcases ht with rfl | ⟨t', ⟨ht', hk⟩, rfl⟩
    · exact .nil _
    · have hkU : k ∉ U := hU k (by simp [Trace.nonces])
      have hr := runs_of_denote P (Fin.snoc σ (.var (.inl k))) (by rw [msgs_snoc]; exact ht')
        fun k' hk' hk'U => by
          rcases Finset.mem_insert.1 hk'U with rfl | hk'U
          · exact hk hk'
          · exact hU k' (by simp [Trace.nonces, hk']) hk'U
      exact .act (.new _ k hkU) (Runs.eqv hr (.cons (subst_inst_eqv P σ _).symm .zero))
  | _, .let_ D P Q, σ, U, t, ht, hU => by
    simp only [Process.denote] at ht
    simp only [Process.subst]
    rw [← Expr.denote_subst_msg σ D] at ht
    refine Runs.ctx_of_mem (C := fun D' => .let_ D' (P.subst (liftSubst σ)) (Q.subst σ))
      (isCtx_let _ _) (@fun U' V u t₂ hV ht₂ hfr => ?_) ht hU
    cases u with
    | none =>
      obtain rfl := hV.eq_fail rfl
      exact .tau (.eval₂ _ _) (runs_of_denote Q σ ht₂ hfr)
    | some a =>
      obtain ⟨M, rfl⟩ := msg_surjective a
      have hr := runs_of_denote P (Fin.snoc σ M) (by rw [msgs_snoc]; exact ht₂) hfr
      exact .tau (.eval₁ M _ _ hV rfl) (Runs.eqv hr (.cons (subst_inst_eqv P σ M).symm .zero))
  | _, .ite C P Q, σ, U, t, ht, hU => by
    simp only [Process.denote] at ht
    simp only [Process.subst]
    rw [← Expr.denote_subst_msg σ C] at ht
    refine Runs.ctx_of_mem (C := fun C' => .ite C' (P.subst σ) (Q.subst σ)) (isCtx_ite _ _)
      (@fun U' V u t₂ hV ht₂ hfr => ?_) ht hU
    cases u with
    | none => exact (Set.mem_singleton_iff.1 ht₂).symm ▸ .nil _
    | some c =>
      change _ ∈ if c = StdOps.tt then _ else _ at ht₂
      split_ifs at ht₂ with hc
      · subst hc
        exact .tau (.cond₁ _ _ hV) (runs_of_denote P σ ht₂ hfr)
      · exact .tau (.cond₂ _ _ hV hc) (runs_of_denote Q σ ht₂ hfr)
  | _, .event e args P, σ, U, t, ht, hU => by
    simp only [Process.denote] at ht
    simp only [Process.subst]
    rw [denote_args_subst] at ht
    refine Runs.argCtx_of_mem (C := fun args' => .event e args' (P.subst σ))
      (Step.isArgCtx_event _ _) (@fun U' Vs us t₂ hV ht₂ hfr => ?_)
      (fun j => Expr.sound (args j) σ) ht hU
    rcases mem_eventK ht₂ with rfl | ⟨ms, t', hms, rfl, ht'⟩
    · exact .nil _
    · have hV' : ∀ i, Val A (Vs i) (some (ms i)) := fun i => by
        rw [← hms i]
        exact hV i
      exact .act (.event e _ hV')
        (runs_of_denote P σ ht' fun k hk => hfr k (nonces_cons_subset _ _ hk))

variable (A)

/-- Adequacy: a closed process denotes its weak traces. -/
theorem denote_eq_traces (P : Process F G Ev 0) :
    P.denote finZeroElim = Config.traces A ⟨∅, {P}⟩ := by
  ext t
  have hσ : (fun i : Fin 0 => Tm.msg A ((finZeroElim : Fin 0 → Tm F Ev 0) i)) = finZeroElim :=
    funext fun i => i.elim0
  constructor
  · intro ht
    have := runs_of_denote P finZeroElim (by rw [hσ]; exact ht) fun _ _ => Finset.notMem_empty _
    rwa [Process.subst_finZero] at this
  · intro (h : Runs A ⟨∅, {P}⟩ t)
    rw [← Process.subst_finZero P] at h
    have := denote_of_runs P finZeroElim h
    rwa [hσ] at this

end ProVerif.Specification
