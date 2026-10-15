/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.Specification.Denotation
import ScalingTrust.ProVerif.Specification.Invariance

/-!
# Adequacy

The write-up's Theorem "Adequacy": a closed process denotes its weak traces
(`denote_eq_traces`), and the weak traces of a union of multisets are the parallel
composition of those of the parts (`traces_add`).

The first is proved for a process under binders instantiated by closed terms, by
induction on the process: `denote_of_runs` reads the denotation off a run, inverting
its first step with `Step.singleton`, and `runs_of_denote` builds a run from a trace of
the denotation.  Instantiating the last variable after substituting for the others is,
modulo `E`, substituting for all at once (`subst_inst_eqv`), which the invariance of
runs under equality modulo `E` turns into an equality of runs.  Replication is the
case that is not structural: a run of `!P` unfolds it finitely often, so it is a run of
finitely many copies of `P` (`Runs.bang_unfold`, `Runs.of_replicate`), and a trace of
`Proc.bang P` is a trace of finitely many copies in parallel (`mem_bang_iff`).
-/

namespace ProVerif.Specification

open FirstOrder FirstOrder.Language ProVerif.TraceSemantics

variable {F G : Sig} {A : Model F G} {n m k : ℕ}

/-! ## Terms of messages and substitution -/

theorem realize_var_eq : ∀ t : F.lang.Term ℕ, t.realize (M := TraceSemantics.Term F) Term.var = t
  | .var _ => rfl
  | .func f ts => by
    simp only [Term.realize_func, Term.funMap_eq]
    congr 1
    funext i
    exact realize_var_eq (ts i)

/-- Every message is the message of a closed term. -/
theorem msg_surjective (a : A.Msg) : ∃ M : Tm F 0, Tm.msg A M = a := by
  induction a using Quotient.inductionOn with
  | h t =>
    refine ⟨t.relabel Sum.inl, ?_⟩
    show (t.relabel Sum.inl).realize (env finZeroElim) = ⟦t⟧
    rw [Term.realize_relabel,
      show env (A := A) finZeroElim ∘ Sum.inl = fun i => (⟦Term.var i⟧ : A.Msg) from rfl,
      Term.realize_quotient_mk', realize_var_eq]

theorem Tm.msg_subst (σ : Fin n → Tm F 0) (N : Tm F n) :
    Tm.msg A (Tm.subst σ N) = N.realize (env fun i => Tm.msg A (σ i)) :=
  Tm.realize_subst σ N finZeroElim

theorem Expr.denote_subst_msg (σ : Fin n → Tm F 0) (D : Expr F G (ℕ ⊕ Fin n)) :
    (D.subst σ).denote (env finZeroElim) = D.denote (env fun i => Tm.msg A (σ i)) :=
  Expr.denote_subst σ finZeroElim D

theorem msgs_snoc (σ : Fin n → Tm F 0) (M : Tm F 0) :
    (fun i => Tm.msg A (Fin.snoc (α := fun _ => Tm F 0) σ M i)) =
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

theorem Tm.subst_var (M : Tm F n) : Tm.subst (fun i => .var (.inr i)) M = M := by
  rw [Tm.subst, show (Sum.elim (fun k => (.var (.inl k) : Tm F n)) fun i => .var (.inr i)) =
    Term.var from funext fun x => by cases x <;> rfl]
  exact term_subst_var M

theorem liftSubst_var :
    liftSubst (fun i => (.var (.inr i) : Tm F n)) = fun i => .var (.inr i) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [liftSubst]
  | cast j => simp [liftSubst, Term.relabel]

theorem Expr.subst_var : ∀ D : Expr F G (ℕ ⊕ Fin n), D.subst (fun i => .var (.inr i)) = D
  | .term M => by rw [Expr.subst, Tm.subst_var]
  | .ctor f args => by
    simp only [Expr.subst]
    congr 1
    funext i
    exact Expr.subst_var (args i)
  | .dtor g args => by
    simp only [Expr.subst]
    congr 1
    funext i
    exact Expr.subst_var (args i)
  | .fail => rfl

theorem Process.subst_var : ∀ {n : ℕ} (P : Process F G n), P.subst (fun i => .var (.inr i)) = P
  | _, .nil => rfl
  | _, .out N M P => by rw [Process.subst, Tm.subst_var, Tm.subst_var, Process.subst_var P]
  | _, .inp N P => by rw [Process.subst, Tm.subst_var, liftSubst_var, Process.subst_var P]
  | _, .par P Q => by rw [Process.subst, Process.subst_var P, Process.subst_var Q]
  | _, .bang P => by rw [Process.subst, Process.subst_var P]
  | _, .new P => by rw [Process.subst, liftSubst_var, Process.subst_var P]
  | _, .let_ D P Q => by
    rw [Process.subst, Expr.subst_var, liftSubst_var, Process.subst_var P, Process.subst_var Q]
  | _, .ite M P Q => by
    rw [Process.subst, Tm.subst_var, Process.subst_var P, Process.subst_var Q]
  | _, .event M P => by rw [Process.subst, Tm.subst_var, Process.subst_var P]

theorem Process.subst_finZero (P : Process F G 0) : P.subst finZeroElim = P := by
  rw [show (finZeroElim : Fin 0 → Tm F 0) = fun i => .var (.inr i) from funext fun i => i.elim0]
  exact Process.subst_var P

/-- Substituting twice is, modulo `E`, substituting the composite. -/
theorem Tm.subst_subst_eqv (N : Tm F n) {σ : Fin n → Tm F m} {τ : Fin m → Tm F k}
    {ρ : Fin n → Tm F k} (h : ∀ i, Tm.Eqv A (Tm.subst τ (σ i)) (ρ i)) :
    Tm.Eqv A (Tm.subst τ (Tm.subst σ N)) (Tm.subst ρ N) := fun xs => by
  have hf : (fun i => (σ i).realize (env fun j => (τ j).realize (env xs))) =
      fun i => (ρ i).realize (env xs) := funext fun i => by rw [← h i xs, Tm.realize_subst]
  rw [Tm.realize_subst, Tm.realize_subst, Tm.realize_subst, hf]

theorem liftSubst_subst_eqv {σ : Fin n → Tm F m} {τ : Fin m → Tm F k} {ρ : Fin n → Tm F k}
    (h : ∀ i, Tm.Eqv A (Tm.subst τ (σ i)) (ρ i)) (i : Fin (n + 1)) :
    Tm.Eqv A (Tm.subst (liftSubst τ) (liftSubst σ i)) (liftSubst ρ i) := fun xs => by
  obtain ⟨ys, a, rfl⟩ : ∃ ys a, xs = Fin.snoc ys a := ⟨_, _, (Fin.snoc_init_self xs).symm⟩
  have h1 : (fun j => (liftSubst τ j).realize (env (Fin.snoc ys a))) =
      Fin.snoc (α := fun _ => A.Msg) (fun j => (τ j).realize (env ys)) a :=
    funext fun j => realize_liftSubst τ ys a j
  have hf : (fun j => (σ j).realize (env fun j' => (τ j').realize (env ys))) =
      fun j => (ρ j).realize (env ys) := funext fun j => by rw [← h j ys, Tm.realize_subst]
  rw [Tm.realize_subst, h1, realize_liftSubst, realize_liftSubst, hf]

theorem Expr.subst_subst_eqv : ∀ (D : Expr F G (ℕ ⊕ Fin n)) {σ : Fin n → Tm F m}
    {τ : Fin m → Tm F k} {ρ : Fin n → Tm F k}, (∀ i, Tm.Eqv A (Tm.subst τ (σ i)) (ρ i)) →
    Expr.Eqv A ((D.subst σ).subst τ) (D.subst ρ)
  | .term M, _, _, _, h => .term (Tm.subst_subst_eqv M h)
  | .ctor f args, _, _, _, h => .ctor f fun i => Expr.subst_subst_eqv (args i) h
  | .dtor g args, _, _, _, h => .dtor g fun i => Expr.subst_subst_eqv (args i) h
  | .fail, _, _, _, _ => .fail

theorem Process.subst_subst_eqv : ∀ {n m k : ℕ} (P : Process F G n) {σ : Fin n → Tm F m}
    {τ : Fin m → Tm F k} {ρ : Fin n → Tm F k}, (∀ i, Tm.Eqv A (Tm.subst τ (σ i)) (ρ i)) →
    Process.Eqv A ((P.subst σ).subst τ) (P.subst ρ)
  | _, _, _, .nil, _, _, _, _ => .nil
  | _, _, _, .out N M P, _, _, _, h =>
    .out (Tm.subst_subst_eqv N h) (Tm.subst_subst_eqv M h) (Process.subst_subst_eqv P h)
  | _, _, _, .inp N P, _, _, _, h =>
    .inp (Tm.subst_subst_eqv N h) (Process.subst_subst_eqv P (liftSubst_subst_eqv h))
  | _, _, _, .par P Q, _, _, _, h =>
    .par (Process.subst_subst_eqv P h) (Process.subst_subst_eqv Q h)
  | _, _, _, .bang P, _, _, _, h => .bang (Process.subst_subst_eqv P h)
  | _, _, _, .new P, _, _, _, h => .new (Process.subst_subst_eqv P (liftSubst_subst_eqv h))
  | _, _, _, .let_ D P Q, _, _, _, h =>
    .let_ (Expr.subst_subst_eqv D h) (Process.subst_subst_eqv P (liftSubst_subst_eqv h))
      (Process.subst_subst_eqv Q h)
  | _, _, _, .ite M P Q, _, _, _, h =>
    .ite (Tm.subst_subst_eqv M h) (Process.subst_subst_eqv P h) (Process.subst_subst_eqv Q h)
  | _, _, _, .event M P, _, _, _, h =>
    .event (Tm.subst_subst_eqv M h) (Process.subst_subst_eqv P h)

/-- Instantiating the last variable after substituting for the others is, modulo `E`,
substituting for all at once. -/
theorem subst_inst_eqv (P : Process F G (n + 1)) (σ : Fin n → Tm F 0) (M : Tm F 0) :
    Process.Eqv A ((P.subst (liftSubst σ)).inst M) (P.subst (Fin.snoc σ M)) :=
  Process.subst_subst_eqv P fun i => by
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

/-! ## Steps of a single process -/

/-- The step one process can make, by cases on it. -/
def StepOf (U : Finset ℕ) (l : Option (Act A.Msg)) (c' : Config F G) : Process F G 0 → Prop
  | .nil => l = none ∧ c' = ⟨U, 0⟩
  | .out N M P => l = some (.out (Tm.msg A N) (Tm.msg A M)) ∧ c' = ⟨U, {P}⟩
  | .inp N P => ∃ M, l = some (.inp (Tm.msg A N) (Tm.msg A M)) ∧ c' = ⟨U, {P.inst M}⟩
  | .par P Q => l = none ∧ c' = ⟨U, P ::ₘ {Q}⟩
  | .bang P => l = none ∧ c' = ⟨U, P ::ₘ {.bang P}⟩
  | .new P => ∃ k, k ∉ U ∧ l = some (.new k) ∧ c' = ⟨insert k U, {P.inst (.var (.inl k))}⟩
  | .let_ D P Q => (∃ M, Eval A D (some (Tm.msg A M)) ∧ l = none ∧ c' = ⟨U, {P.inst M}⟩) ∨
      (Eval A D none ∧ l = none ∧ c' = ⟨U, {Q}⟩)
  | .ite M P Q => (Tm.msg A M = Theory.Msg.app A.tt ![] ∧ l = none ∧ c' = ⟨U, {P}⟩) ∨
      (Tm.msg A M ≠ Theory.Msg.app A.tt ![] ∧ l = none ∧ c' = ⟨U, {Q}⟩)
  | .event M P => l = some (.event (Tm.msg A M)) ∧ c' = ⟨U, {P}⟩

theorem Step.singleton {c c' : Config F G} {l : Option (Act A.Msg)} (h : Step A c l c')
    {U : Finset ℕ} {X : Process F G 0} (hc : c = ⟨U, {X}⟩) : StepOf U l c' X := by
  cases h
  case comm N M Q N' P M' hN hM =>
    obtain ⟨rfl, hX⟩ := Config.mk.inj hc
    exact absurd ((Multiset.singleton_eq_cons_iff _).1 hX.symm).2 Multiset.cons_ne_zero
  all_goals
    obtain ⟨rfl, hX⟩ := Config.mk.inj hc
    obtain ⟨rfl, rfl⟩ := (Multiset.singleton_eq_cons_iff _).1 hX.symm
    dsimp only [StepOf]
    first
      | exact ⟨rfl, rfl⟩ | exact ⟨_, rfl, rfl⟩ | exact ⟨_, ‹_›, rfl, rfl⟩
      | exact Or.inl ⟨_, ‹_›, rfl, rfl⟩ | exact Or.inl ⟨‹_›, rfl, rfl⟩
      | exact Or.inr ⟨‹_›, rfl, rfl⟩

theorem Step.zero {c c' : Config F G} {l : Option (Act A.Msg)} (h : Step A c l c')
    {U : Finset ℕ} (hc : c = ⟨U, 0⟩) : False := by
  cases h <;> exact Multiset.cons_ne_zero (Config.mk.inj hc).2

theorem Runs.zero {c : Config F G} {t : Trace A.Msg} (h : Runs A c t) {U : Finset ℕ}
    (hc : c = ⟨U, 0⟩) : t = [] := by
  cases h with
  | nil => rfl
  | tau hs => exact (hs.zero hc).elim
  | act hs => exact (hs.zero hc).elim

/-- A step of some processes is a step of them beside others. -/
theorem Step.frame {U U' : Finset ℕ} {Ps Ps' : Multiset (Process F G 0)}
    {l : Option (Act A.Msg)} (h : Step A ⟨U, Ps⟩ l ⟨U', Ps'⟩) (Qs : Multiset (Process F G 0)) :
    Step A ⟨U, Ps + Qs⟩ l ⟨U', Ps' + Qs⟩ := by
  rcases h.names_eq with ⟨k, rfl, hk, rfl⟩ | ⟨hl, rfl⟩
  · simpa [Finset.insert_union] using h.add Qs (U₁ := U) fun k' hk' => by
      obtain rfl := Act.new.inj (Option.some.inj hk')
      exact hk
  · simpa using h.add Qs (U₁ := U) fun k hk => (hl k hk).elim

/-- A run is a run beside idle processes. -/
theorem Runs.add_right {c : Config F G} {t : Trace A.Msg} (h : Runs A c t)
    (Qs : Multiset (Process F G 0)) : Runs A ⟨c.names, c.procs + Qs⟩ t := by
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
theorem Runs.bang_unfold {c : Config F G} {t : Trace A.Msg} (h : Runs A c t)
    {P : Process F G 0} : ∀ {U : Finset ℕ} {Ps : Multiset (Process F G 0)},
      c = ⟨U, Ps + {.bang P}⟩ → ∃ n, Runs A ⟨U, Ps + Multiset.replicate n P⟩ t := by
  induction h with
  | nil c =>
    rintro U Ps rfl
    exact ⟨0, .nil _⟩
  | tau hs _ ih =>
    rintro U Ps rfl
    rcases hs.add_cases rfl with ⟨U', Ps', rfl, hs'⟩ | ⟨U', Qs', rfl, hs'⟩ |
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
    rcases hs.add_cases rfl with ⟨U', Ps', rfl, hs'⟩ | ⟨U', Qs', rfl, hs'⟩ |
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
theorem Runs.of_replicate {U : Finset ℕ} {P : Process F G 0} {t : Trace A.Msg} :
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

/-! ## The denotation and the runs -/

theorem nil_mem_denote : ∀ {n : ℕ} (P : Process F G n) (xs : Fin n → A.Msg), [] ∈ P.denote xs
  | _, .nil, _ => rfl
  | _, .out _ _ _, _ => Set.mem_insert _ _
  | _, .inp _ _, _ => Set.mem_iUnion.2 ⟨Theory.Msg.name 0, Set.mem_insert _ _⟩
  | _, .par P Q, xs => ⟨⟨![[], ([] : Trace A.Msg)], [], Fin.forall_fin_two.2 ⟨nil_mem_denote P xs,
      nil_mem_denote Q xs⟩, fun i => by fin_cases i <;> rfl, .nil⟩, List.nodup_nil⟩
  | _, .bang P, xs => ⟨⟨fun _ => [], [], fun _ => nil_mem_denote P xs, fun _ => rfl, .nil⟩,
      List.nodup_nil⟩
  | _, .new _, _ => Set.mem_iUnion.2 ⟨0, Set.mem_insert _ _⟩
  | _, .let_ D P Q, xs => by
    simp only [Process.denote]
    cases D.denote (env xs) with
    | none => exact nil_mem_denote Q xs
    | some a => exact nil_mem_denote P (Fin.snoc xs a)
  | _, .ite M P Q, xs => by
    simp only [Process.denote]
    split_ifs
    · exact nil_mem_denote P xs
    · exact nil_mem_denote Q xs
  | _, .event _ _, _ => Set.mem_insert _ _

/-- A trace of a run is a trace of the denotation. -/
theorem denote_of_runs : ∀ {n : ℕ} (P : Process F G n) (σ : Fin n → Tm F 0) {U : Finset ℕ}
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
    cases h with
    | nil => exact nil_mem_denote _ _
    | tau hs _ =>
      obtain ⟨h, -⟩ := Step.singleton hs rfl
      cases h
    | act hs hr =>
      obtain ⟨h, rfl⟩ := Step.singleton hs rfl
      obtain rfl := Option.some.inj h
      simp only [Process.denote]
      rw [Tm.msg_subst, Tm.msg_subst]
      exact Or.inr ⟨_, denote_of_runs P σ hr, rfl⟩
  | _, .inp N P, σ, U, t, h => by
    simp only [Process.subst] at h
    cases h with
    | nil => exact nil_mem_denote _ _
    | tau hs _ =>
      obtain ⟨_, h, -⟩ := Step.singleton hs rfl
      cases h
    | act hs hr =>
      obtain ⟨M, h, rfl⟩ := Step.singleton hs rfl
      obtain rfl := Option.some.inj h
      simp only [Process.denote]
      rw [Tm.msg_subst]
      refine Set.mem_iUnion.2 ⟨Tm.msg A M, Or.inr ⟨_, ?_, rfl⟩⟩
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
    have h0 : ({Process.bang (P.subst σ)} : Multiset (Process F G 0)) =
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
    cases h with
    | nil => exact nil_mem_denote _ _
    | tau hs hr =>
      simp only [Process.denote]
      rcases Step.singleton hs rfl with ⟨M, hD, -, rfl⟩ | ⟨hD, -, rfl⟩
      · rw [eval_iff, Expr.denote_subst_msg] at hD
        rw [← hD]
        have := denote_of_runs P (Fin.snoc σ M) (Runs.eqv hr (.cons (subst_inst_eqv P σ M) .zero))
        rw [msgs_snoc] at this
        exact this
      · rw [eval_iff, Expr.denote_subst_msg] at hD
        rw [← hD]
        exact denote_of_runs Q σ hr
    | act hs _ =>
      rcases Step.singleton hs rfl with ⟨_, _, h, -⟩ | ⟨_, h, -⟩ <;> cases h
  | _, .ite M P Q, σ, U, t, h => by
    simp only [Process.subst] at h
    cases h with
    | nil => exact nil_mem_denote _ _
    | tau hs hr =>
      simp only [Process.denote]
      rcases Step.singleton hs rfl with ⟨hM, -, rfl⟩ | ⟨hM, -, rfl⟩
      · rw [Tm.msg_subst] at hM
        rw [if_pos hM]
        exact denote_of_runs P σ hr
      · rw [Tm.msg_subst] at hM
        rw [if_neg hM]
        exact denote_of_runs Q σ hr
    | act hs _ =>
      rcases Step.singleton hs rfl with ⟨_, h, -⟩ | ⟨_, h, -⟩ <;> cases h
  | _, .event M P, σ, U, t, h => by
    simp only [Process.subst] at h
    cases h with
    | nil => exact nil_mem_denote _ _
    | tau hs _ =>
      obtain ⟨h, -⟩ := Step.singleton hs rfl
      cases h
    | act hs hr =>
      obtain ⟨h, rfl⟩ := Step.singleton hs rfl
      obtain rfl := Option.some.inj h
      simp only [Process.denote]
      rw [Tm.msg_subst]
      exact Or.inr ⟨_, denote_of_runs P σ hr, rfl⟩

theorem nonces_proj_subset {ι : Type} [DecidableEq ι] {s : TaggedTrace ι A.Msg} {t : Trace A.Msg}
    (hc : s.Comms t) (i : ι) : (s.proj i).nonces ⊆ t.nonces := by
  rw [hc.nonces]
  exact (Trace.nonces_sublist (List.filter_sublist.map _)).subset

/-- A trace of the denotation is a trace of a run, from any created names it avoids. -/
theorem runs_of_denote : ∀ {n : ℕ} (P : Process F G n) (σ : Fin n → Tm F 0) {U : Finset ℕ}
    {t : Trace A.Msg}, t ∈ P.denote (fun i => Tm.msg A (σ i)) → (∀ k ∈ t.nonces, k ∉ U) →
    Runs A ⟨U, {P.subst σ}⟩ t
  | _, .nil, σ, U, t, ht, _ => by
    obtain rfl := Set.mem_singleton_iff.1 ht
    exact .nil _
  | _, .out N M P, σ, U, t, ht, hU => by
    simp only [Process.denote] at ht
    simp only [Process.subst]
    rcases ht with rfl | ⟨t', ht', rfl⟩
    · exact .nil _
    · refine .act ?_ (runs_of_denote P σ ht' fun k hk =>
        hU k ((Trace.nonces_sublist (List.sublist_cons_self _ _)).subset hk))
      rw [← Tm.msg_subst, ← Tm.msg_subst]
      exact .out _ _ _
  | _, .inp N P, σ, U, t, ht, hU => by
    simp only [Process.denote] at ht
    simp only [Process.subst]
    obtain ⟨a, ht⟩ := Set.mem_iUnion.1 ht
    rcases ht with rfl | ⟨t', ht', rfl⟩
    · exact .nil _
    · obtain ⟨M, rfl⟩ := msg_surjective a
      have hr := runs_of_denote P (Fin.snoc σ M) (by rw [msgs_snoc]; exact ht') fun k hk =>
        hU k ((Trace.nonces_sublist (List.sublist_cons_self _ _)).subset hk)
      refine .act ?_ (Runs.eqv hr (.cons (subst_inst_eqv P σ M).symm .zero))
      rw [← Tm.msg_subst]
      exact .inp _ _ M
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
    rcases hD : D.denote (env fun i => Tm.msg A (σ i)) with _ | a
    · rw [hD] at ht
      exact .tau (.eval₂ _ _ _ (eval_iff.2 (by rw [Expr.denote_subst_msg, hD])))
        (runs_of_denote Q σ ht hU)
    · rw [hD] at ht
      obtain ⟨M, rfl⟩ := msg_surjective a
      have hr := runs_of_denote P (Fin.snoc σ M) (by rw [msgs_snoc]; exact ht) hU
      exact .tau (.eval₁ _ _ _ M (eval_iff.2 (by rw [Expr.denote_subst_msg, hD])))
        (Runs.eqv hr (.cons (subst_inst_eqv P σ M).symm .zero))
  | _, .ite M P Q, σ, U, t, ht, hU => by
    simp only [Process.denote] at ht
    simp only [Process.subst]
    split_ifs at ht with hM
    · exact .tau (.cond₁ _ _ _ (by rw [Tm.msg_subst]; exact hM)) (runs_of_denote P σ ht hU)
    · exact .tau (.cond₂ _ _ _ (by rw [Tm.msg_subst]; exact hM)) (runs_of_denote Q σ ht hU)
  | _, .event M P, σ, U, t, ht, hU => by
    simp only [Process.denote] at ht
    simp only [Process.subst]
    rcases ht with rfl | ⟨t', ht', rfl⟩
    · exact .nil _
    · refine .act ?_ (runs_of_denote P σ ht' fun k hk =>
        hU k ((Trace.nonces_sublist (List.sublist_cons_self _ _)).subset hk))
      rw [← Tm.msg_subst]
      exact .event _ _

variable (A)

/-- Adequacy: a closed process denotes its weak traces. -/
theorem denote_eq_traces (P : Process F G 0) :
    P.denote finZeroElim = Config.traces A ⟨∅, {P}⟩ := by
  ext t
  have hσ : (fun i : Fin 0 => Tm.msg A ((finZeroElim : Fin 0 → Tm F 0) i)) = finZeroElim :=
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
