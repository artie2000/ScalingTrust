/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.Specification.Semantics

/-!
# Equality modulo `E` and the invariance of the semantics

The manual reads its rules modulo `=_E`: a step on a term `M' =_E M` counts as a step on
`M`.  Processes here are terms, so this is a theorem about them.  Terms under binders are
equal modulo `E` when they are equal in every environment (`Tm.Eqv`), and expressions and
processes when they have the same shape and equal terms (`Expr.Eqv`, `Process.Eqv`).
Substitution respects these; a term step of an expression is matched by a step of any
expression equal to it modulo `E` (`TStep.eqv`), and a step of a multiset of processes by
a step of any multiset equal to it modulo `E` (`Step.eqv`); so the weak traces of a
configuration depend only on its processes modulo `E` (`traces_eqv`), and the term that a
communication or a `let` substitutes, among those of a message, does not matter
(`traces_inst`).
-/

namespace ProVerif.Specification

open FirstOrder FirstOrder.Language ProVerif.TraceSemantics

variable {F G Ev : Sig} {A : Model F G Ev} {n m : ℕ}

/-! ## Terms -/

/-- Terms under `n` binders equal modulo `E`: equal in every environment. -/
def Tm.Eqv (A : Model F G Ev) (M M' : Tm F Ev n) : Prop :=
  ∀ xs : Fin n → A.Msg, M.realize (env xs) = M'.realize (env xs)

theorem Tm.Eqv.refl (M : Tm F Ev n) : Tm.Eqv A M M := fun _ => rfl

theorem Tm.Eqv.symm {M M' : Tm F Ev n} (h : Tm.Eqv A M M') : Tm.Eqv A M' M :=
  fun xs => (h xs).symm

/-- Closed terms are equal modulo `E` when their messages are. -/
theorem Tm.eqv_iff {M M' : Tm F Ev 0} : Tm.Eqv A M M' ↔ Tm.msg A M = Tm.msg A M' :=
  ⟨fun h => h finZeroElim, fun h xs => by
    rw [show xs = finZeroElim from funext fun i => i.elim0]
    exact h⟩

theorem Tm.Eqv.subst {M M' : Tm F Ev n} (h : Tm.Eqv A M M') {σ σ' : Fin n → Tm F Ev m}
    (hσ : ∀ i, Tm.Eqv A (σ i) (σ' i)) : Tm.Eqv A (Tm.subst σ M) (Tm.subst σ' M') := fun xs => by
  rw [Tm.realize_subst, Tm.realize_subst,
    show (fun i => (σ' i).realize (env xs)) = fun i => (σ i).realize (env xs) from
      funext fun i => (hσ i xs).symm]
  exact h _

theorem liftSubst_eqv {σ σ' : Fin n → Tm F Ev m} (hσ : ∀ i, Tm.Eqv A (σ i) (σ' i))
    (i : Fin (n + 1)) : Tm.Eqv A (liftSubst σ i) (liftSubst σ' i) := fun xs => by
  rw [← Fin.snoc_init_self xs, realize_liftSubst, realize_liftSubst,
    show (fun j => (σ' j).realize (env (Fin.init xs))) =
      fun j => (σ j).realize (env (Fin.init xs)) from funext fun j => (hσ j _).symm]

theorem snoc_eqv {M M' : Tm F Ev n} (hM : Tm.Eqv A M M') (i : Fin (n + 1)) :
    Tm.Eqv A (Fin.snoc (α := fun _ => Tm F Ev n) (fun i => .var (.inr i)) M i)
      (Fin.snoc (α := fun _ => Tm F Ev n) (fun i => .var (.inr i)) M' i) := by
  induction i using Fin.lastCases with
  | last => simpa only [Fin.snoc_last] using hM
  | cast j => simpa only [Fin.snoc_castSucc] using Tm.Eqv.refl (.var (.inr j))

/-! ## Expressions and processes -/

/-- Expressions equal modulo `E`: the same shape, with terms equal modulo `E`. -/
inductive Expr.Eqv (A : Model F G Ev) : ∀ {n : ℕ}, Expr F G Ev n → Expr F G Ev n → Prop
  | term {n : ℕ} {M M' : Tm F Ev n} : Tm.Eqv A M M' → Eqv A (.term M) (.term M')
  | ctor {n k : ℕ} (f : Sig.cons F Ev k) {args args' : Fin k → Expr F G Ev n} :
      (∀ i, Eqv A (args i) (args' i)) → Eqv A (.ctor f args) (.ctor f args')
  | dtor {n k : ℕ} (g : Sig.withBuiltin G k) {args args' : Fin k → Expr F G Ev n} :
      (∀ i, Eqv A (args i) (args' i)) → Eqv A (.dtor g args) (.dtor g args')
  | fail {n : ℕ} : Eqv A (.fail (n := n)) .fail
  | new {n : ℕ} {D D' : Expr F G Ev (n + 1)} : Eqv A D D' → Eqv A (.new D) (.new D')
  | ite {n : ℕ} {C C' D₁ D₁' D₂ D₂' : Expr F G Ev n} : Eqv A C C' → Eqv A D₁ D₁' →
      Eqv A D₂ D₂' → Eqv A (.ite C D₁ D₂) (.ite C' D₁' D₂')
  | let_ {n : ℕ} {D D' : Expr F G Ev n} {D₁ D₁' : Expr F G Ev (n + 1)} {D₂ D₂' : Expr F G Ev n} :
      Eqv A D D' → Eqv A D₁ D₁' → Eqv A D₂ D₂' → Eqv A (.let_ D D₁ D₂) (.let_ D' D₁' D₂')
  | event {n k : ℕ} (e : Ev k) {args args' : Fin k → Expr F G Ev n} {D D' : Expr F G Ev n} :
      (∀ i, Eqv A (args i) (args' i)) → Eqv A D D' → Eqv A (.event e args D) (.event e args' D')

theorem Expr.Eqv.refl : ∀ {n : ℕ} (D : Expr F G Ev n), Expr.Eqv A D D
  | _, .term M => .term (Tm.Eqv.refl M)
  | _, .ctor f args => .ctor f fun i => Expr.Eqv.refl (args i)
  | _, .dtor g args => .dtor g fun i => Expr.Eqv.refl (args i)
  | _, .fail => .fail
  | _, .new D => .new (Expr.Eqv.refl D)
  | _, .ite C D₁ D₂ => .ite (Expr.Eqv.refl C) (Expr.Eqv.refl D₁) (Expr.Eqv.refl D₂)
  | _, .let_ D D₁ D₂ => .let_ (Expr.Eqv.refl D) (Expr.Eqv.refl D₁) (Expr.Eqv.refl D₂)
  | _, .event e args D => .event e (fun i => Expr.Eqv.refl (args i)) (Expr.Eqv.refl D)

theorem Expr.Eqv.symm {D D' : Expr F G Ev n} (h : Expr.Eqv A D D') : Expr.Eqv A D' D := by
  induction h with
  | term h => exact .term h.symm
  | ctor f _ ih => exact .ctor f ih
  | dtor g _ ih => exact .dtor g ih
  | fail => exact .fail
  | new _ ih => exact .new ih
  | ite _ _ _ ih ih₁ ih₂ => exact .ite ih ih₁ ih₂
  | let_ _ _ _ ih ih₁ ih₂ => exact .let_ ih ih₁ ih₂
  | event e _ _ ih ih' => exact .event e ih ih'

theorem Expr.Eqv.subst {D D' : Expr F G Ev n} (h : Expr.Eqv A D D') :
    ∀ {m : ℕ} {σ σ' : Fin n → Tm F Ev m}, (∀ i, Tm.Eqv A (σ i) (σ' i)) →
      Expr.Eqv A (D.subst σ) (D'.subst σ') := by
  induction h with
  | term h => exact fun hσ => .term (h.subst hσ)
  | ctor f _ ih => exact fun hσ => .ctor f fun i => ih i hσ
  | dtor g _ ih => exact fun hσ => .dtor g fun i => ih i hσ
  | fail => exact fun _ => .fail
  | new _ ih => exact fun hσ => .new (ih (liftSubst_eqv hσ))
  | ite _ _ _ ih ih₁ ih₂ => exact fun hσ => .ite (ih hσ) (ih₁ hσ) (ih₂ hσ)
  | let_ _ _ _ ih ih₁ ih₂ => exact fun hσ => .let_ (ih hσ) (ih₁ (liftSubst_eqv hσ)) (ih₂ hσ)
  | event e _ _ ih ih' => exact fun hσ => .event e (fun i => ih i hσ) (ih' hσ)

/-- Instantiation respects equality modulo `E`. -/
theorem Expr.Eqv.inst {D D' : Expr F G Ev (n + 1)} (h : Expr.Eqv A D D') {M M' : Tm F Ev n}
    (hM : Tm.Eqv A M M') : Expr.Eqv A (D.inst M) (D'.inst M') :=
  h.subst (snoc_eqv hM)

/-- `fail` is equal modulo `E` only to `fail`. -/
theorem Expr.Eqv.eq_fail {E : Expr F G Ev n} (h : Expr.Eqv A .fail E) : E = .fail := by
  cases h
  rfl

/-- A term is equal modulo `E` only to terms. -/
theorem Expr.Eqv.isTerm {V E : Expr F G Ev n} (h : Expr.Eqv A V E) (hV : V.IsTerm) :
    E.IsTerm := by
  induction hV generalizing E with
  | term M =>
    cases h with
    | term _ => exact .term _
  | ctor f _ ih =>
    cases h with
    | ctor _ hargs' => exact .ctor f fun i => ih i (hargs' i)

/-- A may-fail term is equal modulo `E` only to may-fail terms. -/
theorem Expr.Eqv.isValue {V E : Expr F G Ev n} (h : Expr.Eqv A V E) (hV : V.IsValue) :
    E.IsValue := by
  rcases hV with hV | rfl
  · exact Or.inl (h.isTerm hV)
  · exact Or.inr h.eq_fail

/-- A may-fail term is equal modulo `E` only to may-fail terms with its value. -/
theorem Expr.Eqv.val {V E : Expr F G Ev 0} (h : Expr.Eqv A V E) {u : Option A.Msg}
    (hV : Val A V u) : Val A E u := by
  induction hV generalizing E with
  | term M =>
    cases h with
    | term hM =>
      rw [Tm.eqv_iff.1 hM]
      exact .term _
  | ctor f _ ih =>
    cases h with
    | ctor _ hargs' => exact .ctor f fun i => ih i (hargs' i)
  | fail =>
    cases h
    exact .fail

theorem update_eqv {k : ℕ} {args args' : Fin k → Expr F G Ev n}
    (h : ∀ i, Expr.Eqv A (args i) (args' i)) (i : Fin k) {D D' : Expr F G Ev n}
    (hD : Expr.Eqv A D D') (j : Fin k) :
    Expr.Eqv A (Function.update args i D j) (Function.update args' i D' j) := by
  by_cases hj : j = i
  · subst hj
    simpa only [Function.update_self] using hD
  · simpa only [Function.update_of_ne hj] using h j

/-- The `i`-th of expressions equal modulo `E` to `fail` is `fail`. -/
theorem eq_fail_of_eqv {k : ℕ} {args args' : Fin k → Expr F G Ev n}
    (h : ∀ i, Expr.Eqv A (args i) (args' i)) {i : Fin k} (hi : args i = .fail) :
    args' i = .fail := by
  have h' := h i
  rw [hi] at h'
  exact h'.eq_fail

/-- Processes equal modulo `E`: the same shape, with expressions equal modulo `E`. -/
inductive Process.Eqv (A : Model F G Ev) : ∀ {n : ℕ}, Process F G Ev n → Process F G Ev n → Prop
  | nil {n : ℕ} : Eqv A (.nil (n := n)) .nil
  | out {n : ℕ} {N N' M M' : Expr F G Ev n} {P P' : Process F G Ev n} : Expr.Eqv A N N' →
      Expr.Eqv A M M' → Eqv A P P' → Eqv A (.out N M P) (.out N' M' P')
  | inp {n : ℕ} {N N' : Expr F G Ev n} {P P' : Process F G Ev (n + 1)} : Expr.Eqv A N N' →
      Eqv A P P' → Eqv A (.inp N P) (.inp N' P')
  | par {n : ℕ} {P P' Q Q' : Process F G Ev n} : Eqv A P P' → Eqv A Q Q' →
      Eqv A (.par P Q) (.par P' Q')
  | bang {n : ℕ} {P P' : Process F G Ev n} : Eqv A P P' → Eqv A (.bang P) (.bang P')
  | new {n : ℕ} {P P' : Process F G Ev (n + 1)} : Eqv A P P' → Eqv A (.new P) (.new P')
  | let_ {n : ℕ} {D D' : Expr F G Ev n} {P P' : Process F G Ev (n + 1)}
      {Q Q' : Process F G Ev n} : Expr.Eqv A D D' → Eqv A P P' → Eqv A Q Q' →
      Eqv A (.let_ D P Q) (.let_ D' P' Q')
  | ite {n : ℕ} {C C' : Expr F G Ev n} {P P' Q Q' : Process F G Ev n} : Expr.Eqv A C C' →
      Eqv A P P' → Eqv A Q Q' → Eqv A (.ite C P Q) (.ite C' P' Q')
  | event {n k : ℕ} (e : Ev k) {args args' : Fin k → Expr F G Ev n} {P P' : Process F G Ev n} :
      (∀ i, Expr.Eqv A (args i) (args' i)) → Eqv A P P' →
      Eqv A (.event e args P) (.event e args' P')

theorem Process.Eqv.refl : ∀ {n : ℕ} (P : Process F G Ev n), Process.Eqv A P P
  | _, .nil => .nil
  | _, .out N M P => .out (Expr.Eqv.refl N) (Expr.Eqv.refl M) (Process.Eqv.refl P)
  | _, .inp N P => .inp (Expr.Eqv.refl N) (Process.Eqv.refl P)
  | _, .par P Q => .par (Process.Eqv.refl P) (Process.Eqv.refl Q)
  | _, .bang P => .bang (Process.Eqv.refl P)
  | _, .new P => .new (Process.Eqv.refl P)
  | _, .let_ D P Q => .let_ (Expr.Eqv.refl D) (Process.Eqv.refl P) (Process.Eqv.refl Q)
  | _, .ite C P Q => .ite (Expr.Eqv.refl C) (Process.Eqv.refl P) (Process.Eqv.refl Q)
  | _, .event e args P => .event e (fun i => Expr.Eqv.refl (args i)) (Process.Eqv.refl P)

theorem Process.Eqv.symm {P P' : Process F G Ev n} (h : Process.Eqv A P P') :
    Process.Eqv A P' P := by
  induction h with
  | nil => exact .nil
  | out hN hM _ ih => exact .out hN.symm hM.symm ih
  | inp hN _ ih => exact .inp hN.symm ih
  | par _ _ ih₁ ih₂ => exact .par ih₁ ih₂
  | bang _ ih => exact .bang ih
  | new _ ih => exact .new ih
  | let_ hD _ _ ih₁ ih₂ => exact .let_ hD.symm ih₁ ih₂
  | ite hC _ _ ih₁ ih₂ => exact .ite hC.symm ih₁ ih₂
  | event e hargs _ ih => exact .event e (fun i => (hargs i).symm) ih

theorem Process.Eqv.subst {P P' : Process F G Ev n} (h : Process.Eqv A P P') :
    ∀ {m : ℕ} {σ σ' : Fin n → Tm F Ev m}, (∀ i, Tm.Eqv A (σ i) (σ' i)) →
      Process.Eqv A (P.subst σ) (P'.subst σ') := by
  induction h with
  | nil => exact fun _ => .nil
  | out hN hM _ ih => exact fun hσ => .out (hN.subst hσ) (hM.subst hσ) (ih hσ)
  | inp hN _ ih => exact fun hσ => .inp (hN.subst hσ) (ih (liftSubst_eqv hσ))
  | par _ _ ih₁ ih₂ => exact fun hσ => .par (ih₁ hσ) (ih₂ hσ)
  | bang _ ih => exact fun hσ => .bang (ih hσ)
  | new _ ih => exact fun hσ => .new (ih (liftSubst_eqv hσ))
  | let_ hD _ _ ih₁ ih₂ => exact fun hσ => .let_ (hD.subst hσ) (ih₁ (liftSubst_eqv hσ)) (ih₂ hσ)
  | ite hC _ _ ih₁ ih₂ => exact fun hσ => .ite (hC.subst hσ) (ih₁ hσ) (ih₂ hσ)
  | event e hargs _ ih => exact fun hσ => .event e (fun i => (hargs i).subst hσ) (ih hσ)

/-- Instantiation respects equality modulo `E`. -/
theorem Process.Eqv.inst {P P' : Process F G Ev (n + 1)} (h : Process.Eqv A P P')
    {M M' : Tm F Ev n} (hM : Tm.Eqv A M M') : Process.Eqv A (P.inst M) (P'.inst M') :=
  h.subst (snoc_eqv hM)

/-! ## Steps -/

/-- A term step of an expression is matched by a step of any expression equal to it
modulo `E`, with the same label and created names. -/
theorem TStep.eqv {U U' : Finset ℕ} {D D' : Expr F G Ev 0} {l : Option (Act A.Msg)}
    (h : TStep A U D l U' D') : ∀ {E : Expr F G Ev 0}, Expr.Eqv A D E →
      ∃ E', TStep A U E l U' E' ∧ Expr.Eqv A D' E' := by
  induction h with
  | ctor_fail f i hv hi =>
    intro E hE
    cases hE with
    | ctor _ hargs' =>
      exact ⟨_, .ctor_fail f i (fun j => (hargs' j).isValue (hv j)) (eq_fail_of_eqv hargs' hi),
        .fail⟩
  | dtor g M hargs hr =>
    intro E hE
    cases hE with
    | dtor _ hargs' => exact ⟨_, .dtor g M (fun i => (hargs' i).val (hargs i)) hr, Expr.Eqv.refl _⟩
  | dtor_fail g hargs hr =>
    intro E hE
    cases hE with
    | dtor _ hargs' => exact ⟨_, .dtor_fail g (fun i => (hargs' i).val (hargs i)) hr, .fail⟩
  | new D k hk =>
    intro E hE
    cases hE with
    | new hD => exact ⟨_, .new _ k hk, hD.inst (Tm.Eqv.refl _)⟩
  | ite₁ D₁ D₂ hC =>
    intro E hE
    cases hE with
    | ite hC' hD₁ hD₂ => exact ⟨_, .ite₁ _ _ (hC'.val hC), hD₁⟩
  | ite₂ D₁ D₂ hC hm =>
    intro E hE
    cases hE with
    | ite hC' hD₁ hD₂ => exact ⟨_, .ite₂ _ _ (hC'.val hC) hm, hD₂⟩
  | ite_fail D₁ D₂ =>
    intro E hE
    cases hE with
    | ite hC hD₁ hD₂ =>
      cases hC
      exact ⟨_, .ite_fail _ _, .fail⟩
  | let₁ M' D₁ D₂ hD hM' =>
    intro E hE
    cases hE with
    | let_ hD' hD₁ hD₂ => exact ⟨_, .let₁ M' _ _ (hD'.val hD) hM', hD₁.inst (Tm.Eqv.refl _)⟩
  | let₂ D₁ D₂ =>
    intro E hE
    cases hE with
    | let_ hD hD₁ hD₂ =>
      cases hD
      exact ⟨_, .let₂ _ _, hD₂⟩
  | event e D hargs =>
    intro E hE
    cases hE with
    | event _ hargs' hD => exact ⟨_, .event e _ (fun i => (hargs' i).val (hargs i)), hD⟩
  | event_fail e i D hv hi =>
    intro E hE
    cases hE with
    | event _ hargs' hD =>
      exact ⟨_, .event_fail e i _ (fun j => (hargs' j).isValue (hv j)) (eq_fail_of_eqv hargs' hi),
        .fail⟩
  | ctor_ctx f i hv _ ih =>
    intro E hE
    cases hE with
    | ctor _ hargs' =>
      obtain ⟨E', hs', hE'⟩ := ih (hargs' i)
      exact ⟨_, .ctor_ctx f i (fun j hj => (hargs' j).isValue (hv j hj)) hs',
        .ctor f (update_eqv hargs' i hE')⟩
  | dtor_ctx g i hv _ ih =>
    intro E hE
    cases hE with
    | dtor _ hargs' =>
      obtain ⟨E', hs', hE'⟩ := ih (hargs' i)
      exact ⟨_, .dtor_ctx g i (fun j hj => (hargs' j).isValue (hv j hj)) hs',
        .dtor g (update_eqv hargs' i hE')⟩
  | ite_ctx D₁ D₂ _ ih =>
    intro E hE
    cases hE with
    | ite hC hD₁ hD₂ =>
      obtain ⟨E', hs', hE'⟩ := ih hC
      exact ⟨_, .ite_ctx _ _ hs', .ite hE' hD₁ hD₂⟩
  | let_ctx D₁ D₂ _ ih =>
    intro E hE
    cases hE with
    | let_ hD hD₁ hD₂ =>
      obtain ⟨E', hs', hE'⟩ := ih hD
      exact ⟨_, .let_ctx _ _ hs', .let_ hE' hD₁ hD₂⟩
  | event_ctx e i D hv _ ih =>
    intro E hE
    cases hE with
    | event _ hargs' hD =>
      obtain ⟨E', hs', hE'⟩ := ih (hargs' i)
      exact ⟨_, .event_ctx e i _ (fun j hj => (hargs' j).isValue (hv j hj)) hs',
        .event e (update_eqv hargs' i hE') hD⟩

/-- A run of a term configuration is matched by a run of any expression equal to it modulo
`E`, with the same trace and created names. -/
theorem TRuns.eqv {U U' : Finset ℕ} {D D' : Expr F G Ev 0} {t : Trace A.Msg}
    (h : TRuns A U D t U' D') : ∀ {E : Expr F G Ev 0}, Expr.Eqv A D E →
      ∃ E', TRuns A U E t U' E' ∧ Expr.Eqv A D' E' := by
  induction h with
  | nil U D => exact fun hE => ⟨_, .nil _ _, hE⟩
  | tau hs _ ih =>
    intro E hE
    obtain ⟨E₁, hs', hE₁⟩ := hs.eqv hE
    obtain ⟨E', hr', hE'⟩ := ih hE₁
    exact ⟨E', .tau hs' hr', hE'⟩
  | act hs _ ih =>
    intro E hE
    obtain ⟨E₁, hs', hE₁⟩ := hs.eqv hE
    obtain ⟨E', hr', hE'⟩ := ih hE₁
    exact ⟨E', .act hs' hr', hE'⟩

/-- A step of a multiset of processes is matched by a step of any multiset equal to it
modulo `E`, with the same label and created names. -/
theorem Step.eqv {U U' : Finset ℕ} {Ps Ps' Qs : Multiset (Process F G Ev 0)}
    {l : Option (Act A.Msg)} (h : Step A ⟨U, Ps⟩ l ⟨U', Ps'⟩)
    (hr : Multiset.Rel (Process.Eqv A) Ps Qs) :
    ∃ Qs', Step A ⟨U, Qs⟩ l ⟨U', Qs'⟩ ∧ Multiset.Rel (Process.Eqv A) Ps' Qs' := by
  cases h with
  | nil =>
    obtain ⟨R, Qs₀, hR, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr
    cases hR
    exact ⟨Qs₀, .nil, hrest⟩
  | par P Q =>
    obtain ⟨R, Qs₀, hR, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr
    cases hR with
    | par hP hQ => exact ⟨_, .par _ _, .cons hP (.cons hQ hrest)⟩
  | bang P =>
    obtain ⟨R, Qs₀, hR, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr
    cases hR with
    | bang hP => exact ⟨_, .bang _, .cons hP (.cons (.bang hP) hrest)⟩
  | new P k hk =>
    obtain ⟨R, Qs₀, hR, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr
    cases hR with
    | new hP => exact ⟨_, .new _ k hk, .cons (hP.inst (Tm.Eqv.refl _)) hrest⟩
  | comm Q P M' hN hM hN' hM' =>
    obtain ⟨R₁, Qs₁, hR₁, hr₁, rfl⟩ := Multiset.rel_cons_left.1 hr
    obtain ⟨R₂, Qs₀, hR₂, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr₁
    cases hR₁ with
    | out hN₁ hM₁ hQ =>
      cases hR₂ with
      | inp hN₁' hP =>
        exact ⟨_, .comm _ _ M' (hN₁.val hN) (hM₁.val hM) (hN₁'.val hN') hM',
          .cons hQ (.cons (hP.inst (Tm.Eqv.refl _)) hrest)⟩
  | eval₁ M' P Q hD hM' =>
    obtain ⟨R, Qs₀, hR, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr
    cases hR with
    | let_ hD' hP hQ =>
      exact ⟨_, .eval₁ M' _ _ (hD'.val hD) hM', .cons (hP.inst (Tm.Eqv.refl _)) hrest⟩
  | eval₂ P Q =>
    obtain ⟨R, Qs₀, hR, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr
    cases hR with
    | let_ hD hP hQ =>
      cases hD
      exact ⟨_, .eval₂ _ _, .cons hQ hrest⟩
  | cond₁ P Q hC =>
    obtain ⟨R, Qs₀, hR, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr
    cases hR with
    | ite hC' hP hQ => exact ⟨_, .cond₁ _ _ (hC'.val hC), .cons hP hrest⟩
  | cond₂ P Q hC hm =>
    obtain ⟨R, Qs₀, hR, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr
    cases hR with
    | ite hC' hP hQ => exact ⟨_, .cond₂ _ _ (hC'.val hC) hm, .cons hQ hrest⟩
  | event e P hargs =>
    obtain ⟨R, Qs₀, hR, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr
    cases hR with
    | event _ hargs' hP => exact ⟨_, .event e _ (fun i => (hargs' i).val (hargs i)), .cons hP hrest⟩
  | out P hN hM =>
    obtain ⟨R, Qs₀, hR, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr
    cases hR with
    | out hN' hM' hP => exact ⟨_, .out _ (hN'.val hN) (hM'.val hM), .cons hP hrest⟩
  | inp P M hN =>
    obtain ⟨R, Qs₀, hR, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr
    cases hR with
    | inp hN' hP => exact ⟨_, .inp _ M (hN'.val hN), .cons (hP.inst (Tm.Eqv.refl _)) hrest⟩
  | out_ctx₁ M P hs =>
    obtain ⟨R, Qs₀, hR, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr
    cases hR with
    | out hN hM hP =>
      obtain ⟨N₁', hs', hN'⟩ := hs.eqv hN
      exact ⟨_, .out_ctx₁ _ _ hs', .cons (.out hN' hM hP) hrest⟩
  | out_ctx₂ N P hNv hs =>
    obtain ⟨R, Qs₀, hR, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr
    cases hR with
    | out hN hM hP =>
      obtain ⟨M₁', hs', hM'⟩ := hs.eqv hM
      exact ⟨_, .out_ctx₂ _ _ (hN.isValue hNv) hs', .cons (.out hN hM' hP) hrest⟩
  | inp_ctx P hs =>
    obtain ⟨R, Qs₀, hR, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr
    cases hR with
    | inp hN hP =>
      obtain ⟨N₁', hs', hN'⟩ := hs.eqv hN
      exact ⟨_, .inp_ctx _ hs', .cons (.inp hN' hP) hrest⟩
  | ite_ctx P Q hs =>
    obtain ⟨R, Qs₀, hR, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr
    cases hR with
    | ite hC hP hQ =>
      obtain ⟨C₁', hs', hC'⟩ := hs.eqv hC
      exact ⟨_, .ite_ctx _ _ hs', .cons (.ite hC' hP hQ) hrest⟩
  | let_ctx P Q hs =>
    obtain ⟨R, Qs₀, hR, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr
    cases hR with
    | let_ hD hP hQ =>
      obtain ⟨D₁', hs', hD'⟩ := hs.eqv hD
      exact ⟨_, .let_ctx _ _ hs', .cons (.let_ hD' hP hQ) hrest⟩
  | event_ctx e i P hv hs =>
    obtain ⟨R, Qs₀, hR, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr
    cases hR with
    | event _ hargs' hP =>
      obtain ⟨E', hs', hE'⟩ := hs.eqv (hargs' i)
      exact ⟨_, .event_ctx e i _ (fun j hj => (hargs' j).isValue (hv j hj)) hs',
        .cons (.event e (update_eqv hargs' i hE') hP) hrest⟩

/-- A run of a multiset of processes is a run of any multiset equal to it modulo `E`. -/
theorem Runs.eqv {c : Config F G Ev} {t : Trace A.Msg} (h : Runs A c t) :
    ∀ {Qs : Multiset (Process F G Ev 0)}, Multiset.Rel (Process.Eqv A) c.procs Qs →
      Runs A ⟨c.names, Qs⟩ t := by
  induction h with
  | nil c => exact fun _ => .nil _
  | @tau c c' t hs _ ih =>
    obtain ⟨U, Ps⟩ := c
    obtain ⟨U', Ps'⟩ := c'
    intro Qs hr
    obtain ⟨Qs', hs', hr'⟩ := hs.eqv hr
    exact .tau hs' (ih hr')
  | @act c c' a t hs _ ih =>
    obtain ⟨U, Ps⟩ := c
    obtain ⟨U', Ps'⟩ := c'
    intro Qs hr
    obtain ⟨Qs', hs', hr'⟩ := hs.eqv hr
    exact .act hs' (ih hr')

/-- The weak traces of a configuration depend only on its processes modulo `E`. -/
theorem traces_eqv {U : Finset ℕ} {Ps Qs : Multiset (Process F G Ev 0)}
    (h : Multiset.Rel (Process.Eqv A) Ps Qs) :
    Config.traces A ⟨U, Ps⟩ = Config.traces A ⟨U, Qs⟩ :=
  Set.ext fun _ => ⟨fun ht => Runs.eqv ht h,
    fun ht => Runs.eqv ht (Multiset.rel_flip.1 (h.mono fun _ _ _ _ h => h.symm))⟩

/-- A step on a term `M' =_E M` counts as a step on `M`: the term that a communication or
a `let` substitutes does not matter beyond its message. -/
theorem traces_inst {U : Finset ℕ} {P : Process F G Ev 1} {M M' : Tm F Ev 0}
    (h : Tm.msg A M = Tm.msg A M') (Ps : Multiset (Process F G Ev 0)) :
    Config.traces A ⟨U, P.inst M ::ₘ Ps⟩ = Config.traces A ⟨U, P.inst M' ::ₘ Ps⟩ :=
  traces_eqv (.cons ((Process.Eqv.refl P).inst (Tm.eqv_iff.2 h))
    (Multiset.rel_refl_of_refl_on fun Q _ => Process.Eqv.refl Q))

end ProVerif.Specification
