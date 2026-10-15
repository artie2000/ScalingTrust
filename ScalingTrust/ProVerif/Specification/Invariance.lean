/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.Specification.Semantics

/-!
# Equality modulo `E` and the invariance of the semantics

The survey reads its definitions modulo `=_E`: a step on a term `M' =_E M` counts as a
step on `M`.  Processes here are terms, so this is a theorem about them.  Terms under
binders are equal modulo `E` when they are equal in every environment (`Tm.Eqv`), and
expressions and processes when they have the same shape and equal terms (`Expr.Eqv`,
`Process.Eqv`).  Substitution and evaluation respect these; a step of a multiset of
processes is matched by a step of any multiset equal to it modulo `E` (`Step.eqv`); so
the weak traces of a configuration depend only on its processes modulo `E`
(`traces_eqv`), and the term that (Red I/O') or (Red Eval 1) substitutes, among those
of a message, does not matter (`traces_inst`).
-/

namespace ProVerif.Specification

open FirstOrder FirstOrder.Language ProVerif.TraceSemantics

variable {F G : Sig} {A : Model F G} {n m : ℕ}

/-! ## Terms -/

/-- Terms under `n` binders equal modulo `E`: equal in every environment. -/
def Tm.Eqv (A : Model F G) (M M' : Tm F n) : Prop :=
  ∀ xs : Fin n → A.Msg, M.realize (env xs) = M'.realize (env xs)

theorem Tm.Eqv.refl (M : Tm F n) : Tm.Eqv A M M := fun _ => rfl

theorem Tm.Eqv.symm {M M' : Tm F n} (h : Tm.Eqv A M M') : Tm.Eqv A M' M :=
  fun xs => (h xs).symm

/-- Closed terms are equal modulo `E` when their messages are. -/
theorem Tm.eqv_iff {M M' : Tm F 0} : Tm.Eqv A M M' ↔ Tm.msg A M = Tm.msg A M' :=
  ⟨fun h => h finZeroElim, fun h xs => by
    rw [show xs = finZeroElim from funext fun i => i.elim0]
    exact h⟩

theorem Tm.Eqv.subst {M M' : Tm F n} (h : Tm.Eqv A M M') {σ σ' : Fin n → Tm F m}
    (hσ : ∀ i, Tm.Eqv A (σ i) (σ' i)) : Tm.Eqv A (Tm.subst σ M) (Tm.subst σ' M') := fun xs => by
  rw [Tm.realize_subst, Tm.realize_subst,
    show (fun i => (σ' i).realize (env xs)) = fun i => (σ i).realize (env xs) from
      funext fun i => (hσ i xs).symm]
  exact h _

theorem liftSubst_eqv {σ σ' : Fin n → Tm F m} (hσ : ∀ i, Tm.Eqv A (σ i) (σ' i))
    (i : Fin (n + 1)) : Tm.Eqv A (liftSubst σ i) (liftSubst σ' i) := fun xs => by
  rw [← Fin.snoc_init_self xs, realize_liftSubst, realize_liftSubst,
    show (fun j => (σ' j).realize (env (Fin.init xs))) =
      fun j => (σ j).realize (env (Fin.init xs)) from funext fun j => (hσ j _).symm]

/-! ## Expressions and processes -/

/-- Expressions equal modulo `E`: the same shape, with terms equal modulo `E`. -/
inductive Expr.Eqv (A : Model F G) : Expr F G (ℕ ⊕ Fin n) → Expr F G (ℕ ⊕ Fin n) → Prop
  | term {M M'} : Tm.Eqv A M M' → Eqv A (.term M) (.term M')
  | ctor {k : ℕ} (f : F k) {args args'} : (∀ i, Eqv A (args i) (args' i)) →
      Eqv A (.ctor f args) (.ctor f args')
  | dtor {k : ℕ} (g : G k) {args args'} : (∀ i, Eqv A (args i) (args' i)) →
      Eqv A (.dtor g args) (.dtor g args')
  | fail : Eqv A .fail .fail

theorem Expr.Eqv.refl : ∀ D : Expr F G (ℕ ⊕ Fin n), Expr.Eqv A D D
  | .term M => .term (Tm.Eqv.refl M)
  | .ctor f args => .ctor f fun i => Expr.Eqv.refl (args i)
  | .dtor g args => .dtor g fun i => Expr.Eqv.refl (args i)
  | .fail => .fail

theorem Expr.Eqv.symm {D D' : Expr F G (ℕ ⊕ Fin n)} (h : Expr.Eqv A D D') :
    Expr.Eqv A D' D := by
  induction h with
  | term h => exact .term h.symm
  | ctor f _ ih => exact .ctor f ih
  | dtor g _ ih => exact .dtor g ih
  | fail => exact .fail

theorem Expr.Eqv.subst {D D' : Expr F G (ℕ ⊕ Fin n)} (h : Expr.Eqv A D D')
    {σ σ' : Fin n → Tm F m} (hσ : ∀ i, Tm.Eqv A (σ i) (σ' i)) :
    Expr.Eqv A (D.subst σ) (D'.subst σ') := by
  induction h with
  | term h => exact .term (h.subst hσ)
  | ctor f _ ih => exact .ctor f ih
  | dtor g _ ih => exact .dtor g ih
  | fail => exact .fail

/-- Processes equal modulo `E`: the same shape, with terms and expressions equal
modulo `E`. -/
inductive Process.Eqv (A : Model F G) : ∀ {n : ℕ}, Process F G n → Process F G n → Prop
  | nil {n : ℕ} : Eqv A (.nil (n := n)) .nil
  | out {n : ℕ} {N N' M M' : Tm F n} {P P' : Process F G n} : Tm.Eqv A N N' → Tm.Eqv A M M' →
      Eqv A P P' → Eqv A (.out N M P) (.out N' M' P')
  | inp {n : ℕ} {N N' : Tm F n} {P P' : Process F G (n + 1)} : Tm.Eqv A N N' → Eqv A P P' →
      Eqv A (.inp N P) (.inp N' P')
  | par {n : ℕ} {P P' Q Q' : Process F G n} : Eqv A P P' → Eqv A Q Q' →
      Eqv A (.par P Q) (.par P' Q')
  | bang {n : ℕ} {P P' : Process F G n} : Eqv A P P' → Eqv A (.bang P) (.bang P')
  | new {n : ℕ} {P P' : Process F G (n + 1)} : Eqv A P P' → Eqv A (.new P) (.new P')
  | let_ {n : ℕ} {D D' : Expr F G (ℕ ⊕ Fin n)} {P P' : Process F G (n + 1)}
      {Q Q' : Process F G n} : Expr.Eqv A D D' → Eqv A P P' → Eqv A Q Q' →
      Eqv A (.let_ D P Q) (.let_ D' P' Q')
  | ite {n : ℕ} {M M' : Tm F n} {P P' Q Q' : Process F G n} : Tm.Eqv A M M' → Eqv A P P' →
      Eqv A Q Q' → Eqv A (.ite M P Q) (.ite M' P' Q')
  | event {n : ℕ} {M M' : Tm F n} {P P' : Process F G n} : Tm.Eqv A M M' → Eqv A P P' →
      Eqv A (.event M P) (.event M' P')

theorem Process.Eqv.refl : ∀ {n : ℕ} (P : Process F G n), Process.Eqv A P P
  | _, .nil => .nil
  | _, .out N M P => .out (Tm.Eqv.refl N) (Tm.Eqv.refl M) (Process.Eqv.refl P)
  | _, .inp N P => .inp (Tm.Eqv.refl N) (Process.Eqv.refl P)
  | _, .par P Q => .par (Process.Eqv.refl P) (Process.Eqv.refl Q)
  | _, .bang P => .bang (Process.Eqv.refl P)
  | _, .new P => .new (Process.Eqv.refl P)
  | _, .let_ D P Q => .let_ (Expr.Eqv.refl D) (Process.Eqv.refl P) (Process.Eqv.refl Q)
  | _, .ite M P Q => .ite (Tm.Eqv.refl M) (Process.Eqv.refl P) (Process.Eqv.refl Q)
  | _, .event M P => .event (Tm.Eqv.refl M) (Process.Eqv.refl P)

theorem Process.Eqv.symm {P P' : Process F G n} (h : Process.Eqv A P P') :
    Process.Eqv A P' P := by
  induction h with
  | nil => exact .nil
  | out hN hM _ ih => exact .out hN.symm hM.symm ih
  | inp hN _ ih => exact .inp hN.symm ih
  | par _ _ ih₁ ih₂ => exact .par ih₁ ih₂
  | bang _ ih => exact .bang ih
  | new _ ih => exact .new ih
  | let_ hD _ _ ih₁ ih₂ => exact .let_ hD.symm ih₁ ih₂
  | ite hM _ _ ih₁ ih₂ => exact .ite hM.symm ih₁ ih₂
  | event hM _ ih => exact .event hM.symm ih

theorem Process.Eqv.subst {P P' : Process F G n} (h : Process.Eqv A P P') :
    ∀ {m : ℕ} {σ σ' : Fin n → Tm F m}, (∀ i, Tm.Eqv A (σ i) (σ' i)) →
      Process.Eqv A (P.subst σ) (P'.subst σ') := by
  induction h with
  | nil => exact fun _ => .nil
  | out hN hM _ ih => exact fun hσ => .out (hN.subst hσ) (hM.subst hσ) (ih hσ)
  | inp hN _ ih => exact fun hσ => .inp (hN.subst hσ) (ih (liftSubst_eqv hσ))
  | par _ _ ih₁ ih₂ => exact fun hσ => .par (ih₁ hσ) (ih₂ hσ)
  | bang _ ih => exact fun hσ => .bang (ih hσ)
  | new _ ih => exact fun hσ => .new (ih (liftSubst_eqv hσ))
  | let_ hD _ _ ih₁ ih₂ => exact fun hσ => .let_ (hD.subst hσ) (ih₁ (liftSubst_eqv hσ)) (ih₂ hσ)
  | ite hM _ _ ih₁ ih₂ => exact fun hσ => .ite (hM.subst hσ) (ih₁ hσ) (ih₂ hσ)
  | event hM _ ih => exact fun hσ => .event (hM.subst hσ) (ih hσ)

/-- Instantiation respects equality modulo `E`. -/
theorem Process.Eqv.inst {P P' : Process F G (n + 1)} (h : Process.Eqv A P P') {M M' : Tm F n}
    (hM : Tm.Eqv A M M') : Process.Eqv A (P.inst M) (P'.inst M') :=
  h.subst fun i => by
    induction i using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using hM
    | cast j => simpa only [Fin.snoc_castSucc] using Tm.Eqv.refl (.var (.inr j))

/-! ## Evaluation and steps -/

theorem Eval.eqv {D D' : Expr F G (ℕ ⊕ Fin 0)} (h : Expr.Eqv A D D') :
    ∀ {v : Option A.Msg}, Eval A D v → Eval A D' v := by
  induction h with
  | term hM =>
    intro v hv
    cases hv
    rw [Tm.eqv_iff.1 hM]
    exact .term _
  | ctor f _ ih =>
    intro v hv
    cases hv with
    | ctor _ hargs => exact .ctor f fun i => ih i (hargs i)
  | dtor g _ ih =>
    intro v hv
    cases hv with
    | dtor _ hargs hr => exact .dtor g (fun i => ih i (hargs i)) hr
  | fail =>
    intro v hv
    cases hv
    exact .fail

/-- A step of a multiset of processes is matched by a step of any multiset equal to it
modulo `E`, with the same label and created names. -/
theorem Step.eqv {U U' : Finset ℕ} {Ps Ps' Qs : Multiset (Process F G 0)}
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
  | comm N M Q N' P M' hN hM =>
    obtain ⟨R₁, Qs₁, hR₁, hr₁, rfl⟩ := Multiset.rel_cons_left.1 hr
    obtain ⟨R₂, Qs₀, hR₂, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr₁
    cases hR₁ with
    | out hN₁ hM₁ hQ =>
      cases hR₂ with
      | inp hN₁' hP =>
        refine ⟨_, ?_, .cons hQ (.cons (hP.inst (Tm.Eqv.refl _)) hrest)⟩
        rw [Tm.eqv_iff.1 hN₁, Tm.eqv_iff.1 hM₁]
        exact .comm _ _ _ _ _ M' ((Tm.eqv_iff.1 hN₁).symm.trans (hN.trans (Tm.eqv_iff.1 hN₁')))
          (hM.trans (Tm.eqv_iff.1 hM₁))
  | eval₁ D P Q M hD =>
    obtain ⟨R, Qs₀, hR, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr
    cases hR with
    | let_ hD' hP hQ =>
      exact ⟨_, .eval₁ _ _ _ M (Eval.eqv hD' hD), .cons (hP.inst (Tm.Eqv.refl _)) hrest⟩
  | eval₂ D P Q hD =>
    obtain ⟨R, Qs₀, hR, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr
    cases hR with
    | let_ hD' hP hQ => exact ⟨_, .eval₂ _ _ _ (Eval.eqv hD' hD), .cons hQ hrest⟩
  | cond₁ M P Q hM =>
    obtain ⟨R, Qs₀, hR, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr
    cases hR with
    | ite hM' hP hQ => exact ⟨_, .cond₁ _ _ _ ((Tm.eqv_iff.1 hM').symm.trans hM), .cons hP hrest⟩
  | cond₂ M P Q hM =>
    obtain ⟨R, Qs₀, hR, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr
    cases hR with
    | ite hM' hP hQ =>
      exact ⟨_, .cond₂ _ _ _ fun h => hM ((Tm.eqv_iff.1 hM').trans h), .cons hQ hrest⟩
  | event M P =>
    obtain ⟨R, Qs₀, hR, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr
    cases hR with
    | event hM hP =>
      refine ⟨_, ?_, .cons hP hrest⟩
      rw [Tm.eqv_iff.1 hM]
      exact .event _ _
  | out N M P =>
    obtain ⟨R, Qs₀, hR, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr
    cases hR with
    | out hN hM hP =>
      refine ⟨_, ?_, .cons hP hrest⟩
      rw [Tm.eqv_iff.1 hN, Tm.eqv_iff.1 hM]
      exact .out _ _ _
  | inp N P M =>
    obtain ⟨R, Qs₀, hR, hrest, rfl⟩ := Multiset.rel_cons_left.1 hr
    cases hR with
    | inp hN hP =>
      refine ⟨_, ?_, .cons (hP.inst (Tm.Eqv.refl _)) hrest⟩
      rw [Tm.eqv_iff.1 hN]
      exact .inp _ _ M

/-- A run of a multiset of processes is a run of any multiset equal to it modulo `E`. -/
theorem Runs.eqv {c : Config F G} {t : Trace A.Msg} (h : Runs A c t) :
    ∀ {Qs : Multiset (Process F G 0)}, Multiset.Rel (Process.Eqv A) c.procs Qs →
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
theorem traces_eqv {U : Finset ℕ} {Ps Qs : Multiset (Process F G 0)}
    (h : Multiset.Rel (Process.Eqv A) Ps Qs) :
    Config.traces A ⟨U, Ps⟩ = Config.traces A ⟨U, Qs⟩ :=
  Set.ext fun _ => ⟨fun ht => Runs.eqv ht h,
    fun ht => Runs.eqv ht (Multiset.rel_flip.1 (h.mono fun _ _ _ _ h => h.symm))⟩

/-- A step on a term `M' =_E M` counts as a step on `M`: the term that (Red I/O') or
(Red Eval 1) substitutes does not matter beyond its message. -/
theorem traces_inst {U : Finset ℕ} {P : Process F G 1} {M M' : Tm F 0}
    (h : Tm.msg A M = Tm.msg A M') (Ps : Multiset (Process F G 0)) :
    Config.traces A ⟨U, P.inst M ::ₘ Ps⟩ = Config.traces A ⟨U, P.inst M' ::ₘ Ps⟩ :=
  traces_eqv (.cons ((Process.Eqv.refl P).inst (Tm.eqv_iff.2 h))
    (Multiset.rel_refl_of_refl_on fun Q _ => Process.Eqv.refl Q))

end ProVerif.Specification
