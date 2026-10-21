/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.Specification.Adequacy

/-!
# Adversaries and the attacker

The two halves of the write-up's Theorem "Attacks", on the operational side.

* **Adversaries are attacker traces.** As an `N_pub`-adversary runs, the closed terms
  substituted into it are derivable from what it has received and created, and its
  expressions, with public symbols and no event, keep that under term steps, which
  create at most a name it then knows (`Model.DerivX`, `Model.AdvK`, `Model.AdvK.tstep`);
  so every run of it is a trace of the attacker of the trace semantics (`Runs.enemy`).
* **Attacker traces are runs of adversaries.** A message derivable from the values of
  the bound variables is the value of a public effect-free expression
  (`expr_of_derive`), so an attacker trace is replayed by an adversary process that
  receives, computes with `let`, sends and creates names as the trace does, and
  communicates with itself for the attacker's outputs to itself (`Enemy.process`).
-/

namespace ProVerif.Specification

open FirstOrder FirstOrder.Language ProVerif.TraceSemantics
open Attacker (derive)

variable {F G Ev : Sig} {A : Model F G Ev} {n : ℕ}

/-! ## Adversaries are attacker traces -/

/-- In an environment of messages derivable from any `K' ⊇ K`, the term's value is
derivable from `K'`. -/
def Model.Deriv (K : Set A.Msg) (N : Tm F Ev n) : Prop :=
  ∀ K', K ⊆ K' → ∀ xs : Fin n → A.Msg, (∀ i, xs i ∈ derive K') →
    N.realize (env xs) ∈ derive K'

/-- Every term of the expression is derivable from `K` in the sense of `Model.Deriv`, its
symbols are public, and it has no event. -/
def Model.DerivX (K : Set A.Msg) : ∀ {n : ℕ}, Expr F G Ev n → Prop
  | _, .term M => A.Deriv K M
  | _, .ctor f args => A.Public f ∧ ∀ i, Model.DerivX K (args i)
  | _, .dtor g args => A.PublicDt g ∧ ∀ i, Model.DerivX K (args i)
  | _, .fail => True
  | _, .new D => Model.DerivX K D
  | _, .ite C D₁ D₂ => Model.DerivX K C ∧ Model.DerivX K D₁ ∧ Model.DerivX K D₂
  | _, .let_ D D₁ D₂ => Model.DerivX K D ∧ Model.DerivX K D₁ ∧ Model.DerivX K D₂
  | _, .event _ _ _ => False

/-- An adversary with closed terms derivable from `K` substituted in: what an
`N_pub`-adversary becomes as it runs, knowing `K`. -/
def Model.AdvK (K : Set A.Msg) : ∀ {n : ℕ}, Process F G Ev n → Prop
  | _, .nil => True
  | _, .out N M P => A.DerivX K N ∧ A.DerivX K M ∧ Model.AdvK K P
  | _, .inp N P => A.DerivX K N ∧ Model.AdvK K P
  | _, .par P Q => Model.AdvK K P ∧ Model.AdvK K Q
  | _, .bang P => Model.AdvK K P
  | _, .new P => Model.AdvK K P
  | _, .let_ D P Q => A.DerivX K D ∧ Model.AdvK K P ∧ Model.AdvK K Q
  | _, .ite C P Q => A.DerivX K C ∧ Model.AdvK K P ∧ Model.AdvK K Q
  | _, .event _ _ _ => False

theorem Model.Deriv.mono {K K' : Set A.Msg} {N : Tm F Ev n} (h : A.Deriv K N) (hK : K ⊆ K') :
    A.Deriv K' N := fun K'' hK' => h K'' (hK.trans hK')

theorem Model.DerivX.mono {K K' : Set A.Msg} (hK : K ⊆ K') :
    ∀ {n : ℕ} {D : Expr F G Ev n}, A.DerivX K D → A.DerivX K' D
  | _, .term _, h => Model.Deriv.mono h hK
  | _, .ctor _ args, h => ⟨h.1, fun i => Model.DerivX.mono hK (D := args i) (h.2 i)⟩
  | _, .dtor _ args, h => ⟨h.1, fun i => Model.DerivX.mono hK (D := args i) (h.2 i)⟩
  | _, .fail, _ => trivial
  | _, .new D, h => Model.DerivX.mono hK (D := D) h
  | _, .ite C D₁ D₂, h => ⟨Model.DerivX.mono hK (D := C) h.1, Model.DerivX.mono hK (D := D₁) h.2.1,
      Model.DerivX.mono hK (D := D₂) h.2.2⟩
  | _, .let_ D D₁ D₂, h => ⟨Model.DerivX.mono hK (D := D) h.1,
      Model.DerivX.mono hK (D := D₁) h.2.1, Model.DerivX.mono hK (D := D₂) h.2.2⟩
  | _, .event _ _ _, h => h.elim

theorem Model.AdvK.mono {K K' : Set A.Msg} (hK : K ⊆ K') :
    ∀ {n : ℕ} {P : Process F G Ev n}, A.AdvK K P → A.AdvK K' P
  | _, .nil, _ => trivial
  | _, .out _ _ P, h => ⟨h.1.mono hK, h.2.1.mono hK, Model.AdvK.mono (P := P) hK h.2.2⟩
  | _, .inp _ P, h => ⟨h.1.mono hK, Model.AdvK.mono (P := P) hK h.2⟩
  | _, .par P Q, h => ⟨Model.AdvK.mono (P := P) hK h.1, Model.AdvK.mono (P := Q) hK h.2⟩
  | _, .bang P, h => Model.AdvK.mono (P := P) hK h
  | _, .new P, h => Model.AdvK.mono (P := P) hK h
  | _, .let_ _ P Q, h =>
    ⟨h.1.mono hK, Model.AdvK.mono (P := P) hK h.2.1, Model.AdvK.mono (P := Q) hK h.2.2⟩
  | _, .ite _ P Q, h =>
    ⟨h.1.mono hK, Model.AdvK.mono (P := P) hK h.2.1, Model.AdvK.mono (P := Q) hK h.2.2⟩
  | _, .event _ _ _, h => h.elim

theorem Model.Deriv.msg {K : Set A.Msg} {M : Tm F Ev 0} (h : A.Deriv K M) :
    Tm.msg A M ∈ derive K :=
  h K subset_rfl finZeroElim fun i => i.elim0

theorem Model.deriv_of_msg {K : Set A.Msg} {M : Tm F Ev 0} (h : Tm.msg A M ∈ derive K) :
    A.Deriv K M := fun K' hK xs _ => by
  rw [show xs = finZeroElim from funext fun i => i.elim0]
  exact derive.monotone hK h

theorem Model.deriv_var (K : Set A.Msg) (i : Fin n) : A.Deriv K (.var (.inr i)) :=
  fun _ _ _ hxs => hxs i

theorem Model.PubTerm.deriv (K : Set A.Msg) : ∀ {N : Tm F Ev n}, A.PubTerm N → A.Deriv K N
  | .var (.inl _), h => h.elim
  | .var (.inr i), _ => A.deriv_var K i
  | .func f ts, h => fun K' hK xs hxs => by
    rw [Term.realize_func]
    exact A.app_mem_derive h.1 fun i => Model.PubTerm.deriv K (h.2 i) K' hK xs hxs

theorem Model.PubExpr.derivX (K : Set A.Msg) :
    ∀ {n : ℕ} {D : Expr F G Ev n}, A.PubExpr D → A.DerivX K D
  | _, .term _, h => Model.PubTerm.deriv K h
  | _, .ctor _ args, h => ⟨h.1, fun i => Model.PubExpr.derivX K (D := args i) (h.2 i)⟩
  | _, .dtor _ args, h => ⟨h.1, fun i => Model.PubExpr.derivX K (D := args i) (h.2 i)⟩
  | _, .fail, _ => trivial
  | _, .new D, h => Model.PubExpr.derivX K (D := D) h
  | _, .ite C D₁ D₂, h => ⟨Model.PubExpr.derivX K (D := C) h.1,
      Model.PubExpr.derivX K (D := D₁) h.2.1, Model.PubExpr.derivX K (D := D₂) h.2.2⟩
  | _, .let_ D D₁ D₂, h => ⟨Model.PubExpr.derivX K (D := D) h.1,
      Model.PubExpr.derivX K (D := D₁) h.2.1, Model.PubExpr.derivX K (D := D₂) h.2.2⟩
  | _, .event _ _ _, h => h.elim

theorem Model.Adversary.advK (K : Set A.Msg) :
    ∀ {n : ℕ} {P : Process F G Ev n}, A.Adversary P → A.AdvK K P
  | _, .nil, _ => trivial
  | _, .out _ _ P, h => ⟨Model.PubExpr.derivX K h.1, Model.PubExpr.derivX K h.2.1,
      Model.Adversary.advK K (P := P) h.2.2⟩
  | _, .inp _ P, h => ⟨Model.PubExpr.derivX K h.1, Model.Adversary.advK K (P := P) h.2⟩
  | _, .par P Q, h => ⟨Model.Adversary.advK K (P := P) h.1, Model.Adversary.advK K (P := Q) h.2⟩
  | _, .bang P, h => Model.Adversary.advK K (P := P) h
  | _, .new P, h => Model.Adversary.advK K (P := P) h
  | _, .let_ _ P Q, h => ⟨Model.PubExpr.derivX K h.1, Model.Adversary.advK K (P := P) h.2.1,
      Model.Adversary.advK K (P := Q) h.2.2⟩
  | _, .ite _ P Q, h => ⟨Model.PubExpr.derivX K h.1, Model.Adversary.advK K (P := P) h.2.1,
      Model.Adversary.advK K (P := Q) h.2.2⟩
  | _, .event _ _ _, h => h.elim

theorem Model.Deriv.subst {K : Set A.Msg} {N : Tm F Ev n} (h : A.Deriv K N) {m : ℕ}
    {σ : Fin n → Tm F Ev m} (hσ : ∀ i, A.Deriv K (σ i)) : A.Deriv K (Tm.subst σ N) :=
  fun K' hK xs hxs => by
    rw [Tm.realize_subst]
    exact h K' hK _ fun i => hσ i K' hK xs hxs

theorem Model.deriv_liftSubst {K : Set A.Msg} {m : ℕ} {σ : Fin n → Tm F Ev m}
    (hσ : ∀ i, A.Deriv K (σ i)) (i : Fin (n + 1)) : A.Deriv K (liftSubst σ i) := by
  induction i using Fin.lastCases with
  | last =>
    simp only [liftSubst, Fin.snoc_last]
    exact A.deriv_var K _
  | cast j =>
    simp only [liftSubst, Fin.snoc_castSucc]
    intro K' hK xs hxs
    rw [Term.realize_relabel,
      show env xs ∘ Sum.map id Fin.castSucc = env (A := A) fun j' => xs j'.castSucc from
        funext fun x => by cases x <;> rfl]
    exact hσ j K' hK _ fun j' => hxs _

theorem Model.DerivX.subst {K : Set A.Msg} :
    ∀ {n m : ℕ} {D : Expr F G Ev n} {σ : Fin n → Tm F Ev m}, A.DerivX K D →
      (∀ i, A.Deriv K (σ i)) → A.DerivX K (D.subst σ)
  | _, _, .term _, _, h, hσ => Model.Deriv.subst h hσ
  | _, _, .ctor _ args, σ, h, hσ =>
    ⟨h.1, fun i => Model.DerivX.subst (D := args i) (σ := σ) (h.2 i) hσ⟩
  | _, _, .dtor _ args, σ, h, hσ =>
    ⟨h.1, fun i => Model.DerivX.subst (D := args i) (σ := σ) (h.2 i) hσ⟩
  | _, _, .fail, _, _, _ => trivial
  | _, _, .new D, σ, h, hσ =>
    Model.DerivX.subst (D := D) (σ := liftSubst σ) h (A.deriv_liftSubst hσ)
  | _, _, .ite C D₁ D₂, σ, h, hσ =>
    ⟨Model.DerivX.subst (D := C) (σ := σ) h.1 hσ, Model.DerivX.subst (D := D₁) (σ := σ) h.2.1 hσ,
      Model.DerivX.subst (D := D₂) (σ := σ) h.2.2 hσ⟩
  | _, _, .let_ D D₁ D₂, σ, h, hσ =>
    ⟨Model.DerivX.subst (D := D) (σ := σ) h.1 hσ,
      Model.DerivX.subst (D := D₁) (σ := liftSubst σ) h.2.1 (A.deriv_liftSubst hσ),
      Model.DerivX.subst (D := D₂) (σ := σ) h.2.2 hσ⟩
  | _, _, .event _ _ _, _, h, _ => h.elim

theorem Model.AdvK.subst {K : Set A.Msg} :
    ∀ {n m : ℕ} {P : Process F G Ev n} {σ : Fin n → Tm F Ev m}, A.AdvK K P →
      (∀ i, A.Deriv K (σ i)) → A.AdvK K (P.subst σ)
  | _, _, .nil, _, _, _ => trivial
  | _, _, .out _ _ P, σ, h, hσ =>
    ⟨h.1.subst hσ, h.2.1.subst hσ, Model.AdvK.subst (P := P) (σ := σ) h.2.2 hσ⟩
  | _, _, .inp _ P, σ, h, hσ =>
    ⟨h.1.subst hσ, Model.AdvK.subst (P := P) (σ := liftSubst σ) h.2 (A.deriv_liftSubst hσ)⟩
  | _, _, .par P Q, σ, h, hσ =>
    ⟨Model.AdvK.subst (P := P) (σ := σ) h.1 hσ, Model.AdvK.subst (P := Q) (σ := σ) h.2 hσ⟩
  | _, _, .bang P, σ, h, hσ => Model.AdvK.subst (P := P) (σ := σ) h hσ
  | _, _, .new P, σ, h, hσ =>
    Model.AdvK.subst (P := P) (σ := liftSubst σ) h (A.deriv_liftSubst hσ)
  | _, _, .let_ _ P Q, σ, h, hσ =>
    ⟨h.1.subst hσ, Model.AdvK.subst (P := P) (σ := liftSubst σ) h.2.1 (A.deriv_liftSubst hσ),
      Model.AdvK.subst (P := Q) (σ := σ) h.2.2 hσ⟩
  | _, _, .ite _ P Q, σ, h, hσ =>
    ⟨h.1.subst hσ, Model.AdvK.subst (P := P) (σ := σ) h.2.1 hσ,
      Model.AdvK.subst (P := Q) (σ := σ) h.2.2 hσ⟩
  | _, _, .event _ _ _, _, h, _ => h.elim

theorem Model.deriv_snoc {K : Set A.Msg} {M : Tm F Ev n} (hM : A.Deriv K M) (i : Fin (n + 1)) :
    A.Deriv K (Fin.snoc (α := fun _ => Tm F Ev n) (fun i => .var (.inr i)) M i) := by
  induction i using Fin.lastCases with
  | last => simpa only [Fin.snoc_last] using hM
  | cast j => simpa only [Fin.snoc_castSucc] using A.deriv_var K j

theorem Model.DerivX.inst {K : Set A.Msg} {D : Expr F G Ev (n + 1)} (h : A.DerivX K D)
    {M : Tm F Ev n} (hM : A.Deriv K M) : A.DerivX K (D.inst M) :=
  h.subst (A.deriv_snoc hM)

theorem Model.AdvK.inst {K : Set A.Msg} {P : Process F G Ev (n + 1)} (h : A.AdvK K P)
    {M : Tm F Ev n} (hM : A.Deriv K M) : A.AdvK K (P.inst M) :=
  h.subst (A.deriv_snoc hM)

/-- The value of an adversary's may-fail term is derivable. -/
theorem Val.deriv {K : Set A.Msg} {V : Expr F G Ev 0} {u : Option A.Msg} (hV : Val A V u)
    (hD : A.DerivX K V) : ∀ m, u = some m → m ∈ derive K := by
  induction hV with
  | term M =>
    rintro m hm
    obtain rfl := Option.some.inj hm
    exact Model.Deriv.msg hD
  | ctor f _ ih =>
    rintro m hm
    obtain rfl := Option.some.inj hm
    exact A.app_mem_derive hD.1 fun i => ih i (hD.2 i) _ rfl
  | fail => rintro m hm; cases hm

theorem derivX_update {K : Set A.Msg} {k : ℕ} {args : Fin k → Expr F G Ev 0}
    (h : ∀ j, A.DerivX K (args j)) {i : Fin k} {D' : Expr F G Ev 0} (hD : A.DerivX K D')
    (j : Fin k) : A.DerivX K (Function.update args i D' j) := by
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self]
    exact hD
  · rw [Function.update_of_ne hj]
    exact h j

/-- A term step of an adversary's expression keeps it an adversary's, or creates a name
the adversary then knows. -/
theorem Model.AdvK.tstep {U U' : Finset ℕ} {D D' : Expr F G Ev 0} {l : Option (Act A.Msg)}
    (h : TStep A U D l U' D') : ∀ {K : Set A.Msg}, A.DerivX K D →
      (l = none ∧ A.DerivX K D') ∨
        ∃ k, l = some (.new k) ∧ A.DerivX (insert (Theory.Msg.name k) K) D' := by
  induction h with
  | ctor_fail => exact fun _ => Or.inl ⟨rfl, trivial⟩
  | @dtor k g args us M hargs hr =>
    intro K hD
    exact Or.inl ⟨rfl, A.deriv_of_msg (A.dtorFun_mem_derive hD.1
      (fun i m' hm' => (hargs i).deriv (hD.2 i) m' hm') ((A.rewrites_iff g).1 hr))⟩
  | dtor_fail => exact fun _ => Or.inl ⟨rfl, trivial⟩
  | @new D k hk =>
    intro K hD
    exact Or.inr ⟨k, rfl, (Model.DerivX.mono (Set.subset_insert _ _) hD).inst
      (A.deriv_of_msg (derive.le_closure _ (Set.mem_insert _ _)))⟩
  | ite₁ => exact fun hD => Or.inl ⟨rfl, hD.2.1⟩
  | ite₂ => exact fun hD => Or.inl ⟨rfl, hD.2.2⟩
  | ite_fail => exact fun _ => Or.inl ⟨rfl, trivial⟩
  | @let₁ D m M' D₁ D₂ hD hM' =>
    intro K hDX
    refine Or.inl ⟨rfl, hDX.2.1.inst (A.deriv_of_msg ?_)⟩
    rw [hM']
    exact hD.deriv hDX.1 m rfl
  | let₂ => exact fun hD => Or.inl ⟨rfl, hD.2.2⟩
  | event => exact fun hD => hD.elim
  | event_fail => exact fun hD => hD.elim
  | @ctor_ctx U' l k f args i D' hv hs ih =>
    intro K hD
    rcases ih (hD.2 i) with ⟨rfl, hD'⟩ | ⟨k', rfl, hD'⟩
    · exact Or.inl ⟨rfl, hD.1, derivX_update hD.2 hD'⟩
    · exact Or.inr ⟨k', rfl, hD.1,
        derivX_update (fun j => (hD.2 j).mono (Set.subset_insert _ _)) hD'⟩
  | @dtor_ctx U' l k g args i D' hv hs ih =>
    intro K hD
    rcases ih (hD.2 i) with ⟨rfl, hD'⟩ | ⟨k', rfl, hD'⟩
    · exact Or.inl ⟨rfl, hD.1, derivX_update hD.2 hD'⟩
    · exact Or.inr ⟨k', rfl, hD.1,
        derivX_update (fun j => (hD.2 j).mono (Set.subset_insert _ _)) hD'⟩
  | ite_ctx _ _ _ ih =>
    intro K hD
    rcases ih hD.1 with ⟨rfl, hD'⟩ | ⟨k', rfl, hD'⟩
    · exact Or.inl ⟨rfl, hD', hD.2⟩
    · exact Or.inr ⟨k', rfl, hD', hD.2.1.mono (Set.subset_insert _ _),
        hD.2.2.mono (Set.subset_insert _ _)⟩
  | let_ctx _ _ _ ih =>
    intro K hD
    rcases ih hD.1 with ⟨rfl, hD'⟩ | ⟨k', rfl, hD'⟩
    · exact Or.inl ⟨rfl, hD', hD.2⟩
    · exact Or.inr ⟨k', rfl, hD', hD.2.1.mono (Set.subset_insert _ _),
        hD.2.2.mono (Set.subset_insert _ _)⟩
  | event_ctx => exact fun hD => hD.elim

/-- What a step of adversaries is, and what they know afterwards. -/
theorem Model.AdvK.step {K : Set A.Msg} {U U' : Finset ℕ} {Ps Ps' : Multiset (Process F G Ev 0)}
    {l : Option (Act A.Msg)} (h : Step A ⟨U, Ps⟩ l ⟨U', Ps'⟩) (hPs : ∀ P ∈ Ps, A.AdvK K P) :
    (l = none ∧ ∀ P ∈ Ps', A.AdvK K P) ∨
    (∃ c m, l = some (.out c m) ∧ c ∈ derive K ∧ m ∈ derive K ∧
      ∀ P ∈ Ps', A.AdvK K P) ∨
    (∃ c m, l = some (.comm c m) ∧ c ∈ derive K ∧ m ∈ derive K ∧
      ∀ P ∈ Ps', A.AdvK K P) ∨
    (∃ c m, l = some (.inp c m) ∧ c ∈ derive K ∧ ∀ P ∈ Ps', A.AdvK (insert m K) P) ∨
    (∃ k, l = some (.new k) ∧ ∀ P ∈ Ps', A.AdvK (insert (Theory.Msg.name k) K) P) := by
  have hins : ∀ {K' : Set A.Msg} {Qs : Multiset (Process F G Ev 0)}, (∀ P ∈ Qs, A.AdvK K P) →
      K ⊆ K' → ∀ P ∈ Qs, A.AdvK K' P := fun h hK P hP => Model.AdvK.mono hK (h P hP)
  cases h with
  | nil => exact Or.inl ⟨rfl, (Multiset.forall_mem_cons.1 hPs).2⟩
  | par P Q =>
    obtain ⟨⟨hP, hQ⟩, hrest⟩ := Multiset.forall_mem_cons.1 hPs
    exact Or.inl ⟨rfl, Multiset.forall_mem_cons.2 ⟨hP, Multiset.forall_mem_cons.2 ⟨hQ, hrest⟩⟩⟩
  | bang P =>
    obtain ⟨hP, hrest⟩ := Multiset.forall_mem_cons.1 hPs
    exact Or.inl ⟨rfl, Multiset.forall_mem_cons.2 ⟨hP, Multiset.forall_mem_cons.2 ⟨hP, hrest⟩⟩⟩
  | new P k hk =>
    obtain ⟨hP, hrest⟩ := Multiset.forall_mem_cons.1 hPs
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨k, rfl, Multiset.forall_mem_cons.2
      ⟨(Model.AdvK.mono (Set.subset_insert _ _) hP).inst ?_, hins hrest (Set.subset_insert _ _)⟩⟩)))
    exact A.deriv_of_msg (derive.le_closure _ (Set.mem_insert _ _))
  | comm Q P M' hN hM hN' hM' =>
    obtain ⟨⟨hNX, hMX, hQ⟩, hrest⟩ := Multiset.forall_mem_cons.1 hPs
    obtain ⟨⟨-, hP⟩, hrest⟩ := Multiset.forall_mem_cons.1 hrest
    refine Or.inr (Or.inr (Or.inl ⟨_, _, rfl, hN.deriv hNX _ rfl, hM.deriv hMX _ rfl,
      Multiset.forall_mem_cons.2 ⟨hQ, Multiset.forall_mem_cons.2 ⟨hP.inst (A.deriv_of_msg ?_),
        hrest⟩⟩⟩))
    rw [hM']
    exact hM.deriv hMX _ rfl
  | eval₁ M' P Q hD hM' =>
    obtain ⟨⟨hDX, hP, -⟩, hrest⟩ := Multiset.forall_mem_cons.1 hPs
    refine Or.inl ⟨rfl, Multiset.forall_mem_cons.2 ⟨hP.inst (A.deriv_of_msg ?_), hrest⟩⟩
    rw [hM']
    exact hD.deriv hDX _ rfl
  | eval₂ P Q =>
    obtain ⟨⟨-, -, hQ⟩, hrest⟩ := Multiset.forall_mem_cons.1 hPs
    exact Or.inl ⟨rfl, Multiset.forall_mem_cons.2 ⟨hQ, hrest⟩⟩
  | cond₁ P Q hC =>
    obtain ⟨⟨-, hP, -⟩, hrest⟩ := Multiset.forall_mem_cons.1 hPs
    exact Or.inl ⟨rfl, Multiset.forall_mem_cons.2 ⟨hP, hrest⟩⟩
  | cond₂ P Q hC hm =>
    obtain ⟨⟨-, -, hQ⟩, hrest⟩ := Multiset.forall_mem_cons.1 hPs
    exact Or.inl ⟨rfl, Multiset.forall_mem_cons.2 ⟨hQ, hrest⟩⟩
  | event e P hargs => exact ((Multiset.forall_mem_cons.1 hPs).1).elim
  | out P hN hM =>
    obtain ⟨⟨hNX, hMX, hP⟩, hrest⟩ := Multiset.forall_mem_cons.1 hPs
    exact Or.inr (Or.inl ⟨_, _, rfl, hN.deriv hNX _ rfl, hM.deriv hMX _ rfl,
      Multiset.forall_mem_cons.2 ⟨hP, hrest⟩⟩)
  | inp P M hN =>
    obtain ⟨⟨hNX, hP⟩, hrest⟩ := Multiset.forall_mem_cons.1 hPs
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, hN.deriv hNX _ rfl,
      Multiset.forall_mem_cons.2 ⟨(Model.AdvK.mono (Set.subset_insert _ _) hP).inst ?_,
        hins hrest (Set.subset_insert _ _)⟩⟩)))
    exact A.deriv_of_msg (derive.le_closure _ (Set.mem_insert _ _))
  | out_ctx₁ M P hs =>
    obtain ⟨⟨hN, hM, hP⟩, hrest⟩ := Multiset.forall_mem_cons.1 hPs
    rcases Model.AdvK.tstep hs hN with ⟨rfl, hN'⟩ | ⟨k, rfl, hN'⟩
    · exact Or.inl ⟨rfl, Multiset.forall_mem_cons.2 ⟨⟨hN', hM, hP⟩, hrest⟩⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨k, rfl, Multiset.forall_mem_cons.2
        ⟨⟨hN', hM.mono (Set.subset_insert _ _), Model.AdvK.mono (Set.subset_insert _ _) hP⟩,
          hins hrest (Set.subset_insert _ _)⟩⟩)))
  | out_ctx₂ N P hNv hs =>
    obtain ⟨⟨hN, hM, hP⟩, hrest⟩ := Multiset.forall_mem_cons.1 hPs
    rcases Model.AdvK.tstep hs hM with ⟨rfl, hM'⟩ | ⟨k, rfl, hM'⟩
    · exact Or.inl ⟨rfl, Multiset.forall_mem_cons.2 ⟨⟨hN, hM', hP⟩, hrest⟩⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨k, rfl, Multiset.forall_mem_cons.2
        ⟨⟨hN.mono (Set.subset_insert _ _), hM', Model.AdvK.mono (Set.subset_insert _ _) hP⟩,
          hins hrest (Set.subset_insert _ _)⟩⟩)))
  | inp_ctx P hs =>
    obtain ⟨⟨hN, hP⟩, hrest⟩ := Multiset.forall_mem_cons.1 hPs
    rcases Model.AdvK.tstep hs hN with ⟨rfl, hN'⟩ | ⟨k, rfl, hN'⟩
    · exact Or.inl ⟨rfl, Multiset.forall_mem_cons.2 ⟨⟨hN', hP⟩, hrest⟩⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨k, rfl, Multiset.forall_mem_cons.2
        ⟨⟨hN', Model.AdvK.mono (Set.subset_insert _ _) hP⟩,
          hins hrest (Set.subset_insert _ _)⟩⟩)))
  | ite_ctx P Q hs =>
    obtain ⟨⟨hC, hP, hQ⟩, hrest⟩ := Multiset.forall_mem_cons.1 hPs
    rcases Model.AdvK.tstep hs hC with ⟨rfl, hC'⟩ | ⟨k, rfl, hC'⟩
    · exact Or.inl ⟨rfl, Multiset.forall_mem_cons.2 ⟨⟨hC', hP, hQ⟩, hrest⟩⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨k, rfl, Multiset.forall_mem_cons.2
        ⟨⟨hC', Model.AdvK.mono (Set.subset_insert _ _) hP,
          Model.AdvK.mono (Set.subset_insert _ _) hQ⟩, hins hrest (Set.subset_insert _ _)⟩⟩)))
  | let_ctx P Q hs =>
    obtain ⟨⟨hD, hP, hQ⟩, hrest⟩ := Multiset.forall_mem_cons.1 hPs
    rcases Model.AdvK.tstep hs hD with ⟨rfl, hD'⟩ | ⟨k, rfl, hD'⟩
    · exact Or.inl ⟨rfl, Multiset.forall_mem_cons.2 ⟨⟨hD', hP, hQ⟩, hrest⟩⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨k, rfl, Multiset.forall_mem_cons.2
        ⟨⟨hD', Model.AdvK.mono (Set.subset_insert _ _) hP,
          Model.AdvK.mono (Set.subset_insert _ _) hQ⟩, hins hrest (Set.subset_insert _ _)⟩⟩)))
  | event_ctx e i P hv hs => exact ((Multiset.forall_mem_cons.1 hPs).1).elim

/-- A run of adversaries knowing `K` is a trace of the attacker knowing `K`. -/
theorem Runs.enemy {c : Config F G Ev} {t : Trace A.Msg} (h : Runs A c t) :
    ∀ {K : Set A.Msg}, (∀ P ∈ c.procs, A.AdvK K P) → t ∈ Enemy K := by
  induction h with
  | nil c => exact fun _ => Enemy.nil
  | @tau c c' t hs _ ih =>
    obtain ⟨U, Ps⟩ := c
    obtain ⟨U', Ps'⟩ := c'
    intro K hK
    rcases Model.AdvK.step hs hK with ⟨-, h'⟩ | ⟨_, _, h, -⟩ | ⟨_, _, h, -⟩ | ⟨_, _, h, -⟩ |
      ⟨_, h, -⟩
    · exact ih h'
    all_goals cases h
  | @act c c' a t hs hr ih =>
    obtain ⟨U, Ps⟩ := c
    obtain ⟨U', Ps'⟩ := c'
    intro K hK
    rcases Model.AdvK.step hs hK with ⟨h, -⟩ | ⟨c, m, h, hc, hm, h'⟩ | ⟨c, m, h, hc, hm, h'⟩ |
      ⟨c, m, h, hc, h'⟩ | ⟨k, h, h'⟩
    · cases h
    · obtain rfl := Option.some.inj h
      exact Enemy.out c m hc hm (ih h')
    · obtain rfl := Option.some.inj h
      exact Enemy.comm c m hc hm (ih h')
    · obtain rfl := Option.some.inj h
      exact Enemy.inp c m hc (ih h')
    · obtain rfl := Option.some.inj h
      refine Enemy.new k (fun hk => (Runs.nonces hr).2 k hk ?_) (ih h')
      rcases hs.names_eq with ⟨k', hk', -, rfl⟩ | ⟨hl, -⟩
      · obtain rfl := Act.new.inj (Option.some.inj hk')
        exact Finset.mem_insert_self k U
      · exact (hl k rfl).elim

/-! ## Attacker traces are runs of adversaries -/

theorem derive_subset_of_subset {K S : Set A.Msg} (h : K ⊆ derive S) :
    derive K ⊆ derive S :=
  derive.closure_min h (derive.isClosed_closure S)

theorem range_subset_snoc (xs : Fin n → A.Msg) (a : A.Msg) :
    Set.range xs ⊆ Set.range (Fin.snoc (α := fun _ => A.Msg) xs a) := by
  rintro _ ⟨i, rfl⟩
  exact ⟨i.castSucc, Fin.snoc_castSucc _ _ _⟩

theorem mem_range_snoc (xs : Fin n → A.Msg) (a : A.Msg) :
    a ∈ Set.range (Fin.snoc (α := fun _ => A.Msg) xs a) :=
  ⟨Fin.last n, Fin.snoc_last _ _⟩

/-- A message derivable from the values of the bound variables is the value of a public
effect-free expression. -/
theorem expr_of_derive {xs : Fin n → A.Msg} {a : A.Msg} (h : a ∈ derive (Set.range xs)) :
    ∃ D : Expr F G Ev n, A.PubExpr D ∧ D.Pure ∧ D.denote xs = pure (some a) := by
  refine derive.closure_min (y := {a | ∃ D : Expr F G Ev n,
    A.PubExpr D ∧ D.Pure ∧ D.denote xs = pure (some a)}) ?_ ?_ h
  · rintro _ ⟨i, rfl⟩
    exact ⟨.term (.var (.inr i)), trivial, trivial, rfl⟩
  · intro o ho args hargs r hr
    have hD : ∀ i, ∃ D : Expr F G Ev n, A.PubExpr D ∧ D.Pure ∧ D.denote xs = pure (args i) :=
      fun i => by
        rcases h : args i with _ | m
        · exact ⟨.fail, trivial, trivial, rfl⟩
        · exact hargs i m h
    choose Ds hDs using hD
    have hargs' : (fun i => (Ds i).denote xs) = fun i => pure (args i) :=
      funext fun i => (hDs i).2.2
    rcases ho with (ho | ho) | (⟨k, rfl⟩ | ⟨⟨k, i⟩, rfl⟩) | rfl | rfl
    · obtain ⟨k, f', hf', rfl⟩ := Set.mem_iUnion.1 ho
      obtain ⟨f, hf, rfl⟩ := hf'
      refine ⟨.ctor (.inl (.inl f)) Ds, ⟨hf, fun i => (hDs i).1⟩, fun i => (hDs i).2.1, ?_⟩
      simp only [Expr.denote]
      rw [hargs', seqFin_pure, pure_bind]
      exact congrArg pure hr
    · obtain ⟨k, g, hg, rfl⟩ := Set.mem_iUnion.1 ho
      refine ⟨.dtor (.inl g) Ds, ⟨hg, fun i => (hDs i).1⟩, fun i => (hDs i).2.1, ?_⟩
      simp only [Expr.denote]
      rw [hargs', seqFin_pure, pure_bind]
      exact congrArg pure hr
    · refine ⟨.ctor (.inr (.tuple k)) Ds, ⟨trivial, fun i => (hDs i).1⟩, fun i => (hDs i).2.1, ?_⟩
      simp only [Expr.denote]
      rw [hargs', seqFin_pure, pure_bind]
      exact congrArg pure hr
    · refine ⟨.dtor (.inr (.proj k i)) Ds, ⟨trivial, fun i => (hDs i).1⟩, fun i => (hDs i).2.1, ?_⟩
      simp only [Expr.denote]
      rw [hargs', seqFin_pure, pure_bind, A.dtorFun_proj]
      exact congrArg pure hr
    · obtain rfl := Option.some_injective _ hr
      refine ⟨.ctor (.inr .tt) Ds, ⟨trivial, fun i => (hDs i).1⟩, fun i => (hDs i).2.1, ?_⟩
      simp only [Expr.denote]
      rw [hargs', seqFin_pure, pure_bind, liftFail_zero, Theory.Msg.tt_def]
      exact congrArg pure (congrArg some (congrArg _ (funext fun i => i.elim0)))
    · obtain rfl := Option.some_injective _ hr
      refine ⟨.ctor (.inr .ff) Ds, ⟨trivial, fun i => (hDs i).1⟩, fun i => (hDs i).2.1, ?_⟩
      simp only [Expr.denote]
      rw [hargs', seqFin_pure, pure_bind, liftFail_zero, Theory.Msg.ff_def]
      exact congrArg pure (congrArg some (congrArg _ (funext fun i => i.elim0)))

/-! ### Steps of a substituted process -/

theorem Runs.let_step {σ : Fin n → Tm F Ev 0} {D : Expr F G Ev n} (hD : D.Pure)
    {P : Process F G Ev (n + 1)} {Q : Process F G Ev n} {M : Tm F Ev 0} {U : Finset ℕ}
    {t : Trace A.Msg} (hD' : D.denote (fun i => Tm.msg A (σ i)) = pure (some (Tm.msg A M)))
    (h : Runs A ⟨U, {P.subst (Fin.snoc σ M)}⟩ t) :
    Runs A ⟨U, {(Process.let_ D P Q).subst σ}⟩ t := by
  simp only [Process.subst]
  obtain ⟨V, u, hr, hV, hd⟩ := Expr.Pure.reduces_subst (A := A) hD σ U
  rw [Expr.denote_subst_msg, hD'] at hd
  obtain rfl := Proc.pure_inj hd
  exact Runs.ctx (C := fun D' => Process.let_ D' (P.subst (liftSubst σ)) (Q.subst σ))
    (isCtx_let _ _) hr (.tau (.eval₁ M _ _ hV rfl)
      (Runs.eqv h (.cons (subst_inst_eqv P σ M).symm .zero)))

theorem Runs.inp_step {σ : Fin n → Tm F Ev 0} {N : Tm F Ev n} {P : Process F G Ev (n + 1)}
    {M : Tm F Ev 0} {U : Finset ℕ} {t : Trace A.Msg} {c m : A.Msg}
    (hN : N.realize (env fun i => Tm.msg A (σ i)) = c) (hM : Tm.msg A M = m)
    (h : Runs A ⟨U, {P.subst (Fin.snoc σ M)}⟩ t) :
    Runs A ⟨U, {(Process.inp (.term N) P).subst σ}⟩ (.inp c m :: t) := by
  simp only [Process.subst, Expr.subst]
  subst hN hM
  rw [← Tm.msg_subst]
  exact .act (.inp _ M (.term _)) (Runs.eqv h (.cons (subst_inst_eqv P σ M).symm .zero))

theorem Runs.out_step {σ : Fin n → Tm F Ev 0} {N M : Tm F Ev n} {P : Process F G Ev n}
    {U : Finset ℕ} {t : Trace A.Msg} {c m : A.Msg} (hN : N.realize (env fun i => Tm.msg A (σ i)) = c)
    (hM : M.realize (env fun i => Tm.msg A (σ i)) = m) (h : Runs A ⟨U, {P.subst σ}⟩ t) :
    Runs A ⟨U, {(Process.out (.term N) (.term M) P).subst σ}⟩ (.out c m :: t) := by
  simp only [Process.subst, Expr.subst]
  subst hN hM
  rw [← Tm.msg_subst, ← Tm.msg_subst]
  exact .act (.out _ (.term _) (.term _)) h

theorem Runs.new_step {σ : Fin n → Tm F Ev 0} {P : Process F G Ev (n + 1)} {U : Finset ℕ} {k : ℕ}
    {t : Trace A.Msg} (hk : k ∉ U)
    (h : Runs A ⟨insert k U, {P.subst (Fin.snoc σ (.var (.inl k)))}⟩ t) :
    Runs A ⟨U, {(Process.new P).subst σ}⟩ (.new k :: t) := by
  simp only [Process.subst]
  exact .act (.new _ k hk) (Runs.eqv h (.cons (subst_inst_eqv P σ _).symm .zero))

theorem Runs.par_step {σ : Fin n → Tm F Ev 0} {P Q : Process F G Ev n} {U : Finset ℕ}
    {t : Trace A.Msg} (h : Runs A ⟨U, {P.subst σ} + {Q.subst σ}⟩ t) :
    Runs A ⟨U, {(Process.par P Q).subst σ}⟩ t := by
  simp only [Process.subst]
  rw [Multiset.singleton_add] at h
  exact .tau (.par _ _) h

theorem Tm.msg_var_inr (σ : Fin (n + 1) → Tm F Ev 0) (i : Fin (n + 1)) :
    Tm.msg A (Tm.subst σ (.var (.inr i))) = Tm.msg A (σ i) := by
  simp [Tm.subst, Term.subst, Tm.msg]

/-- An attacker trace is replayed by an adversary process. -/
theorem Enemy.process {K : Set A.Msg} {e : Trace A.Msg} (he : Enemy K e) :
    ∀ {n : ℕ} (xs : Fin n → A.Msg), K ⊆ derive (Set.range xs) →
      ∃ Q : Process F G Ev n, A.Adversary Q ∧ ∀ σ : Fin n → Tm F Ev 0,
        (fun i => Tm.msg A (σ i)) = xs → ∀ U : Finset ℕ, (∀ k ∈ e.nonces, k ∉ U) →
          Runs A ⟨U, {Q.subst σ}⟩ e := by
  induction he with
  | nil => exact fun xs _ => ⟨.nil, trivial, fun σ _ U _ => .nil _⟩
  | @inp K e c m hc _ ih =>
    intro n xs hK
    obtain ⟨Dc, hDc, hDcp, hDcv⟩ := expr_of_derive (G := G) (derive_subset_of_subset hK hc)
    obtain ⟨Q', hQ', hrun⟩ := ih (Fin.snoc (Fin.snoc xs c) m) (Set.insert_subset_iff.2
      ⟨derive.le_closure _ (mem_range_snoc _ _),
        hK.trans (derive.monotone ((range_subset_snoc _ _).trans (range_subset_snoc _ _)))⟩)
    refine ⟨.let_ Dc (.inp (.term (.var (.inr (Fin.last _)))) Q') .nil, ?_, ?_⟩
    · dsimp only [Model.Adversary, Model.PubExpr, Model.PubTerm]
      exact ⟨hDc, ⟨trivial, hQ'⟩, trivial⟩
    · intro σ hσ U hU
      obtain ⟨Mc, hMc⟩ := msg_surjective c
      obtain ⟨Mm, hMm⟩ := msg_surjective m
      refine Runs.let_step hDcp (M := Mc) (by rw [hσ, hDcv, hMc]) ?_
      refine Runs.inp_step (M := Mm) (by simp [msgs_snoc, hMc]) hMm ?_
      exact hrun (Fin.snoc (Fin.snoc σ Mc) Mm) (by rw [msgs_snoc, msgs_snoc, hσ, hMc, hMm]) U
        fun k hk => hU k ((Trace.nonces_sublist (List.sublist_cons_self _ _)).subset hk)
  | @out K e c m hc hm _ ih =>
    intro n xs hK
    obtain ⟨Dc, hDc, hDcp, hDcv⟩ := expr_of_derive (G := G) (derive_subset_of_subset hK hc)
    obtain ⟨Dm, hDm, hDmp, hDmv⟩ := expr_of_derive (G := G) (xs := Fin.snoc xs c)
      (derive_subset_of_subset (hK.trans (derive.monotone (range_subset_snoc _ _))) hm)
    obtain ⟨Q', hQ', hrun⟩ := ih (Fin.snoc (Fin.snoc xs c) m)
      (hK.trans (derive.monotone ((range_subset_snoc _ _).trans (range_subset_snoc _ _))))
    refine ⟨.let_ Dc (.let_ Dm (.out (.term (.var (.inr (Fin.last n).castSucc)))
      (.term (.var (.inr (Fin.last (n + 1))))) Q') .nil) .nil, ?_, ?_⟩
    · dsimp only [Model.Adversary, Model.PubExpr, Model.PubTerm]
      exact ⟨hDc, ⟨hDm, ⟨trivial, trivial, hQ'⟩, trivial⟩, trivial⟩
    · intro σ hσ U hU
      obtain ⟨Mc, hMc⟩ := msg_surjective c
      obtain ⟨Mm, hMm⟩ := msg_surjective m
      refine Runs.let_step hDcp (M := Mc) (by rw [hσ, hDcv, hMc]) ?_
      refine Runs.let_step hDmp (M := Mm) (by rw [msgs_snoc, hσ, hMc, hDmv, hMm]) ?_
      refine Runs.out_step (by simp [msgs_snoc, hMc]) (by simp [msgs_snoc, hMm]) ?_
      exact hrun (Fin.snoc (Fin.snoc σ Mc) Mm) (by rw [msgs_snoc, msgs_snoc, hσ, hMc, hMm]) U
        fun k hk => hU k ((Trace.nonces_sublist (List.sublist_cons_self _ _)).subset hk)
  | @comm K e c m hc hm _ ih =>
    intro n xs hK
    obtain ⟨Dc, hDc, hDcp, hDcv⟩ := expr_of_derive (G := G) (derive_subset_of_subset hK hc)
    obtain ⟨Dm, hDm, hDmp, hDmv⟩ := expr_of_derive (G := G) (xs := Fin.snoc xs c)
      (derive_subset_of_subset (hK.trans (derive.monotone (range_subset_snoc _ _))) hm)
    obtain ⟨Q', hQ', hrun⟩ := ih (Fin.snoc (Fin.snoc (Fin.snoc xs c) m) m)
      (hK.trans (derive.monotone (((range_subset_snoc _ _).trans
        (range_subset_snoc _ _)).trans (range_subset_snoc _ _))))
    refine ⟨.let_ Dc (.let_ Dm (.par (.out (.term (.var (.inr (Fin.last n).castSucc)))
      (.term (.var (.inr (Fin.last (n + 1))))) .nil)
      (.inp (.term (.var (.inr (Fin.last n).castSucc))) Q')) .nil) .nil, ?_, ?_⟩
    · dsimp only [Model.Adversary, Model.PubExpr, Model.PubTerm]
      exact ⟨hDc, ⟨hDm, ⟨⟨trivial, trivial, trivial⟩, trivial, hQ'⟩, trivial⟩, trivial⟩
    · intro σ hσ U hU
      obtain ⟨Mc, hMc⟩ := msg_surjective c
      obtain ⟨Mm, hMm⟩ := msg_surjective m
      refine Runs.let_step hDcp (M := Mc) (by rw [hσ, hDcv, hMc]) ?_
      refine Runs.let_step hDmp (M := Mm) (by rw [msgs_snoc, hσ, hMc, hDmv, hMm]) ?_
      refine Runs.par_step ?_
      simp only [Process.subst, Expr.subst]
      rw [Multiset.singleton_add]
      have h1 : Tm.msg A (Tm.subst (Fin.snoc (Fin.snoc σ Mc) Mm)
          (.var (.inr (Fin.last n).castSucc))) = c := by
        rw [Tm.msg_var_inr]
        simp [hMc]
      have h2 : Tm.msg A (Tm.subst (Fin.snoc (Fin.snoc σ Mc) Mm)
          (.var (.inr (Fin.last (n + 1))))) = m := by
        rw [Tm.msg_var_inr]
        simp [hMm]
      have hs := Step.comm (A := A) (U := U) (Ps := 0) .nil
        (Q'.subst (liftSubst (Fin.snoc (Fin.snoc σ Mc) Mm))) Mm
        (Val.term (Tm.subst (Fin.snoc (Fin.snoc σ Mc) Mm) (.var (.inr (Fin.last n).castSucc))))
        (Val.term (Tm.subst (Fin.snoc (Fin.snoc σ Mc) Mm) (.var (.inr (Fin.last (n + 1))))))
        (Val.term (Tm.subst (Fin.snoc (Fin.snoc σ Mc) Mm) (.var (.inr (Fin.last n).castSucc))))
        (hMm.trans h2.symm)
      rw [h1, h2] at hs
      have hr := hrun (Fin.snoc (Fin.snoc (Fin.snoc σ Mc) Mm) Mm)
        (by rw [msgs_snoc, msgs_snoc, msgs_snoc, hσ, hMc, hMm]) U fun k hk =>
          hU k ((Trace.nonces_sublist (List.sublist_cons_self _ _)).subset hk)
      exact .act hs (.tau .nil (Runs.eqv hr (.cons (subst_inst_eqv Q' _ Mm).symm .zero)))
  | @new K e k hk _ ih =>
    intro n xs hK
    obtain ⟨Q', hQ', hrun⟩ := ih (Fin.snoc xs (Theory.Msg.name k)) (Set.insert_subset_iff.2
      ⟨derive.le_closure _ (mem_range_snoc _ _),
        hK.trans (derive.monotone (range_subset_snoc _ _))⟩)
    refine ⟨.new Q', hQ', ?_⟩
    intro σ hσ U hU
    refine Runs.new_step (hU k (by simp [Trace.nonces])) ?_
    refine hrun (Fin.snoc σ (.var (.inl k))) (by rw [msgs_snoc, hσ]; rfl) (insert k U)
      fun k' hk' hk'U => ?_
    rcases Finset.mem_insert.1 hk'U with rfl | hk'U
    · exact hk hk'
    · exact hU k' (by simp [Trace.nonces, hk']) hk'U

/-! ## Intercepting the protocol's communications

The attacker's knowledge counts every communication on a channel it knows, whoever
received it.  To output such a message the adversary intercepts it and relays it: a
communication between two components of the protocol becomes two communications
through the attacker.  The protocol's trace changes only by splitting communications
into their offers (`CommSplit`), which a run can always do (`Runs.commSplit`).
-/

/-- The `new` and `event` actions of a trace: what a trace of the manual observes. -/
def obs {M : Type} (t : Trace M) : Trace M :=
  t.filter fun a => match a with | .new _ => true | .event _ => true | _ => false

theorem obs_comm {M : Type} (c m : M) (t : Trace M) : obs (.comm c m :: t) = obs t := rfl

theorem obs_new {M : Type} (k : ℕ) (t : Trace M) : obs (.new k :: t) = .new k :: obs t := rfl

theorem obs_event {M : Type} (e : M) (t : Trace M) : obs (.event e :: t) = .event e :: obs t :=
  rfl

theorem obs_append {M : Type} (t t' : Trace M) : obs (t ++ t') = obs t ++ obs t' :=
  List.filter_append t t'

/-- A trace with some communications split into their offers. -/
inductive CommSplit {M : Type} : Trace M → Trace M → Prop
  | nil : CommSplit [] []
  | cons (a : Act M) {t t'} : CommSplit t t' → CommSplit (a :: t) (a :: t')
  | split (c m : M) {t t'} : CommSplit t t' →
      CommSplit (.comm c m :: t) (.out c m :: .inp c m :: t')

theorem Step.comm_inv {U : Finset ℕ} {Ps : Multiset (Process F G Ev 0)} {c m : A.Msg}
    {c' : Config F G Ev} (h : Step A ⟨U, Ps⟩ (some (.comm c m)) c') :
    ∃ N M Q N' P M' R, Ps = .out N M Q ::ₘ .inp N' P ::ₘ R ∧ Val A N (some c) ∧
      Val A M (some m) ∧ Val A N' (some c) ∧ Tm.msg A M' = m ∧
      c' = ⟨U, Q ::ₘ P.inst M' ::ₘ R⟩ := by
  cases h
  case comm => exact ⟨_, _, _, _, _, _, _, rfl, ‹_›, ‹_›, ‹_›, ‹_›, rfl⟩
  all_goals rcases TStep.label ‹_› with h | ⟨_, h⟩ | ⟨_, h⟩ <;> cases h

/-- A run can make its offers instead of a communication. -/
theorem Runs.commSplit {t t' : Trace A.Msg} (h : CommSplit t t') :
    ∀ {c : Config F G Ev}, Runs A c t → Runs A c t' := by
  induction h with
  | nil => exact fun _ => .nil _
  | cons a _ ih =>
    intro c h
    obtain ⟨c₁, c₂, hτ, hs, hr⟩ := h.cons
    exact Runs.tauStar hτ (.act hs (ih hr))
  | split c m _ ih =>
    intro cfg h
    obtain ⟨⟨U, Ps⟩, c₂, hτ, hs, hr⟩ := h.cons
    obtain ⟨N, M, Q, N', P, M', R, rfl, hN, hM, hN', hM', rfl⟩ := hs.comm_inv
    refine Runs.tauStar hτ (.act (.out Q hN hM) (.act ?_ (ih hr)))
    rw [Multiset.cons_swap, Multiset.cons_swap Q, ← hM']
    exact .inp P M' hN'

/-- The attacker's knowledge after its trace: what it received and created. -/
def enemyK (K : Set A.Msg) : Trace A.Msg → Set A.Msg
  | [] => K
  | .inp _ m :: e => enemyK (insert m K) e
  | .new k :: e => enemyK (insert (Theory.Msg.name k) K) e
  | _ :: e => enemyK K e

/-- The attacker can end by outputting anything it knows to itself. -/
theorem Enemy.append_comm {K : Set A.Msg} {e : Trace A.Msg} (h : Enemy K e)
    {c m : A.Msg} (hc : c ∈ derive (enemyK K e)) (hm : m ∈ derive (enemyK K e)) :
    Enemy K (e ++ [.comm c m]) := by
  induction h with
  | nil => exact Enemy.comm c m hc hm Enemy.nil
  | inp c' m' hc' _ ih => exact Enemy.inp c' m' hc' (ih hc hm)
  | out c' m' hc' hm' _ ih => exact Enemy.out c' m' hc' hm' (ih hc hm)
  | comm c' m' hc' hm' _ ih => exact Enemy.comm c' m' hc' hm' (ih hc hm)
  | new k hk _ ih =>
    exact Enemy.new k (by simpa [Trace.nonces_append, Trace.nonces] using hk) (ih hc hm)

theorem TaggedTrace.Comms.append {ι M : Type} {s s' : TaggedTrace ι M} {t t' : Trace M}
    (h : s.Comms t) (h' : s'.Comms t') : (s ++ s').Comms (t ++ t') := by
  induction h with
  | nil => exact h'
  | cons i a _ ih => exact ih.cons i a
  | pair hij c m _ ih => exact ih.pair hij c m

theorem TaggedTrace.proj_append {ι M : Type} [DecidableEq ι] (s s' : TaggedTrace ι M) (i : ι) :
    (s ++ s').proj i = s.proj i ++ s'.proj i := by
  simp [TaggedTrace.proj, List.filter_append]

theorem proj_cons_self {M : Type} (i : Fin 2) (a : Act M) (s : TaggedTrace (Fin 2) M) :
    TaggedTrace.proj ((i, a) :: s) i = a :: s.proj i := by simp

theorem proj_cons_zero_one {M : Type} (a : Act M) (s : TaggedTrace (Fin 2) M) :
    TaggedTrace.proj ((0, a) :: s) 1 = s.proj 1 := by simp

theorem proj_cons_one_zero {M : Type} (a : Act M) (s : TaggedTrace (Fin 2) M) :
    TaggedTrace.proj ((1, a) :: s) 0 = s.proj 0 := by simp

/-- The attacker knowing more can do the same. -/
theorem Enemy.mono {K : Set A.Msg} {e : Trace A.Msg} (h : Enemy K e) :
    ∀ {K' : Set A.Msg}, K ⊆ K' → Enemy K' e := by
  induction h with
  | nil => exact fun _ => Enemy.nil
  | inp c m hc _ ih =>
    exact fun hK => Enemy.inp c m (derive.monotone hK hc) (ih (Set.insert_subset_insert hK))
  | out c m hc hm _ ih =>
    exact fun hK => Enemy.out c m (derive.monotone hK hc) (derive.monotone hK hm) (ih hK)
  | comm c m hc hm _ ih =>
    exact fun hK => Enemy.comm c m (derive.monotone hK hc) (derive.monotone hK hm) (ih hK)
  | new k hk _ ih => exact fun hK => Enemy.new k hk (ih (Set.insert_subset_insert hK))

theorem learn_subset {K K' : Set A.Msg} {a : Act A.Msg} (hK : K ⊆ derive K')
    (ha : ∀ c m, a = .comm c m → c ∈ K → m ∈ derive K') :
    derive (K ∪ {m | ∃ c, a = .comm c m ∧ c ∈ K}) ⊆ derive K' :=
  derive_subset_of_subset (Set.union_subset hK fun _ ⟨c, h, hc⟩ => ha c _ h hc)

theorem subset_attackerKnowledge (K : Set A.Msg) :
    ∀ t : Trace A.Msg, K ⊆ t.attackerKnowledge K
  | [] => subset_rfl
  | _ :: t => (Set.subset_union_left.trans (derive.le_closure _)).trans
      (subset_attackerKnowledge _ t)

/-- A message communicated on a known channel becomes known. -/
theorem mem_attackerKnowledge_of_comm {c m : A.Msg} :
    ∀ {t : Trace A.Msg} {K : Set A.Msg}, c ∈ K → Act.comm c m ∈ t →
      m ∈ t.attackerKnowledge K
  | [], _, _, h => (List.not_mem_nil h).elim
  | a :: t, K, hc, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact subset_attackerKnowledge
        (derive (K ∪ {m' | ∃ c', Act.comm c m = .comm c' m' ∧ c' ∈ K})) t
        (derive.le_closure _ (Set.mem_union_right _ ⟨c, rfl, hc⟩))
    · exact mem_attackerKnowledge_of_comm (t := t)
        (K := derive (K ∪ {m | ∃ c, a = .comm c m ∧ c ∈ K}))
        (Set.subset_union_left.trans (derive.le_closure _) hc) h

/-- An attack is observed by an attack in which the attacker received every message
communicated on a channel it knew, so that it knows what the trace semantics says it
knows; the protocol's trace changes only by splitting communications. -/
theorem intercept {s : TaggedTrace (Fin 2) A.Msg} {t : Trace A.Msg} (hc : s.Comms t) :
    ∀ {K Ka : Set A.Msg} (p e : Trace A.Msg), s.proj 0 = p → s.proj 1 = e → t.Closed →
      Enemy K e → Ka ⊆ derive K →
      ∃ (s' : TaggedTrace (Fin 2) A.Msg) (t' : Trace A.Msg), s'.Comms t' ∧ t'.Closed ∧
        CommSplit p (s'.proj 0) ∧ Enemy K (s'.proj 1) ∧
        (s'.proj 1).nonces = e.nonces ∧ obs t' = obs t ∧ t'.nonces = t.nonces ∧
        t.attackerKnowledge Ka ⊆ derive (enemyK K (s'.proj 1)) := by
  induction hc with
  | nil =>
    rintro K Ka p e rfl rfl _ _ hKa
    exact ⟨[], [], .nil, fun _ h => (List.not_mem_nil h).elim, .nil, Enemy.nil, rfl, rfl,
      rfl, hKa⟩
  | @cons s t i a hc ih =>
    rintro K Ka p e hp he hcl hen hKa
    have hcl' : t.Closed := fun b hb => hcl b (List.mem_cons_of_mem a hb)
    have ha : ¬ a.Unfinished := hcl a List.mem_cons_self
    fin_cases i
    · simp at hp he
      subst hp he
      cases a with
      | out c m => exact (ha (.out c m)).elim
      | inp c m => exact (ha (.inp c m)).elim
      | comm c m =>
        by_cases hcKa : c ∈ Ka
        · obtain ⟨s', t', hc', hcl', hsp, hen', hnon, hobs, hnonces, hknow⟩ :=
            ih _ _ rfl rfl hcl' (Enemy.mono hen (Set.subset_insert m K))
              (learn_subset (K' := insert m K) (a := .comm c m)
                (hKa.trans (derive.monotone (Set.subset_insert _ _))) fun c' m' h _ => by
                  obtain ⟨rfl, rfl⟩ := Act.comm.inj h
                  exact derive.le_closure _ (Set.mem_insert _ _))
          refine ⟨(0, .out c m) :: (1, .inp c m) :: (1, .out c m) :: (0, .inp c m) :: s',
            .comm c m :: .comm c m :: t',
            (hc'.pair (by decide : (1 : Fin 2) ≠ 0) c m).pair (by decide : (0 : Fin 2) ≠ 1) c m,
            List.forall_mem_cons.2 ⟨nofun, List.forall_mem_cons.2 ⟨nofun, hcl'⟩⟩, ?_, ?_, ?_, ?_,
            ?_, ?_⟩
          · rw [proj_cons_self, proj_cons_one_zero, proj_cons_one_zero, proj_cons_self]
            exact .split c m hsp
          · rw [proj_cons_zero_one, proj_cons_self, proj_cons_self, proj_cons_zero_one]
            exact Enemy.inp c m (hKa hcKa) (Enemy.out c m
              (derive.monotone (Set.subset_insert _ _) (hKa hcKa))
              (derive.le_closure _ (Set.mem_insert _ _)) hen')
          · rw [proj_cons_zero_one, proj_cons_self, proj_cons_self, proj_cons_zero_one]
            simpa [Trace.nonces] using hnon
          · simpa [obs_comm] using hobs
          · simpa [Trace.nonces] using hnonces
          · rw [proj_cons_zero_one, proj_cons_self, proj_cons_self, proj_cons_zero_one]
            exact hknow
        · obtain ⟨s', t', hc', hcl', hsp, hen', hnon, hobs, hnonces, hknow⟩ :=
            ih _ _ rfl rfl hcl' hen (learn_subset (K' := K) (a := .comm c m) hKa
              fun c' m' h hc' => by
                obtain ⟨rfl, -⟩ := Act.comm.inj h
                exact absurd hc' hcKa)
          refine ⟨(0, .comm c m) :: s', .comm c m :: t', hc'.cons 0 _,
            List.forall_mem_cons.2 ⟨nofun, hcl'⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [proj_cons_self]
            exact .cons _ hsp
          · rw [proj_cons_zero_one]
            exact hen'
          · rw [proj_cons_zero_one]
            exact hnon
          · simpa [obs_comm] using hobs
          · simpa [Trace.nonces] using hnonces
          · rw [proj_cons_zero_one]
            exact hknow
      | new k =>
        obtain ⟨s', t', hc', hcl', hsp, hen', hnon, hobs, hnonces, hknow⟩ :=
          ih _ _ rfl rfl hcl' hen (learn_subset (K' := K) (a := .new k) hKa
            fun _ _ h _ => nomatch h)
        refine ⟨(0, .new k) :: s', .new k :: t', hc'.cons 0 _,
          List.forall_mem_cons.2 ⟨nofun, hcl'⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [proj_cons_self]
          exact .cons _ hsp
        · rw [proj_cons_zero_one]
          exact hen'
        · rw [proj_cons_zero_one]
          exact hnon
        · simpa [obs_new] using hobs
        · simpa [Trace.nonces] using hnonces
        · rw [proj_cons_zero_one]
          exact hknow
      | event e' =>
        obtain ⟨s', t', hc', hcl', hsp, hen', hnon, hobs, hnonces, hknow⟩ :=
          ih _ _ rfl rfl hcl' hen (learn_subset (K' := K) (a := .event e') hKa
            fun _ _ h _ => nomatch h)
        refine ⟨(0, .event e') :: s', .event e' :: t', hc'.cons 0 _,
          List.forall_mem_cons.2 ⟨nofun, hcl'⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [proj_cons_self]
          exact .cons _ hsp
        · rw [proj_cons_zero_one]
          exact hen'
        · rw [proj_cons_zero_one]
          exact hnon
        · simpa [obs_event] using hobs
        · simpa [Trace.nonces] using hnonces
        · rw [proj_cons_zero_one]
          exact hknow
    · simp at hp he
      subst hp he
      cases hen with
      | inp c m => exact (ha (.inp c m)).elim
      | out c m => exact (ha (.out c m)).elim
      | comm c m hcK hmK hen' =>
        obtain ⟨s', t', hc', hcl', hsp, hen'', hnon, hobs, hnonces, hknow⟩ :=
          ih _ _ rfl rfl hcl' hen' (learn_subset (K' := K) (a := .comm c m) hKa
            fun c' m' h _ => by
              obtain ⟨rfl, rfl⟩ := Act.comm.inj h
              exact hmK)
        refine ⟨(1, .comm c m) :: s', .comm c m :: t', hc'.cons 1 _,
          List.forall_mem_cons.2 ⟨nofun, hcl'⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [proj_cons_one_zero]
          exact hsp
        · rw [proj_cons_self]
          exact Enemy.comm c m hcK hmK hen''
        · rw [proj_cons_self]
          simpa [Trace.nonces] using hnon
        · simpa [obs_comm] using hobs
        · simpa [Trace.nonces] using hnonces
        · rw [proj_cons_self]
          exact hknow
      | new k hk hen' =>
        obtain ⟨s', t', hc', hcl', hsp, hen'', hnon, hobs, hnonces, hknow⟩ :=
          ih _ _ rfl rfl hcl' hen' (learn_subset (K' := insert (Theory.Msg.name k) K)
            (a := .new k) (hKa.trans (derive.monotone (Set.subset_insert _ _)))
            fun _ _ h _ => nomatch h)
        refine ⟨(1, .new k) :: s', .new k :: t', hc'.cons 1 _,
          List.forall_mem_cons.2 ⟨nofun, hcl'⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [proj_cons_one_zero]
          exact hsp
        · rw [proj_cons_self]
          exact Enemy.new k (by rw [hnon]; exact hk) hen''
        · rw [proj_cons_self]
          simpa [Trace.nonces] using hnon
        · simpa [obs_new] using hobs
        · simpa [Trace.nonces] using hnonces
        · rw [proj_cons_self]
          exact hknow
  | @pair s t i j hij c m hc ih =>
    rintro K Ka p e hp he hcl hen hKa
    have hcl' : t.Closed := fun b hb => hcl b (List.mem_cons_of_mem _ hb)
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simp at hp he
      subst hp he
      cases hen with
      | inp _ _ hcK hen' =>
        obtain ⟨s', t', hc', hcl', hsp, hen'', hnon, hobs, hnonces, hknow⟩ :=
          ih _ _ rfl rfl hcl' hen' (learn_subset (K' := insert m K) (a := .comm c m)
            (hKa.trans (derive.monotone (Set.subset_insert _ _))) fun c' m' h _ => by
              obtain ⟨rfl, rfl⟩ := Act.comm.inj h
              exact derive.le_closure _ (Set.mem_insert _ _))
        refine ⟨(0, .out c m) :: (1, .inp c m) :: s', .comm c m :: t',
          hc'.pair (by decide : (0 : Fin 2) ≠ 1) c m,
          List.forall_mem_cons.2 ⟨nofun, hcl'⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [proj_cons_self, proj_cons_one_zero]
          exact .cons _ hsp
        · rw [proj_cons_zero_one, proj_cons_self]
          exact Enemy.inp c m hcK hen''
        · rw [proj_cons_zero_one, proj_cons_self]
          simpa [Trace.nonces] using hnon
        · simpa [obs_comm] using hobs
        · simpa [Trace.nonces] using hnonces
        · rw [proj_cons_zero_one, proj_cons_self]
          exact hknow
    · simp at hp he
      subst hp he
      cases hen with
      | out _ _ hcK hmK hen' =>
        obtain ⟨s', t', hc', hcl', hsp, hen'', hnon, hobs, hnonces, hknow⟩ :=
          ih _ _ rfl rfl hcl' hen' (learn_subset (K' := K) (a := .comm c m) hKa
            fun c' m' h _ => by
              obtain ⟨rfl, rfl⟩ := Act.comm.inj h
              exact hmK)
        refine ⟨(1, .out c m) :: (0, .inp c m) :: s', .comm c m :: t',
          hc'.pair (by decide : (1 : Fin 2) ≠ 0) c m,
          List.forall_mem_cons.2 ⟨nofun, hcl'⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [proj_cons_one_zero, proj_cons_self]
          exact .cons _ hsp
        · rw [proj_cons_self, proj_cons_zero_one]
          exact Enemy.out c m hcK hmK hen''
        · rw [proj_cons_self, proj_cons_zero_one]
          simpa [Trace.nonces] using hnon
        · simpa [obs_comm] using hobs
        · simpa [Trace.nonces] using hnonces
        · rw [proj_cons_self, proj_cons_zero_one]
          exact hknow
    · exact absurd rfl hij

end ProVerif.Specification
