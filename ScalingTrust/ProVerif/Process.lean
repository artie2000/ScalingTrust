/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib.Control.Monad.Cont
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Embedding.Basic

/-!
# Processes

A process represented by a set of possible traces, which are lists of actions.
`out`, `in`, `new` and `event` prepend an action; a family of processes runs
in parallel by merging one trace of each, a matching output and input of two
different components cancelling into a communication; `P | Q` and `!P` are the
merges of two processes and of countably many copies of a process, respectively.
There is no syntax of processes: what a process computes between actions is Lean code.
In particular, a process may be written as a `do` block in the continuation monad `Cont (Proc M)`,
closed with `Proc.run`.

Trace sets are prefix-closed by construction, so a trace is a run so far, and a
process that blocks simply has no longer traces.  `out` and `in` are *unfinished*
actions; a trace with none represents a run in which every communication was
completed.

Names are created by index.  `new` never creates a name that the rest of the
process creates again, and a merge keeps the names created by different
components apart, so the names created in a trace are pairwise distinct.
-/

namespace ProVerif

/-- The messages of the calculus, with the names created by `new`. -/
class Names (M : Type) where
  /-- The `n`-th fresh name. -/
  nonce : ℕ ↪ M

/-- An action.  `out` and `inp` are offers to communicate; a completed
communication leaves no action. -/
inductive Act (M : Type) where
  /-- Offer to send `m` on `c`. -/
  | out (c m : M)
  /-- Offer to receive `m` on `c`. -/
  | inp (c m : M)
  /-- `new a`, creating the `n`-th fresh name. -/
  | new (n : ℕ)
  /-- `event e` -/
  | event (e : M)
  /-- The attacker declares that it knows `m`.  Honest processes never `say`. -/
  | say (m : M)

/-- The nonce indices created in a trace. -/
def nonces : List (Act M) → List ℕ
  | [] => []
  | .new n :: t => n :: nonces t
  | _ :: t => nonces t

/-- A process is a set of traces. -/
abbrev Proc (M : Type) := Set (List (Act M))

/-!
## The merge relation

The merge relation allows us to express what traces may arise from
a collection of processes running concurrently.  It is defined for
a collection indexed arbitrarily, and the cases of two processes and
countably many are analysed.
-/

variable {M ι : Type} [DecidableEq ι]

/-- `Merges f t` means that `t` interleaves the traces `f i`, except that an output of one
component and a matching input of another may meet in a communication which
leaves nothing in `t`.  A derivation is finite, so only finitely many components act. -/
inductive Merges : (ι → List (Act M)) → List (Act M) → Prop
  | nil : Merges (fun _ => []) []
  | act {f t} (i : ι) (a : Act M) : Merges f t →
      Merges (Function.update f i (a :: f i)) (a :: t)
  | comm {f t} {i j : ι} (c m : M) : i ≠ j → Merges f t →
      Merges (Function.update (Function.update f i (.out c m :: f i)) j (.inp c m :: f j)) t

/-! ## Two components -/

@[simp] theorem update_two_zero {α : Type} (u v w : α) : Function.update ![u, v] 0 w = ![w, v] :=
  funext (Fin.forall_fin_two.2 ⟨by simp, by simp⟩)

@[simp] theorem update_two_one {α : Type} (u v w : α) : Function.update ![u, v] 1 w = ![u, w] :=
  funext (Fin.forall_fin_two.2 ⟨by simp, by simp⟩)

theorem Merges.nil₂ : Merges (![[], []] : Fin 2 → List (Act M)) [] := by
  rw [show (![[], []] : Fin 2 → List (Act M)) = fun _ => [] from
    funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)]
  exact .nil

theorem Merges.left {u v t : List (Act M)} (a : Act M) (h : Merges ![u, v] t) :
    Merges ![a :: u, v] (a :: t) := by
  simpa using h.act 0 a

theorem Merges.right {u v t : List (Act M)} (a : Act M) (h : Merges ![u, v] t) :
    Merges ![u, a :: v] (a :: t) := by
  simpa using h.act 1 a

theorem Merges.commL {u v t : List (Act M)} (c m : M) (h : Merges ![u, v] t) :
    Merges ![.out c m :: u, .inp c m :: v] t := by
  simpa using h.comm (i := 0) (j := 1) c m (by decide)

theorem Merges.commR {u v t : List (Act M)} (c m : M) (h : Merges ![u, v] t) :
    Merges ![.inp c m :: u, .out c m :: v] t := by
  simpa using h.comm (i := 1) (j := 0) c m (by decide)

-- TODO : induction principle showing the above 5 constructors are the only possibilities

/-! ##  Countably many processes -/

-- TODO : explain structure of this section and golf it

/-- `x` as component `0`, then the components of `h`: `Fin.cons` for `ℕ`. -/
def cons {α : Type} (x : α) (h : ℕ → α) : ℕ → α
  | 0 => x
  | n + 1 => h n

@[simp] theorem cons_zero {α : Type} (x : α) (h : ℕ → α) : cons x h 0 = x := rfl

@[simp] theorem cons_succ {α : Type} (x : α) (h : ℕ → α) (n : ℕ) : cons x h (n + 1) = h n := rfl

@[simp] theorem update_cons_zero {α : Type} (x : α) (h : ℕ → α) (y : α) :
    Function.update (cons x h) 0 y = cons y h := by
  funext n
  cases n <;> simp

@[simp] theorem update_cons_succ {α : Type} (x : α) (h : ℕ → α) (j : ℕ) (v : α) :
    Function.update (cons x h) (j + 1) v = cons x (Function.update h j v) := by
  funext n
  cases n with
  | zero => simp
  | succ k => by_cases hk : k = j <;> simp [hk]

@[simp] theorem update_zero_comp_succ {α : Type} (f : ℕ → α) (v : α) :
    Function.update f 0 v ∘ Nat.succ = f ∘ Nat.succ :=
  Function.update_comp_eq_of_forall_ne _ _ fun k => Nat.succ_ne_zero k

@[simp] theorem update_succ_comp_succ {α : Type} (f : ℕ → α) (n : ℕ) (v : α) :
    Function.update f (n + 1) v ∘ Nat.succ = Function.update (f ∘ Nat.succ) n v :=
  Function.update_comp_eq_of_injective _ Nat.succ_injective n v

/-- A communication among the components of `g` is one among those of `cons x g`. -/
theorem Merges.cons_comm {x : List (Act M)} {g : ℕ → List (Act M)} {s : List (Act M)}
    (h : Merges (cons x g) s) {i i' : ℕ} (c m : M) (hii' : i ≠ i') :
    Merges (cons x (Function.update (Function.update g i (.out c m :: g i)) i'
      (.inp c m :: g i'))) s := by
  simpa using h.comm (i := i + 1) (j := i' + 1) c m (by omega)

/-- An idle component `0` changes nothing. -/
theorem Merges.cons_nil {g : ℕ → List (Act M)} {s : List (Act M)} (h : Merges g s) :
    Merges (cons [] g) s := by
  induction h with
  | nil =>
    rw [show cons [] (fun _ : ℕ => ([] : List (Act M))) = fun _ => [] from
      funext fun n => by cases n <;> rfl]
    exact .nil
  | act i a _ ih => simpa using ih.act (i + 1) a
  | comm c m hij _ ih => exact ih.cons_comm c m hij

/-- A derivation of `a :: t` is some communications, then `a` by some component `j`,
then a derivation of `t`: `f` is reached from `Function.update f' j (a :: f' j)` by
communications alone. -/
theorem Merges.peel {f : ι → List (Act M)} {a : Act M} {t : List (Act M)}
    (h : Merges f (a :: t)) :
    ∃ j f', Merges f' t ∧ ∀ Φ : (ι → List (Act M)) → Prop,
      (∀ g i i' c m, i ≠ i' → Φ g →
        Φ (Function.update (Function.update g i (.out c m :: g i)) i' (.inp c m :: g i'))) →
      Φ (Function.update f' j (a :: f' j)) → Φ f := by
  generalize hs : a :: t = s at h
  induction h with
  | nil => cases hs
  | act i b h _ =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs
    exact ⟨i, _, h, fun _ _ hΦ => hΦ⟩
  | comm c m hij _ ih =>
    obtain ⟨j, f', h', K⟩ := ih hs
    exact ⟨j, f', h', fun Φ hc hΦ => hc _ _ _ c m hij (K Φ hc hΦ)⟩

/-- Merging `h` into component `1` of a two-component merge. -/
theorem Merges.join {g : Fin 2 → List (Act M)} {t : List (Act M)} (hg : Merges g t)
    {h : ℕ → List (Act M)} (hh : Merges h (g 1)) : Merges (cons (g 0) h) t := by
  have two : ∀ j : Fin 2, j = 0 ∨ j = 1 := Fin.forall_fin_two.2 ⟨.inl rfl, .inr rfl⟩
  induction hg generalizing h with
  | nil => exact hh.cons_nil
  | @act g t i a _ ih =>
    rcases two i with rfl | rfl
    · simp only [Function.update_self, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
        at hh ⊢
      simpa using (ih hh).act 0 a
    · simp only [Function.update_self, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
        at hh ⊢
      obtain ⟨j, h', hh', K⟩ := hh.peel
      exact K (fun h₁ => Merges (cons (g 0) h₁) (a :: t))
        (fun _ _ _ c m hii' hΦ => Merges.cons_comm hΦ c m hii')
        (by simpa using (ih hh').act (j + 1) a)
  | @comm g t i i' c m hii' _ ih =>
    rcases two i with rfl | rfl <;> rcases two i' with rfl | rfl
    · exact absurd rfl hii'
    · simp only [Function.update_self, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
        at hh ⊢
      obtain ⟨j, h', hh', K⟩ := hh.peel
      exact K (fun h₁ => Merges (cons (.out c m :: g 0) h₁) t)
        (fun _ _ _ c' m' hii' hΦ => Merges.cons_comm hΦ c' m' hii')
        (by simpa using (ih hh').comm (i := 0) (j := j + 1) c m (by omega))
    · simp only [Function.update_self, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
        at hh ⊢
      obtain ⟨j, h', hh', K⟩ := hh.peel
      exact K (fun h₁ => Merges (cons (.inp c m :: g 0) h₁) t)
        (fun _ _ _ c' m' hii' hΦ => Merges.cons_comm hΦ c' m' hii')
        (by simpa using (ih hh').comm (i := j + 1) (j := 0) c m (by omega))
    · exact absurd rfl hii'

/-- A merge over `ℕ` is a merge of component `0` with a merge of the rest. -/
theorem Merges.split {f : ℕ → List (Act M)} {t : List (Act M)} (h : Merges f t) :
    ∃ t', Merges (f ∘ Nat.succ) t' ∧ Merges ![f 0, t'] t := by
  induction h with
  | nil => exact ⟨[], .nil, .nil₂⟩
  | @act f t i a _ ih =>
    obtain ⟨t', h', h₀⟩ := ih
    cases i with
    | zero => exact ⟨t', by simpa using h', by simpa using h₀.left a⟩
    | succ n => exact ⟨a :: t', by simpa using h'.act n a, by simpa using h₀.right a⟩
  | @comm f t i j c m hij _ ih =>
    obtain ⟨t', h', h₀⟩ := ih
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hij
      | succ n =>
        exact ⟨.inp c m :: t', by simpa using h'.act n (.inp c m), by simpa using h₀.commL c m⟩
    | succ n =>
      cases j with
      | zero =>
        exact ⟨.out c m :: t', by simpa using h'.act n (.out c m), by simpa using h₀.commR c m⟩
      | succ n' =>
        exact ⟨t', by simpa using h'.comm (i := n) (j := n') c m (by omega), by simpa using h₀⟩

/-! ## Names created by a merge -/

/-- The names a component creates are among those of the merged trace, in order. -/
theorem Merges.nonces_sublist {f : ι → List (Act M)} {t : List (Act M)} (h : Merges f t)
    (i : ι) : (nonces (f i)).Sublist (nonces t) := by
  induction h with
  | nil => simp [nonces]
  | act j a _ ih =>
    by_cases hi : i = j
    · subst hi
      rw [Function.update_self]
      cases a <;> simp [nonces, ih]
    · rw [Function.update_of_ne hi]
      exact ih.trans (by cases a <;> simp [nonces])
  | @comm f t i' j c m hij _ ih =>
    have : nonces (Function.update (Function.update f i' (.out c m :: f i')) j
        (.inp c m :: f j) i) = nonces (f i) := by
      by_cases hj : i = j
      · subst hj; simp [nonces]
      · rw [Function.update_of_ne hj]
        by_cases hi : i = i'
        · subst hi; simp [nonces]
        · rw [Function.update_of_ne hi]
    rw [this]; exact ih

/-! ## Process trace constructors -/

namespace Proc

/-- `0` -/
abbrev nil : Proc M := {[]}

/-- Perform `a`, then behave as `P`. -/
abbrev act (a : Act M) (P : Proc M) : Proc M := insert [] ((a :: ·) '' P)

/-- `out(c, m); P` -/
abbrev out (c m : M) (P : Proc M) : Proc M := act (.out c m) P

/-- `in(c, x); P x` -/
abbrev inp (c : M) (P : M → Proc M) : Proc M := ⋃ m, act (.inp c m) (P m)

/-- `new a; P a`, where `a` is not created again in `P a`. -/
abbrev new [Names M] (P : M → Proc M) : Proc M :=
  ⋃ n, act (.new n) {t ∈ P (Names.nonce n) | n ∉ nonces t}

/-- `event e; P` -/
abbrev event (e : M) (P : Proc M) : Proc M := act (.event e) P

/-- The processes `P i` in parallel, creating distinct names. -/
abbrev merge (P : ι → Proc M) : Proc M :=
  {t | (∃ f, (∀ i, f i ∈ P i) ∧ Merges f t) ∧ (nonces t).Nodup}

/-- `P | Q` -/
abbrev par (P Q : Proc M) : Proc M := merge ![P, Q]

/-- `!P`: an unbounded number of copies of `P` in parallel. -/
abbrev bang (P : Proc M) : Proc M := merge fun _ : ℕ => P

example (c : M) :
    inp c (fun x => out c x nil) =
    {[]} ∪ {[.inp c x] | x} ∪ {[.inp c x, .out c x] | x} := by
  have : Nonempty M := ⟨c⟩
  ext
  simp [inp, out, act, nil]
  grind

example (c m : M) :
    par (out c m .nil) (inp c fun _ => nil) =
    {[], [.out c m]} ∪ {[.inp c x] | x} ∪ {[.inp c x, .out c m] | x} ∪ {[.out c m, .inp c x] | x} := by
  have : Nonempty M := ⟨c⟩
  ext
  simp [Proc.inp, Proc.out, Proc.act, Proc.nil]
  sorry

/-- `!P = P | !P` -/
theorem bang_eq (P : Proc M) : bang P = par P (bang P) := by
  ext t
  constructor
  · rintro ⟨⟨f, hf, h⟩, hn⟩
    obtain ⟨t', h', h₀⟩ := h.split
    exact ⟨⟨![f 0, t'], Fin.forall_fin_two.2 ⟨hf 0, ⟨f ∘ Nat.succ, fun n => hf _, h'⟩,
      hn.sublist (h₀.nonces_sublist 1)⟩, h₀⟩, hn⟩
  · rintro ⟨⟨g, hg, h⟩, hn⟩
    obtain ⟨⟨h', hh', hm⟩, -⟩ := hg 1
    exact ⟨⟨cons (g 0) h', fun n => (match n with | 0 => hg 0 | n + 1 => hh' n), h.join hm⟩, hn⟩

end Proc

/-! ## Completed communications -/

/-- An offer to communicate is unfinished until a partner takes it up. -/
inductive Act.Unfinished : Act M → Prop
  | out (c m : M) : (Act.out c m).Unfinished
  | inp (c m : M) : (Act.inp c m).Unfinished

theorem subset_update {α : Type} {f : ι → List α} {i : ι} {l : List α} (h : f i ⊆ l) (k : ι) :
    f k ⊆ Function.update f i l k := by
  by_cases hk : k = i
  · subst hk; rwa [Function.update_self]
  · exact fun _ h => by rwa [Function.update_of_ne hk]

/-- If no action of the merged trace `w` is unfinished,
every message received in one subtrace was sent in another. -/
theorem Merges.out_of_inp {f : ι → List (Act M)} {w : List (Act M)} {c m : M} {k : ι}
    (h : Merges f w) (hw : ∀ a ∈ w, ¬ a.Unfinished) (hm : Act.inp c m ∈ f k) :
    ∃ i, i ≠ k ∧ Act.out c m ∈ f i := by
  induction h generalizing k with
  | nil => simp at hm
  | @act f t i a _ ih =>
    have hw' : ∀ b ∈ t, ¬ b.Unfinished := fun b hb => hw b (List.mem_cons_of_mem _ hb)
    by_cases hk : k = i
    · subst hk
      rw [Function.update_self] at hm
      rcases List.mem_cons.1 hm with rfl | hm
      · exact (hw _ List.mem_cons_self (.inp _ _)).elim
      · obtain ⟨i', hi', h'⟩ := ih hw' hm
        exact ⟨i', hi', by rwa [Function.update_of_ne hi']⟩
    · rw [Function.update_of_ne hk] at hm
      obtain ⟨i', hi', h'⟩ := ih hw' hm
      exact ⟨i', hi', subset_update (List.subset_cons_self _ _) i' h'⟩
  | @comm f t i j c' m' hij _ ih =>
    have hg : ∀ k, f k ⊆
        Function.update (Function.update f i (Act.out c' m' :: f i)) j (Act.inp c' m' :: f j) k :=
      fun k x hx => subset_update
        (by rw [Function.update_of_ne hij.symm]; exact List.subset_cons_self _ _) k
        (subset_update (List.subset_cons_self _ _) k hx)
    by_cases hk : k = j
    · subst hk
      rw [Function.update_self] at hm
      rcases List.mem_cons.1 hm with h | hm
      · obtain ⟨rfl, rfl⟩ := Act.inp.inj h
        refine ⟨i, hij, ?_⟩
        rw [Function.update_of_ne hij, Function.update_self]
        exact List.mem_cons_self
      · obtain ⟨i', hi', h'⟩ := ih hw hm
        exact ⟨i', hi', hg i' h'⟩
    · rw [Function.update_of_ne hk] at hm
      have hm' : Act.inp c m ∈ f k := by
        by_cases hk' : k = i
        · subst hk'
          rw [Function.update_self] at hm
          rcases List.mem_cons.1 hm with h | hm
          · cases h
          · exact hm
        · rwa [Function.update_of_ne hk'] at hm
      obtain ⟨i', hi', h'⟩ := ih hw hm'
      exact ⟨i', hi', hg i' h'⟩

theorem Merges.out_of_inp₂ {f : Fin 2 → List (Act M)} {w : List (Act M)} {c m : M}
    (h : Merges f w) (hw : ∀ a ∈ w, ¬ a.Unfinished) (hm : Act.inp c m ∈ f 1) :
    Act.out c m ∈ f 0 := by simpa using h.out_of_inp hw (k := 1) hm

/-- Every action of the merged trace was performed by some component. -/
theorem Merges.mem_of_mem {f : ι → List (Act M)} {w : List (Act M)} (h : Merges f w) {a : Act M}
    (ha : a ∈ w) : ∃ i, a ∈ f i := by
  induction h with
  | nil => simp at ha
  | act i b _ ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨i, by simp⟩
    · obtain ⟨i', h'⟩ := ih ha
      exact ⟨i', subset_update (List.subset_cons_self _ _) i' h'⟩
  | comm c m hij _ ih =>
    obtain ⟨i', h'⟩ := ih ha
    exact ⟨i', subset_update
      (by rw [Function.update_of_ne hij.symm]; exact List.subset_cons_self _ _) i'
      (subset_update (List.subset_cons_self _ _) i' h')⟩

/-! ## Process monad constructors -/

namespace Proc

/-- `out(c, m)` -/
def send (c m : M) : Cont (Proc M) Unit := fun k => Proc.out c m (k ())

/-- `in(c, x)`, returning `x`. -/
def recv (c : M) : Cont (Proc M) M := fun k => Proc.inp c k

/-- `new a`, returning `a`. -/
def fresh [Names M] : Cont (Proc M) M := fun k => Proc.new k

/-- `event e` -/
def emit (e : M) : Cont (Proc M) Unit := fun k => Proc.event e (k ())

/-- Fork: the rest of the body runs twice in parallel, with `true` and `false`. -/
def fork : Cont (Proc M) Bool := fun k => Proc.merge k

/-- Replicate the rest of the body. -/
def repl : Cont (Proc M) Unit := fun k => Proc.bang (k ())

/-- Stop here. -/
def stop : Cont (Proc M) α := fun _ => Proc.nil

/-- The traces of a body. -/
def run (b : Cont (Proc M) Unit) : Proc M := b fun _ => Proc.nil

end Proc

end ProVerif
