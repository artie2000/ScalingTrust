/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib.Control.Monad.Cont
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Embedding.Basic

/-!
# Processes

A process is the set of traces it can perform.  Every construct of ProVerif's
calculus is a function on trace sets: `out`, `in`, `new` and `event` prepend an
action, and `P | Q` and `!P` are both the interleaving of a family of trace
sets, which also covers unboundedly many sessions at once.  There is no syntax
of processes; what a role computes between actions is written as Lean code.

Trace sets are prefix-closed by construction, so a trace is a run *so far*.

A role is written as a `do` block in the continuation monad `Cont (Proc M)`;
`Body.run` closes it with `0`.
-/

namespace List

variable {α : Type*}

/-- `Merges l₁ l₂ t`: `t` is a merge of `l₁` and `l₂`, an interleaving that keeps
the order within each.  Isabelle/HOL's `t ∈ shuffles l₁ l₂`. -/
inductive Merges : List α → List α → List α → Prop
  | nil : Merges [] [] []
  | left {a : α} {l₁ l₂ t : List α} : Merges l₁ l₂ t → Merges (a :: l₁) l₂ (a :: t)
  | right {b : α} {l₁ l₂ t : List α} : Merges l₁ l₂ t → Merges l₁ (b :: l₂) (b :: t)

end List

namespace ProVerif

/-- The messages of the calculus, with the names honest parties create. -/
class Names (M : Type) where
  /-- The `n`-th fresh name. -/
  nonce : ℕ ↪ M

/-- An observable action. -/
inductive Act (M : Type) where
  /-- `out(c, m)` -/
  | out (c m : M)
  /-- `in(c, x)` receiving `m` -/
  | inp (c m : M)
  /-- `new a`, creating the `n`-th fresh name -/
  | new (n : ℕ)
  /-- `event e` -/
  | event (e : M)

/-- A process is a set of traces. -/
abbrev Proc (M : Type) := Set (List (Act M))

variable {M : Type}

/-- The actions of the labelled trace `l` that carry the label `i`. -/
def fibre {ι : Type} [DecidableEq ι] (i : ι) (l : List (ι × Act M)) : List (Act M) :=
  (l.filter fun p => decide (p.1 = i)).map Prod.snd

namespace Proc

/-- `0` -/
def nil : Proc M := {[]}

/-- Perform `a`, then behave as `P`. -/
def act (a : Act M) (P : Proc M) : Proc M := insert [] ((a :: ·) '' P)

/-- `out(c, m); P` -/
def out (c m : M) (P : Proc M) : Proc M := act (.out c m) P

/-- `in(c, x); P x` -/
def inp (c : M) (P : M → Proc M) : Proc M := ⋃ m, act (.inp c m) (P m)

/-- `new a; P a` -/
def new [Names M] (P : M → Proc M) : Proc M := ⋃ n, act (.new n) (P (Names.nonce n))

/-- `event e; P` -/
def event (e : M) (P : Proc M) : Proc M := act (.event e) P

/-- `‖ᵢ P i`: the traces that can be labelled so that the actions labelled `i`
form a trace of `P i`.  A finite trace carries finitely many labels, so this is
the interleaving of finitely many of the `P i`, however large `ι` is. -/
def interleave {ι : Type} [DecidableEq ι] (P : ι → Proc M) : Proc M :=
  {t | ∃ l : List (ι × Act M), l.map Prod.snd = t ∧ ∀ i, fibre i l ∈ P i}

/-- `P | Q` -/
def par (P Q : Proc M) : Proc M := interleave ![P, Q]

/-- `!P` -/
def bang (P : Proc M) : Proc M := interleave fun _ : ℕ => P

end Proc

namespace Body

/-- `out(c, m)` -/
def send (c m : M) : Cont (Proc M) Unit := fun k => Proc.out c m (k ())

/-- `in(c, x)`, returning `x`. -/
def recv (c : M) : Cont (Proc M) M := fun k => Proc.inp c k

/-- `new a`, returning `a`. -/
def fresh [Names M] : Cont (Proc M) M := fun k => Proc.new k

/-- `event e` -/
def emit (e : M) : Cont (Proc M) Unit := fun k => Proc.event e (k ())

/-- Spawn one copy of the rest of the body for each element of `ι`, in parallel,
each copy knowing its index.  With the index used this is replication with
session identifiers. -/
def spawn (ι : Type) [DecidableEq ι] : Cont (Proc M) ι := fun k => Proc.interleave k

/-- Fork: the rest of the body runs twice in parallel, with `true` and `false`. -/
def fork : Cont (Proc M) Bool := spawn Bool

/-- Replicate the rest of the body. -/
def bang : Cont (Proc M) Unit := fun k => Proc.bang (k ())

/-- Stop here. -/
def stop : Cont (Proc M) α := fun _ => Proc.nil

/-- The traces of a body. -/
def run (b : Cont (Proc M) Unit) : Proc M := b fun _ => Proc.nil

end Body

/-! ### `par` and `bang` in terms of binary merges -/

@[simp] theorem fibre_nil {ι : Type} [DecidableEq ι] (i : ι) :
    fibre i ([] : List (ι × Act M)) = [] := rfl

@[simp] theorem fibre_cons {ι : Type} [DecidableEq ι] (i j : ι) (a : Act M)
    (l : List (ι × Act M)) :
    fibre i ((j, a) :: l) = if j = i then a :: fibre i l else fibre i l := by
  unfold fibre
  by_cases h : j = i <;> simp [h]

/-- A `Fin 2`-labelled trace is a merge of its two fibres. -/
theorem merges_fibres : ∀ l : List (Fin 2 × Act M),
    List.Merges (fibre 0 l) (fibre 1 l) (l.map Prod.snd)
  | [] => .nil
  | (i, a) :: l => by
    revert i
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · simpa using (merges_fibres l).left (a := a)
    · simpa using (merges_fibres l).right (b := a)

/-- Conversely, a merge can be labelled by `Fin 2`. -/
theorem exists_labelling {u v t : List (Act M)} (h : List.Merges u v t) :
    ∃ l : List (Fin 2 × Act M), l.map Prod.snd = t ∧ fibre 0 l = u ∧ fibre 1 l = v := by
  induction h with
  | nil => exact ⟨[], rfl, rfl, rfl⟩
  | @left a _ _ _ _ ih =>
    obtain ⟨l, rfl, rfl, rfl⟩ := ih
    exact ⟨(0, a) :: l, by simp, by simp, by simp⟩
  | @right b _ _ _ _ ih =>
    obtain ⟨l, rfl, rfl, rfl⟩ := ih
    exact ⟨(1, b) :: l, by simp, by simp, by simp⟩

/-- Splitting the label `0` off an `ℕ`-labelled trace, the other labels shifting down. -/
theorem merges_fibre_zero : ∀ l : List (ℕ × Act M), ∃ l' : List (ℕ × Act M),
    List.Merges (fibre 0 l) (l'.map Prod.snd) (l.map Prod.snd) ∧
      ∀ j, fibre j l' = fibre (j + 1) l
  | [] => ⟨[], .nil, fun _ => rfl⟩
  | (0, a) :: l => by
    obtain ⟨l', hs, hf⟩ := merges_fibre_zero l
    exact ⟨l', by simpa using hs.left (a := a), fun j => by simp [hf]⟩
  | (k + 1, a) :: l => by
    obtain ⟨l', hs, hf⟩ := merges_fibre_zero l
    exact ⟨(k, a) :: l', by simpa using hs.right (b := a), fun j => by simp [hf]⟩

/-- Labelling a merge of `u` with an `ℕ`-labelled `v`: `u` gets label `0` and the
labels of `v` shift up. -/
theorem exists_labelling_nat {u v t : List (Act M)} (h : List.Merges u v t) :
    ∀ l' : List (ℕ × Act M), l'.map Prod.snd = v → ∃ l : List (ℕ × Act M),
      l.map Prod.snd = t ∧ fibre 0 l = u ∧ ∀ j, fibre (j + 1) l = fibre j l' := by
  induction h with
  | nil =>
    intro l' hl'
    rw [List.map_eq_nil_iff] at hl'
    subst hl'
    exact ⟨[], rfl, rfl, fun _ => rfl⟩
  | @left a _ _ _ _ ih =>
    intro l' hl'
    obtain ⟨l, rfl, rfl, hf⟩ := ih l' hl'
    exact ⟨(0, a) :: l, by simp, by simp, fun j => by simp [hf]⟩
  | @right b _ _ _ _ ih =>
    rintro (_ | ⟨⟨i, c⟩, l'⟩) hl'
    · simp at hl'
    · simp only [List.map_cons, List.cons.injEq] at hl'
      obtain ⟨hc, hl'⟩ := hl'
      obtain ⟨l, rfl, rfl, hf⟩ := ih l' hl'
      exact ⟨(i + 1, b) :: l, by simp, by simp, fun j => by simp [hf, hc]⟩

namespace Proc

/-- `P | Q` is the set of merges of a trace of `P` with a trace of `Q`. -/
theorem mem_par {P Q : Proc M} {t : List (Act M)} :
    t ∈ par P Q ↔ ∃ u ∈ P, ∃ v ∈ Q, List.Merges u v t := by
  constructor
  · rintro ⟨l, rfl, h⟩
    exact ⟨_, by simpa using h 0, _, by simpa using h 1, merges_fibres l⟩
  · rintro ⟨u, hu, v, hv, h⟩
    obtain ⟨l, rfl, rfl, rfl⟩ := exists_labelling h
    exact ⟨l, rfl, Fin.forall_fin_two.2 ⟨by simpa using hu, by simpa using hv⟩⟩

/-- `!P` is `P | !P`: one more copy can always be split off. -/
theorem bang_eq_par (P : Proc M) : bang P = par P (bang P) := by
  ext t
  rw [mem_par]
  constructor
  · rintro ⟨l, rfl, h⟩
    obtain ⟨l', hs, hf⟩ := merges_fibre_zero l
    exact ⟨_, h 0, _, ⟨l', rfl, fun j => by rw [hf]; exact h _⟩, hs⟩
  · rintro ⟨u, hu, v, ⟨l', rfl, hl'⟩, h⟩
    obtain ⟨l, rfl, rfl, hf⟩ := exists_labelling_nat h l' rfl
    refine ⟨l, rfl, fun j => ?_⟩
    cases j with
    | zero => exact hu
    | succ j => rw [hf]; exact hl' j

/-- The fixed-point equation of `!P`, with the empty trace made explicit. -/
theorem bang_eq_nil_union_par {P : Proc M} (h : [] ∈ P) :
    bang P = nil ∪ par P (bang P) := by
  rw [← bang_eq_par]
  refine (Set.union_eq_right.2 ?_).symm
  rintro _ rfl
  exact ⟨[], rfl, fun _ => h⟩

end Proc

example (c : M) :
    Proc.inp c (fun x => Proc.out c x Proc.nil) =
    {[]} ∪ {[Act.inp c x] | x} ∪ {[Act.inp c x, Act.out c x] | x} := by
  have : Nonempty M := ⟨c⟩
  ext
  simp [Proc.inp, Proc.out, Proc.act, Proc.nil]
  grind

end ProVerif
