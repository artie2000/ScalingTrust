/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib.Control.Monad.Cont
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Embedding.Basic
import Mathlib.Tactic.FinCases

/-!
# Processes

A process represented by a set of possible traces, which are lists of actions.
`out`, `in`, `new` and `event` prepend an action.  A family of processes runs in
parallel in two stages: their traces are interleaved, each action tagged with the
component that performed it, and then an output immediately followed by a matching
input of a *different* component may meet in a communication, which the trace
records as a single `comm` action.  `P | Q` and `!P` are the merges of two processes and of countably
many copies of a process, respectively.
There is no syntax of processes: what a process computes between actions is Lean code.
A ProVerif process is translated to a `do` block in the continuation monad
`Cont (Proc M)`, closed with `Proc.run`: `Proc.send`, `Proc.recv`, `Proc.fresh` and
`Proc.emit` for its actions, `Proc.fork` and `Proc.repl` for `|` and `!`, and Lean's
`match` and `if` for `let` and `if`.

Trace sets are prefix-closed by construction, so a trace is a run so far, and a
process that blocks simply has no longer traces.  `out` and `in` are *unfinished*
actions; a trace with none represents a run in which every communication was
completed.

Names are created by index.  `new` never creates a name that the rest of the
process creates again, and a merge keeps the names created by different
components apart, so the names created in a trace are pairwise distinct.
-/

namespace ProVerif

variable {M ι : Type}

/-- The messages of the calculus, with the names created by `new`. -/
class Names (M : Type) where
  /-- The `n`-th fresh name. -/
  nonce : ℕ ↪ M

/-- An action.  `out` and `inp` are offers to communicate; `comm` is a completed
communication. -/
inductive Act (M : Type) where
  /-- Offer to send `m` on `c`. -/
  | out (c m : M)
  /-- Offer to receive `m` on `c`. -/
  | inp (c m : M)
  /-- `m` sent and received on `c`. -/
  | comm (c m : M)
  /-- `new a`, creating the `n`-th fresh name. -/
  | new (n : ℕ)
  /-- `event e` -/
  | event (e : M)
  deriving DecidableEq

/-- An offer to communicate is unfinished until a partner takes it up. -/
inductive Act.Unfinished : Act M → Prop
  | out (c m : M) : (Act.out c m).Unfinished
  | inp (c m : M) : (Act.inp c m).Unfinished

/-- A trace is a list of actions. -/
abbrev Trace (M : Type) := List (Act M)

/-- A trace is closed if it has no unfinished actions. -/
abbrev Closed (t : Trace M) : Prop := ∀ a ∈ t, ¬ a.Unfinished

/-- The nonce indices created in a trace. -/
def nonces : List (Act M) → List ℕ
  | [] => []
  | .new n :: t => n :: nonces t
  | _ :: t => nonces t

theorem nonces_sublist {l₁ l₂ : List (Act M)} (h : l₁.Sublist l₂) :
    (nonces l₁).Sublist (nonces l₂) := by
  induction h with
  | slnil => exact .slnil
  | cons a _ ih => exact ih.trans (by cases a <;> simp [nonces])
  | cons_cons a _ ih => cases a <;> simp [nonces, ih]

/-- A process is a set of traces. -/
abbrev Proc (M : Type) := Set (Trace M)

/-! ## Communication -/

section interleave

variable [DecidableEq ι]

/-- The trace of component `i` in the tagged trace `s`. -/
def proj (i : ι) (s : List (ι × Act M)) : Trace M := (s.filter (·.1 = i)).map Prod.snd

@[simp] theorem proj_nil (i : ι) : proj i ([] : List (ι × Act M)) = [] := rfl

@[simp] theorem proj_cons (i j : ι) (a : Act M) (s : List (ι × Act M)) :
    proj i ((j, a) :: s) = if j = i then a :: proj i s else proj i s := by
  by_cases h : j = i <;> simp [proj, h]

@[simp] theorem proj_append (i : ι) (s s' : List (ι × Act M)) :
    proj i (s ++ s') = proj i s ++ proj i s' := by
  simp [proj, List.filter_append]

theorem mem_proj {i : ι} {a : Act M} {s : List (ι × Act M)} : a ∈ proj i s ↔ (i, a) ∈ s := by
  simp only [proj, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨x, ⟨hs, rfl⟩, rfl⟩
    exact hs
  · intro hs
    exact ⟨(i, a), ⟨hs, rfl⟩, rfl⟩

/-- `s` interleaves the traces `f i`, each action tagged with its component:
every component reads its own trace back off `s`. -/
def Interleaves (f : ι → Trace M) (s : List (ι × Act M)) : Prop := ∀ i, proj i s = f i

theorem Interleaves.mem_iff {f : ι → Trace M} {s : List (ι × Act M)} (h : Interleaves f s)
    {i : ι} {a : Act M} : (i, a) ∈ s ↔ a ∈ f i := by
  rw [← h i, mem_proj]

end interleave

/-- The traces obtained from a tagged interleaving by letting an output immediately
followed by a matching input of a different component meet in a communication,
recorded as `comm`. -/
def comms : List (ι × Act M) → Set (Trace M)
  | [] => {[]}
  | (i, .out c m) :: (j, .inp c' m') :: s =>
      (Act.out c m :: ·) '' comms ((j, .inp c' m') :: s) ∪
        (Act.comm c m :: ·) '' {t ∈ comms s | i ≠ j ∧ c = c' ∧ m = m'}
  | (_, a) :: s => (a :: ·) '' comms s

theorem mem_comms_cons {s : List (ι × Act M)} {t : Trace M} (h : t ∈ comms s) (i : ι)
    (a : Act M) : a :: t ∈ comms ((i, a) :: s) := by
  rcases s with _ | ⟨⟨j, b⟩, s⟩ <;> cases a <;> (try cases b) <;>
    first | exact Or.inl ⟨t, h, rfl⟩ | exact ⟨t, h, rfl⟩

theorem mem_comms_pair {s : List (ι × Act M)} {t : Trace M} {i j : ι} (hij : i ≠ j) (c m : M)
    (h : t ∈ comms s) : Act.comm c m :: t ∈ comms ((i, .out c m) :: (j, .inp c m) :: s) := by
  rw [comms.eq_2]
  exact Or.inr ⟨t, ⟨h, hij, rfl, rfl⟩, rfl⟩

/-- Retagging with an injection preserves communication. -/
theorem comms_retag {κ : Type} {φ : ι → κ} (hφ : Function.Injective φ)
    {s : List (ι × Act M)} {t : Trace M} (h : t ∈ comms s) :
    t ∈ comms (s.map (Prod.map φ id)) := by
  induction s using comms.induct generalizing t with
  | case1 => simpa [comms] using h
  | case2 i c m j c' m' s ih₁ ih₂ =>
    rw [comms.eq_2] at h
    rcases h with ⟨t₀, h₀, rfl⟩ | ⟨t₀, ⟨h₀, hij, rfl, rfl⟩, rfl⟩
    · exact mem_comms_cons (ih₁ h₀) (φ i) _
    · exact mem_comms_pair (hφ.ne hij) _ _ (ih₂ h₀)
  | case3 i a s hne ih =>
    rw [comms.eq_3 _ _ _ hne] at h
    obtain ⟨t₀, h₀, rfl⟩ := h
    exact mem_comms_cons (ih h₀) (φ i) a

/-- A trace `a :: t` arises from the first action of `s`, or from a communication of its
first two actions. -/
theorem peel {s : List (ι × Act M)} {a : Act M} {t : Trace M} (h : a :: t ∈ comms s) :
    (∃ i s', s = (i, a) :: s' ∧ t ∈ comms s') ∨
      ∃ c m i j s', a = .comm c m ∧ i ≠ j ∧ s = (i, .out c m) :: (j, .inp c m) :: s' ∧
        t ∈ comms s' := by
  induction s using comms.induct generalizing t with
  | case1 => simp [comms] at h
  | case2 i c m j c' m' s _ _ =>
    rw [comms.eq_2] at h
    rcases h with ⟨t₀, h₀, ht⟩ | ⟨t₀, ⟨h₀, hij, rfl, rfl⟩, ht⟩
    · obtain ⟨rfl, rfl⟩ := List.cons.inj ht
      exact Or.inl ⟨i, _, rfl, h₀⟩
    · obtain ⟨rfl, rfl⟩ := List.cons.inj ht
      exact Or.inr ⟨c, m, i, j, s, rfl, hij, rfl, h₀⟩
  | case3 i b s hne _ =>
    rw [comms.eq_3 _ _ _ hne] at h
    obtain ⟨t₀, h₀, ht⟩ := h
    obtain ⟨rfl, rfl⟩ := List.cons.inj ht
    exact Or.inl ⟨i, s, rfl, h₀⟩

/-- Communication removes only offers, so the names created are those of the interleaving. -/
theorem nonces_of_mem_comms {s : List (ι × Act M)} {t : Trace M} (h : t ∈ comms s) :
    nonces t = nonces (s.map Prod.snd) := by
  induction s using comms.induct generalizing t with
  | case1 =>
    obtain rfl : t = [] := h
    rfl
  | case2 i c m j c' m' s ih₁ ih₂ =>
    rw [comms.eq_2] at h
    rcases h with ⟨t₀, h₀, rfl⟩ | ⟨t₀, ⟨h₀, -, rfl, rfl⟩, rfl⟩
    · simpa [nonces] using ih₁ h₀
    · simpa [nonces] using ih₂ h₀
  | case3 i a s hne ih =>
    rw [comms.eq_3 _ _ _ hne] at h
    obtain ⟨t₀, h₀, rfl⟩ := h
    cases a <;> simp [nonces, ih h₀]

/-! ## Process trace constructors -/

namespace Proc

/-- `0` -/
abbrev nil : Proc M := {[]}

/-- Perform `a`, then behave as `P`. -/
def act (a : Act M) (P : Proc M) : Proc M := insert [] ((a :: ·) '' P)

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
def merge [DecidableEq ι] (P : ι → Proc M) : Proc M :=
  {t | (∃ f s, (∀ i, f i ∈ P i) ∧ Interleaves f s ∧ t ∈ comms s) ∧ (nonces t).Nodup}

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

/-! ### Countably many copies

`!P = P | !P` relates a tagged trace over `ℕ` to one over `Fin 2`: component `0` on
one side, and on the other the trace that the remaining components produce among
themselves, in which their offers to component `0` are still unfinished.
-/

/-- `x` as component `0`, then the components of `h`. -/
def cons {α : Type} (x : α) (h : ℕ → α) : ℕ → α
  | 0 => x
  | n + 1 => h n

/-- Drop the entries of component `0` and shift the other tags down. -/
def dec : List (ℕ × Act M) → List (ℕ × Act M) :=
  List.filterMap fun | (0, _) => none | (n + 1, a) => some (n, a)

@[simp] theorem dec_nil : dec ([] : List (ℕ × Act M)) = [] := rfl

@[simp] theorem dec_cons_zero (a : Act M) (s : List (ℕ × Act M)) : dec ((0, a) :: s) = dec s := rfl

@[simp] theorem dec_cons_succ (n : ℕ) (a : Act M) (s : List (ℕ × Act M)) :
    dec ((n + 1, a) :: s) = (n, a) :: dec s := rfl

theorem dec_sublist (s : List (ℕ × Act M)) : ((dec s).map Prod.snd).Sublist (s.map Prod.snd) := by
  induction s with
  | nil => exact .slnil
  | cons x s ih =>
    obtain ⟨i, a⟩ := x
    cases i with
    | zero => exact ih.trans (List.sublist_cons_self _ _)
    | succ n => exact ih.cons_cons a

theorem proj_dec (s : List (ℕ × Act M)) (n : ℕ) : proj n (dec s) = proj (n + 1) s := by
  induction s with
  | nil => rfl
  | cons x s ih =>
    obtain ⟨i, a⟩ := x
    cases i with
    | zero => simpa using ih
    | succ k => by_cases hk : k = n <;> simp [hk, ih]

/-- Shift all tags up. -/
def inc : List (ℕ × Act M) → List (ℕ × Act M) := List.map (Prod.map Nat.succ id)

@[simp] theorem inc_nil : inc ([] : List (ℕ × Act M)) = [] := rfl

@[simp] theorem inc_cons (i : ℕ) (a : Act M) (s : List (ℕ × Act M)) :
    inc ((i, a) :: s) = (i + 1, a) :: inc s := rfl

theorem proj_inc_zero (s : List (ℕ × Act M)) : proj 0 (inc s) = [] := by
  induction s with
  | nil => rfl
  | cons x s ih =>
    obtain ⟨i, a⟩ := x
    simpa using ih

theorem proj_inc_succ (s : List (ℕ × Act M)) (n : ℕ) : proj (n + 1) (inc s) = proj n s := by
  induction s with
  | nil => rfl
  | cons x s ih =>
    obtain ⟨i, a⟩ := x
    by_cases hk : i = n <;> simp [hk, ih]

/-- `t` splits as component `0` of `s` against the trace `t'` that the other components
of `s` produce among themselves. -/
def Splits (s : List (ℕ × Act M)) (t : Trace M) : Prop :=
  ∃ (t' : Trace M) (s₂ : List (Fin 2 × Act M)), t' ∈ comms (dec s) ∧ t ∈ comms s₂ ∧
    proj 0 s₂ = proj 0 s ∧ proj 1 s₂ = t'

theorem Splits.cons {s : List (ℕ × Act M)} {t : Trace M} (h : Splits s t) (i : ℕ) (a : Act M) :
    Splits ((i, a) :: s) (a :: t) := by
  obtain ⟨t', s₂, h1, h2, h3, h4⟩ := h
  cases i with
  | zero =>
    exact ⟨t', (0, a) :: s₂, by simpa using h1, mem_comms_cons h2 0 a, by simpa using h3,
      by simpa using h4⟩
  | succ n =>
    exact ⟨a :: t', (1, a) :: s₂, by simpa using mem_comms_cons h1 n a, mem_comms_cons h2 1 a,
      by simpa using h3, by simpa using h4⟩

theorem Splits.pair {s : List (ℕ × Act M)} {t : Trace M} (h : Splits s t) {i j : ℕ} (hij : i ≠ j)
    (c m : M) : Splits ((i, .out c m) :: (j, .inp c m) :: s) (.comm c m :: t) := by
  obtain ⟨t', s₂, h1, h2, h3, h4⟩ := h
  rcases i with _ | n <;> rcases j with _ | n'
  · exact absurd rfl hij
  · exact ⟨.inp c m :: t', (0, .out c m) :: (1, .inp c m) :: s₂,
      by simpa using mem_comms_cons h1 n' (.inp c m), mem_comms_pair (by decide) c m h2,
      by simpa using h3, by simpa using h4⟩
  · exact ⟨.out c m :: t', (1, .out c m) :: (0, .inp c m) :: s₂,
      by simpa using mem_comms_cons h1 n (.out c m), mem_comms_pair (by decide) c m h2,
      by simpa using h3, by simpa using h4⟩
  · exact ⟨.comm c m :: t', (1, .comm c m) :: s₂,
      by simpa using mem_comms_pair (by omega : n ≠ n') c m h1, mem_comms_cons h2 1 _,
      by simpa using h3, by simpa using h4⟩

/-- Splitting off component `0`. -/
theorem split {s : List (ℕ × Act M)} {t : Trace M} (h : t ∈ comms s) : Splits s t := by
  induction s using comms.induct generalizing t with
  | case1 =>
    obtain rfl : t = [] := h
    exact ⟨[], [], by simp [comms], by simp [comms], rfl, rfl⟩
  | case2 i c m j c' m' s ih₁ ih₂ =>
    rw [comms.eq_2] at h
    rcases h with ⟨t₀, h₀, rfl⟩ | ⟨t₀, ⟨h₀, hij, rfl, rfl⟩, rfl⟩
    · exact (ih₁ h₀).cons i _
    · exact (ih₂ h₀).pair hij _ _
  | case3 i a s hne ih =>
    rw [comms.eq_3 _ _ _ hne] at h
    obtain ⟨t₀, h₀, rfl⟩ := h
    exact (ih h₀).cons i a

/-- The components of `s'` can be merged into component `1` of `s₂`, producing `t`. -/
def Joins (s₂ : List (Fin 2 × Act M)) (s' : List (ℕ × Act M)) (t : Trace M) : Prop :=
  ∃ s : List (ℕ × Act M), t ∈ comms s ∧ proj 0 s = proj 0 s₂ ∧ ∀ n, proj (n + 1) s = proj n s'

theorem Joins.cons₀ {s₂ : List (Fin 2 × Act M)} {s' : List (ℕ × Act M)} {t : Trace M}
    (h : Joins s₂ s' t) (a : Act M) : Joins ((0, a) :: s₂) s' (a :: t) := by
  obtain ⟨s, hs1, hs2, hs3⟩ := h
  exact ⟨(0, a) :: s, mem_comms_cons hs1 0 a, by simpa using hs2, fun n => by simpa using hs3 n⟩

theorem Joins.cons₁ {s₂ : List (Fin 2 × Act M)} {s'' : List (ℕ × Act M)} {t : Trace M}
    (h : Joins s₂ s'' t) (k : ℕ) (a : Act M) : Joins ((1, a) :: s₂) ((k, a) :: s'') (a :: t) := by
  obtain ⟨s, hs1, hs2, hs3⟩ := h
  refine ⟨(k + 1, a) :: s, mem_comms_cons hs1 (k + 1) a, by simpa using hs2, fun n => ?_⟩
  by_cases hk : k = n <;> simpa [hk] using hs3 n

/-- Components `k` and `k'` of `s''` communicate among themselves. -/
theorem Joins.pair₁₁ {s₂ : List (Fin 2 × Act M)} {s'' : List (ℕ × Act M)} {t : Trace M}
    (h : Joins s₂ s'' t) {k k' : ℕ} (hkk' : k ≠ k') (c m : M) :
    Joins ((1, .comm c m) :: s₂) ((k, .out c m) :: (k', .inp c m) :: s'') (.comm c m :: t) := by
  obtain ⟨s, hs1, hs2, hs3⟩ := h
  refine ⟨(k + 1, .out c m) :: (k' + 1, .inp c m) :: s, mem_comms_pair (by omega) c m hs1,
    by simpa using hs2, fun n => ?_⟩
  by_cases hk : k = n <;> by_cases hk' : k' = n <;> simpa [hk, hk'] using hs3 n

theorem Joins.pair₀₁ {s₂ : List (Fin 2 × Act M)} {s'' : List (ℕ × Act M)} {t : Trace M}
    (h : Joins s₂ s'' t) (k : ℕ) (c m : M) :
    Joins ((0, .out c m) :: (1, .inp c m) :: s₂) ((k, .inp c m) :: s'') (.comm c m :: t) := by
  obtain ⟨s, hs1, hs2, hs3⟩ := h
  refine ⟨(0, .out c m) :: (k + 1, .inp c m) :: s, mem_comms_pair (by omega) c m hs1,
    by simpa using hs2, fun n => ?_⟩
  by_cases hk : k = n <;> simpa [hk] using hs3 n

theorem Joins.pair₁₀ {s₂ : List (Fin 2 × Act M)} {s'' : List (ℕ × Act M)} {t : Trace M}
    (h : Joins s₂ s'' t) (k : ℕ) (c m : M) :
    Joins ((1, .out c m) :: (0, .inp c m) :: s₂) ((k, .out c m) :: s'') (.comm c m :: t) := by
  obtain ⟨s, hs1, hs2, hs3⟩ := h
  refine ⟨(k + 1, .out c m) :: (0, .inp c m) :: s, mem_comms_pair (by omega) c m hs1,
    by simpa using hs2, fun n => ?_⟩
  by_cases hk : k = n <;> simpa [hk] using hs3 n

theorem join_cons {s₂ : List (Fin 2 × Act M)} {t : Trace M} {i : Fin 2} {a : Act M}
    (ih : ∀ s', proj 1 s₂ ∈ comms s' → Joins s₂ s' t) {s' : List (ℕ × Act M)}
    (h' : proj 1 ((i, a) :: s₂) ∈ comms s') : Joins ((i, a) :: s₂) s' (a :: t) := by
  fin_cases i
  · exact (ih s' (by simpa using h')).cons₀ a
  · rcases peel (by simpa using h' : a :: proj 1 s₂ ∈ comms s') with
      ⟨k, s'', rfl, ht''⟩ | ⟨c, m, k, k', s'', rfl, hkk', rfl, ht''⟩
    · exact (ih s'' ht'').cons₁ k a
    · exact (ih s'' ht'').pair₁₁ hkk' c m

/-- Merging the components of `s'` into component `1` of the two-component trace `s₂`. -/
theorem join {s₂ : List (Fin 2 × Act M)} {t : Trace M} (h : t ∈ comms s₂)
    {s' : List (ℕ × Act M)} (h' : proj 1 s₂ ∈ comms s') : Joins s₂ s' t := by
  induction s₂ using comms.induct generalizing t s' with
  | case1 =>
    obtain rfl : t = [] := h
    exact ⟨inc s', comms_retag Nat.succ_injective h', by simp [proj_inc_zero], proj_inc_succ s'⟩
  | case2 i c m j c' m' s₂ ih₁ ih₂ =>
    rw [comms.eq_2] at h
    rcases h with ⟨t₀, h₀, rfl⟩ | ⟨t₀, ⟨h₀, hij, rfl, rfl⟩, rfl⟩
    · exact join_cons (fun _ => ih₁ h₀) h'
    · fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · rcases peel (by simpa using h' : .inp _ _ :: proj 1 s₂ ∈ comms s') with
          ⟨k, s'', rfl, ht''⟩ | ⟨_, _, _, _, _, h, _⟩
        · exact (ih₂ h₀ ht'').pair₀₁ k _ _
        · cases h
      · rcases peel (by simpa using h' : .out _ _ :: proj 1 s₂ ∈ comms s') with
          ⟨k, s'', rfl, ht''⟩ | ⟨_, _, _, _, _, h, _⟩
        · exact (ih₂ h₀ ht'').pair₁₀ k _ _
        · cases h
      · exact absurd rfl hij
  | case3 i a s₂ hne ih =>
    rw [comms.eq_3 _ _ _ hne] at h
    obtain ⟨t₀, h₀, rfl⟩ := h
    exact join_cons (fun _ => ih h₀) h'

/-- `!P = P | !P` -/
theorem bang_eq (P : Proc M) : bang P = par P (bang P) := by
  ext t
  constructor
  · rintro ⟨⟨f, s, hf, hi, ht⟩, hn⟩
    obtain ⟨t', s₂, h1, h2, h3, h4⟩ := split ht
    have hn' : (nonces t').Nodup := by
      rw [nonces_of_mem_comms h1]
      rw [nonces_of_mem_comms ht] at hn
      exact hn.sublist (nonces_sublist (dec_sublist s))
    exact ⟨⟨![f 0, t'], s₂, Fin.forall_fin_two.2 ⟨hf 0, ⟨⟨f ∘ Nat.succ, dec s, fun n => hf _,
      fun n => (proj_dec s n).trans (hi (n + 1)), h1⟩, hn'⟩⟩,
      Fin.forall_fin_two.2 ⟨h3.trans (hi 0), h4⟩, h2⟩, hn⟩
  · rintro ⟨⟨g, s₂, hg, hi, ht⟩, hn⟩
    obtain ⟨⟨h, s', hh, hi', ht'⟩, -⟩ := hg 1
    obtain ⟨s, hs1, hs2, hs3⟩ := join ht (by rw [hi 1]; exact ht')
    exact ⟨⟨cons (g 0) h, s, fun n => (match n with | 0 => hg 0 | n + 1 => hh n),
      fun n => (match n with | 0 => hs2.trans (hi 0) | n + 1 => (hs3 n).trans (hi' n)), hs1⟩, hn⟩

end Proc

/-! ## Process monad constructors -/

namespace Proc

/-- `out(c, m)` -/
abbrev send (c m : M) : Cont (Proc M) Unit := fun k => Proc.out c m (k ())

/-- `in(c, x)`, returning `x`. -/
abbrev recv (c : M) : Cont (Proc M) M := fun k => Proc.inp c k

/-- `new a`, returning `a`. -/
abbrev fresh [Names M] : Cont (Proc M) M := fun k => Proc.new k

/-- `event e` -/
abbrev emit (e : M) : Cont (Proc M) Unit := fun k => Proc.event e (k ())

/-- Fork: the rest of the body runs twice in parallel, with `true` and `false`. -/
abbrev fork : Cont (Proc M) Bool := fun k => Proc.par (k true) (k false)

/-- Replicate the rest of the body. -/
abbrev repl : Cont (Proc M) Unit := fun k => Proc.bang (k ())

/-- Stop here. -/
abbrev stop {α : Type} : Cont (Proc M) α := fun _ => Proc.nil

/-- The traces of a body. -/
abbrev run (b : Cont (Proc M) Unit) : Proc M := b fun _ => Proc.nil

end Proc

end ProVerif
