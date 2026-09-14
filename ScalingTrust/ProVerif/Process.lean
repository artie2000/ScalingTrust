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
`out`, `in`, `new` and `event` prepend an action.  A family of processes runs in
parallel in two stages: their traces are interleaved, each action tagged with the
component that performed it, and then an output immediately followed by a matching
input of a *different* component may meet in a communication, which leaves nothing
in the trace.  `P | Q` and `!P` are the merges of two processes and of countably
many copies of a process, respectively.
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

variable {M ι : Type}

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
  deriving DecidableEq

/-- An offer to communicate is unfinished until a partner takes it up. -/
inductive Act.Unfinished : Act M → Prop
  | out (c m : M) : (Act.out c m).Unfinished
  | inp (c m : M) : (Act.inp c m).Unfinished

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
abbrev Proc (M : Type) := Set (List (Act M))

/-! ## Communication -/

/-- `(i, a)` can communicate with the head of `s`: `a` is an output and the head a
matching input of another component. -/
def Meets (i : ι) (a : Act M) : List (ι × Act M) → Prop
  | (j, .inp c m) :: _ => i ≠ j ∧ a = .out c m
  | _ => False

/-- The traces obtained from a tagged interleaving by letting adjacent outputs and
inputs of different components meet. -/
def comms : List (ι × Act M) → Set (List (Act M))
  | [] => {[]}
  | (i, a) :: s => (a :: ·) '' comms s ∪ {t ∈ comms s.tail | Meets i a s}
termination_by s => s.length

@[simp] theorem comms_nil : comms ([] : List (ι × Act M)) = {[]} := by rw [comms]

@[simp] theorem comms_cons (i : ι) (a : Act M) (s : List (ι × Act M)) :
    comms ((i, a) :: s) = (a :: ·) '' comms s ∪ {t ∈ comms s.tail | Meets i a s} := by
  rw [comms]

theorem mem_comms_cons {s : List (ι × Act M)} {t : List (Act M)} (h : t ∈ comms s) (i : ι)
    (a : Act M) : a :: t ∈ comms ((i, a) :: s) := by
  rw [comms_cons]
  exact Or.inl ⟨t, h, rfl⟩

theorem mem_comms_pair {s : List (ι × Act M)} {t : List (Act M)} {i j : ι} (hij : i ≠ j) (c m : M)
    (h : t ∈ comms s) : t ∈ comms ((i, .out c m) :: (j, .inp c m) :: s) := by
  rw [comms_cons]
  exact Or.inr ⟨h, by simp [Meets, hij]⟩

/-- Communications happen within a tagged trace, so tagged traces concatenate. -/
theorem comms_append {r q : List (ι × Act M)} {u v : List (Act M)} (hu : u ∈ comms r)
    (hv : v ∈ comms q) : u ++ v ∈ comms (r ++ q) := by
  induction r using comms.induct generalizing u with
  | case1 =>
    simp only [comms_nil, Set.mem_singleton_iff] at hu
    subst hu
    simpa
  | case2 i a r ih₁ ih₂ =>
    rw [comms_cons] at hu
    rcases hu with ⟨u₀, hu₀, rfl⟩ | ⟨hu, hm⟩
    · exact mem_comms_cons (ih₁ hu₀) i a
    · rcases r with _ | ⟨⟨j, b⟩, r⟩
      · simp [Meets] at hm
      · rcases b with ⟨c, m⟩ | ⟨c, m⟩ | n | e | m <;> simp [Meets] at hm
        obtain ⟨hij, rfl⟩ := hm
        exact mem_comms_pair hij c m (ih₂ hu)

/-- Retagging with an injection preserves communication. -/
theorem comms_retag {κ : Type} {φ : ι → κ} (hφ : Function.Injective φ)
    {s : List (ι × Act M)} {t : List (Act M)} (h : t ∈ comms s) :
    t ∈ comms (s.map (Prod.map φ id)) := by
  induction s using comms.induct generalizing t with
  | case1 => simpa using h
  | case2 i a s ih₁ ih₂ =>
    rw [comms_cons] at h
    rcases h with ⟨t₀, h₀, rfl⟩ | ⟨h₀, hm⟩
    · exact mem_comms_cons (ih₁ h₀) (φ i) a
    · rcases s with _ | ⟨⟨j, b⟩, r⟩
      · simp [Meets] at hm
      · rcases b with ⟨c, m⟩ | ⟨c, m⟩ | n | e | m <;> simp [Meets] at hm
        obtain ⟨hij, rfl⟩ := hm
        exact mem_comms_pair (hφ.ne hij) c m (ih₂ h₀)

/-- A trace `a :: t` arises from some communications, then `a`, then `t`. -/
theorem peel {s : List (ι × Act M)} {a : Act M} {t : List (Act M)} (h : a :: t ∈ comms s) :
    ∃ p i s', [] ∈ comms p ∧ s = p ++ (i, a) :: s' ∧ t ∈ comms s' := by
  induction s using comms.induct generalizing t with
  | case1 => simp at h
  | case2 i b s ih₁ ih₂ =>
    rw [comms_cons] at h
    rcases h with ⟨t₀, h₀, ht⟩ | ⟨h₀, hm⟩
    · obtain ⟨rfl, rfl⟩ := List.cons.inj ht
      exact ⟨[], i, s, by simp, rfl, h₀⟩
    · rcases s with _ | ⟨⟨j, b'⟩, r⟩
      · simp [Meets] at hm
      · rcases b' with ⟨c, m⟩ | ⟨c, m⟩ | n | e | m <;> simp [Meets] at hm
        obtain ⟨hij, rfl⟩ := hm
        obtain ⟨p, i', s', hp, hr, ht'⟩ := ih₂ h₀
        simp only [List.tail_cons] at hr
        subst hr
        exact ⟨(i, .out c m) :: (j, .inp c m) :: p, i', s', mem_comms_pair hij c m hp, rfl, ht'⟩

/-- Communication removes only offers, so the names created are those of the interleaving. -/
theorem nonces_of_mem_comms {s : List (ι × Act M)} {t : List (Act M)} (h : t ∈ comms s) :
    nonces t = nonces (s.map Prod.snd) := by
  induction s using comms.induct generalizing t with
  | case1 =>
    simp only [comms_nil, Set.mem_singleton_iff] at h
    subst h
    rfl
  | case2 i a s ih₁ ih₂ =>
    rw [comms_cons] at h
    rcases h with ⟨t₀, h₀, rfl⟩ | ⟨h₀, hm⟩
    · cases a <;> simp [nonces, ih₁ h₀]
    · rcases s with _ | ⟨⟨j, b⟩, r⟩
      · simp [Meets] at hm
      · rcases b with ⟨c, m⟩ | ⟨c, m⟩ | n | e | m <;> simp [Meets] at hm
        obtain ⟨-, rfl⟩ := hm
        simpa [nonces] using ih₂ h₀

/-- Every action of the trace was performed by some component. -/
theorem mem_of_mem_comms {s : List (ι × Act M)} {t : List (Act M)} (h : t ∈ comms s) {a : Act M}
    (ha : a ∈ t) : ∃ i, (i, a) ∈ s := by
  induction s using comms.induct generalizing t with
  | case1 =>
    simp only [comms_nil, Set.mem_singleton_iff] at h
    subst h
    simp at ha
  | case2 i b s ih₁ ih₂ =>
    rw [comms_cons] at h
    rcases h with ⟨t₀, h₀, rfl⟩ | ⟨h₀, -⟩
    · rcases List.mem_cons.1 ha with rfl | ha
      · exact ⟨i, List.mem_cons_self⟩
      · obtain ⟨k, hk⟩ := ih₁ h₀ ha
        exact ⟨k, List.mem_cons_of_mem _ hk⟩
    · obtain ⟨k, hk⟩ := ih₂ h₀ ha
      exact ⟨k, List.mem_cons_of_mem _ (List.mem_of_mem_tail hk)⟩

/-- If no action of the trace is unfinished, every message received by one component
was sent by another. -/
theorem out_of_inp_comms {s : List (ι × Act M)} {t : List (Act M)} (h : t ∈ comms s)
    (hw : ∀ a ∈ t, ¬ a.Unfinished) {k : ι} {c m : M} (hk : (k, Act.inp c m) ∈ s) :
    ∃ i, i ≠ k ∧ (i, Act.out c m) ∈ s := by
  induction s using comms.induct generalizing t with
  | case1 => simp at hk
  | case2 i a s ih₁ ih₂ =>
    rw [comms_cons] at h
    rcases h with ⟨t₀, h₀, rfl⟩ | ⟨h₀, hm⟩
    · rcases List.mem_cons.1 hk with hk | hk
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk
        exact (hw _ List.mem_cons_self (.inp _ _)).elim
      · obtain ⟨i', hi', h'⟩ :=
          ih₁ h₀ (fun b hb => hw b (List.mem_cons_of_mem _ hb)) hk
        exact ⟨i', hi', List.mem_cons_of_mem _ h'⟩
    · rcases s with _ | ⟨⟨j, b⟩, r⟩
      · simp [Meets] at hm
      · rcases b with ⟨c', m'⟩ | ⟨c', m'⟩ | n | e | m' <;> simp [Meets] at hm
        obtain ⟨hij, rfl⟩ := hm
        rcases List.mem_cons.1 hk with hk | hk
        · cases hk
        · rcases List.mem_cons.1 hk with hk | hk
          · obtain ⟨rfl, h⟩ := Prod.mk.inj hk
            obtain ⟨rfl, rfl⟩ := Act.inp.inj h
            exact ⟨i, hij, List.mem_cons_self⟩
          · obtain ⟨i', hi', h'⟩ := ih₂ h₀ hw hk
            exact ⟨i', hi', List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h')⟩

/-! ## Interleaving -/

variable [DecidableEq ι]

/-- `s` interleaves the traces `f i`, each action tagged with its component:
every component reads its own trace back off `s`. -/
def Interleaves (f : ι → List (Act M)) (s : List (ι × Act M)) : Prop :=
  ∀ i, (s.filter (·.1 = i)).map Prod.snd = f i

theorem Interleaves.mem_iff {f : ι → List (Act M)} {s : List (ι × Act M)} (h : Interleaves f s)
    {i : ι} {a : Act M} : (i, a) ∈ s ↔ a ∈ f i := by
  rw [← h i]
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · intro hs
    exact ⟨(i, a), ⟨hs, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨hs, rfl⟩, rfl⟩
    exact hs

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
def merge (P : ι → Proc M) : Proc M :=
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

example (c m : M) :
    par (out c m .nil) (inp c fun _ => nil) =
    {[], [.out c m]} ∪ {[.inp c x] | x} ∪ {[.inp c x, .out c m] | x} ∪ {[.out c m, .inp c x] | x} := by
  have : Nonempty M := ⟨c⟩
  ext
  simp [Proc.inp, Proc.out, Proc.act, Proc.nil]
  sorry

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

theorem filter_dec (s : List (ℕ × Act M)) (n : ℕ) :
    ((dec s).filter (·.1 = n)).map Prod.snd = (s.filter (·.1 = n + 1)).map Prod.snd := by
  induction s with
  | nil => rfl
  | cons x s ih =>
    obtain ⟨i, a⟩ := x
    cases i with
    | zero => simpa [List.filter_cons] using ih
    | succ k => by_cases hk : k = n <;> simpa [List.filter_cons, hk] using ih

/-- Shift all tags up. -/
def inc : List (ℕ × Act M) → List (ℕ × Act M) := List.map (Prod.map Nat.succ id)

@[simp] theorem inc_nil : inc ([] : List (ℕ × Act M)) = [] := rfl

@[simp] theorem inc_cons (i : ℕ) (a : Act M) (s : List (ℕ × Act M)) :
    inc ((i, a) :: s) = (i + 1, a) :: inc s := rfl

theorem filter_inc_zero (s : List (ℕ × Act M)) : ((inc s).filter (·.1 = 0)).map Prod.snd = [] := by
  induction s with
  | nil => rfl
  | cons x s ih =>
    obtain ⟨i, a⟩ := x
    simpa [List.filter_cons] using ih

theorem filter_inc_succ (s : List (ℕ × Act M)) (n : ℕ) :
    ((inc s).filter (·.1 = n + 1)).map Prod.snd = (s.filter (·.1 = n)).map Prod.snd := by
  induction s with
  | nil => rfl
  | cons x s ih =>
    obtain ⟨i, a⟩ := x
    by_cases hk : i = n <;> simpa [List.filter_cons, hk] using ih

/-- Splitting off component `0`: the other components produce `t'` among themselves,
and `t` is a two-component merge of component `0` with `t'`. -/
theorem split {s : List (ℕ × Act M)} {t : List (Act M)} (h : t ∈ comms s) :
    ∃ (t' : List (Act M)) (s₂ : List (Fin 2 × Act M)), t' ∈ comms (dec s) ∧ t ∈ comms s₂ ∧
      (s₂.filter (·.1 = 0)).map Prod.snd = (s.filter (·.1 = 0)).map Prod.snd ∧
      (s₂.filter (·.1 = 1)).map Prod.snd = t' := by
  induction s using comms.induct generalizing t with
  | case1 =>
    simp only [comms_nil, Set.mem_singleton_iff] at h
    subst h
    exact ⟨[], [], by simp, by simp, rfl, rfl⟩
  | case2 i a s ih₁ ih₂ =>
    rw [comms_cons] at h
    rcases h with ⟨t₀, h₀, rfl⟩ | ⟨h₀, hm⟩
    · obtain ⟨t', s₂, h1, h2, h3, h4⟩ := ih₁ h₀
      cases i with
      | zero =>
        exact ⟨t', (0, a) :: s₂, by simpa using h1, mem_comms_cons h2 0 a,
          by simpa [List.filter_cons] using h3, by simpa [List.filter_cons] using h4⟩
      | succ n =>
        exact ⟨a :: t', (1, a) :: s₂, by simpa using mem_comms_cons h1 n a,
          mem_comms_cons h2 1 a, by simpa [List.filter_cons] using h3,
          by simpa [List.filter_cons] using h4⟩
    · rcases s with _ | ⟨⟨j, b⟩, r⟩
      · simp [Meets] at hm
      · rcases b with ⟨c, m⟩ | ⟨c, m⟩ | n | e | m <;> simp [Meets] at hm
        obtain ⟨hij, rfl⟩ := hm
        obtain ⟨t', s₂, h1, h2, h3, h4⟩ := ih₂ h₀
        cases i with
        | zero =>
          cases j with
          | zero => exact absurd rfl hij
          | succ n =>
            exact ⟨.inp c m :: t', (0, .out c m) :: (1, .inp c m) :: s₂,
              by simpa using mem_comms_cons h1 n (.inp c m),
              mem_comms_pair (by decide) c m h2, by simpa [List.filter_cons] using h3,
              by simpa [List.filter_cons] using h4⟩
        | succ n =>
          cases j with
          | zero =>
            exact ⟨.out c m :: t', (1, .out c m) :: (0, .inp c m) :: s₂,
              by simpa using mem_comms_cons h1 n (.out c m),
              mem_comms_pair (by decide) c m h2, by simpa [List.filter_cons] using h3,
              by simpa [List.filter_cons] using h4⟩
          | succ n' =>
            exact ⟨t', s₂, by simpa using mem_comms_pair (by omega : n ≠ n') c m h1, h2,
              by simpa [List.filter_cons] using h3, by simpa [List.filter_cons] using h4⟩

/-- Merging the components of `s'` into component `1` of the two-component trace `s₂`. -/
theorem join {s₂ : List (Fin 2 × Act M)} {t : List (Act M)} (h : t ∈ comms s₂)
    {s' : List (ℕ × Act M)} (h' : (s₂.filter (·.1 = 1)).map Prod.snd ∈ comms s') :
    ∃ s : List (ℕ × Act M), t ∈ comms s ∧
      (s.filter (·.1 = 0)).map Prod.snd = (s₂.filter (·.1 = 0)).map Prod.snd ∧
      ∀ n, (s.filter (·.1 = n + 1)).map Prod.snd = (s'.filter (·.1 = n)).map Prod.snd := by
  have two : ∀ j : Fin 2, j = 0 ∨ j = 1 := Fin.forall_fin_two.2 ⟨.inl rfl, .inr rfl⟩
  induction s₂ using comms.induct generalizing t s' with
  | case1 =>
    simp only [comms_nil, Set.mem_singleton_iff] at h
    subst h
    simp only [List.filter_nil, List.map_nil] at h'
    exact ⟨inc s', comms_retag Nat.succ_injective h', by simp [filter_inc_zero],
      filter_inc_succ s'⟩
  | case2 i a s₂ ih₁ ih₂ =>
    rw [comms_cons] at h
    rcases h with ⟨t₀, h₀, rfl⟩ | ⟨h₀, hm⟩
    · rcases two i with rfl | rfl
      · have h' : (s₂.filter (·.1 = 1)).map Prod.snd ∈ comms s' := by
          simpa [List.filter_cons] using h'
        obtain ⟨s, hs1, hs2, hs3⟩ := ih₁ h₀ h'
        exact ⟨(0, a) :: s, mem_comms_cons hs1 0 a, by simpa [List.filter_cons] using hs2,
          fun n => by simpa [List.filter_cons] using hs3 n⟩
      · have h' : a :: (s₂.filter (·.1 = 1)).map Prod.snd ∈ comms s' := by
          simpa [List.filter_cons] using h'
        obtain ⟨p, k, s'', hp, rfl, ht''⟩ := peel h'
        obtain ⟨s, hs1, hs2, hs3⟩ := ih₁ h₀ ht''
        refine ⟨inc p ++ (k + 1, a) :: s,
          comms_append (comms_retag Nat.succ_injective hp) (mem_comms_cons hs1 (k + 1) a),
          by simpa [List.filter_append, List.filter_cons, filter_inc_zero] using hs2, fun n => ?_⟩
        by_cases hk : k = n <;>
          simpa [List.filter_append, List.filter_cons, filter_inc_succ, hk] using hs3 n
    · rcases s₂ with _ | ⟨⟨j, b⟩, r₂⟩
      · simp [Meets] at hm
      · rcases b with ⟨c, m⟩ | ⟨c, m⟩ | n | e | m <;> simp [Meets] at hm
        obtain ⟨hij, rfl⟩ := hm
        rcases two i with rfl | rfl <;> rcases two j with rfl | rfl
        · exact absurd rfl hij
        · have h' : .inp c m :: (r₂.filter (·.1 = 1)).map Prod.snd ∈ comms s' := by
            simpa [List.filter_cons] using h'
          obtain ⟨p, k, s'', hp, rfl, ht''⟩ := peel h'
          obtain ⟨s, hs1, hs2, hs3⟩ := ih₂ h₀ ht''
          refine ⟨inc p ++ (0, .out c m) :: (k + 1, .inp c m) :: s,
            comms_append (comms_retag Nat.succ_injective hp)
              (mem_comms_pair (by omega) c m hs1),
            by simpa [List.filter_append, List.filter_cons, filter_inc_zero] using hs2,
            fun n => ?_⟩
          by_cases hk : k = n <;>
            simpa [List.filter_append, List.filter_cons, filter_inc_succ, hk] using hs3 n
        · have h' : .out c m :: (r₂.filter (·.1 = 1)).map Prod.snd ∈ comms s' := by
            simpa [List.filter_cons] using h'
          obtain ⟨p, k, s'', hp, rfl, ht''⟩ := peel h'
          obtain ⟨s, hs1, hs2, hs3⟩ := ih₂ h₀ ht''
          refine ⟨inc p ++ (k + 1, .out c m) :: (0, .inp c m) :: s,
            comms_append (comms_retag Nat.succ_injective hp)
              (mem_comms_pair (by omega) c m hs1),
            by simpa [List.filter_append, List.filter_cons, filter_inc_zero] using hs2,
            fun n => ?_⟩
          by_cases hk : k = n <;>
            simpa [List.filter_append, List.filter_cons, filter_inc_succ, hk] using hs3 n
        · exact absurd rfl hij

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
      fun n => (filter_dec s n).trans (hi (n + 1)), h1⟩, hn'⟩⟩,
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
