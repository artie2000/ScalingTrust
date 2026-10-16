/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib.Control.Monad.Cont
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Stream.Defs
import Mathlib.Logic.Embedding.Basic
import Mathlib.SetTheory.Descriptive.Tree
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
`Proc.emit` for its actions, `Proc.fork` and `Proc.repl` for `|` and `!`, Lean's
`match` and `if` for `let` and `if`, and an `Option` bound with `←` for a `let` without
`else`, which stops the process when it fails.

Every constructor preserves prefix-closure (`Descriptive.tree`), so a trace is a run
so far and a process that blocks has no longer traces.  `out` and `in` are *unfinished*
actions; a trace with none represents a run in which every communication was
completed.

Names are created by index.  `new` never creates a name that the rest of the
process creates again, and a merge keeps the names created by different
components apart, so the names created in a trace are pairwise distinct.
-/

namespace ProVerif.TraceSemantics

open Descriptive

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
abbrev Trace.Closed (t : Trace M) : Prop := ∀ a ∈ t, ¬ a.Unfinished

/-- The nonce indices created in a trace. -/
def Trace.nonces : Trace M → List ℕ
  | [] => []
  | .new n :: t => n :: nonces t
  | _ :: t => nonces t

theorem Trace.nonces_sublist {l₁ l₂ : Trace M} (h : l₁.Sublist l₂) :
    l₁.nonces.Sublist l₂.nonces := by
  induction h with
  | slnil => exact .slnil
  | cons a _ ih => exact ih.trans (by cases a <;> simp [nonces])
  | cons_cons a _ ih => cases a <;> simp [nonces, ih]

/-- A process is a set of traces. -/
abbrev Proc (M : Type) := Set (Trace M)

/-! ## Communication -/

/-- A trace with each action tagged by the component that performed it. -/
abbrev TaggedTrace (ι M : Type) := List (ι × Act M)

namespace TaggedTrace

section interleave

variable [DecidableEq ι]

/-- The trace of component `i` in `s`. -/
def proj (s : TaggedTrace ι M) (i : ι) : Trace M := (s.filter (·.1 = i)).map Prod.snd

@[simp] theorem proj_nil (i : ι) : proj ([] : TaggedTrace ι M) i = [] := rfl

@[simp] theorem proj_cons (i j : ι) (a : Act M) (s : TaggedTrace ι M) :
    proj ((j, a) :: s) i = if j = i then a :: s.proj i else s.proj i := by
  by_cases h : j = i <;> simp [proj, h]

theorem proj_prefix {s' s : TaggedTrace ι M} (h : s' <+: s) (i : ι) : s'.proj i <+: s.proj i :=
  (h.filter _).map _

theorem proj_sublist (s : TaggedTrace ι M) (i : ι) : (s.proj i).Sublist (s.map Prod.snd) :=
  List.filter_sublist.map _

/-- When the names created in a tagged trace are distinct, different components create
different names. -/
theorem proj_nonces_disjoint {s : TaggedTrace ι M} (h : (Trace.nonces (s.map Prod.snd)).Nodup)
    {i j : ι} (hij : i ≠ j) : (s.proj i).nonces.Disjoint (s.proj j).nonces := by
  induction s with
  | nil => exact List.disjoint_nil_left _
  | cons x s ih =>
    obtain ⟨k, a⟩ := x
    have hsub (l : ι) : Trace.nonces (proj s l) ⊆ Trace.nonces (s.map Prod.snd) :=
      (Trace.nonces_sublist (proj_sublist s l)).subset
    cases a
    case new n =>
      simp only [List.map_cons, Trace.nonces, List.nodup_cons] at h
      rcases eq_or_ne k i with rfl | hki
      · simp only [proj_cons, if_true, hij, if_false, Trace.nonces]
        exact List.disjoint_cons_left.2 ⟨fun h' => h.1 (hsub j h'), ih h.2⟩
      rcases eq_or_ne k j with rfl | hkj
      · simp only [proj_cons, if_true, hki, if_false, Trace.nonces]
        exact List.disjoint_cons_right.2 ⟨fun h' => h.1 (hsub i h'), ih h.2⟩
      · simpa only [proj_cons, hki, hkj, if_false] using ih h.2
    all_goals
      by_cases hki : k = i <;> by_cases hkj : k = j <;>
        simpa [proj_cons, hki, hkj, hij, hij.symm, Trace.nonces] using ih (by simpa [Trace.nonces] using h)

/-- `s` interleaves the traces `f i`, each action tagged with its component:
every component reads its own trace back off `s`. -/
def Interleaves (s : TaggedTrace ι M) (f : ι → Trace M) : Prop := ∀ i, s.proj i = f i

end interleave

/-- `t` is obtained from `s` by letting an output immediately followed by a matching
input of a different component meet in a communication, recorded as `comm`. -/
inductive Comms : TaggedTrace ι M → Trace M → Prop
  | nil : Comms [] []
  | cons {s t} (i : ι) (a : Act M) : Comms s t → Comms ((i, a) :: s) (a :: t)
  | pair {s t} {i j : ι} (hij : i ≠ j) (c m : M) : Comms s t →
      Comms ((i, .out c m) :: (j, .inp c m) :: s) (.comm c m :: t)

/-- Retagging with an injection preserves communication. -/
theorem Comms.map {κ : Type} {φ : ι → κ} (hφ : Function.Injective φ) {s : TaggedTrace ι M}
    {t : Trace M} (h : s.Comms t) : Comms (s.map (Prod.map φ id)) t := by
  induction h with
  | nil => exact .nil
  | cons i a _ ih => exact ih.cons (φ i) a
  | pair hij c m _ ih => exact ih.pair (hφ.ne hij) c m

/-- Communication removes only offers, so the names created are those of the interleaving. -/
theorem Comms.nonces {s : TaggedTrace ι M} {t : Trace M} (h : s.Comms t) :
    t.nonces = Trace.nonces (s.map Prod.snd) := by
  induction h with
  | nil => rfl
  | cons i a _ ih => cases a <;> simp [Trace.nonces, ih]
  | pair _ c m _ ih => simpa [Trace.nonces] using ih

/-- A prefix of `t` is obtained from a prefix of `s`. -/
theorem Comms.prefix {s : TaggedTrace ι M} {t l : Trace M} (h : s.Comms t) (hl : l <+: t) :
    ∃ s' : TaggedTrace ι M, s' <+: s ∧ s'.Comms l := by
  induction h generalizing l with
  | nil =>
    obtain rfl := List.prefix_nil.1 hl
    exact ⟨[], List.nil_prefix, .nil⟩
  | cons i a _ ih =>
    rcases l with _ | ⟨b, l⟩
    · exact ⟨[], List.nil_prefix, .nil⟩
    · rw [List.cons_prefix_cons] at hl
      obtain ⟨rfl, hl⟩ := hl
      obtain ⟨s', hs', h'⟩ := ih hl
      exact ⟨(i, b) :: s', List.cons_prefix_cons.2 ⟨rfl, hs'⟩, h'.cons i b⟩
  | @pair _ _ i j hij c m _ ih =>
    rcases l with _ | ⟨b, l⟩
    · exact ⟨[], List.nil_prefix, .nil⟩
    · rw [List.cons_prefix_cons] at hl
      obtain ⟨rfl, hl⟩ := hl
      obtain ⟨s', hs', h'⟩ := ih hl
      exact ⟨(i, .out c m) :: (j, .inp c m) :: s',
        List.cons_prefix_cons.2 ⟨rfl, List.cons_prefix_cons.2 ⟨rfl, hs'⟩⟩, h'.pair hij c m⟩

end TaggedTrace

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
  ⋃ n, act (.new n) {t ∈ P (Names.nonce n) | n ∉ t.nonces}

/-- `event e; P` -/
abbrev event (e : M) (P : Proc M) : Proc M := act (.event e) P

/-- The processes `P i` in parallel, creating distinct names. -/
def merge [DecidableEq ι] (P : ι → Proc M) : Proc M :=
  {t | (∃ (f : ι → Trace M) (s : TaggedTrace ι M), (∀ i, f i ∈ P i) ∧ s.Interleaves f ∧
    s.Comms t) ∧ t.nonces.Nodup}

/-- `P | Q` -/
abbrev par (P Q : Proc M) : Proc M := merge ![P, Q]

/-- `!P`: an unbounded number of copies of `P` in parallel. -/
abbrev bang (P : Proc M) : Proc M := merge fun _ : ℕ => P

/-! ### Prefix-closure

Every constructor preserves it, as `aesop` rules, so `aesop` proves it of a translated
process, splitting the `match` of a `let`. -/

@[aesop unsafe] theorem nil_mem_tree : (nil : Proc M) ∈ tree (Act M) :=
  fun _ _ h => by simp at h

@[aesop unsafe] theorem act_mem_tree (a : Act M) {P : Proc M}
    (h : P ∈ tree (Act M)) : act a P ∈ tree (Act M) := by
  intro x b hx
  simp only [act, Set.mem_insert_iff, Set.mem_image] at hx ⊢
  rcases hx with hx | ⟨t, ht, hx⟩
  · simp at hx
  · rcases x with _ | ⟨_, x⟩
    · exact Or.inl rfl
    · obtain ⟨rfl, rfl⟩ := List.cons.inj hx
      exact Or.inr ⟨x, Tree.mem_of_append (T := ⟨P, h⟩) ht, rfl⟩

@[aesop unsafe] theorem inp_mem_tree (c : M) {P : M → Proc M}
    (h : ∀ m, P m ∈ tree (Act M)) : inp c P ∈ tree (Act M) := by
  refine CompleteSublattice.sSupClosed (L := tree (Act M)) ?_
  rintro _ ⟨m, rfl⟩
  exact act_mem_tree _ (h m)

@[aesop unsafe] theorem new_mem_tree [Names M] {P : M → Proc M}
    (h : ∀ n, P (Names.nonce n) ∈ tree (Act M)) :
    new P ∈ tree (Act M) := by
  refine CompleteSublattice.sSupClosed (L := tree (Act M)) ?_
  rintro _ ⟨n, rfl⟩
  refine act_mem_tree _ (Sublattice.inf_mem (L := (tree (Act M)).toSublattice)
    (a := P (Names.nonce n)) (b := {t : Trace M | n ∉ t.nonces}) (h n) ?_)
  exact fun _ _ hn h' => hn ((Trace.nonces_sublist (List.sublist_append_left _ _)).subset h')

@[aesop unsafe] theorem merge_mem_tree [DecidableEq ι] {P : ι → Proc M}
    (hP : ∀ i, P i ∈ tree (Act M)) : merge P ∈ tree (Act M) := by
  rintro x a ⟨⟨f, s, hf, hs, hst⟩, hn⟩
  obtain ⟨s', hs', h'⟩ := hst.prefix (List.prefix_append x [a])
  refine ⟨⟨TaggedTrace.proj s', s', fun i => Tree.mem_of_prefix (T := ⟨P i, hP i⟩)
    (hs i ▸ TaggedTrace.proj_prefix hs' i) (hf i), fun _ => rfl, h'⟩, ?_⟩
  rw [h'.nonces]
  rw [hst.nonces] at hn
  exact hn.sublist (Trace.nonces_sublist (hs'.map Prod.snd).sublist)

@[aesop unsafe] theorem par_mem_tree {P Q : Proc M} (hP : P ∈ tree (Act M))
    (hQ : Q ∈ tree (Act M)) : par P Q ∈ tree (Act M) :=
  merge_mem_tree (Fin.forall_fin_two.2 ⟨hP, hQ⟩)

end Proc

/-! ### Countably many copies

`!P = P | !P` relates a tagged trace over `ℕ` to one over `Fin 2`: component `0` on
one side, and on the other the trace that the remaining components produce among
themselves, in which their offers to component `0` are still unfinished.
-/

namespace TaggedTrace

/-- Drop the entries of component `0` and shift the other tags down. -/
def dec : TaggedTrace ℕ M → TaggedTrace ℕ M :=
  List.filterMap fun | (0, _) => none | (n + 1, a) => some (n, a)

@[simp] theorem dec_cons_zero (a : Act M) (s : TaggedTrace ℕ M) : dec ((0, a) :: s) = s.dec := rfl

@[simp] theorem dec_cons_succ (n : ℕ) (a : Act M) (s : TaggedTrace ℕ M) :
    dec ((n + 1, a) :: s) = (n, a) :: s.dec := rfl

theorem dec_sublist (s : TaggedTrace ℕ M) : (s.dec.map Prod.snd).Sublist (s.map Prod.snd) := by
  induction s with
  | nil => exact .slnil
  | cons x s ih =>
    obtain ⟨_ | n, a⟩ := x
    · exact ih.trans (List.sublist_cons_self _ _)
    · exact ih.cons_cons a

theorem proj_dec (s : TaggedTrace ℕ M) (n : ℕ) : s.dec.proj n = s.proj (n + 1) := by
  induction s with
  | nil => rfl
  | cons x s ih =>
    obtain ⟨_ | k, a⟩ := x
    · simpa using ih
    · by_cases hk : k = n <;> simp [hk, ih]

/-- Shift all tags up. -/
def inc : TaggedTrace ℕ M → TaggedTrace ℕ M := List.map (Prod.map Nat.succ id)

@[simp] theorem inc_cons (i : ℕ) (a : Act M) (s : TaggedTrace ℕ M) :
    inc ((i, a) :: s) = (i + 1, a) :: s.inc := rfl

theorem proj_inc_zero (s : TaggedTrace ℕ M) : s.inc.proj 0 = [] := by
  induction s with
  | nil => rfl
  | cons x s ih =>
    obtain ⟨i, a⟩ := x
    simpa using ih

theorem proj_inc_succ (s : TaggedTrace ℕ M) (n : ℕ) : s.inc.proj (n + 1) = s.proj n := by
  induction s with
  | nil => rfl
  | cons x s ih =>
    obtain ⟨i, a⟩ := x
    by_cases hk : i = n <;> simp [hk, ih]

/-- Component `0` of `s` against the trace that the other components of `s` produce
among themselves. -/
theorem Comms.split {s : TaggedTrace ℕ M} {t : Trace M} (h : s.Comms t) :
    ∃ (t' : Trace M) (s₂ : TaggedTrace (Fin 2) M), s.dec.Comms t' ∧ s₂.Comms t ∧
      s₂.proj 0 = s.proj 0 ∧ s₂.proj 1 = t' := by
  induction h with
  | nil => exact ⟨[], [], .nil, .nil, rfl, rfl⟩
  | cons i a _ ih =>
    obtain ⟨t', s₂, h1, h2, h3, h4⟩ := ih
    cases i with
    | zero => exact ⟨t', (0, a) :: s₂, h1, h2.cons 0 a, by simpa using h3, by simpa using h4⟩
    | succ n =>
      exact ⟨a :: t', (1, a) :: s₂, h1.cons n a, h2.cons 1 a, by simpa using h3,
        by simpa using h4⟩
  | @pair _ _ i j hij c m _ ih =>
    obtain ⟨t', s₂, h1, h2, h3, h4⟩ := ih
    rcases i with _ | n <;> rcases j with _ | n'
    · exact absurd rfl hij
    · exact ⟨.inp c m :: t', (0, .out c m) :: (1, .inp c m) :: s₂, h1.cons n' _,
        h2.pair (by decide) c m, by simpa using h3, by simpa using h4⟩
    · exact ⟨.out c m :: t', (1, .out c m) :: (0, .inp c m) :: s₂, h1.cons n _,
        h2.pair (by decide) c m, by simpa using h3, by simpa using h4⟩
    · exact ⟨.comm c m :: t', (1, .comm c m) :: s₂, h1.pair (by omega : n ≠ n') c m,
        h2.cons 1 _, by simpa using h3, by simpa using h4⟩

/-- Merging the components of `s'` into component `1` of the two-component trace `s₂`. -/
theorem Comms.join {s₂ : TaggedTrace (Fin 2) M} {t : Trace M} (h : s₂.Comms t)
    {s' : TaggedTrace ℕ M} (h' : s'.Comms (s₂.proj 1)) :
    ∃ s : TaggedTrace ℕ M, s.Comms t ∧ s.proj 0 = s₂.proj 0 ∧
      ∀ n, s.proj (n + 1) = s'.proj n := by
  induction h generalizing s' with
  | nil => exact ⟨s'.inc, h'.map Nat.succ_injective, by simp [proj_inc_zero], proj_inc_succ s'⟩
  | cons i a _ ih =>
    fin_cases i <;> simp at h'
    · obtain ⟨s, hs1, hs2, hs3⟩ := ih h'
      exact ⟨(0, a) :: s, hs1.cons 0 a, by simpa using hs2, fun n => by simpa using hs3 n⟩
    · cases h' with
      | cons k _ h' =>
        obtain ⟨s, hs1, hs2, hs3⟩ := ih h'
        refine ⟨(k + 1, a) :: s, hs1.cons (k + 1) a, by simpa using hs2, fun n => ?_⟩
        by_cases hk : k = n <;> simpa [hk] using hs3 n
      | @pair _ _ k k' hkk' c m h' =>
        obtain ⟨s, hs1, hs2, hs3⟩ := ih h'
        refine ⟨(k + 1, .out c m) :: (k' + 1, .inp c m) :: s, hs1.pair (by omega) c m,
          by simpa using hs2, fun n => ?_⟩
        by_cases hk : k = n <;> by_cases hk' : k' = n <;> simpa [hk, hk'] using hs3 n
  | @pair _ _ i j hij c m _ ih =>
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simp at h'
      cases h' with
      | cons k _ h' =>
        obtain ⟨s, hs1, hs2, hs3⟩ := ih h'
        refine ⟨(0, .out c m) :: (k + 1, .inp c m) :: s, hs1.pair (by omega) c m,
          by simpa using hs2, fun n => ?_⟩
        by_cases hk : k = n <;> simpa [hk] using hs3 n
    · simp at h'
      cases h' with
      | cons k _ h' =>
        obtain ⟨s, hs1, hs2, hs3⟩ := ih h'
        refine ⟨(k + 1, .out c m) :: (0, .inp c m) :: s, hs1.pair (by omega) c m,
          by simpa using hs2, fun n => ?_⟩
        by_cases hk : k = n <;> simpa [hk] using hs3 n
    · exact absurd rfl hij

end TaggedTrace

namespace Proc

/-- `!P = P | !P` -/
theorem bang_eq (P : Proc M) : P.bang = P.par P.bang := by
  ext t
  constructor
  · rintro ⟨⟨f, s, hf, hi, ht⟩, hn⟩
    obtain ⟨t', s₂, h1, h2, h3, h4⟩ := ht.split
    have hn' : t'.nonces.Nodup := by
      rw [h1.nonces]
      rw [ht.nonces] at hn
      exact hn.sublist (Trace.nonces_sublist s.dec_sublist)
    exact ⟨⟨![f 0, t'], s₂, Fin.forall_fin_two.2 ⟨hf 0, ⟨⟨f ∘ Nat.succ, s.dec, fun n => hf _,
      fun n => (s.proj_dec n).trans (hi (n + 1)), h1⟩, hn'⟩⟩,
      Fin.forall_fin_two.2 ⟨h3.trans (hi 0), h4⟩, h2⟩, hn⟩
  · rintro ⟨⟨g, s₂, hg, hi, ht⟩, hn⟩
    obtain ⟨⟨h, s', hh, hi', ht'⟩, -⟩ := hg 1
    obtain ⟨s, hs1, hs2, hs3⟩ := ht.join (hi 1 ▸ ht')
    exact ⟨⟨Stream'.cons (g 0) h, s, fun n => (match n with | 0 => hg 0 | n + 1 => hh n),
      fun n => (match n with | 0 => hs2.trans (hi 0) | n + 1 => (hs3 n).trans (hi' n)), hs1⟩, hn⟩

/-! ## Process monad constructors -/

/-- `out(c, m)` -/
abbrev send (c m : M) : Cont (Proc M) Unit := .mk fun k => out c m (k ())

/-- `in(c, x)`, returning `x`. -/
abbrev recv (c : M) : Cont (Proc M) M := .mk fun k => inp c k

/-- `new a`, returning `a`. -/
abbrev fresh [Names M] : Cont (Proc M) M := .mk fun k => new k

/-- `event e` -/
abbrev emit (e : M) : Cont (Proc M) Unit := .mk fun k => event e (k ())

/-- Fork: the rest of the body runs twice in parallel, with `true` and `false`. -/
abbrev fork : Cont (Proc M) Bool := .mk fun k => par (k true) (k false)

/-- Replicate the rest of the body. -/
abbrev repl : Cont (Proc M) Unit := .mk fun k => bang (k ())

/-- Stop here. -/
abbrev stop {α : Type} : Cont (Proc M) α := .mk fun _ => nil

/-- `let x = D in P` without `else`: if `D` fails the process stops.  `Option` lifts into
the monad this way, so a destructor's result is bound with `←`. -/
abbrev ofOption {α : Type} (o : Option α) : Cont (Proc M) α :=
  .mk fun k => match o with | some a => k a | none => nil

instance : MonadLift Option (Cont (Proc M)) := ⟨ofOption⟩

@[simp] theorem monadLift_eq_ofOption {α : Type} (o : Option α) :
    (monadLift o : Cont (Proc M) α) = ofOption o := rfl

/-- The traces of a body. -/
abbrev run (b : Cont (Proc M) Unit) : Proc M := b.run fun _ => nil

end Proc

end ProVerif.TraceSemantics
