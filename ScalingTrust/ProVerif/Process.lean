/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib.Control.Monad.Cont
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Embedding.Basic

/-!
# Processes

A process is the set of traces it can perform.  `out`, `in`, `new` and `event`
prepend an action; `P | Q` merges traces, a matching output and input of the two
sides cancelling into a communication; `!P` is a least fixed point.  There is no
syntax of processes: what a role computes between actions is Lean code, and a
role is written as a `do` block in the continuation monad `Cont (Proc M)`,
closed with `Body.run`.

Trace sets are prefix-closed by construction, so a trace is a run so far, and a
process that blocks simply has no longer traces.  A run of a *closed* system is
a pair of traces in which every offer is taken up by the other side (`Sync`).
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

/-- A process is a set of traces. -/
abbrev Proc (M : Type) := Set (List (Act M))

variable {M : Type}

/-- `Merges u v t`: `t` interleaves `u` and `v`, except that a matching offer of
each side may meet in a communication — ProVerif's rule (Red I/O) — which leaves
nothing in `t`. -/
inductive Merges : List (Act M) → List (Act M) → List (Act M) → Prop
  | nil : Merges [] [] []
  | left {a u v t} : Merges u v t → Merges (a :: u) v (a :: t)
  | right {a u v t} : Merges u v t → Merges u (a :: v) (a :: t)
  | commL {c m u v t} : Merges u v t → Merges (.out c m :: u) (.inp c m :: v) t
  | commR {c m u v t} : Merges u v t → Merges (.inp c m :: u) (.out c m :: v) t

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

/-- `P | Q` -/
def par (P Q : Proc M) : Proc M := {t | ∃ u ∈ P, ∃ v ∈ Q, Merges u v t}

theorem par_mono {P P' Q Q' : Proc M} (hP : P ⊆ P') (hQ : Q ⊆ Q') : par P Q ⊆ par P' Q' :=
  fun _ ⟨u, hu, v, hv, h⟩ => ⟨u, hP hu, v, hQ hv, h⟩

/-- One more copy of `P` alongside `X`. -/
def bangStep (P : Proc M) : Proc M →o Proc M :=
  ⟨fun X => nil ∪ par P X, fun _ _ h => Set.union_subset_union_right _ (par_mono le_rfl h)⟩

/-- `!P`: the least set of traces closed under running one more copy of `P`. -/
def bang (P : Proc M) : Proc M := OrderHom.lfp (bangStep P)

/-- The fixed-point equation of replication. -/
theorem bang_eq (P : Proc M) : bang P = nil ∪ par P (bang P) :=
  (OrderHom.map_lfp (bangStep P)).symm

end Proc

/-! ## Runs of a closed system -/

/-- `Sync u v`: `u` and `v` run together, every offer of either side being taken
up by the other — a run of `P | Q` as a closed system. -/
inductive Sync : List (Act M) → List (Act M) → Prop
  | nil : Sync [] []
  | new_left {u v n} : Sync u v → Sync (.new n :: u) v
  | event_left {u v e} : Sync u v → Sync (.event e :: u) v
  | new_right {u v n} : Sync u v → Sync u (.new n :: v)
  | event_right {u v e} : Sync u v → Sync u (.event e :: v)
  | commL {u v c m} : Sync u v → Sync (.out c m :: u) (.inp c m :: v)
  | commR {u v c m} : Sync u v → Sync (.inp c m :: u) (.out c m :: v)

/-- Every message received on one side was offered by the other. -/
theorem Sync.out_of_inp {u v : List (Act M)} {c m : M} (h : Sync u v)
    (hm : Act.inp c m ∈ v) : Act.out c m ∈ u := by
  induction h with
  | nil => simp at hm
  | new_left _ ih => exact List.mem_cons_of_mem _ (ih hm)
  | event_left _ ih => exact List.mem_cons_of_mem _ (ih hm)
  | new_right _ ih =>
    rcases List.mem_cons.1 hm with h | hm
    · cases h
    · exact ih hm
  | event_right _ ih =>
    rcases List.mem_cons.1 hm with h | hm
    · cases h
    · exact ih hm
  | commL _ ih =>
    rcases List.mem_cons.1 hm with h | hm
    · obtain ⟨rfl, rfl⟩ := Act.inp.inj h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hm)
  | commR _ ih =>
    rcases List.mem_cons.1 hm with h | hm
    · cases h
    · exact List.mem_cons_of_mem _ (ih hm)

/-- The nonce indices created in `t`. -/
def nonces : List (Act M) → List ℕ :=
  List.filterMap fun | .new n => some n | _ => none

namespace Body

/-- `out(c, m)` -/
def send (c m : M) : Cont (Proc M) Unit := fun k => Proc.out c m (k ())

/-- `in(c, x)`, returning `x`. -/
def recv (c : M) : Cont (Proc M) M := fun k => Proc.inp c k

/-- `new a`, returning `a`. -/
def fresh [Names M] : Cont (Proc M) M := fun k => Proc.new k

/-- `event e` -/
def emit (e : M) : Cont (Proc M) Unit := fun k => Proc.event e (k ())

/-- Fork: the rest of the body runs twice in parallel, with `true` and `false`. -/
def fork : Cont (Proc M) Bool := fun k => Proc.par (k true) (k false)

/-- Replicate the rest of the body. -/
def bang : Cont (Proc M) Unit := fun k => Proc.bang (k ())

/-- Stop here. -/
def stop : Cont (Proc M) α := fun _ => Proc.nil

/-- The traces of a body. -/
def run (b : Cont (Proc M) Unit) : Proc M := b fun _ => Proc.nil

end Body

example (c : M) :
    Proc.inp c (fun x => Proc.out c x Proc.nil) =
    {[]} ∪ {[Act.inp c x] | x} ∪ {[Act.inp c x, Act.out c x] | x} := by
  have : Nonempty M := ⟨c⟩
  ext
  simp [Proc.inp, Proc.out, Proc.act, Proc.nil]
  grind

end ProVerif
