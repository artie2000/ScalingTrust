/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib.Order.Closure
import ScalingTrust.ProVerif.Process

/-!
# The attacker and the queries

The attacker is a process like any other: `Enemy K₀ u K` says that, knowing
`K₀`, it can behave as `u` and then knows `K`.  It may receive on any channel it
can derive, send anything it can derive on any channel it can derive, and
create names.  What it can derive from a set of messages is a closure operator,
`Attacker.derive`.

A *run* is a trace of the system `P | Enemy` in which every communication was
completed: a trace `t` of the protocol merged with a trace `u` of the attacker,
with no unfinished action and all nonces distinct.  This is ProVerif's `P₀ | Q`
for every adversary `Q` at once.
Queries quantify over runs: secrecy reads what the attacker ends up knowing,
correspondences read the events of the run.  Nothing here distinguishes public
from private channels: a private channel is a term the attacker cannot derive,
on which it therefore makes no offers.
-/

namespace ProVerif

/-- The attacker's deductive power. -/
class Attacker (M : Type) where
  derive : ClosureOperator (Set M)

open Attacker

variable {M : Type} [Attacker M] [Names M]

/-- `Enemy K₀ u K`: the attacker, knowing `K₀`, can execute with trace `u` and then know `K`. -/
inductive Enemy : Set M → List (Act M) → Set M → Prop
  | nil {K₀} : Enemy K₀ [] K₀
  | inp {K₀ u K} (c m : M) : c ∈ derive K₀ → Enemy (insert m K₀) u K →
      Enemy K₀ (.inp c m :: u) K
  | out {K₀ u K} (c m : M) : c ∈ derive K₀ → m ∈ derive K₀ → Enemy K₀ u K →
      Enemy K₀ (.out c m :: u) K
  | new {K₀ u K} (n : ℕ) : Enemy (insert (Names.nonce n) K₀) u K →
      Enemy K₀ (.new n :: u) K

/-- A run of the protocol `P` against the attacker with initial knowledge `K₀`: the
protocol behaves as `t`, the attacker as `u` and ends up knowing `K`, and
together they run `w`. -/
structure Run (P : Proc M) (K₀ : Set M) (t u w : List (Act M)) (K : Set M) : Prop where
  honest : t ∈ P
  enemy : Enemy K₀ u K
  merges : Merges ![t, u] w
  complete : ∀ a ∈ w, ¬ a.Unfinished
  fresh : (nonces w).Nodup

/-- `query attacker(s)` fails: in no run does the attacker come to know `s`. -/
def Secret (P : Proc M) (K₀ : Set M) (s : M) : Prop :=
  ∀ t u w K, Run P K₀ t u w K → s ∉ derive K

/-- `query event(e) ==> event(e')`, non-injective: in every run, an event satisfying
`Pre` is preceded by one related to it by `R`. -/
def Corr (P : Proc M) (K₀ : Set M) (Pre : M → Prop) (R : M → M → Prop) : Prop :=
  ∀ t u w K, Run P K₀ t u w K → ∀ pre e post, w = pre ++ .event e :: post → Pre e →
    ∃ e', Act.event e' ∈ pre ∧ R e e'

/-! ## Bounding the attacker's knowledge -/

/-- What the attacker knows lies in `S` if its initial knowledge, every nonce, and
every message it received do. -/
theorem Enemy.subset {K₀ K S : Set M} {u : List (Act M)} (h : Enemy K₀ u K)
    (hK₀ : K₀ ⊆ S) (hn : ∀ n, Names.nonce n ∈ S) (hu : ∀ c m, Act.inp c m ∈ u → m ∈ S) :
    K ⊆ S := by
  induction h with
  | nil => exact hK₀
  | inp c m _ _ ih =>
    exact ih (Set.insert_subset_iff.2 ⟨hu c m List.mem_cons_self, hK₀⟩)
      fun c' m' h' => hu c' m' (List.mem_cons_of_mem _ h')
  | out _ _ _ _ _ ih => exact ih hK₀ fun c' m' h' => hu c' m' (List.mem_cons_of_mem _ h')
  | new n _ ih =>
    exact ih (Set.insert_subset_iff.2 ⟨hn n, hK₀⟩)
      fun c' m' h' => hu c' m' (List.mem_cons_of_mem _ h')

/-- The closed-set method for secrecy: if `S` is closed under derivation and contains
the attacker's initial knowledge, every nonce, and every message the protocol
offers, the attacker never knows anything outside `S`. -/
theorem Run.derive_subset {P : Proc M} {K₀ K S : Set M} {t u w : List (Act M)}
    (r : Run P K₀ t u w K) (hK₀ : K₀ ⊆ S) (hS : derive.IsClosed S)
    (hn : ∀ n, Names.nonce n ∈ S) (ht : ∀ c m, Act.out c m ∈ t → m ∈ S) : derive K ⊆ S :=
  ClosureOperator.closure_min
    (r.enemy.subset hK₀ hn fun c m h => ht c m (r.merges.out_of_inp r.complete h)) hS

/-! ## Attackers from public operations -/

/-- `S` is closed under each operation in `ops`, an operation being a partial
function of some arity. -/
def ClosedUnder (ops : Set (Σ n, (Fin n → M) → Option M)) (S : Set M) : Prop :=
  ∀ o ∈ ops, ∀ args : Fin o.1 → M, (∀ i, args i ∈ S) → ∀ r ∈ o.2 args, r ∈ S

/-- The attacker that can apply the public operations `ops`: ProVerif's
`attacker` predicate for a term algebra. -/
@[instance_reducible]
def Attacker.ofOps (ops : Set (Σ n, (Fin n → M) → Option M)) : Attacker M where
  derive := ClosureOperator.ofCompletePred (ClosedUnder ops) fun _ h o ho args hargs r hr => by
    simp only [Set.sInf_eq_sInter, Set.mem_sInter] at hargs ⊢
    exact fun S hS => h S hS o ho args (fun i => hargs i S hS) r hr

end ProVerif
