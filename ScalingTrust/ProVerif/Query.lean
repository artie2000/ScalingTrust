/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib.Order.Closure
import ScalingTrust.ProVerif.Process

/-!
# The attacker and the queries

The attacker is a closure operator on sets of messages: `m ∈ derive K` means the
attacker can compute `m` from `K`.  It is not a process, so it never appears in
a trace; instead a trace is *valid* when the attacker could have taken part in
it — every channel is one it knows, every input is one it can derive, every
nonce is new.  Queries quantify over valid traces.

Restricting inputs to the attacker's knowledge means all communication passes
through the attacker.  Private channels are not modelled.
-/

namespace ProVerif

/-- The attacker's deductive power. -/
class Attacker (M : Type) where
  derive : ClosureOperator (Set M)

open Attacker

variable {M : Type} [Attacker M]

/-- `Valid K U t`: the attacker, knowing `K`, with nonces `U` already used, can
take part in `t`. -/
def Valid : Set M → Set ℕ → List (Act M) → Prop
  | _, _, [] => True
  | K, U, .out c m :: t => c ∈ derive K ∧ Valid (insert m K) U t
  | K, U, .inp c m :: t => c ∈ derive K ∧ m ∈ derive K ∧ Valid K U t
  | K, U, .new n :: t => n ∉ U ∧ Valid K (insert n U) t
  | K, U, .event _ :: t => Valid K U t

/-- The attacker's knowledge after `t`. -/
def knows (K : Set M) : List (Act M) → Set M
  | [] => K
  | .out _ m :: t => knows (insert m K) t
  | _ :: t => knows K t

/-- `query attacker(s)` fails: no valid trace of `P` lets the attacker derive `s`. -/
def Secret (P : Proc M) (K₀ : Set M) (s : M) : Prop :=
  ∀ t ∈ P, Valid K₀ ∅ t → s ∉ derive (knows K₀ t)

/-- `query event(e) ==> event(e')`, non-injective: in every valid trace, an
event satisfying `Pre` is preceded by one related to it by `R`. -/
def Corr (P : Proc M) (K₀ : Set M) (Pre : M → Prop) (R : M → M → Prop) : Prop :=
  ∀ t ∈ P, Valid K₀ ∅ t → ∀ pre e post, t = pre ++ .event e :: post → Pre e →
    ∃ e', Act.event e' ∈ pre ∧ R e e'

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
