/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.Process

/-!
# The attacker and the queries

The attacker is a process, `Enemy K`: the traces a Dolev-Yao attacker with
initial knowledge `K` can perform.  It may receive on any channel it can
derive, send anything it can derive on any channel it can derive, create names,
and `say` anything it can derive.  What it can derive from a set of messages is
a closure operator, `Attacker.derive`.

An *attack* on `P` is a trace of `P | Enemy K` in which every communication was
completed; `Attacks P K` is the process of attacks.
Queries are properties of attacks.  A communication leaves no action, so an
attack does not record what the attacker learnt; instead `say s` in an attack is
the attacker's knowledge of `s` made visible, and secrecy and correspondences
alike read the actions of the attack.

Nothing here distinguishes public from private channels: a private channel is
a term the attacker cannot derive, on which it therefore makes no offers.
-/

namespace ProVerif

/-- The attacker's deductive power. -/
class Attacker (M : Type) where
  derive : ClosureOperator (Set M)

open Attacker

variable {M : Type} [Attacker M] [Names M]

/-- `Enemy K`: the attacker, knowing `K`, as a process. -/
inductive Enemy : Set M → Proc M
  | nil {K} : Enemy K []
  | inp {K e} (c m : M) : c ∈ derive K → e ∈ Enemy (insert m K) →
      Enemy K (.inp c m :: e) -- defeq abuse for `(.inp c m :: e) ∈ Enemy K`, etc.
  | out {K e} (c m : M) : c ∈ derive K → m ∈ derive K → e ∈ Enemy K →
      Enemy K (.out c m :: e)
  | new {K e} (n : ℕ) : n ∉ nonces e → e ∈ Enemy (insert (Names.nonce n) K) →
      Enemy K (.new n :: e)
  | say {K e} (m : M) : m ∈ derive K → e ∈ Enemy K →
      Enemy K (.say m :: e)

/-- The attacks of `P` by an attacker knowing `K`: the closed traces of `P | Enemy K`. -/
def Attacks (P : Proc M) (K : Set M) : Set (Trace M) := {t ∈ Proc.par P (Enemy K) | Closed t}

/-- `query attacker(s)` fails: in no attack does the attacker come to know `s`. -/
def Secret (P : Proc M) (K : Set M) (s : M) : Prop :=
  ∀ t ∈ Attacks P K, .say s ∉ t

/-- A non-injective correspondence: in every attack, each action satisfying `Pre` is
preceded by one related to it by `R`.  For `query event(e) ==> event(e')`, `Pre`
picks out events; for `query attacker(M) ==> event(e')`, it picks out `say M`. -/
def Corr (P : Proc M) (K : Set M) (Pre : Act M → Prop) (R : Act M → Act M → Prop) : Prop :=
  ∀ t ∈ Attacks P K, ∀ pre a post, t = pre ++ a :: post → Pre a → ∃ b ∈ pre, R a b

/-! ## Bounding the attacker's knowledge -/

/-- Whatever the attacker says lies in `S` if `S` is closed under derivation and
contains its initial knowledge, every nonce, and every message it receives. -/
theorem Enemy.say_mem {K S : Set M} {e : Trace M} (h : e ∈ Enemy K) (hK : K ⊆ S)
    (hS : derive.IsClosed S) (hn : ∀ n, Names.nonce n ∈ S)
    (he : ∀ c m, Act.inp c m ∈ e → m ∈ S) {m : M} (hm : Act.say m ∈ e) : m ∈ S := by
  induction h with
  | nil => simp at hm
  | inp c m' _ _ ih =>
    rcases List.mem_cons.1 hm with h | hm
    · cases h
    · exact ih (Set.insert_subset_iff.2 ⟨he c m' List.mem_cons_self, hK⟩)
        (fun c' m' h' => he c' m' (List.mem_cons_of_mem _ h')) hm
  | out _ _ _ _ _ ih =>
    rcases List.mem_cons.1 hm with h | hm
    · cases h
    · exact ih hK (fun c' m' h' => he c' m' (List.mem_cons_of_mem _ h')) hm
  | new n _ _ ih =>
    rcases List.mem_cons.1 hm with h | hm
    · cases h
    · exact ih (Set.insert_subset_iff.2 ⟨hn n, hK⟩)
        (fun c' m' h' => he c' m' (List.mem_cons_of_mem _ h')) hm
  | say m' hd _ ih =>
    rcases List.mem_cons.1 hm with h | hm
    · obtain rfl := Act.say.inj h
      exact ClosureOperator.closure_min hK hS hd
    · exact ih hK (fun c' m' h' => he c' m' (List.mem_cons_of_mem _ h')) hm

/-- The closed-set method for secrecy: if `S` is closed under derivation and contains
the attacker's initial knowledge, every nonce, and every message `P` offers, and `P`
never says anything itself, then nothing outside `S` is ever said. -/
theorem secret_of_closed {P : Proc M} {K S : Set M} (hK : K ⊆ S) (hS : derive.IsClosed S)
    (hn : ∀ n, Names.nonce n ∈ S) (hP : ∀ t ∈ P, ∀ c m, Act.out c m ∈ t → m ∈ S)
    (hsay : ∀ t ∈ P, ∀ m, Act.say m ∉ t) {s : M} (hs : s ∉ S) : Secret P K s := by
  rintro t ⟨⟨⟨f, l, hf, hl, ht⟩, -⟩, hc⟩ hm
  obtain ⟨i, hi⟩ := mem_of_mem_comms ht hm
  rw [hl.mem_iff] at hi
  fin_cases i
  · exact hsay _ (hf 0) s hi
  · refine hs (Enemy.say_mem (hf 1) hK hS hn (fun c m h => ?_) hi)
    obtain ⟨j, hj, hj'⟩ := out_of_inp_comms ht hc (hl.mem_iff.2 h)
    fin_cases j
    · exact hP _ (hf 0) c m (hl.mem_iff.1 hj')
    · exact absurd rfl hj

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
