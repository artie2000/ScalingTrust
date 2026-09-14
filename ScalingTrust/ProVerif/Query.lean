/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib.Order.Closure
import ScalingTrust.ProVerif.Process

/-!
# The attacker and the queries

The attacker is a process, `Enemy K₀`: the traces a Dolev-Yao attacker with
initial knowledge `K₀` can perform.  It may receive on any channel it can
derive, send anything it can derive on any channel it can derive, create names,
and `say` anything it can derive.  What it can derive from a set of messages is
a closure operator, `Attacker.derive`.

A *run* of `P` is a trace of `P | Enemy K₀` in which every communication was
completed; `Runs P K₀` is the process of runs.
Queries are properties of runs.  A communication leaves no action, so a run
does not record what the attacker learnt; instead `say s` in a run is the
attacker's knowledge of `s` made visible, and secrecy and correspondences alike
read the actions of the run.

Nothing here distinguishes public from private channels: a private channel is
a term the attacker cannot derive, on which it therefore makes no offers.
-/

namespace ProVerif

/-- The attacker's deductive power. -/
class Attacker (M : Type) where
  derive : ClosureOperator (Set M)

open Attacker

variable {M : Type} [Attacker M] [Names M]

/-- `Enemy K₀`: the attacker, knowing `K₀`, as a process. -/
inductive Enemy : Set M → Proc M
  | nil {K₀} : Enemy K₀ []
  | inp {K₀ e} (c m : M) : c ∈ derive K₀ → Enemy (insert m K₀) e →
      Enemy K₀ (.inp c m :: e)
  | out {K₀ e} (c m : M) : c ∈ derive K₀ → m ∈ derive K₀ → Enemy K₀ e →
      Enemy K₀ (.out c m :: e)
  | new {K₀ e} (n : ℕ) : n ∉ nonces e → Enemy (insert (Names.nonce n) K₀) e →
      Enemy K₀ (.new n :: e)
  | say {K₀ e} (m : M) : m ∈ derive K₀ → Enemy K₀ e →
      Enemy K₀ (.say m :: e)

/-- The runs of `P` against an attacker knowing `K₀`: the traces of `P | Enemy K₀`
in which every communication was completed. -/
def Runs (P : Proc M) (K₀ : Set M) : Proc M :=
  {w ∈ Proc.par P (Enemy K₀) | ∀ a ∈ w, ¬ a.Unfinished}

/-- `query attacker(s)` fails: in no run does the attacker say `s`. -/
def Secret (P : Proc M) (K₀ : Set M) (s : M) : Prop :=
  ∀ w ∈ Runs P K₀, .say s ∉ w

/-- A non-injective correspondence: in every run, each action satisfying `Pre` is
preceded by one related to it by `R`.  For `query event(e) ==> event(e')`, `Pre`
picks out events; for `query attacker(M) ==> event(e')`, it picks out `say M`. -/
def Corr (P : Proc M) (K₀ : Set M) (Pre : Act M → Prop) (R : Act M → Act M → Prop) : Prop :=
  ∀ w ∈ Runs P K₀, ∀ pre a post, w = pre ++ a :: post → Pre a → ∃ b ∈ pre, R a b

/-! ## Bounding the attacker's knowledge -/

/-- Whatever the attacker says lies in `S` if `S` is closed under derivation and
contains its initial knowledge, every nonce, and every message it receives. -/
theorem Enemy.say_mem {K₀ S : Set M} {e : List (Act M)} (h : Enemy K₀ e) (hK₀ : K₀ ⊆ S)
    (hS : derive.IsClosed S) (hn : ∀ n, Names.nonce n ∈ S)
    (he : ∀ c m, Act.inp c m ∈ e → m ∈ S) {m : M} (hm : Act.say m ∈ e) : m ∈ S := by
  induction h with
  | nil => simp at hm
  | inp c m' _ _ ih =>
    rcases List.mem_cons.1 hm with h | hm
    · cases h
    · exact ih (Set.insert_subset_iff.2 ⟨he c m' List.mem_cons_self, hK₀⟩)
        (fun c' m' h' => he c' m' (List.mem_cons_of_mem _ h')) hm
  | out _ _ _ _ _ ih =>
    rcases List.mem_cons.1 hm with h | hm
    · cases h
    · exact ih hK₀ (fun c' m' h' => he c' m' (List.mem_cons_of_mem _ h')) hm
  | new n _ _ ih =>
    rcases List.mem_cons.1 hm with h | hm
    · cases h
    · exact ih (Set.insert_subset_iff.2 ⟨hn n, hK₀⟩)
        (fun c' m' h' => he c' m' (List.mem_cons_of_mem _ h')) hm
  | say m' hd _ ih =>
    rcases List.mem_cons.1 hm with h | hm
    · obtain rfl := Act.say.inj h
      exact ClosureOperator.closure_min hK₀ hS hd
    · exact ih hK₀ (fun c' m' h' => he c' m' (List.mem_cons_of_mem _ h')) hm

/-- The closed-set method for secrecy: if `S` is closed under derivation and contains
the attacker's initial knowledge, every nonce, and every message `P` offers, and `P`
never says anything itself, then nothing outside `S` is ever said. -/
theorem secret_of_closed {P : Proc M} {K₀ S : Set M} (hK₀ : K₀ ⊆ S) (hS : derive.IsClosed S)
    (hn : ∀ n, Names.nonce n ∈ S) (hP : ∀ t ∈ P, ∀ c m, Act.out c m ∈ t → m ∈ S)
    (hsay : ∀ t ∈ P, ∀ m, Act.say m ∉ t) {s : M} (hs : s ∉ S) : Secret P K₀ s := by
  rintro w ⟨⟨⟨f, l, hf, hl, hw⟩, -⟩, hc⟩ hw'
  obtain ⟨i, hi⟩ := mem_of_mem_comms hw hw'
  rw [hl.mem_iff] at hi
  have two : ∀ j : Fin 2, j = 0 ∨ j = 1 := Fin.forall_fin_two.2 ⟨.inl rfl, .inr rfl⟩
  rcases two i with rfl | rfl
  · exact hsay _ (hf 0) s hi
  · refine hs (Enemy.say_mem (hf 1) hK₀ hS hn (fun c m h => ?_) hi)
    obtain ⟨j, hj, hj'⟩ := out_of_inp_comms hw hc (hl.mem_iff.2 h)
    rcases two j with rfl | rfl
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
