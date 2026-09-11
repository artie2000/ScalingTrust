/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.Query

/-!
# Examples

A term algebra with a hash and pairs, a role written with `do`, an attack, and a
secrecy proof.
-/

namespace ProVerif.Toy

/-- A public channel, a private free name, nonces, a hash and pairs. -/
inductive T where
  | c
  | s
  | n (i : ℕ)
  | hash (t : T)
  | pair (a b : T)
  deriving DecidableEq

instance : Names T := ⟨⟨T.n, fun _ _ h => T.n.inj h⟩⟩

def T.fst : T → Option T
  | .pair a _ => some a
  | _ => none

def T.snd : T → Option T
  | .pair _ b => some b
  | _ => none

/-- The public operations: hash and pairing, and the projections. -/
def T.ops : Set (Σ n, (Fin n → T) → Option T) :=
  {⟨1, fun a => some (.hash (a 0))⟩, ⟨2, fun a => some (.pair (a 0) (a 1))⟩,
   ⟨1, fun a => (a 0).fst⟩, ⟨1, fun a => (a 0).snd⟩}

instance : Attacker T := .ofOps T.ops

open Attacker

/-- A replicated role: what happens between actions is plain Lean. -/
example : Proc T := Body.run do
  Body.bang
  let k ← Body.fresh
  Body.send .c (.hash k)
  let x ← Body.recv .c
  match x.fst with
  | some y => if y = .hash k then Body.emit y else pure ()
  | none => Body.stop

/-- Two roles in parallel. -/
example (A B : Cont (Proc T) Unit) : Proc T := Body.run do
  if ← Body.fork then A else B

/-- Outputting `s` in the clear is an attack: the attacker receives it. -/
theorem leak_attack : ¬ Secret (Proc.out .c .s Proc.nil) {T.c} T.s := by
  intro h
  exact h [.out .c .s] [.inp .c .s] [] _
    ⟨.inr ⟨[], rfl, rfl⟩, .inp _ _ (derive.le_closure _ rfl) .nil, .commL .nil,
      by simp [Closed], List.nodup_nil⟩
    (derive.le_closure _ (Set.mem_insert _ _))

/-- Terms in which `s` occurs only under a hash. -/
def Hid : T → Prop
  | .s => False
  | .pair a b => Hid a ∧ Hid b
  | _ => True

theorem hid_closed : ClosedUnder T.ops {t | Hid t} := by
  intro o ho args hargs r hr
  simp only [T.ops, Set.mem_insert_iff, Set.mem_singleton_iff] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · simp only [Option.mem_def, Option.some.injEq] at hr; subst hr; trivial
  · simp only [Option.mem_def, Option.some.injEq] at hr; subst hr
    exact ⟨hargs 0, hargs 1⟩
  · have h0 : Hid (args 0) := hargs 0
    simp only [Option.mem_def] at hr
    generalize args 0 = a at h0 hr
    cases a <;> simp_all [T.fst, Hid]
  · have h0 : Hid (args 0) := hargs 0
    simp only [Option.mem_def] at hr
    generalize args 0 = a at h0 hr
    cases a <;> simp_all [T.snd, Hid]

/-- Outputting `hash s` keeps `s` secret: everything the attacker can ever know lies
in the closed set of terms in which `s` occurs only under a hash. -/
theorem hashed_secret : Secret (Proc.out .c (.hash .s) Proc.nil) {T.c} T.s := by
  intro t u w K r hs
  refine r.derive_subset (S := {t | Hid t}) (by simp [Hid]) hid_closed
    (fun n => show Hid (T.n n) from trivial) ?_ hs
  intro c' m hm
  rcases r.honest with rfl | ⟨_, (rfl : _ = []), rfl⟩
  · simp at hm
  · simp at hm
    obtain ⟨rfl, rfl⟩ := hm
    trivial

end ProVerif.Toy
