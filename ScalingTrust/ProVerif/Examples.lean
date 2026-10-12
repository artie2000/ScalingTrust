/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.DH
import ScalingTrust.ProVerif.Query

/-!
# Examples

The survey's running example (§2.2), the simplified Denning-Sacco protocol, written
as `do` blocks over the Diffie-Hellman algebra; an attack; and a secrecy proof by
the closed-set method, whose closed set is defined through the universal property
of the message quotient.
-/

namespace ProVerif.Examples

open FirstOrder.Language Attacker

/-- The free names: a public channel and a private secret. -/
inductive Free
  | c
  | s
  deriving DecidableEq

/-- Messages over the Diffie-Hellman algebra with these free names. -/
abbrev M : Type := Msg (DH.T Free)

noncomputable instance pubFree : Pub (DH.T Free) := DH.pub {.c}

def c : M := DH.const .c
def s : M := DH.const .s

/-! ## The protocol

```
P_A(sskA, pkB) = ! new k; out(c, aenc(sign(k, sskA), pkB)); in(c, x); let z = sdec(x, k) in 0
P_B(skB, spkA) = ! in(c, y); let y' = adec(y, skB) in let xk = check(y', spkA) in
                   out(c, senc(s, xk))
P₀ = new sskA; new skB; out(c, pk(sskA)); out(c, pk(skB)); (P_A(sskA, pk(skB)) | P_B(skB, pk(sskA)))
```

The survey notes (Example 3.2) that this protocol does not keep `s` secret.
-/

/-- The role of `A`: create a session key, send it signed and encrypted, and decrypt
the reply with it. -/
noncomputable def initiator (sskA pkB : M) : Cont (Proc M) Unit := do
  .repl
  let k ← .fresh
  .send c (DH.aenc (DH.sign k sskA) pkB)
  let x ← .recv c
  match DH.sdec x k with
  | some _ => pure ()
  | none => .stop

/-- The role of `B`: receive the session key, decrypt, verify the signature, and send
the secret under the key. -/
noncomputable def responder (skB spkA : M) : Cont (Proc M) Unit := do
  .repl
  let y ← .recv c
  match DH.adec y skB with
  | none => .stop
  | some y' =>
    match DH.check y' spkA with
    | none => .stop
    | some xk => .send c (DH.senc s xk)

/-- The protocol `P₀`. -/
noncomputable def system : Proc M := .run do
  let sskA ← .fresh
  let skB ← .fresh
  .send c (DH.pk sskA)
  .send c (DH.pk skB)
  if ← .fork then initiator sskA (DH.pk skB) else responder skB (DH.pk sskA)

/-! ## An attack -/

/-- Outputting `s` in the clear is an attack: the attacker receives it. -/
theorem leak_attack : ¬ Secret (Proc.out c s Proc.nil) {c} s := by
  intro h
  have ht : [Act.out c s] ∈ Proc.out c s Proc.nil := .inr ⟨[], rfl, rfl⟩
  have he : [Act.inp c s, .say s] ∈ Enemy {c} :=
    .inp _ _ (derive.le_closure _ rfl) (.say _ (derive.le_closure _ (Set.mem_insert _ _)) .nil)
  have hc : Closed [Act.say s] := fun _ ha h => by
    obtain rfl := List.mem_singleton.1 ha
    cases h
  exact h [.say s] ⟨⟨⟨![_, _], [(0, .out c s), (1, .inp c s), (1, .say s)],
    Fin.forall_fin_two.2 ⟨ht, he⟩, Fin.forall_fin_two.2 ⟨rfl, rfl⟩, by simp [comms]⟩,
    List.nodup_nil⟩, hc⟩ List.mem_cons_self

/-! ## A secrecy proof

"`s` occurs only under a hash" is a predicate on raw terms.  To define it on messages
it must respect the equation, which it does because it is evaluation in a structure
on `Prop` that satisfies the equation: a hash is hidden, the secret is not, and
every other symbol is hidden when its arguments are.
-/

/-- The interpretation of the symbols on `Prop`. -/
def hid : ∀ {n : ℕ}, DH.Fun Free n → (Fin n → Prop) → Prop
  | _, .hash, _ => True
  | _, .const .s, _ => False
  | _, _, args => ∀ i, args i

instance : (Sig.lang (DH.Fun Free)).Structure Prop where
  funMap := hid
  RelMap r := r.elim

@[simp] theorem funMap_prop {n : ℕ} (f : DH.Fun Free n) (args : Fin n → Prop) :
    Structure.funMap (L := Sig.lang (DH.Fun Free)) f args = hid f args := rfl

theorem hid_satisfies : (DH.T Free).Satisfies Prop := by
  intro e he v
  rw [show (DH.T Free).E = DH.E Free from rfl, DH.E, Set.mem_singleton_iff] at he
  subst he
  simp only [Term.realize_func₂, Term.realize_func₀, Term.realize_var, funMap_prop, hid,
    Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp [and_comm]

/-- Messages in which `s` occurs only under a hash. -/
def Hid : M → Prop := Msg.lift hid_satisfies fun _ => True

theorem hid_app {n : ℕ} (f : DH.Fun Free n) (ms : Fin n → M) :
    Hid (Msg.app f ms) = hid f fun i => Hid (ms i) :=
  Msg.lift_app _ _ f ms

theorem hid_pair {a b : M} : Hid (DH.pair a b) ↔ Hid a ∧ Hid b := by
  rw [DH.pair, hid_app]
  exact Fin.forall_fin_two

theorem hid_senc {m k : M} : Hid (DH.senc m k) ↔ Hid m ∧ Hid k := by
  rw [DH.senc, hid_app]
  exact Fin.forall_fin_two

theorem hid_aenc {m p : M} : Hid (DH.aenc m p) ↔ Hid m ∧ Hid p := by
  rw [DH.aenc, hid_app]
  exact Fin.forall_fin_two

theorem hid_sign {m k : M} : Hid (DH.sign m k) ↔ Hid m ∧ Hid k := by
  rw [DH.sign, hid_app]
  exact Fin.forall_fin_two

theorem hid_closed : ClosedUnder (Pub.ops (DH.T Free)) {m | Hid m} := by
  rintro o (ho | ⟨d, hd, rfl⟩) args hargs r hr
  · rw [Set.mem_iUnion] at ho
    obtain ⟨n, f, hf, rfl⟩ := ho
    obtain rfl := Set.mem_singleton_iff.1 hr
    show Hid (Msg.app f args)
    rw [hid_app]
    cases f with
    | const a =>
      cases a
      · exact fun i => i.elim0
      · exact nomatch (hf : Free.s = Free.c)
    | hash => trivial
    | _ => exact hargs
  · change d.2 args = some r at hr
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at hr hargs
    · obtain ⟨b, hb⟩ := DH.fst_eq_some.1 hr
      have h : Hid (args 0) := hargs 0
      rw [hb] at h
      exact (hid_pair.1 h).1
    · obtain ⟨a, ha⟩ := DH.snd_eq_some.1 hr
      have h : Hid (args 0) := hargs 0
      rw [ha] at h
      exact (hid_pair.1 h).2
    · have h : Hid (args 0) := hargs 0
      rw [DH.sdec_eq_some.1 hr] at h
      exact (hid_senc.1 h).1
    · have h : Hid (args 0) := hargs 0
      rw [DH.adec_eq_some.1 hr] at h
      exact (hid_aenc.1 h).1
    · obtain ⟨k, hk, -⟩ := DH.check_eq_some.1 hr
      have h : Hid (args 0) := hargs 0
      rw [hk] at h
      exact (hid_sign.1 h).1
    · obtain ⟨k, hk⟩ := DH.getmess_eq_some.1 hr
      have h : Hid (args 0) := hargs 0
      rw [hk] at h
      exact (hid_sign.1 h).1

/-- Outputting `hash s` keeps `s` secret: everything the attacker can ever know lies
in the closed set of messages in which `s` occurs only under a hash. -/
theorem hid_c : Hid c := by
  rw [c, DH.const, hid_app]
  exact fun i => i.elim0

theorem not_hid_s : ¬ Hid s := by
  rw [s, DH.const, hid_app]
  exact id

theorem hid_hash (m : M) : Hid (DH.hash m) := by
  rw [DH.hash, hid_app]
  trivial

theorem hashed_secret : Secret (Proc.out c (DH.hash s) Proc.nil) {c} s := by
  refine secret_of_closed (S := {m | Hid m}) ?_ hid_closed
    (fun n => show Hid (Msg.name n) from trivial) ?_ ?_ not_hid_s
  · rintro _ rfl
    exact hid_c
  · intro t ht c' m hm
    rcases ht with rfl | ⟨_, (rfl : _ = []), rfl⟩
    · simp at hm
    · simp at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact hid_hash s
  · intro t ht m hm
    rcases ht with rfl | ⟨_, (rfl : _ = []), rfl⟩ <;> simp at hm

end ProVerif.Examples
