/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.DH
import ScalingTrust.ProVerif.Security

/-!
# Examples

The translation of the survey's running example (§2.2), the simplified
Denning-Sacco protocol, over the algebra of `ProVerif.DH`: its free names are a
public channel `c` and a private secret `s`, and its roles and system are `do`
blocks.  Then an attack, and a secrecy proof by the closed-set method, whose closed
set is defined through the universal property of the message quotient.
-/

namespace ProVerif.Examples

open FirstOrder.Language

/-- The free names: a public channel and a private secret. -/
inductive Free
  | c
  | s
  deriving DecidableEq

/-- Messages over the Diffie-Hellman algebra with these free names. -/
abbrev M : Type := (DH.T Free).Msg

/-- The algebra: `c` is public and `s` private. -/
noncomputable abbrev alg : MsgAlgebra (DH.Fun Free) := DH.alg {.c}

def c : M := DH.const .c
def s : M := DH.const .s

/-! ## The protocol

```
P_A(sskA, pkB) = ! new k; out(c, aenc(sign(k, sskA), pkB)); in(c, x); let z = sdec(x, k) in 0
P_B(skB, spkA) = ! in(c, y); let y' = adec(y, skB) in let xk = check(y', spkA) in
                   out(c, senc(s, xk))
P₀ = new sskA; new skB; out(c, pk(sskA)); out(c, pk(skB)); (P_A(sskA, pk(skB)) | P_B(skB, pk(sskA)))
```
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
theorem leak_attack : ¬ (Proc.out c s Proc.nil).Secret alg.derive s := by
  intro h
  have hc : c ∈ alg.derive (∅ : Set M) :=
    MsgAlgebra.app_mem_derive (ms := ![]) rfl fun i => i.elim0
  have ht : [Act.out c s] ∈ Proc.out c s Proc.nil := .inr ⟨[], rfl, rfl⟩
  have he : [Act.inp c s] ∈ Enemy alg.derive (∅ : Set M) := .inp _ _ hc .nil
  refine h [.comm c s] ⟨⟨⟨![_, _], [(0, .out c s), (1, .inp c s)], Fin.forall_fin_two.2 ⟨ht, he⟩,
    Fin.forall_fin_two.2 ⟨rfl, rfl⟩, .pair (by decide) c s .nil⟩, List.nodup_nil⟩,
    List.forall_mem_singleton.2 nofun⟩ _ (List.prefix_refl _) _ (Set.mem_singleton _) ?_
  show s ∈ alg.derive (alg.derive ∅ ∪ {m | ∃ c', Act.comm c s = .comm c' m ∧ c' ∈ alg.derive ∅})
  exact alg.derive.le_closure _ (Set.mem_union_right _ ⟨c, rfl, hc⟩)

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
  rintro e (rfl : e = _) v
  simp only [Term.realize_func₂, Term.realize_func₀, Term.realize_var, funMap_prop, hid,
    Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp [and_comm]

/-- Messages in which `s` occurs only under a hash. -/
def Hid : M → Prop := hid_satisfies.lift fun _ => True

theorem hid_app {n : ℕ} (f : DH.Fun Free n) (ms : Fin n → M) :
    Hid (.app f ms) = hid f fun i => Hid (ms i) :=
  hid_satisfies.lift_app _ f ms

theorem hid_app₂ {f : DH.Fun Free 2} (hf : ∀ args, hid f args = ∀ i, args i) {m k : M} :
    Hid (.app f ![m, k]) ↔ Hid m ∧ Hid k := by
  rw [hid_app, hf]
  exact Fin.forall_fin_two

theorem hid_closed : ClosedUnder alg.ops {m | Hid m} := by
  rintro o (ho | hd) args hargs r hr
  · obtain ⟨n, f, hf, rfl⟩ := Set.mem_iUnion.1 ho
    dsimp only at hr
    obtain ⟨ms, hms, hr⟩ := liftFail_eq_some.1 hr
    obtain rfl := Option.some_injective _ hr
    show Hid (.app f ms)
    rw [hid_app]
    cases f with
    | const a => cases a <;> first | exact fun i => i.elim0 | exact nomatch (hf : Free.s = Free.c)
    | hash => trivial
    | _ => exact fun i => hargs i _ (hms i)
  · rcases hd with rfl | rfl | rfl <;> dsimp only at hr <;>
      obtain ⟨ms, hms, hr⟩ := liftFail_eq_some.1 hr <;> have h : Hid (ms 0) := hargs 0 _ (hms 0)
    · rw [DH.sdec_eq_some.1 hr, DH.senc] at h
      exact ((hid_app₂ fun _ => rfl).1 h).1
    · rw [DH.adec_eq_some.1 hr, DH.aenc] at h
      exact ((hid_app₂ fun _ => rfl).1 h).1
    · obtain ⟨k, hk, -⟩ := DH.check_eq_some.1 hr
      rw [hk, DH.sign] at h
      exact ((hid_app₂ fun _ => rfl).1 h).1

theorem not_hid_s : ¬ Hid s := by
  rw [s, DH.const, hid_app]
  exact id

theorem hid_hash (m : M) : Hid (DH.hash m) := by
  rw [DH.hash, hid_app]
  trivial

/-- Outputting `hash s` keeps `s` secret: everything the attacker can ever know lies
in the closed set of messages in which `s` occurs only under a hash. -/
theorem hashed_secret : (Proc.out c (DH.hash s) Proc.nil).Secret alg.derive s := by
  refine Proc.secret_of_closed (S := {m | Hid m}) hid_closed (fun _ => trivial) ?_ not_hid_s
  rintro u (rfl | ⟨_, (rfl : _ = []), rfl⟩)
  · trivial
  · exact ⟨hid_hash s, trivial⟩

end ProVerif.Examples
