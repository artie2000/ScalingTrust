/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.Translation.Examples.DenningSacco

/-!
# Examples

Security proofs of translated models.  `DenningSacco`, in `../Translation/Examples/`,
is the translation of the survey's running example (§2.2), the simplified
Denning-Sacco protocol, whose one query is `attacker(s)`; `system_secret` proves it by
the closed-set method, `Proc.secret_of_closed`.  `leak_attack` exhibits an attack, on
the one-action process `out(c, s)` over the same algebra, and `swap` is a process written
by hand over it, with tuples and a boolean.
-/

namespace ProVerif.TraceSemantics.Examples

open FirstOrder.Language DenningSacco
open Attacker (derive)

/-! ## An attack -/

/-- Outputting `s` in the clear is an attack: the attacker receives it. -/
theorem leak_attack : ¬ (Proc.out c s Proc.nil).Secret s := by
  intro h
  have hc : c ∈ derive (∅ : Set T.Msg) :=
    Attacker.app_mem_derive (Attacker.ofDecls_mem (by trivial)) (ms := ![]) fun i => i.elim0
  have ht : [Act.out c s] ∈ Proc.out c s Proc.nil := .inr ⟨[], rfl, rfl⟩
  have he : [Act.inp c s] ∈ Enemy (∅ : Set T.Msg) := .inp _ _ hc .nil
  refine h [.comm c s] ⟨⟨⟨![_, _], [(0, .out c s), (1, .inp c s)], Fin.forall_fin_two.2 ⟨ht, he⟩,
    Fin.forall_fin_two.2 ⟨rfl, rfl⟩, .pair (by decide) c s .nil⟩, List.nodup_nil⟩,
    List.forall_mem_singleton.2 nofun⟩ ?_
  show s ∈ derive (derive ∅ ∪ {m | ∃ c', Act.comm c s = .comm c' m ∧ c' ∈ derive ∅})
  exact derive.le_closure _ (Set.mem_union_right _ ⟨c, rfl, hc⟩)

/-! ## The secrecy proof

The closed set is the set of messages the attacker may know when the protocol has
created the names `N`, its keys `sskA` and `skB` and the session keys `k`: a message in
which `s` and the names in `N` occur only under a hash, under `pk`, encrypted under a
name in `N`, or signed with a name in `N` and encrypted for one.  The responder's output
`senc(s, xk)` lies in it when `xk ∈ N`, which the responder's checks guarantee: `xk` was
signed with `sskA`, and only the initiator signs with `sskA`, only session keys.

To define the set on messages it must respect the equation, so it is evaluation in a
structure on `Shape`: a message's shape records whether the attacker may know it and
whether it is a name in `N`, the public key of one or a signature of one with one, the
three shapes that the interpretations of `aenc` and `senc` consult.
-/

/-- What matters about a message. -/
structure Shape where
  /-- The attacker may know it. -/
  safe : Prop
  /-- It is a name in `N`. -/
  nonce : Prop
  /-- It is `pk(k)` for a name `k ∈ N`. -/
  key : Prop
  /-- It is `sign(k, k')` for names `k, k' ∈ N`. -/
  sig : Prop

/-- The interpretation of the symbols on `Shape`.  `senc` hides its plaintext when the key
is a name in `N`, and `aenc` when the key is the public key of one and the plaintext a
signature by one; `pk` and `hash` hide their argument; every other symbol, the tuples
included, is safe when its arguments are, and the booleans are safe. -/
def shape : ∀ {n : ℕ}, Sig.withData Fun n → (Fin n → Shape) → Shape
  | _, .inl (.const .c), _ => ⟨True, False, False, False⟩
  | _, .inl (.const .s), _ => ⟨False, False, False, False⟩
  | _, .inl .g, _ => ⟨True, False, False, False⟩
  | _, .inl .pk, a => ⟨True, False, (a 0).nonce, False⟩
  | _, .inl .hash, _ => ⟨True, False, False, False⟩
  | _, .inl .senc, a => ⟨(a 0).safe ∧ (a 1).safe ∨ (a 1).nonce, False, False, False⟩
  | _, .inl .aenc, a => ⟨(a 0).safe ∧ (a 1).safe ∨ (a 1).key ∧ (a 0).sig, False, False, False⟩
  | _, .inl .sign, a => ⟨(a 0).safe ∧ (a 1).safe, False, False, (a 0).nonce ∧ (a 1).nonce⟩
  | _, .inl .exp, a => ⟨(a 0).safe ∧ (a 1).safe, False, False, False⟩
  | _, .inr (.tuple _), a => ⟨∀ i, (a i).safe, False, False, False⟩
  | _, .inr .tt, _ => ⟨True, False, False, False⟩
  | _, .inr .ff, _ => ⟨True, False, False, False⟩

instance : (Sig.lang (Sig.withData Fun)).Structure Shape where
  funMap := shape
  RelMap r := r.elim

@[simp] theorem funMap_shape {n : ℕ} (f : Sig.withData Fun n) (args : Fin n → Shape) :
    Structure.funMap (L := Sig.lang (Sig.withData Fun)) f args = shape f args := rfl

theorem shape_satisfies : T.Satisfies Shape := by
  refine T₀.satisfies_withData_iff.2 ?_
  rintro e (rfl : e = _) v
  simp [Term.realize_var, shape, and_comm]

/-- The shape of a message when the protocol has created the names `N`: a name in `N` is
a `nonce` the attacker may not know, any other name one it may. -/
def abs (N : Set ℕ) : T.Msg → Shape :=
  shape_satisfies.lift fun n => ⟨n ∉ N, n ∈ N, False, False⟩

/-- The messages the attacker may know when the protocol has created the names `N`. -/
def Safe (N : Set ℕ) (m : T.Msg) : Prop := (abs N m).safe

theorem abs_app (N : Set ℕ) {n : ℕ} (f : Sig.withData Fun n) (ms : Fin n → T.Msg) :
    abs N (.app f ms) = shape f fun i => abs N (ms i) :=
  shape_satisfies.lift_app _ f ms

@[simp] theorem abs_name (N : Set ℕ) (n : ℕ) :
    abs N (Names.nonce n) = ⟨n ∉ N, n ∈ N, False, False⟩ := rfl

@[simp] theorem abs_s (N : Set ℕ) : abs N s = ⟨False, False, False, False⟩ := by
  simp [s, abs_app, shape]

@[simp] theorem abs_pk (N : Set ℕ) (k : T.Msg) :
    abs N (pk k) = ⟨True, False, (abs N k).nonce, False⟩ := by
  simp [pk, abs_app, shape]

@[simp] theorem abs_senc (N : Set ℕ) (m k : T.Msg) :
    abs N (senc m k) =
      ⟨(abs N m).safe ∧ (abs N k).safe ∨ (abs N k).nonce, False, False, False⟩ := by
  simp [senc, abs_app, shape]

@[simp] theorem abs_aenc (N : Set ℕ) (m p : T.Msg) :
    abs N (aenc m p) =
      ⟨(abs N m).safe ∧ (abs N p).safe ∨ (abs N p).key ∧ (abs N m).sig, False, False, False⟩ := by
  simp [aenc, abs_app, shape]

@[simp] theorem abs_sign (N : Set ℕ) (m k : T.Msg) :
    abs N (sign m k) =
      ⟨(abs N m).safe ∧ (abs N k).safe, False, False, (abs N m).nonce ∧ (abs N k).nonce⟩ := by
  simp [sign, abs_app, shape]

@[simp] theorem abs_tuple (N : Set ℕ) (n : ℕ) (ms : Fin n → T.Msg) :
    abs N (StdOps.tuple n ms) = ⟨∀ i, (abs N (ms i)).safe, False, False, False⟩ := by
  simp [Theory.Msg.tuple_def, abs_app, shape]

@[simp] theorem abs_tt (N : Set ℕ) : abs N (StdOps.tt : T.Msg) = ⟨True, False, False, False⟩ := by
  simp [Theory.Msg.tt_def, abs_app, shape]

@[simp] theorem abs_ff (N : Set ℕ) : abs N (StdOps.ff : T.Msg) = ⟨True, False, False, False⟩ := by
  simp [Theory.Msg.ff_def, abs_app, shape]

/-- Only a name in `N` is a `nonce`, and the attacker may not know it. -/
theorem not_safe_of_nonce (N : Set ℕ) (m : T.Msg) (h : (abs N m).nonce) : ¬ Safe N m := by
  induction m using Quotient.inductionOn with
  | h t =>
    cases t with
    | var n => exact fun h' => h' h
    | func f ts =>
      rcases f with f | d
      · cases f
        case const a => cases a <;> exact (h : False).elim
        all_goals exact (h : False).elim
      · cases d <;> exact (h : False).elim

/-- The set is closed under the attacker's operations. -/
theorem safe_closed (N : Set ℕ) : ClosedUnder Attacker.ops {m | Safe N m} := by
  rintro o ((ho | hd) | hs) args hargs r hr
  · obtain ⟨n, f, hf, rfl⟩ := Set.mem_iUnion.1 ho
    dsimp only at hr
    obtain ⟨ms, hms, hr⟩ := liftFail_eq_some.1 hr
    obtain rfl := Option.some_injective _ hr
    have h (i) : Safe N (ms i) := hargs i _ (hms i)
    show (abs N (.app (.inl f) ms)).safe
    rw [abs_app]
    cases f with
    | const a =>
      cases a
      · trivial
      · exact (hf : False).elim
    | g => trivial
    | pk => trivial
    | hash => trivial
    | senc => exact Or.inl ⟨h 0, h 1⟩
    | aenc => exact Or.inl ⟨h 0, h 1⟩
    | sign => exact ⟨h 0, h 1⟩
    | exp => exact ⟨h 0, h 1⟩
  · rcases hd with rfl | rfl | rfl <;> dsimp only at hr <;>
      obtain ⟨ms, hms, hr⟩ := liftFail_eq_some.1 hr <;>
      have h₀ : Safe N (ms 0) := hargs 0 _ (hms 0) <;> have h₁ : Safe N (ms 1) := hargs 1 _ (hms 1)
    · rw [sdec_eq_some.1 hr] at h₀
      simp only [Set.mem_ofPred_eq, Safe, abs_senc] at h₀ ⊢
      exact h₀.elim And.left fun hk => (not_safe_of_nonce N _ hk h₁).elim
    · rw [adec_eq_some.1 hr] at h₀
      simp only [Set.mem_ofPred_eq, Safe, abs_aenc, abs_pk] at h₀ ⊢
      exact h₀.elim And.left fun hk => (not_safe_of_nonce N _ hk.1 h₁).elim
    · obtain ⟨k, hk, -⟩ := check_eq_some.1 hr
      rw [hk] at h₀
      simp only [Set.mem_ofPred_eq, Safe, abs_sign] at h₀ ⊢
      exact h₀.1
  · rcases hs with (⟨n, rfl⟩ | ⟨⟨k, i⟩, rfl⟩) | rfl | rfl <;> dsimp only at hr
    · obtain ⟨ms, hms, hr⟩ := liftFail_eq_some.1 hr
      obtain rfl := Option.some_injective _ hr
      simp only [Set.mem_ofPred_eq, Safe, abs_tuple]
      exact fun i => hargs i _ (hms i)
    · obtain ⟨ms, hms, hr⟩ := liftFail_eq_some.1 hr
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hr
      have h₀ : Safe N (ms 0) := hargs 0 _ (hms 0)
      rw [StdOps.tuple_untuple hb] at h₀
      simp only [Set.mem_ofPred_eq, Safe, abs_tuple] at h₀ ⊢
      exact h₀ i
    · obtain rfl := Option.some_injective _ hr
      simp [Safe]
    · obtain rfl := Option.some_injective _ hr
      simp [Safe]

/-- The protocol is bounded: its keys and session keys are the names it creates, and
everything it sends is safe relative to them. -/
theorem system_bounded : system.Bounded (fun N => {m | Safe N m}) fun _ => True := by
  simp only [system, initiator, responder, Proc.run, ContT.run_bind, ContT.run_mk,
    Bool.false_eq_true, if_true, if_false]
  refine .new fun a => .new fun b => .out (fun N _ => ?_) (.out (fun N _ => ?_) (.par
    (.bang (.new fun k => .out (fun N hN => ?_) (.inp fun x => ?_)))
    (.bang (.inp fun y => ?_))))
  · simp [Safe]
  · simp [Safe]
  · simp [Safe, hN.1.1.2, hN.1.2, hN.2]
  · split <;> exact .nil
  · split
    · rename_i y' hA
      split
      · rename_i xk hC
        refine .out (fun N hN => ?_) .nil
        obtain ⟨⟨⟨-, ha⟩, hb⟩, hy⟩ := hN
        obtain ⟨k, rfl, hpk⟩ := check_eq_some.1 hC
        obtain rfl := adec_eq_some.1 hA
        have hk : (abs N k).nonce := by
          have h := congrArg (fun m => (abs N m).key) hpk
          simp only [abs_pk, abs_name] at h
          exact h.mp ha
        simp only [Set.mem_ofPred_eq, Safe, abs_aenc, abs_sign, abs_pk, abs_senc, abs_s] at hy ⊢
        exact Or.inr (hy.elim (fun h => (not_safe_of_nonce N k hk h.1.2).elim) fun h => h.2.1)
      · exact .nil
    · exact .nil

/-- The model's `query attacker(s)` holds: the protocol keeps `s` secret. -/
theorem system_secret : query₁ :=
  Proc.secret_of_closed (S := fun N => {m | Safe N m}) safe_closed (fun _ _ hn => hn)
    system_bounded fun N h => by simp [Safe] at h

/-! ## Tuples and booleans, written by hand -/

/-- `in(c, (x, y)); out(c, (y, x, true))`.  `Tuple.ofMsg` reads the pair, and bound with
`←` its failure stops the process, as ProVerif's `let` without `else` does; a product or a
boolean where a message is expected is the tuple or the constant. -/
def swap : Proc T.Msg :=
  .run do
    let m ← .recv c
    let (x, y) ← Tuple.ofMsg (T.Msg × T.Msg) m
    .send c (y, x, (true : T.Msg))

theorem swap_mem_tree : swap ∈ Descriptive.tree (Act T.Msg) := by
  aesop (add norm simp [swap])

end ProVerif.TraceSemantics.Examples
