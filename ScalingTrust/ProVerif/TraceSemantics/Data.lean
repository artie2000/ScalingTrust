/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.TraceSemantics.Term

/-!
# The data symbols: tuples and booleans

Tuples and booleans are built into ProVerif's term algebra whatever a model declares
(manual, Appendix B).  `Sig.withData` adds their symbols to a signature and
`Theory.withData` carries a theory across, so that the messages of a model are
`T.withData.Msg`.  `StdOps` is the structure they put on a type of messages, with the laws
that make `untuple` the inverse of `tuple`; `T.withData.Msg` is an instance.

For protocols written directly in Lean, a product of messages `(m₁, …, mₙ)` where a
message is expected is the `n`-tuple, by the class `Tuple` and a coercion,
`Tuple.ofMsg (M × ⋯ × M)` reads the components back, and a `Bool` where a message is
expected is the constant, `StdOps.ofBool`.  The components of a product are messages, so a
nested tuple or a boolean inside one is written with its type, as `((a, b) : M)`.
-/

namespace ProVerif.TraceSemantics

open FirstOrder FirstOrder.Language

variable {F : Sig} {T : Theory F}

/-- The data symbols: a tuple constructor of every arity and the two booleans. -/
inductive Data : ℕ → Type
  | tuple (n : ℕ) : Data n
  | tt : Data 0
  | ff : Data 0

/-- `F` with the data symbols. -/
abbrev Sig.withData (F : Sig) : Sig := fun n => F n ⊕ Data n

/-- The inclusion of `F` in `F.withData`, as a map of languages. -/
def Sig.inclusion (F : Sig) : F.lang →ᴸ F.withData.lang := ⟨fun _ => Sum.inl, fun _ => id⟩

theorem Term.Rigid.onTerm {free : ∀ n, F n → Bool} {t : Term F} (h : t.Rigid free) :
    Term.Rigid (fun n => Sum.elim (free n) fun _ => true) ((Sig.inclusion F).onTerm t) := by
  cases t with
  | var => exact h.elim
  | func f ts => exact h

/-- `T` on the signature with the data symbols: the same equations, and the data symbols
free. -/
def Theory.withData (T : Theory F) : Theory F.withData where
  E := (fun e : Term F × Term F =>
    ((Sig.inclusion F).onTerm e.1, (Sig.inclusion F).onTerm e.2)) '' T.E
  free n := Sum.elim (T.free n) fun _ => true
  heads := by
    rintro _ ⟨e, he, rfl⟩
    exact ⟨(T.heads e he).1.onTerm, (T.heads e he).2.onTerm⟩

@[simp] theorem Theory.withData_free (T : Theory F) (n : ℕ) (f : F.withData n) :
    T.withData.free n f = Sum.elim (T.free n) (fun _ => true) f := rfl

/-- A structure for `F.withData` satisfies `T.withData` iff, read as a structure for `F`
through the inclusion, it satisfies `T`. -/
theorem Theory.satisfies_withData_iff (T : Theory F) {A : Type} [F.withData.lang.Structure A] :
    T.withData.Satisfies A ↔ @Theory.Satisfies F T A ((Sig.inclusion F).reduct A) := by
  have h := @LHom.realize_onTerm _ _ A ((Sig.inclusion F).reduct A) ℕ _ (Sig.inclusion F)
    ((Sig.inclusion F).isExpansionOn_reduct A)
  simp only [Theory.Satisfies, Theory.withData, Set.forall_mem_image, h]

/-- Through the inclusion, a symbol of `F` is interpreted as its image. -/
@[simp] theorem Sig.funMap_inl {A : Type} [F.withData.lang.Structure A] {n : ℕ} (f : F n)
    (as : Fin n → A) :
    @Structure.funMap F.lang A ((Sig.inclusion F).reduct A) n f as =
      Structure.funMap (L := F.withData.lang) (Sum.inl f) as := rfl

/-- The messages of `T.withData` interpret `F` through the inclusion. -/
instance : F.lang.Structure T.withData.Msg := (Sig.inclusion F).reduct _

/-- The messages of `T.withData` satisfy `T`: the equation theorems of a translated model. -/
theorem Theory.withData_satisfies (T : Theory F) : T.Satisfies T.withData.Msg :=
  T.satisfies_withData_iff.1 T.withData.satisfies_msg

/-- The standard operations on a type of messages: tuples of every arity, `untuple` reading
the components back, and the two booleans. -/
class StdOps (M : Type) where
  tuple (n : ℕ) : (Fin n → M) → M
  untuple (n : ℕ) : M → Option (Fin n → M)
  tt : M
  ff : M
  untuple_tuple (n : ℕ) (a : Fin n → M) : untuple n (tuple n a) = some a
  tuple_untuple {n : ℕ} {m : M} {a : Fin n → M} : untuple n m = some a → m = tuple n a
  tt_ne_ff : tt ≠ ff

namespace Theory.Msg

/-- The data symbols give the messages of `T.withData` their standard operations. -/
instance : StdOps T.withData.Msg where
  tuple n a := app (.inr (.tuple n)) a
  untuple n m :=
    match m.view with
    | .app (.inr (.tuple k)) a => if h : k = n then some fun i => a (Fin.cast h.symm i) else none
    | _ => none
  tt := app (.inr .tt) ![]
  ff := app (.inr .ff) ![]
  untuple_tuple n a := by simp
  tuple_untuple {n m a} h := by
    rcases hv : m.view with _ | ⟨f, b⟩ | _ <;> rw [hv] at h <;> try cases h
    rcases f with f | d
    · cases h
    cases d with
    | tuple _ =>
      simp only [Option.dite_none_right_eq_some] at h
      obtain ⟨rfl, h⟩ := h
      cases h
      exact m.eq_app_of_view hv
    | tt => cases h
    | ff => cases h
  tt_ne_ff h := by simpa using congrArg view h

theorem tuple_def (n : ℕ) (a : Fin n → T.withData.Msg) :
    StdOps.tuple n a = app (.inr (.tuple n)) a := rfl

theorem tt_def : (StdOps.tt : T.withData.Msg) = app (.inr .tt) ![] := rfl

theorem ff_def : (StdOps.ff : T.withData.Msg) = app (.inr .ff) ![] := rfl

end Theory.Msg

/-! ## Writing tuples and booleans -/

section

variable {M : Type}

/-- A product of messages read as a tuple: `α` is `M × ⋯ × M` with `n` factors, and
`components` is the vector of them. -/
class Tuple (α M : Type) (n : outParam ℕ) where
  components : α ≃ (Fin n → M)

instance Tuple.single : Tuple M M 1 where
  components := ⟨fun m => ![m], fun v => v 0, fun _ => rfl,
    fun v => funext fun i => by rw [Subsingleton.elim i 0]; simp⟩

instance Tuple.cons {β : Type} {n : ℕ} [Tuple β M n] : Tuple (M × β) M (n + 1) where
  components := ⟨fun p => Matrix.vecCons p.1 (Tuple.components p.2),
    fun v => (Matrix.vecHead v, Tuple.components.symm (Matrix.vecTail v)),
    fun p => by simp, fun v => by simp⟩

@[simp] theorem Tuple.components_single (m : M) : (Tuple.components m : Fin 1 → M) = ![m] := rfl

@[simp] theorem Tuple.components_cons {β : Type} {n : ℕ} [Tuple β M n] (a : M) (p : β) :
    Tuple.components (a, p) = Matrix.vecCons a (Tuple.components p) := rfl

end

section

variable {M : Type} [StdOps M]

namespace StdOps

/-- A boolean, as a message. -/
@[coe] def ofBool : Bool → M
  | true => tt
  | false => ff

instance : Coe Bool M := ⟨ofBool⟩

/-! Not `simp` lemmas: rewriting `↑true` inside the condition of an `if` leaves it in a form
that `split`, and so the prefix-closure proofs of translated models, cannot split. -/

theorem ofBool_true : (ofBool true : M) = tt := rfl

theorem ofBool_false : (ofBool false : M) = ff := rfl

end StdOps

namespace Tuple

variable {α β : Type} {n : ℕ}

/-- A product of messages, as the tuple. -/
@[coe] def toMsg [Tuple α M n] (p : α) : M := StdOps.tuple n (components p)

instance [Tuple β M n] : CoeOut (M × β) M := ⟨toMsg⟩

/-- The components of `m`, if it is a tuple of the arity of `α`. -/
def ofMsg (α : Type) [Tuple α M n] (m : M) : Option α :=
  (StdOps.untuple n m).map components.symm

theorem toMsg_def [Tuple α M n] (p : α) : (toMsg p : M) = StdOps.tuple n (components p) := rfl

@[simp] theorem ofMsg_toMsg [Tuple α M n] (p : α) : ofMsg α (toMsg p : M) = some p := by
  simp [ofMsg, toMsg, StdOps.untuple_tuple]

theorem eq_toMsg_of_ofMsg [Tuple α M n] {m : M} {p : α} (h : ofMsg α m = some p) :
    m = toMsg p := by
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [StdOps.tuple_untuple hv, toMsg_def, Equiv.apply_symm_apply]

end Tuple

end

end ProVerif.TraceSemantics
