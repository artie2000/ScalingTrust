/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.Term

/-!
# Example: the standard primitives with Diffie-Hellman

The translation of the declarations of the survey's primitives (§2.1) that its
running example uses: the free names `A`, symmetric and asymmetric encryption,
signatures and a hash, with Diffie-Hellman exponentiation and its equation (2.7).
`exp` is the only symbol at the root of an equation, so every other symbol is
free.  `pub P` makes the free names in `P` public and the rest private, the
survey's `N_pub` and `N_priv`; every other symbol and every destructor is public.
Each destructor comes with the theorem that its graph is exactly the instances of
its rewrite rule, `sdec c k = some m ↔ c = senc m k` and so on.
-/

namespace ProVerif.DH

open FirstOrder.Language

/-- The constructors, by arity. -/
inductive Fun (A : Type) : ℕ → Type
  | const (a : A) : Fun A 0
  | g : Fun A 0
  | pk : Fun A 1
  | hash : Fun A 1
  | senc : Fun A 2
  | aenc : Fun A 2
  | sign : Fun A 2
  | exp : Fun A 2

variable {A : Type}

/-- The equation (2.7), `exp(exp(g, x), y) = exp(exp(g, y), x)`. -/
def E (A : Type) : Set (Term (Fun A) × Term (Fun A)) :=
  {(.func .exp ![.func .exp ![.func .g ![], .var 0], .var 1],
    .func .exp ![.func .exp ![.func .g ![], .var 1], .var 0])}

/-- Everything but `exp` is free. -/
def free : ∀ n, Fun A n → Bool
  | _, .const _ => true
  | _, .g => true
  | _, .pk => true
  | _, .hash => true
  | _, .senc => true
  | _, .aenc => true
  | _, .sign => true
  | _, .exp => false

def T (A : Type) : Theory (Fun A) where
  E := E A
  free := free
  heads := by
    intro e he
    rw [E, Set.mem_singleton_iff] at he
    subst he
    exact ⟨rfl, rfl⟩

@[simp] theorem free_eq {n : ℕ} (f : Fun A n) : (T A).free n f = free n f := rfl

/-! ## Constructors -/

def const (a : A) : Msg (T A) := .app (.const a) ![]
def g : Msg (T A) := .app .g ![]
def pk (k : Msg (T A)) : Msg (T A) := .app .pk ![k]
def hash (m : Msg (T A)) : Msg (T A) := .app .hash ![m]
def senc (m k : Msg (T A)) : Msg (T A) := .app .senc ![m, k]
def aenc (m p : Msg (T A)) : Msg (T A) := .app .aenc ![m, p]
def sign (m k : Msg (T A)) : Msg (T A) := .app .sign ![m, k]
def exp (b e : Msg (T A)) : Msg (T A) := .app .exp ![b, e]

/-- The equation (2.7) on messages. -/
theorem exp_exp_g (x y : Msg (T A)) : exp (exp g x) y = exp (exp g y) x := by
  have h := (T A).satisfies_msg _ (Set.mem_singleton _) fun n => if n = 0 then x else y
  simp only [Term.realize_func₂, Term.realize_func₀, Term.realize_var] at h
  simpa [exp, g] using h

/-! ## Destructors

Each is a match on the view with one branch for its rule, then failure; the nested
pattern `pk(y)` of `adec` and `check`, which mentions a variable bound elsewhere, is
an equality test.  No rule has a may-fail variable, so each destructor is written
on messages and lifted by `liftFail` in `pub`.
-/

open Classical

/-- `sdec(senc(x, y), y) → x` -/
noncomputable def sdec (c k : Msg (T A)) : Option (Msg (T A)) :=
  match c.view with
  | .app .senc a => if a 1 = k then some (a 0) else none
  | _ => none

/-- `adec(aenc(x, pk(y)), y) → x`, the rule (2.1). -/
noncomputable def adec (c k : Msg (T A)) : Option (Msg (T A)) :=
  match c.view with
  | .app .aenc a => if a 1 = pk k then some (a 0) else none
  | _ => none

/-- `check(sign(x, y), pk(y)) → x`, the rule (2.3). -/
noncomputable def check (s p : Msg (T A)) : Option (Msg (T A)) :=
  match s.view with
  | .app .sign a => if p = pk (a 1) then some (a 0) else none
  | _ => none

/-! ### The destructors' graphs are their rules -/

theorem vec_eta₂ (a : Fin 2 → Msg (T A)) : ![a 0, a 1] = a :=
  funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)

theorem sdec_eq_some {c k m : Msg (T A)} : sdec c k = some m ↔ c = senc m k := by
  constructor
  · intro h
    unfold sdec at h
    generalize hv : c.view = w at h
    cases w with
    | name _ => simp at h
    | other => simp at h
    | app f a =>
      cases f <;> simp at h
      obtain ⟨rfl, rfl⟩ := h
      rw [Msg.eq_app_of_view hv, senc, vec_eta₂]
  · rintro rfl
    simp [sdec, senc, free]

theorem adec_eq_some {c k m : Msg (T A)} : adec c k = some m ↔ c = aenc m (pk k) := by
  constructor
  · intro h
    unfold adec at h
    generalize hv : c.view = w at h
    cases w with
    | name _ => simp at h
    | other => simp at h
    | app f a =>
      cases f <;> simp at h
      obtain ⟨hk, rfl⟩ := h
      rw [Msg.eq_app_of_view hv, aenc, ← hk, vec_eta₂]
  · rintro rfl
    simp [adec, aenc, free]

theorem check_eq_some {s p m : Msg (T A)} :
    check s p = some m ↔ ∃ k, s = sign m k ∧ p = pk k := by
  constructor
  · intro h
    unfold check at h
    generalize hv : s.view = w at h
    cases w with
    | name _ => simp at h
    | other => simp at h
    | app f a =>
      cases f <;> simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨a 1, by rw [Msg.eq_app_of_view hv, sign, vec_eta₂], rfl⟩
  · rintro ⟨k, rfl, rfl⟩
    simp [check, sign, free]

/-! ## Public operations -/

/-- The free names in `P` are public, the rest private; everything else is public. -/
@[instance_reducible]
noncomputable def pub (P : Set A) : Pub (T A) where
  pubFun _ := {f | match f with | .const a => a ∈ P | _ => True}
  dtors :=
    {⟨2, liftFail fun a => sdec (a 0) (a 1)⟩, ⟨2, liftFail fun a => adec (a 0) (a 1)⟩,
     ⟨2, liftFail fun a => check (a 0) (a 1)⟩}

end ProVerif.DH
