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
free.  `alg P` is the message algebra in which the free names in `P` are public and
the rest private, the survey's `N_pub` and `N_priv`; every other symbol and every
destructor is public.
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

def const (a : A) : (T A).Msg := .app (.const a) ![]
def g : (T A).Msg := .app .g ![]
def pk (k : (T A).Msg) : (T A).Msg := .app .pk ![k]
def hash (m : (T A).Msg) : (T A).Msg := .app .hash ![m]
def senc (m k : (T A).Msg) : (T A).Msg := .app .senc ![m, k]
def aenc (m p : (T A).Msg) : (T A).Msg := .app .aenc ![m, p]
def sign (m k : (T A).Msg) : (T A).Msg := .app .sign ![m, k]
def exp (b e : (T A).Msg) : (T A).Msg := .app .exp ![b, e]

/-- The equation (2.7) on messages. -/
theorem exp_exp_g (x y : (T A).Msg) : exp (exp g x) y = exp (exp g y) x := by
  have h := (T A).satisfies_msg _ (Set.mem_singleton _) fun n => if n = 0 then x else y
  simp only [Term.realize_func₂, Term.realize_func₀, Term.realize_var] at h
  simpa [exp, g] using h

/-! ## Destructors

Each is a match on the view with one branch for its rule, then failure; the nested
pattern `pk(y)` of `adec` and `check`, which mentions a variable bound elsewhere, is
an equality test.  No rule has a may-fail variable or a `fail` pattern, so each
destructor is written on messages and lifted by `liftFail` in `alg`.
-/

open Classical

/-- `sdec(senc(x, y), y) → x` -/
noncomputable def sdec (c k : (T A).Msg) : Option (T A).Msg :=
  match c.view with
  | .app .senc a => if a 1 = k then some (a 0) else none
  | _ => none

/-- `adec(aenc(x, pk(y)), y) → x`, the rule (2.1). -/
noncomputable def adec (c k : (T A).Msg) : Option (T A).Msg :=
  match c.view with
  | .app .aenc a => if a 1 = pk k then some (a 0) else none
  | _ => none

/-- `check(sign(x, y), pk(y)) → x`, the rule (2.3). -/
noncomputable def check (s p : (T A).Msg) : Option (T A).Msg :=
  match s.view with
  | .app .sign a => if p = pk (a 1) then some (a 0) else none
  | _ => none

/-! ### The destructors' graphs are their rules -/

theorem vec_eta₂ (a : Fin 2 → (T A).Msg) : ![a 0, a 1] = a :=
  funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)

theorem sdec_eq_some {c k m : (T A).Msg} : sdec c k = some m ↔ c = senc m k := by
  refine ⟨fun h => ?_, fun h => by simp [h, sdec, senc, free]⟩
  rcases hv : c.view with _ | ⟨f, a⟩ | _ <;> simp [sdec, hv] at h
  cases f <;> simp at h
  obtain ⟨rfl, rfl⟩ := h
  rw [c.eq_app_of_view hv, senc, vec_eta₂]

theorem adec_eq_some {c k m : (T A).Msg} : adec c k = some m ↔ c = aenc m (pk k) := by
  refine ⟨fun h => ?_, fun h => by simp [h, adec, aenc, free]⟩
  rcases hv : c.view with _ | ⟨f, a⟩ | _ <;> simp [adec, hv] at h
  cases f <;> simp at h
  obtain ⟨hk, rfl⟩ := h
  rw [c.eq_app_of_view hv, aenc, ← hk, vec_eta₂]

theorem check_eq_some {s p m : (T A).Msg} :
    check s p = some m ↔ ∃ k, s = sign m k ∧ p = pk k := by
  refine ⟨fun h => ?_, fun ⟨k, hs, hp⟩ => by simp [hs, hp, check, sign, free]⟩
  rcases hv : s.view with _ | ⟨f, a⟩ | _ <;> simp [check, hv] at h
  cases f <;> simp at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨a 1, by rw [s.eq_app_of_view hv, sign, vec_eta₂], rfl⟩

/-! ## The message algebra -/

/-- The free names in `P` are public, the rest private; everything else is public. -/
noncomputable abbrev alg (P : Set A) : MsgAlgebra (Fun A) where
  toTheory := T A
  pubFun _ := {f | match f with | .const a => a ∈ P | _ => True}
  pubDtors :=
    {⟨2, liftFail fun a => sdec (a 0) (a 1)⟩, ⟨2, liftFail fun a => adec (a 0) (a 1)⟩,
     ⟨2, liftFail fun a => check (a 0) (a 1)⟩}

end ProVerif.DH
