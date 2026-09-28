/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.Term

/-!
# Example: the standard primitives with Diffie-Hellman

A message algebra with the survey's standard primitives (§2.1): the booleans,
pairs, symmetric and asymmetric encryption, signatures and a hash, together with
Diffie-Hellman exponentiation and its equation (2.7).  Every symbol but `exp` is
free, and every symbol and destructor is public.
-/

namespace ProVerif.DH

open FirstOrder.Language

/-- The constructors, by arity. -/
inductive Fun : ℕ → Type
  | tt : Fun 0
  | ff : Fun 0
  | g : Fun 0
  | pk : Fun 1
  | hash : Fun 1
  | pair : Fun 2
  | senc : Fun 2
  | aenc : Fun 2
  | sign : Fun 2
  | exp : Fun 2

/-- The equation (2.7), `exp(exp(g, x), y) = exp(exp(g, y), x)`. -/
def E : Set (Term Fun × Term Fun) :=
  {(.func .exp ![.func .exp ![.func .g ![], .var 0], .var 1],
    .func .exp ![.func .exp ![.func .g ![], .var 1], .var 0])}

/-- Everything but `exp` is free. -/
def free : ∀ n, Fun n → Bool
  | _, .exp => false
  | _, _ => true

def T : Theory Fun where
  E := E
  free := free
  heads := by
    intro e he
    rw [E, Set.mem_singleton_iff] at he
    subst he
    exact ⟨rfl, rfl⟩

/-! ## Constructors -/

def tt : Msg T := .app .tt ![]
def ff : Msg T := .app .ff ![]
def g : Msg T := .app .g ![]
def pk (k : Msg T) : Msg T := .app .pk ![k]
def hash (m : Msg T) : Msg T := .app .hash ![m]
def pair (a b : Msg T) : Msg T := .app .pair ![a, b]
def senc (m k : Msg T) : Msg T := .app .senc ![m, k]
def aenc (m p : Msg T) : Msg T := .app .aenc ![m, p]
def sign (m k : Msg T) : Msg T := .app .sign ![m, k]
def exp (b e : Msg T) : Msg T := .app .exp ![b, e]

/-- The equation (2.7) on messages. -/
theorem exp_exp_g (x y : Msg T) : exp (exp g x) y = exp (exp g y) x := by
  have h := T.realize_eq (Set.mem_singleton _) fun n => if n = 0 then x else y
  simp only [Msg.realize_func₂, Msg.realize_func₀, Term.realize_var] at h
  simpa [exp, g] using h

/-! ## Destructors

One branch per rewrite rule, then failure.
-/

open Classical

/-- `1th((x, y)) → x` -/
def fst (p : Msg T) : Option (Msg T) :=
  match p.view with
  | .app .pair a => some (a 0)
  | _ => none

/-- `2th((x, y)) → y` -/
def snd (p : Msg T) : Option (Msg T) :=
  match p.view with
  | .app .pair a => some (a 1)
  | _ => none

/-- `sdec(senc(x, y), y) → x` -/
noncomputable def sdec (c k : Msg T) : Option (Msg T) :=
  match c.view with
  | .app .senc a => if a 1 = k then some (a 0) else none
  | _ => none

/-- `adec(aenc(x, pk(y)), y) → x`, the rule (2.1). -/
noncomputable def adec (c k : Msg T) : Option (Msg T) :=
  match c.view with
  | .app .aenc a =>
    match (a 1).view with
    | .app .pk b => if b 0 = k then some (a 0) else none
    | _ => none
  | _ => none

/-- `check(sign(x, y), pk(y)) → x`, the rule (2.3). -/
noncomputable def check (s p : Msg T) : Option (Msg T) :=
  match s.view, p.view with
  | .app .sign a, .app .pk b => if a 1 = b 0 then some (a 0) else none
  | _, _ => none

/-- `getmess(sign(x, y)) → x`, the rule (2.4). -/
def getmess (s : Msg T) : Option (Msg T) :=
  match s.view with
  | .app .sign a => some (a 0)
  | _ => none

theorem sdec_senc (m k : Msg T) : sdec (senc m k) k = some m := by
  simp [sdec, senc]
  exact if_pos rfl

/-- Every symbol and destructor is public. -/
noncomputable instance : Pub T where
  pubFun _ := Set.univ
  dtors :=
    {⟨1, fun a => fst (a 0)⟩, ⟨1, fun a => snd (a 0)⟩, ⟨2, fun a => sdec (a 0) (a 1)⟩,
     ⟨2, fun a => adec (a 0) (a 1)⟩, ⟨2, fun a => check (a 0) (a 1)⟩,
     ⟨1, fun a => getmess (a 0)⟩}

end ProVerif.DH
