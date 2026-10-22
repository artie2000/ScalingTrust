/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.Specification.Syntax

/-!
# Patterns, as abbreviations

The manual's patterns in `in` and `let` (§3.1.4, §4.1.2, Appendix B), the write-up's
Definition "Patterns": a variable, the wildcard `_`, an equality test `=D`, a tuple of
patterns or a data constructor applied to patterns, the declared destructors that are its
projections given with it.  A pattern abbreviates into the fragment of
Definition "Source syntax", for processes and expressions alike (`Target`): the term
matched is bound to a variable, every test of the pattern is evaluated into a tuple, each
leaf of the pattern is bound to the projections reading it, left to right, and each test
leaf is compared with its test; a term, a test, a projection or a comparison that fails
takes the `else` branch, and the tests are evaluated whether or not the term failed, which
is the order of the manual's rules.  `Process.letPat`, `Process.inpPat` and `Expr.letPat`
are the abbreviations.  Binders are indices, so the abbreviation renames: `Expr.weaken`
and the renamings in `Target.letSeq` insert the binders it introduces.

A constructor declared `[data]` is public and its projections are declared destructors
with the rule `dataRule`, which `Model.IsData` says of a model.
-/

namespace ProVerif.Specification

open FirstOrder FirstOrder.Language ProVerif.TraceSemantics

variable {F G Ev : Sig} {n m : ℕ}

/-- The rule of the `i`-th projection of the data constructor `f`, `fᵢ(f(y₁, …, yₖ)) → yᵢ`,
the variables numbered by position (manual §4.1.2). -/
def dataRule {k : ℕ} (f : F k) (i : Fin k) : Rule (Sig.cons F Ev) 1 where
  args := ![.term (.func (.inl (.inl f)) fun j => .var j)]
  rhs := .term (.var i)
  vars := by simp [MayFail.vars, Term.varFinset]
  mvars := by simp [MayFail.mvars]

/-- `f` is a data constructor of the model with the projections `proj`: public, each
projection a public declared destructor with the one rule `dataRule f i`. -/
def Model.IsData (A : Model F G Ev) {k : ℕ} (f : F k) (proj : Fin k → G 1) : Prop :=
  f ∈ A.pubFun k ∧ ∀ i, proj i ∈ A.pubDtor 1 ∧ A.dtor (proj i) = [dataRule f i]

/-- A pattern under `n` binders: a variable, the wildcard `_`, an equality test `=D`, a tuple
of patterns, or a data constructor `f` applied to patterns, with the declared destructors
`proj i` that are its projections. -/
inductive Pat (F G Ev : Sig) (n : ℕ) : Type
  | var
  | wild
  | eq (D : Expr F G Ev n)
  | tuple {k : ℕ} (ps : Fin k → Pat F G Ev n)
  | data {k : ℕ} (f : F k) (proj : Fin k → G 1) (ps : Fin k → Pat F G Ev n)

namespace Pat

/-- The number of variables the pattern binds, left to right. -/
def vars : Pat F G Ev n → ℕ
  | .var => 1
  | .wild => 0
  | .eq _ => 0
  | .tuple (k := k) ps => ((List.finRange k).map fun i => (ps i).vars).sum
  | .data (k := k) _ _ ps => ((List.finRange k).map fun i => (ps i).vars).sum

/-- The tests of the pattern, the `D` of its `=D`, left to right. -/
def tests : Pat F G Ev n → List (Expr F G Ev n)
  | .var => []
  | .wild => []
  | .eq D => [D]
  | .tuple (k := k) ps => (List.finRange k).flatMap fun i => (ps i).tests
  | .data (k := k) _ _ ps => (List.finRange k).flatMap fun i => (ps i).tests

/-- The pattern with `f` applied to its tests. -/
def map (f : Expr F G Ev n → Expr F G Ev m) : Pat F G Ev n → Pat F G Ev m
  | .var => .var
  | .wild => .wild
  | .eq D => .eq (f D)
  | .tuple ps => .tuple fun i => (ps i).map f
  | .data g proj ps => .data g proj fun i => (ps i).map f

theorem vars_map (f : Expr F G Ev n → Expr F G Ev m) : ∀ p : Pat F G Ev n, (p.map f).vars = p.vars
  | .var => rfl
  | .wild => rfl
  | .eq _ => rfl
  | .tuple ps => by
    simp only [map, vars]
    congr 2
    funext i
    exact vars_map f (ps i)
  | .data _ _ ps => by
    simp only [map, vars]
    congr 2
    funext i
    exact vars_map f (ps i)

/-- A leaf of a pattern: a variable, the wildcard or a test. -/
inductive Leaf
  | var
  | wild
  | test

/-- The leaves of the pattern matched against `x`, left to right, each with the
projections reading it from `x`: the `i`-th component of a tuple through `ith`, that of a
data constructor through its `i`-th projection. -/
def leaves (x : Expr F G Ev n) : Pat F G Ev n → List (Expr F G Ev n × Leaf)
  | .var => [(x, .var)]
  | .wild => [(x, .wild)]
  | .eq _ => [(x, .test)]
  | .tuple (k := k) ps =>
    (List.finRange k).flatMap fun i => (ps i).leaves (.dtor (.inr (.proj k i)) ![x])
  | .data (k := k) _ proj ps =>
    (List.finRange k).flatMap fun i => (ps i).leaves (.dtor (.inl (proj i)) ![x])

end Pat

/-- `D` under one more binder, which it does not use. -/
def Expr.weaken (D : Expr F G Ev n) : Expr F G Ev (n + 1) :=
  D.subst fun i => .var (.inr i.castSucc)

/-- The variable at index `i`, as an expression. -/
def Expr.v (i : Fin n) : Expr F G Ev n := .term (.var (.inr i))

/-- What the abbreviation of a pattern needs of the construct it abbreviates into:
processes and expressions both have `let` with an `else`, `if` and substitution. -/
structure Target (F G Ev : Sig) where
  /-- Processes or expressions under `n` binders. -/
  T : ℕ → Type
  /-- `let x = D in P else Q`, binding the last variable. -/
  let_ {n : ℕ} : Expr F G Ev n → T (n + 1) → T n → T n
  /-- `if D then P else Q` -/
  ite {n : ℕ} : Expr F G Ev n → T n → T n → T n
  /-- Substitution for the bound variables. -/
  subst {n m : ℕ} : (Fin n → Tm F Ev m) → T n → T m

/-- Processes. -/
def Target.process : Target F G Ev := ⟨Process F G Ev, .let_, .ite, Process.subst⟩

/-- Expressions. -/
def Target.expr : Target F G Ev := ⟨Expr F G Ev, .let_, .ite, Expr.subst⟩

namespace Target

variable (t : Target F G Ev)

/-- `P` under one more binder, which it does not use. -/
def weaken (P : t.T n) : t.T (n + 1) := t.subst (fun i => .var (.inr i.castSucc)) P

/-- `let a₁ = t₁ in … let a_L = t_L in P else Q … else Q`: the `tᵢ`, at depth `m`, are
evaluated in order, each bound to the next variable, and a failure runs `Q`. -/
def letSeq : {m : ℕ} → (L : ℕ) → (Fin L → Expr F G Ev m) → t.T (m + L) → t.T m → t.T m
  | _, 0, _, P, _ => P
  | m, L + 1, ts, P, Q =>
    t.let_ (ts 0)
      (letSeq L (fun i => (ts i.succ).weaken)
        (t.subst (fun i => .var (.inr (Fin.cast (by omega) i))) P) (t.weaken Q)) Q

/-- `if a₁ = j₁th_k(z) then … if aᵣ = jᵣth_k(z) then P else Q … else Q`: each variable `aᵢ`
is compared with the `jᵢ`-th component of the `k`-tuple `z`. -/
def ifSeq (k : ℕ) (z : Fin m) : List (Fin m × Fin k) → t.T m → t.T m → t.T m
  | [], P, _ => P
  | (a, j) :: rest, P, Q =>
    t.ite (.dtor (.inr .equal) ![.v a, .dtor (.inr (.proj k j)) ![.v z] ]) (ifSeq k z rest P Q) Q

/-- `let pat = D in P else Q`, the write-up's Definition "Patterns": `x` is bound to `D`,
`z` to the tuple of the pattern's tests, each leaf of the pattern to the projections reading
it from `x`, left to right, and each test leaf is compared with its test; a `D` that fails,
a test that fails, a projection that fails or a comparison that fails runs `Q`, the tests
being evaluated whether or not `D` fails, as the manual's rules have it (Appendix B).
`P` is under the pattern's variables, which the abbreviation renames to the variables of
their leaves. -/
def letPat (p : Pat F G Ev n) (D : Expr F G Ev n) (P : t.T (n + p.vars)) (Q : t.T n) : t.T n :=
  let k := p.tests.length
  let tests₀ : Expr F G Ev n := .ctor (.inr (.tuple k)) fun j => p.tests.get j
  let tests₁ : Expr F G Ev (n + 1) := .ctor (.inr (.tuple k)) fun j => (p.tests.get j).weaken
  let ls := ((p.map Expr.weaken).map Expr.weaken).leaves (.v ⟨n, by omega⟩)
  let L := ls.length
  let pos : Fin L → Fin (n + 2 + L) := Fin.natAdd (n + 2)
  let z : Fin (n + 2 + L) := ⟨n + 1, by omega⟩
  let testLeaves : List (Fin (n + 2 + L) × Fin k) :=
    ((List.finRange L).filter fun i => (ls.get i).2 matches .test).zipIdx.filterMap
      fun (i, j) => if h : j < k then some (pos i, ⟨j, h⟩) else none
  let varPos : List (Fin (n + 2 + L)) :=
    ((List.finRange L).filter fun i => (ls.get i).2 matches .var).map pos
  let P' : t.T (n + 2 + L) := t.subst (fun i => .var (.inr
    (if h : i.val < n then ⟨i.val, by omega⟩ else varPos.getD (i.val - n) ⟨n, by omega⟩))) P
  let Q₂ : t.T (n + 2) := t.weaken (t.weaken Q)
  let Q₃ : t.T (n + 2 + L) := t.subst (fun i => .var (.inr (Fin.castAdd L i))) Q₂
  let body : t.T (n + 2) := t.letSeq L (fun i => (ls.get i).1) (t.ifSeq k z testLeaves P' Q₃) Q₂
  t.let_ D (t.let_ tests₁ body (t.weaken Q)) (t.let_ tests₀ (t.weaken Q) Q)

end Target

/-- `let pat = D in P else Q`. -/
def Process.letPat (p : Pat F G Ev n) (D : Expr F G Ev n) (P : Process F G Ev (n + p.vars))
    (Q : Process F G Ev n) : Process F G Ev n :=
  Target.process.letPat p D P Q

/-- `in(N, pat); P`: `in(N, x); let pat = x in P else 0`, the communication binding the
variable and the pattern matched then, as the manual's rules have it (Figure B.2). -/
def Process.inpPat (N : Expr F G Ev n) (p : Pat F G Ev n) (P : Process F G Ev (n + p.vars)) :
    Process F G Ev n :=
  .inp N (Process.letPat (p.map Expr.weaken) (.v (Fin.last n))
    (P.subst fun i => .var (.inr (Fin.cast (by rw [Pat.vars_map])
      (if h : i.val < n then ⟨i.val, by omega⟩ else ⟨i.val + 1, by have := i.isLt; omega⟩))))
    .nil)

/-- `let pat = D in D₁ else D₂`, an omitted `else` being `fail`. -/
def Expr.letPat (p : Pat F G Ev n) (D : Expr F G Ev n) (D₁ : Expr F G Ev (n + p.vars))
    (D₂ : Expr F G Ev n) : Expr F G Ev n :=
  Target.expr.letPat p D D₁ D₂

end ProVerif.Specification
