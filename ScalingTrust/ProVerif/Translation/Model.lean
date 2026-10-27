/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/

/-!
# ProVerif models

A model as the translation reads it, types erased: the free names, constructors,
events, equations and destructors a ProVerif file declares, its function and
process macros, its queries and its main process, with the printing of its terms
and queries for the docstrings of the translation and the renaming of its
identifiers.  `Parser.parse` reads a model off the text of a file.
-/

namespace ProVerif.Translation

mutual

/-- A term: an identifier, which is a variable, a free name, a constant or `true` or
`false`; an application; a tuple `(M₁, …, Mₙ)`, never of one term; `fail`, in rewrite
rules; or one of the enriched terms of the manual's §4.1.4, which evaluate with effects: a
restriction, a conditional on a boolean term, a term evaluation with a pattern and an
event.  An absent `else` is `fail` (Appendix B).  The comparisons `M = N` and `M <> N`
and the connectives `M && N`, `M || N` and `not(M)` are applications of `"="`, `"<>"`,
`"&&"`, `"||"` and `"not"`, which are not identifiers. -/
inductive Term where
  | ident (x : String)
  | app (f : String) (args : Array Term)
  | tuple (args : Array Term)
  | fail
  | new (x : String) (M : Term)
  | ite (c : Term) (N : Term) (N' : Option Term)
  | «let» (p : Pat) (d : Term) (N : Term) (N' : Option Term)
  | event (e : String) (args : Array Term) (M : Term)
  deriving Inhabited, Repr

/-- A pattern of `in` and `let` (manual §4.1.3): a variable, an equality test `=M`, a
tuple of patterns, or a data constructor applied to patterns. -/
inductive Pat where
  | var (x : String)
  | eq (M : Term)
  | tuple (ps : Array Pat)
  | app (f : String) (ps : Array Pat)
  deriving Inhabited, Repr

end

/-- `fun f(t₁, …, tₙ) : t` or `const c : t`, with its options. -/
structure Ctor where
  name : String
  arity : Nat
  pub : Bool
  /-- `[typeConverter]`: the identity, as under ProVerif's default `ignoreTypes = true`. -/
  converter : Bool
  /-- `[data]`: patterns may match on it, and its projections are destructors, public as the
  manual requires it to be (§4.1.2). -/
  data : Bool
  deriving Repr

/-- A rewrite rule `forall x₁ : t₁ [or fail], …; g(p₁, …, pₙ) = r`: its variables,
each marked if it may fail, its patterns and its right-hand side. -/
structure Rule where
  vars : Array (String × Bool)
  lhs : Array Term
  rhs : Term
  deriving Inhabited, Repr

/-- A destructor: `reduc` with rules separated by `;`, a set the manual requires to be
deterministic (§3.1.1), which the translation checks; or `fun … reduc` with rules
separated by `otherwise`, a sequence in which the first rule that applies decides
(§4.2.1).  Either way the rules are compiled in order, which for a deterministic set
chooses a rule that applies. -/
structure Dtor where
  name : String
  arity : Nat
  pub : Bool
  rules : Array Rule
  /-- Declared with `;`: the rules are a set. -/
  plain : Bool
  deriving Repr

/-- `equation forall x₁ : t₁, …; l = r` -/
structure Equation where
  vars : Array String
  lhs : Term
  rhs : Term
  deriving Repr

/-- A process of the fragment.  An `if` tests a boolean term; `in` and `let` bind a
pattern; an absent `else` and an absent `in` are `0`.  The manual's sugar is read as what
it abbreviates: `yield` as `0`, `foreach i <= N do P` and `! i <= N P` as `!P`,
`x <-R t; P` as `new x : t; P` and `x <- D; P` as `let x = D in P` (§6.8).  `insert` and
`get` on tables (§4.1.5), the phase prefix `phase n; P` (§4.1.6) and the synchronisation
`sync n [tag]; P` (§4.1.7) are compiled out before the translation, by `Compile.lean`. -/
inductive Proc where
  | nil
  | call (p : String) (args : Array Term)
  | par (P Q : Proc)
  | repl (P : Proc)
  | new (x : String) (P : Proc)
  | ite (c : Term) (P Q : Proc)
  | inp (c : Term) (p : Pat) (P : Proc)
  | out (c m : Term) (P : Proc)
  | «let» (p : Pat) (d : Term) (P Q : Proc)
  | event (e : String) (args : Array Term) (P : Proc)
  /-- `insert d(M₁, …, Mₙ); P` -/
  | insert (d : String) (args : Array Term) (P : Proc)
  /-- `get d(T₁, …, Tₙ) suchthat M in P else Q` -/
  | get (d : String) (ps : Array Pat) (cond : Option Term) (P Q : Proc)
  /-- `phase n; P` -/
  | phase (n : Nat) (P : Proc)
  /-- `sync n [tag]; P`, the tag when written -/
  | sync (n : Nat) (tag : Option String) (P : Proc)
  deriving Inhabited, Repr

/-- A fact of a query (manual, Figure A.5): the attacker knows `M`, an event, a message on
a channel or an element of a table, each but the event qualified by a phase or not; an
equality `M = N` or a disequality `M <> N`, after the arrow only; and, once phases are
compiled out, a fact before the first occurrence of an event, `F before e(M₁, …, Mₙ)`,
which no ProVerif query writes.  An event carries a phase only as the element of a table
once tables are compiled out. -/
inductive Fact where
  | attacker (m : Term) (phase : Option Nat)
  | event (e : String) (args : Array Term) (phase : Option Nat)
  | mess (c m : Term) (phase : Option Nat)
  | table (d : String) (args : Array Term) (phase : Option Nat)
  | eq (l r : Term)
  | ne (l r : Term)
  | before (f : Fact) (e : String) (args : Array Term)
  deriving Repr, Inhabited

/-- The hypothesis of a query, after `==>` (Figure A.5): a fact, injective or not; a
conjunction, `&&` binding tighter than `||`; a disjunction; `false`; or a nested
correspondence `F ==> H`. -/
inductive Hyp where
  | fact (inj : Bool) (f : Fact)
  | and (h₁ h₂ : Hyp)
  | or (h₁ h₂ : Hyp)
  | false
  | corr (inj : Bool) (f : Fact) (h : Hyp)
  deriving Repr, Inhabited

/-- `query x₁ : t₁, …; F₁ && … && Fₙ ==> H`, or `query x₁ : t₁, …; F₁ && … && Fₙ`, which
asks that the facts never hold together, as `==> false` does; the facts before the arrow
are each marked if injective.  A reference `new n` to a bound name in a fact (manual §6.4)
is a variable of the query, listed in `bound` with its restriction, which `Compile.lean`
ties to the names created there; the `let x = M in` bindings of a query are substituted
by the parser.  `source` is the query as written, for the docstring of its translation,
which the compilations of `Compile.lean` keep. -/
structure Query where
  vars : Array String
  premise : Array (Bool × Fact)
  concl : Hyp
  source : String
  bound : Array (String × String) := #[]
  deriving Repr, Inhabited

/-- `let p(x₁ : t₁ [or fail], …) = P.`, the parameters each marked if they may fail (manual
§4.2.4). -/
structure Macro where
  name : String
  params : Array (String × Bool)
  body : Proc
  deriving Repr

/-- `letfun f(x₁ : t₁ [or fail], …) = M.`, a function macro, the parameters each marked if
they may fail (manual §4.2.3). -/
structure Fn where
  name : String
  params : Array (String × Bool)
  body : Term
  deriving Repr

/-- A model: its declarations, in order, and its main process. -/
structure Model where
  /-- The free names, each marked if public. -/
  frees : Array (String × Bool) := #[]
  ctors : Array Ctor := #[]
  /-- The events, with their arities. -/
  events : Array (String × Nat) := #[]
  /-- The tables, with their arities; none once compiled to private channels. -/
  tables : Array (String × Nat) := #[]
  equations : Array Equation := #[]
  dtors : Array Dtor := #[]
  /-- The function macros, in order: each may call only the earlier ones. -/
  fns : Array Fn := #[]
  macros : Array Macro := #[]
  queries : Array Query := #[]
  /-- The bound names of `query secret x` declarations; none once compiled to queries. -/
  secrets : Array String := #[]
  main : Proc := .nil
  deriving Repr

/-- The digits of `n` as subscripts: `12` is `₁₂`. -/
def subscript (n : Nat) : String :=
  String.ofList <| (toString n).toList.map fun c => Char.ofNat (c.toNat - '0'.toNat + '₀'.toNat)

/-! ## Printing, for the docstrings of the translation -/

/-- An application, `f(a, b)`, or `f` when there are no arguments. -/
def printApp (f : String) (args : Array String) : String :=
  if args.isEmpty then f else s!"{f}({", ".intercalate args.toList})"

/-- Whether a term is an enriched one, printed in parentheses as an argument. -/
def Term.enriched : Term → Bool
  | .new .. | .ite .. | .let .. | .event .. => true
  | _ => false

/-- Whether a term is an infix comparison or connective, printed in parentheses as an
argument. -/
def Term.infix : Term → Bool
  | .app "=" _ | .app "<>" _ | .app "&&" _ | .app "||" _ => true
  | _ => false

mutual

partial def Term.print : Term → String
  | .ident x => x
  | .app "=" #[l, r] => s!"{l.arg} = {r.arg}"
  | .app "<>" #[l, r] => s!"{l.arg} <> {r.arg}"
  | .app "&&" #[l, r] => s!"{l.arg} && {r.arg}"
  | .app "||" #[l, r] => s!"{l.arg} || {r.arg}"
  | .app "new" #[.ident n] => s!"new {n}"
  | .app f args => s!"{f}({", ".intercalate (args.map Term.arg).toList})"
  | .tuple args => s!"({", ".intercalate (args.map Term.print).toList})"
  | .fail => "fail"
  | .new x M => s!"new {x}; {M.print}"
  | .ite c N N' => s!"if {c.print} then {N.print}{Term.orElse N'}"
  | .let p d N N' => s!"let {p.print} = {d.print} in {N.print}{Term.orElse N'}"
  | .event e args M => s!"event {printApp e (args.map Term.arg)}; {M.print}"

/-- A term as an argument or an operand. -/
partial def Term.arg (t : Term) : String :=
  if t.enriched || t.infix then s!"({t.print})" else t.print

partial def Term.orElse : Option Term → String
  | none => ""
  | some N' => s!" else {N'.print}"

partial def Pat.print : Pat → String
  | .var x => x
  | .eq M => s!"={M.arg}"
  | .tuple ps => s!"({", ".intercalate (ps.map Pat.print).toList})"
  | .app f ps => printApp f (ps.map Pat.print)

end

/-- A parameter, `x or fail` when it may fail. -/
def printParam (p : String × Bool) : String := if p.2 then s!"{p.1} or fail" else p.1

def Fn.print (f : Fn) : String :=
  s!"{printApp f.name (f.params.map printParam)} = {f.body.print}"

/-- A fact as ProVerif writes it, an injective event with `inj-event`. -/
partial def Fact.print (inj : Bool := false) : Fact → String
  | .attacker m ph => s!"attacker({m.print}){phase ph}"
  | .event e args ph => s!"{if inj then "inj-event" else "event"}({printApp e (args.map Term.print)}){phase ph}"
  | .mess c m ph => s!"mess({c.print}, {m.print}){phase ph}"
  | .table d args ph => s!"table({printApp d (args.map Term.print)}){phase ph}"
  | .eq l r => s!"{l.arg} = {r.arg}"
  | .ne l r => s!"{l.arg} <> {r.arg}"
  | .before f e args => s!"{f.print} before {printApp e (args.map Term.print)}"
where
  phase : Option Nat → String
    | none => ""
    | some n => s!" phase {n}"

/-- A hypothesis, with the parentheses the precedences need. -/
partial def Hyp.print : Hyp → String
  | .fact inj f => f.print inj
  | .and h₁ h₂ => s!"{operand Bool.true h₁} && {operand Bool.true h₂}"
  | .or h₁ h₂ => s!"{operand Bool.false h₁} || {operand Bool.false h₂}"
  | .false => "false"
  | .corr inj f h => s!"({f.print inj} ==> {h.print})"
where
  /-- An operand of `&&`, when `conj`, or of `||`: a disjunction, or a conjunction under
  `&&`, in parentheses. -/
  operand (conj : Bool) (h : Hyp) : String :=
    match h with
    | .or .. => s!"({h.print})"
    | .and .. => if conj then h.print else s!"({h.print})"
    | _ => h.print

/-- Whether some fact of the hypothesis is injective. -/
def Hyp.hasInj : Hyp → Bool
  | .fact inj _ => inj
  | .and h₁ h₂ | .or h₁ h₂ => h₁.hasInj || h₂.hasInj
  | .false => Bool.false
  | .corr inj _ h => inj || h.hasInj

/-- A rule of the destructor `g`, as `g(p₁, …, pₙ) → r`. -/
def Rule.print (g : String) (r : Rule) : String :=
  s!"{(Term.app g r.lhs).print} → {r.rhs.print}"

/-! ## The identifiers of a model, and renaming them -/

mutual

/-- Every identifier of a term: symbols, operators and variables, bound or free. -/
partial def Term.names : Term → Array String
  | .ident x => #[x]
  | .app f args => #[f] ++ args.flatMap Term.names
  | .tuple args => args.flatMap Term.names
  | .fail => #[]
  | .new x M => #[x] ++ M.names
  | .ite c N N' => c.names ++ N.names ++ (N'.map Term.names).getD #[]
  | .let p d N N' => p.names ++ d.names ++ N.names ++ (N'.map Term.names).getD #[]
  | .event e args M => #[e] ++ args.flatMap Term.names ++ M.names

partial def Pat.names : Pat → Array String
  | .var x => #[x]
  | .eq M => M.names
  | .tuple ps => ps.flatMap Pat.names
  | .app f ps => #[f] ++ ps.flatMap Pat.names

end

/-- The variables a pattern binds, in order. -/
partial def Pat.vars : Pat → Array String
  | .var x => #[x]
  | .eq _ => #[]
  | .tuple ps | .app _ ps => ps.flatMap vars

/-- The terms of the equality tests of a pattern. -/
partial def Pat.tests : Pat → Array Term
  | .var _ => #[]
  | .eq M => #[M]
  | .tuple ps | .app _ ps => ps.flatMap tests

partial def Proc.names : Proc → Array String
  | .nil => #[]
  | .call p args => #[p] ++ args.flatMap Term.names
  | .par P Q => P.names ++ Q.names
  | .repl P => P.names
  | .new x P => #[x] ++ P.names
  | .ite c P Q => c.names ++ P.names ++ Q.names
  | .inp c p P => c.names ++ p.names ++ P.names
  | .out c m P => c.names ++ m.names ++ P.names
  | .let p d P Q => p.names ++ d.names ++ P.names ++ Q.names
  | .event e args P => #[e] ++ args.flatMap Term.names ++ P.names
  | .insert d args P => #[d] ++ args.flatMap Term.names ++ P.names
  | .get d ps cond P Q =>
    #[d] ++ ps.flatMap Pat.names ++ (cond.map Term.names).getD #[] ++ P.names ++ Q.names
  | .phase _ P | .sync _ _ P => P.names

partial def Fact.names : Fact → Array String
  | .attacker m _ => m.names
  | .event e args _ => #[e] ++ args.flatMap Term.names
  | .mess c m _ => c.names ++ m.names
  | .table d args _ => #[d] ++ args.flatMap Term.names
  | .eq l r | .ne l r => l.names ++ r.names
  | .before f e args => f.names ++ #[e] ++ args.flatMap Term.names

partial def Hyp.names : Hyp → Array String
  | .fact _ f => f.names
  | .and h₁ h₂ | .or h₁ h₂ => h₁.names ++ h₂.names
  | .false => #[]
  | .corr _ f h => f.names ++ h.names

def Query.names (q : Query) : Array String :=
  q.vars ++ q.premise.flatMap (·.2.names) ++ q.concl.names

def Rule.names (r : Rule) : Array String :=
  r.vars.map (·.1) ++ r.lhs.flatMap Term.names ++ r.rhs.names

/-- Every identifier of a model. -/
def Model.names (m : Model) : Array String :=
  m.frees.map (·.1) ++ m.ctors.map (·.name) ++ m.events.map (·.1) ++ m.tables.map (·.1)
    ++ m.equations.flatMap (fun e => e.vars ++ e.lhs.names ++ e.rhs.names)
    ++ m.dtors.flatMap (fun d => #[d.name] ++ d.rules.flatMap Rule.names)
    ++ m.fns.flatMap (fun f => #[f.name] ++ f.params.map (·.1) ++ f.body.names)
    ++ m.macros.flatMap (fun p => #[p.name] ++ p.params.map (·.1) ++ p.body.names)
    ++ m.queries.flatMap Query.names ++ m.secrets
    ++ m.main.names

/-- `t` with the term `M` for the variable `x`, in a term without binders, as in a rule or
an equation: the manual's `let x = M in …` there. -/
partial def Term.substVar (x : String) (M : Term) : Term → Term
  | .ident y => if y == x then M else .ident y
  | .app f args => .app f (args.map (substVar x M))
  | .tuple args => .tuple (args.map (substVar x M))
  | t => t

/-- `t` under the bindings `let x₁ = M₁ in … let xₖ = Mₖ in`, the later ones substituted
first since each may use the earlier ones. -/
def Term.withBindings (binds : Array (String × Term)) (t : Term) : Term :=
  binds.foldr (fun (x, m) t => Term.substVar x m t) t

partial def Fact.substVar (x : String) (M : Term) : Fact → Fact
  | .attacker m ph => .attacker (Term.substVar x M m) ph
  | .event e args ph => .event e (args.map (Term.substVar x M)) ph
  | .mess c m ph => .mess (Term.substVar x M c) (Term.substVar x M m) ph
  | .table d args ph => .table d (args.map (Term.substVar x M)) ph
  | .eq l r => .eq (Term.substVar x M l) (Term.substVar x M r)
  | .ne l r => .ne (Term.substVar x M l) (Term.substVar x M r)
  | .before f e args => .before (Fact.substVar x M f) e (args.map (Term.substVar x M))

partial def Hyp.substVar (x : String) (M : Term) : Hyp → Hyp
  | .fact inj f => .fact inj (Fact.substVar x M f)
  | .and h₁ h₂ => .and (Hyp.substVar x M h₁) (Hyp.substVar x M h₂)
  | .or h₁ h₂ => .or (Hyp.substVar x M h₁) (Hyp.substVar x M h₂)
  | .false => .false
  | .corr inj f h => .corr inj (Fact.substVar x M f) (Hyp.substVar x M h)

/-- A query as ProVerif writes it, a variable standing for a bound name, in `bound`,
printed as its reference `new n`. -/
def Query.print (vars : Array String) (premise : Array (Bool × Fact)) (concl : Hyp)
    (bound : Array (String × String) := #[]) : String :=
  let shown := vars.filter fun x => !bound.any (·.1 == x)
  let vs := if shown.isEmpty then "" else s!"{", ".intercalate shown.toList}; "
  let back (f : Fact) : Fact :=
    bound.foldl (fun f (v, n) => Fact.substVar v (.app "new" #[.ident n]) f) f
  let fs := " && ".intercalate (premise.map fun (inj, f) => (back f).print inj).toList
  match bound.foldl (fun h (v, n) => Hyp.substVar v (.app "new" #[.ident n]) h) concl with
  | .false => s!"query {vs}{fs}"
  | h => s!"query {vs}{fs} ==> {h.print}"

mutual

partial def Term.rename (σ : String → String) : Term → Term
  | .ident x => .ident (σ x)
  | .app f args => .app (σ f) (args.map (Term.rename σ))
  | .tuple args => .tuple (args.map (Term.rename σ))
  | .fail => .fail
  | .new x M => .new (σ x) (M.rename σ)
  | .ite c N N' => .ite (c.rename σ) (N.rename σ) (N'.map (Term.rename σ))
  | .let p d N N' => .let (p.rename σ) (d.rename σ) (N.rename σ) (N'.map (Term.rename σ))
  | .event e args M => .event (σ e) (args.map (Term.rename σ)) (M.rename σ)

partial def Pat.rename (σ : String → String) : Pat → Pat
  | .var x => .var (σ x)
  | .eq M => .eq (M.rename σ)
  | .tuple ps => .tuple (ps.map (Pat.rename σ))
  | .app f ps => .app (σ f) (ps.map (Pat.rename σ))

end

partial def Proc.rename (σ : String → String) : Proc → Proc
  | .nil => .nil
  | .call p args => .call (σ p) (args.map (Term.rename σ))
  | .par P Q => .par (P.rename σ) (Q.rename σ)
  | .repl P => .repl (P.rename σ)
  | .new x P => .new (σ x) (P.rename σ)
  | .ite c P Q => .ite (c.rename σ) (P.rename σ) (Q.rename σ)
  | .inp c p P => .inp (c.rename σ) (p.rename σ) (P.rename σ)
  | .out c m P => .out (c.rename σ) (m.rename σ) (P.rename σ)
  | .let p d P Q => .let (p.rename σ) (d.rename σ) (P.rename σ) (Q.rename σ)
  | .event e args P => .event (σ e) (args.map (Term.rename σ)) (P.rename σ)
  | .insert d args P => .insert (σ d) (args.map (Term.rename σ)) (P.rename σ)
  | .get d ps cond P Q =>
    .get (σ d) (ps.map (Pat.rename σ)) (cond.map (Term.rename σ)) (P.rename σ) (Q.rename σ)
  | .phase n P => .phase n (P.rename σ)
  | .sync n tag P => .sync n tag (P.rename σ)

partial def Fact.rename (σ : String → String) : Fact → Fact
  | .attacker m ph => .attacker (m.rename σ) ph
  | .event e args ph => .event (σ e) (args.map (Term.rename σ)) ph
  | .mess c m ph => .mess (c.rename σ) (m.rename σ) ph
  | .table d args ph => .table (σ d) (args.map (Term.rename σ)) ph
  | .eq l r => .eq (l.rename σ) (r.rename σ)
  | .ne l r => .ne (l.rename σ) (r.rename σ)
  | .before f e args => .before (f.rename σ) (σ e) (args.map (Term.rename σ))

partial def Hyp.rename (σ : String → String) : Hyp → Hyp
  | .fact inj f => .fact inj (f.rename σ)
  | .and h₁ h₂ => .and (h₁.rename σ) (h₂.rename σ)
  | .or h₁ h₂ => .or (h₁.rename σ) (h₂.rename σ)
  | .false => .false
  | .corr inj f h => .corr inj (f.rename σ) (h.rename σ)

def Query.rename (σ : String → String) (q : Query) : Query where
  vars := q.vars.map σ
  premise := q.premise.map fun (inj, f) => (inj, f.rename σ)
  concl := q.concl.rename σ
  source := q.source
  bound := q.bound.map fun (v, n) => (σ v, σ n)

def Rule.rename (σ : String → String) (r : Rule) : Rule where
  vars := r.vars.map fun (x, b) => (σ x, b)
  lhs := r.lhs.map (Term.rename σ)
  rhs := r.rhs.rename σ

/-- `m` with `σ` applied to every identifier. -/
def Model.rename (σ : String → String) (m : Model) : Model where
  frees := m.frees.map fun (a, pub) => (σ a, pub)
  ctors := m.ctors.map fun c => { c with name := σ c.name }
  events := m.events.map fun (e, n) => (σ e, n)
  tables := m.tables.map fun (d, n) => (σ d, n)
  equations := m.equations.map fun e =>
    { vars := e.vars.map σ, lhs := e.lhs.rename σ, rhs := e.rhs.rename σ }
  dtors := m.dtors.map fun d => { d with name := σ d.name, rules := d.rules.map (Rule.rename σ) }
  fns := m.fns.map fun f =>
    { name := σ f.name, params := f.params.map fun (x, b) => (σ x, b), body := f.body.rename σ }
  macros := m.macros.map fun p =>
    { name := σ p.name, params := p.params.map fun (x, b) => (σ x, b), body := p.body.rename σ }
  queries := m.queries.map (Query.rename σ)
  secrets := m.secrets.map σ
  main := m.main.rename σ

end ProVerif.Translation
