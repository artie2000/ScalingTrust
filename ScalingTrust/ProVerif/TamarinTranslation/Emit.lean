/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.Translation.Emit
import ScalingTrust.ProVerif.TamarinTranslation.Parser

/-!
# Emitting the translation

The recipe of `README.md`, from a `Model` to Lean source over
`ProVerif.TamarinTranslation.Rewriting`.  The algebra of a model, its functions, its
equations and the destructors its equations define, is the algebra of a ProVerif model
whose events are the facts, so its signature, its theory, its destructors and its
attacker are emitted by the ProVerif translator, `ProVerif.Translation.Emit`, run on that
model (`pv`); the names, the rules, the restrictions and the lemmas are emitted here.
Each declaration of the output is built as Lean syntax by quotation and printed by
Lean's pretty printer; `emitFile` assembles them, and `translate` runs the whole
translation on the text of a model.

The names of the model are kept: a function, a fact, a rule, a restriction and a lemma
become Lean definitions of the same name, and a variable a binder of the same name,
prefixed with `_` when nothing uses it.  The binders the translation introduces carry
subscripts, `s₀`, `t₀`, `v₀`, which no Tamarin identifier has, and an identifier of the
model that is a name the translation uses unqualified, `reserved`, is first renamed with
primes, `Model.safe`.
-/

namespace ProVerif.TamarinTranslation

open Lean PrettyPrinter
open ProVerif.Translation (ident sub num dot)

/-- What a name of the model denotes.  A fact, a rule, a restriction and a lemma are
definitions under `Fact`, `Rule`, `Restriction` and `Lemma`, since a rule and a fact may
share a name. -/
inductive Sym where
  | ctor (arity : Nat)
  | dtor (arity : Nat)
  | fact (arity : Nat) (persistent : Bool)
  | bool (b : Bool)

/-- The model and its symbol table. -/
structure Ctx where
  model : Model
  /-- The context of the ProVerif translator on the algebra of the model. -/
  pv : ProVerif.Translation.Ctx
  syms : Std.HashMap String Sym
  /-- The equations of the theory, as declared, for the docstrings. -/
  theoryEqs : Array Equation
  /-- Whether the rules use `fst` or `snd`. -/
  projections : Bool

/-- The state of emission: that of the ProVerif translator, and the destructor
applications of the rule being emitted, each bound to a name `v₀`, `v₁`, …, by the printed
application. -/
structure St where
  pv : ProVerif.Translation.St := {}
  computed : Array (Ident × Lean.Term) := #[]
  memo : Std.HashMap String Ident := {}
  deriving Inhabited

/-- Emission: the context, the state, and `CoreM` for quotations and the pretty printer. -/
abbrev EmitM := ReaderT Ctx (StateT St CoreM)

/-- Run an action of the ProVerif translator on the algebra of the model. -/
def pv {α : Type} (act : ProVerif.Translation.EmitM α) : EmitM α := fun ctx st => do
  let (a, pvSt) ← (act ctx.pv).run st.pv
  return (a, { st with pv := pvSt })

/-- A fresh binder `base₀`, `base₁`, … -/
def fresh (base : String) : EmitM Ident := pv (ProVerif.Translation.fresh base)

def pp (c : Command) : EmitM String := pv (ProVerif.Translation.pp c)

def sym? (x : String) : EmitM (Option Sym) := return (← read).syms[x]?

def app (f : Lean.Term) (args : Array Lean.Term) : EmitM Lean.Term :=
  if args.isEmpty then pure f else `($f $args*)

/-- The names the translation uses unqualified, which a definition or a binder of the
model would shadow: those of the ProVerif translator, whose output this one contains, and
its own. -/
def reserved : List String :=
  ProVerif.Translation.reserved ++
  ["const", "Step", "Rules", "Config", "Run", "ActionAt", "KnowsAt", "tupleOf", "nonce",
   "pubName", "channel", "rules", "Fact", "Rule", "Restriction", "Restrictions", "Lemma", "fst",
   "snd", "Trace", "List", "String", "Multiset", "Prod", "Names", "Enemy", "Attacks"]

/-- The definition of the fact, rule, restriction or lemma `x` under the namespace `ns`. -/
def qualified (ns x : String) : Ident := mkIdent (Name.mkStr (.mkSimple ns) x)

/-- `m` with each of its identifiers in `reserved` renamed by appending primes until the
name is neither reserved nor another identifier of the model, and the renamings, new name
to old. -/
def Model.safe (m : Model) : Model × Std.HashMap String String := Id.run do
  let names := m.names
  let mut used : Std.HashSet String := Std.HashSet.ofList names.toList
  let mut σ : Std.HashMap String String := {}
  let mut renamed : Std.HashMap String String := {}
  for x in names do
    if reserved.contains x && !σ.contains x then
      let mut y := x ++ "'"
      while reserved.contains y || used.contains y do
        y := y ++ "'"
      σ := σ.insert x y
      renamed := renamed.insert y x
      used := used.insert y
  if σ.isEmpty then return (m, renamed)
  return (m.rename fun x => σ.getD x x, renamed)

/-! ## Builtins -/

/-- The functions and the equations of a builtin.  The pairs are always there, as the
tuples of the trace semantics; `diffie-hellman` is read as the exponentiation `exp` with
the one equation `(x^y)^z = (x^z)^y`, without the inverses and the multiplication of
Tamarin's theory. -/
def builtin (name : String) : Except String (Array Function × Array Equation) :=
  let v (x : String) : Term := .var x .msg
  let f (name : String) (args : Array Term) : Term := .app name args
  let fn (name : String) (arity : Nat) : Function := { name, arity, pub := true }
  let eq (lhs rhs : Term) : Equation := { lhs, rhs }
  match name with
  | "hashing" => pure (#[fn "h" 1], #[])
  | "symmetric-encryption" =>
    pure (#[fn "senc" 2, fn "sdec" 2], #[eq (f "sdec" #[f "senc" #[v "m", v "k"], v "k"]) (v "m")])
  | "asymmetric-encryption" =>
    pure (#[fn "aenc" 2, fn "adec" 2, fn "pk" 1],
      #[eq (f "adec" #[f "aenc" #[v "m", f "pk" #[v "sk"]], v "sk"]) (v "m")])
  | "signing" =>
    pure (#[fn "sign" 2, fn "verify" 3, fn "pk" 1, fn "true" 0],
      #[eq (f "verify" #[f "sign" #[v "m", v "sk"], v "m", f "pk" #[v "sk"]]) (v "true")])
  | "revealing-signing" =>
    pure (#[fn "revealSign" 2, fn "revealVerify" 3, fn "getMessage" 1, fn "pk" 1, fn "true" 0],
      #[eq (f "revealVerify" #[f "revealSign" #[v "m", v "sk"], v "m", f "pk" #[v "sk"]]) (v "true"),
        eq (f "getMessage" #[f "revealSign" #[v "m", v "sk"]]) (v "m")])
  | "diffie-hellman" =>
    pure (#[fn "exp" 2],
      #[eq (f "^" #[f "^" #[v "x", v "y"], v "z"]) (f "^" #[f "^" #[v "x", v "z"], v "y"])])
  | _ => throw s!"the builtin `{name}` is not translated"

/-- `m` with the functions and equations of its builtins, a function two builtins declare
counted once; `true` and `false`, declared or not, are the booleans and get no function. -/
def Model.withBuiltins (m : Model) : Except String Model := do
  let mut fns : Array Function := #[]
  let mut eqs : Array Equation := #[]
  for b in m.builtins do
    let (bf, be) ← builtin b
    for f in bf do
      match fns.find? (·.name == f.name) with
      | some g => unless g.arity == f.arity do throw s!"`{f.name}` is declared with two arities"
      | none => fns := fns.push f
    eqs := eqs ++ be
  for f in m.functions do
    if let some g := fns.find? (·.name == f.name) then
      unless g.arity == f.arity do throw s!"`{f.name}` is declared with two arities"
    else fns := fns.push f
  let bools := ["true", "false"]
  for f in fns do
    if bools.contains f.name && f.arity != 0 then throw s!"`{f.name}` is not nullary"
  return { m with functions := fns.filter (!bools.contains ·.name), equations := eqs ++ m.equations }

/-! ## The algebra, as a ProVerif model -/

/-- The symbol at the root of a term, `exp` for `^`. -/
def Term.root : Term → Option String
  | .app "^" _ => some "exp"
  | .app f _ => some f
  | _ => none

/-- The variables of a term: its bare identifiers that are not nullary functions. -/
partial def Term.vars (nullary : String → Bool) : Term → Array String
  | .var x _ => if nullary x then #[] else #[x]
  | .const _ => #[]
  | .app _ args => args.flatMap (Term.vars nullary)

/-- A term of an equation as a term of the ProVerif translator: `^` is `exp`, and a public
constant is rejected, as a tuple then is by that translator. -/
partial def Term.toPV : Term → Except String ProVerif.Translation.Term
  | .var x .msg => pure (.ident x)
  | .var x k => throw s!"the sorted variable `{(Term.var x k).print}` in an equation"
  | .const c => throw s!"the public constant `'{c}'` in an equation is not translated"
  | .app "pair" #[a, b] => do pure (.tuple #[← a.toPV, ← b.toPV])
  | .app "^" args => do pure (.app "exp" (← args.mapM Term.toPV))
  | .app f args => do pure (.app f (← args.mapM Term.toPV))

/-- The algebra of a model as the declarations of a ProVerif model: an equation whose two
sides have the same root is an equation of the theory, and any other is a rewrite rule of
the function at the root of its left-hand side, which is then a destructor with those
rules in order; the other functions are constructors. -/
def algebra (m : Model) :
    Except String (Array ProVerif.Translation.Ctor × Array Equation ×
      Array ProVerif.Translation.Equation × Array ProVerif.Translation.Dtor) := do
  let nullary (x : String) : Bool :=
    x == "true" || x == "false" || m.functions.any fun f => f.name == x && f.arity == 0
  let mut theoryEqs : Array Equation := #[]
  let mut eqs : Array ProVerif.Translation.Equation := #[]
  let mut rules : Array (String × ProVerif.Translation.Rule) := #[]
  for e in m.equations do
    let some f := e.lhs.root | throw s!"the left-hand side of `{e.print}` is not an application"
    let vars := (e.lhs.vars nullary ++ e.rhs.vars nullary).toList.eraseDups.toArray
    let l ← e.lhs.toPV
    let r ← e.rhs.toPV
    if e.rhs.root == some f then
      theoryEqs := theoryEqs.push e
      eqs := eqs.push { vars, lhs := l, rhs := r }
    else
      let .app _ args := l | throw s!"the left-hand side of `{e.print}` is not an application"
      rules := rules.push (f, { vars := vars.map (·, false), lhs := args, rhs := r })
  let mut names : Array String := #[]
  for (f, _) in rules do
    unless names.contains f do names := names.push f
  let mut dtors : Array ProVerif.Translation.Dtor := #[]
  for f in names do
    let some fn := m.functions.find? (·.name == f)
      | throw s!"`{f}`, at the root of an equation, is not a declared function"
    let rs := (rules.filter (·.1 == f)).map (·.2)
    for r in rs do
      unless r.lhs.size == fn.arity do throw s!"an equation applies `{f}` to {r.lhs.size} arguments"
    dtors := dtors.push { name := f, arity := fn.arity, pub := fn.pub, rules := rs, plain := true }
  let ctors := (m.functions.filter fun f => !names.contains f.name).map fun f =>
    { name := f.name, arity := f.arity, pub := f.pub, converter := false, data := false }
  return (ctors, theoryEqs, eqs, dtors)

/-! ## Facts -/

/-- The fact names Tamarin reserves. -/
def reservedFacts : List String := ["Fr", "In", "Out", "K", "KU", "KD"]

/-- The facts of a formula. -/
partial def Formula.facts : Formula → Array Fact
  | .atom f _ => #[f]
  | .not φ => φ.facts
  | .and φ ψ | .or φ ψ | .imp φ ψ | .iff φ ψ => φ.facts ++ ψ.facts
  | .all _ φ | .ex _ φ => φ.facts
  | _ => #[]

/-- The facts of a model other than the reserved ones, each with its arity and whether it
is persistent, which every use must agree on; a use in a formula says nothing about
persistence. -/
def facts (m : Model) : Except String (Array (String × Nat × Bool)) := do
  let add (fs : Array (String × Nat × Bool)) (inRule : Bool) (f : Fact) :
      Except String (Array (String × Nat × Bool)) := do
    if reservedFacts.contains f.name then return fs
    match fs.find? (·.1 == f.name) with
    | some (_, n, p) =>
      unless n == f.args.size do
        throw s!"the fact `{f.name}` is used with {n} and with {f.args.size} arguments"
      if inRule && p != f.persistent then
        throw s!"the fact `{f.name}` is used both as persistent and as linear"
      return fs
    | none => return fs.push (f.name, f.args.size, f.persistent)
  let mut fs := #[]
  for r in m.rules do
    for f in r.premises ++ r.actions ++ r.conclusions do fs ← add fs true f
  for r in m.restrictions do
    for f in r.body.facts do fs ← add fs false f
  for l in m.lemmas do
    for f in l.body.facts do fs ← add fs false f
  return fs

/-- Whether a term applies `fst` or `snd`. -/
partial def Term.usesProjection : Term → Bool
  | .app f args => f == "fst" || f == "snd" || args.any Term.usesProjection
  | _ => false

/-- The context of a model `Model.safe` has renamed, with its renamings. -/
def mkCtx (m : Model) (renamed : Std.HashMap String String) : Except String Ctx := do
  let (ctors, theoryEqs, eqs, dtors) ← algebra m
  let fs ← facts m
  let pvModel : ProVerif.Translation.Model :=
    { ctors, events := fs.map fun (n, k, _) => (n, k), equations := eqs, dtors }
  let pvCtx ← ProVerif.Translation.mkCtx pvModel renamed
  let add (syms : Std.HashMap String Sym) (x : String) (s : Sym) :
      Except String (Std.HashMap String Sym) := do
    if syms.contains x then throw s!"`{x}` is declared twice"
    return syms.insert x s
  let mut syms : Std.HashMap String Sym := {}
  syms := (syms.insert "true" (.bool true)).insert "false" (.bool false)
  for c in ctors do syms ← add syms c.name (.ctor c.arity)
  for d in dtors do syms ← add syms d.name (.dtor d.arity)
  for (n, k, p) in fs do syms ← add syms n (.fact k p)
  -- The body of `Rule.x` reads `x` as itself, so a rule, a restriction or a lemma may not
  -- have the name of a function.
  let distinct (what : String) (names : Array String) : Except String Unit := do
    for (x, i) in names.toList.zipIdx do
      if names[0:i].any (· == x) then throw s!"the {what} `{x}` is declared twice"
      match syms[x]? with
      | some (.ctor _) | some (.dtor _) =>
        throw s!"the {what} `{x}` has the name of a function; rename one of them"
      | _ => pure ()
  distinct "rule" (m.rules.map (·.name))
  distinct "restriction" (m.restrictions.map (·.name))
  distinct "lemma" (m.lemmas.map (·.name))
  let projections := m.rules.any fun r =>
    (r.actions ++ r.conclusions).any fun f => f.args.any Term.usesProjection
  return { model := m, pv := pvCtx, syms, theoryEqs, projections }

/-! ## Terms -/

/-- The environment of a rule or a formula: each variable's sort and the term it is read
as. -/
abbrev Env := Std.HashMap String (Kind × Lean.Term)

/-- A term as a Lean term, its variables read from `env`: a fresh variable is `nonce x`
and a public one `pubName x`, a public constant is `pubName "c"`, a pair is the 2-tuple and
`^` is `exp`.  An application of a destructor, allowed when `dtors`, is bound to a name
`v₀`, `v₁`, … recorded in the state, the same name for the same application, so that the
rule ranges over its results. -/
partial def emitTerm (env : Env) (dtors : Bool) : Term → EmitM Lean.Term
  | .var x k => do
    match env[x]? with
    | some (k', e) =>
      unless k == k' do throwError "the variable `{x}` has two sorts"
      return e
    | none =>
      match ← sym? x with
      | some (.ctor 0) =>
        unless k == .msg do throwError "the function `{x}` with a sort"
        return ident x
      | some (.bool true) => `((true : T.Msg))
      | some (.bool false) => `((false : T.Msg))
      | _ => throwError "the variable `{(Term.var x k).print}` is not bound"
  | .const c => `(pubName $(Syntax.mkStrLit c))
  | .app "pair" #[a, b] => do
    `((($(← emitTerm env dtors a), $(← emitTerm env dtors b)) : T.Msg))
  | .app "^" args => emitTerm env dtors (.app "exp" args)
  | t@(.app f args) => do
    let as ← args.mapM (emitTerm env dtors)
    let arity (n : Nat) : EmitM Unit := do
      unless n == args.size do throwError "`{f}` takes {n} arguments, not {args.size}"
    match ← sym? f with
    | some (.ctor n) =>
      arity n
      app (ident f) as
    | some (.dtor n) =>
      arity n
      computed t (← app (ident f) as)
    | some (.fact ..) => throwError "the fact `{f}` in a term"
    | some (.bool _) => throwError "`{f}` takes no arguments"
    | none =>
      if f == "fst" || f == "snd" then
        arity 1
        computed t (← app (ident f) as)
      else if f == "exp" then throwError "`^` needs the `diffie-hellman` builtin"
      else throwError "unknown function `{f}`"
where
  /-- The name bound to the application `call` of a destructor, the term `t`. -/
  computed (t : Term) (call : Lean.Term) : EmitM Lean.Term := do
    unless dtors do throwError "the destructor application `{t.print}` in a premise"
    let key := t.print
    if let some v := (← get).memo[key]? then return v
    let v ← fresh "v"
    modify fun st => { st with computed := st.computed.push (v, call), memo := st.memo.insert key v }
    return v

/-- A fact as a message, `Fact.F a b`. -/
def factTerm (env : Env) (dtors : Bool) (f : Fact) : EmitM Lean.Term := do
  let some (.fact n _) ← sym? f.name | throwError "unknown fact `{f.name}`"
  unless n == f.args.size do throwError "`{f.name}` takes {n} arguments, not {f.args.size}"
  app (qualified "Fact" f.name) (← f.args.mapM (emitTerm env dtors))

/-- The function applying the fact symbol `f` of arity `n` to messages, `Fact.f`. -/
def emitFact (f : String) (n : Nat) : EmitM Command := do
  let name := qualified "Fact" f
  let pat := dot f
  if n == 0 then return ← `(def $name:ident : T.Msg := .app (.inl $pat) ![])
  let xs := Array.range n |>.map (sub "x")
  let args : Array Lean.Term := xs.map (·)
  `(def $name:ident ($xs* : T.Msg) : T.Msg := .app (.inl $pat) ![$args,*])

/-- The Lean type of a variable of a sort: a message, the index of a fresh name, a public
name, or a position in the trace. -/
def kindType : Kind → EmitM Lean.Term
  | .msg => `(T.Msg)
  | .pub => `(String)
  | .fresh => `(ℕ)
  | .node => `(ℕ)

/-- Whether two sorts have the same Lean type. -/
def sameType (k k' : Kind) : Bool :=
  k == k' || (k == .fresh && k' == .node) || (k == .node && k' == .fresh)

/-- Consecutive binders of the same type, grouped. -/
def groupBinders (bs : Array (Ident × Kind)) : Array (Array Ident × Kind) :=
  bs.foldl (init := #[]) fun acc (x, k) =>
    match acc.back? with
    | some (xs, k') => if sameType k k' then acc.pop.push (xs.push x, k') else acc.push (#[x], k)
    | none => acc.push (#[x], k)

/-- `∃ (x y : τ) (z : τ'), body` -/
def existsOver (bs : Array (Ident × Kind)) (body : Lean.Term) : EmitM Lean.Term := do
  if bs.isEmpty then return body
  let groups ← (groupBinders bs).mapM fun (xs, k) => do
    let bis ← xs.mapM fun x => `(Lean.binderIdent| $x:ident)
    `(Lean.bracketedExplicitBinders| ($bis* : $(← kindType k)))
  `(∃ $groups*, $body)

/-- `∀ (x y : τ) (z : τ'), body` -/
def forallOver (bs : Array (Ident × Kind)) (body : Lean.Term) : EmitM Lean.Term := do
  if bs.isEmpty then return body
  let groups ← (groupBinders bs).mapM fun (xs, k) => do
    `(Lean.Parser.Term.bracketedBinderF| ($xs* : $(← kindType k)))
  `(∀ $groups*, $body)

/-- The variable `x` of sort `k` read as a term, through the binder `b`. -/
def varTerm (b : Ident) : Kind → EmitM Lean.Term
  | .msg => pure b
  | .fresh => `(nonce $b)
  | .pub => `(pubName $b)
  | .node => pure b

/-- The binder for the variable `x`, `_x` when nothing uses it; a variable may not have
the name of a declared symbol, which it would shadow. -/
def binder (x : String) (used : Bool) : EmitM Ident := do
  if (← sym? x).isSome then throwError "the variable `{x}` has the name of a declared symbol"
  return ident (if used then x else "_" ++ x)

/-! ## Rules -/

/-- Every variable occurrence of a term, with its sort. -/
partial def Term.occurrences : Term → Array (String × Kind)
  | .var x k => #[(x, k)]
  | .const _ => #[]
  | .app _ args => args.flatMap Term.occurrences

/-- A rule as the set of its instances: for every value of its variables, in order of
first occurrence, a fresh one an index and a public one a string, and of the results of
the destructor applications of its actions and conclusions, the step with the facts of
its premises, consumed or required as they are linear or persistent, the messages of its
`In` premises, the names of its `Fr` premises, its action facts, the messages of its `Out`
conclusions and the facts of its other conclusions. -/
def emitRule (r : Rule) : EmitM Command := do
  pv ProVerif.Translation.resetSt
  modify fun st => { st with computed := #[], memo := {} }
  let occurrences (fs : Array Fact) : Array (String × Kind) :=
    fs.flatMap fun f => f.args.flatMap Term.occurrences
  let bound := occurrences r.premises
  let mut vars : Array (String × Kind) := #[]
  for (x, k) in occurrences (r.premises ++ r.actions ++ r.conclusions) do
    if k == .msg then
      match ← sym? x with
      | some (.ctor 0) | some (.bool _) => continue
      | _ => pure ()
    match vars.find? (·.1 == x) with
    | some (_, k') => unless k == k' do throwError "the variable `{x}` has two sorts in `{r.name}`"
    | none => vars := vars.push (x, k)
  let mut env : Env := {}
  let mut binders : Array (Ident × Kind) := #[]
  for (x, k) in vars do
    if k == .node then throwError "the timepoint `#{x}` in `{r.name}`"
    unless k == .pub || bound.contains (x, k) do
      throwError "the variable `{(Term.var x k).print}` of `{r.name}` is not bound by a premise"
    let b ← binder x true
    env := env.insert x (k, ← varTerm b k)
    binders := binders.push (b, k)
  let mut consumed : Array Lean.Term := #[]
  let mut persistent : Array Lean.Term := #[]
  let mut inputs : Array Lean.Term := #[]
  let mut freshs : Array Lean.Term := #[]
  let mut actions : Array Lean.Term := #[]
  let mut outputs : Array Lean.Term := #[]
  let mut produced : Array Lean.Term := #[]
  let one (f : Fact) : EmitM Unit := do
    unless f.args.size == 1 do throwError "`{f.name}` takes one argument"
  for f in r.premises do
    match f.name with
    | "Fr" =>
      one f
      let #[.var x .fresh] := f.args | throwError "`Fr` takes a fresh variable `~x`"
      freshs := freshs.push (ident x)
    | "In" =>
      one f
      inputs := inputs.push (← emitTerm env false f.args[0]!)
    | _ =>
      if reservedFacts.contains f.name then throwError "`{f.name}` in a premise of `{r.name}`"
      let m ← factTerm env false f
      if f.persistent then persistent := persistent.push m else consumed := consumed.push m
  for f in r.actions do
    if reservedFacts.contains f.name then throwError "`{f.name}` as an action of `{r.name}`"
    actions := actions.push (← factTerm env true f)
  for f in r.conclusions do
    match f.name with
    | "Out" =>
      one f
      outputs := outputs.push (← emitTerm env true f.args[0]!)
    | _ =>
      if reservedFacts.contains f.name then throwError "`{f.name}` in a conclusion of `{r.name}`"
      produced := produced.push (← factTerm env true f)
  let mut fields : Array (TSyntax ``Parser.Term.structInstField) := #[]
  let field (name : String) (val : Lean.Term) : EmitM (TSyntax ``Parser.Term.structInstField) :=
    `(Parser.Term.structInstField| $(ident name):ident := $val)
  unless consumed.isEmpty do fields := fields.push (← field "consumed" (← `({$consumed:term,*})))
  unless persistent.isEmpty do fields := fields.push (← field "persistent" (← `([$persistent,*])))
  unless inputs.isEmpty do fields := fields.push (← field "inputs" (← `([$inputs,*])))
  unless freshs.isEmpty do fields := fields.push (← field "fresh" (← `([$freshs,*])))
  unless actions.isEmpty do fields := fields.push (← field "actions" (← `([$actions,*])))
  unless outputs.isEmpty do fields := fields.push (← field "outputs" (← `([$outputs,*])))
  unless produced.isEmpty do fields := fields.push (← field "produced" (← `({$produced:term,*})))
  let body ← if fields.isEmpty then `({}) else `({ $fields:structInstField,* })
  let mut prop ← `(s₀ = $body)
  let computed := (← get).computed
  for (v, call) in computed.reverse do prop ← `($call = some $v ∧ $prop)
  prop ← existsOver (binders ++ computed.map fun (v, _) => (v, .msg)) prop
  `(def $(qualified "Rule" r.name):ident : Rules T.Msg := {s₀ | $prop})

/-! ## Formulas -/

/-- The reserved fact a formula mentions that the translation has no reading of, if
any: `KU` and `KD`, the facts of Tamarin's proofs. -/
partial def Formula.unsupported (φ : Formula) : Option String :=
  (φ.facts.find? fun f => f.name == "KU" || f.name == "KD").map (·.name)

/-- A formula as a proposition about the trace `t₀`: `F(M) @ i` is `ActionAt t₀ i (F M)`,
`K(M) @ i` is `KnowsAt t₀ i M`, `i < j`, `i = j` and `M = N` are what they say, the
connectives are `¬`, `∧`, `∨`, `→` and `↔`, and a quantifier binds its variables, a
message as `T.Msg`, a fresh name as its index, a public name as a string and a timepoint as
a position. -/
partial def emitFormula (env : Env) : Formula → EmitM Lean.Term
  | .tt => `(True)
  | .ff => `(False)
  | .atom f i => do
    let it ← node env i
    if f.name == "K" then
      unless f.args.size == 1 do throwError "`K` takes one argument"
      `(KnowsAt t₀ $it $(← emitTerm env false f.args[0]!))
    else
      if reservedFacts.contains f.name then throwError "`{f.name}` in a formula"
      `(ActionAt t₀ $it $(← factTerm env false f))
  | .lt i j => do `($(← node env i) < $(← node env j))
  | .teq i j => do `($(← node env i) = $(← node env j))
  | .eq a b => do `($(← emitTerm env false a) = $(← emitTerm env false b))
  | .not φ => do `(¬ $(← emitFormula env φ))
  | .and φ ψ => do `($(← emitFormula env φ) ∧ $(← emitFormula env ψ))
  | .or φ ψ => do `($(← emitFormula env φ) ∨ $(← emitFormula env ψ))
  | .imp φ ψ => do `($(← emitFormula env φ) → $(← emitFormula env ψ))
  | .iff φ ψ => do `($(← emitFormula env φ) ↔ $(← emitFormula env ψ))
  | .all vars φ => quantified env vars φ false
  | .ex vars φ => quantified env vars φ true
where
  /-- The timepoint variable `i`. -/
  node (env : Env) (i : String) : EmitM Lean.Term := do
    match env[i]? with
    | some (.node, e) => return e
    | some _ => throwError "`{i}` is not a timepoint"
    | none => throwError "the timepoint `#{i}` is not bound"
  quantified (env : Env) (vars : Array (String × Kind)) (φ : Formula) (ex : Bool) :
      EmitM Lean.Term := do
    let names := φ.names
    let mut env := env
    let mut bs : Array (Ident × Kind) := #[]
    for (x, k) in vars do
      let b ← binder x (names.contains x)
      env := env.insert x (k, ← varTerm (ident x) k)
      bs := bs.push (b, k)
    let body ← emitFormula env φ
    if ex then existsOver bs body else forallOver bs body

/-- A restriction, a predicate on the trace. -/
def emitRestriction (r : Restriction) : EmitM Command := do
  pv ProVerif.Translation.resetSt
  let body ← emitFormula {} r.body
  `(def $(qualified "Restriction" r.name):ident (t₀ : Trace T.Msg) : Prop := $body)

/-- The conjunction of the restrictions. -/
def emitRestrictions : EmitM Command := do
  let rs := (← read).model.restrictions
  let calls ← rs.mapM fun r => `($(qualified "Restriction" r.name) t₀)
  let body ← calls.pop.foldrM (init := calls.back!) fun c acc => `($c ∧ $acc)
  `(def Restrictions (t₀ : Trace T.Msg) : Prop := $body)

/-- A lemma: the property of every attack, or of some attack, satisfying the
restrictions, that its formula states. -/
def emitLemma (l : Lemma) : EmitM Command := do
  pv ProVerif.Translation.resetSt
  let body ← emitFormula {} l.body
  let restricted := !(← read).model.restrictions.isEmpty
  let prop ← match l.existsTrace, restricted with
    | false, true => `(∀ t₀ ∈ system.Attacks, Restrictions t₀ → $body)
    | false, false => `(∀ t₀ ∈ system.Attacks, $body)
    | true, true => `(∃ t₀ ∈ system.Attacks, Restrictions t₀ ∧ $body)
    | true, false => `(∃ t₀ ∈ system.Attacks, $body)
  `(def $(qualified "Lemma" l.name):ident : Prop := $prop)

/-! ## The file -/

def header (ns src : String) : String :=
s!"/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.TamarinTranslation.Rewriting

/-!
# `{(System.FilePath.mk src).fileName.getD src}`, translated

Generated by `ScalingTrust.ProVerif.TamarinTranslation` from
`{src}`, following the recipe of
`ScalingTrust/ProVerif/TamarinTranslation/README.md`; translate again rather than edit.
-/

noncomputable section

namespace {ns}

open ProVerif.TraceSemantics ProVerif.TamarinTranslation Classical
"

/-- The translation of the model, as the source of a Lean file in the namespace `ns`. -/
def emitFile (ns src : String) : EmitM String := do
  let ctx ← read
  let m := ctx.model
  let alg := ctx.pv.model
  let mut out := header ns src
  let push (out : String) (doc : Option String) (c : Command) : EmitM String := do
    let s ← pp c
    return out ++ "\n" ++ (doc.map fun d => s!"/-- {d} -/\n").getD "" ++ s ++ "\n"
  out ← push out "The public names, which the attacker knows." (← `(abbrev Free := String))
  out ← push out "The constructors, by arity: the public names, the functions and the facts."
    (← pv ProVerif.Translation.emitFun)
  let eqs := "; ".intercalate (ctx.theoryEqs.map Equation.print).toList
  out ← push out (if ctx.theoryEqs.isEmpty then "No equations." else s!"The equations: `{eqs}`.")
    (← pv ProVerif.Translation.emitEquations)
  out ← push out "The free symbols: those at the root of no equation."
    (← pv ProVerif.Translation.emitFreeSymbols)
  let (t₀, t) ← pv ProVerif.Translation.emitTheory
  out ← push out "The theory of the declarations." t₀
  out ← push out "The theory, with the data symbols: its messages are those of the model." t
  out ← push out none
    (← `(@[simp] theorem free_eq {n : ℕ} (f : Fun n) : T₀.free n f = free n f := rfl))
  out := out ++ "\n/-! ## Names -/\n"
  out ← push out "The `n`-th fresh name." (← `(def nonce (n : ℕ) : T.Msg := .name n))
  out ← push out "The public name `a`."
    (← `(def pubName (a : String) : T.Msg := .app (.inl (.const a)) ![]))
  unless alg.ctors.isEmpty do
    out := out ++ "\n/-! ## Functions -/\n"
    for c in alg.ctors do
      out ← push out (← pv (ProVerif.Translation.docOf c.name none))
        (← pv (ProVerif.Translation.emitCtorFun c.name c.arity))
  unless alg.events.isEmpty do
    out := out ++ "\n/-! ## Facts -/\n"
    for (e, n) in alg.events do
      out ← push out (← pv (ProVerif.Translation.docOf e none)) (← emitFact e n)
  unless ctx.theoryEqs.isEmpty do
    out := out ++ "\n/-! ## The equations, on messages -/\n"
    for (e, i) in alg.equations.toList.zipIdx do
      out ← push out s!"`{ctx.theoryEqs[i]!.print}`"
        (← pv (ProVerif.Translation.emitEquationTheorem (i + 1) e))
  unless alg.dtors.isEmpty && !ctx.projections do
    out := out ++ "\n/-! ## Destructors -/\n"
    let mut thms : Array Command := #[]
    for d in alg.dtors do
      let (doc, c, thm) ← pv (ProVerif.Translation.emitDtor d)
      out ← push out (← pv (ProVerif.Translation.docOf d.name doc)) c
      thms := thms.push thm
    if ctx.projections then
      out ← push out "`fst(<x, y>) → x`: the first projection of the pairs, the 2-tuples."
        (← `(def fst (x₀ : T.Msg) : Option T.Msg := (Tuple.ofMsg (T.Msg × T.Msg) x₀).map Prod.fst))
      out ← push out "`snd(<x, y>) → y`: the second projection of the pairs, the 2-tuples."
        (← `(def snd (x₀ : T.Msg) : Option T.Msg := (Tuple.ofMsg (T.Msg × T.Msg) x₀).map Prod.snd))
    unless thms.isEmpty do
      out := out ++ "\n/-! ### The destructors' graphs are their rules -/\n"
      for thm in thms do out ← push out none thm
  out := out ++ "\n/-! ## The attacker -/\n"
  if let some c ← pv ProVerif.Translation.emitPub then
    out ← push out "The public symbols: the public names and the public functions." c
  out ← push out
    "The attacker: the public names, the public functions and destructors, and the standard operations."
    (← pv ProVerif.Translation.emitAttacker)
  out := out ++ "\n/-! ## Rules -/\n"
  for r in m.rules do
    out ← push out (← pv (ProVerif.Translation.docOf r.name s!"`{r.print}`")) (← emitRule r)
  out := out ++ "\n/-! ## The system -/\n"
  out ← push out "The channel, a public name: the network is the attacker."
    (← `(def channel : T.Msg := pubName "net"))
  let union ← if m.rules.isEmpty then `((∅ : Rules T.Msg)) else
    (m.rules.map fun r => (qualified "Rule" r.name : Lean.Term)).toList.tail.foldlM
      (init := (qualified "Rule" m.rules[0]!.name : Lean.Term)) fun acc r => `($acc ∪ $r)
  out ← push out "The rules." (← `(def rules : Rules T.Msg := $union))
  out ← push out "The system: the process of the rules." (← `(def system : Proc T.Msg := Rules.proc channel rules))
  out ← push out "The system is prefix-closed."
    (← `(theorem system_mem_tree : system ∈ Descriptive.tree (Act T.Msg) :=
      Rules.proc_mem_tree channel rules))
  unless m.restrictions.isEmpty do
    out := out ++ "\n/-! ## Restrictions -/\n"
    for r in m.restrictions do
      if let some f := r.body.unsupported then
        throwError "the restriction `{r.name}` mentions `{f}`"
      out ← push out (← pv (ProVerif.Translation.docOf r.name s!"`{r.print}`")) (← emitRestriction r)
    out ← push out "The restrictions, together." (← emitRestrictions)
  unless m.lemmas.isEmpty do
    out := out ++ "\n/-! ## Lemmas -/\n"
    for l in m.lemmas do
      if let some f := l.body.unsupported then
        out := out ++ s!"\n/-! `lemma {l.name}` is not translated: it mentions `{f}`. -/\n"
      else
        out ← push out (← pv (ProVerif.Translation.docOf l.name s!"`{l.print}`")) (← emitLemma l)
  return out ++ s!"\nend {ns}\n\nend\n"

/-- Translate the text of the model `src`, in the environment `env`, which must import
this module, to the source of a Lean file in the namespace `ns`. -/
def translate (env : Environment) (src text ns : String) : IO (Except String String) := do
  match Parser.parse text with
  | .error e => return .error s!"{src}:{e}"
  | .ok m =>
    let ctx : Except String Ctx := do
      let m ← m.withBuiltins
      let (m, renamed) := m.safe
      mkCtx m renamed
    match ctx with
    | .error e => return .error s!"{src}: {e}"
    | .ok ctx =>
      try
        let (s, _) ← (((emitFile ns src).run ctx).run' {}).toIO
          { fileName := src, fileMap := default } { env }
        return .ok s
      catch e => return .error s!"{src}: {e}"

end ProVerif.TamarinTranslation
