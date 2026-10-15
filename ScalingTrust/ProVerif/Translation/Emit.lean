/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Set.Defs
import Mathlib.Tactic.FinCases
import ScalingTrust.ProVerif.Translation.Model

/-!
# Emitting the translation

The recipe of `README.md`, from a `Model` to Lean source over
`ProVerif.TraceSemantics`.  Each declaration of the output is built as Lean syntax
by quotation and printed by Lean's pretty printer; `emitFile` assembles them, with
the header and the docstrings as text, and `translate` runs the whole translation
on the text of a model.

The names of the model are kept: a symbol becomes a Lean definition of the same
name, a variable a binder of the same name, prefixed with `_` when nothing uses it.
The binders the translation introduces carry subscripts, `x₀`, `a₀`, `t₀`, `u₀`,
which no ProVerif identifier has, and the names it uses unqualified, `reserved`, a
model's symbols may not.
-/

namespace ProVerif.Translation

open Lean PrettyPrinter

/-- What a name of the model denotes. -/
inductive Sym where
  | free (pub : Bool)
  | ctor (c : Ctor)
  | event (arity : Nat)
  | dtor (d : Dtor) (mayFail : Bool)
  | proc (m : Macro)

/-- The model and its symbol table. -/
structure Ctx where
  model : Model
  syms : Std.HashMap String Sym
  /-- The symbols at the root of an equation, which no destructor may match on. -/
  equated : Std.HashSet String

/-- A `match` on a view in a compiled rule: the scrutinee, the pattern matched against it,
the pattern's symbol and the binder of the arguments. -/
structure Match where
  scrutinee : Lean.Term
  pattern : Term
  symbol : String
  binder : Ident

/-- The state of emission: a counter for fresh binders, and the record of the rule last
compiled, from which its graph theorem is proved: its matches, outermost first, its
equality tests, and the term each of its variables is bound to. -/
structure St where
  counter : Nat := 0
  views : Array Match := #[]
  tests : Array (Lean.Term × Lean.Term) := #[]
  env : Std.HashMap String Lean.Term := {}
  deriving Inhabited

/-- Emission: the context, the state, and `CoreM` for quotations and the pretty printer. -/
abbrev EmitM := ReaderT Ctx (StateT St CoreM)

/-- The names the translation uses unqualified, which a model's symbols must avoid. -/
def reserved : List String :=
  ["Free", "Fun", "E", "free", "free_eq", "T", "pub", "alg", "system", "system_mem_tree", "Option",
   "some", "none", "Set", "Term", "Theory", "MsgAlgebra", "liftFail", "Cont", "Proc", "Unit", "Prop",
   "Type", "Bool", "Fact", "True", "False", "Classical", "Fin", "Descriptive", "Act"]

/-- Whether a destructor's rules match `fail`, by a may-fail variable or the constant. -/
def Dtor.mayFail (d : Dtor) : Bool :=
  d.rules.any fun r => r.vars.any (·.2) || r.lhs.any (· matches .fail)

/-- The symbol at the root of a side of an equation. -/
partial def rootSymbol (syms : Std.HashMap String Sym) (vars : Array String) :
    Term → Except String String
  | .ident x =>
    if vars.contains x then throw s!"the side `{x}` of an equation is a variable" else pure x
  | .app f args =>
    match syms[f]?, args[0]? with
    | some (.ctor c), some a => if c.converter then rootSymbol syms vars a else pure f
    | _, _ => pure f
  | .fail => throw "`fail` in an equation"

def mkCtx (m : Model) : Except String Ctx := do
  let add (syms : Std.HashMap String Sym) (x : String) (s : Sym) :
      Except String (Std.HashMap String Sym) := do
    if reserved.contains x then throw s!"`{x}` is a name the translation uses; rename it"
    if syms.contains x then throw s!"`{x}` is declared twice"
    return syms.insert x s
  let mut syms : Std.HashMap String Sym := {}
  for (x, pub) in m.frees do syms ← add syms x (.free pub)
  for c in m.ctors do syms ← add syms c.name (.ctor c)
  for (e, n) in m.events do syms ← add syms e (.event n)
  for d in m.dtors do syms ← add syms d.name (.dtor d d.mayFail)
  for p in m.macros do syms ← add syms p.name (.proc p)
  let mut equated : Std.HashSet String := {}
  for e in m.equations do
    equated := equated.insert (← rootSymbol syms e.vars e.lhs)
    equated := equated.insert (← rootSymbol syms e.vars e.rhs)
  return { model := m, syms, equated }

/-! ## Syntax -/

def ident (s : String) : Ident := mkIdent (.mkSimple s)

def subscript (n : Nat) : String :=
  String.ofList <| (toString n).toList.map fun c => Char.ofNat (c.toNat - '0'.toNat + '₀'.toNat)

/-- `base` with the subscript `n`. -/
def sub (base : String) (n : Nat) : Ident := ident (base ++ subscript n)

/-- `.x`, resolved by the expected type. -/
def dot (s : String) : Lean.Term := ⟨mkNode ``Parser.Term.dotIdent #[mkAtom ".", ident s]⟩

/-- A fresh binder `base₀`, `base₁`, … -/
def fresh (base : String) : EmitM Ident :=
  modifyGet fun st => (sub base st.counter, { st with counter := st.counter + 1 })

/-- Record that the rule being compiled binds `x` to `e`. -/
def bindVar (x : String) (e : Lean.Term) : EmitM Unit :=
  modify fun st => { st with env := st.env.insert x e }

def num (n : Nat) : NumLit := Syntax.mkNumLit (toString n)

def app (f : Lean.Term) (args : Array Lean.Term) : EmitM Lean.Term :=
  if args.isEmpty then pure f else `($f $args*)

def sym? (x : String) : EmitM (Option Sym) := return (← read).syms[x]?

/-- The symbol `f` as a constructor of `Fun`: `.const .a` for a free name, `.f` otherwise. -/
def funCtor (f : String) : EmitM Lean.Term := do
  match ← sym? f with
  | some (.free _) => `(.const $(dot f))
  | _ => pure (dot f)

abbrev DoElem := TSyntax `doElem
abbrev DoSeq := TSyntax ``Parser.Term.doSeq

def mkDoSeq (es : Array DoElem) : DoSeq :=
  ⟨mkNode ``Parser.Term.doSeqIndent
    #[mkNullNode <| es.map fun e => mkNode ``Parser.Term.doSeqItem #[e, mkNullNode]]⟩

/-- Quotations give their identifiers macro scopes, which the printed source must not have. -/
partial def eraseScopes : Syntax → Syntax
  | .node info k args => .node info k (args.map eraseScopes)
  | .ident info raw n pre => .ident info raw n.eraseMacroScopes pre
  | s => s

def pp (c : Command) : EmitM String := do
  let s := (← ppCommand ⟨eraseScopes c⟩).pretty 100
  let trimEnd (l : String) := String.ofList (l.toList.reverse.dropWhile (· == ' ')).reverse
  return "\n".intercalate (s.splitOn "\n" |>.map trimEnd)

/-! ## Terms -/

/-- The identifiers of a term. -/
partial def Term.vars : Term → Array String
  | .ident x => #[x]
  | .app _ args => args.flatMap vars
  | .fail => #[]

/-- A message, or a term that may fail, of type `Option T.Msg`. -/
inductive Msg where
  | pure (e : Lean.Term)
  | may (e : Lean.Term)

def Msg.term : Msg → Lean.Term
  | .pure e | .may e => e

/-- Bind the terms that may fail, in order, around a body of type `Option _`. -/
def bindMay (ms : Array Msg) (body : Array Lean.Term → EmitM Lean.Term) : EmitM Lean.Term := do
  let mut args : Array Lean.Term := #[]
  let mut binds : Array (Ident × Lean.Term) := #[]
  for m in ms do
    match m with
    | .pure e => args := args.push e
    | .may e =>
      let t ← fresh "t"
      args := args.push t
      binds := binds.push (t, e)
  let mut r ← body args
  for (t, e) in binds.reverse do
    r ← `($e >>= fun $t:ident => $r)
  return r

/-- A term of the model as a Lean term, its variables read from `env`; a destructor
makes it one that may fail, where `allowDtor`. -/
partial def emitMsg (env : Std.HashMap String Lean.Term) (allowDtor : Bool) : Term → EmitM Msg
  | .fail => throwError "`fail` outside a rewrite rule"
  | .ident x => do
    if let some e := env[x]? then return .pure e
    match ← sym? x with
    | some (.free _) => return .pure (ident x)
    | some (.ctor c) =>
      unless c.arity == 0 do throwError "`{x}` takes {c.arity} arguments"
      return .pure (ident x)
    | some _ => throwError "`{x}` is not a term"
    | none => throwError "unknown identifier `{x}`"
  | .app f args => do
    match ← sym? f with
    | some (.ctor c) =>
      unless c.arity == args.size do throwError "`{f}` takes {c.arity} arguments, not {args.size}"
      if c.converter then
        unless c.arity == 1 do throwError "the type converter `{f}` is not unary"
        emitMsg env allowDtor args[0]!
      else
        let ms ← args.mapM (emitMsg env allowDtor)
        if ms.all (· matches .pure _) then return .pure (← app (ident f) (ms.map Msg.term))
        return .may (← bindMay ms fun as => do `(some $(← app (ident f) as)))
    | some (.dtor d mayFail) =>
      unless allowDtor do throwError "the destructor `{f}` in a term"
      unless d.arity == args.size do throwError "`{f}` takes {d.arity} arguments, not {args.size}"
      let ms ← args.mapM (emitMsg env allowDtor)
      if mayFail then
        return .may (← app (ident f) (← ms.mapM fun | .pure e => `(some $e) | .may e => pure e))
      return .may (← bindMay ms fun as => app (ident f) as)
    | some _ => throwError "`{f}` is not a function"
    | none => throwError "unknown function `{f}`"

/-- A term without destructors. -/
def emitPure (env : Std.HashMap String Lean.Term) (t : Term) : EmitM Lean.Term := do
  return (← emitMsg env false t).term

/-- A side of an equation as a raw `Term Fun`, its variables numbered as declared. -/
partial def emitRaw (vars : Array String) : Term → EmitM Lean.Term
  | .ident x => do
    if let some i := vars.findIdx? (· == x) then `(.var $(num i))
    else
      match ← sym? x with
      | some (.free _) | some (.ctor ⟨_, 0, _, _⟩) => do `(.func $(← funCtor x) ![])
      | _ => throwError "`{x}` in an equation is neither a variable nor a constant"
  | .app f args => do
    match ← sym? f with
    | some (.ctor c) =>
      unless c.arity == args.size do throwError "`{f}` takes {c.arity} arguments, not {args.size}"
      if c.converter then emitRaw vars args[0]!
      else
        let as ← args.mapM (emitRaw vars)
        `(.func $(← funCtor f) ![$as,*])
    | _ => throwError "`{f}` in an equation is not a constructor"
  | .fail => throwError "`fail` in an equation"

/-! ## The signature and the theory -/

def emitFree : EmitM Command := do
  let ctors ← (← read).model.frees.mapM fun (a, _) => `(Parser.Command.ctor| | $(ident a):ident)
  `(inductive Free $ctors:ctor*)

def emitFun : EmitM Command := do
  let m := (← read).model
  let syms := m.ctors.map (fun c => (c.name, c.arity)) ++ m.events
  let ctors ← syms.mapM fun (f, n) => `(Parser.Command.ctor| | $(ident f):ident : Fun $(num n))
  `(inductive Fun : ℕ → Type
      | const (a : Free) : Fun 0
      $ctors:ctor*)

def emitEquations : EmitM Command := do
  let pairs ← (← read).model.equations.mapM fun e => do
    `(($(← emitRaw e.vars e.lhs), $(← emitRaw e.vars e.rhs)))
  let body ← if pairs.isEmpty then `(∅) else `({$pairs:term,*})
  `(def E : Set (Term Fun × Term Fun) := $body)

def emitFreeSymbols : EmitM Command := do
  let ctx ← read
  let m := ctx.model
  let names := m.frees.map (·.1) ++ m.ctors.map (·.name)
  let equated := names.filter ctx.equated.contains
  if equated.isEmpty then return ← `(def free : ∀ n, Fun n → Bool := fun _ _ => true)
  let mut alts ← equated.mapM fun f => do `(Parser.Term.matchAltExpr| | _, $(← funCtor f) => false)
  if equated.size < names.size || !m.events.isEmpty then
    alts := alts.push (← `(Parser.Term.matchAltExpr| | _, _ => true))
  `(def free : ∀ n, Fun n → Bool $alts:matchAlt*)

def emitTheory : EmitM Command := do
  let proof ← if (← read).model.equations.isEmpty then `(by simp [E])
    else `(by simp [E, Term.Rigid, free])
  `(def T : Theory Fun where
      E := E
      free := free
      heads := $proof)

/-- The function applying the symbol `f` of arity `n` to messages. -/
def emitCtorFun (f : String) (n : Nat) : EmitM Command := do
  let pat ← funCtor f
  if n == 0 then return ← `(def $(ident f):ident : T.Msg := .app $pat ![])
  let xs := Array.range n |>.map (sub "x")
  let args : Array Lean.Term := xs.map (·)
  `(def $(ident f):ident ($xs* : T.Msg) : T.Msg := .app $pat ![$args,*])

/-! ## Destructors

A rule is compiled against the arguments `x₀, …`: its top-level variables are bound
first; then each structured pattern becomes a `match` on the view of its scrutinee,
or an equality test once all its variables are bound, and a repeated variable an
equality test; the tests are conjoined in one `if`.  A may-fail destructor takes
`u₀, … : Option T.Msg`, which the rule first matches against `some xᵢ`, `none` for
the pattern `fail`, or binds to a may-fail variable.
-/

/-- The patterns still to match, each against a scrutinee. -/
abbrev Pending := List (Term × Lean.Term)

/-- The variables of a rule, and which of them are used: on the right-hand side, or
again on the left. -/
structure RuleVars where
  isVar : String → Bool
  used : String → Bool

/-- Whether matching `p` reads its scrutinee: a variable that nothing uses does not. -/
def RuleVars.needs (rv : RuleVars) : Term → Bool
  | .ident v => !rv.isVar v || rv.used v
  | _ => true

/-- Match the pending patterns, then test the collected equalities and give `k env`. -/
partial def matchPats (rv : RuleVars) (pending : Pending)
    (env : Std.HashMap String Lean.Term) (tests : Array (Lean.Term × Lean.Term))
    (k : Std.HashMap String Lean.Term → EmitM Lean.Term) : EmitM Lean.Term :=
  match pending with
  | [] => do
    modify fun st => { st with tests := st.tests ++ tests }
    let res ← k env
    if tests.isEmpty then return res
    let mut conj ← `($(tests[0]!.1) = $(tests[0]!.2))
    for (a, b) in tests[1:] do
      conj ← `($conj ∧ $a = $b)
    `(if $conj then $res else none)
  | (p, s) :: rest => do
    match p with
    | .fail => throwError "`fail` inside a pattern"
    | .ident x =>
      if rv.isVar x then
        if let some e := env[x]? then matchPats rv rest env (tests.push (s, e)) k
        else
          bindVar x s
          if rv.used x then matchPats rv rest (env.insert x s) tests k
          else matchPats rv rest env tests k
      else matchPats rv ((.app x #[], s) :: rest) env tests k
    | .app f ps =>
      let arity ← match ← sym? f with
        | some (.ctor c) =>
          if c.converter then
            unless c.arity == 1 do throwError "the type converter `{f}` is not unary"
            return ← matchPats rv ((ps[0]!, s) :: rest) env tests k
          pure c.arity
        | some (.free _) => pure 0
        | _ => throwError "`{f}` in a pattern is not a constructor"
      unless arity == ps.size do throwError "`{f}` takes {arity} arguments, not {ps.size}"
      if (← read).equated.contains f then
        throwError "the pattern `{p.print}` matches on `{f}`, which an equation mentions"
      if (p.vars.filter rv.isVar).all env.contains then
        matchPats rv rest env (tests.push (s, ← emitPure env p)) k
      else
        let a ← fresh "a"
        modify fun st => { st with views := st.views.push ⟨s, p, f, a⟩ }
        let items ← ps.toList.zipIdx.mapM fun (q, i) => do return (q, ← `($a $(num i)))
        let inner ← matchPats rv (items ++ rest) env tests k
        let binder : Lean.Term ← if ps.any rv.needs then pure a else `(_)
        let view ← `($(s).view)
        `(match $view:term with
          | .app $(← funCtor f) $binder => $inner
          | _ => none)

/-- One rule as a term, `none` when it does not apply; `wrap` puts its result under
`some`, for a rule among several. -/
partial def compileRule (mayFail : Bool) (args : Array Ident) (r : Rule) (wrap : Bool) :
    EmitM Lean.Term := do
  let ruleVars := r.vars.map (·.1)
  let mayVars := (r.vars.filter (·.2)).map (·.1)
  let isVar (x : String) := ruleVars.contains x
  let lhsVars := r.lhs.flatMap Term.vars
  let rv : RuleVars :=
    { isVar, used := fun v => r.rhs.vars.contains v || (lhsVars.filter (· == v)).size ≥ 2 }
  let result (env : Std.HashMap String Lean.Term) : EmitM Lean.Term := do
    for v in r.rhs.vars do
      if isVar v && !env.contains v then
        throwError "the variable `{v}` of the right-hand side is not bound by the left-hand side"
    let e ← match r.rhs with
      | .fail => `(none)
      | .ident u =>
        if mayVars.contains u then pure env[u]! else do `(some $(← emitPure env r.rhs))
      | rhs => do
        for v in rhs.vars do
          if mayVars.contains v then throwError "the may-fail variable `{v}` inside a term"
        `(some $(← emitPure env rhs))
    if wrap then `(some $e) else pure e
  -- The arguments in order: unwrapped where may-fail, then the pending patterns.
  let rec unwrap (i : Nat) (pending : Pending) (env : Std.HashMap String Lean.Term) :
      EmitM Lean.Term := do
    if h : i < args.size then
      let p := r.lhs[i]!
      let u := args[i]
      if !mayFail then unwrap (i + 1) (pending ++ [(p, (u : Lean.Term))]) env
      else
        match p with
        | .fail =>
          let inner ← unwrap (i + 1) pending env
          `(match $u:ident with
            | none => $inner
            | some _ => none)
        | .ident v =>
          if mayVars.contains v then
            if let some e := env[v]? then
              modify fun st => { st with tests := st.tests.push (u, e) }
              let inner ← unwrap (i + 1) pending env
              `(if $u = $e then $inner else none)
            else
              bindVar v u
              unwrap (i + 1) pending (env.insert v u)
          else if rv.needs p then
            let x := sub "x" i
            let inner ← unwrap (i + 1) (pending ++ [(p, (x : Lean.Term))]) env
            `(match $u:ident with
              | some $x:ident => $inner
              | none => none)
          else
            bindVar v (sub "x" i)
            let inner ← unwrap (i + 1) pending env
            `(match $u:ident with
              | some _ => $inner
              | none => none)
        | _ =>
          let x := sub "x" i
          let inner ← unwrap (i + 1) (pending ++ [(p, (x : Lean.Term))]) env
          `(match $u:ident with
            | some $x:ident => $inner
            | none => none)
    else
      -- Bind the top-level variables first, then match the rest.
      let mut env := env
      let mut rest : Pending := []
      for (p, s) in pending do
        match p with
        | .ident x =>
          if isVar x && !env.contains x then
            bindVar x s
            env := env.insert x s
          else rest := rest ++ [(p, s)]
        | _ => rest := rest ++ [(p, s)]
      matchPats rv rest env #[] result
  unwrap 0 [] {}

abbrev Tactic := TSyntax `tactic
abbrev SimpLemma := TSyntax ``Parser.Tactic.simpLemma
abbrev RCasesPat := TSyntax ``Parser.Tactic.rcasesPatLo

def simpLemma (x : String) : EmitM SimpLemma := `(Parser.Tactic.simpLemma| $(ident x):ident)

def mkTacticSeq (ts : Array Tactic) : TSyntax ``Parser.Tactic.tacticSeq :=
  let items := ts.toList.zipIdx.foldl (init := #[]) fun acc (t, i) =>
    if i == 0 then #[t.raw] else acc ++ #[mkNullNode, t.raw]
  ⟨mkNode ``Parser.Tactic.tacticSeq
    #[mkNode ``Parser.Tactic.tacticSeq1Indented #[mkNullNode items]]⟩

/-- The constructor functions a term applies, for unfolding. -/
partial def Term.symbols (vars : Array String) : Term → EmitM (Array String)
  | .ident x => return if vars.contains x then #[] else #[x]
  | .app f args => do
    let inner ← args.flatMapM (Term.symbols vars)
    match ← sym? f with
    | some (.ctor c) => return if c.converter then inner else #[f] ++ inner
    | _ => return #[f] ++ inner
  | .fail => return #[]

/-! ### Graph theorems

The graph of a destructor `g` is `g x₀ … = some m₀ ↔ D₁ ∨ D₂ ∨ …`, a disjunct per rule
whose result is not `fail`: no earlier rule matches, and this one does with that
result, `∃ v…, x₀ = p₀ ∧ … ∧ m₀ = r`.  A variable that is a whole argument, and the
result when it is a variable, are named by them instead, as in
`sdec c k = some m ↔ c = senc m k`.  On may-fail arguments the conjuncts read
`u₀ = some p₀`, `u₀ = none` for the pattern `fail`, and a may-fail variable is a whole
argument.  Forwards the proof reads the chain of rules with `orElse_eq_some`, then the
rule that applies as the destructor evaluates it, and refutes each earlier rule by
computing; backwards it substitutes and computes, with a lemma per earlier rule, that
it matches only as its disjunct says.
-/

/-- A rule with the record of its compilation and what its graph says about it. -/
structure RuleInfo where
  r : Rule
  st : St
  alt : Lean.Term
  mayVars : Array String
  /-- The first position of each variable that is a whole argument. -/
  firstPos : Std.HashMap String Nat
  /-- Those variables, as the arguments. -/
  posθ : Std.HashMap String Lean.Term
  /-- The result, when a variable not among them, which `m₀` names. -/
  resultVar : Option String
  /-- The constructor functions of the patterns, and `free` when a view is matched. -/
  syms : Array SimpLemma
  deriving Inhabited

def mkRuleInfo (mayFail : Bool) (xs : Array Ident) (r : Rule) (st : St) (alt : Lean.Term) :
    EmitM RuleInfo := do
  let vars := r.vars.map (·.1)
  let mayVars := (r.vars.filter (·.2)).map (·.1)
  let mut firstPos : Std.HashMap String Nat := {}
  for (p, j) in r.lhs.toList.zipIdx do
    if let .ident v := p then
      if vars.contains v && !firstPos.contains v && (!mayFail || mayVars.contains v) then
        firstPos := firstPos.insert v j
  let posθ := firstPos.fold (init := ({} : Std.HashMap String Lean.Term)) fun acc v j =>
    acc.insert v (xs[j]! : Lean.Term)
  let resultVar := match r.rhs with
    | .ident v =>
      if vars.contains v && !mayVars.contains v && !firstPos.contains v then some v else none
    | _ => none
  let names := (← r.lhs.flatMapM (Term.symbols vars)).toList.eraseDups.toArray
  let syms ← (if st.views.isEmpty then names else names.push "free").mapM simpLemma
  return { r, st, alt, mayVars, firstPos, posθ, resultVar, syms }

/-- How a conjunct of a rule's graph is proved once the rule is read off: by `rfl`, by what
proves its scrutinee, or by that under `some`. -/
inductive ConjProof where
  | rfl
  | ofScrutinee (s : Lean.Term)
  | someOf (s : Lean.Term)

/-- The conjuncts of a rule's graph, each with its proof, and the variables it quantifies:
one per argument that is not a whole-argument variable, and the result's `withResult`. -/
def ruleConj (info : RuleInfo) (xs : Array Ident) (m : Ident) (mayFail withResult : Bool) :
    EmitM (Array (Lean.Term × ConjProof) × Array String) := do
  let r := info.r
  let vars := r.vars.map (·.1)
  let resultVar := if withResult then info.resultVar else none
  let exVars := vars.filter fun v => !info.firstPos.contains v && resultVar != some v
  let mut θ := info.posθ
  if let some v := resultVar then θ := θ.insert v m
  for v in exVars do θ := θ.insert v (ident v)
  let mut conj : Array (Lean.Term × ConjProof) := #[]
  for (p, j) in r.lhs.toList.zipIdx do
    let u : Lean.Term := xs[j]!
    let whole := match p with | .ident v => info.firstPos[v]? == some j | _ => false
    if whole then continue
    match p with
    | .fail => conj := conj.push (← `($u = none), .rfl)
    | .ident v =>
      if let some e := info.posθ[v]? then conj := conj.push (← `($u = $e), .ofScrutinee u)
      else if mayFail then
        conj := conj.push (← `($u = some $(← emitPure θ p)), .someOf (sub "x" j))
      else conj := conj.push (← `($u = $(← emitPure θ p)), .ofScrutinee u)
    | _ =>
      if mayFail then conj := conj.push (← `($u = some $(← emitPure θ p)), .someOf (sub "x" j))
      else conj := conj.push (← `($u = $(← emitPure θ p)), .ofScrutinee u)
  if withResult && resultVar.isNone then
    match r.rhs with
    | .ident v =>
      if let some e := (if info.mayVars.contains v then info.posθ[v]? else none) then
        conj := conj.push (← `($e = some $m), .rfl)
      else conj := conj.push (← `($m = $(← emitPure θ r.rhs)), .rfl)
    | rhs => conj := conj.push (← `($m = $(← emitPure θ rhs)), .rfl)
  return (conj, exVars)

/-- `∃ vars, c₁ ∧ …`, or `True`. -/
def ruleProp (conj : Array (Lean.Term × ConjProof)) (exVars : Array String) :
    EmitM Lean.Term := do
  if conj.isEmpty then return ← `(True)
  let cs := conj.map (·.1)
  let body ← cs.pop.foldrM (init := cs.back!) fun c acc => `($c ∧ $acc)
  exVars.foldrM (init := body) fun v acc => `(∃ $(ident v):ident, $acc)

/-- The pattern destructuring `∃ vars, c₁ ∧ …`: the variables, then `rfl` per conjunct. -/
def destructPats (conj : Array (Lean.Term × ConjProof)) (exVars : Array String) :
    EmitM (Array RCasesPat) := do
  return (← exVars.mapM fun v => `(Parser.Tactic.rcasesPatLo| $(ident v):ident))
    ++ (← conj.mapM fun _ => `(Parser.Tactic.rcasesPatLo| rfl))

def rcasesWith (h : Ident) (pats : Array RCasesPat) : EmitM Tactic :=
  if pats.size == 1 then `(tactic| rcases $h:ident with $(pats[0]!):rcasesPatLo)
  else `(tactic| rcases $h:ident with ⟨$pats,*⟩)

def simpAt (lemmas : Array SimpLemma) (h : Ident) : EmitM Tactic :=
  if lemmas.isEmpty then `(tactic| simp at $h:ident) else `(tactic| simp [$lemmas,*] at $h:ident)

def simpGoal (lemmas : Array SimpLemma) : EmitM Tactic :=
  if lemmas.isEmpty then `(tactic| simp) else `(tactic| simp [$lemmas,*])

def bullet (ts : Array Tactic) : EmitM Tactic := `(tactic| · $(mkTacticSeq ts):tacticSeq)

/-- What proves `s = …` for a scrutinee `s` once a rule is read off: the `eₖ` of its view or
the `hₜ` of its test; `none` when it is `rfl`. -/
def proofOf (st : St) (s : Lean.Term) : Option Lean.Term :=
  match st.views.findIdx? (·.scrutinee.raw.structEq s.raw) with
  | some k => some (sub "e" k)
  | none => (st.tests.findIdx? (·.1.raw.structEq s.raw)).map fun t => sub "h" (t + 1)

/-- Read the hypothesis `hX : alt = some o` of a rule as the destructor evaluates it: match
each may-fail argument in order, split the view of each matched scrutinee, then read off
the tests `h₁, …` and the result, which in the `main` case `o = some m₀` determines `m₀`;
`first` are lemmas for the first `simp`.  Then recover each matched argument from its view,
as `e₀, …`.  In the `main` case a rule whose result is `fail` is refuted on the way. -/
def forwardChain (info : RuleInfo) (xs : Array Ident) (mayFail main : Bool) (hX : Ident)
    (first : Array SimpLemma) : EmitM (Array Tactic) := do
  let r := info.r
  let st := info.st
  let mut tacs : Array Tactic := #[]
  let mut pending := first
  let mut touched := false
  if mayFail then
    for (p, j) in r.lhs.toList.zipIdx do
      let u := xs[j]!
      let x := sub "x" j
      let step? : Option Tactic ← match p with
        | .fail => some <$> `(tactic| rcases $u:ident with _ | _ <;> $(← simpAt pending hX):tactic)
        | .ident v =>
          if info.mayVars.contains v then pure none
          else some <$> `(tactic| rcases $u:ident with _ | $x:ident <;> $(← simpAt pending hX):tactic)
        | _ => some <$> `(tactic| rcases $u:ident with _ | $x:ident <;> $(← simpAt pending hX):tactic)
      if let some step := step? then
        tacs := tacs.push step
        pending := #[]
        touched := true
  for (v, k) in st.views.toList.zipIdx do
    let hv := sub "hv" k
    let f := sub "f" k
    let sv ← `($(v.scrutinee).view)
    let lemmas := pending.push (← `(Parser.Tactic.simpLemma| $hv:ident))
    tacs := tacs.push (← `(tactic|
      rcases $hv:ident : $sv:term with _ | ⟨$f:ident, $(v.binder):ident⟩ | _ <;>
        simp [$lemmas,*] at $hX:ident))
    tacs := tacs.push (← `(tactic| cases $f:ident <;> try simp at $hX:ident))
    if (← sym? v.symbol) matches some (.free _) then
      tacs := tacs.push (← `(tactic| cases ‹Free› <;> try simp at $hX:ident))
    pending := #[]
    touched := true
  unless touched do tacs := tacs.push (← simpAt pending hX)
  if main && r.rhs matches .fail then return tacs
  let t := st.tests.size
  let hr := sub "h" (t + 1)
  if t == 0 then
    if main then tacs := tacs.push (← `(tactic| subst $hX:ident))
  else
    let hs ← (Array.range t).mapM fun k => `(Parser.Tactic.rcasesPatLo| $(sub "h" (k + 1)):ident)
    let last ← if main then `(Parser.Tactic.rcasesPatLo| $hr:ident)
      else `(Parser.Tactic.rcasesPatLo| -)
    tacs := tacs.push (← `(tactic| rcases $hX:ident with ⟨$(hs.push last),*⟩))
    if main then tacs := tacs.push (← `(tactic| subst $hr:ident))
  for (v, k) in st.views.toList.zipIdx.reverse do
    let e := sub "e" k
    let hv := sub "hv" k
    let rhsTerm ← emitPure st.env v.pattern
    let n := match v.pattern with | .app _ ps => ps.size | _ => 0
    let components ← (Array.range n).mapM fun i => do
      let p := (proofOf st (← `($(v.binder) $(num i)))).getD (ident "rfl")
      `(tactic| · exact $p)
    let byCases := mkTacticSeq (#[← `(tactic| intro i₀), ← `(tactic| fin_cases i₀)] ++ components)
    tacs := tacs.push (← `(tactic| have $e:ident : $(v.scrutinee) = $rhsTerm :=
      $(v.scrutinee).eq_app_of_view' $hv (by $byCases:tacticSeq)))
  return tacs

/-- `exact ⟨witnesses, proofs⟩` for a rule's graph once the rule is read off. -/
def exactFor (info : RuleInfo) (conj : Array (Lean.Term × ConjProof)) (exVars : Array String)
    (dname : String) : EmitM Tactic := do
  let ws ← exVars.mapM fun v => do
    let some w := info.st.env[v]? | throwError "the variable `{v}` of `{dname}` is bound nowhere"
    pure w
  let proofs ← conj.mapM fun (_, pf) => do
    match pf with
    | .rfl => pure (ident "rfl" : Lean.Term)
    | .ofScrutinee s => pure ((proofOf info.st s).getD (ident "rfl"))
    | .someOf s =>
      match proofOf info.st s with
      | some p => `(congrArg some $p)
      | none => pure (ident "rfl")
  let items := ws ++ proofs
  if items.isEmpty then `(tactic| trivial)
  else if items.size == 1 then `(tactic| exact $(items[0]!))
  else `(tactic| exact ⟨$items,*⟩)

/-- The `q`-th of `n` disjuncts, `hole` inside. -/
def selectDisj (q n : Nat) (hole : Lean.Term) : EmitM Lean.Term := do
  let mut t ← if q + 1 < n then `(Or.inl $hole) else pure hole
  for _ in [0:q] do t ← `(Or.inr $t)
  return t

/-- Rule `i` of `n` in `a₀ = some o ∨ (a₀ = none ∧ (a₁ = some o ∨ …))`: a hole for each
earlier rule's `= none`, then `hole`. -/
def selectRule (i n : Nat) (hole : Lean.Term) : EmitM Lean.Term := do
  let mut t ← if i + 1 < n then `(Or.inl $hole) else pure hole
  for _ in [0:i] do t ← `(Or.inr ⟨?_, $t⟩)
  return t

def emitDtorTheorem (d : Dtor) (alts : Array Lean.Term) (recs : Array St) : EmitM Command := do
  let mayFail := d.mayFail
  let k := d.rules.size
  let xs := Array.range d.arity |>.map (sub (if mayFail then "u" else "x"))
  let m := ident "m₀"
  let h := ident "h₀"
  let infos ← (d.rules.zip (recs.zip alts)).mapM fun (r, st, alt) => mkRuleInfo mayFail xs r st alt
  let live := (infos.toList.zipIdx.filter fun (info, _) => !(info.r.rhs matches .fail)).toArray
  let g ← simpLemma d.name
  -- the statement
  let mut disj : Array Lean.Term := #[]
  for (info, i) in live do
    let mut parts : Array Lean.Term := #[]
    for j in [0:i] do
      let (c, ex) ← ruleConj infos[j]! xs m mayFail false
      parts := parts.push (← `(¬ $(← ruleProp c ex)))
    let (c, ex) ← ruleConj info xs m mayFail true
    parts := parts.push (← ruleProp c ex)
    disj := disj.push (← parts.pop.foldrM (init := parts.back!) fun a acc => `($a ∧ $acc))
  let rhs ← if disj.isEmpty then `(False)
    else disj.pop.foldrM (init := disj.back!) fun a acc => `($a ∨ $acc)
  let call ← app (ident d.name) (xs.map (·))
  let unfoldG := mkIdent (Name.mkStr (.mkSimple d.name) "eq_def")
  let rwRules : Array (TSyntax ``Parser.Tactic.rwRule) :=
    #[← `(Parser.Tactic.rwRule| $unfoldG:ident), ← `(Parser.Tactic.rwRule| join_eq_some)]
      ++ (← (Array.range (k - 1)).mapM fun _ => `(Parser.Tactic.rwRule| orElse_eq_some))
  -- forwards
  let mut fwd : Array Tactic := #[]
  if k == 1 then
    let info := infos[0]!
    fwd := fwd ++ (← forwardChain info xs mayFail true h #[g])
    unless info.r.rhs matches .fail do
      let (c, ex) ← ruleConj info xs m mayFail true
      fwd := fwd.push (← exactFor info c ex d.name)
  else
    fwd := fwd.push (← `(tactic| rw [$rwRules,*] at $h:ident))
    let mut pat ← `(Parser.Tactic.rcasesPatLo| $h:ident)
    for i in (List.range (k - 1)).reverse do
      let n := sub "n" i
      pat ← `(Parser.Tactic.rcasesPatLo| $h:ident | ⟨$n:ident, $pat⟩)
    fwd := fwd.push (← `(tactic| rcases $h:ident with $pat:rcasesPatLo))
    for (info, i) in infos.toList.zipIdx do
      let mut b : Array Tactic := #[]
      if info.r.rhs matches .fail then
        b := b ++ (← forwardChain info xs mayFail true h #[])
      else
        let q := (live.findIdx? (·.2 == i)).get!
        let (c, ex) ← ruleConj info xs m mayFail true
        let sTacs := (← forwardChain info xs mayFail true h #[]).push (← exactFor info c ex d.name)
        if i == 0 then
          unless live.size == 1 do
            b := b.push (← `(tactic| refine $(← selectDisj q live.size (← `(?_)))))
          b := b ++ sTacs
        else
          let holes ← (Array.range (i + 1)).mapM fun _ => `(?_)
          b := b.push (← `(tactic| refine $(← selectDisj q live.size (← `(⟨$holes,*⟩)))))
          for j in [0:i] do
            let (cj, exj) ← ruleConj infos[j]! xs m mayFail false
            let mut nb : Array Tactic := #[]
            if cj.isEmpty then nb := nb.push (← `(tactic| intro _))
            else
              nb := nb.push (← `(tactic| intro hm₀))
              nb := nb.push (← rcasesWith (ident "hm₀") (← destructPats cj exj))
            nb := nb.push (← simpAt infos[j]!.syms (sub "n" j))
            b := b.push (← bullet nb)
          b := b.push (← bullet sTacs)
      fwd := fwd.push (← bullet b)
  -- backwards
  let mut bwd : Array Tactic := #[]
  if live.isEmpty then bwd := bwd.push (← `(tactic| exact $(h).elim))
  else if k == 1 then
    let info := infos[0]!
    let (c, ex) ← ruleConj info xs m mayFail true
    let pats ← destructPats c ex
    unless pats.isEmpty do bwd := bwd.push (← rcasesWith h pats)
    bwd := bwd.push (← simpGoal (#[g] ++ info.syms))
  else
    let lastLive := live.back!.2
    for j in [0:lastLive] do
      let infoJ := infos[j]!
      let (cj, exj) ← ruleConj infoJ xs m mayFail false
      let prop ← ruleProp cj exj
      let pf ← if cj.isEmpty then `(fun _ _ => trivial) else do
        let chain := (← forwardChain infoJ xs mayFail false (ident "ho₀") #[]).push
          (← exactFor infoJ cj exj d.name)
        `(fun o₀ ho₀ => by $(mkTacticSeq chain):tacticSeq)
      bwd := bwd.push (← `(tactic| have $(sub "r" j):ident : ∀ o, $(infoJ.alt) = some o → $prop := $pf))
    let mut dpat ← `(Parser.Tactic.rcasesPatLo| $(sub "d" (live.size - 1)):ident)
    for q in (List.range (live.size - 1)).reverse do
      dpat ← `(Parser.Tactic.rcasesPatLo| $(sub "d" q):ident | ($dpat))
    if live.size > 1 then bwd := bwd.push (← `(tactic| rcases $h:ident with $dpat:rcasesPatLo))
    for ((info, i), q) in live.toList.zipIdx do
      let dq := if live.size > 1 then sub "d" q else h
      let (c, ex) ← ruleConj info xs m mayFail true
      let negs ← (Array.range i).mapM fun j => `(Parser.Tactic.rcasesPatLo| $(sub "n" j):ident)
      let pats := negs ++ (← destructPats c ex)
      let mut b : Array Tactic := #[]
      unless pats.isEmpty do b := b.push (← rcasesWith dq pats)
      b := b.push (← `(tactic| rw [$rwRules,*]))
      if i == 0 then
        b := b.push (← `(tactic| refine Or.inl ?_))
        b := b.push (← simpGoal info.syms)
      else
        b := b.push (← `(tactic| refine $(← selectRule i k (← `(?_)))))
        for j in [0:i] do
          b := b.push (← bullet #[← `(tactic| by_contra hne₀),
            ← `(tactic| obtain ⟨o₀, ho₀⟩ := Option.ne_none_iff_exists'.1 hne₀),
            ← `(tactic| exact $(sub "n" j) ($(sub "r" j) o₀ ho₀))])
        b := b.push (← bullet #[← simpGoal info.syms])
      if live.size > 1 then bwd := bwd.push (← bullet b) else bwd := bwd ++ b
  let name := d.name ++ "_eq_some"
  if (← read).syms.contains name then throwError "`{name}` is a name the translation uses; rename it"
  let fwdTerm ← `(fun $h:ident => by $(mkTacticSeq fwd):tacticSeq)
  let bwdTerm ← `(fun $h:ident => by $(mkTacticSeq bwd):tacticSeq)
  let stmt ← `($call = some $m ↔ $rhs)
  if !mayFail then
    `(theorem $(ident name):ident {$xs* $m:ident : T.Msg} : $stmt := ⟨$fwdTerm, $bwdTerm⟩)
  else if xs.isEmpty then
    `(theorem $(ident name):ident {$m:ident : T.Msg} : $stmt := ⟨$fwdTerm, $bwdTerm⟩)
  else
    `(theorem $(ident name):ident {$xs* : Option T.Msg} {$m:ident : T.Msg} : $stmt :=
      ⟨$fwdTerm, $bwdTerm⟩)

/-- A destructor: its docstring, its definition and its graph theorem. -/
def emitDtor (d : Dtor) : EmitM (String × Command × Command) := do
  set ({} : St)
  let mayFail := d.mayFail
  let args := Array.range d.arity |>.map (sub (if mayFail then "u" else "x"))
  let argTy ← if mayFail then `(Option T.Msg) else `(T.Msg)
  let single := d.rules.size == 1
  let mut alts : Array Lean.Term := #[]
  let mut recs : Array St := #[]
  for r in d.rules do
    modify fun st => { counter := st.counter }
    alts := alts.push (← compileRule mayFail args r (!single))
    recs := recs.push (← get)
  let body ← if single then pure alts[0]! else do
    let chain ← alts.pop.foldrM (init := alts.back!) fun a acc => `($a <|> $acc)
    `(Option.join ($chain))
  let cmd ← if args.isEmpty then `(def $(ident d.name):ident : Option T.Msg := $body)
    else `(def $(ident d.name):ident ($args* : $argTy) : Option T.Msg := $body)
  let thm ← emitDtorTheorem d alts recs
  return (s!"`{"; ".intercalate (d.rules.map (·.print d.name)).toList}`", cmd, thm)

/-! ## The algebra -/

/-- The symbols not marked private, and not events. -/
def hidden (m : Model) : Array String :=
  (m.frees.filter (!·.2)).map (·.1) ++ (m.ctors.filter (!·.pub)).map (·.name) ++ m.events.map (·.1)

/-- The predicate `pub`, when some symbol is private. -/
def emitPub : EmitM (Option Command) := do
  let m := (← read).model
  let hidden := hidden m
  if hidden.isEmpty then return none
  let mut alts ← hidden.mapM fun f => do `(Parser.Term.matchAltExpr| | _, $(← funCtor f) => False)
  if hidden.size < m.frees.size + m.ctors.size + m.events.size then
    alts := alts.push (← `(Parser.Term.matchAltExpr| | _, _ => True))
  return some (← `(def pub : ∀ n, Fun n → Prop $alts:matchAlt*))

def emitAlg : EmitM Command := do
  let m := (← read).model
  let pubFun ← if (hidden m).isEmpty then `(fun _ => Set.univ) else `(fun n => {f | pub n f})
  let dtors ← (m.dtors.filter (·.pub)).mapM fun d => do
    let a := ident "a"
    let args ← (Array.range d.arity).mapM fun i => `($a $(num i))
    let call ← app (ident d.name) args
    if d.mayFail then `(⟨$(num d.arity), fun $a:ident => $call⟩)
    else `(⟨$(num d.arity), liftFail fun $a:ident => $call⟩)
  let pubDtors ← if dtors.isEmpty then `(∅) else `({$dtors:term,*})
  `(abbrev alg : MsgAlgebra Fun where
      toTheory := T
      pubFun := $pubFun
      pubDtors := $pubDtors)

/-! ## Processes -/

/-- The identifiers a process mentions. -/
partial def Proc.idents : Proc → Array String
  | .nil => #[]
  | .call _ args => args.flatMap Term.vars
  | .par P Q => P.idents ++ Q.idents
  | .repl P => P.idents
  | .new _ P => P.idents
  | .ite l _ r P Q => l.vars ++ r.vars ++ P.idents ++ Q.idents
  | .inp c _ P => c.vars ++ P.idents
  | .out c m P => c.vars ++ m.vars ++ P.idents
  | .let _ d P Q => d.vars ++ P.idents ++ Q.idents
  | .event _ args P => args.flatMap Term.vars ++ P.idents

/-- The binder for the variable `x` of a process, `_x` when `P` does not use it. -/
def binder (x : String) (P : Proc) : EmitM Ident := do
  if (← read).syms.contains x then
    throwError "the variable `{x}` has the name of a declared symbol"
  return ident (if P.idents.contains x then x else "_" ++ x)

/-- Run `k` on the messages of `ms`: a term that may fail is matched first, and the rest
of the block runs under `some`. -/
partial def hoist (ms : List Msg) (acc : Array Lean.Term)
    (k : Array Lean.Term → EmitM (Array DoElem)) : EmitM (Array DoElem) :=
  match ms with
  | [] => k acc
  | .pure e :: rest => hoist rest (acc.push e) k
  | .may e :: rest => do
    let t ← fresh "t"
    let body ← hoist rest (acc.push t) k
    return #[← `(doElem| match $e:term with
      | some $t:ident => $(mkDoSeq body):doSeq
      | none => .stop)]

partial def emitProc (env : Std.HashMap String Lean.Term) : Proc → EmitM (Array DoElem)
  | .nil => return #[← `(doElem| .stop)]
  | .repl P => return #[← `(doElem| .repl)] ++ (← cont env P)
  | .out c m P => do
    let mc ← emitMsg env true c
    let mm ← emitMsg env true m
    hoist [mc, mm] #[] fun as =>
      return #[← `(doElem| .send $(as[0]!) $(as[1]!))] ++ (← cont env P)
  | .event e args P => do
    let some (.event n) ← sym? e | throwError "unknown event `{e}`"
    unless n == args.size do throwError "`{e}` takes {n} arguments, not {args.size}"
    let ms ← args.mapM (emitMsg env true)
    hoist ms.toList #[] fun as =>
      return #[← `(doElem| .emit $(← app (ident e) as))] ++ (← cont env P)
  | .call p args => do
    let some (.proc m) ← sym? p | throwError "unknown process macro `{p}`"
    unless m.params.size == args.size do
      throwError "`{p}` takes {m.params.size} arguments, not {args.size}"
    let ms ← args.mapM (emitMsg env true)
    hoist ms.toList #[] fun as => return #[← `(doElem| $(← app (ident p) as):term)]
  | .par P Q => do
    let p ← emitProc env P
    let q ← emitProc env Q
    return #[← `(doElem| if ← .fork then $(mkDoSeq p):doSeq else $(mkDoSeq q):doSeq)]
  | .new x P => do
    let b ← binder x P
    return #[← `(doElem| let $b:ident ← .fresh)] ++ (← emitProc (env.insert x b) P)
  | .ite l eq r P Q => do
    let ml ← emitMsg env true l
    let mr ← emitMsg env true r
    hoist [ml, mr] #[] fun as => do
      let c ← if eq then `($(as[0]!) = $(as[1]!)) else `($(as[0]!) ≠ $(as[1]!))
      let p ← emitProc env P
      let q ← emitProc env Q
      return #[← `(doElem| if $c then $(mkDoSeq p):doSeq else $(mkDoSeq q):doSeq)]
  | .inp c x P => do
    let mc ← emitMsg env true c
    hoist [mc] #[] fun as => do
      let b ← binder x P
      return #[← `(doElem| let $b:ident ← .recv $(as[0]!))] ++ (← emitProc (env.insert x b) P)
  | .let x d P Q => do
    let b ← binder x P
    match ← emitMsg env true d with
    | .pure e => return #[← `(doElem| let $b:ident := $e)] ++ (← emitProc (env.insert x b) P)
    | .may e =>
      let p ← emitProc (env.insert x b) P
      let q ← emitProc env Q
      return #[← `(doElem| match $e:term with
        | some $b:ident => $(mkDoSeq p):doSeq
        | none => $(mkDoSeq q):doSeq)]
where
  /-- The rest of the block after an action: nothing, when it is `0`. -/
  cont (env : Std.HashMap String Lean.Term) : Proc → EmitM (Array DoElem)
    | .nil => pure #[]
    | P => emitProc env P

def emitMacro (m : Macro) : EmitM Command := do
  set ({} : St)
  let mut env : Std.HashMap String Lean.Term := {}
  for x in m.params do
    if (← read).syms.contains x then
      throwError "the parameter `{x}` of `{m.name}` has the name of a declared symbol"
    env := env.insert x (ident x)
  let body := mkDoSeq (← emitProc env m.body)
  let ps := m.params.map ident
  if ps.isEmpty then `(def $(ident m.name):ident : Cont (Proc T.Msg) Unit := do $body:doSeq)
  else `(def $(ident m.name):ident ($ps* : T.Msg) : Cont (Proc T.Msg) Unit := do $body:doSeq)

def emitMain : EmitM Command := do
  set ({} : St)
  let body := mkDoSeq (← emitProc {} (← read).model.main)
  `(def system : Proc T.Msg := .run do $body:doSeq)

/-! ## Theorems -/

/-- The `i`-th equation on messages, in the variables it declares; its proof instantiates
`Theory.satisfies_msg` and evaluates the raw terms. -/
def emitEquationTheorem (i : Nat) (e : Equation) : EmitM Command := do
  let mut env : Std.HashMap String Lean.Term := {}
  for x in e.vars do
    if (← read).syms.contains x then
      throwError "the variable `{x}` of an equation has the name of a declared symbol"
    env := env.insert x (ident x)
  let l ← emitPure env e.lhs
  let r ← emitPure env e.rhs
  let lraw ← emitRaw e.vars e.lhs
  let rraw ← emitRaw e.vars e.rhs
  let n := ident "n₀"
  let mut val : Lean.Term ← if e.vars.isEmpty then `(Theory.Msg.name 0) else pure (ident e.vars[0]!)
  for (x, k) in e.vars.toList.zipIdx.reverse do
    val ← `(if $n = $(num k) then $(ident x) else $val)
  let unfold ← ((← e.lhs.symbols e.vars) ++ (← e.rhs.symbols e.vars)).toList.eraseDups.toArray.mapM
    simpLemma
  let proof ← `(by
    have h₀ := T.satisfies_msg ($lraw, $rraw) (by simp [T, E]) fun $n:ident => $val
    simp only [Term.realize_func_comp, comp_vecCons, comp_vecEmpty,
      FirstOrder.Language.Term.realize_var] at h₀
    simpa [$unfold,*] using h₀)
  let name := sub "equation" i
  if e.vars.isEmpty then `(theorem $name:ident : $l = $r := $proof)
  else
    let xs := e.vars.map ident
    `(theorem $name:ident ($xs* : T.Msg) : $l = $r := $proof)

/-- The main process is prefix-closed, by `aesop` as in `ProVerif.TraceSemantics.Examples`. -/
def emitTree : EmitM Command := do
  let names := (← read).model.macros.map (·.name) |>.push "system"
  let rules ← names.mapM fun n => `(Aesop.rule_expr| $(ident n):ident)
  `(theorem system_mem_tree : system ∈ Descriptive.tree (Act T.Msg) := by
      aesop (add norm simp [$rules,*]))

/-! ## Queries -/

def emitFact (env : Std.HashMap String Lean.Term) : Fact → EmitM Lean.Term
  | .attacker m => do `(Fact.knows $(← emitPure env m))
  | .event e args => do
    let some (.event n) ← sym? e | throwError "unknown event `{e}`"
    unless n == args.size do throwError "`{e}` takes {n} arguments, not {args.size}"
    `(Fact.event $(← app (ident e) (← args.mapM (emitPure env))))

/-- The `i`-th query: its variables as a type, when it has any or is a correspondence,
and the property it checks. -/
def emitQuery (i : Nat) (q : Query) : EmitM (Array (String × Command)) := do
  let vars := sub "Vars" i
  let σ := ident "σ"
  let mut env : Std.HashMap String Lean.Term := {}
  for x in q.vars do
    if (← read).syms.contains x then
      throwError "the query variable `{x}` has the name of a declared symbol"
    env := env.insert x (← `($σ $(dot x)))
  let σb : Ident := if q.vars.isEmpty then ident "_" else σ
  let mut out := #[]
  if !q.vars.isEmpty || q.conclusion.isSome then
    let ctors ← q.vars.mapM fun x => `(Parser.Command.ctor| | $(ident x):ident)
    out := out.push (s!"The variables of `{q.print}`.", ← `(inductive $vars:ident $ctors:ctor*))
  let prop ← match q.conclusion with
    | none =>
      let .attacker m := q.premise
        | throwError "the query `{q.print}` is not a secrecy query nor a correspondence"
      let m ← emitPure env m
      if q.vars.isEmpty then `(system.Secret alg.derive $m)
      else `(∀ $σ:ident : $vars → T.Msg, system.Secret alg.derive $m)
    | some h =>
      let f ← emitFact env q.premise
      let g ← emitFact env h
      `(system.Corr alg.derive (fun $σb:ident : $vars → T.Msg => $f) fun $σb:ident => $g)
  return out.push (s!"`{q.print}`", ← `(def $(sub "query" i):ident : Prop := $prop))

/-! ## The file -/

def header (ns src : String) : String :=
s!"/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.TraceSemantics.Security

/-!
# `{(System.FilePath.mk src).fileName.getD src}`, translated

Generated by `ScalingTrust.ProVerif.Translation` from
`{src}`, following the recipe of
`ScalingTrust/ProVerif/Translation/README.md`; translate again rather than edit.
-/

noncomputable section

namespace {ns}

open ProVerif.TraceSemantics Classical
"

/-- The translation of the model, as the source of a Lean file in the namespace `ns`. -/
def emitFile (ns src : String) : EmitM String := do
  let m := (← read).model
  let mut out := header ns src
  let push (out : String) (doc : Option String) (c : Command) : EmitM String := do
    let s ← pp c
    return out ++ "\n" ++ (doc.map fun d => s!"/-- {d} -/\n").getD "" ++ s ++ "\n"
  out ← push out "The free names." (← emitFree)
  out ← push out
    "The constructors, by arity: the free names, the declared constructors and the events."
    (← emitFun)
  let eqs := "; ".intercalate (m.equations.map fun e => s!"{e.lhs.print} = {e.rhs.print}").toList
  out ← push out (if m.equations.isEmpty then "No equations." else s!"The equations: `{eqs}`.")
    (← emitEquations)
  out ← push out "The free symbols: those at the root of no equation." (← emitFreeSymbols)
  out ← push out "The theory." (← emitTheory)
  out ← push out none
    (← `(@[simp] theorem free_eq {n : ℕ} (f : Fun n) : T.free n f = free n f := rfl))
  out := out ++ "\n/-! ## Constructors -/\n"
  for (a, _) in m.frees do out ← push out none (← emitCtorFun a 0)
  for c in m.ctors do
    unless c.converter do out ← push out none (← emitCtorFun c.name c.arity)
  unless m.events.isEmpty do
    out := out ++ "\n/-! ## Events -/\n"
    for (e, n) in m.events do out ← push out none (← emitCtorFun e n)
  unless m.equations.isEmpty do
    out := out ++ "\n/-! ## The equations, on messages -/\n"
    for (e, i) in m.equations.toList.zipIdx do
      out ← push out s!"`{e.lhs.print} = {e.rhs.print}`" (← emitEquationTheorem (i + 1) e)
  unless m.dtors.isEmpty do
    out := out ++ "\n/-! ## Destructors -/\n"
    let mut thms : Array Command := #[]
    for d in m.dtors do
      let (doc, c, thm) ← emitDtor d
      out ← push out doc c
      thms := thms.push thm
    out := out ++ "\n/-! ### The destructors' graphs are their rules -/\n"
    for t in thms do out ← push out none t
  out := out ++ "\n/-! ## The message algebra -/\n"
  if let some c ← emitPub then
    out ← push out "The public symbols: all but the private free names and constructors, and the events." c
  out ← push out
    "The public constructors, including the public free names, and the public destructors."
    (← emitAlg)
  out := out ++ "\n/-! ## The process -/\n"
  for p in m.macros do out ← push out none (← emitMacro p)
  out ← push out "The main process." (← emitMain)
  out ← push out "The main process is prefix-closed." (← emitTree)
  unless m.queries.isEmpty do
    out := out ++ "\n/-! ## Queries -/\n"
    for (q, i) in m.queries.toList.zipIdx do
      for (doc, c) in ← emitQuery (i + 1) q do
        out ← push out doc c
  return out ++ s!"\nend {ns}\n\nend\n"

/-- Translate the text of the model `src`, in the environment `env`, which must import
this module, to the source of a Lean file in the namespace `ns`. -/
def translate (env : Environment) (src text ns : String) : IO (Except String String) := do
  match parse env text src with
  | .error e => return .error e
  | .ok stx =>
    match Model.ofSyntax (adapt text).toFileMap stx with
    | .error e => return .error s!"{src}:{e}"
    | .ok m =>
      match mkCtx m with
      | .error e => return .error s!"{src}: {e}"
      | .ok ctx =>
        try
          let (s, _) ← (((emitFile ns src).run ctx).run' {}).toIO
            { fileName := src, fileMap := default } { env }
          return .ok s
        catch e => return .error s!"{src}: {e}"

end ProVerif.Translation
