/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Set.Defs
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

/-- Emission: the context, a counter for fresh binders, and `CoreM` for quotations
and the pretty printer. -/
abbrev EmitM := ReaderT Ctx (StateT Nat CoreM)

/-- The names the translation uses unqualified, which a model's symbols must avoid. -/
def reserved : List String :=
  ["Free", "Fun", "E", "free", "free_eq", "T", "pub", "alg", "system", "Option", "some", "none", "Set",
   "Term", "Theory", "MsgAlgebra", "liftFail", "Cont", "Proc", "Unit", "Prop", "Type", "Bool",
   "Fact", "True", "False", "Classical", "Fin"]

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
def fresh (base : String) : EmitM Ident := modifyGet fun n => (sub base n, n + 1)

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
        else if rv.used x then matchPats rv rest (env.insert x s) tests k
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
              let inner ← unwrap (i + 1) pending env
              `(if $u = $e then $inner else none)
            else unwrap (i + 1) pending (env.insert v u)
          else if rv.needs p then
            let x := sub "x" i
            let inner ← unwrap (i + 1) (pending ++ [(p, (x : Lean.Term))]) env
            `(match $u:ident with
              | some $x:ident => $inner
              | none => none)
          else
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
          if isVar x && !env.contains x then env := env.insert x s else rest := rest ++ [(p, s)]
        | _ => rest := rest ++ [(p, s)]
      matchPats rv rest env #[] result
  unwrap 0 [] {}

def emitDtor (d : Dtor) : EmitM (String × Command) := do
  set 0
  let mayFail := d.mayFail
  let args := Array.range d.arity |>.map (sub (if mayFail then "u" else "x"))
  let argTy ← if mayFail then `(Option T.Msg) else `(T.Msg)
  let body ←
    if d.rules.size == 1 then compileRule mayFail args d.rules[0]! false
    else do
      let alts ← d.rules.mapM (compileRule mayFail args · true)
      let mut chain := alts[0]!
      for a in alts[1:] do
        chain ← `($chain <|> $a)
      `(Option.join ($chain))
  let cmd ← if args.isEmpty then `(def $(ident d.name):ident : Option T.Msg := $body)
    else `(def $(ident d.name):ident ($args* : $argTy) : Option T.Msg := $body)
  return (s!"`{"; ".intercalate (d.rules.map (·.print d.name)).toList}`", cmd)

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
  set 0
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
  set 0
  let body := mkDoSeq (← emitProc {} (← read).model.main)
  `(def system : Proc T.Msg := .run do $body:doSeq)

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
  unless m.dtors.isEmpty do
    out := out ++ "\n/-! ## Destructors -/\n"
    for d in m.dtors do
      let (doc, c) ← emitDtor d
      out ← push out doc c
  out := out ++ "\n/-! ## The message algebra -/\n"
  if let some c ← emitPub then
    out ← push out "The public symbols: all but the private free names and constructors, and the events." c
  out ← push out
    "The public constructors, including the public free names, and the public destructors."
    (← emitAlg)
  out := out ++ "\n/-! ## The process -/\n"
  for p in m.macros do out ← push out none (← emitMacro p)
  out ← push out "The main process." (← emitMain)
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
          let (s, _) ← (((emitFile ns src).run ctx).run' 0).toIO
            { fileName := src, fileMap := default } { env }
          return .ok s
        catch e => return .error s!"{src}: {e}"

end ProVerif.Translation
