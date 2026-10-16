/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.Translation.Syntax

/-!
# ProVerif models

A model as the translation reads it, types erased: the free names, constructors,
events, equations and destructors a ProVerif file declares, its function and
process macros, its queries and its main process.  `Model.ofSyntax` reads one off
the parsed text, and rejects what the fragment leaves out: tuples, numerals,
patterns other than a variable, may-fail parameters of macros, and queries other
than a fact and a correspondence between two facts.
-/

namespace ProVerif.Translation

open Lean

/-- A term: an identifier, which is a variable, a free name or a constant; an
application; `fail`, in rewrite rules; or one of the enriched terms of the manual's
§4.1.4, which evaluate with effects: a restriction, a conditional comparing two
terms, a term evaluation and an event.  An absent `else` is `fail` (Appendix B). -/
inductive Term where
  | ident (x : String)
  | app (f : String) (args : Array Term)
  | fail
  | new (x : String) (M : Term)
  | ite (l : Term) (eq : Bool) (r : Term) (N : Term) (N' : Option Term)
  | «let» (x : String) (d : Term) (N : Term) (N' : Option Term)
  | event (e : String) (args : Array Term) (M : Term)
  deriving Inhabited, Repr

/-- `fun f(t₁, …, tₙ) : t` or `const c : t`, with its options. -/
structure Ctor where
  name : String
  arity : Nat
  pub : Bool
  /-- `[typeConverter]`: the identity, as under ProVerif's default `ignoreTypes = true`. -/
  converter : Bool
  deriving Repr

/-- A rewrite rule `forall x₁ : t₁ [or fail], …; g(p₁, …, pₙ) = r`: its variables,
each marked if it may fail, its patterns and its right-hand side. -/
structure Rule where
  vars : Array (String × Bool)
  lhs : Array Term
  rhs : Term
  deriving Inhabited, Repr

/-- A destructor: `reduc` with rules separated by `;`, or `fun … reduc` with rules
separated by `otherwise`.  Either way the first rule that applies decides
(manual §4.2.1). -/
structure Dtor where
  name : String
  arity : Nat
  pub : Bool
  rules : Array Rule
  deriving Repr

/-- `equation forall x₁ : t₁, …; l = r` -/
structure Equation where
  vars : Array String
  lhs : Term
  rhs : Term
  deriving Repr

/-- A process of the fragment.  An `if` compares two terms, with `=` or `<>`; an
absent `else` and an absent `in` are `0`. -/
inductive Proc where
  | nil
  | call (p : String) (args : Array Term)
  | par (P Q : Proc)
  | repl (P : Proc)
  | new (x : String) (P : Proc)
  | ite (l : Term) (eq : Bool) (r : Term) (P Q : Proc)
  | inp (c : Term) (x : String) (P : Proc)
  | out (c m : Term) (P : Proc)
  | «let» (x : String) (d : Term) (P Q : Proc)
  | event (e : String) (args : Array Term) (P : Proc)
  deriving Inhabited, Repr

/-- A fact of a query. -/
inductive Fact where
  | attacker (m : Term)
  | event (e : String) (args : Array Term)
  deriving Repr

/-- `query x₁ : t₁, …; F ==> H`, or `query x₁ : t₁, …; F`, which asks that `F` never
holds, as does `F ==> false`. -/
structure Query where
  vars : Array String
  premise : Fact
  /-- `H`, or `none` when the query asks that the premise never holds. -/
  conclusion : Option Fact
  deriving Repr

/-- `let p(x₁ : t₁, …) = P.` -/
structure Macro where
  name : String
  params : Array String
  body : Proc
  deriving Repr

/-- `letfun f(x₁ : t₁, …) = M.`, a function macro (manual §4.2.3). -/
structure Fn where
  name : String
  params : Array String
  body : Term
  deriving Repr

/-- A model: its declarations, in order, and its main process. -/
structure Model where
  /-- The free names, each marked if public. -/
  frees : Array (String × Bool) := #[]
  ctors : Array Ctor := #[]
  /-- The events, with their arities. -/
  events : Array (String × Nat) := #[]
  equations : Array Equation := #[]
  dtors : Array Dtor := #[]
  /-- The function macros, in order: each may call only the earlier ones. -/
  fns : Array Fn := #[]
  macros : Array Macro := #[]
  queries : Array Query := #[]
  main : Proc := .nil
  deriving Repr

/-! ## Printing, for the docstrings of the translation -/

/-- An application, `f(a, b)`, or `f` when there are no arguments. -/
def printApp (f : String) (args : Array String) : String :=
  if args.isEmpty then f else s!"{f}({", ".intercalate args.toList})"

/-- Whether a term is an enriched one, printed in parentheses as an argument. -/
def Term.enriched : Term → Bool
  | .new .. | .ite .. | .let .. | .event .. => true
  | _ => false

partial def Term.print : Term → String
  | .ident x => x
  | .app f args => s!"{f}({", ".intercalate (args.map arg).toList})"
  | .fail => "fail"
  | .new x M => s!"new {x}; {M.print}"
  | .ite l eq r N N' =>
    s!"if {l.print} {if eq then "=" else "<>"} {r.print} then {N.print}{orElse N'}"
  | .let x d N N' => s!"let {x} = {d.print} in {N.print}{orElse N'}"
  | .event e args M => s!"event {printApp e (args.map arg)}; {M.print}"
where
  arg (t : Term) : String := if t.enriched then s!"({t.print})" else t.print
  orElse : Option Term → String
    | none => ""
    | some N' => s!" else {N'.print}"

def Fn.print (f : Fn) : String :=
  s!"{printApp f.name f.params} = {f.body.print}"

def Fact.print : Fact → String
  | .attacker m => s!"attacker({m.print})"
  | .event e args => s!"event({printApp e (args.map Term.print)})"

def Query.print (q : Query) : String :=
  let vars := if q.vars.isEmpty then "" else s!"{", ".intercalate q.vars.toList}; "
  match q.conclusion with
  | none => s!"query {vars}{q.premise.print}"
  | some h => s!"query {vars}{q.premise.print} ==> {h.print}"

/-- A rule of the destructor `g`, as `g(p₁, …, pₙ) → r`. -/
def Rule.print (g : String) (r : Rule) : String :=
  s!"{(Term.app g r.lhs).print} → {r.rhs.print}"

/-! ## From the parsed text -/

/-- Conversion, with the positions of the parsed text for its error messages. -/
abbrev ConvM := ReaderT FileMap (Except String)

def throwAt {α : Type} (stx : Syntax) (msg : String) : ConvM α := do
  let fm ← read
  let pos := match stx.getPos? with
    | some p => let p := fm.toPosition p; s!"{p.line}:{p.column}: "
    | none => ""
  throw s!"{pos}{msg}"

def identStr (x : Ident) : ConvM String := do
  let n := x.getId.eraseMacroScopes
  unless n.isAtomic do throwAt x s!"unexpected qualified identifier `{n}`"
  return n.toString

partial def Term.ofSyntax (stx : TSyntax `pv_term) : ConvM Term :=
  match stx with
  | `(pv_term| $x:ident) => do
    let s ← identStr x
    return if s == "fail" then .fail else .ident s
  | `(pv_term| $f:ident($args:pv_term,*)) => do
    return .app (← identStr f) (← args.getElems.mapM ofSyntax)
  | `(pv_term| ($t:pv_term)) => ofSyntax t
  | `(pv_term| new $x:ident $[: $_t]? ; $M) => return .new (← identStr x) (← ofSyntax M)
  | `(pv_term| if $l = $r then $N $[else $N']?) =>
    return .ite (← ofSyntax l) true (← ofSyntax r) (← ofSyntax N) (← N'.mapM ofSyntax)
  | `(pv_term| if $l <> $r then $N $[else $N']?) =>
    return .ite (← ofSyntax l) false (← ofSyntax r) (← ofSyntax N) (← N'.mapM ofSyntax)
  | `(pv_term| let $x:ident $[: $_t]? = $d in $N $[else $N']?) =>
    return .let (← identStr x) (← ofSyntax d) (← ofSyntax N) (← N'.mapM ofSyntax)
  | `(pv_term| event $e:ident $[($args:pv_term,*)]? ; $M) => do
    let args ← (args.map (·.getElems)).getD #[] |>.mapM ofSyntax
    return .event (← identStr e) args (← ofSyntax M)
  | _ => throwAt stx "unexpected term: tuples and numerals are not translated"

/-- The variables of `x, y : t [or fail]`, each marked if it may fail. -/
def binders (b : TSyntax ``pv_binders) : ConvM (Array (String × Bool)) :=
  match b with
  | `(pv_binders| $xs:ident,* : $_t or fail) => do
    return (← xs.getElems.mapM identStr).map (·, true)
  | `(pv_binders| $xs:ident,* : $_t) => do
    return (← xs.getElems.mapM identStr).map (·, false)
  | _ => throwAt b "unexpected variable declaration"

def forallVars : Option (TSyntax ``pv_forall) → ConvM (Array (String × Bool))
  | none => pure #[]
  | some stx =>
    match stx with
    | `(pv_forall| forall $bs:pv_binders,* ;) => do return (← bs.getElems.mapM binders).flatten
    | _ => throwAt stx "unexpected quantifier"

/-- A rewrite rule, with the name of the destructor it is for. -/
def rule (stx : TSyntax ``pv_rule) : ConvM (String × Rule) :=
  match stx with
  | `(pv_rule| $[$q:pv_forall]? $l = $r) => do
    let vars ← forallVars q
    let .app g lhs ← Term.ofSyntax l
      | throwAt l "the left-hand side of a rewrite rule applies the destructor"
    return (g, { vars, lhs, rhs := ← Term.ofSyntax r })
  | _ => throwAt stx "unexpected rewrite rule"

def equation (stx : TSyntax ``pv_rule) : ConvM Equation :=
  match stx with
  | `(pv_rule| $[$q:pv_forall]? $l = $r) => do
    let vars ← forallVars q
    if let some (x, _) := vars.find? (·.2) then
      throwAt stx s!"may-fail variable `{x}` in an equation"
    return { vars := vars.map (·.1), lhs := ← Term.ofSyntax l, rhs := ← Term.ofSyntax r }
  | _ => throwAt stx "unexpected equation"

/-- The words of an option list `[private, data]`. -/
partial def optionWords : Syntax → Array String
  | .atom _ v => #[v]
  | .node _ _ args => args.flatMap optionWords
  | _ => #[]

def hasOption (opts : Option (TSyntax ``pv_options)) (w : String) : Bool :=
  match opts with
  | some o => (optionWords o.raw).contains w
  | none => false

partial def Proc.ofSyntax (stx : TSyntax `pv_proc) : ConvM Proc :=
  match stx with
  | `(pv_proc| $n:num) =>
    if n.getNat == 0 then pure .nil else throwAt stx "unexpected numeral"
  | `(pv_proc| $p:ident $[($args:pv_term,*)]?) => do
    return .call (← identStr p) (← terms args)
  | `(pv_proc| ($P)) => ofSyntax P
  | `(pv_proc| $P | $Q) => return .par (← ofSyntax P) (← ofSyntax Q)
  | `(pv_proc| ! $P) => return .repl (← ofSyntax P)
  | `(pv_proc| new $x:ident $[: $_t]? $[; $P]?) => return .new (← identStr x) (← rest P)
  | `(pv_proc| if $l = $r then $P $[else $Q]?) =>
    return .ite (← Term.ofSyntax l) true (← Term.ofSyntax r) (← ofSyntax P) (← rest Q)
  | `(pv_proc| if $l <> $r then $P $[else $Q]?) =>
    return .ite (← Term.ofSyntax l) false (← Term.ofSyntax r) (← ofSyntax P) (← rest Q)
  | `(pv_proc| in($c, $x:ident $[: $_t]?) $[; $P]?) =>
    return .inp (← Term.ofSyntax c) (← identStr x) (← rest P)
  | `(pv_proc| out($c, $m) $[; $P]?) =>
    return .out (← Term.ofSyntax c) (← Term.ofSyntax m) (← rest P)
  | `(pv_proc| let $x:ident $[: $_t]? = $d $[in $P $[else $Q]?]?) =>
    return .let (← identStr x) (← Term.ofSyntax d) (← rest P) (← rest Q.join)
  | `(pv_proc| event $e:ident $[($args:pv_term,*)]? $[; $P]?) =>
    return .event (← identStr e) (← terms args) (← rest P)
  | _ => throwAt stx "unexpected process"
where
  rest : Option (TSyntax `pv_proc) → ConvM Proc
    | none => pure .nil
    | some P => ofSyntax P
  terms (args : Option (Syntax.TSepArray `pv_term ",")) : ConvM (Array Term) :=
    (args.map (·.getElems)).getD #[] |>.mapM Term.ofSyntax

partial def Fact.ofSyntax (stx : TSyntax `pv_fact) : ConvM Fact :=
  match stx with
  | `(pv_fact| attacker($m)) => return .attacker (← Term.ofSyntax m)
  | `(pv_fact| event($e:ident $[($args:pv_term,*)]?)) => do
    return .event (← identStr e) (← (args.map (·.getElems)).getD #[] |>.mapM Term.ofSyntax)
  | `(pv_fact| ($f)) => ofSyntax f
  | `(pv_fact| false) => throwAt stx "`false` is not a fact"
  | _ => throwAt stx "unexpected fact"

/-- The conclusion of a correspondence: a fact, or `false`, which makes the query ask that
its premise never holds. -/
partial def conclusion (stx : TSyntax `pv_fact) : ConvM (Option Fact) :=
  match stx with
  | `(pv_fact| ($h)) => conclusion h
  | `(pv_fact| false) => pure none
  | _ => some <$> Fact.ofSyntax stx

def query (vars : Array String) (stx : TSyntax ``pv_query) : ConvM Query :=
  match stx with
  | `(pv_query| $f $[==> $h]?) => do
    let concl ← match h with
      | none => pure none
      | some h => conclusion h
    return { vars, premise := ← Fact.ofSyntax f, conclusion := concl }
  | _ => throwAt stx "unexpected query"

/-- The rules of one destructor: all for the same symbol, all of its arity. -/
def dtor (stx : Syntax) (pub : Bool) (rules : Array (String × Rule)) : ConvM Dtor := do
  let (name, first) := rules[0]!
  let arity := first.lhs.size
  for (g, r) in rules do
    unless g == name do throwAt stx s!"a rule for `{g}` among the rules of `{name}`"
    unless r.lhs.size == arity do throwAt stx s!"the rules of `{name}` differ in arity"
  return { name, arity, pub, rules := rules.map (·.2) }

def decl (m : Model) (stx : TSyntax `pv_decl) : ConvM Model :=
  match stx with
  | `(pv_decl| type $_ $[$_:pv_options]? .) => pure m
  | `(pv_decl| set $_ = $_ .) => pure m
  | `(pv_decl| channel $xs:ident,* .) => do
    return { m with frees := m.frees ++ (← xs.getElems.mapM identStr).map (·, true) }
  | `(pv_decl| free $xs:ident,* : $_t $[$opts]? .) => do
    return { m with
      frees := m.frees ++ (← xs.getElems.mapM identStr).map (·, !hasOption opts "private") }
  | `(pv_decl| const $xs:ident,* : $_t $[$opts]? .) => do
    let cs := (← xs.getElems.mapM identStr).map fun name =>
      { name, arity := 0, pub := !hasOption opts "private",
        converter := hasOption opts "typeConverter" : Ctor }
    return { m with ctors := m.ctors ++ cs }
  | `(pv_decl| fun $f:ident($ts:ident,*) : $_t $[reduc $r $[otherwise $rs]*]? $[$opts]? .) => do
    let name ← identStr f
    let arity := ts.getElems.size
    let pub := !hasOption opts "private"
    match r with
    | none =>
      return { m with
        ctors := m.ctors.push { name, arity, pub, converter := hasOption opts "typeConverter" } }
    | some r =>
      let d ← dtor stx pub (← (#[r] ++ rs.getD #[]).mapM rule)
      unless d.name == name do throwAt stx s!"the rules of `{name}` are for `{d.name}`"
      unless d.arity == arity do throwAt stx s!"the rules of `{name}` do not have its arity"
      return { m with dtors := m.dtors.push d }
  | `(pv_decl| reduc $r $[; $rs]* $[$opts]? .) => do
    return { m with dtors := m.dtors.push (← dtor stx (!hasOption opts "private") (← (#[r] ++ rs).mapM rule)) }
  | `(pv_decl| equation $e $[; $es]* $[$_opts]? .) => do
    return { m with equations := m.equations ++ (← (#[e] ++ es).mapM equation) }
  | `(pv_decl| event $e:ident $[($ts:ident,*)]? .) => do
    return { m with events := m.events.push (← identStr e, (ts.map (·.getElems.size)).getD 0) }
  | `(pv_decl| let $p:ident $[($bs:pv_binders,*)]? = $P .) => do
    let params := (← (bs.map (·.getElems)).getD #[] |>.mapM binders).flatten
    if let some (x, _) := params.find? (·.2) then
      throwAt stx s!"may-fail parameter `{x}` of a process macro"
    let mac : Macro := { name := ← identStr p, params := params.map (·.1), body := ← Proc.ofSyntax P }
    return { m with macros := m.macros.push mac }
  | `(pv_decl| letfun $f:ident $[($bs:pv_binders,*)]? = $M .) => do
    let params := (← (bs.map (·.getElems)).getD #[] |>.mapM binders).flatten
    if let some (x, _) := params.find? (·.2) then
      throwAt stx s!"may-fail parameter `{x}` of a function macro"
    let fn : Fn := { name := ← identStr f, params := params.map (·.1), body := ← Term.ofSyntax M }
    return { m with fns := m.fns.push fn }
  | `(pv_decl| query $[$vs:pv_qvars]? $q $[; $qs]* $[$_opts]? .) => do
    let vars ← match vs with
      | none => pure #[]
      | some s =>
        match s with
        | `(pv_qvars| $bs:pv_binders,* ;) => do
          pure (((← bs.getElems.mapM binders).flatten).map (·.1))
        | _ => throwAt s "unexpected query variables"
    return { m with queries := m.queries ++ (← (#[q] ++ qs).mapM (query vars)) }
  | _ => throwAt stx "unexpected declaration"

/-- The model of a parsed file; `fm` maps the positions of its text to lines for
error messages. -/
def Model.ofSyntax (fm : FileMap) (stx : TSyntax `pv_model) : Except String Model :=
  (go stx).run fm
where
  go (stx : TSyntax `pv_model) : ConvM Model :=
    match stx with
    | `(pv_model| $ds:pv_decl* process $P) => do
      let m ← ds.foldlM decl {}
      return { m with main := ← Proc.ofSyntax P }
    | _ => throwAt stx "unexpected model"

end ProVerif.Translation
