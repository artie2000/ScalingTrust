/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Std.Data.HashMap
import ScalingTrust.ProVerif.Translation.Model

/-!
# The compilations before the translation

Five features of ProVerif outside the fragment of the trace semantics are compiled away
on the model before it is translated, in this order, each to what the manual or the
write-up (§3) gives as its encoding:

* **The secrecy of a bound name or variable**, `query secret x` (manual §4.3.1): an event
  `xₛ(x)` marks each binding of `x` by `new`, by an input or by a `let`, and the query
  becomes `event(xₛ(x)) && attacker(x)`, that the attacker never knows a value so bound.
* **References to bound names in queries**, `new n` (manual §6.4), which the parser has
  made variables of the query: an event `nᵣ(n)` marks each `new n`, and the variable `v`
  carries the fact `event(nᵣ(v))`, before the arrow when `v` occurs there and beside each
  fact after the arrow that mentions it otherwise, so that `v` is any name created at
  that restriction.
* **Synchronisation**, `sync t [tag]; P` (manual §4.1.7), to a coordinator: a process
  reaching level `t` reports on the private free name `barrierₜ` and waits on `resumeₜ`;
  the coordinator takes one report per tag of the level, releases as many processes on
  `resumeₜ`, and goes on to the next level, so that the levels run in increasing order
  and a level completes only when every one of its tags is reached.  A `sync` under a
  replication is refused, as the manual forbids it, and so is a model with both
  synchronisations and phases.
* **Tables**, to private channels, the manual's encoding (§6.7.3): a table `d` is a private
  free name; `insert d(M₁, …, Mₙ); P` evaluates the record and puts an unbounded supply of
  it on `d` beside `P`, `let rec₀ = (M₁, …, Mₙ) in ((!out(d, rec₀)) | P)`, so that a record
  that fails blocks and the effects of the `Mᵢ` run once; and
  `get d(T₁, …, Tₙ) suchthat M in P` reads one, `in(d, (T₁, …, Tₙ)); if M then P`, which
  blocks when no record matches, as a `get` without `else` does.  A `get` with an `else`
  branch is refused: an input cannot tell that no record matches.  When a query has a
  `table(d(…))` fact, an event `dᵢ(rec₀)` records each insertion and the fact becomes
  `event(dᵢ((M₁, …, Mₙ)))`.
* **Phases**, to channels tagged by the phase and a clock, the encoding of the write-up's
  §3, which is exact: the attacker advances the clock from phase `t-1` to `t` by sending on
  the public free name `clockₜ`; the clock takes the token `tokₜ₋₁` away for good, emits
  the event `tickₜ`, supplies `goₜ` to the processes waiting at `phase t` and releases
  `tokₜ`.  A process under phase `t` communicates on `(c, phₜ)` instead of `c`, so that it
  meets only processes of its phase and the attacker, which knows the public constant
  `phₜ`; after each input it takes and returns `tokₜ`, so that a process left behind by a
  transition, which the manual discards, never acts on what it receives afterwards.  A
  table's supply is put on `(d, phₛ)` for every phase `s` from the insertion's on.  A fact
  `attacker(M) phase s` or `table(…) phase s` becomes the fact before the event `tickₛ₊₁`,
  and `mess(N, M) phase s` becomes `mess((N, phₛ), M)`, the phase of a fact without a
  qualifier being the last.  A process macro runs in the phase of its calls, with a copy
  `pₜ` for each phase `t` when they differ.
-/

namespace ProVerif.Translation

/-- The variable binding the record of an `insert`, which no ProVerif identifier is. -/
def recordVar : String := "rec₀"

/-- The variable binding the token a process takes after an input. -/
def tokenVar : String := "tokᵥ"

/-- The event marking a binding of `x`, `xₛ`. -/
def secretEvent (x : String) : String := x ++ "ₛ"

/-- The event recording an insertion into the table `d`, `dᵢ`. -/
def tableEvent (d : String) : String := d ++ "ᵢ"

/-- The public constant tagging the channels of phase `t`, `phₜ`. -/
def phaseConst (t : Nat) : String := "ph" ++ subscript t

/-- The public free name on which the attacker starts phase `t`, `clockₜ`. -/
def clockChan (t : Nat) : String := "clock" ++ subscript t

/-- The private free name on which the clock releases the processes of phase `t`, `goₜ`. -/
def goChan (t : Nat) : String := "go" ++ subscript t

/-- The private free name of the token of phase `t`, `tokₜ`. -/
def tokChan (t : Nat) : String := "tok" ++ subscript t

/-- The event the clock emits when phase `t` starts, `tickₜ`. -/
def tickEvent (t : Nat) : String := "tick" ++ subscript t

/-- The event marking the creation of a name at the restriction `new n`, `nᵣ`. -/
def boundEvent (n : String) : String := n ++ "ᵣ"

/-- The private free name on which a process reports reaching level `t`, `barrierₜ`. -/
def barrierChan (t : Nat) : String := "barrier" ++ subscript t

/-- The private free name on which the coordinator releases level `t`, `resumeₜ`. -/
def resumeChan (t : Nat) : String := "resume" ++ subscript t

/-! ## Marking the bindings of a name -/

/-- `P` with `event ev(x)` first when `bound`. -/
def markedIf (ev x : String) (bound : Bool) (P : Proc) : Proc :=
  if bound then .event ev #[.ident x] P else P

/-- The process with `event ev(x)` after each binding of `x`: by `new`, and when `vars`
by an input or a `let` too, which the manual's `query secret x` concerns, a binding inside
a term not being allowed there (§4.3.1); a reference `new x` in a query concerns the
restrictions only (§6.4). -/
partial def Proc.marked (ev x : String) (vars : Bool) : Proc → Proc
  | .nil => .nil
  | .call p args => .call p args
  | .par P Q => .par (P.marked ev x vars) (Q.marked ev x vars)
  | .repl P => .repl (P.marked ev x vars)
  | .new y P => .new y (markedIf ev x (y == x) (P.marked ev x vars))
  | .ite c P Q => .ite c (P.marked ev x vars) (Q.marked ev x vars)
  | .inp c p P => .inp c p (markedIf ev x (vars && p.vars.contains x) (P.marked ev x vars))
  | .out c m P => .out c m (P.marked ev x vars)
  | .let p d P Q =>
    .let p d (markedIf ev x (vars && p.vars.contains x) (P.marked ev x vars)) (Q.marked ev x vars)
  | .event e args P => .event e args (P.marked ev x vars)
  | .insert d args P => .insert d args (P.marked ev x vars)
  | .get d ps cond P Q =>
    .get d ps cond (markedIf ev x (vars && ps.any (·.vars.contains x)) (P.marked ev x vars))
      (Q.marked ev x vars)
  | .phase n P => .phase n (P.marked ev x vars)
  | .sync n tag P => .sync n tag (P.marked ev x vars)

/-- The identifiers a process binds by `new`, by an input or by a `let`. -/
partial def Proc.binders : Proc → Array String
  | .nil | .call .. => #[]
  | .par P Q | .ite _ P Q => P.binders ++ Q.binders
  | .repl P | .phase _ P | .sync _ _ P | .out _ _ P | .event _ _ P | .insert _ _ P => P.binders
  | .new y P => #[y] ++ P.binders
  | .inp _ p P => p.vars ++ P.binders
  | .let p _ P Q => p.vars ++ P.binders ++ Q.binders
  | .get _ ps _ P Q => ps.flatMap Pat.vars ++ P.binders ++ Q.binders

/-- The names a process creates by `new`. -/
partial def Proc.news : Proc → Array String
  | .nil | .call .. => #[]
  | .par P Q | .ite _ P Q | .let _ _ P Q | .get _ _ _ P Q => P.news ++ Q.news
  | .repl P | .phase _ P | .sync _ _ P | .inp _ _ P | .out _ _ P | .event _ _ P
  | .insert _ _ P => P.news
  | .new y P => #[y] ++ P.news

/-! ## The secrecy of a bound name or variable -/

/-- `m` with each `query secret x` compiled to the marking event and the query. -/
def Model.withoutSecrets (m : Model) : Except String Model := do
  let mut m := m
  for x in m.secrets do
    unless (m.main.binders ++ m.macros.flatMap (·.body.binders)).contains x do
      throw s!"query secret {x}: `{x}` is not a name or a variable the process binds"
    let query : Query :=
      { vars := #[x],
        premise := #[(false, .event (secretEvent x) #[.ident x] none),
          (false, .attacker (.ident x) none)],
        concl := .false, source := s!"query secret {x}" }
    m := { m with
      events := m.events.push (secretEvent x, 1),
      macros := m.macros.map fun p => { p with body := p.body.marked (secretEvent x) x true },
      main := m.main.marked (secretEvent x) x true,
      queries := m.queries.push query }
  return { m with secrets := #[] }

/-! ## Bound names in queries -/

/-- The hypothesis with `event(ev(v))` conjoined to each of its facts that mentions `v`; a
nested correspondence whose own fact mentions `v` is refused, that fact standing alone
before its arrow. -/
partial def Hyp.withBound (ev v : String) : Hyp → Except String Hyp
  | .fact inj f =>
    if f.names.contains v then
      pure (.and (.fact inj f) (.fact Bool.false (.event ev #[.ident v] none)))
    else pure (.fact inj f)
  | .and h₁ h₂ => return .and (← h₁.withBound ev v) (← h₂.withBound ev v)
  | .or h₁ h₂ => return .or (← h₁.withBound ev v) (← h₂.withBound ev v)
  | .false => pure .false
  | .corr inj f h => do
    if f.names.contains v then
      throw s!"a reference `new …` in `{f.print inj}`, the fact before the arrow of a nested correspondence, is not implemented yet"
    return .corr inj f (← h.withBound ev v)

/-- `m` with the references to bound names in its queries compiled to events: `event nᵣ(n)`
marks each `new n`, and a variable `v` of a query standing for `new n` carries the fact
`event(nᵣ(v))`, before the arrow when `v` occurs there and beside each fact after the
arrow that mentions it otherwise: `v` is any name created at that restriction (manual
§6.4). -/
def Model.withoutBoundNames (m : Model) : Except String Model := do
  let mut events := m.events
  let mut marked : Array String := #[]
  let mut queries : Array Query := #[]
  for q in m.queries do
    let mut premise := q.premise
    let mut concl := q.concl
    for (v, n) in q.bound do
      unless marked.contains n do
        unless (m.main.news ++ m.macros.flatMap (·.body.news)).contains n do
          throw s!"`new {n}` in a query: no restriction of the process creates `{n}`"
        events := events.push (boundEvent n, 1)
        marked := marked.push n
      let fact : Fact := .event (boundEvent n) #[.ident v] none
      if premise.any (·.2.names.contains v) then
        premise := premise.push (false, fact)
      else
        concl ← concl.withBound (boundEvent n) v
    queries := queries.push { q with
      premise
      concl
      bound := #[] }
  let mark (P : Proc) : Proc := marked.foldl (fun P n => P.marked (boundEvent n) n false) P
  return { m with
    events
    macros := m.macros.map fun p => { p with body := mark p.body }
    main := mark m.main
    queries }

/-! ## Tables -/

/-- The record of an `insert` or the element of a `table` fact: the one term, or the
tuple. -/
def tableRecord (args : Array Term) : Term :=
  if args.size == 1 then args[0]! else .tuple args

/-- The process with its tables compiled to private channels; `recorded` are the tables
whose insertions are recorded by an event. -/
partial def Proc.withoutTables (tables recorded : Array String) : Proc → Except String Proc
  | .nil => pure .nil
  | .call p args => pure (.call p args)
  | .par P Q => return .par (← P.withoutTables tables recorded) (← Q.withoutTables tables recorded)
  | .repl P => return .repl (← P.withoutTables tables recorded)
  | .new x P => return .new x (← P.withoutTables tables recorded)
  | .ite c P Q => return .ite c (← P.withoutTables tables recorded) (← Q.withoutTables tables recorded)
  | .inp c p P => return .inp c p (← P.withoutTables tables recorded)
  | .out c m P => return .out c m (← P.withoutTables tables recorded)
  | .let p d P Q => return .let p d (← P.withoutTables tables recorded) (← Q.withoutTables tables recorded)
  | .event e args P => return .event e args (← P.withoutTables tables recorded)
  | .phase n P => return .phase n (← P.withoutTables tables recorded)
  | .sync n tag P => return .sync n tag (← P.withoutTables tables recorded)
  | .insert d args P => do
    unless tables.contains d do throw s!"`{d}` is not a table"
    let supply : Proc := .repl (.out (.ident d) (.ident recordVar) .nil)
    let rest := Proc.par supply (← P.withoutTables tables recorded)
    let rest := if recorded.contains d then .event (tableEvent d) #[.ident recordVar] rest else rest
    return .let (.var recordVar) (tableRecord args) rest .nil
  | .get d ps cond P Q => do
    unless tables.contains d do throw s!"`{d}` is not a table"
    unless Q matches .nil do
      throw s!"the else branch of `get {d}(…)` is not translated: tables are compiled to private channels (manual §6.7.3), on which an input cannot tell that no record matches"
    let pat := if ps.size == 1 then ps[0]! else .tuple ps
    let body ← P.withoutTables tables recorded
    return .inp (.ident d) pat (match cond with | none => body | some c => .ite c body .nil)

/-- The fact with a `table` fact compiled to the event of the insertion. -/
partial def Fact.withoutTables (tables : Array String) : Fact → Except String Fact
  | .table d args ph => do
    unless tables.contains d do throw s!"`{d}` is not a table"
    return .event (tableEvent d) #[tableRecord args] ph
  | .before f e args => return .before (← f.withoutTables tables) e args
  | f => pure f

partial def Hyp.withoutTables (tables : Array String) : Hyp → Except String Hyp
  | .fact inj f => return .fact inj (← f.withoutTables tables)
  | .and h₁ h₂ => return .and (← h₁.withoutTables tables) (← h₂.withoutTables tables)
  | .or h₁ h₂ => return .or (← h₁.withoutTables tables) (← h₂.withoutTables tables)
  | .false => pure .false
  | .corr inj f h => return .corr inj (← f.withoutTables tables) (← h.withoutTables tables)

def Query.withoutTables (tables : Array String) (q : Query) : Except String Query := do
  let premise ← q.premise.mapM fun (inj, f) => do return (inj, ← f.withoutTables tables)
  let concl ← q.concl.withoutTables tables
  return { q with premise, concl }

/-- The tables that a `table` fact of a query mentions. -/
partial def Fact.tables : Fact → Array String
  | .table d _ _ => #[d]
  | .before f _ _ => f.tables
  | _ => #[]

partial def Hyp.tables : Hyp → Array String
  | .fact _ f => f.tables
  | .and h₁ h₂ | .or h₁ h₂ => h₁.tables ++ h₂.tables
  | .false => #[]
  | .corr _ f h => f.tables ++ h.tables

/-- `m` with its tables compiled to private channels. -/
def Model.withoutTables (m : Model) : Except String Model := do
  let tables := m.tables.map (·.1)
  let recorded := tables.filter fun d =>
    m.queries.any fun q => q.premise.any (·.2.tables.contains d) || q.concl.tables.contains d
  let macros ← m.macros.mapM fun p => do
    let body ← p.body.withoutTables tables recorded
    return { p with body }
  let main ← m.main.withoutTables tables recorded
  let queries ← m.queries.mapM (·.withoutTables tables)
  return { m with
    frees := m.frees ++ tables.map (·, false)
    tables := #[]
    events := m.events ++ recorded.map (tableEvent ·, 1)
    macros, main, queries }

/-! ## Phases -/

/-- The greatest phase a process mentions, `0` when it mentions none. -/
partial def Proc.maxPhase : Proc → Nat
  | .nil | .call .. => 0
  | .par P Q | .ite _ P Q | .let _ _ P Q | .get _ _ _ P Q => max P.maxPhase Q.maxPhase
  | .repl P | .new _ P | .inp _ _ P | .out _ _ P | .event _ _ P | .insert _ _ P
  | .sync _ _ P => P.maxPhase
  | .phase n P => max n P.maxPhase

partial def Fact.maxPhase : Fact → Nat
  | .attacker _ ph | .event _ _ ph | .mess _ _ ph | .table _ _ ph => ph.getD 0
  | .eq .. | .ne .. => 0
  | .before f _ _ => f.maxPhase

partial def Hyp.maxPhase : Hyp → Nat
  | .fact _ f => f.maxPhase
  | .and h₁ h₂ | .or h₁ h₂ => max h₁.maxPhase h₂.maxPhase
  | .false => 0
  | .corr _ f h => max f.maxPhase h.maxPhase

/-- The greatest phase of the model: of its processes and of its queries. -/
def Model.maxPhase (m : Model) : Nat :=
  let qs := m.queries.map fun q =>
    max ((q.premise.map (·.2.maxPhase)).foldl max 0) q.concl.maxPhase
  (m.macros.map (·.body.maxPhase) ++ qs).foldl max m.main.maxPhase

/-- The macro calls of a process under phase `t`, with the phase of each; a call under a
phase prefix no later than `t` is dead. -/
partial def Proc.calls (t : Nat) : Proc → Array (String × Nat)
  | .nil => #[]
  | .call p _ => #[(p, t)]
  | .par P Q | .ite _ P Q | .let _ _ P Q | .get _ _ _ P Q => P.calls t ++ Q.calls t
  | .repl P | .new _ P | .inp _ _ P | .out _ _ P | .event _ _ P | .insert _ _ P
  | .sync _ _ P => P.calls t
  | .phase s P => if s ≤ t then #[] else P.calls s

/-- The phases in which each process macro runs, those of its calls: a macro calls only
the macros declared before it, so the later macros are visited first. -/
def macroPhases (m : Model) : Std.HashMap String (List Nat) := Id.run do
  let mut φ : Std.HashMap String (List Nat) := {}
  let mut pending := m.main.calls 0
  for p in m.macros.reverse do
    let ts := ((pending.filter (·.1 == p.name)).map (·.2)).toList.eraseDups
    pending := pending.filter (·.1 != p.name)
    unless ts.isEmpty do
      φ := φ.insert p.name ts
      for t in ts do pending := pending ++ p.body.calls t
  return φ

/-- The copy of the process macro `p` that runs in phase `t`: `p` itself when it runs in
one phase, `pₜ` when it runs in several. -/
def phaseCopy (φ : Std.HashMap String (List Nat)) (p : String) (t : Nat) : String :=
  match φ[p]? with
  | some (_ :: _ :: _) => p ++ subscript t
  | _ => p

/-- The channel `c` tagged with phase `t`. -/
def tagged (c : Term) (t : Nat) : Term := .tuple #[c, .ident (phaseConst t)]

/-- `P` after an input of phase `t`: the token taken and returned. -/
def checked (t : Nat) (P : Proc) : Proc :=
  .inp (.ident (tokChan t)) (.var tokenVar) (.out (.ident (tokChan t)) (.ident tokenVar) P)

/-- A process under phase `t`, of a model with phases up to `n`, the tables `tables` and
the macros running in the phases `φ`, with its phases compiled out. -/
partial def Proc.withoutPhases (n : Nat) (tables : Array String)
    (φ : Std.HashMap String (List Nat)) (t : Nat) : Proc → Except String Proc
  | .nil => pure .nil
  | .call p args => pure (.call (phaseCopy φ p t) args)
  | .par P Q => return .par (← P.withoutPhases n tables φ t) (← Q.withoutPhases n tables φ t)
  | .repl (.out (.ident d) m .nil) =>
    if tables.contains d then
      -- A table's supply, for every phase from the insertion's on.
      let supplies := (Array.range (n + 1 - t)).map fun k =>
        Proc.repl (.out (tagged (.ident d) (t + k)) m .nil)
      return supplies.pop.foldr (fun P acc => .par P acc) supplies.back!
    else pure (.repl (.out (tagged (.ident d) t) m .nil))
  | .repl P => return .repl (← P.withoutPhases n tables φ t)
  | .new x P => return .new x (← P.withoutPhases n tables φ t)
  | .ite c P Q =>
    return .ite c (← P.withoutPhases n tables φ t) (← Q.withoutPhases n tables φ t)
  | .inp c p P => return .inp (tagged c t) p (checked t (← P.withoutPhases n tables φ t))
  | .out c m P => return .out (tagged c t) m (← P.withoutPhases n tables φ t)
  | .let p d P Q =>
    return .let p d (← P.withoutPhases n tables φ t) (← Q.withoutPhases n tables φ t)
  | .event e args P => return .event e args (← P.withoutPhases n tables φ t)
  | .insert .. | .get .. => throw "tables are compiled out before phases"
  | .sync .. => throw "synchronisations are compiled out before phases"
  | .phase s P =>
    if s ≤ t then pure .nil
    else return .inp (.ident (goChan s)) (.var tokenVar) (← P.withoutPhases n tables φ s)

/-- The clock of a model with phases `1` to `n`: `tok₀` at first, and for each `t` in turn,
`in(clockₜ, _); in(tokₜ₋₁, _); event tickₜ; ((!out(goₜ, phₜ)) | out(tokₜ, phₜ) | …)`. -/
def clock (n : Nat) : Proc :=
  .par (.out (.ident (tokChan 0)) (.ident (phaseConst 0)) .nil) (chain n 1)
where
  /-- The transitions to the phases `t`, `t + 1`, … while `k` phases remain. -/
  chain : Nat → Nat → Proc
    | 0, _ => .nil
    | k + 1, t =>
      .inp (.ident (clockChan t)) (.var tokenVar)
        (.inp (.ident (tokChan (t - 1))) (.var tokenVar)
          (.event (tickEvent t) #[]
            (.par (.repl (.out (.ident (goChan t)) (.ident (phaseConst t)) .nil))
              (.par (.out (.ident (tokChan t)) (.ident (phaseConst t)) .nil) (chain k (t + 1))))))

/-- The fact with its phase compiled out, in a model with phases up to `n`: a fact of phase
`s < n` is the fact before `tickₛ₊₁`, one of the last phase or without a phase is the fact
itself, and a message of phase `s` is a message on the channel tagged `phₛ`, `n` being
the phase of a message without a qualifier. -/
partial def Fact.withoutPhases (n : Nat) : Fact → Except String Fact
  | .attacker m ph => pure (dephase (.attacker m none) ph)
  | .event e args ph => pure (dephase (.event e args none) ph)
  | .mess c m ph => pure (.mess (if n == 0 then c else tagged c (ph.getD n)) m none)
  | .table .. => throw "tables are compiled out before phases"
  | .eq l r => pure (.eq l r)
  | .ne l r => pure (.ne l r)
  | .before f e args => return .before (← f.withoutPhases n) e args
where
  dephase (f : Fact) : Option Nat → Fact
    | none => f
    | some s => if n ≤ s then f else .before f (tickEvent (s + 1)) #[]

partial def Hyp.withoutPhases (n : Nat) : Hyp → Except String Hyp
  | .fact inj f => return .fact inj (← f.withoutPhases n)
  | .and h₁ h₂ => return .and (← h₁.withoutPhases n) (← h₂.withoutPhases n)
  | .or h₁ h₂ => return .or (← h₁.withoutPhases n) (← h₂.withoutPhases n)
  | .false => pure .false
  | .corr inj f h => return .corr inj (← f.withoutPhases n) (← h.withoutPhases n)

def Query.withoutPhases (n : Nat) (q : Query) : Except String Query := do
  let premise ← q.premise.mapM fun (inj, f) => do return (inj, ← f.withoutPhases n)
  let concl ← q.concl.withoutPhases n
  return { q with premise, concl }

/-- `m`, whose tables were `tables`, with its phases compiled out. -/
def Model.withoutPhases (tables : Array String) (m : Model) : Except String Model := do
  let n := m.maxPhase
  let queries ← m.queries.mapM (·.withoutPhases n)
  if n == 0 then return { m with queries }
  let φ := macroPhases m
  let mut macros : Array Macro := #[]
  for p in m.macros do
    for t in (φ.getD p.name [0]).mergeSort (· ≤ ·) do
      let body ← p.body.withoutPhases n tables φ t
      macros := macros.push { p with name := phaseCopy φ p.name t, body }
  let main ← m.main.withoutPhases n tables φ 0
  let later := (Array.range n).map (· + 1)
  let ctors := (Array.range (n + 1)).map fun t =>
    { name := phaseConst t, arity := 0, pub := true, converter := false, data := false : Ctor }
  return { m with
    ctors := m.ctors ++ ctors
    frees := m.frees ++ later.map (clockChan ·, true) ++ later.map (goChan ·, false)
      ++ (Array.range (n + 1)).map (tokChan ·, false)
    events := m.events ++ later.map (tickEvent ·, 0)
    macros, main := .par main (clock n), queries }

/-! ## Synchronisation -/

/-- The synchronisations a process reaches, its macro calls expanded, as level and tag, an
untagged one tagged by its number; one under a replication is refused (manual §4.1.7). -/
partial def Proc.syncs (macros : Array Macro) (underRepl : Bool) :
    Proc → StateT Nat (Except String) (Array (Nat × String))
  | .nil => pure #[]
  | .call p _ =>
    match macros.find? (·.name == p) with
    | some q => q.body.syncs macros underRepl
    | none => pure #[]
  | .par P Q | .ite _ P Q | .let _ _ P Q | .get _ _ _ P Q =>
    return (← P.syncs macros underRepl) ++ (← Q.syncs macros underRepl)
  | .repl P => P.syncs macros true
  | .new _ P | .inp _ _ P | .out _ _ P | .event _ _ P | .insert _ _ P | .phase _ P =>
    P.syncs macros underRepl
  | .sync n tag P => do
    if underRepl then throw s!"`sync {n}` under a replication, which the manual forbids (§4.1.7)"
    let k ← getModify (· + 1)
    return #[(n, tag.getD s!"#{k}")] ++ (← P.syncs macros underRepl)

/-- The process with each `sync t; P` as a report on `barrierₜ` and a wait on `resumeₜ`. -/
partial def Proc.withoutSyncs : Proc → Proc
  | .nil => .nil
  | .call p args => .call p args
  | .par P Q => .par P.withoutSyncs Q.withoutSyncs
  | .repl P => .repl P.withoutSyncs
  | .new x P => .new x P.withoutSyncs
  | .ite c P Q => .ite c P.withoutSyncs Q.withoutSyncs
  | .inp c p P => .inp c p P.withoutSyncs
  | .out c m P => .out c m P.withoutSyncs
  | .let p d P Q => .let p d P.withoutSyncs Q.withoutSyncs
  | .event e args P => .event e args P.withoutSyncs
  | .insert d args P => .insert d args P.withoutSyncs
  | .get d ps cond P Q => .get d ps cond P.withoutSyncs Q.withoutSyncs
  | .phase n P => .phase n P.withoutSyncs
  | .sync n _ P =>
    .out (.ident (barrierChan n)) (.ident (barrierChan n))
      (.inp (.ident (resumeChan n)) (.var "_") P.withoutSyncs)

/-- The coordinator of the levels `(t, k)` in increasing order, `k` the number of tags of
level `t`: `k` reports on `barrierₜ`, then `k` releases on `resumeₜ` beside the
coordinator of the next level. -/
def coordinator : List (Nat × Nat) → Proc
  | [] => .nil
  | (t, k) :: rest =>
    let releases := (List.range k).foldl
      (fun acc _ => .par (.out (.ident (resumeChan t)) (.ident (resumeChan t)) .nil) acc)
      (coordinator rest)
    (List.range k).foldl (fun P _ => .inp (.ident (barrierChan t)) (.var "_") P) releases

/-- `m` with its synchronisations compiled to the coordinator. -/
def Model.withoutSyncs (m : Model) : Except String Model := do
  let (pairs, _) ← (m.main.syncs m.macros false).run 0
  if pairs.isEmpty then return m
  if m.maxPhase > 0 then
    throw "synchronisations and phases in one model, which the manual forbids (§4.1.7)"
  let levels := (pairs.map (·.1)).toList.eraseDups.mergeSort (· ≤ ·)
  let counts := levels.map fun t =>
    (t, ((pairs.filter (·.1 == t)).map (·.2)).toList.eraseDups.length)
  return { m with
    frees := m.frees ++ (levels.map fun t => (barrierChan t, false)).toArray
      ++ (levels.map fun t => (resumeChan t, false)).toArray
    macros := m.macros.map fun p => { p with body := p.body.withoutSyncs }
    main := .par m.main.withoutSyncs (coordinator counts) }

end ProVerif.Translation
