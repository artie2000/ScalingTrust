# Translating ProVerif models to Lean

A translator from a fragment of ProVerif's input language to Lean source over
`../TraceSemantics/`: the declarations of a model become a type of messages with
its attacker, its process a `do` block and its queries the security properties they check,
following the recipe below. A translated model is ordinary Lean, written against
the API of the trace semantics, so that its security properties are proved as
ordinary Lean theorems; the translator does not go through the syntax of
`../Specification/`.

The translator reads a model with a parser of its own, written with the parser
combinators of `Std.Internal.Parsec`, and produces source by building Lean syntax
with quotations and printing it with Lean's pretty printer.
`Examples/DenningSacco.lean` is the survey's running example translated by the
program; `../TraceSemantics/Examples/DenningSacco.lean` imports it and proves its query.

## Modules

| Module | Contents |
| --- | --- |
| `ProVerif.Translation.Model` | The abstract model, types erased, and its printing |
| `ProVerif.Translation.Parser` | The lexer and the parser of the fragment, with `Std.Internal.Parsec`: `Lexer.lex` and `parse` |
| `ProVerif.Translation.Compile` | The compilations before the translation, in the order run: `query secret x` to a marking event and a reachability query, tables to private channels and `table` facts to the events of insertions, and phases to tagged channels, tokens and a clock, the facts qualified by a phase read before the clock's events |
| `ProVerif.Translation.Emit` | The recipe: Lean commands for a model, the definitions and the theorems about them, assembled by `emitFile`; `translate` runs the whole translation |
| `ProVerif.Translation.Main` | The entry point |
| `Examples/` | `DenningSacco.pv`, `Features.pv` and `Sync.pv` with their translations, and `NN.lean` and `XX.lean`, the translations of Noise Explorer's `../Reference/NN.noise.active.pv` and `XX.noise.active.pv`; `ScalingTrust.ProVerif` imports the five so that the build checks them, and `../TraceSemantics/Examples/` proves or refutes the queries of `DenningSacco` and `NN` |

## Running it

```sh
lake build ScalingTrust.ProVerif.Translation.Emit
lake env lean --run ScalingTrust/ProVerif/Translation/Main.lean Model.pv Model.lean
```

The output is a module in the namespace named after the output file, importing
`ScalingTrust.ProVerif.TraceSemantics.Query`. The translator runs under
`lean --run` rather than as a `lake exe`: it imports Mathlib's notations to quote
and print them, and an executable would need those modules compiled to native
code. Translation errors carry the line and column of the model.

The two examples were produced by

```sh
lake env lean --run ScalingTrust/ProVerif/Translation/Main.lean ScalingTrust/ProVerif/Translation/Examples/DenningSacco.pv ScalingTrust/ProVerif/Translation/Examples/DenningSacco.lean
```

and likewise for `Features` and `Sync`, and `NN.lean` by

```sh
lake env lean --run ScalingTrust/ProVerif/Translation/Main.lean ScalingTrust/ProVerif/Reference/NN.noise.active.pv ScalingTrust/ProVerif/Translation/Examples/NN.lean
```

and likewise `XX.lean` from `XX.noise.active.pv`. Run the same after changing
the translator.

## The fragment

The declarations `type`, `set`, `channel`, `free`, `const`, `fun` with the
options `private`, `data` and `typeConverter`, a data constructor or a type
converter not being private as the manual requires (§4.1.2), `reduc` and `fun …
reduc … otherwise …` with may-fail variables and the constant `fail`, `equation`,
`event`, `table`, `let` process macros, `letfun` function macros and `query`; the
processes `0`, `P | Q`, `!P`, `new`, `in` and `out`, `event`, macro calls,
`let pat = D in P else Q`, `if D then P else Q`, `insert` and `get` without
`else`, `phase t; P`, `sync t [tag]; P`, and the manual's sugar `yield`,
`foreach i <= N do P`, `! i <= N P`, `x <-R t; P` and `x <- D; P` (§6.8), read
as what it abbreviates; a parameter of a macro declared `or fail`; the queries
of the manual's §4.3.1, `F₁ && … && Fₙ` and `F₁ && … && Fₙ ==> H` with variables
declared before them, the facts `attacker(M)`, `mess(N, M)` and `table(d(M…))`,
each with an optional `phase n`, `event(e(M…))` and `inj-event(e(M…))`,
possibly in parentheses, and `H` built from facts, equalities `M = N` and
disequalities `M <> N` with `&&`, `||`, `false` and nested correspondences `(F
==> H)`, `&&` binding tighter than `||`; `let x = M in` bindings before a
query, a hypothesis or a fact and references `new n` to bound names in query
terms (§6.4); and `secret x` as an item of a `query` declaration. Terms
are identifiers, applications, tuples `(M₁, …, Mₙ)` with `(M)`
being `M`, the booleans `true` and `false`, the comparisons `M = N` and
`M <> N` and the connectives `M && N`, `M || N` and `not(M)`, which bind as in
the manual, and in a process position also the enriched terms of the manual's
§4.1.4: `new a; M`, `event e(M…); M`, `if D then M' else M''` and `let pat = M
in M' else M''`, an absent `else` being `fail`. A pattern is a variable or the
wildcard `_`, an equality test `=M`, a tuple of patterns or a `[data]`
constructor applied to patterns. A rule or an equation may begin with `let x =
M in` bindings, which are substituted. The options after an input or a `get`,
such as `[precise]`, are read and dropped.

Not translated: numerals, tuples and booleans in equations, tuple patterns in
rewrite rules, `get` with an `else` branch, `insert` and `get` inside terms,
predicates, `sync` under a replication or together with phases, and in queries
the inequalities between naturals, `is_nat`, time variables `F@t`, the options
of `secret x` and `public_vars`, and a reference `new n` in the fact before
the arrow of a nested correspondence. An equation with a variable as a side and a rule mentioning a symbol
at the root of an equation are rejected too, the write-up's restrictions (R1)
and (R2) on the models translated, which the manual's semantics does not
impose. A `set` declaration is read and dropped, except that `set ignoreTypes`
with a value other than `true` and `set attacker = passive` are refused, with
an error saying that the typed semantics and the passive attacker are not
implemented.

The lexer reads identifiers, numerals and symbols, the longest symbol first, and
skips comments, which may nest. ProVerif's reserved words are not identifiers,
and nothing else is reserved. The precedences of processes are the manual's
(§3.1.4): `|` is the one infix form, left-associative, and `!`, `new`, `in`,
`out` and `event` extend to the right as far as possible, so `! P | Q` is
`!(P | Q)`. A parse error names the line and column of the token it is at.

## The recipe

Five features are first compiled away on the model, by `Compile.lean`, in this
order and as the write-up's §3 describes:

* `query secret x` (`Model.withoutSecrets`): an event `xₛ(x)` marks each
  binding of `x` by `new`, by an input or by a `let`, in the process and its
  macros, and the query becomes `event(xₛ(x)) && attacker(x)`, the
  reachability query the manual says it is (§4.3.1).
* References `new n` to bound names in queries (`Model.withoutBoundNames`),
  which the parser has made variables of the query, one per occurrence and one
  per `let x = new n in` binding: an event `nᵣ(n)` marks each `new n`, and the
  variable `v` carries the fact `event(nᵣ(v))`, before the arrow when `v` occurs
  there and beside each fact after the arrow that mentions it otherwise, so
  that `v` is any name created at that restriction (§6.4).
* Tables, to private channels, the manual's encoding (§6.7.3)
  (`Model.withoutTables`): a table `d` becomes a private free name, `insert
  d(M₁, …, Mₙ); P` becomes `let rec₀ = (M₁, …, Mₙ) in ((!out(d, rec₀)) | P)`,
  so that a record that fails blocks and the effects of the `Mᵢ` run once, and
  `get d(T₁, …, Tₙ) suchthat M in P` becomes `in(d, (T₁, …, Tₙ)); if M then P`,
  which blocks when no record matches, as a `get` without `else` does. A `get`
  with an `else` branch is refused: an input cannot tell that no record
  matches. When a query has a `table(d(…))` fact, an event `dᵢ(rec₀)` records
  each insertion and the fact becomes `event(dᵢ((M₁, …, Mₙ)))`.
* Synchronisation (`Model.withoutSyncs`), to a coordinator: `sync t [tag]; P`
  becomes `out(barrierₜ, barrierₜ); in(resumeₜ, _); P` on private free names,
  and the coordinator, beside the process, takes one report per tag of level
  `t`, an untagged `sync` counting as a tag of its own and macro calls
  expanded, releases as many processes on `resumeₜ` and goes on to the next
  level, so that the levels run in increasing order and a level completes only
  when every one of its tags is reached (§4.1.7). A `sync` under a replication
  and a model with both synchronisations and phases are refused, as the
  manual forbids them.
* Phases, exactly, to channels tagged by the phase, tokens and a clock
  (`Model.withoutPhases`): with `n` the greatest phase, the model gains the
  public constants `ph₀ … phₙ`, the public free names `clock₁ … clockₙ`, the
  private free names `go₁ … goₙ` and `tok₀ … tokₙ`, the events `tick₁ … tickₙ`
  and, beside its process, the clock `out(tok₀, ph₀) | in(clock₁, _);
  in(tok₀, _); event tick₁; ((!out(go₁, ph₁)) | out(tok₁, ph₁) | in(clock₂,
  _); …)`, which the attacker advances. Under phase `t`, `out(N, M)` is
  `out((N, phₜ), M)`, `in(N, T); P` is `in((N, phₜ), T); in(tokₜ, tokᵥ);
  out(tokₜ, tokᵥ); P`, `phase s; P` is `in(go_s, _); P` with `P` under phase
  `s`, or `0` when `s ≤ t`, and a table's supply is repeated for every phase
  from `t` to `n`; the main process is under phase `0` and a macro under the
  phase of its calls, with a copy `pₜ` for each phase `t` when the calls
  disagree. A fact `attacker(M) phase s` or
  `table(…) phase s` with `s < n` becomes the fact `before tick_{s+1}`, `mess(N,
  M) phase s` becomes `mess((N, ph_s), M)`, and an unqualified `mess` is of
  the last phase. The write-up's §3 argues that the encoding is exact: a
  process left behind by a transition can receive once but never acts on it,
  and its other actions could have run before the transition.

A model is then translated piece by piece, types erased as in the manual's
semantics (Appendix B).
An identifier of the model that is a name the translation uses unqualified,
listed in `Emit.reserved`, such as `T` or `pure`, or that `aesop` reads as a
phase or a builder in a rule list, such as `forward`, is first renamed by
appending primes until it is free, `T'`, and the definition of a renamed symbol
says so in its docstring. An identifier that is a Lean keyword, such as `show`,
is printed escaped, `«show»`, by Lean's pretty printer, which decides by the
token table of the translator's environment; the translator imports the module
a translation imports, so that the table is the translation's. A variable
named like a declared symbol, which ProVerif allows and whose binder would
shadow the symbol's definition, is renamed with primes, `initiator'`.

1. **Free names** (`free a`, `channel a`) become the constructors of an inductive
   type `Free`, and the nullary constructor `Fun.const : Free → Fun 0`; a free
   name `a` is the message `a := .app (.const .a) ![]`. `Theory.Msg.name n` is
   reserved for the nonces that `new` creates.
2. **Constructors** (`fun`, `const`) become the symbols of a signature
   `Fun : ℕ → Type`, and each the function `f (x₀ … : T.Msg) : T.Msg` applying
   it, as the symbol `.inl f` of `Sig.withData Fun`. **Events** are constructors
   of `Fun` too, private, so that `event e(M)` is `Proc.emit (e M)` and the
   facts of queries are messages. A `[typeConverter]` is the identity, as under
   ProVerif's default `ignoreTypes = true`, and gets no symbol. A `[data]`
   constructor `f` of arity `n` gets the projections `f₁, …, fₙ`, destructors
   with the rule `fᵢ(f(y₁, …, yₙ)) → yᵢ`, public when `f` is (manual §4.1.2).
   The data symbols of the trace semantics stand for the tuples and the
   booleans: a tuple `(M₁, …, Mₙ)` is the product `(m₁, …, mₙ) : T.Msg`, a
   message through the coercion of `Tuple`, `true` and `false` are
   `(true : T.Msg)` and `(false : T.Msg)`, and the comparisons and connectives
   are the destructors ProVerif represents them by internally (manual, Appendix
   B), added to the model for the operators it uses: `equal(x, x) → true;
   equal(x, y) → false`, `not(true) → false; not(x) → true`, `and(true, u) → u;
   and(x, u) → false` and `or(true, u) → true; or(x, u) → u`, with `u` may-fail,
   so that `false && fail` is `false`; `M <> N` is `not(equal(M, N))`. They are
   not public, since each result is a boolean or an argument, which the attacker
   has.
3. **Equations** (`equation`) become a `Theory Fun` named `T₀`: the set `E` of
   pairs of raw terms, the variables of each `forall` numbered in order, and
   `free`, true of every symbol at the root of no equation; `heads` is proved by
   `simp`. A free name in an equation is rejected, as ProVerif rejects it
   (manual, Appendix A). `T := T₀.withData` adds the data symbols, the tuples and the
   booleans, and `T.Msg`, terms modulo `E`, is the message type, with its
   `StdOps` instance; Lean's `=` on it is the survey's `=_E`.
4. **Destructors** (`reduc`) become functions to `Option T.Msg`, `none` being
   `fail`. A rule is compiled against the arguments: its top-level variables are
   bound first; then each structured pattern becomes a `match` on
   `Theory.Msg.view` of its scrutinee, nested patterns nested matches, or an
   equality test once all its variables are bound, and a repeated variable an
   equality test, the tests conjoined in one `if`. A single rule is one such
   term with a final `none`. With several
   rules, each becomes a term of type `Option (Option T.Msg)`, `none` when its
   patterns do not match and `some r` when they do, and the destructor is the
   rules in order chained with `<|>` and flattened by `Option.join`, so that the
   first rule that matches decides, even when its result is `fail`. The rules
   of a destructor declared with `;` are a set, which the manual requires to be
   deterministic (§3.1.1), the write-up's (D), and the translation checks it:
   two rules whose patterns unify, a may-fail variable with anything and an
   ordinary variable with anything but `fail`, must give the same result under
   the unifier, compared syntactically, so a pair that agrees only modulo the
   equations is rejected and is to be ordered with `otherwise` instead. A pattern
   mentions no symbol at the root of an equation, the write-up's (R2), and no
   free name, which ProVerif forbids in a rule (Appendix A); `true` and `false`
   are constant patterns, tested by equality, and a tuple pattern in a rule is
   not translated. A
   destructor whose rules have neither a
   may-fail variable nor the pattern `fail` is written on messages and lifted by
   `liftFail` in the algebra; one whose rules match `fail` takes
   `u₀ … : Option T.Msg` directly, and each rule first matches them against
   `some xᵢ`, against `none` for the pattern `fail`, or binds a may-fail
   variable to one.
5. **Public and private** declarations give the attacker, the instance
   `Attacker T.Msg := .ofDecls pubFun pubDtors`: `pubFun` is everything, or
   `{f | pub n f}` for the predicate `pub`, false of the private free names and
   constructors and of the events; `pubDtors` holds the public destructors; the
   standard operations, the tuples, their projections and the booleans, come
   with `Attacker.ofDecls`.
6. **The process** becomes `system : Proc T.Msg`, the `Proc.run` of a `do` block
   in `Cont (Proc T.Msg) Unit`, and each `let` macro a function of its parameters
   to such a block: `out` is `Proc.send`, `in` is `Proc.recv`, `new` is
   `Proc.fresh`, `event` is `Proc.emit`, `P | Q` is `if ← Proc.fork then P else
   Q`, `!P` is `Proc.repl` followed by `P`, and `0` is `Proc.stop` or the end of
   the block. `Proc.fork` and `Proc.repl` capture the rest of the block, so they
   end it, and so does a call to a macro. `let x = M in P` for a message `M` is a
   Lean `let`, and `let x = D in P else Q` for a `D` with a destructor a `match`
   on `D`, `some x` running `P` and `none` running `Q`. A destructor inside the
   terms of `out`, `in`, `event`, a macro call or a condition may fail, and a
   failing term takes no branch (manual, Appendix B), so the term is matched first,
   `t₀`, with `Proc.stop` for `none`. A condition `if D then P else Q` is a Lean
   `if` on a proposition when it can be: `M = N` and `M <> N` are the equality
   of messages and its negation, `&&`, `||` and `not` are `∧`, `∨` and `¬`,
   `true` and `false` are `True` and `False`, and another term `M`, a boolean,
   is `M = true`; the terms of a comparison are matched first, which is the
   failure of the condition, but the operands of `&&` and `||` must be messages
   with neither effects nor failure, since `false && fail` is `false`, and a
   condition with such a connective is otherwise computed as a boolean term,
   by the destructors `and` and `or`, and tested against `true`. The graph
   theorems of `equal`, `not`, `and` and `or` are what justify reading a
   condition as a proposition. A pattern
   other than a variable, in `in` or `let`, is matched by nested `match`es and
   `if`s: a tuple is read with `Tuple.ofMsg` into the binders of its
   components, a `[data]` constructor through its projections, one `match`
   each, and `=M` is an `if` on the equality; `P` runs where every test passes
   and `Q`, or `Proc.stop` after an `in`, where one fails, `Q` bound first as a
   block `q₀` since the pattern can fail at several points. A test `=D` whose
   `D` has effects or may fail is evaluated first, after the term matched and
   before the match, every such test of the pattern in order, as the manual's
   Appendix B has it, and matched, its failure failing the match, before the
   pattern is read with the value in its place. The pattern is not
   matched in an `Option` `do` block, which `aesop` cannot normalise. Variables
   keep their names, prefixed with `_` when nothing uses them. The process never
   uses `Theory.Msg.name`.
7. **Terms with effects**, the enriched terms, are emitted as the elements of
   the enclosing block that perform their effects, followed by their value,
   which the process then uses as in item 6: `new a; M` is `Proc.fresh`,
   `event e(M…); M` is `Proc.emit`, `let x = M in M'` with an `M` that
   cannot fail is a Lean `let`, and a pattern is matched as in item 6. The order
   and the failure rules are those of
   the manual's Appendix B (Figure B.1), which `../Specification/` formalises:
   the effects of every argument of an application run, left to right,
   before a failure propagates, and so do those of the channel of an output
   before those of its message; an event whose argument fails is not emitted
   and its continuation does not run; a conditional whose condition fails runs
   neither branch; a term evaluation whose term fails runs its `else` branch.
   A call of a macro, function or process, is the nested `let`s of the
   write-up's Definition "Source syntax": each argument's effects run and its
   value is tested before the next argument is evaluated, so an argument that
   fails stops the evaluation of those after it. Where the effects depend on a
   test, the test and what follows it become a sub-block bound to a fresh `tᵢ`
   by `←`, returning `Option T.Msg` when the term may fail: the branches of a
   conditional or of a term evaluation when either has effects, an event whose
   argument may fail, and a call of a function macro when an argument may fail
   and the macro or an argument has effects. Branches without effects stay a
   Lean `if` or `match` on the value. A **function macro**
   (`letfun`) becomes a function of its parameters: to its value, of type
   `T.Msg` or `Option T.Msg`, when its body has no effects, and to a block in
   `Cont (Proc T.Msg)` otherwise, so that a call with effects is bound by `←`.
   A parameter declared `or fail`, of a function or a process macro, has the
   type `Option T.Msg`: a call passes the argument's value as it is, `some` of
   a message or the `Option` of a term that may fail, instead of matching it
   first, and inside the body the parameter is a term that may fail, as a
   destructor application is, so `let y = x in P else Q` matches it (manual
   §4.2.3, §4.2.4). This is the write-up's abbreviation of such a call, the
   `else` branch of the parameter's `let` running the rest with `fail` for it.
8. **Queries** become the properties they check, `query₁`, `query₂`, … in order,
   each with its source text as docstring. The facts are functions of a
   valuation `σ : Varsᵢ → T.Msg` of the query's variables, the inductive type
   `Varsᵢ`, the variables standing for bound names, `n₀`, `n₁`, …, among
   them. The basic shapes are stated with the `Fact` of `Security.lean`:
   `query attacker(M)` and `query attacker(M) ==> false` are `system.Secret M`,
   `query event(…)` is written out, `∀ t₀ ∈ system.Attacks, ¬ F.Holds t₀`, both
   quantified over `σ` when the query has variables, and `query F ==> H` with
   one fact on each side, neither injective, is `system.Corr F H`, the
   survey's Def. 3.5. Every other query is `system.Satisfies (X := Varsᵢ)
   ⟨[(inj₁, F₁), …], H⟩` over the facts of `TraceSemantics/Query.lean`, the
   write-up's Definition "Translation of queries": `attacker(M)` is `QFact.knows
   M`, `event(e(M))` and `inj-event(e(M))` are `QFact.event (e M)`, `mess(N,
   M)` is `QFact.mess N M`, `M = N` and `M <> N` are `QFact.eq M N` and
   `QFact.ne M N`, and the compiled `F before e` is `QFact.before F e`;
   the list holds the facts before `==>` with their injectivity, and `H` is
   the hypothesis as a `Hyp`, `.fact inj F`, `.and`, `.or`, `.false` and
   `.corr inj F H`. A fact before `==>` is injective when `H` has an
   `inj-event`: the manual says so of an event (§4.3.1), and the translation
   extends it to the other facts, an injective `attacker(M)` becoming the
   acquisition `QFact.learns M`, which holds at the one step at which the
   attacker comes to know `M`, so that its executions are counted as those of
   an event are; the write-up's Definition "Queries" records the extension.
9. **Theorems**, with generated proofs:
   * each equation on messages, `equationᵢ (x y : T.Msg) : l = r`, by
     instantiating `T₀.withData_satisfies` at the raw equation and evaluating
     both sides with `Term.realize_func_comp`, `comp_vecCons` and
     `comp_vecEmpty`, the lemmas of `TraceSemantics/Term.lean` for this;
   * the graph of each destructor, `g_eq_some : g x₀ … = some m₀ ↔ D₁ ∨ D₂ ∨ …`,
     a disjunct per rule whose result is not `fail`: no earlier rule matches,
     and this one does with that result, `∃ v…, x₀ = p₀ ∧ … ∧ m₀ = r`. A
     variable that is a whole argument, and the result when it is a variable,
     are named by them instead, so that a single rule reads
     `sdec c k = some m ↔ c = senc m k`. On may-fail arguments the conjuncts
     read `u₀ = some p₀`, `u₀ = none` for the pattern `fail`, and a may-fail
     variable is a whole argument. Forwards the proof reads the chain of rules
     with `orElse_eq_some` and `join_eq_some`, then the rule that applies as
     the destructor evaluates it, matching each may-fail argument and the view
     of each matched scrutinee in order, reading the tests and the result off
     the hypothesis and recovering each matched argument from its view with
     `Theory.Msg.eq_app_of_view'`, and refutes each earlier rule by computing;
     backwards it substitutes and computes, with a lemma per earlier rule that
     it matches only as its disjunct says;
   * `p_tree : Cont.Tree (p x …)` for each function macro with effects and
     each process macro `p`, by `aesop` after unfolding `p`, with the rules of
     the primitives, `Cont.Tree.bind` and the others of `Process.lean`, and
     the lemmas of the macros declared before it; its `simp` normalisation is
     off, since on a large block it exceeds its step limit, and `dsimp only`
     in its place reduces the `have` of a `let` in the block, which `aesop`
     neither indexes nor splits through, and its limits on the depth and the
     number of rule applications are off, since the search follows the block
     one safe rule per element and a block of Noise Explorer's `XX` model is
     deeper than the default limit; and then
     `system_mem_tree : system ∈ Descriptive.tree (Act T.Msg)` from
     `Cont.Tree.run` the same way: a macro call ends a block, so a macro
     always runs with the final continuation, as `Proc.run` does. A parameter
     of a macro that its body does not mention is prefixed with `_`.

Every binder the translation introduces carries a subscript, `x₀`, `a₀`, `t₀`,
`u₀`, `σ`, and in proofs `h₀`, `hv₀`, `e₀`, `f₀`, `i₀`, `n₀`, which no ProVerif
identifier has, so it never captures a name of the model.
