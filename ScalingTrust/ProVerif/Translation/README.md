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
program; `ProVerif.TraceSemantics.Examples` imports it and proves its query.

## Modules

| Module | Contents |
| --- | --- |
| `ProVerif.Translation.Model` | The abstract model, types erased, and its printing |
| `ProVerif.Translation.Parser` | The lexer and the parser of the fragment, with `Std.Internal.Parsec`: `Lexer.lex` and `parse` |
| `ProVerif.Translation.Emit` | The recipe: Lean commands for a model, the definitions and the theorems about them, assembled by `emitFile`; `translate` runs the whole translation |
| `ProVerif.Translation.Main` | The entry point |
| `Examples/` | `DenningSacco.pv` and `Features.pv`, and their translations, which `ScalingTrust.ProVerif` imports so that the build checks them |

## Running it

```sh
lake build ScalingTrust.ProVerif.Translation.Emit
lake env lean --run ScalingTrust/ProVerif/Translation/Main.lean Model.pv Model.lean
```

The output is a module in the namespace named after the output file, importing
`ScalingTrust.ProVerif.TraceSemantics.Security`. The translator runs under
`lean --run` rather than as a `lake exe`: it imports Mathlib's notations to quote
and print them, and an executable would need those modules compiled to native
code. Translation errors carry the line and column of the model.

The two examples were produced by

```sh
lake env lean --run ScalingTrust/ProVerif/Translation/Main.lean ScalingTrust/ProVerif/Translation/Examples/DenningSacco.pv ScalingTrust/ProVerif/Translation/Examples/DenningSacco.lean
```

and likewise for `Features`; run the same after changing the translator.

## The fragment

The declarations `type`, `set`, `channel`, `free`, `const`, `fun` with the
options `private`, `data` and `typeConverter`, `reduc` and `fun … reduc …
otherwise …` with may-fail variables and the constant `fail`, `equation`,
`event`, `let` process macros, `letfun` function macros and `query`; the
processes `0`, `P | Q`, `!P`, `new`, `in` and `out`, `event`, macro calls,
`let pat = D in P else Q` and `if D then P else Q`; and the queries `F`,
`F ==> false` and `F ==> H` for single facts `F` and `H`, `attacker(M)` or an
event, possibly in parentheses, with variables declared before them. Terms are
identifiers, applications, tuples `(M₁, …, Mₙ)` with `(M)` being `M`, the
booleans `true` and `false`, the comparisons `M = N` and `M <> N` and the
connectives `M && N`, `M || N` and `not(M)`, which bind as in the manual, and in
a process position also the enriched terms of the manual's §4.1.4: `new a; M`,
`event e(M…); M`, `if D then M' else M''` and `let pat = M in M' else M''`, an
absent `else` being `fail`. A pattern is a variable, an equality test `=M`, a
tuple of patterns or a `[data]` constructor applied to patterns.

Not translated: numerals, tuples and booleans in equations, tuple patterns in
rewrite rules, `=D` patterns with a destructor in `D`, may-fail parameters of
macros, `let` in equations and rules, tables, predicates, phases, and queries
other than the three above, so none with `&&`, `||`, `inj-event`, nested
correspondences or `secret`.

The lexer reads identifiers, numerals and symbols, the longest symbol first, and
skips comments, which may nest. ProVerif's reserved words are not identifiers,
and nothing else is reserved. The precedences of processes are the manual's
(§3.1.4): `|` is the one infix form, left-associative, and `!`, `new`, `in`,
`out` and `event` extend to the right as far as possible, so `! P | Q` is
`!(P | Q)`. A parse error names the line and column of the token it is at.

## The recipe

A model is translated piece by piece, types erased as in the manual's semantics
(Appendix B).
An identifier of the model that is a name the translation uses unqualified,
listed in `Emit.reserved`, such as `T` or `pure`, or that `aesop` reads as a
phase or a builder in a rule list, such as `forward`, is first renamed by
appending primes until it is free, `T'`, and the definition of a renamed symbol
says so in its docstring.

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
   first rule that matches decides, even when its result is `fail`. A pattern
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
   block `q₀` since the pattern can fail at several points. The pattern is not
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
8. **Queries** become the properties they check, `query₁`, `query₂`, … in order,
   with `attacker(M)` as `Fact.knows M` and `event(e(M))` as `Fact.event (e M)`.
   `query F` and `query F ==> false` both ask that `F` never holds: for
   `attacker(M)` this is `system.Secret M`, and for an event it is
   written out, `∀ t₀ ∈ system.Attacks, ¬ F.Holds t₀`;
   `query F ==> H` is `system.Corr F H`, the survey's Def. 3.5. The
   facts are functions of a valuation `σ : Varsᵢ → T.Msg` of the query's
   variables, the inductive type `Varsᵢ`, and a never-holds query with variables
   is quantified over `σ`.
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
   * `p_mem_tree : Proc.run (p x …) ∈ Descriptive.tree (Act T.Msg)` for each
     process macro `p`, by `aesop` unfolding the function macros and `p` and
     using the lemmas of the macros declared before it, and then
     `system_mem_tree : system ∈ Descriptive.tree (Act T.Msg)` the same way from
     `system` and the macros' lemmas: a macro call ends a block, so a macro
     always runs with the final continuation, as `Proc.run` does.

Every binder the translation introduces carries a subscript, `x₀`, `a₀`, `t₀`,
`u₀`, `σ`, and in proofs `h₀`, `hv₀`, `e₀`, `f₀`, `i₀`, `n₀`, which no ProVerif
identifier has, so it never captures a name of the model.
