# Translating ProVerif models to Lean

A translator from a fragment of ProVerif's input language to Lean source over
`../TraceSemantics/`: the declarations of a model become a message algebra, its
process a `do` block and its queries the security properties they check,
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
`let x = D in P else Q` and `if D = D' then P else Q` or
`if D <> D' then P else Q`; and the queries `F`, `F ==> false` and `F ==> H` for
single facts `F` and `H`, `attacker(M)` or an event, possibly in parentheses,
with variables declared before them. Terms are identifiers and applications,
`(M)` is `M`, and in a process position also the enriched terms of the manual's
§4.1.4: `new a; M`, `event e(M…); M`, `if M = N then M' else M''` or with `<>`,
and `let x = M in M' else M''`, an absent `else` being `fail`.

Not translated: tuples and numerals, patterns other than a variable in `in` and
`let`, booleans and the boolean operators as terms (an `if`, in a process or in
a term, has to compare), may-fail parameters of macros, `let` in equations and
rules, tables, predicates, phases, and queries other than the three above, so
none with `&&`, `||`, `inj-event`, nested correspondences or `secret`. A model
whose symbols include a name the translation uses, listed in `Emit.reserved`,
is rejected too.

The lexer reads identifiers, numerals and symbols, the longest symbol first, and
skips comments, which may nest. ProVerif's reserved words are not identifiers,
and nothing else is reserved. The precedences of processes are the manual's
(§3.1.4): `|` is the one infix form, left-associative, and `!`, `new`, `in`,
`out` and `event` extend to the right as far as possible, so `! P | Q` is
`!(P | Q)`. A parse error names the line and column of the token it is at.

## The recipe

A model is translated piece by piece, types erased as in the survey's semantics.

1. **Free names** (`free a`, `channel a`) become the constructors of an inductive
   type `Free`, and the nullary constructor `Fun.const : Free → Fun 0`; a free
   name `a` is the message `a := .app (.const .a) ![]`. `Theory.Msg.name n` is
   reserved for the nonces that `new` creates.
2. **Constructors** (`fun`, `const`) become the symbols of a signature
   `Fun : ℕ → Type`, and each the function `f (x₀ … : T.Msg) : T.Msg` applying
   it. **Events** are constructors of `Fun` too, private, so that `event e(M)`
   is `Proc.emit (e M)` and the facts of queries are messages. A
   `[typeConverter]` is the identity, as under ProVerif's default
   `ignoreTypes = true`, and gets no symbol.
3. **Equations** (`equation`) become a `Theory Fun` named `T`: the set `E` of
   pairs of raw terms, the variables of each `forall` numbered in order, and
   `free`, true of every symbol at the root of no equation; `heads` is proved by
   `simp`. `T.Msg`, terms modulo `E`, is the message type, and Lean's `=` on it
   is the survey's `=_E`.
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
   may only match on a free symbol. A destructor whose rules have neither a
   may-fail variable nor the pattern `fail` is written on messages and lifted by
   `liftFail` in the algebra; one whose rules match `fail` takes
   `u₀ … : Option T.Msg` directly, and each rule first matches them against
   `some xᵢ`, against `none` for the pattern `fail`, or binds a may-fail
   variable to one.
5. **Public and private** declarations complete `alg : MsgAlgebra Fun`: `pubFun`
   is everything, or `{f | pub n f}` for the predicate `pub`, false of the
   private free names and constructors and of the events; `pubDtors` holds the
   public destructors.
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
   failing term takes no branch (survey §2.5.2), so the term is matched first,
   `t₀`, with `Proc.stop` for `none`, and `if M = N then P else Q` is then a Lean
   `if` on the equation of messages. Variables keep their names, prefixed with
   `_` when nothing uses them. The process never uses `Theory.Msg.name`.
7. **Terms with effects**, the enriched terms, are emitted as the elements of
   the enclosing block that perform their effects, followed by their value,
   which the process then uses as in item 6: `new a; M` is `Proc.fresh`,
   `event e(M…); M` is `Proc.emit`, and `let x = M in M'` with an `M` that
   cannot fail is a Lean `let`. The order and the failure rules are those of
   the manual's Appendix B (Figure B.1), which `../Specification/` does not yet
   cover: the effects of every argument of an application run, left to right,
   before a failure propagates, and so do those of the channel of an output
   before those of its message; an event whose argument fails is not emitted
   and its continuation does not run; a conditional whose condition fails runs
   neither branch; a term evaluation whose term fails runs its `else` branch.
   Where the effects depend on a test, the test and what follows it become a
   sub-block bound to a fresh `tᵢ` by `←`, returning `Option T.Msg` when the
   term may fail: the branches of a conditional or of a term evaluation when
   either has effects, an event whose argument may fail, and a call of a
   function macro with effects on an argument that may fail. Branches without
   effects stay a Lean `if` or `match` on the value. A **function macro**
   (`letfun`) becomes a function of its parameters: to its value, of type
   `T.Msg` or `Option T.Msg`, when its body has no effects, and to a block in
   `Cont (Proc T.Msg)` otherwise, so that a call with effects is bound by `←`.
8. **Queries** become the properties they check, `query₁`, `query₂`, … in order,
   with `attacker(M)` as `Fact.knows M` and `event(e(M))` as `Fact.event (e M)`.
   `query F` and `query F ==> false` both ask that `F` never holds: for
   `attacker(M)` this is `system.Secret alg.derive M`, and for an event it is
   written out, `∀ t₀ ∈ system.Attacks alg.derive, ¬ F.Holds alg.derive t₀`;
   `query F ==> H` is `system.Corr alg.derive F H`, the survey's Def. 3.5. The
   facts are functions of a valuation `σ : Varsᵢ → T.Msg` of the query's
   variables, the inductive type `Varsᵢ`, and a never-holds query with variables
   is quantified over `σ`.
9. **Theorems**, with generated proofs:
   * each equation on messages, `equationᵢ (x y : T.Msg) : l = r`, by
     instantiating `Theory.satisfies_msg` at the raw equation and evaluating
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
   * `system_mem_tree : system ∈ Descriptive.tree (Act T.Msg)`, by `aesop`
     unfolding the function macros, the process macros and `system`.

Every binder the translation introduces carries a subscript, `x₀`, `a₀`, `t₀`,
`u₀`, `σ`, and in proofs `h₀`, `hv₀`, `e₀`, `f₀`, `i₀`, `n₀`, which no ProVerif
identifier has, so it never captures a name of the model.
