# Translating Tamarin models to Lean

A translator from a fragment of Tamarin's input language to Lean source over
`../TraceSemantics/`, through `Rewriting.lean` here, which reads a labelled
multiset rewriting system as a process of the trace semantics: the signature of
a model becomes a type of messages with its attacker, each rule the set of its
instances, the system the process of its rules, and each restriction and lemma
the property it states, following the recipe below. The algebra of a model, its
functions, equations and destructors, is the algebra of a ProVerif model whose
events are the facts, so that part of the output is produced by the ProVerif
translator in `../Translation/`, which this one imports; the names, rules,
restrictions and lemmas are its own. A translated model is ordinary Lean against
the API of the trace semantics and of `Rewriting.lean`.

Nothing is proved about the translation: `Rewriting.lean` defines the semantics
it targets, and no correspondence with Tamarin's own semantics is stated. The
deviations from Tamarin that the recipe records are where such a correspondence
would need care.

## Modules

| Module | Contents |
| --- | --- |
| `ProVerif.TamarinTranslation.Rewriting` | Multiset rewriting as a process: a `Step`, what an instance of a rule does; the runs of a system of rules and its process `Rules.proc`, prefix-closed; the atoms of trace formulas, `ActionAt` and `KnowsAt` |
| `ProVerif.TamarinTranslation.Model` | The abstract model: terms, facts, rules, formulas, restrictions and lemmas, with their printing and the renaming of identifiers |
| `ProVerif.TamarinTranslation.Parser` | The lexer and the parser of the fragment, over the tokens and token parsers of `../Translation/`: `Lexer.lex` and `parse` |
| `ProVerif.TamarinTranslation.Emit` | The recipe: Lean commands for a model, assembled by `emitFile`; `translate` runs the whole translation |
| `ProVerif.TamarinTranslation.Main` | The entry point |
| `Examples/` | `FirstExample.spthy`, the initial example of the Tamarin manual, and `Fragment.spthy`, the rest of the fragment, with their translations, which `ScalingTrust.ProVerif` imports so that the build checks them |

## Running it

```sh
lake build ScalingTrust.ProVerif.TamarinTranslation.Emit
lake env lean --run ScalingTrust/ProVerif/TamarinTranslation/Main.lean Model.spthy Model.lean
```

The output is a module in the namespace named after the output file, importing
`ScalingTrust.ProVerif.TamarinTranslation.Rewriting`. As for the ProVerif
translator, it runs under `lean --run` rather than as a `lake exe`, since it
imports Mathlib's notations to quote and print them. Translation errors carry
the line and column of the model. `Main.lean` is the one module of the folder
that `ScalingTrust.ProVerif` does not import, since its `main` would clash with
the ProVerif translator's; it is compiled whenever the translator runs.

The two examples were produced by

```sh
lake env lean --run ScalingTrust/ProVerif/TamarinTranslation/Main.lean ScalingTrust/ProVerif/TamarinTranslation/Examples/FirstExample.spthy ScalingTrust/ProVerif/TamarinTranslation/Examples/FirstExample.lean
```

and likewise for `Fragment`; run the same after changing the translator.

## The fragment

A theory `theory Name begin … end` with the declarations `builtins`, among
`hashing`, `symmetric-encryption`, `asymmetric-encryption`, `signing`,
`revealing-signing` and `diffie-hellman`; `functions`, as `f/n` with the
attribute `[private]`; `equations`; `rule`, with a `let` block, attributes, a
`(modulo …)` clause and fact annotations, which are skipped; `restriction`, or
`axiom`; and `lemma`, with attributes and `all-traces` or `exists-trace`. Terms
are variables `x`, `~x`, `$x` and `#i`, also written `x:msg`, `x:fresh`,
`x:pub` and `i:node`, public constants `'c'`, applications, pairs `<M, …>`,
and `M^N` with the `diffie-hellman` builtin. Facts are `F(M, …)` and `!F(M,
…)`, with `Fr`, `In` and `Out` reserved. Formulas are `T`, `F`, `F(M) @ i`,
`K(M) @ i`, `i < j`, `i = j`, `M = N`, `not`, `&`, `|`, `==>` and `<=>`, which
bind as in the manual, and `All` and `Ex` over sorted variables.

Not translated: the builtins `xor`, `multiset`, `bilinear-pairing`,
`natural-numbers` and the rest; `*`, `+`, `XOR`, natural numbers and fresh
constants `~'c'`; typed function declarations; rule variants and diff rules;
`macros`, `predicates`, `options`, `heuristic`, `tactic`, `configuration`,
processes and anything else of SAPIC; `last` and the subterm relation `<<`; a
fact named `T` or `F`; proofs after lemmas. A lemma or restriction mentioning
`KU` or `KD`, as the sources lemmas do, is skipped with a note in the output.

The lexer reads identifiers, numerals and symbols, the longest symbol first, and
skips `/* … */` comments, which may nest, and `//` comments; the quoted formula
of a lemma is its tokens between two `"`. Tamarin's keywords are not
identifiers, and nothing else is reserved.

## The recipe

An identifier of the model that is a name the translation uses unqualified,
`Emit.reserved`, is first renamed by appending primes until it is free, and the
definition of a renamed symbol says so in its docstring. A fact, a rule, a
restriction and a lemma are defined under the namespaces `Fact`, `Rule`,
`Restriction` and `Lemma`, since Tamarin lets a rule and a fact share a name;
one of them may not have the name of a function, which its body would read as
itself.

1. **Names.** The public names are strings: `Free := String` and the
   constructor `Fun.const : Free → Fun 0` of the ProVerif translator make
   `pubName a : T.Msg` the public name `a`, which the attacker always knows, so
   that `'c'` is `pubName "c"` and a public variable `$x` ranges over `String`.
   A fresh variable `~x` ranges over `ℕ`, the index of the name `nonce x`, which
   is `Theory.Msg.name x`.
2. **Functions and facts** become the constructors of `Fun`, the functions as
   the ProVerif translator's constructors and the facts as its events, so that
   a fact is a message `Fact.F x₀ …` and the fact symbols are private. `true`
   and `false` are the booleans of the trace semantics and get no symbol. A pair
   `<M, N>` is the 2-tuple `((m, n) : T.Msg)`, with `<M, N, P>` being
   `<M, <N, P>>`, and `fst` and `snd` are its projections, defined when a rule
   uses them. `M^N` is `exp m n`.
3. **Equations.** An equation whose two sides have the same root symbol is an
   equation of the theory. Any other is a rewrite rule of the symbol at the root
   of its left-hand side, which is then a destructor with those rules as a set,
   checked deterministic as a ProVerif `reduc` declared with `;` is; so
   `sdec(senc(m, k), k) = m` makes `sdec` a destructor, a function to
   `Option T.Msg`, and `kdf(x, y) = kdf(y, x)` is an equation. The signature,
   the theory `T₀` and its extension `T` by the data symbols, the constructor
   functions, the equation theorems, the destructors with their graph theorems
   and the `Attacker` instance are items 2 to 5 of the ProVerif recipe
   (`../Translation/README.md`), the attacker having the public functions and
   destructors besides the public names and the standard operations. Two
   deviations: where Tamarin's theory has the inverses and the multiplication
   of `diffie-hellman`, the builtin is read as `exp` with the one equation
   `(x^y)^z = (x^z)^y`; and where Tamarin's term algebra keeps an application
   such as `sdec(c, k)` that reduces to nothing as a term, a destructor fails,
   so a step whose action or conclusion applies one fails and does not happen.
4. **Rules.** A rule `rule N: [ … ] --[ … ]-> [ … ]` is the set of its instances,
   `Rule.N : Rules T.Msg := {s₀ | ∃ vars, … ∧ s₀ = { … }}`: for every value of
   its variables, in order of first occurrence, with a fresh one an index and a
   public one a string, the `Step` with the facts of its premises, `consumed`
   when linear and `persistent` when persistent, the messages of its `In`
   premises as `inputs`, the indices of its `Fr` premises as `fresh`, its action
   facts as `actions`, the messages of its `Out` conclusions as `outputs` and
   the facts of its other conclusions as `produced`, each field omitted when
   empty. A variable of an action or a conclusion must occur in a premise unless
   it is public, which a rule chooses freely. A destructor application in an
   action or a conclusion, `adec(request, ~ltkS)`, is bound to a variable `v₀`,
   the same for the same application, with the conjunct
   `adec request (nonce ltkS) = some v₀`; in a premise it is rejected, since
   a premise is a pattern. The set ranges over messages, so a pattern is matched
   modulo the equations and a repeated variable is an equality, with nothing
   further to do.
5. **The system.** `channel : T.Msg := pubName "net"` is the one channel, a
   public name, so that the network is the attacker; `rules` is the union of
   the rules and `system : Proc T.Msg := Rules.proc channel rules`, with
   `system_mem_tree` from `Rules.proc_mem_tree`. A step performs its segment on
   the channel: its inputs, its names, one `event` whose message is the tuple
   of its action facts, and its outputs.
6. **Restrictions.** `Restriction.N (t₀ : Trace T.Msg) : Prop` is the formula
   read on `t₀`, and `Restrictions t₀` their conjunction, when there are any.
7. **Lemmas.** `Lemma.N : Prop` is `∀ t₀ ∈ system.Attacks, Restrictions t₀ → φ`
   for `all-traces` and `∃ t₀ ∈ system.Attacks, Restrictions t₀ ∧ φ` for
   `exists-trace`. A formula is read on the trace by position: a timepoint
   `#i` is a position `i : ℕ`, `F(M) @ i` is `ActionAt t₀ i (Fact.F m)`, the
   `i`-th action being the event of a step among whose action facts is the
   fact, `i < j` and `i = j` are what they say on positions, `M = N` is the
   equality of messages, modulo the equations, and the connectives are `¬`,
   `∧`, `∨`, `→` and `↔`. `K(M) @ i` is `KnowsAt t₀ i m`: the attacker can
   derive `m` from what it has heard before the `i`-th action. This deviates
   from Tamarin, whose `K(M) @ i` is the adversary sending `M` at `i`; the two
   agree where an adversary that sends whatever it can is the worst case, `K`
   in the hypotheses of an `all-traces` lemma and in the conclusion of an
   `exists-trace` one. A quantifier binds a message as `T.Msg`, a fresh name as
   `ℕ`, read as `nonce x`, a public name as `String`, read as `pubName x`, and
   a timepoint as `ℕ`; a variable nothing uses is prefixed with `_`.

Every binder the translation introduces carries a subscript, `s₀`, `t₀`, `v₀`,
`x₀`, which no Tamarin identifier has, so it never captures a name of the model.

## References

* The Tamarin prover manual, <https://tamarin-prover.com/manual/master/book/>:
  its chapter "Initial Example" is `Examples/FirstExample.spthy`, and its
  chapter "Syntax Description" is the grammar the parser follows. The manual is
  published as a web book and is not kept in `../Reference/`.
