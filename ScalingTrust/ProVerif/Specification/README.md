# ProVerif's calculus and its semantics

A deep embedding of the process calculus behind ProVerif, for the trace
semantics of `../TraceSemantics/` to be measured against: its syntax, the
operational semantics of its processes, the meaning of its queries, and the
theorems that the trace semantics gets them right.

The reference is `../Writeup/Semantics.tex`: its §2 for the syntax and the
semantics, its §3.1 for the denotation and its §3.2 for the theorems. Its
sources are those of the folder README's "Sources". The semantics is the
ProVerif manual's (Appendix B of `../Reference/proverif-manual.pdf`, Figures
B.1 and B.2), restricted to the fragment with terms with effects (`new`, `if`,
`let` and `event` inside terms) and function macros: no patterns other than
variables, tables, predicates, phases, synchronisation or natural numbers. The
adversary and the properties of queries are the survey's Definitions 3.1–3.5
(`../Reference/BlanchetFnTPS16.pdf`), to which the manual refers for them,
extended to the manual's terms with effects as said below. The write-up says
where it departs from the sources, as in reading their rules modulo `=_E`. The
modules follow the write-up and record every further deviation in their
docstrings; the ones that shape the design are listed below.

## Modules

| Module | Contents |
| --- | --- |
| `ProVerif.Specification.Syntax` | Terms, expressions and processes of the write-up's Definition "Source syntax"; rewrite rules of destructors and the matching of their arguments; a `Model`, the write-up's Definition "Model" with the conditions (D), (R1) and (R2), and the theory of the trace semantics it instantiates; substitution for the bound variables |
| `ProVerif.Specification.Patterns` | Patterns as abbreviations, the write-up's Definition "Patterns": `Pat`, its variables, tests and leaves, and `Process.letPat`, `Process.inpPat` and `Expr.letPat`, the processes and expressions of the fragment that `let pat = D in P else Q`, `in(N, pat); P` and `let pat = D in D₁ else D₂` abbreviate, for any `Target` with `let`, `if` and substitution; the rule `dataRule` of a data constructor's projections and `Model.IsData` |
| `ProVerif.Specification.Semantics` | Rewriting by rules, any matching rule deciding under (D); the labelled step relations on term configurations (Figure B.1) and on configurations (Figure B.2), weak traces; steps and runs of processes beside others, of expressions in contexts and of the arguments of a `k`-ary context; the survey's Definitions 3.1–3.5 and the write-up's "Deduction, knowledge", "Satisfaction", the facts of queries, events, attacker and message facts, equalities and disequalities and `before`, holding at steps of a trace, and "Correspondences", `Model.Satisfies`, the general queries of `TraceSemantics/Query.lean` read on the traces of the manual |
| `ProVerif.Specification.Invariance` | Equality modulo `E` of terms, expressions and processes, and the invariance of runs under it: a step on a term `M' =_E M` counts as a step on `M` |
| `ProVerif.Specification.Denotation` | Destructors as functions, the projections denoting the standard operations and the boolean destructors yielding a boolean or an argument, and the model's `Attacker` instance; the computation of an expression and the denotation of a process in `TraceSemantics`; substitution commutes with denotation |
| `ProVerif.Specification.Adequacy` | The write-up's Lemma "Expressions" and Theorem "Adequacy": the traces of the computation of an expression with a continuation are its runs followed by traces of the continuation; a closed process denotes its weak traces; the Lemma "Evaluation" for effect-free expressions |
| `ProVerif.Specification.Attacks` | Runs of `N_pub`-adversaries are attacker traces; attacker traces are replayed by adversary processes |
| `ProVerif.Specification.Correspondence` | The write-up's Theorems "Attacks", "Secrecy" and "Correspondences", the last for `F ⇝ H` and for `F ⇝ false`; the attackers of the calculus and of the trace semantics know the same messages after a trace |

Everything is proved; nothing is admitted.

## Design decisions

* **Binders by index.** A process is indexed by its number of bound variables,
  as Mathlib's `BoundedFormula` is, and so is an expression; `in`, `new` and
  `let` bind the last variable, and an environment extends with `Fin.snoc`.
  The manual's names are atoms; here `new` binds a variable, which the step
  replaces by the created name `ν_k`, a variable `.var (.inl k)` of the term.
  Free names are nullary constructors, as in the trace semantics, so an
  adversary's names being in `N_pub` is its symbols being public.
* **Event symbols are private constructors of the messages.** The manual
  declares event symbols `ev` apart from the constructors, so that
  `ev(M₁, …, Mₙ)` is not a term. A `Model` takes them as a signature `Ev` of
  their own; `event` applies one to expressions, a query fact to terms, and
  the event step records the event as the message `ev(M₁, …, Mₙ)`, as the
  write-up's §3 has it: the constructors of the messages, `Sig.cons F Ev`, are
  the declared ones, the event symbols and the data symbols, and an event
  symbol is private (`Model.Public`) and free (`Model.theory`). The terms and
  the rewrite rules of the calculus are over that signature too, so an event
  symbol may occur in a term or in a rule, which the manual's grammar does not
  allow and the translator never emits; nothing here depends on its absence.
* **Adversaries over terms with effects.** The survey defines its
  `N_pub`-adversaries for its own calculus. Here an adversary is any process of
  the fragment whose names and symbols are public and that has no event, inside
  its terms too (`Model.Adversary`, `Model.PubExpr`), so it may use `new`, `if`
  and `let` in a term: the natural extension. It may also write `fail`, which
  the input language lacks but which `if false then true` with its `else`
  omitted evaluates to (manual §4.1.4), as the survey's clause (Rfail) gives the
  adversary `fail` outright (§3.2.2). The private names, which the survey's
  Definition 3.3 chooses with the model, are the declared `N_priv`.
* **Terms have two spellings.** An expression is a term, a constructor or
  destructor applied to expressions, `fail`, or one of the manual's enriched
  forms. The write-up's grammar derives `f(M₁, …, Mₙ)` both as a term and as
  an application of `f` to terms, and here the two are different trees,
  `term` and `ctor f (term Mᵢ)`; both are terms (`Expr.IsTerm`), so may-fail
  terms, the values of expressions (`Expr.IsValue`, `Val`), and neither has a
  step, as the manual reads an application of a constructor to terms as a
  term. A constructor steps only when an argument is `fail` (`TStep.ctor_fail`).
  The result of a destructor and the terms that a communication or a `let`
  substitute are spelled with `term`.
* **The model is the declaration data.** `Model` is the write-up's Definition
  "Model" without the process, which the theorems take separately: the
  equations, the rules of each declared destructor, and the public
  constructors and destructors, with the conditions (R1) and (R2) of the
  write-up's §3 as fields, and (D) of its §2: the destructors declared with
  `;` are marked, `Model.plain`, and the manual's requirement that their
  rules be deterministic (§3.1.1) is the field `Model.det`, under which any
  rule that matches decides (`Model.rewrites_of_matching`), so that the list
  of rules rewrites as the set does. The theory of the trace semantics is derived from
  it (`Model.theory`): its free symbols are the declared constructors at the
  root of no equation and the event symbols, and (R1) gives the condition (H).
  (R2) is what makes the matching of a rule unique (`Rule.Matching.eval_eq`).
* **Data symbols built in.** A model's theory is over its declared constructors
  and the event symbols, `Sig.withEv F Ev`, but the terms of the calculus are
  over `Sig.cons F Ev`, those with the tuples and the booleans, and its
  destructors over `Sig.withBuiltin G`, the declared ones with the built-in
  ones: the projections of tuples, each with the rule
  `proj k i (tuple k (x₀, …)) → xᵢ`, and the boolean destructors `equal`,
  `not`, `and` and `or` with the survey's rules (`Builtin.rules`), which
  ProVerif's `=`, `<>`, `not`, `&&` and `||` stand for. So `true` is
  `StdOps.tt`, the messages `A.Msg` are `A.theory.withData.Msg` of the trace
  semantics with their `StdOps` instance, and the attacker is
  `Attacker.ofDecls`, as a translated model declares it. The
  data symbols and the built-in destructors are public (`Model.Public`,
  `Model.PublicDt`): the Attacks theorem needs every operation of the attacker
  to be a public expression, and every public expression to evaluate to
  something the attacker derives. `Model.dtorFun_proj` gives the latter for a
  projection, which denotes the standard projection, and `Model.dtorFun_bool`
  for a boolean destructor, whose result is `true`, `false` or an argument, so
  that it is not among the attacker's operations.
* **Everything on messages.** The semantics is read on messages, terms modulo
  `E`, as the write-up reads the manual's rules modulo `=_E`: a closed term
  denotes its class and rules match messages. A process is a term, so a
  communication, `let` and the rewrite of a destructor substitute any term of
  the message received, of the value or of the result, and the invariance
  theorem shows that the runs of a configuration depend only on its processes
  modulo `E`. The denotation needs no bijection `ι` between names and indices:
  a created name is its index.
* **One labelled semantics, two step relations.** The manual's transition
  relations and the write-up's labelled semantics are a step relation on term
  configurations, `TStep`, labelled `τ`, `new k` or `event m`, and one on
  configurations, `Step`, labelled by `Option (Act A.Msg)`. The manual's
  transitions are the steps whose label is not an offer: the communication is
  the step labelled `comm`, `new` the step labelled `new` and `event` the step
  labelled `event`; a trace of the manual is a run whose labels are closed.
  The `out` and `inp` steps are the offers of a process to its environment,
  which the manual has no rule for. The manual's evaluation contexts are the
  context constructors of the two relations, one per hole: the arguments of a
  constructor, a destructor or an event are evaluated from left to right, the
  channel of an output before its message, and the evaluation goes on after
  an earlier argument, or the channel, has failed, as the manual's contexts
  allow. Where the manual has no rule, as for `out(fail, M)`, `if fail` or
  `event ev(fail)`, a process blocks. A run of the arguments of a `k`-ary
  context (`ArgRuns`) is the common form of the runs of the three.
* **Computations in the continuation monad.** An expression denotes, in an
  environment, a computation of `Cont (Proc A.Msg) (Option A.Msg)`, exactly
  what the translator emits: the arguments of an application or an event run
  in order (`seqFin`), `new` is `Proc.fresh`, `event` is `Proc.emit` of the
  event message, `if` and `let` are case analyses on the result of their
  first expression. A process runs
  the computations of its expressions with the rest of the process as the
  continuation (`Cont.runWith`), and `Proc.nil` where it blocks. The adequacy
  of expressions, the write-up's Lemma "Expressions", relates the traces of a
  computation with a continuation to the runs of the term configuration
  followed by a trace of the continuation on the may-fail term reached.
* **Rules with explicit variables.** The manual writes the rules of a destructor
  as a set of conditional rules with side formulas, generated from the ordered
  `otherwise` form in which they are declared; `Rule` keeps the ordered form,
  and the write-up's Definition "Rewrite rules" says the two define the same
  rewriting. A rule is that definition's: its arguments and its right-hand
  side are may-fail terms, its ordinary and may-fail variables are indexed by
  `ℕ`, and every variable of its right-hand side occurs in an argument.
  Matching is equality of values, so a term accepts only a message, `fail`
  only `fail` and a may-fail variable anything. Two matchings against a rule
  whose terms are over the free symbols, which (R2) gives for the rules of a
  model, yield the same right-hand side, so the function of the write-up's
  Definition "Destructors from rewrite rules" that a destructor denotes is
  well defined.
* **Patterns are abbreviations.** The manual's patterns in `in` and `let`, a
  variable, `_`, `=D`, a tuple or a data constructor applied to patterns, are
  not syntax here: `Process.letPat` and the others of `Patterns.lean` are the
  processes and expressions of the fragment they abbreviate, the write-up's
  Definition "Patterns", binding the term matched, evaluating every test into
  a tuple, binding each leaf to the projections reading it and comparing the
  test leaves, with every failure taking the `else` branch; the manual's
  `matches` is defined exactly when none fails. Binders being indices, the
  abbreviation renames the variables of the body to those of their leaves.
  The translator compiles patterns the same way, with `Tuple.ofMsg` for the
  projections of a tuple.
* **Queries.** `Model.Satisfies` is the write-up's Definition
  "Correspondences": a query of `TraceSemantics/Query.lean`, several facts
  before `==>` and a hypothesis with `&&`, `||`, `false`, nested
  correspondences and injective facts, read on the manual's traces with the
  facts holding at steps, `Model.SatisfiedAt`: an event or a message at the
  step of the action, an attacker fact once the attacker knows the term, and
  `F before e` while the event has not occurred, the fact that the phase
  compilation produces. `corr_iff` relates it to the property the translation
  of a query states, `Proc.Satisfies` of the denotation, through
  `satisfiedAt_iff`: the facts hold at the same steps in the two semantics.
* **Attacker facts are knowledge.** The survey defines correspondences for
  event facts only (Definition 3.5). An attacker fact in a query is read as the
  manual reads it (§4.3.1), "the attacker knows `M`": `Model.Derives` is the
  Dolev–Yao deduction with the public constructors and destructors,
  `Model.knowledge` what the attacker has intercepted along a trace, every
  message communicated on a channel it could derive, and `Model.Knows` their
  composition. `Model.knows_iff` proves it the knowledge of the trace
  semantics, which is defined on its own.
* **Secrecy is reachability.** `Model.Preserves` says that after no trace
  against an adversary does the attacker know `M`: the reachability of
  `attacker(M)`, which is what ProVerif decides for `query attacker(M)`. This
  is a deliberate deviation from the survey's Definitions 3.2 and 3.3, to which
  the manual refers, where secrecy is the absence of an output of `M` on a
  name in `N_pub`. The two agree when `N_pub` is nonempty, since the attacker
  can output what it knows on a public name; but `N_pub` holds the names
  declared `free` or `channel` and not the public constants, which Appendix B
  files among the constructors, and a model may declare its public channel as
  a constant, as the Noise Explorer models do with `const pub:channel`. Such
  a model has an empty `N_pub`, so the survey's definition makes every term
  secret in it while ProVerif finds the attacks on it: the strict reading is
  inconsistent with the tool, and the definition follows the tool. The
  write-up's Definition "Satisfaction, secrecy" and its remark record this.
* **The Attacks theorem.** The write-up states it as the Lean proves it: in
  `attacks_sound` and `attacks_complete` the trace of the manual against an
  adversary is the attack itself, and conversely, and `Model.knows_iff` says
  that the two attackers know the same messages after a trace. Secrecy and
  Correspondences follow from the three. The write-up's hypothesis that `P₀`
  and the secret mention no created name is not needed.
