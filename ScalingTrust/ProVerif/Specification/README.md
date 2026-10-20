# ProVerif's calculus and its semantics

A deep embedding of the process calculus behind ProVerif, for the trace
semantics of `../TraceSemantics/` to be measured against: its syntax, the
operational semantics of its processes, the meaning of its queries, and the
theorems that the trace semantics gets them right.

The reference is `../Writeup/Semantics.tex`: its §2 for the syntax and the
semantics, its §3.1 for the denotation and its §3.2 for the theorems. The
write-up restates, for the fragment of ProVerif's input language with terms
with effects (`new`, `if`, `let` and `event` inside terms) and function macros,
the semantics of the ProVerif manual (Appendix B of
`../Reference/proverif-manual.pdf`, Figures B.1 and B.2), restricted to that
fragment: no patterns other than variables, tables, predicates, phases,
synchronisation or natural numbers. The manual defines no adversary and no
security property, so the write-up takes those from Blanchet's survey (§3.1–3.3
of `../Reference/BlanchetFnTPS16.pdf`), whose semantics (§2.4) the manual's
extends. The write-up says where it departs from the two, as in reading their
rules modulo `=_E`. The modules follow the write-up and record every further
deviation in their docstrings; the ones that shape the design are listed below.

## Modules

| Module | Contents |
| --- | --- |
| `ProVerif.Specification.Syntax` | Terms, expressions and processes of the write-up's Definition "Source syntax"; rewrite rules of destructors; a `Model`; substitution for the bound variables |
| `ProVerif.Specification.Semantics` | Matching and rewriting by rules; the labelled step relations on term configurations (Figure B.1) and on configurations (Figure B.2), weak traces; steps and runs of processes beside others and of expressions in contexts; the survey's Definitions 3.1–3.5 and the write-up's "Satisfaction" and "Correspondences between facts" |
| `ProVerif.Specification.Invariance` | Equality modulo `E` of terms, expressions and processes, and the invariance of runs under it: a step on a term `M' =_E M` counts as a step on `M` |
| `ProVerif.Specification.Denotation` | Destructors as functions, the projections denoting the standard operations and the boolean destructors yielding a boolean or an argument, and the model's `Attacker` instance; the computation of an expression and the denotation of a process in `TraceSemantics`; substitution commutes with denotation |
| `ProVerif.Specification.Adequacy` | The write-up's Lemma "Expressions" and Theorem "Adequacy": the traces of the computation of an expression with a continuation are its runs followed by traces of the continuation; a closed process denotes its weak traces; the Lemma "Evaluation" for effect-free expressions |
| `ProVerif.Specification.Attacks` | Runs of `N_pub`-adversaries are attacker traces; attacker traces are replayed by adversary processes; an adversary intercepting the protocol's communications |
| `ProVerif.Specification.Correspondence` | The write-up's Theorems "Attacks", "Secrecy" and "Correspondences" |

Everything is proved; nothing is admitted.

## Design decisions

* **Binders by index.** A process is indexed by its number of bound variables,
  as Mathlib's `BoundedFormula` is, and so is an expression; `in`, `new` and
  `let` bind the last variable, and an environment extends with `Fin.snoc`.
  The manual's names are atoms; here `new` binds a variable, which the step
  replaces by the created name `ν_k`, a variable `.var (.inl k)` of the term.
  Free names are nullary constructors, as in the trace semantics, and `N_pub`
  is the set of public ones.
* **Terms are leaves.** An expression is a term, a constructor or destructor
  applied to expressions, `fail`, or one of the manual's enriched forms. The
  manual reads an application of a constructor to terms as a term; here the
  two are different trees, and the application steps by `τ` to the term it
  denotes (`TStep.ctor`), as a destructor application steps to its result. The
  may-fail terms, the values of expressions, are the terms and `fail`
  (`Expr.IsValue`, `Val`).
* **The model is the instantiated one.** The write-up's model is the survey's
  data, and its §3 instantiates the trace semantics from it under the
  conditions (R1) and (R2). `Model` carries that instantiation: a `Theory`
  over the declared constructors, with the free symbols and the condition (H),
  the rules of the declared destructors, and the public constructors and
  destructors. The theorems hold for any free symbols satisfying (H), not only
  those at the root of no equation.
* **Data symbols built in.** A model's theory is over its declared constructors
  `F`, but the terms of the calculus are over `F.withData`, the declared
  constructors with the tuples and the booleans, and its destructors over
  `Sig.withBuiltin G`, the declared ones with the built-in ones: the
  projections of tuples, each with the rule `proj k i (tuple k (x₀, …)) → xᵢ`,
  and the boolean destructors `equal`, `not`, `and` and `or` with the survey's
  rules (`Builtin.rules`), which ProVerif's `=`, `<>`, `not`, `&&` and `||`
  stand for. So `true` is `StdOps.tt`, the messages `A.Msg` are
  `A.withData.Msg` of the trace semantics with their `StdOps` instance, and
  the attacker is `Attacker.ofDecls`, as a translated model declares it. The
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
  constructor or destructor are evaluated from left to right, the channel of
  an output before its message, and the evaluation of an argument goes on
  after an earlier one has failed, as the manual's contexts allow. Where the
  manual has no rule, as for `out(fail, M)` or `if fail`, a process blocks.
* **Computations in the continuation monad.** An expression denotes, in an
  environment, a computation of `Cont (Proc A.Msg) (Option A.Msg)`, exactly
  what the translator emits: the arguments of an application run in order
  (`seqFin`), `new` is `Proc.fresh`, `event` is `Proc.emit`, `if` and `let`
  are case analyses on the result of their first expression. A process runs
  the computations of its expressions with the rest of the process as the
  continuation (`Cont.runWith`), and `Proc.nil` where it blocks. The adequacy
  of expressions, the write-up's Lemma "Expressions", relates the traces of a
  computation with a continuation to the runs of the term configuration
  followed by a trace of the continuation on the may-fail term reached.
* **Rules with explicit variables.** A rule is the write-up's Definition
  "Rewrite rules": its arguments and its right-hand side are may-fail terms,
  its ordinary and may-fail variables are indexed by `ℕ`, its arguments are
  over the free symbols, which is the write-up's (R2) built into the type, and
  every variable of its right-hand side occurs in an argument. Matching is
  equality of values, so a term accepts only a message, `fail` only `fail` and
  a may-fail variable anything. Two matchings against a rule give the same
  right-hand side, so the function of the write-up's Definition "Destructors
  from rewrite rules" that a destructor denotes is well defined.
* **Queries with single facts.** `Model.Satisfies` is the write-up's
  Definition "Correspondences between facts" for one fact on each side, which
  is what `Proc.Corr` of the trace semantics checks.
* **The Attacks theorem.** The write-up states it as lightly as the query
  theorems need, as two correspondences between the traces of the manual
  against adversaries and the attacks: of their events, and, when `N_pub` is
  nonempty, of what a trace outputs publicly and what the attacker knows
  after an attack, each taken over the traces with the same events. The Lean
  proves more, which the constructions give for free: in `attacks_sound` and
  `attacks_complete` the trace of the manual is the attack itself, and in
  `attacks_known` the trace has the same created names and events as the
  attack and outputs the message at its last step. The write-up's form is
  derived from these (`events_sound`, `events_complete`, `known_sound`,
  `known_complete`), and Secrecy and Correspondences are proved from it
  alone, so that they survive a change of the constructions. The write-up's
  hypothesis that `P₀` and the secret mention no created name is not needed.
