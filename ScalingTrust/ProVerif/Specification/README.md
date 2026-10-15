# ProVerif's calculus and its semantics

A deep embedding of the process calculus behind ProVerif, for the trace
semantics of `../TraceSemantics/` to be measured against: its syntax, the
operational semantics of its processes, the meaning of its queries, and the
theorems that the trace semantics gets them right.

The reference is `../Writeup/Semantics.tex`: its §1.3 for the syntax and the
denotation, its §2 for the semantics and the theorems. The write-up restates
the semantics of Blanchet's survey (§2.4, §2.5.1 and §3.1–3.3 of
`../Reference/BlanchetFnTPS16.pdf`) and says where it departs from it, as in
reading the survey's definitions modulo `=_E`. The modules follow the write-up
and record every further deviation in their docstrings; the ones that shape the
design are listed below. The ProVerif manual gives its own semantics of the full
input language, Appendix B of `../Reference/proverif-manual.pdf`, with tables,
phases and synchronisations; it is not the reference for now, and whether to
move to it is a question to return to.

## Modules

| Module | Contents |
| --- | --- |
| `ProVerif.Specification.Syntax` | Terms, expressions and processes of the write-up's Definition "Source syntax"; rewrite rules of destructors; a `Model`; substitution for the bound variables |
| `ProVerif.Specification.Semantics` | Matching and rewriting by rules, evaluation `D ⇓ U`, configurations and the labelled step relation, weak traces; the survey's Definitions 3.1–3.5 and the write-up's "Satisfaction" and "Correspondences between facts" |
| `ProVerif.Specification.Denotation` | Destructors as functions and the model's `MsgAlgebra`; the denotation of expressions and processes in `TraceSemantics`; the Evaluation lemma; substitution commutes with denotation |
| `ProVerif.Specification.Correspondence` | The theorems of the write-up's §2.2: Adequacy, Attacks, Secrecy and Correspondences |

## Status

The syntax, the semantics and the denotation are complete, with the Evaluation
lemma (`eval_iff`) and the substitution lemma (`Process.denote_inst`) proved.
The second part of Adequacy, that the weak traces of a union of multisets are
the parallel composition of those of the parts (`traces_add`), is proved, from
the composition and decomposition of runs (`runs_add`, `Runs.split`). Secrecy
(`secret_iff`) and Correspondences (`corr_iff`) are proved from the Attacks
theorem. The first part of Adequacy (`denote_eq_traces`) and the Attacks
theorem (`attacks_sound`, `attacks_complete`, `attacks_known`) are stated and
not yet proved.

## Design decisions

* **Binders by index.** A process is indexed by its number of bound variables,
  as Mathlib's `BoundedFormula` is; `in`, `new` and `let` bind the last
  variable, and an environment extends with `Fin.snoc`. The survey's names are
  atoms; here `new` binds a variable, which (Red Res) replaces by the created
  name `ν_k`, a variable `.var (.inl k)` of the term. Free names are nullary
  constructors, as in the trace semantics, and `N_pub` is the set of public
  ones.
* **Everything on messages.** The semantics is read on messages, terms modulo
  `E`, as the write-up reads the survey's definitions modulo `=_E`: a closed
  term denotes its class, rules match messages, and the survey's `D ⇓ U` is a
  relation on may-fail messages that the Evaluation lemma shows total and
  functional. A process is a term, so (Red I/O') and (Red Eval 1) substitute
  any term of the message received or of the value. The denotation needs no
  bijection `ι` between names and indices: a created name is its index.
* **One labelled semantics.** The survey's reduction and the write-up's
  labelled semantics are one step relation labelled by `Option (Act A.Msg)`.
  The survey's reduction is a step whose label is not an offer: (Red I/O') is
  the step labelled `comm`, (Red Res) the step labelled `new` and (Red Event)
  the step labelled `event`; a trace of the survey is a run whose labels are
  closed. The `out` and `inp` steps are the offers of a process to its
  environment, which the survey has no rule for.
* **Rules with explicit variables.** A rule's ordinary and may-fail variables
  are indexed by `ℕ`, its patterns are over the free symbols (the write-up's
  (R2)) and every variable of its right-hand side occurs in its patterns, the
  write-up's Definition "Destructors from rewrite rules". Two matchings against
  a rule give the same right-hand side, so the destructor it defines is a
  function.
* **Queries with single facts.** `Model.Satisfies` is the write-up's
  Definition "Correspondences between facts" for one fact on each side, which
  is what `Proc.Corr` of the trace semantics checks.
