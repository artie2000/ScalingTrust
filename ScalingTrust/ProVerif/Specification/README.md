# ProVerif's calculus and its semantics

A deep embedding of the process calculus behind ProVerif, for the trace
semantics of `../TraceSemantics/` to be measured against: its syntax, the
operational semantics of its processes, the meaning of its queries, and the
proofs that the trace semantics gets them right. Nothing is formalised here
yet.

The reference is `../Writeup/Semantics.tex`: its §1.3 for the syntax and the
denotation, its §2 for the semantics and the theorems. The write-up restates
the semantics of Blanchet's survey (§2.4, §2.5.1 and §3.1–3.3 of
`../Reference/BlanchetFnTPS16.pdf`) and says where it departs from it, as in
reading the survey's definitions modulo `=_E`. The modules here are to follow
the write-up and to record every further deviation, from the write-up or from
the survey, in their docstrings. The ProVerif manual gives its own semantics of
the full input language, Appendix B of `../Reference/proverif-manual.pdf`, with
tables, phases and synchronisations; it is not the reference for now, and
whether to move to it is a question to return to.

* **Syntax.** The write-up's Definition "Source syntax": terms, expressions
  with destructors and `fail`, and processes with `0`, `out`, `in`, `|`, `!`,
  `new`, `let`, `if` and `event`, types erased.
* **Operational semantics.** The write-up's §2.1: evaluation of expressions
  by the rewrite rules of destructors, and reduction of configurations, a pair
  of name sets and a multiset of closed processes, by the rules (Red Nil) to
  (Red Event), taken modulo `=_E`.
* **The attacker and the queries.** The write-up's Definitions "Survey,
  Definitions 3.1–3.5", "Satisfaction" and "Correspondences between facts": an
  `N_pub`-adversary is a closed process over the public names and symbols
  without events, a trace outputs a term publicly or executes an event, and
  secrecy and correspondence quantify over every adversary and every trace.
* **The trace denotation.** The write-up's Definition "Translation": the map
  from a process of the syntax to a process of the trace semantics, expressions
  evaluated to may-fail messages and each construct sent to the constructors of
  `ProVerif.TraceSemantics.Process`.
* **The correspondence theorems.** The write-up's §2.2: evaluation agrees with
  the denotation of expressions (Evaluation), the denotation of a process is
  its set of weak traces (Adequacy), every attack in the trace semantics is an
  execution against some adversary and conversely (Attacks), and the two
  notions of secrecy and of correspondence coincide under the stated
  hypotheses (Secrecy, Correspondences).
