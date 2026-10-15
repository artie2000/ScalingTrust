# Translating ProVerif models to Lean

A translator from ProVerif's input language to Lean source over
`../TraceSemantics/`: the declarations of a model become a message algebra, its
process a `do` block and its queries the security properties they check,
following the recipe below. Nothing is implemented yet.

The translator maps source text straight to Lean source and does not go through
the syntax of `../Specification/`: the point of the shallow embedding is that a
translated model is ordinary Lean, written against the API of the trace
semantics, so that its security properties are proved as ordinary Lean
theorems. It is a program that emits `.lean` files, and it uses existing APIs
wherever they reach, Lean's own for parsing and for producing source, rather
than its own. `ProVerif.TraceSemantics.DH` and
`ProVerif.TraceSemantics.Examples` are the survey's running example translated
by hand along the recipe; the models the translator is for are ProVerif files
such as the two Noise Explorer models in `../Reference/`.

The fragment translated is the one the trace semantics covers: the
`TraceSemantics` README lists what it does not model.

## The recipe

A model is translated piece by piece, types erased as in the survey's semantics.

1. **Free names** (`free a`) become nullary constructors, `DH.Fun.const a` over a
   type of the model's free names; `Theory.Msg.name n` is reserved for the nonces that
   `new` creates.
2. **Constructors** (`fun`, `const`) become the symbols of a signature `F : Sig`.
3. **Equations** (`equation`) become a `Theory F`: the equations `E`, and the
   symbols declared *free*, every symbol that is not at the root of a side of an
   equation (`Theory.heads`, proved by `rfl`). `T.Msg`, terms modulo `E`, is the
   message type, and Lean's `=` on it is the survey's `=_E`.
4. **Destructors** (`reduc`) become Lean functions to `Option T.Msg`, `none`
   being `fail`. Each rewrite rule becomes a function to `Option (Option T.Msg)`:
   `none` when its patterns do not match, `some r` when they do, with `r` the
   right-hand side and `r = none` for `fail`. A pattern over a free symbol is a
   `match` on `Theory.Msg.view` of the argument, a nested pattern a nested match,
   and a repeated variable an equality test. The destructor is the rules in
   order, chained with `<|>` and flattened by `Option.join`, so that the first
   rule that matches decides, even when its result is `fail`, and the result is
   `fail` when none does. With a single rule this is a `match` with a final
   `none`, as in `ProVerif.TraceSemantics.DH`. A destructor whose rules have
   neither a may-fail variable nor the pattern `fail` is written on messages and
   lifted by `liftFail`; one whose rules match `fail`, by a may-fail variable or
   by the constant itself, takes `Option T.Msg` arguments directly.
5. **Public and private** declarations complete a `MsgAlgebra F`, the theory
   extended by `pubFun`, the public constructors, including the public free
   names, and `pubDtors`, the public destructors.
6. **The process** becomes a `do` block in `Cont (Proc T.Msg)`, closed with
   `Proc.run`: `out` is `Proc.send`, `in` is `Proc.recv`, `new` is `Proc.fresh`,
   `event` is `Proc.emit`, `P | Q` is `if ← Proc.fork then P else Q`, `!P` is
   `Proc.repl` followed by `P`, and `0` is `Proc.stop` or the end of the block.
   `Proc.fork` and `Proc.repl` capture the rest of the block: whatever follows
   them runs in both branches, or in every copy, so they end the block, and so
   does a call to a helper that uses them.
   `let x = D in P else Q` is a Lean `match` on the destructor's result, and
   `if M = N then P else Q`, for messages `M` and `N`, a Lean `if` on the
   equation of messages. A condition containing a destructor may fail, and a
   failing condition takes neither branch (survey §2.5.2), so such an `if` is a
   `match` on the condition, `Proc.stop` for `none` and the Lean `if` for
   `some`. The process never uses `Theory.Msg.name`.
7. **Queries** become the security properties they check: `query attacker(M)`
   is `Proc.Secret`, for `M` without nonces; `query F ==> H`, for single facts
   `F` and `H`, is `Proc.Corr F H` with `F` and `H` written as functions of a
   valuation of the query's variables, the survey's Def. 3.5; `attacker(M)` is
   `Fact.knows`.
