/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.Noise.Patterns

/-!
# The pattern derivation rules of §18.3

Appendix 18.3 of the specification states that the one-way, fundamental and
deferred handshake patterns are not arbitrary: they are *generated* from their
names by a small rule system.

> First, populate the pre-message contents as defined by the pattern name.
>
> Next populate the initiator's first message by applying the first rule from
> the below table which matches.  Then delete the matching rule and repeat this
> process until no more rules can be applied.  If this is a one-way pattern, it
> is now complete.
>
> Otherwise, populate the responder's first message in the same way.  Once no
> more responder rules can be applied, then switch to the initiator's next
> message and repeat this process, switching messages until no more rules can be
> applied by either party.
>
> **Initiator rules:**
> 1. Send `"e"`.
> 2. Perform `"ee"` if `"e"` has been sent, and received.
> 3. Perform `"se"` if `"s"` has been sent, and `"e"` received.  If initiator
>    authentication is deferred, skip this rule for the first message in which
>    it applies, then mark the initiator authentication as non-deferred.
> 4. Perform `"es"` if `"e"` has been sent, and `"s"` received.  If responder
>    authentication is deferred, skip this rule for the first message in which
>    it applies, then mark the responder authentication as non-deferred.
> 5. Perform `"ss"` if `"s"` has been sent, and received, and `"es"` has been
>    performed, and this is the first message, and initiator authentication is
>    not deferred.
> 6. Send `"s"` if this is the first message and initiator is `"I"` or one-way
>    `"X"`.
> 7. Send `"s"` if this is not the first message and initiator is `"X"`.
>
> **Responder rules:**
> 1. Send `"e"`.
> 2. Perform `"ee"` if `"e"` has been sent, and received.
> 3. Perform `"se"` if `"e"` has been sent, and `"s"` received.  If initiator
>    authentication is deferred, skip this rule for the first message in which
>    it applies, then mark the initiator authentication as non-deferred.
> 4. Perform `"es"` if `"s"` has been sent, and `"e"` received.  If responder
>    authentication is deferred, skip this rule for the first message in which
>    it applies, then mark the responder authentication as non-deferred.
> 5. Send `"s"` if responder is `"X"`.

This file implements those rules and proves that they reproduce, exactly, all
thirty-eight patterns of §7.4, §7.5 and §18.1.

Two points the prose leaves implicit, which the derivation makes precise:

* "Delete the matching rule" is modelled by the context itself.  A rule's effect
  records a fact — a public key sent, a DH performed — and each rule is guarded
  by the absence of that fact, so it can fire at most once.  The four DH rules
  are shared between the two tables, since a handshake pattern contains each DH
  token at most once (spec §7.3 rule 3).
* Skipping a deferred rule must last for the rest of the message, not just one
  application; otherwise clearing the deferral flag would let the very same
  rule fire again immediately.
-/

namespace Noise

/-- The letter of a pattern name (spec §7.4, §7.5). -/
inductive Letter where
  /-- No static key. -/
  | N : Letter
  /-- Static key Known to the peer. -/
  | K : Letter
  /-- Static key Xmitted to the peer. -/
  | X : Letter
  /-- Static key Immediately transmitted (initiator only). -/
  | I : Letter
  deriving DecidableEq, Repr, Inhabited

namespace Letter

/-- Rendering. -/
def toString : Letter → String
  | .N => "N" | .K => "K" | .X => "X" | .I => "I"

end Letter

/-- A handshake pattern name, decomposed (spec §7.5, §7.6).  For a one-way
pattern the single letter is `initiator`; the recipient's static public key is
always pre-known, so `responder` is `K`. -/
structure PatternName where
  /-- Is this one of the one-way patterns of §7.4? -/
  oneWay : Bool := false
  /-- The initiator's letter. -/
  initiator : Letter
  /-- Is the initiator's authentication DH deferred (the `1` after the first
  letter)? -/
  initiatorDeferred : Bool := false
  /-- The responder's letter. -/
  responder : Letter := .K
  /-- Is the responder's authentication DH deferred (the `1` after the second
  letter)? -/
  responderDeferred : Bool := false
  deriving DecidableEq, Repr, Inhabited

namespace PatternName

/-- The name as the specification writes it, e.g. `"X1K1"`. -/
def toString (nm : PatternName) : String :=
  if nm.oneWay then nm.initiator.toString
  else
    nm.initiator.toString ++ (if nm.initiatorDeferred then "1" else "") ++
    nm.responder.toString ++ (if nm.responderDeferred then "1" else "")

instance : ToString PatternName := ⟨PatternName.toString⟩

end PatternName

/-- One step of the derivation. -/
inductive DeriveStep where
  /-- Append this token to the message under construction. -/
  | emit (t : Token) : DeriveStep
  /-- The initiator's authentication DH is deferred: skip it for the rest of
  this message and clear the deferral. -/
  | deferInitiator : DeriveStep
  /-- The responder's authentication DH is deferred: skip it for the rest of
  this message and clear the deferral. -/
  | deferResponder : DeriveStep
  /-- No rule applies. -/
  | stop : DeriveStep
  deriving DecidableEq, Repr

/-- The state threaded through the derivation. -/
structure DeriveState where
  /-- What has been sent and performed so far.  This is what "delete the
  matching rule" amounts to. -/
  ctx : Ctx
  /-- Is the initiator's authentication DH still deferred? -/
  iDeferred : Bool
  /-- Is the responder's authentication DH still deferred? -/
  rDeferred : Bool
  /-- Has the initiator's authentication rule already been skipped in the
  message currently under construction? -/
  iSkipped : Bool := false
  /-- Has the responder's authentication rule already been skipped in the
  message currently under construction? -/
  rSkipped : Bool := false
  deriving Repr

/-- The initiator's rule table (spec §18.3), returning the first rule that
applies. -/
def initiatorStep (nm : PatternName) (st : DeriveState) (firstMessage : Bool) : DeriveStep :=
  let c := st.ctx
  if !c.initE then .emit Token.e
  else if c.initE && c.respE && !c.ee then .emit Token.ee
  else if c.initS && c.respE && !c.se && !st.iSkipped then
    if st.iDeferred then .deferInitiator else .emit Token.se
  else if c.initE && c.respS && !c.es && !st.rSkipped then
    if st.rDeferred then .deferResponder else .emit Token.es
  else if c.initS && c.respS && c.es && !c.ss && firstMessage && !st.iDeferred then
    .emit Token.ss
  else if firstMessage && !c.initS &&
      (nm.initiator == Letter.I || (nm.oneWay && nm.initiator == Letter.X)) then
    .emit Token.s
  else if !firstMessage && !c.initS && nm.initiator == Letter.X && !nm.oneWay then
    .emit Token.s
  else .stop

/-- The responder's rule table (spec §18.3). -/
def responderStep (nm : PatternName) (st : DeriveState) : DeriveStep :=
  let c := st.ctx
  if !c.respE then .emit Token.e
  else if c.initE && c.respE && !c.ee then .emit Token.ee
  else if c.respE && c.initS && !c.se && !st.iSkipped then
    if st.iDeferred then .deferInitiator else .emit Token.se
  else if c.respS && c.initE && !c.es && !st.rSkipped then
    if st.rDeferred then .deferResponder else .emit Token.es
  else if nm.responder == Letter.X && !c.respS then .emit Token.s
  else .stop

/-- Build one message by applying rules until none matches.  `fuel` bounds the
number of tokens; seven is more than any rule table can produce. -/
def buildMessage (nm : PatternName) (r : Role) (firstMessage : Bool) :
    Nat → DeriveState → MessagePattern → DeriveState × MessagePattern
  | 0, st, acc => (st, acc)
  | fuel + 1, st, acc =>
      match (match r with
             | .initiator => initiatorStep nm st firstMessage
             | .responder => responderStep nm st) with
      | .stop => (st, acc)
      | .deferInitiator =>
          buildMessage nm r firstMessage fuel { st with iDeferred := false, iSkipped := true } acc
      | .deferResponder =>
          buildMessage nm r firstMessage fuel { st with rDeferred := false, rSkipped := true } acc
      | .emit t =>
          buildMessage nm r firstMessage fuel
            { st with ctx := applyToken r st.ctx t } (acc ++ [t])

/-- Build successive messages, alternating direction. -/
def buildMessages (nm : PatternName) : Nat → Role → Nat → DeriveState → List MessagePattern
  | 0, _, _, _ => []
  | n + 1, r, index, st =>
      let (st', m) :=
        buildMessage nm r (index == 0) 8 { st with iSkipped := false, rSkipped := false } []
      m :: buildMessages nm n r.other (index + 1) st'

/-- Drop the trailing messages that no rule contributed to. -/
def dropTrailingEmpty (ms : List MessagePattern) : List MessagePattern :=
  (ms.reverse.dropWhile List.isEmpty).reverse

/-- The pre-messages a name calls for.  The initiator announces its static
public key exactly when its letter is `K`; the responder announces its static
public key when its letter is `K`, and always in a one-way pattern, where the
recipient's key must be known for the sender to encrypt anything. -/
def derivePre (nm : PatternName) : PreMessagePattern × PreMessagePattern :=
  ((if nm.initiator == Letter.K then [KeyKind.s] else []),
   (if nm.oneWay || nm.responder == Letter.K then [KeyKind.s] else []))

/-- **The derivation of §18.3.**  Generate a handshake pattern from its name. -/
def derive (nm : PatternName) : HandshakePattern :=
  let pre := derivePre nm
  let c := pre.2.foldl (fun c k => c.setKey .responder k)
    (pre.1.foldl (fun c k => c.setKey .initiator k) Ctx.empty)
  let st : DeriveState :=
    { ctx := c, iDeferred := nm.initiatorDeferred, rDeferred := nm.responderDeferred }
  let msgs := buildMessages nm 8 .initiator 0 st
  { name := nm.toString
    initiatorPre := pre.1
    responderPre := pre.2
    messages := if nm.oneWay then msgs.take 1 else dropTrailingEmpty msgs }

namespace Patterns

open Letter

/-- A one-way pattern name. -/
def oneWayName (l : Letter) : PatternName := { oneWay := true, initiator := l }

/-- An interactive pattern name. -/
def name (i : Letter) (id : Bool) (r : Letter) (rd : Bool) : PatternName :=
  { initiator := i, initiatorDeferred := id, responder := r, responderDeferred := rd }

/-- Each named pattern paired with the name it should be derived from. -/
def derivationTable : List (PatternName × HandshakePattern) :=
  [ (oneWayName .N, N), (oneWayName .K, K), (oneWayName .X, X),
    -- fundamental (§7.5)
    (name .N false .N false, NN), (name .N false .K false, NK),
    (name .N false .X false, NX), (name .X false .N false, XN),
    (name .X false .K false, XK), (name .X false .X false, XX),
    (name .K false .N false, KN), (name .K false .K false, KK),
    (name .K false .X false, KX), (name .I false .N false, IN),
    (name .I false .K false, IK), (name .I false .X false, IX),
    -- deferred (§18.1)
    (name .N false .K true, NK1), (name .N false .X true, NX1),
    (name .X true .N false, X1N), (name .X true .K false, X1K),
    (name .X false .K true, XK1), (name .X true .K true, X1K1),
    (name .X true .X false, X1X), (name .X false .X true, XX1),
    (name .X true .X true, X1X1), (name .K true .N false, K1N),
    (name .K true .K false, K1K), (name .K false .K true, KK1),
    (name .K true .K true, K1K1), (name .K true .X false, K1X),
    (name .K false .X true, KX1), (name .K true .X true, K1X1),
    (name .I true .N false, I1N), (name .I true .K false, I1K),
    (name .I false .K true, IK1), (name .I true .K true, I1K1),
    (name .I true .X false, I1X), (name .I false .X true, IX1),
    (name .I true .X true, I1X1) ]

/-- **The derivation rules of §18.3 generate every listed pattern.**

All three one-way patterns of §7.4, all twelve fundamental patterns of §7.5 and
all twenty-three deferred patterns of §18.1 are exactly what the rule system
produces from their names — including their names, pre-messages and message
patterns. -/
theorem derivationTable_correct : ∀ e ∈ derivationTable, derive e.1 = e.2 := by decide

/-- The table covers all thirty-eight patterns. -/
theorem derivationTable_length : derivationTable.length = 38 := by decide

/-- Every derived pattern is valid, which is a check on the rules themselves
rather than on the transcription. -/
theorem derived_valid : ∀ e ∈ derivationTable, (derive e.1).isValid = true := by decide

end Patterns
end Noise
