/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.Noise.Patterns

/-!
# Payload security properties

Spec §7.7 assigns two grades to every handshake and transport payload:

> Each payload is assigned a "source" property regarding the degree of
> authentication of the sender provided to the recipient, and a "destination"
> property regarding the degree of confidentiality provided to the sender.

This file turns the prose definitions into two functions of the context reached
at the point the payload is encrypted, and checks the result against the tables
the specification prints in §7.7 and §18.2.

## Source grades (spec §7.7)

> 0. No authentication. This payload may have been sent by any party, including
>    an active attacker.
> 1. Sender authentication vulnerable to key-compromise impersonation (KCI). The
>    sender authentication is based on a static-static DH ("ss") involving both
>    parties' static key pairs.
> 2. Sender authentication resistant to key-compromise impersonation (KCI). The
>    sender authentication is based on an ephemeral-static DH ("es" or "se")
>    between the sender's static key pair and the recipient's ephemeral key pair.

So grade 2 asks for the DH between the *sender's static* key and the
*recipient's ephemeral* key — `se` when the sender is the initiator and `es`
when the sender is the responder — and grade 1 asks for `ss`.

## Destination grades (spec §7.7)

> 0. No confidentiality. This payload is sent in cleartext.
> 1. Encryption to an ephemeral recipient. … forward secrecy, since encryption
>    involves an ephemeral-ephemeral DH ("ee"). However, the sender has not
>    authenticated the recipient …
> 2. Encryption to a known recipient, forward secrecy for sender compromise
>    only, vulnerable to replay. This payload is encrypted based only on DHs
>    involving the recipient's static key pair.
> 3. Encryption to a known recipient, weak forward secrecy. … encrypted based on
>    an ephemeral-ephemeral DH and also an ephemeral-static DH involving the
>    recipient's static key pair. However, the binding between the recipient's
>    alleged ephemeral public key and the recipient's static public key hasn't
>    been verified by the sender …
> 4. Encryption to a known recipient, weak forward secrecy if the sender's
>    private key has been compromised. … the binding … has only been verified
>    based on DHs involving both those public keys and the sender's static
>    private key …
> 5. Encryption to a known recipient, strong forward secrecy.

The three-way split between 3, 4 and 5 is exactly a question of *how well the
sender has already authenticated the recipient*: it is the best source grade of
any message the sender has so far received.  Grade 3 is "not at all", grade 4 is
"by a KCI-vulnerable `ss`", grade 5 is "by a KCI-resistant ephemeral-static DH".
That is the content of `destGrade`.

## Two errors in the specification's tables

Computing the tables and comparing with what Revision 34 prints turns up two
defects in the §18.2 table for deferred patterns; both are recorded (and
proved) at the end of this file.
-/

namespace Noise

/-! ## Grades -/

/-- One row of a payload-security table: who sent the payload, and its source
and destination grades. -/
structure TableRow where
  /-- The party that sent this payload. -/
  sender : Role
  /-- The source (authentication) grade, 0–2 (spec §7.7). -/
  source : Nat
  /-- The destination (confidentiality) grade, 0–5 (spec §7.7). -/
  dest : Nat
  deriving DecidableEq, Repr, Inhabited

namespace TableRow

/-- Rendering in the style of the specification's tables. -/
def toString (r : TableRow) : String :=
  "  " ++ r.sender.arrow ++ "   " ++ Nat.repr r.source ++ "   " ++ Nat.repr r.dest

instance : ToString TableRow := ⟨TableRow.toString⟩

end TableRow

/-- Has any Diffie–Hellman output been mixed into the chaining key yet?

Spec §7.7 grades measure *Diffie–Hellman derived* guarantees, so a key derived
from a pre-shared key alone still carries destination grade 0; this matches the
grades Noise Explorer reports for PSK patterns such as `NNpsk0`. -/
def Ctx.hasDHOutput (c : Ctx) : Bool := c.ee || c.es || c.se || c.ss

/-- The source (authentication) grade of a payload sent by `sender` in context
`c` (spec §7.7). -/
def sourceGrade (c : Ctx) (sender : Role) : Nat :=
  if c.hasDHOf sender .s .e then 2      -- sender's static × recipient's ephemeral
  else if c.ss then 1                   -- static-static only
  else 0

/-- The destination (confidentiality) grade of a payload sent by `sender` in
context `c`, where `authRecv` is the best source grade among the messages
`sender` has already received from the recipient (spec §7.7). -/
def destGrade (c : Ctx) (sender : Role) (authRecv : Nat) : Nat :=
  if !c.hasDHOutput then 0
  else if !c.ee then 2
  else if c.hasDHOf sender .e .s then   -- sender's ephemeral × recipient's static
    if authRecv = 0 then 3 else if authRecv = 1 then 4 else 5
  else 1

theorem sourceGrade_le_two (c : Ctx) (r : Role) : sourceGrade c r ≤ 2 := by
  unfold sourceGrade
  repeat' split
  all_goals omega

theorem destGrade_le_five (c : Ctx) (r : Role) (n : Nat) : destGrade c r n ≤ 5 := by
  unfold destGrade
  repeat' split
  all_goals omega

/-! ## Walking a pattern -/

/-- The state carried while grading a pattern: the context, plus the best source
grade each party has so far seen on a message it received. -/
structure GradeState where
  /-- The accumulated facts. -/
  ctx : Ctx
  /-- Best source grade of a message the initiator has received. -/
  authInitiator : Nat := 0
  /-- Best source grade of a message the responder has received. -/
  authResponder : Nat := 0
  deriving Repr

namespace GradeState

/-- How well `r` has authenticated its peer so far. -/
def auth : GradeState → Role → Nat
  | st, .initiator => st.authInitiator
  | st, .responder => st.authResponder

/-- Record that `receiver` has received a message with source grade `n`. -/
def record : GradeState → Role → Nat → GradeState
  | st, .initiator, n => { st with authInitiator := max st.authInitiator n }
  | st, .responder, n => { st with authResponder := max st.authResponder n }

end GradeState

/-- The grades of a payload sent by `sender`. -/
def rowFor (c : Ctx) (sender : Role) (authRecv : Nat) : TableRow :=
  { sender, source := sourceGrade c sender, dest := destGrade c sender authRecv }

/-- Grade each handshake message in turn, alternating direction. -/
def gradeWalk (r : Role) : GradeState → List MessagePattern →
    GradeState × List TableRow
  | st, [] => (st, [])
  | st, m :: ms =>
      let c := applyTokens r st.ctx m
      let row := rowFor c r (st.auth r)
      let st' := ({ st with ctx := c }).record r.other row.source
      let res := gradeWalk r.other st' ms
      (res.1, row :: res.2)

namespace HandshakePattern

/-- The state reached after the last handshake message. -/
def gradeFinalState (hp : HandshakePattern) : GradeState :=
  (gradeWalk .initiator { ctx := preCtx hp } hp.messages).1

/-- One row per handshake message. -/
def handshakeRows (hp : HandshakePattern) : List TableRow :=
  (gradeWalk .initiator { ctx := preCtx hp } hp.messages).2

/-- One row per transport direction, in the order the messages occur: the first
transport message is sent by whoever did *not* send the last handshake message.
A one-way pattern has only one transport direction (spec §7.4). -/
def transportRows (hp : HandshakePattern) : List TableRow :=
  let st := hp.gradeFinalState
  if hp.isOneWay then
    [rowFor st.ctx .initiator (st.auth .initiator)]
  else
    let last := senderAt (hp.messages.length - 1)
    let first := last.other
    let r1 := rowFor st.ctx first (st.auth first)
    let st1 := st.record last r1.source
    let r2 := rowFor st.ctx last (st1.auth last)
    [r1, r2]

/-- Every payload of the protocol, graded: the handshake messages followed by
the two transport directions.  This is the un-elided listing. -/
def allRows (hp : HandshakePattern) : List TableRow :=
  hp.handshakeRows ++ hp.transportRows

/-- The last handshake payload sent by `r`, if any. -/
def lastHandshakeRow (hp : HandshakePattern) (r : Role) : Option TableRow :=
  (hp.handshakeRows.reverse).find? (fun row => decide (row.sender = r))

/-- The table the specification prints, applying its elision convention:

> Transport payloads are only listed if they have different security properties
> than the previous handshake payload sent from the same party.

For one-way handshakes the specification prints a single row, because there the
listed properties "apply to the handshake payload as well as transport
payloads"; the elision rule produces exactly that. -/
def specTable (hp : HandshakePattern) : List TableRow :=
  hp.handshakeRows ++
    hp.transportRows.filter (fun row =>
      match hp.lastHandshakeRow row.sender with
      | some prev => decide (prev.source ≠ row.source ∨ prev.dest ≠ row.dest)
      | none => true)

/-- Render the graded table in the style of the specification. -/
def renderTable (hp : HandshakePattern) : String :=
  String.intercalate "\n"
    (hp.name :: (hp.specTable.map TableRow.toString))

end HandshakePattern

/-! ## The specification's tables

`ini` and `res` abbreviate a row sent by the initiator (`->`) and by the
responder (`<-`) respectively. -/

/-- A table row for a payload sent by the initiator. -/
def ini (source dest : Nat) : TableRow := ⟨.initiator, source, dest⟩

/-- A table row for a payload sent by the responder. -/
def res (source dest : Nat) : TableRow := ⟨.responder, source, dest⟩

namespace Patterns

/-- The payload security table of spec §7.7, transcribed verbatim: the one-way
patterns of §7.4 and the twelve fundamental patterns of §7.5. -/
def table77 : List (HandshakePattern × List TableRow) :=
  [ (N,  [ini 0 2]),
    (K,  [ini 1 2]),
    (X,  [ini 1 2]),
    (NN, [ini 0 0, res 0 1, ini 0 1]),
    (NK, [ini 0 2, res 2 1, ini 0 5]),
    (NX, [ini 0 0, res 2 1, ini 0 5]),
    (XN, [ini 0 0, res 0 1, ini 2 1, res 0 5]),
    (XK, [ini 0 2, res 2 1, ini 2 5, res 2 5]),
    (XX, [ini 0 0, res 2 1, ini 2 5, res 2 5]),
    (KN, [ini 0 0, res 0 3, ini 2 1, res 0 5]),
    (KK, [ini 1 2, res 2 4, ini 2 5, res 2 5]),
    (KX, [ini 0 0, res 2 3, ini 2 5, res 2 5]),
    (IN, [ini 0 0, res 0 3, ini 2 1, res 0 5]),
    (IK, [ini 1 2, res 2 4, ini 2 5, res 2 5]),
    (IX, [ini 0 0, res 2 3, ini 2 5, res 2 5]) ]

/-- The payload security table of spec §18.2 for deferred patterns, transcribed
verbatim, *except* for `NX1` and `X1N`, whose printed rows are wrong; see
`NX1_table_arrows_swapped` and `X1N_table_missing_row`. -/
def table182 : List (HandshakePattern × List TableRow) :=
  [ (NK1,  [ini 0 0, res 2 1, ini 0 5]),
    (X1K,  [ini 0 2, res 2 1, ini 0 5, res 2 3, ini 2 5, res 2 5]),
    (XK1,  [ini 0 0, res 2 1, ini 2 5, res 2 5]),
    (X1K1, [ini 0 0, res 2 1, ini 0 5, res 2 3, ini 2 5, res 2 5]),
    (X1X,  [ini 0 0, res 2 1, ini 0 5, res 2 3, ini 2 5, res 2 5]),
    (XX1,  [ini 0 0, res 0 1, ini 2 3, res 2 5, ini 2 5]),
    (X1X1, [ini 0 0, res 0 1, ini 0 3, res 2 3, ini 2 5, res 2 5]),
    (K1N,  [ini 0 0, res 0 1, ini 2 1, res 0 5]),
    (K1K,  [ini 0 2, res 2 1, ini 2 5, res 2 5]),
    (KK1,  [ini 0 0, res 2 3, ini 2 5, res 2 5]),
    (K1K1, [ini 0 0, res 2 1, ini 2 5, res 2 5]),
    (K1X,  [ini 0 0, res 2 1, ini 2 5, res 2 5]),
    (KX1,  [ini 0 0, res 0 3, ini 2 3, res 2 5, ini 2 5]),
    (K1X1, [ini 0 0, res 0 1, ini 2 3, res 2 5, ini 2 5]),
    (I1N,  [ini 0 0, res 0 1, ini 2 1, res 0 5]),
    (I1K,  [ini 0 2, res 2 1, ini 2 5, res 2 5]),
    (IK1,  [ini 0 0, res 2 3, ini 2 5, res 2 5]),
    (I1K1, [ini 0 0, res 2 1, ini 2 5, res 2 5]),
    (I1X,  [ini 0 0, res 2 1, ini 2 5, res 2 5]),
    (IX1,  [ini 0 0, res 0 3, ini 2 3, res 2 5, ini 2 5]),
    (I1X1, [ini 0 0, res 0 1, ini 2 3, res 2 5, ini 2 5]) ]

/-! ## Agreement with the specification -/

/-- **The computed payload security grades reproduce the table of spec §7.7**
for all three one-way patterns and all twelve fundamental patterns, including
the specification's convention for eliding transport rows. -/
theorem table77_correct : ∀ e ∈ table77, e.1.specTable = e.2 := by decide

/-- **The computed payload security grades reproduce the table of spec §18.2**
for twenty-one of the twenty-three deferred patterns.  The remaining two are
`NX1` and `X1N`, whose printed rows are defective; see below. -/
theorem table182_correct : ∀ e ∈ table182, e.1.specTable = e.2 := by decide

/-- Every pattern the specification names is covered by one of the two tables,
or is a PSK pattern (§9.4 prints no grades for those), or is `XXfallback`. -/
theorem tables_cover_fundamental :
    ∀ hp ∈ oneWay ++ fundamental, hp.name ∈ table77.map (fun e => e.1.name) := by decide

/-! ### Two defects in Revision 34 of the specification

Both are in the §18.2 table of security properties for deferred patterns. -/

/-- The `NX1` rows as Revision 34 prints them:
```
NX1
  -> e                      0                0
  <- e, ee, s               0                1
  -> es                     0                3
  ->                        2                1
  <-                        0                5
```
-/
def NX1_printed : List TableRow :=
  [ini 0 0, res 0 1, ini 0 3, ini 2 1, res 0 5]

/-- **Defect 1.** The arrows on the two transport rows of the `NX1` table are
interchanged.

The printed table gives source grade 2 to a transport payload sent by the
*initiator*, but `NX1` is an `N`-pattern: the initiator has no static key at
all, so no message it sends can ever be authenticated.  The row with source
grade 2 must be the responder's, and it must come first, because `NX1`'s last
handshake message is the initiator's.  Swapping the two arrows yields exactly
the computed table. -/
theorem NX1_table_arrows_swapped :
    NX1.specTable ≠ NX1_printed ∧
    NX1.specTable = [ini 0 0, res 0 1, ini 0 3, res 2 1, ini 0 5] := by
  constructor <;> decide

/-- The `X1N` rows as Revision 34 prints them:
```
X1N
  -> e                      0                0
  <- e, ee                  0                1
  -> s                      0                1
  <- se                     0                3
  ->                        2                1
```
-/
def X1N_printed : List TableRow :=
  [ini 0 0, res 0 1, ini 0 1, res 0 3, ini 2 1]

/-- **Defect 2.** The `X1N` table omits its last row.

After the responder receives the initiator's first transport payload — which has
source grade 2, since `se` has by then been performed — the responder's own
transport payloads gain strong forward secrecy, moving from `(0, 3)` to
`(0, 5)`.  By the specification's own elision convention that row differs from
the responder's last handshake payload and so must be listed.  Noise Explorer
(Figure 7 of the paper) likewise reports six graded payloads for `X1N`. -/
theorem X1N_table_missing_row :
    X1N.specTable ≠ X1N_printed ∧
    X1N.specTable = X1N_printed ++ [res 0 5] := by
  constructor <;> decide

end Patterns
end Noise
