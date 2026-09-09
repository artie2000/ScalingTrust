/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.Noise.Token

/-!
# Message patterns and handshake patterns

Spec §7.1:

> A *message pattern* is some sequence of tokens from the set
> `("e", "s", "ee", "es", "se", "ss", "psk")`.
>
> A *pre-message pattern* is one of the following sequences of tokens:
> `"e"`, `"s"`, `"e, s"`, empty.
>
> A *handshake pattern* consists of:
> * A pre-message pattern for the initiator …
> * A pre-message pattern for the responder …
> * A sequence of message patterns for the actual handshake messages.
>
> The first actual handshake message is sent from the initiator to the
> responder.  The next message is sent from the responder, the next from the
> initiator, and so on in alternating fashion.

Because directions alternate and the first message is the initiator's, the
direction of a message is a function of its index; we do not store it.
-/

namespace Noise

/-- A message pattern (spec §7.1): a sequence of tokens. -/
abbrev MessagePattern := List Token

/-- A pre-message pattern (spec §7.1).  The spec restricts these to
`[]`, `[e]`, `[s]` and `[e, s]`; the restriction is checked by
`PreMessagePattern.isWellFormed` and enforced by pattern validity. -/
abbrev PreMessagePattern := List KeyKind

namespace PreMessagePattern

/-- Spec §7.1: a pre-message pattern must be one of `[]`, `[e]`, `[s]`,
`[e, s]`. -/
def isWellFormed (p : PreMessagePattern) : Bool :=
  decide (p = [] ∨ p = [KeyKind.e] ∨ p = [KeyKind.s] ∨ p = [KeyKind.e, KeyKind.s])

/-- The four well-formed pre-message patterns. -/
def allWellFormed : List PreMessagePattern := [[], [.e], [.s], [.e, .s]]

theorem isWellFormed_iff (p : PreMessagePattern) :
    isWellFormed p = true ↔ p ∈ allWellFormed := by
  simp [isWellFormed, allWellFormed]

theorem isWellFormed_of_mem {p : PreMessagePattern} (h : p ∈ allWellFormed) :
    isWellFormed p = true := (isWellFormed_iff p).mpr h

/-- Rendering, e.g. `"e, s"`. -/
def toString (p : PreMessagePattern) : String :=
  String.intercalate ", " (p.map KeyKind.toString)

end PreMessagePattern

/-- A handshake pattern (spec §7.1).

The `name` field carries the pattern's name section (spec §8.1), e.g. `"XX"` or
`"IKpsk2"`.  It has no semantic content beyond being hashed into `h` via the
protocol name during `Initialize` (spec §5.3), and equality of patterns ignores
nothing — two patterns with different names are different protocols, which is
precisely the spec's intent (§14, "Protocol names"). -/
structure HandshakePattern where
  /-- The handshake pattern name section, e.g. `"XX"`, `"IKpsk2"` (spec §8.1). -/
  name : String := ""
  /-- Public keys of the initiator already known to the responder (spec §7.1). -/
  initiatorPre : PreMessagePattern := []
  /-- Public keys of the responder already known to the initiator (spec §7.1). -/
  responderPre : PreMessagePattern := []
  /-- The handshake messages, alternating, initiator first. -/
  messages : List MessagePattern
  deriving DecidableEq, Repr, Inhabited

namespace HandshakePattern

/-- The role sending the message at index `i`: the initiator sends the messages
at even indices (spec §7.1, "the first actual handshake message is sent from the
initiator … and so on in alternating fashion"). -/
def senderAt (i : Nat) : Role :=
  if i % 2 == 0 then .initiator else .responder

@[simp] theorem senderAt_zero : senderAt 0 = .initiator := rfl
@[simp] theorem senderAt_one : senderAt 1 = .responder := rfl

theorem senderAt_succ (i : Nat) : senderAt (i + 1) = (senderAt i).other := by
  simp only [senderAt]
  rcases Nat.mod_two_eq_zero_or_one i with h | h <;>
    simp [Nat.add_mod, h, Role.other]

/-- The number of handshake messages. -/
def length (hp : HandshakePattern) : Nat := hp.messages.length

/-- Spec §7.4: a *one-way* handshake pattern consists of a single message, after
which only the initiator may send transport messages.

> Following a one-way handshake the sender can send a stream of transport
> messages …  The second `CipherState` from `Split()` is discarded — the
> recipient must not send any messages using it.
-/
def isOneWay (hp : HandshakePattern) : Bool := hp.messages.length == 1

/-- The roles that may send transport messages after the handshake completes. -/
def transportSenders (hp : HandshakePattern) : List Role :=
  if hp.isOneWay then [.initiator] else [.initiator, .responder]

/-- All tokens occurring anywhere in the handshake messages. -/
def tokens (hp : HandshakePattern) : List Token := hp.messages.flatten

/-- Does this pattern use pre-shared symmetric keys (spec §9)? -/
def usesPsk (hp : HandshakePattern) : Bool := hp.tokens.contains .psk

/-- Does this pattern have any pre-messages? -/
def hasPreMessages (hp : HandshakePattern) : Bool :=
  !hp.initiatorPre.isEmpty || !hp.responderPre.isEmpty

/-- Render a handshake pattern the way the spec prints it, e.g.

```
XX:
  -> e
  <- e, ee, s, es
  -> s, se
```
-/
def render (hp : HandshakePattern) : String :=
  let msgLine (i : Nat) (m : MessagePattern) : String :=
    "  " ++ (senderAt i).arrow ++ " " ++ String.intercalate ", " (m.map Token.toString)
  let preLines : List String :=
    (if hp.initiatorPre.isEmpty then [] else ["  -> " ++ hp.initiatorPre.toString]) ++
    (if hp.responderPre.isEmpty then [] else ["  <- " ++ hp.responderPre.toString]) ++
    (if hp.hasPreMessages then ["  ..."] else [])
  String.intercalate "\n"
    ((hp.name ++ ":") :: (preLines ++ (hp.messages.zipIdx.map (fun p => msgLine p.2 p.1))))

instance : ToString HandshakePattern := ⟨HandshakePattern.render⟩

end HandshakePattern

end Noise
