/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/

/-!
# Tokens, key kinds and roles

This file introduces the smallest pieces of the Noise Protocol Framework's
handshake language: the two *kinds* of Diffie–Hellman key that a party may own,
the two *roles* a party may play, and the *tokens* out of which message patterns
are built.

Reference: *The Noise Protocol Framework*, Revision 34 (2018-07-11), §2.2 and
§7.1; and Kobeissi, Nicolas and Bhargavan, *Noise Explorer: Fully Automated
Modeling and Verification for Arbitrary Noise Protocols* (EuroS&P 2019),
Figure 3.

The spec (§2.2) lists the tokens as

> `"e"`, `"s"`, `"ee"`, `"es"`, `"se"`, `"ss"`

where for the two-letter tokens

> A DH is performed between the initiator's key pair (whether static or
> ephemeral is determined by the first letter) and the responder's key pair
> (whether static or ephemeral is determined by the second letter).

We take that description literally: `Token.dh a b` records that `a` is the
*initiator's* key kind and `b` is the *responder's* key kind.  Consequently a
two-letter token denotes the same DH operation no matter which party is sending
the message that contains it — exactly the invariance the paper highlights.
-/

namespace Noise

/-- The kind of a Diffie–Hellman key pair held by a party: ephemeral or static
(spec §2.2, variables `s`, `e`, `rs`, `re`). -/
inductive KeyKind where
  /-- An ephemeral key pair, freshly generated once per handshake. -/
  | e : KeyKind
  /-- A long-term static key pair. -/
  | s : KeyKind
  deriving DecidableEq, Repr, Inhabited

namespace KeyKind

/-- Rendering as it appears in a handshake pattern. -/
def toString : KeyKind → String
  | .e => "e"
  | .s => "s"

instance : ToString KeyKind := ⟨KeyKind.toString⟩

/-- The two key kinds, in the order used by pre-message patterns. -/
def all : List KeyKind := [.e, .s]

@[simp] theorem mem_all (k : KeyKind) : k ∈ all := by cases k <;> simp [all]

end KeyKind

/-- The role a party plays in a handshake (spec §5.3, the `initiator` boolean).

Note that the spec also introduces *Alice* and *Bob* roles in §7.2, which are
positional rather than functional; we always work with patterns in canonical
(Alice-initiated) form, so role and position coincide. -/
inductive Role where
  /-- The party who sends the first handshake message. -/
  | initiator : Role
  /-- The party who sends the second handshake message. -/
  | responder : Role
  deriving DecidableEq, Repr, Inhabited

namespace Role

/-- The other party. -/
def other : Role → Role
  | .initiator => .responder
  | .responder => .initiator

@[simp] theorem other_other (r : Role) : r.other.other = r := by cases r <;> rfl

@[simp] theorem other_ne (r : Role) : r.other ≠ r := by cases r <;> simp [other]

/-- The arrow the spec uses to introduce a message sent by this role. -/
def arrow : Role → String
  | .initiator => "->"
  | .responder => "<-"

instance : ToString Role := ⟨fun r => match r with | .initiator => "initiator" | .responder => "responder"⟩

/-- Both roles. -/
def all : List Role := [.initiator, .responder]

@[simp] theorem mem_all (r : Role) : r ∈ all := by cases r <;> simp [all]

end Role

/-- A handshake token (spec §7.1).

* `Token.key k` writes a public key of kind `k` into the message.
* `Token.dh a b` performs a DH between the initiator's `a` key and the
  responder's `b` key.
* `Token.psk` mixes in a pre-shared symmetric key (spec §9.2).
-/
inductive Token where
  /-- Transmit a public key: the tokens written `e` and `s`. -/
  | key (k : KeyKind) : Token
  /-- Perform a DH: the tokens written `ee`, `es`, `se`, `ss`.  The first
  argument is the *initiator's* key kind, the second the *responder's*. -/
  | dh (initiatorKey responderKey : KeyKind) : Token
  /-- Mix in the pre-shared symmetric key (spec §9.2). -/
  | psk : Token
  deriving DecidableEq, Repr, Inhabited

namespace Token

/-- The token written `e`. -/
@[match_pattern] abbrev e : Token := .key .e
/-- The token written `s`. -/
@[match_pattern] abbrev s : Token := .key .s
/-- The token written `ee`. -/
@[match_pattern] abbrev ee : Token := .dh .e .e
/-- The token written `es`. -/
@[match_pattern] abbrev es : Token := .dh .e .s
/-- The token written `se`. -/
@[match_pattern] abbrev se : Token := .dh .s .e
/-- The token written `ss`. -/
@[match_pattern] abbrev ss : Token := .dh .s .s

/-- Rendering as it appears in a handshake pattern. -/
def toString : Token → String
  | .key k => k.toString
  | .dh a b => a.toString ++ b.toString
  | .psk => "psk"

instance : ToString Token := ⟨Token.toString⟩

/-- Every token, in a canonical order. -/
def all : List Token := [e, s, ee, es, se, ss, psk]

@[simp] theorem mem_all (t : Token) : t ∈ all := by
  cases t with
  | key k => cases k <;> simp [all]
  | dh a b => cases a <;> cases b <;> simp [all]
  | psk => simp [all]

/-- Is this a DH token? -/
def isDH : Token → Bool
  | .dh _ _ => true
  | _ => false

/-- Is this a public-key token? -/
def isKey : Token → Bool
  | .key _ => true
  | _ => false

/-- The DH token performed between `owner`'s own `own` key and the peer's
`remote` key.

This is the "role-relative" view of a DH token.  Because `Token.dh` stores the
initiator's key kind first, the translation depends on who is speaking:
`dhOf .initiator k₁ k₂ = .dh k₁ k₂` while `dhOf .responder k₁ k₂ = .dh k₂ k₁`.

The spec's processing rules (§5.3) are stated in exactly this role-relative
way: for `"es"` a party calls `MixKey(DH(e, rs))` if it is the initiator and
`MixKey(DH(s, re))` if it is the responder. -/
def dhOf : Role → (own : KeyKind) → (remote : KeyKind) → Token
  | .initiator, a, b => .dh a b
  | .responder, a, b => .dh b a

@[simp] theorem dhOf_initiator (a b : KeyKind) : dhOf .initiator a b = .dh a b := rfl
@[simp] theorem dhOf_responder (a b : KeyKind) : dhOf .responder a b = .dh b a := rfl

/-- A DH token, read from the point of view of either party, is the same token.
Formally: swapping the role and the two key kinds is the identity. -/
@[simp] theorem dhOf_other (r : Role) (a b : KeyKind) :
    dhOf r.other b a = dhOf r a b := by
  cases r <;> rfl

end Token

end Noise
