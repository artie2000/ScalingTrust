/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.Noise.Pattern

/-!
# Handshake contexts

To state the validity rules of spec §7.3 and §9.3 — and, later, the payload
security properties of §7.7 — we need to track, at each point of a handshake,
*which public keys have been communicated* and *which DH operations have been
performed*.

The Noise Explorer paper (Figure 4) calls this a **context** `Γ` and models it
as a set of prior tokens tagged with the direction that produced them.  Since
there are only finitely many such facts we represent `Γ` concretely as a record
of nine booleans, which makes every validity question decidable by evaluation.

Pre-message keys count as communicated (spec §5.3: `Initialize` calls `MixHash`
on each pre-message public key; and §7.3 says the "no more than one occurrence"
restriction holds "including the pre-messages").
-/

namespace Noise

/-- The set of facts accumulated at a point in a handshake pattern.

This is the Noise Explorer paper's context `Γ` (Figure 4), made concrete. -/
structure Ctx where
  /-- The initiator's ephemeral public key has been communicated. -/
  initE : Bool := false
  /-- The initiator's static public key has been communicated. -/
  initS : Bool := false
  /-- The responder's ephemeral public key has been communicated. -/
  respE : Bool := false
  /-- The responder's static public key has been communicated. -/
  respS : Bool := false
  /-- The `ee` DH has been performed. -/
  ee : Bool := false
  /-- The `es` DH has been performed. -/
  es : Bool := false
  /-- The `se` DH has been performed. -/
  se : Bool := false
  /-- The `ss` DH has been performed. -/
  ss : Bool := false
  /-- A `psk` token has been processed. -/
  psk : Bool := false
  deriving DecidableEq, Repr, Inhabited

namespace Ctx

/-- The empty context: nothing has happened yet. -/
def empty : Ctx := {}

@[simp] theorem empty_initE : empty.initE = false := rfl
@[simp] theorem empty_initS : empty.initS = false := rfl
@[simp] theorem empty_respE : empty.respE = false := rfl
@[simp] theorem empty_respS : empty.respS = false := rfl
@[simp] theorem empty_ee : empty.ee = false := rfl
@[simp] theorem empty_es : empty.es = false := rfl
@[simp] theorem empty_se : empty.se = false := rfl
@[simp] theorem empty_ss : empty.ss = false := rfl
@[simp] theorem empty_psk : empty.psk = false := rfl

/-- Has `r`'s public key of kind `k` been communicated? -/
def hasKey (c : Ctx) : Role → KeyKind → Bool
  | .initiator, .e => c.initE
  | .initiator, .s => c.initS
  | .responder, .e => c.respE
  | .responder, .s => c.respS

/-- Record that `r`'s public key of kind `k` has been communicated. -/
def setKey (c : Ctx) : Role → KeyKind → Ctx
  | .initiator, .e => { c with initE := true }
  | .initiator, .s => { c with initS := true }
  | .responder, .e => { c with respE := true }
  | .responder, .s => { c with respS := true }

/-- Has the DH between the initiator's `a` key and the responder's `b` key been
performed? -/
def hasDH (c : Ctx) : KeyKind → KeyKind → Bool
  | .e, .e => c.ee
  | .e, .s => c.es
  | .s, .e => c.se
  | .s, .s => c.ss

/-- Record that the DH between the initiator's `a` key and the responder's `b`
key has been performed. -/
def setDH (c : Ctx) : KeyKind → KeyKind → Ctx
  | .e, .e => { c with ee := true }
  | .e, .s => { c with es := true }
  | .s, .e => { c with se := true }
  | .s, .s => { c with ss := true }

/-- Has the given token already been processed?  Public-key tokens are
role-dependent and are queried with `Ctx.hasKey` instead, so they report
`false` here. -/
def has (c : Ctx) : Token → Bool
  | .key _ => false
  | .dh a b => c.hasDH a b
  | .psk => c.psk

/-- Record that a `psk` token has been processed. -/
def setPsk (c : Ctx) : Ctx := { c with psk := true }

@[simp] theorem hasKey_setKey_self (c : Ctx) (r : Role) (k : KeyKind) :
    (c.setKey r k).hasKey r k = true := by
  cases r <;> cases k <;> rfl

@[simp] theorem hasDH_setDH_self (c : Ctx) (a b : KeyKind) :
    (c.setDH a b).hasDH a b = true := by
  cases a <;> cases b <;> rfl

@[simp] theorem psk_setPsk (c : Ctx) : c.setPsk.psk = true := rfl

/-!
### How the queries interact with the updates

These are the facts needed to show that the executable protocol tracks the
context: recording a key affects only that party's key of that kind, and
recording a DH or a `psk` affects no key at all.
-/

theorem hasKey_setKey_e_s (c : Ctx) (r r' : Role) :
    (c.setKey r .e).hasKey r' .s = c.hasKey r' .s := by
  cases r <;> cases r' <;> rfl

theorem hasKey_setKey_s_e (c : Ctx) (r r' : Role) :
    (c.setKey r .s).hasKey r' .e = c.hasKey r' .e := by
  cases r <;> cases r' <;> rfl

theorem hasKey_setKey_other_role (c : Ctx) (r : Role) (k k' : KeyKind) :
    (c.setKey r k).hasKey r.other k' = c.hasKey r.other k' := by
  cases r <;> cases k <;> cases k' <;> rfl

@[simp] theorem hasKey_setDH (c : Ctx) (a b : KeyKind) (r : Role) (k : KeyKind) :
    (c.setDH a b).hasKey r k = c.hasKey r k := by
  cases a <;> cases b <;> cases r <;> cases k <;> rfl

@[simp] theorem hasKey_setPsk (c : Ctx) (r : Role) (k : KeyKind) :
    c.setPsk.hasKey r k = c.hasKey r k := by
  cases r <;> cases k <;> rfl

/-!
### Role-relative views

The spec states its processing rules and validity rules from the point of view
of the party performing them.  These helpers translate between that view and
the absolute (initiator-first) encoding of `Token.dh`.
-/

/-- Has the DH between `r`'s own key of kind `own` and the peer's key of kind
`remote` been performed? -/
def hasDHOf (c : Ctx) (r : Role) (own remote : KeyKind) : Bool :=
  c.has (Token.dhOf r own remote)

@[simp] theorem hasDHOf_other (c : Ctx) (r : Role) (a b : KeyKind) :
    c.hasDHOf r.other b a = c.hasDHOf r a b := by
  simp [hasDHOf]

@[simp] theorem hasDHOf_initiator (c : Ctx) (a b : KeyKind) :
    c.hasDHOf .initiator a b = c.hasDH a b := rfl

@[simp] theorem hasDHOf_responder (c : Ctx) (a b : KeyKind) :
    c.hasDHOf .responder a b = c.hasDH b a := rfl

/-- Is a symmetric encryption key established, i.e. is `k` non-empty?

Spec §5.2: `k` becomes non-empty exactly when `MixKey` or `MixKeyAndHash` is
called, which happens exactly at a DH token or a `psk` token
(`InitializeSymmetric` calls `InitializeKey(empty)`). -/
def hasCipherKey (c : Ctx) : Bool :=
  c.ee || c.es || c.se || c.ss || c.psk

/-- The number of DH operations performed so far. -/
def dhCount (c : Ctx) : Nat :=
  (if c.ee then 1 else 0) + (if c.es then 1 else 0) +
  (if c.se then 1 else 0) + (if c.ss then 1 else 0)

end Ctx

end Noise
