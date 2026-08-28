/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.Noise.Session
import ScalingTrust.Noise.Transport
import ScalingTrust.Noise.Symbolic
import ScalingTrust.Noise.PatternsValid

/-!
# Running handshakes

`ScalingTrust.Noise.Session` proves that a handshake between two correctly
initialised parties succeeds and leaves them in agreement.  Here we *run* one,
in the symbolic model of `ScalingTrust.Noise.Symbolic`, for every handshake
pattern the specification names.

This is a complement to the theorems rather than a substitute for them.  The
theorems say "if the sender's `WriteMessage` succeeds then the receiver's
`ReadMessage` succeeds and agrees"; running the patterns additionally witnesses
that the senders *do* succeed, so nothing in the development is vacuous.
-/

namespace Noise
namespace Examples

/-- A canonical key setup for running a pattern: distinct private keys for each
of the four possible key pairs, and a pre-shared key. -/
def setupFor (hp : HandshakePattern) : Setup symbolic where
  pattern := hp
  protocolName := "Noise_" ++ hp.name ++ "_25519_ChaChaPoly_SHA256"
  prologue := Sym.empty
  psk := some (Sym.atom 0)
  initiatorStatic := some 1
  initiatorEphemeral := some 2
  responderStatic := some 3
  responderEphemeral := some 4

/-- The ephemeral key pairs the senders generate, and the payloads they send:
one pair per handshake message. -/
def inputsFor (hp : HandshakePattern) : List (Nat × Sym) :=
  (List.range hp.messages.length).map (fun i => (10 + i, Sym.atom (100 + i)))

/-- Equality tests at the symbolic carrier types.  These exist so that instance
search sees `Sym` rather than the unreduced projection `symbolic.Bytes`. -/
def eqS (x y : Sym) : Bool := decide (x = y)
/-- Equality of optional symbolic terms. -/
def eqO (x y : Option Sym) : Bool := decide (x = y)
/-- Equality of lists of symbolic terms. -/
def eqL (x y : List Sym) : Bool := decide (x = y)

/-- Run a pattern end to end and report whether the two parties agreed on
everything that matters: the payloads, the chaining key, the handshake hash, and
both transport keys. -/
def check (hp : HandshakePattern) : Bool :=
  let st := setupFor hp
  match st.state .initiator, st.state .responder with
  | .ok a, .ok b =>
      let inputs := inputsFor hp
      match run a b inputs with
      | .ok (a', b', ps) =>
          eqL ps (inputs.map Prod.snd) &&
          eqS a'.sym.ck b'.sym.ck &&
          eqS a'.sym.h b'.sym.h &&
          eqO a'.sym.split.1.k b'.sym.split.1.k &&
          eqO a'.sym.split.2.k b'.sym.split.2.k &&
          decide (a'.sym.split.1.n = 0) &&
          decide (a'.sym.split.2.n = 0)
      | .error _ => false
  | _, _ => false

/-- **Every handshake pattern the specification names really runs.**

For each of the sixty patterns, both parties complete the handshake in the
symbolic model, each recovers exactly the payloads the other sent, and they
finish with the same chaining key, the same handshake hash, and the same pair of
transport keys. -/
theorem all_patterns_run : ∀ hp ∈ Patterns.all, check hp = true := by decide

theorem XX_runs : check Patterns.XX = true := by decide
theorem IK_runs : check Patterns.IK = true := by decide
theorem IKpsk2_runs : check Patterns.IKpsk2 = true := by decide
theorem XXfallback_runs : check Patterns.XXfallback = true := by decide

/-! ## A worked example: `XX`

```
XX:
  -> e
  <- e, ee, s, es
  -> s, se
```
-/

/-- The initiator's starting state for `XX`. -/
def xxInitiator : Except NoiseError (HandshakeState symbolic) :=
  (setupFor Patterns.XX).state .initiator

/-- The responder's starting state for `XX`. -/
def xxResponder : Except NoiseError (HandshakeState symbolic) :=
  (setupFor Patterns.XX).state .responder

/-- The result of running the whole `XX` handshake. -/
def xxRun : Except NoiseError
    (HandshakeState symbolic × HandshakeState symbolic × List Sym) :=
  match xxInitiator, xxResponder with
  | .ok a, .ok b => run a b (inputsFor Patterns.XX)
  | .error e, _ => .error e
  | _, .error e => .error e

/-- The three payloads arrive exactly as they were sent. -/
theorem xx_payloads :
    xxRun.toOption.map (fun r => (r.2.2 : List Sym))
      = some [.atom 100, .atom 101, .atom 102] := by
  decide

/-- The number of fields in each `XX` message: `-> e` has one public key plus
the payload; `<- e, ee, s, es` has two public keys plus the payload; `-> s, se`
has one public key plus the payload. -/
example : Patterns.XX.messages.map MessagePattern.fieldCount = [2, 3, 2] := by decide

/-! ## The transport phase -/

/-- After the `XX` handshake, the initiator sends two transport messages and the
responder replies with one. -/
def xxChannel : Option (List Sym × List Sym) :=
  match xxRun with
  | .error _ => none
  | .ok (a', b', _) =>
      let ta := Transport.ofSplit .initiator a'.sym.split
      let tb := Transport.ofSplit .responder b'.sym.split
      match ta.writeStream [Sym.atom 200, Sym.atom 201] with
      | .error _ => none
      | .ok (ta₁, cts) =>
        match tb.readStream cts with
        | .error _ => none
        | .ok (tb₁, ps) =>
          match tb₁.writeStream [Sym.atom 300] with
          | .error _ => none
          | .ok (_, cts₂) =>
            match ta₁.readStream cts₂ with
            | .error _ => none
            | .ok (_, ps₂) => some (ps, ps₂)

/-- The transport messages arrive intact and in order, in both directions. -/
theorem xx_channel : xxChannel = some ([.atom 200, .atom 201], [.atom 300]) := by
  decide

/-! ## Inspecting the model

`#eval` these to see the symbolic terms the protocol builds.  They are the
Dolev–Yao terms of `ScalingTrust.Noise.Symbolic`, so for example the shared
chaining key of `XX` visibly contains the three Diffie–Hellman outputs
`dhOut 2 10`, `dhOut 3 10` and `dhOut 1 11`, hashed in order.
-/

/-- The pattern, as the specification prints it. -/
def render (hp : HandshakePattern) : String := hp.render

-- #eval IO.println (render Patterns.XX)
-- #eval IO.println (render Patterns.IKpsk2)
-- #eval (Patterns.all.map (fun hp => (hp.name, check hp)))
-- #eval xxRun.toOption.map (fun r => r.1.sym.ck)
-- #eval IO.println (Patterns.XX.renderTable)
-- #eval xxChannel

end Examples
end Noise
