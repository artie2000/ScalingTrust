/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.Noise.Patterns

/-!
# Every named pattern of the specification is valid

Spec §7.3 closes with

> Users are recommended to only use the handshake patterns listed below, or
> other patterns that have been vetted by experts to satisfy the above checks.

Here we discharge those checks mechanically for every pattern the specification
names, and confirm that the deliberately broken `KXS` pattern of §6 of the Noise
Explorer paper is rejected, with the expected diagnosis.
-/

namespace Noise
namespace Patterns

open HandshakePattern

/-- **Every handshake pattern named in the specification satisfies the validity
rules of §7.3 and §9.3.** -/
theorem all_valid : ∀ hp ∈ all, hp.isValid = true := by decide

/-- The same statement in terms of the declarative rules, via
`HandshakePattern.isValid_iff_patternValid`. -/
theorem all_patternValid : ∀ hp ∈ all, PatternValid hp :=
  fun hp h => (isValid_iff_patternValid hp).mp (all_valid hp h)

theorem oneWay_valid : ∀ hp ∈ oneWay, hp.isValid = true := by decide
theorem fundamental_valid : ∀ hp ∈ fundamental, hp.isValid = true := by decide
theorem deferred_valid : ∀ hp ∈ deferred, hp.isValid = true := by decide
theorem psk_valid : ∀ hp ∈ psk, hp.isValid = true := by decide

/-- The specification names 3 + 12 + 23 + 21 patterns, plus `XXfallback`. -/
theorem all_length : all.length = 60 := by decide

theorem oneWay_length : oneWay.length = 3 := by decide
theorem fundamental_length : fundamental.length = 12 := by decide
theorem deferred_length : deferred.length = 23 := by decide
theorem psk_length : psk.length = 21 := by decide

/-! ## The pattern names are distinct

A Noise protocol name must "uniquely identify the combination of handshake
pattern and crypto functions" (spec §14).  A necessary condition is that
distinct patterns get distinct names. -/

theorem all_names_nodup : (all.map HandshakePattern.name).Nodup := by decide

/-! ## `KXS` is invalid

§6 of the Noise Explorer paper analyses

```
KXS:
  -> s
  ...
  -> e
  <- e, ee, s, ss
```

a variant of `KX` in which `se` and `es` are replaced by a single `ss`.  The
paper exhibits a man-in-the-middle forgery: because the responder's encryption
key depends only on `ss` once an invalid ephemeral forces `ee` to a known
constant, the responder can be made to encrypt two different messages under the
same key and nonce.

Revision 34 of the specification rules this out via rule 4, and our checker
finds exactly that violation: the responder would encrypt after an `ss` token
without a `se` token. -/
theorem KXS_not_valid : KXS.isValid = false := by decide

theorem KXS_not_patternValid : ¬ PatternValid KXS := by
  intro h
  have := (isValid_iff_patternValid KXS).mpr h
  rw [KXS_not_valid] at this
  exact Bool.noConfusion this

/-- The precise diagnosis: the responder is about to encrypt its payload after
an `ss` token, but has not performed the DH between its own ephemeral key and
the initiator's static key. -/
theorem KXS_analyse :
    KXS.analyse = .error (.encryptAfterSS .responder) := rfl

/-! ## The `psk` validity rule has real content

Spec §9.3 forbids sending encrypted data after a `psk` token unless the sender
has already sent an ephemeral public key.  Placing the `psk` token of `NNpsk0`
*after* a static key transmission, so that the static key is encrypted under a
key derived from the PSK alone, is rejected. -/

/-- `-> psk, s` (with the initiator's static key transmitted immediately) is
rejected: the static public key would be encrypted under a key derived from the
PSK with no ephemeral contribution. -/
theorem psk_before_ephemeral_invalid :
    (HandshakePattern.mk "bad" [] [] [[.psk, .s, .e], [.e, .ee]]).isValid = false := by
  decide

/-- Moving the `e` token in front of the `s` token repairs it. -/
theorem psk_after_ephemeral_valid :
    (HandshakePattern.mk "ok" [] [] [[.psk, .e, .s], [.e, .ee, .se]]).isValid = true := by
  decide

/-! ## Rule 4 must be checked at every `ENCRYPT()`, not only at payloads

The Noise Explorer paper's Figure 4 checks rule 4 only at the end of a message.
The pattern below shows the difference: at the `s` token the static public key
is encrypted under a key derived from `ss` alone, yet by the end of the message
an `es` token has repaired the context, so an end-of-message-only check would
accept it. -/
theorem encrypt_check_at_static_token :
    (HandshakePattern.mk "endOnly" [.s] [.s] [[.ss, .s, .es], [.e, .ee, .se]]).isValid
      = false := by
  decide

/-! ## Repeated `psk` tokens

The specification allows a `psk` token to occur more than once (§9.2, and §9.4
names `XXpsk0+psk3`); the Noise Explorer paper's `MsgPSK` rule does not.  Our
checker follows the specification. -/

/-- `XXpsk0+psk3`, named in spec §9.4 as a legitimate pattern that its table
does not list, is valid. -/
def XXpsk0psk3 : HandshakePattern :=
  { name := "XXpsk0+psk3", messages :=
      [[.psk, .e], [.e, .ee, .s, .es], [.s, .se, .psk]] }

theorem XXpsk0psk3_valid : XXpsk0psk3.isValid = true := by decide

/-- …and the Noise Explorer paper's stricter reading would reject it. -/
theorem XXpsk0psk3_hasRepeatedPsk : XXpsk0psk3.hasRepeatedPsk = true := by decide

/-- No pattern that the specification actually lists repeats a `psk` token, so
on the specification's own patterns the two readings agree. -/
theorem all_no_repeated_psk : ∀ hp ∈ all, hp.hasRepeatedPsk = false := by decide

/-! ## No pattern wastes a key share

The Noise Explorer paper adds the soft rule that "Noise Handshake Patterns
should not contain key shares that are not subsequently used in any
Diffie-Hellman operation".  Every listed pattern respects it. -/

theorem all_usesAllKeys : ∀ hp ∈ all, hp.usesAllKeys = true := by decide

end Patterns
end Noise
