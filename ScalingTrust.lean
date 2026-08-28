/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.Noise.Token
import ScalingTrust.Noise.Pattern
import ScalingTrust.Noise.Context
import ScalingTrust.Noise.Validity
import ScalingTrust.Noise.Patterns
import ScalingTrust.Noise.PatternsValid
import ScalingTrust.Noise.Derivation
import ScalingTrust.Noise.Modifiers
import ScalingTrust.Noise.Security
import ScalingTrust.Noise.Crypto
import ScalingTrust.Noise.Symbolic
import ScalingTrust.Noise.State
import ScalingTrust.Noise.Handshake
import ScalingTrust.Noise.Correctness
import ScalingTrust.Noise.Session
import ScalingTrust.Noise.Transport
import ScalingTrust.Noise.Examples

/-!
# A formalisation of the Noise Protocol Framework

This library formalises Revision 34 of *The Noise Protocol Framework*
(Trevor Perrin, 2018-07-11) in Lean 4, together with the formal treatment given
by Kobeissi, Nicolas and Bhargavan in *Noise Explorer: Fully Automated Modeling
and Verification for Arbitrary Noise Protocols* (IEEE EuroS&P 2019).

## The syntax and its rules

* `ScalingTrust.Noise.Token` — key kinds, roles and tokens (spec §2.2, §7.1).
* `ScalingTrust.Noise.Pattern` — message, pre-message and handshake patterns.
* `ScalingTrust.Noise.Context` — the context `Γ` of the Noise Explorer paper.
* `ScalingTrust.Noise.Validity` — the validity rules of §7.3 and §9.3, given
  both as an executable checker and as an inductive relation in the style of the
  paper's Figure 4, and proved equivalent
  (`HandshakePattern.isValid_iff_patternValid`).  Also
  `canEncrypt_ephemeralRandomised`, which turns the stated rationale for rule 4
  into a theorem.
* `ScalingTrust.Noise.Patterns` — every pattern the specification names.
* `ScalingTrust.Noise.PatternsValid` — all sixty are valid (`all_valid`), and
  the `KXS` pattern of the paper's §6 is not (`KXS_not_valid`).
* `ScalingTrust.Noise.Derivation` — the pattern derivation rules of §18.3, and
  a proof that they generate all thirty-eight one-way, fundamental and deferred
  patterns (`derivationTable_correct`).
* `ScalingTrust.Noise.Modifiers` — protocol names (§8), the `pskN` modifiers
  (§9.4) and the `fallback` modifier (§10.2).
* `ScalingTrust.Noise.Security` — the payload security grades of §7.7, checked
  against the specification's tables; two defects in the §18.2 table are
  identified and proved (`NX1_table_arrows_swapped`, `X1N_table_missing_row`).

## The protocol itself

* `ScalingTrust.Noise.Crypto` — the DH, cipher and hash functions of §4, as an
  interface with two laws.
* `ScalingTrust.Noise.Symbolic` — a Dolev–Yao model of that interface, so the
  assumptions are consistent.
* `ScalingTrust.Noise.State` — `CipherState` and `SymmetricState` (§5.1, §5.2).
* `ScalingTrust.Noise.Handshake` — `HandshakeState`, `Initialize`,
  `WriteMessage`, `ReadMessage` (§5.3).
* `ScalingTrust.Noise.Correctness` — the matching invariant and the theorem
  that reading inverts writing, message by message (`run_correct`).
* `ScalingTrust.Noise.Session` — `Initialize` establishes the invariant
  (`initialize_matched`), and the end-to-end statement (`session_correct`).
* `ScalingTrust.Noise.Transport` — the transport phase (§5, §11.3, §11.4), and
  the theorem that a stream of transport messages round-trips
  (`Transport.readStream_writeStream`).
* `ScalingTrust.Noise.Examples` — every named pattern executed end to end in
  the symbolic model (`all_patterns_run`).
-/
