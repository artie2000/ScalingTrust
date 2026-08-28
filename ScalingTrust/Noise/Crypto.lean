/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.Noise.Pattern

/-!
# The crypto functions a Noise protocol is instantiated with

Spec §4:

> A Noise protocol is instantiated with a concrete set of DH functions, cipher
> functions, and hash functions.

We package them as a single structure carrying the two carrier types (byte
sequences and DH private keys), the operations of §4.1–4.3, and the two
algebraic laws the protocol's *functional correctness* depends on:

* `dh_comm` — `DH(a, pub b) = DH(b, pub a)`, the Diffie–Hellman property;
* `decrypt_encrypt` — AEAD decryption inverts encryption under matching key,
  nonce and associated data.

Nothing else is assumed.  In particular the hash is not assumed injective or
collision-resistant: those are *security* properties, not correctness ones, and
every result in `ScalingTrust.Noise.Correctness` holds for any structure
satisfying the two laws above.  `ScalingTrust.Noise.Symbolic` exhibits one, a
Dolev–Yao style term algebra, so the assumptions are consistent and the theory
is not vacuous.

`HKDF` is *derived* from `HMAC` exactly as spec §4.3 prescribes, rather than
being assumed.
-/

namespace Noise

/-- A concrete instantiation of the Noise crypto functions (spec §4). -/
structure Crypto where
  /-- Byte sequences. -/
  Bytes : Type
  /-- DH private keys; `GENERATE_KEYPAIR()` produces one of these together with
  its public key `pub priv`. -/
  Priv : Type
  /-- The public key of a private key (spec §4.1, `GENERATE_KEYPAIR`). -/
  pub : Priv → Bytes
  /-- `DH(key_pair, public_key)` (spec §4.1). -/
  dh : Priv → Bytes → Bytes
  /-- `HASH(data)` (spec §4.3). -/
  hash : Bytes → Bytes
  /-- `HMAC-HASH(key, data)` (spec §4.3). -/
  hmac : Bytes → Bytes → Bytes
  /-- `HASHLEN`, which spec §4.3 requires to be 32 or 64. -/
  hashlen : Nat
  /-- The length in bytes of a byte sequence. -/
  blen : Bytes → Nat
  /-- Zero-padding to a given length, used by `InitializeSymmetric`. -/
  padTo : Nat → Bytes → Bytes
  /-- Truncation to 32 bytes, used when `HASHLEN` is 64 (spec §5.2). -/
  trunc32 : Bytes → Bytes
  /-- The zero-length byte sequence. -/
  emptyBytes : Bytes
  /-- The `||` concatenation operator of spec §4. -/
  cat : Bytes → Bytes → Bytes
  /-- The `byte()` constructor of spec §4. -/
  byte : Nat → Bytes
  /-- ASCII encoding of a protocol name (spec §8). -/
  ofString : String → Bytes
  /-- `ENCRYPT(k, n, ad, plaintext)` (spec §4.2). -/
  encrypt : (k : Bytes) → (n : Nat) → (ad : Bytes) → (plaintext : Bytes) → Bytes
  /-- `DECRYPT(k, n, ad, ciphertext)` (spec §4.2), signalling failure with
  `none`. -/
  decrypt : (k : Bytes) → (n : Nat) → (ad : Bytes) → (ciphertext : Bytes) → Option Bytes
  /-- The Diffie–Hellman property.  Spec §4.1 requires `DH` to be a
  Diffie–Hellman calculation; this equation is what makes the two parties agree
  on a shared secret. -/
  dh_comm : ∀ a b, dh a (pub b) = dh b (pub a)
  /-- AEAD correctness (spec §4.2: `DECRYPT` "returns the plaintext, unless
  authentication fails"). -/
  decrypt_encrypt : ∀ k n ad p, decrypt k n ad (encrypt k n ad p) = some p

namespace Crypto

variable (C : Crypto)

/-- `REKEY(k)` (spec §4.2), using the default definition:

> it defaults to returning the first 32 bytes from
> `ENCRYPT(k, maxnonce, zerolen, zeros)`, where `maxnonce` equals `2^64 - 1`. -/
def rekey (k : C.Bytes) : C.Bytes :=
  C.trunc32 (C.encrypt k (2 ^ 64 - 1) C.emptyBytes (C.padTo 32 C.emptyBytes))

/-- The maximum nonce value, reserved by spec §5.1. -/
def maxNonce : Nat := 2 ^ 64 - 1

/-- `HKDF(chaining_key, input_key_material, 2)` (spec §4.3). -/
def hkdf2 (ck ikm : C.Bytes) : C.Bytes × C.Bytes :=
  let tempKey := C.hmac ck ikm
  let out1 := C.hmac tempKey (C.byte 1)
  let out2 := C.hmac tempKey (C.cat out1 (C.byte 2))
  (out1, out2)

/-- `HKDF(chaining_key, input_key_material, 3)` (spec §4.3). -/
def hkdf3 (ck ikm : C.Bytes) : C.Bytes × C.Bytes × C.Bytes :=
  let tempKey := C.hmac ck ikm
  let out1 := C.hmac tempKey (C.byte 1)
  let out2 := C.hmac tempKey (C.cat out1 (C.byte 2))
  let out3 := C.hmac tempKey (C.cat out2 (C.byte 3))
  (out1, out2, out3)

/-- The first two outputs of `HKDF(_, _, 3)` are the two outputs of
`HKDF(_, _, 2)`; spec §9.1 relies on this when it notes that "the third output
from `HKDF()` is used as the `k` value so that calculation of `k` may be skipped
if `k` is not used". -/
theorem hkdf3_fst_snd (ck ikm : C.Bytes) :
    ((C.hkdf3 ck ikm).1, (C.hkdf3 ck ikm).2.1) = C.hkdf2 ck ikm := rfl

/-- Spec §5.2: "If `HASHLEN` is 64, then truncates `temp_k` to 32 bytes." -/
def cipherKeyOf (b : C.Bytes) : C.Bytes :=
  if C.hashlen = 64 then C.trunc32 b else b

/-- The initial `h` value of spec §5.2:

> If `protocol_name` is less than or equal to `HASHLEN` bytes in length, sets
> `h` equal to `protocol_name` with zero bytes appended to make `HASHLEN` bytes.
> Otherwise sets `h = HASH(protocol_name)`. -/
def initialHash (protocolName : String) : C.Bytes :=
  let n := C.ofString protocolName
  if C.blen n ≤ C.hashlen then C.padTo C.hashlen n else C.hash n

end Crypto

/-- The errors a Noise implementation can signal (spec §5). -/
inductive NoiseError where
  /-- `DECRYPT()` reported an authentication failure (spec §5.1). -/
  | decryptionFailure : NoiseError
  /-- The nonce reached its reserved maximum value (spec §5.1). -/
  | nonceExhausted : NoiseError
  /-- A key required by the pattern was not supplied to `Initialize` (spec
  §5.3), or an `e` token was processed when `e` was already set. -/
  | missingKey (owner : Role) (kind : KeyKind) : NoiseError
  /-- A DH token was processed but one of the two public keys it needs had not
  been communicated. -/
  | missingDHKey (initiatorKey responderKey : KeyKind) : NoiseError
  /-- A `psk` token was processed but no pre-shared key was supplied. -/
  | missingPsk : NoiseError
  /-- `WriteMessage`/`ReadMessage` was called with no message patterns left. -/
  | patternExhausted : NoiseError
  /-- The received message did not have the shape its message pattern
  requires. -/
  | malformedMessage : NoiseError
  deriving DecidableEq, Repr

end Noise
