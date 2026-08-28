/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.Noise.Crypto

/-!
# `CipherState` and `SymmetricState`

Spec §5:

> A `CipherState` object contains `k` and `n` variables, which it uses to
> encrypt and decrypt ciphertexts. …
> A `SymmetricState` object contains a `CipherState` plus `ck` and `h`
> variables.

This file transcribes §5.1 and §5.2 operation by operation.
-/

namespace Noise

variable {C : Crypto}

/-! ## The `CipherState` object (spec §5.1) -/

/-- Spec §5.1:

> `k`: A cipher key of 32 bytes (which may be empty). …
> `n`: An 8-byte (64-bit) unsigned integer nonce. -/
structure CipherState (C : Crypto) where
  /-- The cipher key; `none` is the specification's "empty". -/
  k : Option C.Bytes
  /-- The nonce. -/
  n : Nat

namespace CipherState

/-- `InitializeKey(key)`: "Sets `k = key`.  Sets `n = 0`." -/
def initializeKey (key : Option C.Bytes) : CipherState C := ⟨key, 0⟩

/-- `HasKey()`: "Returns true if `k` is non-empty, false otherwise." -/
def hasKey (cs : CipherState C) : Bool := cs.k.isSome

/-- `SetNonce(nonce)`: "Sets `n = nonce`" (spec §11.4). -/
def setNonce (cs : CipherState C) (nonce : Nat) : CipherState C := { cs with n := nonce }

/-- Spec §5.1: "The maximum `n` value (`2^64 - 1`) is reserved for other use. If
incrementing `n` results in `2^64 - 1`, then any further `EncryptWithAd()` or
`DecryptWithAd()` calls will signal an error to the caller." -/
def nonceAvailable (cs : CipherState C) : Bool := decide (cs.n + 1 < Crypto.maxNonce)

/-- `EncryptWithAd(ad, plaintext)`: "If `k` is non-empty returns
`ENCRYPT(k, n++, ad, plaintext)`.  Otherwise returns `plaintext`." -/
def encryptWithAd (cs : CipherState C) (ad plaintext : C.Bytes) :
    Except NoiseError (CipherState C × C.Bytes) :=
  match cs.k with
  | none => .ok (cs, plaintext)
  | some k =>
      if cs.nonceAvailable then
        .ok ({ cs with n := cs.n + 1 }, C.encrypt k cs.n ad plaintext)
      else .error .nonceExhausted

/-- `DecryptWithAd(ad, ciphertext)`: "If `k` is non-empty returns
`DECRYPT(k, n++, ad, ciphertext)`.  Otherwise returns `ciphertext`.  If an
authentication failure occurs in `DECRYPT()` then `n` is not incremented and an
error is signaled to the caller." -/
def decryptWithAd (cs : CipherState C) (ad ciphertext : C.Bytes) :
    Except NoiseError (CipherState C × C.Bytes) :=
  match cs.k with
  | none => .ok (cs, ciphertext)
  | some k =>
      if cs.nonceAvailable then
        match C.decrypt k cs.n ad ciphertext with
        | some p => .ok ({ cs with n := cs.n + 1 }, p)
        | none => .error .decryptionFailure
      else .error .nonceExhausted

/-- `Rekey()`: "Sets `k = REKEY(k)`" (spec §5.1, §11.3).  Note that it does not
reset `n`. -/
def rekey (cs : CipherState C) : CipherState C :=
  { cs with k := cs.k.map C.rekey }

/-- Decryption inverts encryption when both sides are in the same state.  This
is the `CipherState`-level consequence of `Crypto.decrypt_encrypt`, and it holds
whether or not a key is set — when `k` is empty both operations are the
identity, exactly as spec §5.1 prescribes. -/
theorem decryptWithAd_encryptWithAd (cs : CipherState C) (ad p : C.Bytes)
    {cs' : CipherState C} {ct : C.Bytes} (h : cs.encryptWithAd ad p = .ok (cs', ct)) :
    cs.decryptWithAd ad ct = .ok (cs', p) := by
  cases hk : cs.k with
  | none =>
      simp only [encryptWithAd, hk, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1; subst h2
      simp [decryptWithAd, hk]
  | some k =>
      cases hn : cs.nonceAvailable with
      | false => simp [encryptWithAd, hk, hn] at h
      | true =>
          simp only [encryptWithAd, hk, hn, if_true, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨h1, h2⟩ := h
          subst h1; subst h2
          simp [decryptWithAd, hk, hn, C.decrypt_encrypt]

/-! ### Nonce discipline (spec §5.1, §14)

Spec §14: "Reusing a nonce value for `n` with the same key `k` for encryption
would be catastrophic.  Implementations must carefully follow the rules for
nonces."  The rules are: a fresh key starts at `n = 0`, and every encryption or
decryption advances `n` by exactly one.  Together with the fact that matched
parties hold *the same* `CipherState` throughout a handshake
(`Noise.Matched.sym`), this is what stops the two parties from ever encrypting
two different handshake payloads under the same key and nonce. -/

@[simp] theorem initializeKey_nonce (key : Option C.Bytes) :
    (initializeKey (C := C) key).n = 0 := rfl

theorem encryptWithAd_advances {cs : CipherState C} {ad p : C.Bytes}
    {cs' : CipherState C} {ct : C.Bytes} (h : cs.encryptWithAd ad p = .ok (cs', ct))
    (hk : cs.hasKey = true) : cs'.k = cs.k ∧ cs'.n = cs.n + 1 := by
  cases hkk : cs.k with
  | none => simp [hasKey, hkk] at hk
  | some k =>
      cases hn : cs.nonceAvailable with
      | false => simp [encryptWithAd, hkk, hn] at h
      | true =>
          simp only [encryptWithAd, hkk, hn, if_true, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨h1, -⟩ := h
          subst h1
          exact ⟨rfl, rfl⟩

theorem decryptWithAd_advances {cs : CipherState C} {ad ct : C.Bytes}
    {cs' : CipherState C} {p : C.Bytes} (h : cs.decryptWithAd ad ct = .ok (cs', p))
    (hk : cs.hasKey = true) : cs'.k = cs.k ∧ cs'.n = cs.n + 1 := by
  cases hkk : cs.k with
  | none => simp [hasKey, hkk] at hk
  | some k =>
      cases hn : cs.nonceAvailable with
      | false => simp [decryptWithAd, hkk, hn] at h
      | true =>
          cases hd : C.decrypt k cs.n ad ct with
          | none => simp [decryptWithAd, hkk, hn, hd] at h
          | some pl =>
              simp only [decryptWithAd, hkk, hn, hd, if_true, Except.ok.injEq,
                Prod.mk.injEq] at h
              obtain ⟨h1, -⟩ := h
              subst h1
              exact ⟨rfl, rfl⟩

/-- Without a key, `EncryptWithAd` is the identity and the nonce does not move
(spec §5.1: "Otherwise returns `plaintext`"). -/
theorem encryptWithAd_no_key {cs : CipherState C} (hk : cs.k = none) (ad p : C.Bytes) :
    cs.encryptWithAd ad p = .ok (cs, p) := by simp [encryptWithAd, hk]

end CipherState

/-! ## The `SymmetricState` object (spec §5.2) -/

/-- Spec §5.2: "A `SymmetricState` object contains a `CipherState` plus the
following variables: `ck`, a chaining key of `HASHLEN` bytes; `h`, a hash output
of `HASHLEN` bytes." -/
structure SymmetricState (C : Crypto) where
  /-- The embedded `CipherState`. -/
  cs : CipherState C
  /-- The chaining key. -/
  ck : C.Bytes
  /-- The handshake hash. -/
  h : C.Bytes

namespace SymmetricState

/-- `InitializeSymmetric(protocol_name)` (spec §5.2). -/
def initializeSymmetric (C : Crypto) (protocolName : String) : SymmetricState C :=
  let h := C.initialHash protocolName
  { cs := CipherState.initializeKey none, ck := h, h }

/-- `MixHash(data)`: "Sets `h = HASH(h || data)`." -/
def mixHash (ss : SymmetricState C) (data : C.Bytes) : SymmetricState C :=
  { ss with h := C.hash (C.cat ss.h data) }

/-- `MixKey(input_key_material)` (spec §5.2). -/
def mixKey (ss : SymmetricState C) (ikm : C.Bytes) : SymmetricState C :=
  let (ck, tempK) := C.hkdf2 ss.ck ikm
  { ss with ck, cs := CipherState.initializeKey (some (C.cipherKeyOf tempK)) }

/-- `MixKeyAndHash(input_key_material)` (spec §5.2), used for pre-shared keys
(spec §9.1). -/
def mixKeyAndHash (ss : SymmetricState C) (ikm : C.Bytes) : SymmetricState C :=
  let (ck, tempH, tempK) := C.hkdf3 ss.ck ikm
  let ss := ({ ss with ck } : SymmetricState C).mixHash tempH
  { ss with cs := CipherState.initializeKey (some (C.cipherKeyOf tempK)) }

/-- `GetHandshakeHash()`: "Returns `h`" (spec §5.2, §11.2). -/
def getHandshakeHash (ss : SymmetricState C) : C.Bytes := ss.h

/-- `EncryptAndHash(plaintext)`: "Sets `ciphertext = EncryptWithAd(h, plaintext)`,
calls `MixHash(ciphertext)`, and returns `ciphertext`." -/
def encryptAndHash (ss : SymmetricState C) (plaintext : C.Bytes) :
    Except NoiseError (SymmetricState C × C.Bytes) :=
  match ss.cs.encryptWithAd ss.h plaintext with
  | .error e => .error e
  | .ok (cs, ct) => .ok (({ ss with cs } : SymmetricState C).mixHash ct, ct)

/-- `DecryptAndHash(ciphertext)`: "Sets `plaintext = DecryptWithAd(h, ciphertext)`,
calls `MixHash(ciphertext)`, and returns `plaintext`." -/
def decryptAndHash (ss : SymmetricState C) (ciphertext : C.Bytes) :
    Except NoiseError (SymmetricState C × C.Bytes) :=
  match ss.cs.decryptWithAd ss.h ciphertext with
  | .error e => .error e
  | .ok (cs, p) => .ok (({ ss with cs } : SymmetricState C).mixHash ciphertext, p)

/-- `Split()`: "Returns a pair of `CipherState` objects for encrypting transport
messages" (spec §5.2).  The first is for initiator-to-responder traffic. -/
def split (ss : SymmetricState C) : CipherState C × CipherState C :=
  let (tempK1, tempK2) := C.hkdf2 ss.ck C.emptyBytes
  (CipherState.initializeKey (some (C.cipherKeyOf tempK1)),
   CipherState.initializeKey (some (C.cipherKeyOf tempK2)))

/-- Every `MixKey` starts a new key at nonce zero (spec §5.2), so the nonces
used under one key form an initial segment of the natural numbers. -/
@[simp] theorem mixKey_nonce (ss : SymmetricState C) (ikm : C.Bytes) :
    (ss.mixKey ikm).cs.n = 0 := rfl

/-- The same for `MixKeyAndHash` (spec §5.2, §9.1). -/
@[simp] theorem mixKeyAndHash_nonce (ss : SymmetricState C) (ikm : C.Bytes) :
    (ss.mixKeyAndHash ikm).cs.n = 0 := rfl

/-- Both transport `CipherState`s returned by `Split()` start at nonce zero. -/
@[simp] theorem split_nonce (ss : SymmetricState C) :
    ss.split.1.n = 0 ∧ ss.split.2.n = 0 := ⟨rfl, rfl⟩

/-- Spec §15.2: "The `h` value hashes handshake *ciphertext* instead of
plaintext", so `DecryptAndHash` and `EncryptAndHash` mix in the same value and
the two parties' handshake hashes stay equal. -/
theorem decryptAndHash_encryptAndHash (ss : SymmetricState C) (p : C.Bytes)
    {ss' : SymmetricState C} {ct : C.Bytes} (h : ss.encryptAndHash p = .ok (ss', ct)) :
    ss.decryptAndHash ct = .ok (ss', p) := by
  unfold encryptAndHash at h
  cases he : ss.cs.encryptWithAd ss.h p with
  | error e => rw [he] at h; exact absurd h (by simp)
  | ok r =>
      obtain ⟨cs, ct'⟩ := r
      rw [he] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h2
      unfold decryptAndHash
      rw [CipherState.decryptWithAd_encryptWithAd ss.cs ss.h p he]
      simp [h1]

end SymmetricState

end Noise
