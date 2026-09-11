/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.Noise.Crypto

/-!
# A symbolic instantiation of the crypto functions

`Noise.Crypto` is an interface with two laws.  This file exhibits a model of it,
so the interface is consistent and every theorem stated over an arbitrary
`Crypto` has content.

The model is the *symbolic* (Dolev–Yao) one used by the Noise Explorer paper
(§2.2): byte sequences are terms of a free algebra, primitives are constructors,
and the only equations that hold are the ones we impose.  Concretely:

* private keys are natural numbers and `pub a` is the formal term `g^a`;
* `DH(a, g^b)` normalises to `dhOut (min a b) (max a b)`, which makes
  `dh_comm` hold and nothing else (`Sym.dh_pubKey_eq_iff`);
* `ENCRYPT` builds an `aead` term that `DECRYPT` takes apart only when the key,
  nonce and associated data all match — the symbolic model's "perfect
  cryptography" assumption.

Because everything is a free constructor, the model is also *executable*:
`ScalingTrust.Noise.Examples` runs complete handshakes in it and inspects the
resulting terms.
-/

namespace Noise

/-- Symbolic byte sequences: the terms of the Dolev–Yao algebra. -/
inductive Sym where
  /-- An atomic secret or datum, identified by a number. -/
  | atom (n : Nat) : Sym
  /-- An ASCII string, used for protocol names. -/
  | str (s : String) : Sym
  /-- The zero-length byte sequence. -/
  | empty : Sym
  /-- The public key `g^n`. -/
  | pubKey (n : Nat) : Sym
  /-- A Diffie–Hellman output `g^(a·b)`, stored with `a ≤ b`. -/
  | dhOut (a b : Nat) : Sym
  /-- `HASH(t)`. -/
  | hashOf (t : Sym) : Sym
  /-- `HMAC-HASH(k, d)`. -/
  | hmacOf (k d : Sym) : Sym
  /-- `a || b`. -/
  | catOf (a b : Sym) : Sym
  /-- `byte(n)`. -/
  | byteOf (n : Nat) : Sym
  /-- Zero-padding to `n` bytes. -/
  | padOf (n : Nat) (t : Sym) : Sym
  /-- Truncation to 32 bytes. -/
  | truncOf (t : Sym) : Sym
  /-- An AEAD ciphertext under key `k`, nonce `n`, associated data `ad`. -/
  | aead (k : Sym) (n : Nat) (ad p : Sym) : Sym
  deriving DecidableEq, Repr, Inhabited

namespace Sym

/-- A nominal byte length, enough to drive `InitializeSymmetric`'s length test:
strings have their own length and every derived term is `HASHLEN` bytes. -/
def blen : Sym → Nat
  | .str s => s.length
  | _ => 32

/-- The symbolic Diffie–Hellman: `DH(a, g^b)` normalises to a term symmetric in
`a` and `b`, and fails against anything that is not a public key.  This is the
error-signalling option of spec §4.1, and it is what the reference back end's
partial `dhexp` destructor does. -/
def dh (a : Nat) : Sym → Option Sym
  | .pubKey b => some (.dhOut (min a b) (max a b))
  | _ => none

/-- Symbolic AEAD decryption: it succeeds exactly on ciphertexts produced with
matching key, nonce and associated data. -/
def decrypt (k : Sym) (n : Nat) (ad : Sym) : Sym → Option Sym
  | .aead k' n' ad' p => if k' = k ∧ n' = n ∧ ad' = ad then some p else none
  | _ => none

end Sym

/-- The symbolic instantiation of the Noise crypto functions. -/
def symbolic : Crypto where
  Bytes := Sym
  Priv := Nat
  pub := Sym.pubKey
  dh := Sym.dh
  hash := Sym.hashOf
  hmac := Sym.hmacOf
  hashlen := 32
  blen := Sym.blen
  padTo := Sym.padOf
  trunc32 := Sym.truncOf
  emptyBytes := Sym.empty
  cat := Sym.catOf
  byte := Sym.byteOf
  ofString := Sym.str
  encrypt := Sym.aead
  decrypt := Sym.decrypt
  dh_comm := by grind [Sym.dh]
  decrypt_encrypt := by grind [Sym.decrypt]

@[simp] theorem symbolic_Bytes : symbolic.Bytes = Sym := rfl
@[simp] theorem symbolic_Priv : symbolic.Priv = Nat := rfl

/-! The carrier types of `symbolic` are definitionally `Sym` and `Nat`, but
instance search does not unfold the structure projection, so we register the
instances that make the model usable. -/

instance : DecidableEq symbolic.Bytes := inferInstanceAs (DecidableEq Sym)
instance : DecidableEq symbolic.Priv := inferInstanceAs (DecidableEq Nat)
instance : Repr symbolic.Bytes := inferInstanceAs (Repr Sym)
instance : Repr symbolic.Priv := inferInstanceAs (Repr Nat)
instance : Inhabited symbolic.Bytes := inferInstanceAs (Inhabited Sym)
instance (n : Nat) : OfNat symbolic.Priv n := inferInstanceAs (OfNat Nat n)

/-- The symbolic model does not collapse: distinct atoms stay distinct, so the
`Crypto` interface is not satisfied only by trivial models. -/
theorem symbolic_nontrivial : (Sym.atom 0) ≠ (Sym.atom 1) := by decide

/-- A hash is never a ciphertext, so decryption of an unrelated term fails.
This is the symbolic model's authenticity assumption in its crudest form. -/
theorem symbolic_decrypt_hash (k ad t : Sym) (n : Nat) :
    symbolic.decrypt k n ad (Sym.hashOf t) = none := rfl

/-- **The Diffie–Hellman equational theory, exactly.**  Two Diffie–Hellman
outputs are equal precisely when their exponents agree as an unordered pair: the
model imposes commutativity and nothing else, which is what makes `dh_comm` a
faithful rendering of the equation a ProVerif back end declares rather than an
accident of the `min`/`max` encoding.

`ScalingTrust/ProVerif/Reference/` holds two of the models Noise Explorer
generates, and its `README` compares them with this file. -/
theorem Sym.dh_pubKey_eq_iff (a b c d : Nat) :
    dh a (.pubKey b) = dh c (.pubKey d) ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  grind [dh]

end Noise
