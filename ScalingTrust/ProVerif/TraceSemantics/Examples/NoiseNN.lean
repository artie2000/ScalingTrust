/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.TraceSemantics.Proofs.Attack
import ScalingTrust.ProVerif.TraceSemantics.Proofs.Query
import ScalingTrust.ProVerif.Translation.Examples.NN

/-!
# The Noise Explorer NN model: every query fails

`NN`, in `../../Translation/Examples/`, is the translation of Noise Explorer's model of
the Noise handshake pattern `NN` (`-> e`, `<- e, ee`, `->`, `<-`) against an active
attacker, `../../Reference/NN.noise.active.pv`.  The pattern has no static keys, so
against an active attacker none of its properties hold, as Noise Explorer reports: each
of the model's 37 queries is refuted here by an attack, with the lemmas of `Proofs/`.

Two attacks suffice.  In `attackA` the attacker plays the initiator towards `bob`: it
sends a message a with an ephemeral key of its own, the public constant `empty`, so it
shares the session keys with `bob` and reads messages b and d; `bob` accepts the payloads
`empty` of its messages a and c.  In `attackB` the attacker plays the responder towards
`alice`: it reads message a, which is encrypted under no key, replies with an ephemeral
key of its own, and so reads message c; `alice` accepts the payloads `empty` of its
messages b and d and ends the handshake.  Every authentication query fails since the
payloads received were never sent, every confidentiality query since the attacker reads
the payload, and the termination query since `alice` ends.

The attacker's share of each attack is the dual of the protocol's (`Proc.mem_attacks`);
what it computes along the way is derived by the public constructors and destructors
(`derive`).  The protocol's share is a trace of `system` built one action at a time, the
messages it computes being evaluated by `simp` with the rules of the destructors.
-/

noncomputable section

namespace ProVerif.TraceSemantics.Examples.NoiseNN

open NN
open Attacker (derive)

/-! ## The destructors on the messages they take apart -/

@[simp] theorem keypairunpack_pack (a b : T.Msg) :
    keypairunpack (keypairpack a b) = some ((a, b) : T.Msg) :=
  keypairunpack_eq_some.2 ⟨a, b, rfl, rfl⟩

@[simp] theorem getpublickey_pack (a b : T.Msg) : getpublickey (keypairpack a b) = some a :=
  getpublickey_eq_some.2 ⟨b, rfl⟩

@[simp] theorem aeadunpack_pack (b ad p : T.Msg) :
    aeadunpack (aeadpack b ad p) = some ((b, ad, p) : T.Msg) :=
  aeadunpack_eq_some.2 ⟨b, ad, p, rfl, rfl⟩

@[simp] theorem cipherstateunpack_pack (k n : T.Msg) :
    cipherstateunpack (cipherstatepack k n) = some ((k, n) : T.Msg) :=
  cipherstateunpack_eq_some.2 ⟨k, n, rfl, rfl⟩

@[simp] theorem symmetricstateunpack_pack (cs k h : T.Msg) :
    symmetricstateunpack (symmetricstatepack cs k h) = some ((cs, k, h) : T.Msg) :=
  symmetricstateunpack_eq_some.2 ⟨cs, k, h, rfl, rfl⟩

@[simp] theorem handshakestateunpack_pack (ss s e rs re psk i : T.Msg) :
    handshakestateunpack (handshakestatepack ss s e rs re psk i) =
      some ((ss, s, e, rs, re, psk, i) : T.Msg) :=
  handshakestateunpack_eq_some.2 ⟨ss, s, e, rs, re, psk, i, rfl, rfl⟩

@[simp] theorem handshakestatesetcs_pack (cs k h s e rs re psk i csn : T.Msg) :
    handshakestatesetcs (handshakestatepack (symmetricstatepack cs k h) s e rs re psk i) csn =
      some (handshakestatepack (symmetricstatepack csn k h) s e rs re psk i) :=
  handshakestatesetcs_eq_some.2 ⟨cs, k, h, s, e, rs, re, psk, i, rfl, rfl⟩

@[simp] theorem handshakestategetcs_pack (cs k h s e rs re psk i : T.Msg) :
    handshakestategetcs (handshakestatepack (symmetricstatepack cs k h) s e rs re psk i) =
      some cs :=
  handshakestategetcs_eq_some.2 ⟨k, h, s, e, rs, re, psk, i, rfl⟩

@[simp] theorem deconcat3_concat3 (a b c : T.Msg) :
    deconcat3 (concat3 a b c) = some ((a, b, c) : T.Msg) :=
  deconcat3_eq_some.2 ⟨a, b, c, rfl, rfl⟩

@[simp] theorem decrypt_encrypt (k n ad p : T.Msg) :
    decrypt k n ad (encrypt k n ad p) = some (aeadpack (true : T.Msg) ad p) :=
  decrypt_eq_some.2 ⟨p, rfl, rfl⟩

theorem validkey_ne_zero (k : T.Msg) : validkey k ≠ zero := fun h => by
  simpa [validkey, zero, free] using congrArg Theory.Msg.view h

@[simp] theorem dhexp_validkey (x k : T.Msg) : dhexp x (validkey k) = some (dhexp_real x k) :=
  dhexp_eq_some.2 (Or.inr ⟨validkey_ne_zero k, k, rfl, rfl⟩)

@[simp] theorem statepack_a₁_pack (hs : T.Msg) : statepack_a₁ (statepack_a hs) = some hs :=
  statepack_a₁_eq_some.2 rfl

@[simp] theorem statepack_b₁_pack (hs : T.Msg) : statepack_b₁ (statepack_b hs) = some hs :=
  statepack_b₁_eq_some.2 rfl

@[simp] theorem statepack_c₁_pack (hs c₁ c₂ : T.Msg) :
    statepack_c₁ (statepack_c hs c₁ c₂) = some hs :=
  statepack_c₁_eq_some.2 ⟨c₁, c₂, rfl⟩

@[simp] theorem statepack_c₂_pack (hs c₁ c₂ : T.Msg) :
    statepack_c₂ (statepack_c hs c₁ c₂) = some c₁ :=
  statepack_c₂_eq_some.2 ⟨hs, c₂, rfl⟩

@[simp] theorem statepack_c₃_pack (hs c₁ c₂ : T.Msg) :
    statepack_c₃ (statepack_c hs c₁ c₂) = some c₂ :=
  statepack_c₃_eq_some.2 ⟨hs, c₁, rfl⟩

@[simp] theorem statepack_d₁_pack (hs c₁ c₂ : T.Msg) :
    statepack_d₁ (statepack_d hs c₁ c₂) = some hs :=
  statepack_d₁_eq_some.2 ⟨c₁, c₂, rfl⟩

@[simp] theorem statepack_d₂_pack (hs c₁ c₂ : T.Msg) :
    statepack_d₂ (statepack_d hs c₁ c₂) = some c₁ :=
  statepack_d₂_eq_some.2 ⟨hs, c₂, rfl⟩

@[simp] theorem statepack_d₃_pack (hs c₁ c₂ : T.Msg) :
    statepack_d₃ (statepack_d hs c₁ c₂) = some c₂ :=
  statepack_d₃_eq_some.2 ⟨hs, c₁, rfl⟩

theorem concat3₁_concat3 (a b c : T.Msg) : concat3₁ (concat3 a b c) = some a :=
  concat3₁_eq_some.2 ⟨b, c, rfl⟩

theorem concat3₃_concat3 (a b c : T.Msg) : concat3₃ (concat3 a b c) = some c :=
  concat3₃_eq_some.2 ⟨a, b, rfl⟩

theorem aeadpack₃_pack (b ad p : T.Msg) : aeadpack₃ (aeadpack b ad p) = some p :=
  aeadpack₃_eq_some.2 ⟨b, ad, rfl⟩

/-! ## The free symbols are injective and distinct -/

theorem app_inl_inj {n : ℕ} {f : Fun n} (hf : free n f = true) {a b : Fin n → T.Msg}
    (h : Theory.Msg.app (.inl f) a = .app (.inl f) b) : a = b := by
  have := congrArg Theory.Msg.view h
  simpa [hf] using this

@[simp] theorem SendMsg_eq_SendMsg {a b c d a' b' c' d' : T.Msg} :
    SendMsg a b c d = SendMsg a' b' c' d' ↔ a = a' ∧ b = b' ∧ c = c' ∧ d = d' :=
  ⟨fun h => by
    have := app_inl_inj (f := .SendMsg) rfl h
    exact ⟨congrFun this 0, congrFun this 1, congrFun this 2, congrFun this 3⟩,
    by rintro ⟨rfl, rfl, rfl, rfl⟩; rfl⟩

@[simp] theorem SendMsg_eq_RecvMsg {a b c d a' b' c' d' : T.Msg} :
    SendMsg a b c d = RecvMsg a' b' c' d' ↔ False :=
  iff_false_intro fun h => by simpa [SendMsg, RecvMsg, free] using congrArg Theory.Msg.view h

@[simp] theorem SendMsg_eq_RecvEnd {a b c d e : T.Msg} : SendMsg a b c d = RecvEnd e ↔ False :=
  iff_false_intro fun h => by simpa [SendMsg, RecvEnd, free] using congrArg Theory.Msg.view h

@[simp] theorem LeakS_eq_SendMsg {a b a' b' c' d' : T.Msg} :
    LeakS a b = SendMsg a' b' c' d' ↔ False :=
  iff_false_intro fun h => by simpa [LeakS, SendMsg, free] using congrArg Theory.Msg.view h

@[simp] theorem LeakS_eq_RecvMsg {a b a' b' c' d' : T.Msg} :
    LeakS a b = RecvMsg a' b' c' d' ↔ False :=
  iff_false_intro fun h => by simpa [LeakS, RecvMsg, free] using congrArg Theory.Msg.view h

@[simp] theorem LeakS_eq_RecvEnd {a b e : T.Msg} : LeakS a b = RecvEnd e ↔ False :=
  iff_false_intro fun h => by simpa [LeakS, RecvEnd, free] using congrArg Theory.Msg.view h

@[simp] theorem alice_eq_bob : alice = bob ↔ False :=
  iff_false_intro fun h => by simpa [alice, bob, free] using congrArg Theory.Msg.view h

@[simp] theorem bob_eq_alice : bob = alice ↔ False :=
  iff_false_intro fun h => by simpa [alice, bob, free] using congrArg Theory.Msg.view h

/-! ## The messages of the handshakes

The session is the first one the protocol starts, `sid`.  The attacker's ephemeral private
key is the public constant `empty`, so its public key is `neX`.  The other messages are
named after the attack, `A` or `B`, and the message of the handshake they belong to. -/

/-- The session identifier: the name the protocol creates. -/
abbrev sid : T.Msg := Names.nonce 0

/-- The key pair standing in for the static keys, which `NN` has none of. -/
def dummy : T.Msg := keypairpack empty empty

/-- The hash of the protocol name. -/
def h₀ : T.Msg := hash somename empty

/-- The hash after the prologue. -/
def h₁ : T.Msg := hash h₀ empty

/-- The initial cipher state, with no key. -/
def cs₀ : T.Msg := cipherstatepack empty minnonce

/-- The initial cipher state after one encryption. -/
def csI : T.Msg := cipherstatepack empty (increment_nonce minnonce)

/-- The symmetric state after the prologue. -/
def ss₀ : T.Msg := symmetricstatepack cs₀ h₀ h₁

/-- The handshake state before message a, of the initiator (`true`) or the responder. -/
def hs₀ (i : T.Msg) : T.Msg := handshakestatepack ss₀ dummy dummy empty empty empty i

/-- The attacker's ephemeral public key. -/
def neX : T.Msg := validkey (dhexp_real empty g)

/-! ### Attack A: the attacker is the initiator, `bob` the responder -/

def hA₂ : T.Msg := hash h₁ neX
def cA_a : T.Msg := encrypt empty minnonce hA₂ empty
/-- The attacker's message a, with the payload `empty`. -/
def mA_a : T.Msg := concat3 neX empty cA_a
def hA₃ : T.Msg := hash hA₂ cA_a
/-- `bob`'s state after message a. -/
def hsA₁ : T.Msg :=
  handshakestatepack (symmetricstatepack csI h₀ hA₃) dummy dummy empty neX empty (false : T.Msg)
/-- `bob`'s ephemeral keys. -/
def pkB : T.Msg := dhexp_real (key_e bob alice sid) g
def neB : T.Msg := validkey pkB
def eB : T.Msg := keypairpack neB (key_e bob alice sid)
def hA₄ : T.Msg := hash hA₃ neB
/-- The shared secret `ee`. -/
def dhA : T.Msg := dhexp_real (key_e bob alice sid) (dhexp_real empty g)
def ckA : T.Msg := hmac_hash1 h₀ dhA
def tkA : T.Msg := hmac_hash2 h₀ dhA
def cA_b : T.Msg := encrypt tkA minnonce hA₄ (msg_b bob alice sid)
/-- `bob`'s message b. -/
def mA_b : T.Msg := concat3 neB empty cA_b
def hA₅ : T.Msg := hash hA₄ cA_b
/-- `bob`'s state after message b. -/
def hsA₂ : T.Msg :=
  handshakestatepack (symmetricstatepack (cipherstatepack tkA (increment_nonce minnonce)) ckA hA₅)
    dummy eB empty neX empty (false : T.Msg)
def k1A : T.Msg := hmac_hash1 ckA zero
def k2A : T.Msg := hmac_hash2 ckA zero
def cs1A : T.Msg := cipherstatepack k1A minnonce
def cs2A : T.Msg := cipherstatepack k2A minnonce
/-- `bob`'s state before message c, with the cipher state `cs1A`. -/
def hsA₂' : T.Msg :=
  handshakestatepack (symmetricstatepack cs1A ckA hA₅) dummy eB empty neX empty (false : T.Msg)
def cA_c : T.Msg := encrypt k1A minnonce hA₅ empty
/-- The attacker's message c, with the payload `empty`. -/
def mA_c : T.Msg := concat3 empty empty cA_c
def hA₆ : T.Msg := hash hA₅ cA_c
def cs1A' : T.Msg := cipherstatepack k1A (increment_nonce minnonce)
/-- `bob`'s state after message c. -/
def hsA₃ : T.Msg :=
  handshakestatepack (symmetricstatepack cs1A' ckA hA₆) dummy eB empty neX empty (false : T.Msg)
/-- `bob`'s state before message d, with the cipher state `cs2A`. -/
def hsA₄ : T.Msg :=
  handshakestatepack (symmetricstatepack cs2A ckA hA₆) dummy eB empty neX empty (false : T.Msg)
def cA_d : T.Msg := encrypt k2A minnonce hA₆ (msg_d bob alice sid)
/-- `bob`'s message d. -/
def mA_d : T.Msg := concat3 empty empty cA_d
/-- `bob`'s state after message d. -/
def hsA₅ : T.Msg :=
  handshakestatepack
    (symmetricstatepack (cipherstatepack k2A (increment_nonce minnonce)) ckA (hash hA₆ cA_d))
    dummy eB empty neX empty (false : T.Msg)

/-- `bob`'s records in the table `statestore`. -/
def recA_a : T.Msg := ((bob, alice, sid, statepack_a (hs₀ (false : T.Msg))) : T.Msg)
def recA_b : T.Msg := ((bob, alice, sid, statepack_b hsA₁) : T.Msg)
def recA_c : T.Msg := ((bob, alice, sid, statepack_c hsA₂ cs1A cs2A) : T.Msg)
def recA_d : T.Msg := ((bob, alice, sid, statepack_d hsA₃ cs1A' cs2A) : T.Msg)

/-! ### Attack B: `alice` is the initiator, the attacker the responder -/

/-- `alice`'s ephemeral keys. -/
def pkA : T.Msg := dhexp_real (key_e alice bob sid) g
def neA : T.Msg := validkey pkA
def eA : T.Msg := keypairpack neA (key_e alice bob sid)
def hB₂ : T.Msg := hash h₁ neA
def cB_a : T.Msg := encrypt empty minnonce hB₂ (msg_a alice bob sid)
/-- `alice`'s message a. -/
def mB_a : T.Msg := concat3 neA empty cB_a
def hB₃ : T.Msg := hash hB₂ cB_a
/-- `alice`'s state after message a. -/
def hsB₁ : T.Msg :=
  handshakestatepack (symmetricstatepack csI h₀ hB₃) dummy eA empty empty empty (true : T.Msg)
def hB₄ : T.Msg := hash hB₃ neX
/-- The shared secret `ee`. -/
def dhB : T.Msg := dhexp_real (key_e alice bob sid) (dhexp_real empty g)
def ckB : T.Msg := hmac_hash1 h₀ dhB
def tkB : T.Msg := hmac_hash2 h₀ dhB
def cB_b : T.Msg := encrypt tkB minnonce hB₄ empty
/-- The attacker's message b, with the payload `empty`. -/
def mB_b : T.Msg := concat3 neX empty cB_b
def hB₅ : T.Msg := hash hB₄ cB_b
def k1B : T.Msg := hmac_hash1 ckB zero
def k2B : T.Msg := hmac_hash2 ckB zero
def cs1B : T.Msg := cipherstatepack k1B minnonce
def cs2B : T.Msg := cipherstatepack k2B minnonce
/-- `alice`'s state after message b. -/
def hsB₂ : T.Msg :=
  handshakestatepack (symmetricstatepack (cipherstatepack tkB (increment_nonce minnonce)) ckB hB₅)
    dummy eA empty neX empty (true : T.Msg)
/-- `alice`'s state before message c, with the cipher state `cs1B`. -/
def hsB₂' : T.Msg :=
  handshakestatepack (symmetricstatepack cs1B ckB hB₅) dummy eA empty neX empty (true : T.Msg)
def cB_c : T.Msg := encrypt k1B minnonce hB₅ (msg_c alice bob sid)
/-- `alice`'s message c. -/
def mB_c : T.Msg := concat3 empty empty cB_c
def hB₆ : T.Msg := hash hB₅ cB_c
def cs1B' : T.Msg := cipherstatepack k1B (increment_nonce minnonce)
/-- `alice`'s state after message c. -/
def hsB₃ : T.Msg :=
  handshakestatepack (symmetricstatepack cs1B' ckB hB₆) dummy eA empty neX empty (true : T.Msg)
/-- `alice`'s state before message d, with the cipher state `cs2B`. -/
def hsB₄ : T.Msg :=
  handshakestatepack (symmetricstatepack cs2B ckB hB₆) dummy eA empty neX empty (true : T.Msg)
def cB_d : T.Msg := encrypt k2B minnonce hB₆ empty
/-- The attacker's message d, with the payload `empty`. -/
def mB_d : T.Msg := concat3 empty empty cB_d
/-- `alice`'s state after message d. -/
def hsB₅ : T.Msg :=
  handshakestatepack
    (symmetricstatepack (cipherstatepack k2B (increment_nonce minnonce)) ckB (hash hB₆ cB_d))
    dummy eA empty neX empty (true : T.Msg)

/-- `alice`'s records in the table `statestore`. -/
def recB_a : T.Msg := ((alice, bob, sid, statepack_a (hs₀ (true : T.Msg))) : T.Msg)
def recB_b : T.Msg := ((alice, bob, sid, statepack_b hsB₁) : T.Msg)
def recB_c : T.Msg := ((alice, bob, sid, statepack_c hsB₂ cs1B cs2B) : T.Msg)
def recB_d : T.Msg := ((alice, bob, sid, statepack_d hsB₃ cs1B' cs2B) : T.Msg)

/-! ## What the protocol computes -/

theorem initialize_initiator_eq :
    initialize_initiator empty (keypairpack empty empty) (keypairpack empty empty) empty empty
      empty = some (hs₀ (true : T.Msg)) := by
  simp [initialize_initiator, NN.mixHash, initializeSymmetric, initializeKey, hs₀, ss₀, cs₀, h₀, h₁,
    dummy]

theorem initialize_responder_eq :
    initialize_responder empty (keypairpack empty empty) (keypairpack empty empty) empty empty
      empty = some (hs₀ (false : T.Msg)) := by
  simp [initialize_responder, NN.mixHash, initializeSymmetric, initializeKey, hs₀, ss₀, cs₀, h₀, h₁,
    dummy]

theorem readMessage_a_A :
    readMessage_a bob alice (hs₀ (false : T.Msg)) mA_a sid =
      some ((hsA₁, empty, (true : T.Msg)) : T.Msg) := by
  simp [readMessage_a, decryptAndHash, decryptWithAd, NN.mixHash, setNonce, hs₀, ss₀, cs₀, csI, mA_a,
    cA_a, hA₂, hA₃, hsA₁]

theorem writeMessage_b_A :
    writeMessage_b bob alice hsA₁ (msg_b bob alice sid) sid =
      some ((hsA₂, mA_b, cs1A, cs2A) : T.Msg) := by
  simp [writeMessage_b, generate_keypair, NN.mixHash, dh, mixKey, hkdf, initializeKey,
    encryptAndHash, encryptWithAd, setNonce, split, hsA₁, hsA₂, mA_b, cA_b, cs1A, cs2A, k1A, k2A,
    hA₄, hA₅, eB, neB, pkB, dhA, ckA, tkA, neX]

theorem handshakestatesetcs_A_c : handshakestatesetcs hsA₂ cs1A = some hsA₂' := by
  simp [hsA₂, hsA₂']

theorem readMessage_c_A :
    readMessage_c bob alice hsA₂' mA_c sid = some ((hsA₃, empty, (true : T.Msg)) : T.Msg) := by
  simp [readMessage_c, decryptAndHash, decryptWithAd, NN.mixHash, setNonce, hsA₂', hsA₃, mA_c, cA_c,
    cs1A, cs1A', hA₆]

theorem handshakestategetcs_A : handshakestategetcs hsA₃ = some cs1A' := by
  simp [hsA₃]

theorem handshakestatesetcs_A_d : handshakestatesetcs hsA₃ cs2A = some hsA₄ := by
  simp [hsA₃, hsA₄]

theorem writeMessage_d_A :
    writeMessage_d bob alice hsA₄ (msg_d bob alice sid) sid = some ((hsA₅, mA_d) : T.Msg) := by
  simp [writeMessage_d, encryptAndHash, encryptWithAd, NN.mixHash, setNonce, hsA₄, hsA₅, mA_d, cA_d,
    cs2A]

theorem writeMessage_a_B :
    writeMessage_a alice bob (hs₀ (true : T.Msg)) (msg_a alice bob sid) sid =
      some ((hsB₁, mB_a) : T.Msg) := by
  simp [writeMessage_a, generate_keypair, NN.mixHash, encryptAndHash, encryptWithAd, setNonce, hs₀,
    ss₀, cs₀, csI, hsB₁, mB_a, cB_a, hB₂, hB₃, eA, neA, pkA]

theorem readMessage_b_B :
    readMessage_b alice bob hsB₁ mB_b sid =
      some ((hsB₂, empty, (true : T.Msg), cs1B, cs2B) : T.Msg) := by
  simp [readMessage_b, NN.mixHash, dh, mixKey, hkdf, initializeKey, decryptAndHash, decryptWithAd,
    setNonce, split, hsB₁, hsB₂, mB_b, cB_b, cs1B, cs2B, k1B, k2B, hB₄, hB₅, eA, neA, pkA, dhB,
    ckB, tkB, neX]

theorem handshakestatesetcs_B_c : handshakestatesetcs hsB₂ cs1B = some hsB₂' := by
  simp [hsB₂, hsB₂']

theorem writeMessage_c_B :
    writeMessage_c alice bob hsB₂' (msg_c alice bob sid) sid = some ((hsB₃, mB_c) : T.Msg) := by
  simp [writeMessage_c, encryptAndHash, encryptWithAd, NN.mixHash, setNonce, hsB₂', hsB₃, mB_c, cB_c,
    cs1B, cs1B', hB₆]

theorem handshakestategetcs_B : handshakestategetcs hsB₃ = some cs1B' := by
  simp [hsB₃]

theorem handshakestatesetcs_B_d : handshakestatesetcs hsB₃ cs2B = some hsB₄ := by
  simp [hsB₃, hsB₄]

theorem readMessage_d_B :
    readMessage_d alice bob hsB₄ mB_d sid = some ((hsB₅, empty, (true : T.Msg)) : T.Msg) := by
  simp [readMessage_d, decryptAndHash, decryptWithAd, NN.mixHash, setNonce, hsB₄, hsB₅, mB_d, cB_d,
    cs2B]

/-! ## What the attacker computes -/

section derive

variable {S : Set T.Msg}

theorem app_mem {n : ℕ} (f : Fun n) (hf : pub n f) {ms : Fin n → T.Msg}
    (hms : ∀ i, ms i ∈ derive S) : Theory.Msg.app (.inl f) ms ∈ derive S :=
  Attacker.app_mem_derive (Attacker.ofDecls_mem hf) hms

theorem app₀_mem (f : Fun 0) (hf : pub 0 f) : Theory.Msg.app (.inl f) ![] ∈ derive S :=
  app_mem f hf fun i => i.elim0

theorem app₁_mem (f : Fun 1) (hf : pub 1 f) {a : T.Msg} (ha : a ∈ derive S) :
    Theory.Msg.app (.inl f) ![a] ∈ derive S :=
  app_mem f hf fun i => by fin_cases i; exact ha

theorem app₂_mem (f : Fun 2) (hf : pub 2 f) {a b : T.Msg} (ha : a ∈ derive S)
    (hb : b ∈ derive S) : Theory.Msg.app (.inl f) ![a, b] ∈ derive S :=
  app_mem f hf fun i => by fin_cases i <;> assumption

theorem app₃_mem (f : Fun 3) (hf : pub 3 f) {a b c : T.Msg} (ha : a ∈ derive S)
    (hb : b ∈ derive S) (hc : c ∈ derive S) : Theory.Msg.app (.inl f) ![a, b, c] ∈ derive S :=
  app_mem f hf fun i => by fin_cases i <;> assumption

theorem app₄_mem (f : Fun 4) (hf : pub 4 f) {a b c d : T.Msg} (ha : a ∈ derive S)
    (hb : b ∈ derive S) (hc : c ∈ derive S) (hd : d ∈ derive S) :
    Theory.Msg.app (.inl f) ![a, b, c, d] ∈ derive S :=
  app_mem f hf fun i => by fin_cases i <;> assumption

theorem pub'_mem : pub' ∈ derive S := app₀_mem .pub' trivial
theorem empty_mem : empty ∈ derive S := app₀_mem .empty trivial
theorem g_mem : g ∈ derive S := app₀_mem .g trivial
theorem zero_mem : zero ∈ derive S := app₀_mem .zero trivial
theorem minnonce_mem : minnonce ∈ derive S := app₀_mem .minnonce trivial
theorem somename_mem : somename ∈ derive S := app₀_mem .somename trivial

theorem hash_mem {a b : T.Msg} (ha : a ∈ derive S) (hb : b ∈ derive S) :
    NN.hash a b ∈ derive S :=
  app₂_mem .hash trivial ha hb

theorem hmac_hash1_mem {a b : T.Msg} (ha : a ∈ derive S) (hb : b ∈ derive S) :
    hmac_hash1 a b ∈ derive S :=
  app₂_mem .hmac_hash1 trivial ha hb

theorem hmac_hash2_mem {a b : T.Msg} (ha : a ∈ derive S) (hb : b ∈ derive S) :
    hmac_hash2 a b ∈ derive S :=
  app₂_mem .hmac_hash2 trivial ha hb

theorem encrypt_mem {k n ad p : T.Msg} (hk : k ∈ derive S) (hn : n ∈ derive S)
    (had : ad ∈ derive S) (hp : p ∈ derive S) : encrypt k n ad p ∈ derive S :=
  app₄_mem .encrypt trivial hk hn had hp

theorem concat3_mem {a b c : T.Msg} (ha : a ∈ derive S) (hb : b ∈ derive S) (hc : c ∈ derive S) :
    concat3 a b c ∈ derive S :=
  app₃_mem .concat3 trivial ha hb hc

theorem concat3₁_mem {a b c : T.Msg} (h : concat3 a b c ∈ derive S) : a ∈ derive S :=
  Attacker.dtor_mem_derive (f := fun a => concat3₁ (a 0)) (Attacker.ofDecls_mem_dtor (by simp))
    (ms := ![concat3 a b c]) (fun i => by fin_cases i; exact h) (concat3₁_concat3 a b c)

theorem concat3₃_mem {a b c : T.Msg} (h : concat3 a b c ∈ derive S) : c ∈ derive S :=
  Attacker.dtor_mem_derive (f := fun a => concat3₃ (a 0)) (Attacker.ofDecls_mem_dtor (by simp))
    (ms := ![concat3 a b c]) (fun i => by fin_cases i; exact h) (concat3₃_concat3 a b c)

theorem aeadpack₃_mem {b ad p : T.Msg} (h : aeadpack b ad p ∈ derive S) : p ∈ derive S :=
  Attacker.dtor_mem_derive (f := fun a => aeadpack₃ (a 0)) (Attacker.ofDecls_mem_dtor (by simp))
    (ms := ![aeadpack b ad p]) (fun i => by fin_cases i; exact h) (aeadpack₃_pack b ad p)

theorem decrypt_mem {k n ad p : T.Msg} (hk : k ∈ derive S) (hn : n ∈ derive S)
    (had : ad ∈ derive S) (hc : encrypt k n ad p ∈ derive S) :
    aeadpack (true : T.Msg) ad p ∈ derive S :=
  Attacker.dtor_mem_derive (f := fun a => decrypt (a 0) (a 1) (a 2) (a 3))
    (Attacker.ofDecls_mem_dtor (by simp)) (ms := ![k, n, ad, encrypt k n ad p])
    (fun i => by fin_cases i <;> assumption) (decrypt_encrypt k n ad p)

theorem dhexp_mem {x k : T.Msg} (hx : x ∈ derive S) (hk : validkey k ∈ derive S) :
    dhexp_real x k ∈ derive S :=
  Attacker.dtor_mem_derive (f := fun a => dhexp (a 0) (a 1)) (Attacker.ofDecls_mem_dtor (by simp))
    (ms := ![x, validkey k]) (fun i => by fin_cases i <;> assumption) (dhexp_validkey x k)

theorem h₀_mem : h₀ ∈ derive S := hash_mem somename_mem empty_mem
theorem h₁_mem : h₁ ∈ derive S := hash_mem h₀_mem empty_mem
theorem neX_mem : neX ∈ derive S :=
  app₁_mem .validkey trivial (app₂_mem .dhexp_real trivial empty_mem g_mem)

/-! ### Attack A -/

theorem hA₂_mem : hA₂ ∈ derive S := hash_mem h₁_mem neX_mem
theorem cA_a_mem : cA_a ∈ derive S := encrypt_mem empty_mem minnonce_mem hA₂_mem empty_mem
theorem mA_a_mem : mA_a ∈ derive S := concat3_mem neX_mem empty_mem cA_a_mem
theorem hA₃_mem : hA₃ ∈ derive S := hash_mem hA₂_mem cA_a_mem

/-- From `bob`'s message b the attacker derives the shared secret, by the equation. -/
theorem dhA_mem (hmb : mA_b ∈ derive S) : dhA ∈ derive S := by
  have h : dhexp_real empty pkB ∈ derive S := dhexp_mem empty_mem (concat3₁_mem hmb)
  rw [dhA, ← equation₁]
  exact h

theorem ckA_mem (hmb : mA_b ∈ derive S) : ckA ∈ derive S := hmac_hash1_mem h₀_mem (dhA_mem hmb)
theorem tkA_mem (hmb : mA_b ∈ derive S) : tkA ∈ derive S := hmac_hash2_mem h₀_mem (dhA_mem hmb)
theorem hA₄_mem (hmb : mA_b ∈ derive S) : hA₄ ∈ derive S := hash_mem hA₃_mem (concat3₁_mem hmb)
theorem hA₅_mem (hmb : mA_b ∈ derive S) : hA₅ ∈ derive S :=
  hash_mem (hA₄_mem hmb) (concat3₃_mem hmb)

/-- The attacker reads `bob`'s message b. -/
theorem msg_b_mem (hmb : mA_b ∈ derive S) : msg_b bob alice sid ∈ derive S :=
  aeadpack₃_mem (decrypt_mem (tkA_mem hmb) minnonce_mem (hA₄_mem hmb) (concat3₃_mem hmb))

theorem cA_c_mem (hmb : mA_b ∈ derive S) : cA_c ∈ derive S :=
  encrypt_mem (hmac_hash1_mem (ckA_mem hmb) zero_mem) minnonce_mem (hA₅_mem hmb) empty_mem

theorem mA_c_mem (hmb : mA_b ∈ derive S) : mA_c ∈ derive S :=
  concat3_mem empty_mem empty_mem (cA_c_mem hmb)

/-- The attacker reads `bob`'s message d. -/
theorem msg_d_mem (hmb : mA_b ∈ derive S) (hmd : mA_d ∈ derive S) :
    msg_d bob alice sid ∈ derive S :=
  aeadpack₃_mem (decrypt_mem (hmac_hash2_mem (ckA_mem hmb) zero_mem) minnonce_mem
    (hash_mem (hA₅_mem hmb) (cA_c_mem hmb)) (concat3₃_mem hmd))

/-! ### Attack B -/

theorem hB₂_mem (hma : mB_a ∈ derive S) : hB₂ ∈ derive S := hash_mem h₁_mem (concat3₁_mem hma)

/-- The attacker reads `alice`'s message a, which is encrypted under no key. -/
theorem msg_a_mem (hma : mB_a ∈ derive S) : msg_a alice bob sid ∈ derive S :=
  aeadpack₃_mem (decrypt_mem empty_mem minnonce_mem (hB₂_mem hma) (concat3₃_mem hma))

theorem hB₃_mem (hma : mB_a ∈ derive S) : hB₃ ∈ derive S :=
  hash_mem (hB₂_mem hma) (concat3₃_mem hma)

/-- From `alice`'s message a the attacker derives the shared secret, by the equation. -/
theorem dhB_mem (hma : mB_a ∈ derive S) : dhB ∈ derive S := by
  have h : dhexp_real empty pkA ∈ derive S := dhexp_mem empty_mem (concat3₁_mem hma)
  rw [dhB, ← equation₁]
  exact h

theorem ckB_mem (hma : mB_a ∈ derive S) : ckB ∈ derive S := hmac_hash1_mem h₀_mem (dhB_mem hma)
theorem hB₄_mem (hma : mB_a ∈ derive S) : hB₄ ∈ derive S := hash_mem (hB₃_mem hma) neX_mem
theorem cB_b_mem (hma : mB_a ∈ derive S) : cB_b ∈ derive S :=
  encrypt_mem (hmac_hash2_mem h₀_mem (dhB_mem hma)) minnonce_mem (hB₄_mem hma) empty_mem
theorem mB_b_mem (hma : mB_a ∈ derive S) : mB_b ∈ derive S :=
  concat3_mem neX_mem empty_mem (cB_b_mem hma)
theorem hB₅_mem (hma : mB_a ∈ derive S) : hB₅ ∈ derive S := hash_mem (hB₄_mem hma) (cB_b_mem hma)

/-- The attacker reads `alice`'s message c. -/
theorem msg_c_mem (hma : mB_a ∈ derive S) (hmc : mB_c ∈ derive S) :
    msg_c alice bob sid ∈ derive S :=
  aeadpack₃_mem (decrypt_mem (hmac_hash1_mem (ckB_mem hma) zero_mem) minnonce_mem (hB₅_mem hma)
    (concat3₃_mem hmc))

theorem mB_d_mem (hma : mB_a ∈ derive S) (hmc : mB_c ∈ derive S) : mB_d ∈ derive S :=
  concat3_mem empty_mem empty_mem (encrypt_mem (hmac_hash2_mem (ckB_mem hma) zero_mem)
    minnonce_mem (hash_mem (hB₅_mem hma) (concat3₃_mem hmc)) empty_mem)

end derive

/-! ## The attacks

The protocol's share of an attack is a trace of `system`: of the one session, in which
one of the four principals' processes runs and the others stay idle. -/

theorem initiator_nil (me them sid : T.Msg) : Cont.Nil (initiator me them sid) := by
  unfold initiator
  aesop (config := { enableSimp := false }) (add norm (by dsimp only))

theorem responder_nil (me them sid : T.Msg) : Cont.Nil (responder me them sid) := by
  unfold responder
  aesop (config := { enableSimp := false }) (add norm (by dsimp only))

/-! ### Attack A -/

/-- `bob`'s actions in attack A. -/
def restA : Trace T.Msg :=
  [.comm statestore recA_a, .inp pub' mA_a, .event (RecvMsg bob alice (stagepack_a sid) empty),
    .comm statestore recA_b, .event (SendMsg bob alice (stagepack_b sid) (msg_b bob alice sid)),
    .out pub' mA_b, .comm statestore recA_c, .inp pub' mA_c,
    .event (RecvMsg bob alice (stagepack_c sid) empty), .comm statestore recA_d,
    .event (SendMsg bob alice (stagepack_d sid) (msg_d bob alice sid)), .out pub' mA_d]

/-- The protocol's actions in attack A. -/
def uA : Trace T.Msg := .out pub' (key_s charlie) :: .new 0 :: restA

theorem restA_mem : restA ∈ Proc.run (responder bob alice sid) := by
  simp only [responder, Proc.run, ContT.run_bind, ContT.run_mk, Bool.false_eq_true, if_true,
    if_false, initialize_responder_eq]
  refine Proc.mem_par_seq
    (l := [.comm statestore recA_a, .inp pub' mA_a,
      .event (RecvMsg bob alice (stagepack_a sid) empty), .comm statestore recA_b,
      .event (SendMsg bob alice (stagepack_b sid) (msg_b bob alice sid)), .out pub' mA_b])
    (r := [.inp pub' mA_c, .event (RecvMsg bob alice (stagepack_c sid) empty),
      .comm statestore recA_d, .event (SendMsg bob alice (stagepack_d sid) (msg_d bob alice sid)),
      .out pub' mA_d])
    rfl ?_ ?_ (by simp [restA])
  · refine Proc.mem_par_seq
      (l := [.comm statestore recA_a, .inp pub' mA_a,
        .event (RecvMsg bob alice (stagepack_a sid) empty)])
      (r := [.event (SendMsg bob alice (stagepack_b sid) (msg_b bob alice sid)), .out pub' mA_b,
        .out statestore recA_c])
      rfl ?_ ?_ (by simp)
    · refine Proc.mem_par_seq (l := [])
        (r := [.inp pub' mA_a, .event (RecvMsg bob alice (stagepack_a sid) empty),
          .out statestore recA_b])
        rfl ?_ ?_ (by simp)
      · -- The record of the initial state is inserted.
        exact Proc.mem_par_left (Proc.mem_bang (Proc.mem_act Proc.nil_mem_nil)
          (Proc.nil_mem_act _ _) (by simp)) Proc.nil_mem_nil (by simp)
      · -- Message a is read.
        refine Proc.mem_inp ?_
        simp only [recA_a, Tuple.ofMsg_toMsg, if_true, statepack_a₁_pack,
          ContT.run_bind, ContT.run_mk]
        refine Proc.mem_inp ?_
        simp only [readMessage_a_A, Tuple.ofMsg_toMsg, ContT.run_bind, ContT.run_mk,
          Bool.false_eq_true, if_true, if_false]
        refine Proc.mem_act ?_
        exact Proc.mem_par_left (Proc.mem_bang (Proc.mem_act Proc.nil_mem_nil)
          (Proc.nil_mem_act _ _) (by simp)) Proc.nil_mem_nil (by simp)
    · -- Message b is written.
      refine Proc.mem_inp ?_
      simp only [recA_b, Tuple.ofMsg_toMsg, if_true, statepack_b₁_pack,
        writeMessage_b_A, ContT.run_bind, ContT.run_mk, Bool.false_eq_true, if_false]
      refine Proc.mem_act ?_
      exact Proc.mem_par (s := [(1, .out pub' mA_b), (0, .out statestore recA_c)])
        (l := [.out statestore recA_c]) (r := [.out pub' mA_b]) rfl rfl
        (Proc.mem_bang (Proc.mem_act Proc.nil_mem_nil) (Proc.nil_mem_act _ _) (by simp))
        (Proc.mem_act Proc.nil_mem_nil) (by comms) (by simp)
  · refine Proc.mem_bang ?_ (Proc.nil_mem_par (Proc.nil_mem_inp _ _)
      (Proc.nil_mem_bang (Proc.nil_mem_par (Proc.nil_mem_inp _ _) Proc.nil_mem_nil))) (by simp)
    refine Proc.mem_par_seq
      (l := [.inp statestore recA_c, .inp pub' mA_c,
        .event (RecvMsg bob alice (stagepack_c sid) empty)])
      (r := [.event (SendMsg bob alice (stagepack_d sid) (msg_d bob alice sid)), .out pub' mA_d])
      rfl ?_ ?_ (by simp)
    · -- Message c is read.
      refine Proc.mem_inp ?_
      simp only [recA_c, Tuple.ofMsg_toMsg, if_true, statepack_c₁_pack,
        statepack_c₂_pack, statepack_c₃_pack, handshakestatesetcs_A_c, ContT.run_bind,
        ContT.run_mk]
      refine Proc.mem_inp ?_
      simp only [readMessage_c_A, Tuple.ofMsg_toMsg, handshakestategetcs_A, Option.bind_eq_bind,
        Option.bind, ContT.run_bind, ContT.run_mk]
      refine Proc.mem_act ?_
      exact Proc.mem_par_left (Proc.mem_bang (Proc.mem_act Proc.nil_mem_nil)
        (Proc.nil_mem_act _ _) (by simp)) Proc.nil_mem_nil (by simp)
    · -- Message d is written.
      refine Proc.mem_bang ?_ (Proc.nil_mem_par (Proc.nil_mem_inp _ _) Proc.nil_mem_nil) (by simp)
      refine Proc.mem_par_left ?_ Proc.nil_mem_nil (by simp)
      refine Proc.mem_inp ?_
      simp only [recA_d, Tuple.ofMsg_toMsg, if_true, statepack_d₁_pack,
        statepack_d₂_pack, statepack_d₃_pack, handshakestatesetcs_A_d, writeMessage_d_A,
        ContT.run_bind, ContT.run_mk]
      exact Proc.mem_act (Proc.mem_act Proc.nil_mem_nil)

theorem uA_mem : uA ∈ system := by
  simp only [system, Proc.run, ContT.run_bind, ContT.run_mk, Bool.false_eq_true, if_true, if_false]
  refine Proc.mem_act (Proc.mem_bang (Proc.mem_new ?_ (by simp [restA])) (Proc.nil_mem_new _)
    (by simp [restA]))
  exact Proc.mem_par_left (Proc.mem_par_right (Proc.nil_mem_par
    (Cont.Nil.run (initiator_nil _ _ _)) (Cont.Nil.run (initiator_nil _ _ _))) restA_mem
    (by simp [restA])) (Cont.Nil.run (responder_nil _ _ _)) (by simp [restA])

theorem dualA_mem : uA.dual ∈ Enemy ∅ := by
  simp only [uA, restA, Trace.dual_out, Trace.dual_inp, Trace.dual_comm, Trace.dual_new,
    Trace.dual_event, Trace.dual_nil]
  exact Enemy.inp _ _ pub'_mem (Enemy.out _ _ pub'_mem mA_a_mem (Enemy.inp _ _ pub'_mem
    (Enemy.out _ _ pub'_mem (mA_c_mem (derive.le_closure _ (Set.mem_insert _ _)))
      (Enemy.inp _ _ pub'_mem .nil))))

/-- Attack A. -/
theorem tA_mem : uA.complete ∈ system.Attacks :=
  Proc.mem_attacks uA_mem dualA_mem (by simp [uA, restA])

theorem knowsA_b : (Fact.knows (msg_b bob alice sid)).Holds uA.complete :=
  Fact.holds_knows_of_derive (msg_b_mem (derive.le_closure _
    (show ∃ c, Act.comm c mA_b ∈ uA.complete ∧ c ∈ derive ∅ from
      ⟨pub', by simp [uA, restA], pub'_mem⟩)))

theorem knowsA_d : (Fact.knows (msg_d bob alice sid)).Holds uA.complete :=
  Fact.holds_knows_of_derive (msg_d_mem
    (derive.le_closure _ (show ∃ c, Act.comm c mA_b ∈ uA.complete ∧ c ∈ derive ∅ from
      ⟨pub', by simp [uA, restA], pub'_mem⟩))
    (derive.le_closure _ (show ∃ c, Act.comm c mA_d ∈ uA.complete ∧ c ∈ derive ∅ from
      ⟨pub', by simp [uA, restA], pub'_mem⟩)))

/-! ### Attack B -/

/-- `alice`'s actions in attack B. -/
def restB : Trace T.Msg :=
  [.comm statestore recB_a, .event (SendMsg alice bob (stagepack_a sid) (msg_a alice bob sid)),
    .out pub' mB_a, .comm statestore recB_b, .inp pub' mB_b,
    .event (RecvMsg alice bob (stagepack_b sid) empty), .comm statestore recB_c,
    .event (SendMsg alice bob (stagepack_c sid) (msg_c alice bob sid)), .out pub' mB_c,
    .comm statestore recB_d, .inp pub' mB_d, .event (RecvMsg alice bob (stagepack_d sid) empty),
    .event (RecvEnd (true : T.Msg))]

/-- The protocol's actions in attack B. -/
def uB : Trace T.Msg := .out pub' (key_s charlie) :: .new 0 :: restB

theorem restB_mem : restB ∈ Proc.run (initiator alice bob sid) := by
  simp only [initiator, Proc.run, ContT.run_bind, ContT.run_mk, Bool.false_eq_true, if_true,
    if_false, initialize_initiator_eq]
  refine Proc.mem_par_seq
    (l := [.comm statestore recB_a,
      .event (SendMsg alice bob (stagepack_a sid) (msg_a alice bob sid)), .out pub' mB_a,
      .comm statestore recB_b, .inp pub' mB_b, .event (RecvMsg alice bob (stagepack_b sid) empty)])
    (r := [.event (SendMsg alice bob (stagepack_c sid) (msg_c alice bob sid)), .out pub' mB_c,
      .comm statestore recB_d, .inp pub' mB_d, .event (RecvMsg alice bob (stagepack_d sid) empty),
      .event (RecvEnd (true : T.Msg))])
    rfl ?_ ?_ (by simp [restB])
  · refine Proc.mem_par_seq
      (l := [.comm statestore recB_a,
        .event (SendMsg alice bob (stagepack_a sid) (msg_a alice bob sid)), .out pub' mB_a])
      (r := [.inp pub' mB_b, .event (RecvMsg alice bob (stagepack_b sid) empty),
        .out statestore recB_c])
      rfl ?_ ?_ (by simp)
    · refine Proc.mem_par_seq (l := [])
        (r := [.event (SendMsg alice bob (stagepack_a sid) (msg_a alice bob sid)), .out pub' mB_a,
          .out statestore recB_b])
        rfl ?_ ?_ (by simp)
      · -- The record of the initial state is inserted.
        exact Proc.mem_par_left (Proc.mem_bang (Proc.mem_act Proc.nil_mem_nil)
          (Proc.nil_mem_act _ _) (by simp)) Proc.nil_mem_nil (by simp)
      · -- Message a is written.
        refine Proc.mem_inp ?_
        simp only [recB_a, Tuple.ofMsg_toMsg, if_true, statepack_a₁_pack,
          writeMessage_a_B, ContT.run_bind, ContT.run_mk, Bool.false_eq_true, if_false]
        refine Proc.mem_act ?_
        exact Proc.mem_par (s := [(1, .out pub' mB_a), (0, .out statestore recB_b)])
          (l := [.out statestore recB_b]) (r := [.out pub' mB_a]) rfl rfl
          (Proc.mem_bang (Proc.mem_act Proc.nil_mem_nil) (Proc.nil_mem_act _ _) (by simp))
          (Proc.mem_act Proc.nil_mem_nil) (by comms) (by simp)
    · -- Message b is read.
      refine Proc.mem_inp ?_
      simp only [recB_b, Tuple.ofMsg_toMsg, if_true, statepack_b₁_pack,
        ContT.run_bind, ContT.run_mk]
      refine Proc.mem_inp ?_
      simp only [readMessage_b_B, Tuple.ofMsg_toMsg, ContT.run_bind, ContT.run_mk,
        Bool.false_eq_true, if_true, if_false]
      refine Proc.mem_act ?_
      exact Proc.mem_par_left (Proc.mem_bang (Proc.mem_act Proc.nil_mem_nil)
        (Proc.nil_mem_act _ _) (by simp)) Proc.nil_mem_nil (by simp)
  · refine Proc.mem_bang ?_ (Proc.nil_mem_par (Proc.nil_mem_inp _ _)
      (Proc.nil_mem_bang (Proc.nil_mem_par (Proc.nil_mem_inp _ _) Proc.nil_mem_nil))) (by simp)
    refine Proc.mem_par_seq
      (l := [.inp statestore recB_c,
        .event (SendMsg alice bob (stagepack_c sid) (msg_c alice bob sid)), .out pub' mB_c])
      (r := [.inp pub' mB_d, .event (RecvMsg alice bob (stagepack_d sid) empty),
        .event (RecvEnd (true : T.Msg))])
      rfl ?_ ?_ (by simp)
    · -- Message c is written.
      refine Proc.mem_inp ?_
      simp only [recB_c, Tuple.ofMsg_toMsg, if_true, statepack_c₁_pack,
        statepack_c₂_pack, statepack_c₃_pack, handshakestatesetcs_B_c, writeMessage_c_B,
        handshakestategetcs_B, Option.bind_eq_bind, Option.bind, ContT.run_bind, ContT.run_mk]
      refine Proc.mem_act ?_
      exact Proc.mem_par (s := [(1, .out pub' mB_c), (0, .out statestore recB_d)])
        (l := [.out statestore recB_d]) (r := [.out pub' mB_c]) rfl rfl
        (Proc.mem_bang (Proc.mem_act Proc.nil_mem_nil) (Proc.nil_mem_act _ _) (by simp))
        (Proc.mem_act Proc.nil_mem_nil) (by comms) (by simp)
    · -- Message d is read, and the handshake ends.
      refine Proc.mem_bang ?_ (Proc.nil_mem_par (Proc.nil_mem_inp _ _) Proc.nil_mem_nil) (by simp)
      refine Proc.mem_par_left ?_ Proc.nil_mem_nil (by simp)
      refine Proc.mem_inp ?_
      simp only [recB_d, Tuple.ofMsg_toMsg, if_true, statepack_d₁_pack,
        statepack_d₂_pack, statepack_d₃_pack, handshakestatesetcs_B_d, ContT.run_bind,
        ContT.run_mk]
      refine Proc.mem_inp ?_
      simp only [readMessage_d_B, Tuple.ofMsg_toMsg, ContT.run_bind, ContT.run_mk]
      exact Proc.mem_act (Proc.mem_act Proc.nil_mem_nil)

theorem uB_mem : uB ∈ system := by
  simp only [system, Proc.run, ContT.run_bind, ContT.run_mk, Bool.false_eq_true, if_true, if_false]
  refine Proc.mem_act (Proc.mem_bang (Proc.mem_new ?_ (by simp [restB])) (Proc.nil_mem_new _)
    (by simp [restB]))
  exact Proc.mem_par_left (Proc.mem_par_left (Proc.mem_par_left restB_mem
    (Cont.Nil.run (initiator_nil _ _ _)) (by simp [restB])) (Cont.Nil.run (responder_nil _ _ _))
    (by simp [restB])) (Cont.Nil.run (responder_nil _ _ _)) (by simp [restB])

theorem dualB_mem : uB.dual ∈ Enemy ∅ := by
  simp only [uB, restB, Trace.dual_out, Trace.dual_inp, Trace.dual_comm, Trace.dual_new,
    Trace.dual_event, Trace.dual_nil]
  exact Enemy.inp _ _ pub'_mem (Enemy.inp _ _ pub'_mem (Enemy.out _ _ pub'_mem
    (mB_b_mem (derive.le_closure _ (Set.mem_insert _ _))) (Enemy.inp _ _ pub'_mem
      (Enemy.out _ _ pub'_mem (mB_d_mem (derive.le_closure _ (Set.mem_insert_of_mem _
        (Set.mem_insert _ _))) (derive.le_closure _ (Set.mem_insert _ _))) .nil))))

/-- Attack B. -/
theorem tB_mem : uB.complete ∈ system.Attacks :=
  Proc.mem_attacks uB_mem dualB_mem (by simp [uB, restB])

theorem knowsB_a : (Fact.knows (msg_a alice bob sid)).Holds uB.complete :=
  Fact.holds_knows_of_derive (msg_a_mem (derive.le_closure _
    (show ∃ c, Act.comm c mB_a ∈ uB.complete ∧ c ∈ derive ∅ from
      ⟨pub', by simp [uB, restB], pub'_mem⟩)))

theorem knowsB_c : (Fact.knows (msg_c alice bob sid)).Holds uB.complete :=
  Fact.holds_knows_of_derive (msg_c_mem
    (derive.le_closure _ (show ∃ c, Act.comm c mB_a ∈ uB.complete ∧ c ∈ derive ∅ from
      ⟨pub', by simp [uB, restB], pub'_mem⟩))
    (derive.le_closure _ (show ∃ c, Act.comm c mB_c ∈ uB.complete ∧ c ∈ derive ∅ from
      ⟨pub', by simp [uB, restB], pub'_mem⟩)))

/-! ## The queries

Each query of the model fails: a `Corr` fails since the event received has no sending
event in the attack, a `Secret` since the attacker knows the payload, a general query since
no event of its hypothesis occurs, and `query₃₇` since `alice` ends the handshake. -/

/-- Refutes a hypothesis whose facts are events absent from the attack. -/
macro "no_events" : tactic =>
  `(tactic| (simp [Hyp.map, Hyp.facts]) <;> (repeat' constructor) <;>
    exact QFact.not_holdsAt_event (by simp [uA, restA, uB, restB]))

/-- The receptions of the attacks as facts at a step: `bob` receives messages `a` and `c`
with the payload `empty` in attack A, `alice` messages `b` and `d` in attack B. -/
theorem recvA_a : ∃ i ≤ uA.complete.length,
    (QFact.event (RecvMsg bob alice (stagepack_a sid) empty)).HoldsAt uA.complete i :=
  (Fact.holds_iff_holdsAt _ (.event _)).1 (by simp [Fact.Holds, uA, restA])

theorem recvB_b : ∃ i ≤ uB.complete.length,
    (QFact.event (RecvMsg alice bob (stagepack_b sid) empty)).HoldsAt uB.complete i :=
  (Fact.holds_iff_holdsAt _ (.event _)).1 (by simp [Fact.Holds, uB, restB])

theorem recvA_c : ∃ i ≤ uA.complete.length,
    (QFact.event (RecvMsg bob alice (stagepack_c sid) empty)).HoldsAt uA.complete i :=
  (Fact.holds_iff_holdsAt _ (.event _)).1 (by simp [Fact.Holds, uA, restA])

theorem recvB_d : ∃ i ≤ uB.complete.length,
    (QFact.event (RecvMsg alice bob (stagepack_d sid) empty)).HoldsAt uB.complete i :=
  (Fact.holds_iff_holdsAt _ (.event _)).1 (by simp [Fact.Holds, uB, restB])

/-! ### Message a -/

theorem not_query₁ : ¬ query₁ := fun h => by
  obtain ⟨σ', -, h'⟩ := h (fun v => match v with | .sid_b => sid | _ => empty) _ tA_mem
    (by simp [Fact.Holds, uA, restA])
  simp [Fact.Holds, uA, restA] at h'

theorem not_query₂ : ¬ query₂ :=
  Proc.not_satisfies_single tA_mem (fun v => match v with | .sid_b => sid | _ => empty) recvA_a
    fun _ _ => Hyp.Refuted.of_facts (by no_events)

theorem not_query₃ : ¬ query₃ :=
  Proc.not_satisfies_single tA_mem (fun v => match v with | .sid_b => sid | _ => empty) recvA_a
    fun _ _ => Hyp.Refuted.of_facts (by no_events)

theorem not_query₄ : ¬ query₄ :=
  Proc.not_satisfies_single tA_mem (fun v => match v with | .sid_b => sid | _ => empty) recvA_a
    fun _ _ => Hyp.Refuted.of_facts (by no_events)

theorem not_query₅ : ¬ query₅ :=
  Proc.not_satisfies_single tA_mem (fun v => match v with | .sid_b => sid | _ => empty) recvA_a
    fun _ _ => Hyp.Refuted.of_facts (by no_events)

theorem not_query₆ : ¬ query₆ := fun h => h (fun _ => sid) _ tB_mem knowsB_a

theorem not_query₇ : ¬ query₇ := fun h => h (fun _ => sid) _ tB_mem knowsB_a

theorem not_query₈ : ¬ query₈ :=
  Proc.not_satisfies_single tB_mem (fun _ => sid)
    ((Fact.holds_iff_holdsAt _ (.knows _)).1 knowsB_a) fun _ _ => Hyp.Refuted.of_facts (by no_events)

theorem not_query₉ : ¬ query₉ := fun h => h (fun _ => sid) _ tB_mem knowsB_a

/-! ### Message b -/

theorem not_query₁₀ : ¬ query₁₀ := fun h => by
  obtain ⟨σ', -, h'⟩ := h (fun v => match v with | .sid_a => sid | _ => empty) _ tB_mem
    (by simp [Fact.Holds, uB, restB])
  simp [Fact.Holds, uB, restB] at h'

theorem not_query₁₁ : ¬ query₁₁ :=
  Proc.not_satisfies_single tB_mem (fun v => match v with | .sid_a => sid | _ => empty) recvB_b
    fun _ _ => Hyp.Refuted.of_facts (by no_events)

theorem not_query₁₂ : ¬ query₁₂ :=
  Proc.not_satisfies_single tB_mem (fun v => match v with | .sid_a => sid | _ => empty) recvB_b
    fun _ _ => Hyp.Refuted.of_facts (by no_events)

theorem not_query₁₃ : ¬ query₁₃ :=
  Proc.not_satisfies_single tB_mem (fun v => match v with | .sid_a => sid | _ => empty) recvB_b
    fun _ _ => Hyp.Refuted.of_facts (by no_events)

theorem not_query₁₄ : ¬ query₁₄ :=
  Proc.not_satisfies_single tB_mem (fun v => match v with | .sid_a => sid | _ => empty) recvB_b
    fun _ _ => Hyp.Refuted.of_facts (by no_events)

theorem not_query₁₅ : ¬ query₁₅ := fun h => h (fun _ => sid) _ tA_mem knowsA_b

theorem not_query₁₆ : ¬ query₁₆ := fun h => h (fun _ => sid) _ tA_mem knowsA_b

theorem not_query₁₇ : ¬ query₁₇ :=
  Proc.not_satisfies_single tA_mem (fun _ => sid)
    ((Fact.holds_iff_holdsAt _ (.knows _)).1 knowsA_b) fun _ _ => Hyp.Refuted.of_facts (by no_events)

theorem not_query₁₈ : ¬ query₁₈ := fun h => h (fun _ => sid) _ tA_mem knowsA_b

/-! ### Message c -/

theorem not_query₁₉ : ¬ query₁₉ := fun h => by
  obtain ⟨σ', -, h'⟩ := h (fun v => match v with | .sid_b => sid | _ => empty) _ tA_mem
    (by simp [Fact.Holds, uA, restA])
  simp [Fact.Holds, uA, restA] at h'

theorem not_query₂₀ : ¬ query₂₀ :=
  Proc.not_satisfies_single tA_mem (fun v => match v with | .sid_b => sid | _ => empty) recvA_c
    fun _ _ => Hyp.Refuted.of_facts (by no_events)

theorem not_query₂₁ : ¬ query₂₁ :=
  Proc.not_satisfies_single tA_mem (fun v => match v with | .sid_b => sid | _ => empty) recvA_c
    fun _ _ => Hyp.Refuted.of_facts (by no_events)

theorem not_query₂₂ : ¬ query₂₂ :=
  Proc.not_satisfies_single tA_mem (fun v => match v with | .sid_b => sid | _ => empty) recvA_c
    fun _ _ => Hyp.Refuted.of_facts (by no_events)

theorem not_query₂₃ : ¬ query₂₃ :=
  Proc.not_satisfies_single tA_mem (fun v => match v with | .sid_b => sid | _ => empty) recvA_c
    fun _ _ => Hyp.Refuted.of_facts (by no_events)

theorem not_query₂₄ : ¬ query₂₄ := fun h => h (fun _ => sid) _ tB_mem knowsB_c

theorem not_query₂₅ : ¬ query₂₅ := fun h => h (fun _ => sid) _ tB_mem knowsB_c

theorem not_query₂₆ : ¬ query₂₆ :=
  Proc.not_satisfies_single tB_mem (fun _ => sid)
    ((Fact.holds_iff_holdsAt _ (.knows _)).1 knowsB_c) fun _ _ => Hyp.Refuted.of_facts (by no_events)

theorem not_query₂₇ : ¬ query₂₇ := fun h => h (fun _ => sid) _ tB_mem knowsB_c

/-! ### Message d -/

theorem not_query₂₈ : ¬ query₂₈ := fun h => by
  obtain ⟨σ', -, h'⟩ := h (fun v => match v with | .sid_a => sid | _ => empty) _ tB_mem
    (by simp [Fact.Holds, uB, restB])
  simp [Fact.Holds, uB, restB] at h'

theorem not_query₂₉ : ¬ query₂₉ :=
  Proc.not_satisfies_single tB_mem (fun v => match v with | .sid_a => sid | _ => empty) recvB_d
    fun _ _ => Hyp.Refuted.of_facts (by no_events)

theorem not_query₃₀ : ¬ query₃₀ :=
  Proc.not_satisfies_single tB_mem (fun v => match v with | .sid_a => sid | _ => empty) recvB_d
    fun _ _ => Hyp.Refuted.of_facts (by no_events)

theorem not_query₃₁ : ¬ query₃₁ :=
  Proc.not_satisfies_single tB_mem (fun v => match v with | .sid_a => sid | _ => empty) recvB_d
    fun _ _ => Hyp.Refuted.of_facts (by no_events)

theorem not_query₃₂ : ¬ query₃₂ :=
  Proc.not_satisfies_single tB_mem (fun v => match v with | .sid_a => sid | _ => empty) recvB_d
    fun _ _ => Hyp.Refuted.of_facts (by no_events)

theorem not_query₃₃ : ¬ query₃₃ := fun h => h (fun _ => sid) _ tA_mem knowsA_d

theorem not_query₃₄ : ¬ query₃₄ := fun h => h (fun _ => sid) _ tA_mem knowsA_d

theorem not_query₃₅ : ¬ query₃₅ :=
  Proc.not_satisfies_single tA_mem (fun _ => sid)
    ((Fact.holds_iff_holdsAt _ (.knows _)).1 knowsA_d) fun _ _ => Hyp.Refuted.of_facts (by no_events)

theorem not_query₃₆ : ¬ query₃₆ := fun h => h (fun _ => sid) _ tA_mem knowsA_d

/-! ### Termination -/

theorem not_query₃₇ : ¬ query₃₇ := fun h => h _ tB_mem (by simp [Fact.Holds, uB, restB])

end ProVerif.TraceSemantics.Examples.NoiseNN

end
