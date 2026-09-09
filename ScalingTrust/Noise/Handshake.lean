/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.Noise.State
import ScalingTrust.Noise.Patterns

/-!
# The `HandshakeState` object and the processing rules

This file transcribes spec §5.3: `Initialize`, `WriteMessage` and `ReadMessage`.

## Two modelling choices

* **Key generation is an input.**  Spec §5.3 says the `e` token "Sets `e` (which
  must be empty) to `GENERATE_KEYPAIR()`".  Rather than thread a source of
  randomness we make the freshly generated private key an explicit argument to
  `writeMessage`.  This keeps the model deterministic, which is what makes the
  correctness theorem in `ScalingTrust.Noise.Correctness` provable, and it
  matches spec §14 ("Ephemeral key reuse: … Ephemeral keys must never be
  reused") by making freshness a proof obligation on the caller.

* **Messages are sequences of fields, not bytes.**  Spec §3 notes that "all
  Noise messages can be processed without parsing, since there are no type or
  length fields": the message pattern alone determines how many public keys
  precede the payload and whether each is encrypted.  We therefore model a
  message as the list of its fields.  `writeMessage_length` records the fact
  that justifies this: the number of fields is a function of the message
  pattern.

Everything else follows §5.3 token by token.
-/

namespace Noise

variable {C : Crypto}

/-- A Noise message: a sequence of public-key fields followed by the payload
field (spec §3). -/
abbrev Message (C : Crypto) := List C.Bytes

/-- The number of fields in a message with the given pattern: one per
public-key token, plus the payload (spec §3). -/
def MessagePattern.fieldCount (m : MessagePattern) : Nat :=
  (m.filter Token.isKey).length + 1

/-- Spec §5.3: "A `HandshakeState` object contains a `SymmetricState` plus the
following variables, any of which may be empty … `s`, `e`, `rs`, `re` … A
`HandshakeState` also has variables to track its role, and the remaining portion
of the handshake pattern." -/
structure HandshakeState (C : Crypto) where
  /-- The embedded `SymmetricState`. -/
  sym : SymmetricState C
  /-- The local static key pair. -/
  s : Option C.Priv
  /-- The local ephemeral key pair. -/
  e : Option C.Priv
  /-- The remote party's static public key. -/
  rs : Option C.Bytes
  /-- The remote party's ephemeral public key. -/
  re : Option C.Bytes
  /-- The pre-shared symmetric key, if the pattern uses one (spec §9). -/
  psk : Option C.Bytes
  /-- This party's role.  Spec §5.3 calls this the `initiator` boolean. -/
  role : Role
  /-- Whether this is a PSK handshake, which changes the handling of `e` tokens
  (spec §9.2). -/
  isPsk : Bool
  /-- The remaining message patterns. -/
  messagePatterns : List MessagePattern

namespace HandshakeState

/-- The local private key of the given kind. -/
def ownPriv (hs : HandshakeState C) : KeyKind → Option C.Priv
  | .e => hs.e
  | .s => hs.s

/-- The remote public key of the given kind. -/
def remotePub (hs : HandshakeState C) : KeyKind → Option C.Bytes
  | .e => hs.re
  | .s => hs.rs

/-- Which of the two key kinds in a DH token is the local party's, and which is
the remote party's.

Spec §5.3: "For `"es"`: Calls `MixKey(DH(e, rs))` if initiator, `MixKey(DH(s, re))`
if responder."  Since `Token.dh a b` stores the initiator's kind first, the
initiator's own kind is `a` and the responder's own kind is `b`. -/
def dhKinds : Role → KeyKind → KeyKind → KeyKind × KeyKind
  | .initiator, a, b => (a, b)
  | .responder, a, b => (b, a)

/-- The Diffie–Hellman a party contributes to `MixKey`, given the kinds of its
own key and of the peer's key.

A missing key and a key that `DH` rejects are reported as different errors: the
first is a pattern or `Initialize` fault, the second is what an attacker
supplying a bad public key would provoke.  Both name the token's kinds in
initiator-then-responder order, recovered with `dhKinds`, which is an involution:
applying it to `own` and `remote` undoes the swap that produced them. -/
def dhInputOf (hs : HandshakeState C) (own remote : KeyKind) : Except NoiseError C.Bytes :=
  let (α, β) := dhKinds hs.role own remote
  match hs.ownPriv own, hs.remotePub remote with
  | some priv, some pk =>
      match C.dh priv pk with
      | some ikm => .ok ikm
      | none => .error (.invalidPublicKey α β)
  | _, _ => .error (.missingDHKey α β)

/-- The Diffie–Hellman for a `dh a b` token, from this party's point of view
(spec §5.3). -/
def dhInput (hs : HandshakeState C) (a b : KeyKind) : Except NoiseError C.Bytes :=
  hs.dhInputOf (dhKinds hs.role a b).1 (dhKinds hs.role a b).2

/-- Process a DH token: `MixKey(DH(own, remote))` (spec §5.3). -/
def mixDH (hs : HandshakeState C) (a b : KeyKind) : Except NoiseError (HandshakeState C) :=
  (hs.dhInput a b).map (fun ikm => { hs with sym := hs.sym.mixKey ikm })

/-- Mix an ephemeral public key into the state.

Spec §9.2: "In non-PSK handshakes, the `"e"` token in a pre-message pattern or
message pattern always results in a call to `MixHash(e.public_key)`.  In a PSK
handshake, all of these calls are followed by `MixKey(e.public_key)`." -/
def mixEphemeral (hs : HandshakeState C) (pk : C.Bytes) : SymmetricState C :=
  let sym := hs.sym.mixHash pk
  if hs.isPsk then sym.mixKey pk else sym

/-! ## `WriteMessage` (spec §5.3) -/

/-- Process one token while writing, returning the fields it appends to the
message buffer. -/
def writeToken (hs : HandshakeState C) (eph : C.Priv) :
    Token → Except NoiseError (HandshakeState C × List C.Bytes)
  | .key .e =>
      -- "Sets e (which must be empty) to GENERATE_KEYPAIR(). Appends
      -- e.public_key to the buffer. Calls MixHash(e.public_key)."
      let pk := C.pub eph
      .ok ({ hs with e := some eph, sym := hs.mixEphemeral pk }, [pk])
  | .key .s =>
      -- "Appends EncryptAndHash(s.public_key) to the buffer."
      match hs.s with
      | none => .error (.missingKey hs.role .s)
      | some sk =>
          match hs.sym.encryptAndHash (C.pub sk) with
          | .error err => .error err
          | .ok (sym, ct) => .ok ({ hs with sym }, [ct])
  | .dh a b =>
      match hs.mixDH a b with
      | .error err => .error err
      | .ok hs' => .ok (hs', [])
  | .psk =>
      -- Spec §9.2: "This token is processed by calling MixKeyAndHash(psk)."
      match hs.psk with
      | none => .error .missingPsk
      | some key => .ok ({ hs with sym := hs.sym.mixKeyAndHash key }, [])

/-- Process a message pattern's tokens while writing. -/
def writeTokens (eph : C.Priv) :
    HandshakeState C → List Token → Except NoiseError (HandshakeState C × List C.Bytes)
  | hs, [] => .ok (hs, [])
  | hs, t :: ts =>
      match hs.writeToken eph t with
      | .error err => .error err
      | .ok (hs', out) =>
          match writeTokens eph hs' ts with
          | .error err => .error err
          | .ok (hs'', out') => .ok (hs'', out ++ out')

/-- `WriteMessage(payload, message_buffer)` (spec §5.3).

`eph` is the key pair that `GENERATE_KEYPAIR()` would return; it is used only if
the message pattern contains an `e` token.  The third component of the result is
the pair of transport `CipherState`s returned by `Split()` when this was the
last handshake message. -/
def writeMessage (hs : HandshakeState C) (eph : C.Priv) (payload : C.Bytes) :
    Except NoiseError (HandshakeState C × Message C × Option (CipherState C × CipherState C)) :=
  match hs.messagePatterns with
  | [] => .error .patternExhausted
  | m :: ms =>
      match writeTokens eph hs m with
      | .error err => .error err
      | .ok (hs', fields) =>
          match hs'.sym.encryptAndHash payload with
          | .error err => .error err
          | .ok (sym, ct) =>
              .ok ({ hs' with sym, messagePatterns := ms }, fields ++ [ct],
                   if ms.isEmpty then some sym.split else none)

/-! ## `ReadMessage` (spec §5.3) -/

/-- Process one token while reading, consuming fields from the message. -/
def readToken (hs : HandshakeState C) :
    Token → Message C → Except NoiseError (HandshakeState C × Message C)
  | .key .e, fields =>
      -- "Sets re (which must be empty) to the next DHLEN bytes from the
      -- message. Calls MixHash(re.public_key)."
      match fields with
      | [] => .error .malformedMessage
      | pk :: rest => .ok ({ hs with re := some pk, sym := hs.mixEphemeral pk }, rest)
  | .key .s, fields =>
      -- "Sets temp to the next DHLEN + 16 bytes of the message if
      -- HasKey() == True, or to the next DHLEN bytes otherwise. Sets rs (which
      -- must be empty) to DecryptAndHash(temp)."
      match fields with
      | [] => .error .malformedMessage
      | ct :: rest =>
          match hs.sym.decryptAndHash ct with
          | .error err => .error err
          | .ok (sym, pk) => .ok ({ hs with rs := some pk, sym }, rest)
  | .dh a b, fields =>
      match hs.mixDH a b with
      | .error err => .error err
      | .ok hs' => .ok (hs', fields)
  | .psk, fields =>
      match hs.psk with
      | none => .error .missingPsk
      | some key => .ok ({ hs with sym := hs.sym.mixKeyAndHash key }, fields)

/-- Process a message pattern's tokens while reading. -/
def readTokens :
    HandshakeState C → List Token → Message C → Except NoiseError (HandshakeState C × Message C)
  | hs, [], fields => .ok (hs, fields)
  | hs, t :: ts, fields =>
      match hs.readToken t fields with
      | .error err => .error err
      | .ok (hs', rest) => readTokens hs' ts rest

/-- `ReadMessage(message, payload_buffer)` (spec §5.3). -/
def readMessage (hs : HandshakeState C) (msg : Message C) :
    Except NoiseError (HandshakeState C × C.Bytes × Option (CipherState C × CipherState C)) :=
  match hs.messagePatterns with
  | [] => .error .patternExhausted
  | m :: ms =>
      match readTokens hs m msg with
      | .error err => .error err
      | .ok (hs', rest) =>
          match rest with
          | [ct] =>
              match hs'.sym.decryptAndHash ct with
              | .error err => .error err
              | .ok (sym, p) =>
                  .ok ({ hs' with sym, messagePatterns := ms }, p,
                       if ms.isEmpty then some sym.split else none)
          | _ => .error .malformedMessage

/-! ## `Initialize` (spec §5.3) -/

/-- The public key referred to by a pre-message token, from this party's point
of view: its own key if the pre-message is its own, the stored remote key
otherwise. -/
def preMessageKey (hs : HandshakeState C) (owner : Role) (k : KeyKind) :
    Except NoiseError C.Bytes :=
  if owner = hs.role then
    match hs.ownPriv k with
    | some priv => .ok (C.pub priv)
    | none => .error (.missingKey owner k)
  else
    match hs.remotePub k with
    | some pk => .ok pk
    | none => .error (.missingKey owner k)

/-- Resolve the public keys listed in a pre-message pattern.

Resolution only reads `s`, `e`, `rs`, `re`, none of which `mixPreKeys` changes,
so resolving first and mixing afterwards is the same as interleaving. -/
def resolvePre (hs : HandshakeState C) (owner : Role) :
    PreMessagePattern → Except NoiseError (List (KeyKind × C.Bytes))
  | [] => .ok []
  | k :: ks =>
      match hs.preMessageKey owner k with
      | .error err => .error err
      | .ok pk =>
          match hs.resolvePre owner ks with
          | .error err => .error err
          | .ok rest => .ok ((k, pk) :: rest)

/-- Hash the resolved pre-message public keys into `h`, in the order listed
(spec §5.3), calling `MixKey` after each ephemeral in a PSK handshake
(spec §9.2). -/
def mixPreKeys (hs : HandshakeState C) : List (KeyKind × C.Bytes) → HandshakeState C
  | [] => hs
  | (k, pk) :: rest =>
      let sym := match k with
        | .e => hs.mixEphemeral pk
        | .s => hs.sym.mixHash pk
      ({ hs with sym }).mixPreKeys rest

/-- Hash one party's pre-message public keys into `h`, in the order listed. -/
def mixPreMessage (hs : HandshakeState C) (owner : Role) (ks : PreMessagePattern) :
    Except NoiseError (HandshakeState C) :=
  match hs.resolvePre owner ks with
  | .error err => .error err
  | .ok l => .ok (hs.mixPreKeys l)

/-! ### `mixPreKeys` touches nothing but the symmetric state -/

@[simp] theorem mixPreKeys_role (hs : HandshakeState C) (l : List (KeyKind × C.Bytes)) :
    (hs.mixPreKeys l).role = hs.role := by
  induction l generalizing hs with
  | nil => rfl
  | cons p l ih => obtain ⟨k, pk⟩ := p; cases k <;> simpa [mixPreKeys] using ih _

@[simp] theorem mixPreKeys_isPsk (hs : HandshakeState C) (l : List (KeyKind × C.Bytes)) :
    (hs.mixPreKeys l).isPsk = hs.isPsk := by
  induction l generalizing hs with
  | nil => rfl
  | cons p l ih => obtain ⟨k, pk⟩ := p; cases k <;> simpa [mixPreKeys] using ih _

@[simp] theorem mixPreKeys_s (hs : HandshakeState C) (l : List (KeyKind × C.Bytes)) :
    (hs.mixPreKeys l).s = hs.s := by
  induction l generalizing hs with
  | nil => rfl
  | cons p l ih => obtain ⟨k, pk⟩ := p; cases k <;> simpa [mixPreKeys] using ih _

@[simp] theorem mixPreKeys_e (hs : HandshakeState C) (l : List (KeyKind × C.Bytes)) :
    (hs.mixPreKeys l).e = hs.e := by
  induction l generalizing hs with
  | nil => rfl
  | cons p l ih => obtain ⟨k, pk⟩ := p; cases k <;> simpa [mixPreKeys] using ih _

@[simp] theorem mixPreKeys_rs (hs : HandshakeState C) (l : List (KeyKind × C.Bytes)) :
    (hs.mixPreKeys l).rs = hs.rs := by
  induction l generalizing hs with
  | nil => rfl
  | cons p l ih => obtain ⟨k, pk⟩ := p; cases k <;> simpa [mixPreKeys] using ih _

@[simp] theorem mixPreKeys_re (hs : HandshakeState C) (l : List (KeyKind × C.Bytes)) :
    (hs.mixPreKeys l).re = hs.re := by
  induction l generalizing hs with
  | nil => rfl
  | cons p l ih => obtain ⟨k, pk⟩ := p; cases k <;> simpa [mixPreKeys] using ih _

@[simp] theorem mixPreKeys_psk (hs : HandshakeState C) (l : List (KeyKind × C.Bytes)) :
    (hs.mixPreKeys l).psk = hs.psk := by
  induction l generalizing hs with
  | nil => rfl
  | cons p l ih => obtain ⟨k, pk⟩ := p; cases k <;> simpa [mixPreKeys] using ih _

@[simp] theorem mixPreKeys_messagePatterns (hs : HandshakeState C)
    (l : List (KeyKind × C.Bytes)) :
    (hs.mixPreKeys l).messagePatterns = hs.messagePatterns := by
  induction l generalizing hs with
  | nil => rfl
  | cons p l ih => obtain ⟨k, pk⟩ := p; cases k <;> simpa [mixPreKeys] using ih _

/-- The symmetric state after mixing pre-message keys depends only on the
symmetric state, the PSK flag, and the keys themselves. -/
theorem mixPreKeys_sym_congr (l : List (KeyKind × C.Bytes)) :
    ∀ {a b : HandshakeState C}, a.sym = b.sym → a.isPsk = b.isPsk →
      (a.mixPreKeys l).sym = (b.mixPreKeys l).sym := by
  induction l with
  | nil => intro a b hs _; exact hs
  | cons p l ih =>
      intro a b hs hp
      obtain ⟨k, pk⟩ := p
      cases k with
      | e =>
          refine ih ?_ (by simpa using hp)
          simpa [mixPreKeys] using (by unfold mixEphemeral; rw [hs, hp] :
            a.mixEphemeral pk = b.mixEphemeral pk)
      | s => exact ih (by simp [hs]) (by simpa using hp)

@[simp] theorem preMessageKey_mixPreKeys (hs : HandshakeState C)
    (l : List (KeyKind × C.Bytes)) (owner : Role) (k : KeyKind) :
    (hs.mixPreKeys l).preMessageKey owner k = hs.preMessageKey owner k := by
  unfold preMessageKey ownPriv remotePub
  cases k <;> simp

/-- If resolution succeeds then every key the pre-message mentions was
available. -/
theorem resolvePre_ok (owner : Role) (ks : PreMessagePattern) :
    ∀ {hs : HandshakeState C} {l : List (KeyKind × C.Bytes)},
      hs.resolvePre owner ks = .ok l → ∀ k ∈ ks, ∃ pk, hs.preMessageKey owner k = .ok pk := by
  induction ks with
  | nil => intro hs l _ k hk; exact absurd hk (by simp)
  | cons k' ks ih =>
      intro hs l hr k hk
      simp only [resolvePre] at hr
      cases hk' : hs.preMessageKey owner k' with
      | error err => simp [hk'] at hr
      | ok pk =>
          simp only [hk'] at hr
          cases hrest : hs.resolvePre owner ks with
          | error err => simp [hrest] at hr
          | ok rest =>
              rcases List.mem_cons.mp hk with rfl | hk
              · exact ⟨pk, hk'⟩
              · exact ih hrest k hk

/-- Resolution agrees between the two parties when they agree on every key the
pre-message mentions. -/
theorem resolvePre_congr (owner : Role) (ks : PreMessagePattern) :
    ∀ {a b : HandshakeState C},
      (∀ k ∈ ks, a.preMessageKey owner k = b.preMessageKey owner k) →
      a.resolvePre owner ks = b.resolvePre owner ks := by
  induction ks with
  | nil => intro a b _; rfl
  | cons k ks ih =>
      intro a b hk
      have h1 : a.preMessageKey owner k = b.preMessageKey owner k :=
        hk k (List.mem_cons_self ..)
      have h2 : a.resolvePre owner ks = b.resolvePre owner ks :=
        ih fun k' hk' => hk k' (List.mem_cons_of_mem _ hk')
      simp only [resolvePre, h1, h2]

end HandshakeState

/-- The `HandshakeState` immediately after `InitializeSymmetric` and
`MixHash(prologue)`, before the pre-message public keys are hashed in
(spec §5.3). -/
def initialHandshakeState (C : Crypto) (hp : HandshakePattern) (protocolName : String)
    (role : Role) (prologue : C.Bytes)
    (s e : Option C.Priv) (rs re : Option C.Bytes) (psk : Option C.Bytes) :
    HandshakeState C :=
  { sym := (SymmetricState.initializeSymmetric C protocolName).mixHash prologue,
    s, e, rs, re, psk, role, isPsk := hp.usesPsk, messagePatterns := hp.messages }

/-- `Initialize(handshake_pattern, initiator, prologue, s, e, rs, re)`
(spec §5.3).

`protocolName` is the full protocol name of spec §8; `psk` is the pre-shared key
of spec §9, required exactly when the pattern contains a `psk` token.

Spec §5.3: "If both initiator and responder have pre-messages, the initiator's
public keys are hashed first." -/
def initializeHandshake (C : Crypto) (hp : HandshakePattern) (protocolName : String)
    (role : Role) (prologue : C.Bytes)
    (s e : Option C.Priv) (rs re : Option C.Bytes) (psk : Option C.Bytes) :
    Except NoiseError (HandshakeState C) :=
  let hs := initialHandshakeState C hp protocolName role prologue s e rs re psk
  match hs.resolvePre .initiator hp.initiatorPre with
  | .error err => .error err
  | .ok l₁ =>
      match (hs.mixPreKeys l₁).resolvePre .responder hp.responderPre with
      | .error err => .error err
      | .ok l₂ => .ok ((hs.mixPreKeys l₁).mixPreKeys l₂)

end Noise
