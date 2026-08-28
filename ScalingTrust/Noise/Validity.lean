/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.Noise.Context

/-!
# Handshake pattern validity

Spec §7.3 lists four conditions a handshake pattern must satisfy:

> 1. Parties can only perform DH between private keys and public keys they
>    possess.
> 2. Parties must not send their static public key or ephemeral public key more
>    than once per handshake (i.e. including the pre-messages, there must be no
>    more than one occurrence of `"e"`, and one occurrence of `"s"`, in the
>    messages sent by any party).
> 3. Parties must not perform a DH calculation more than once per handshake
>    (i.e. there must be no more than one occurrence of `"ee"`, `"es"`, `"se"`,
>    or `"ss"` per handshake).
> 4. After performing a DH between a remote public key (either static or
>    ephemeral) and the local static key, the local party must not call
>    `ENCRYPT()` unless it has also performed a DH between its local ephemeral
>    key and the remote public key.  In particular, this means that (using
>    canonical notation):
>    * After an `"se"` token, the initiator must not send a handshake payload or
>      transport payload unless there has also been an `"ee"` token.
>    * After an `"ss"` token, the initiator must not send a handshake payload or
>      transport payload unless there has also been an `"es"` token.
>    * After an `"es"` token, the responder must not send a handshake payload or
>      transport payload unless there has also been an `"ee"` token.
>    * After an `"ss"` token, the responder must not send a handshake payload or
>      transport payload unless there has also been an `"se"` token.

and §9.3 adds a fifth for PSK patterns:

> A party may not send any encrypted data after it processes a `"psk"` token
> unless it has previously sent an ephemeral public key (an `"e"` token), either
> before or after the `"psk"` token.

## Two presentations

We give the rules twice.

* `Noise.stepToken`, `Noise.stepMessage`, `HandshakePattern.analyse` — an
  executable checker returning either a diagnostic `ValidityError` or the final
  context.  Everything about a concrete pattern is then decidable by evaluation.
* `Noise.TokenStep`, `Noise.MessageStep`, `Noise.PatternValid` — an inductive
  (declarative) presentation in the style of Figure 4 of the Noise Explorer
  paper.

`HandshakePattern.isValid_iff_patternValid` proves the two agree, so the
checker is both sound and complete for the declarative rules.

## Two deviations from the Noise Explorer paper's Figure 4

1. The paper checks rule 4 only at the *end* of a message (its `MsgEmpty`
   rules), i.e. only for the payload.  But a `"s"` token also calls `ENCRYPT()`
   when a key has been established (spec §5.3: `WriteMessage` appends
   `EncryptAndHash(s.public_key)`), so rule 4 applies there too.  Checking only
   at the end of a message is strictly weaker: it would accept
   `-> ss, s, es`, in which the static public key is encrypted under a key
   derived from `ss` alone.  We check at every `ENCRYPT()`.
2. The paper's `MsgPSK` rule requires `psk ∉ Γ`, forbidding a `psk` token from
   occurring twice.  The spec explicitly allows repetition (§9.2: "a `psk` token
   is allowed to appear one or more times in a handshake pattern", and §9.4
   names `XXpsk0+psk3` as a legitimate pattern).  We follow the spec, and expose
   the paper's stricter reading separately as
   `HandshakePattern.hasRepeatedPsk`.

We additionally check rule 4 for the *transport* payloads, which spec rule 4
mentions explicitly ("must not send a handshake payload or transport payload").
This is what rejects the `KXS` pattern discussed in §6 of the Noise Explorer
paper; see `ScalingTrust.Noise.PatternsValid`.
-/

namespace Noise

/-- Why a handshake pattern was rejected. -/
inductive ValidityError where
  /-- A pre-message pattern was not one of `[]`, `[e]`, `[s]`, `[e, s]`
  (spec §7.1). -/
  | malformedPreMessage (r : Role) : ValidityError
  /-- The pattern has no handshake messages. -/
  | noMessages : ValidityError
  /-- Spec §7.3 rule 2: a party sent the same public key twice. -/
  | resentKey (r : Role) (k : KeyKind) : ValidityError
  /-- Spec §7.3 rule 1: a DH was requested using a public key that had not been
  communicated.  `missing` is the party whose key was unavailable. -/
  | dhMissingKey (a b : KeyKind) (missing : Role) : ValidityError
  /-- Spec §7.3 rule 3: the same DH was performed twice. -/
  | repeatedDH (a b : KeyKind) : ValidityError
  /-- Spec §7.3 rule 4: `sender` encrypted after a DH between its own static key
  and a remote *ephemeral* key, without an `ee`. -/
  | encryptWithoutEE (sender : Role) : ValidityError
  /-- Spec §7.3 rule 4: `sender` encrypted after `ss`, without a DH between its
  own ephemeral key and the remote static key. -/
  | encryptAfterSS (sender : Role) : ValidityError
  /-- Spec §9.3: `sender` encrypted after a `psk` token without having sent its
  own ephemeral public key. -/
  | encryptAfterPskWithoutEphemeral (sender : Role) : ValidityError
  deriving DecidableEq, Repr

/-! ## Rule 4 and the PSK rule: when may a party call `ENCRYPT()`? -/

/-- Spec §7.3 rule 4 together with spec §9.3, as a boolean test: may `sender`
call `ENCRYPT()` in context `c`?

The three conjuncts are, in order:

* rule 4 for a DH between `sender`'s **static** key and the peer's **ephemeral**
  key (`se` for the initiator, `es` for the responder): it requires `ee`;
* rule 4 for `ss`: it requires the DH between `sender`'s **ephemeral** key and
  the peer's **static** key (`es` for the initiator, `se` for the responder);
* the PSK rule §9.3: a `psk` token requires `sender` to have sent its own `e`.

Note that when no key has been established at all (`Ctx.hasCipherKey c = false`)
no `ENCRYPT()` happens, and indeed all three conjuncts hold vacuously. -/
def canEncrypt (c : Ctx) (sender : Role) : Bool :=
  (!c.hasDHOf sender .s .e || c.ee) &&
  (!c.ss || c.hasDHOf sender .e .s) &&
  (!c.psk || c.hasKey sender .e)

/-- The proposition that `sender` may call `ENCRYPT()` in context `c`. -/
abbrev CanEncrypt (c : Ctx) (sender : Role) : Prop := canEncrypt c sender = true

instance (c : Ctx) (r : Role) : Decidable (CanEncrypt c r) := by
  unfold CanEncrypt; infer_instance

/-- If no cipher key has been established, `ENCRYPT()` is not called and the
rules are vacuous. -/
theorem canEncrypt_of_not_hasCipherKey {c : Ctx} (h : c.hasCipherKey = false)
    (r : Role) : CanEncrypt c r := by
  simp only [Ctx.hasCipherKey, Bool.or_eq_false_iff] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  cases r <;>
    simp [CanEncrypt, canEncrypt, Ctx.hasDHOf, Ctx.has, Ctx.hasDH, h1, h2, h3, h4, h5]

/-- The diagnostic form of `canEncrypt`. -/
def checkEncrypt (c : Ctx) (sender : Role) : Except ValidityError Unit :=
  if c.hasDHOf sender .s .e && !c.ee then .error (.encryptWithoutEE sender)
  else if c.ss && !c.hasDHOf sender .e .s then .error (.encryptAfterSS sender)
  else if c.psk && !c.hasKey sender .e then
    .error (.encryptAfterPskWithoutEphemeral sender)
  else .ok ()

theorem checkEncrypt_eq_ok_iff (c : Ctx) (r : Role) :
    checkEncrypt c r = .ok () ↔ CanEncrypt c r := by
  simp only [checkEncrypt, CanEncrypt, canEncrypt]
  cases hse : c.hasDHOf r .s .e <;> cases hee : c.ee <;> cases hss : c.ss <;>
    cases hes : c.hasDHOf r .e .s <;> cases hpsk : c.psk <;>
    cases he : c.hasKey r .e <;> simp

/-! ### Why rule 4 is there

Spec §7.3 explains the fourth check:

> First, it is necessary because Noise relies on DH outputs involving ephemeral
> keys to randomize the shared secret keys.  Patterns failing this check could
> result in catastrophic key reuse, because the victim might send a message
> encrypted with a key that doesn't include a contribution from their local
> ephemeral key.

`canEncrypt_ephemeralRandomised` turns that sentence into a theorem: whenever a
party is permitted to encrypt and a key has actually been established, the key
material mixed in so far includes a Diffie-Hellman output — or, in PSK mode, a
`MixKey` (spec §9.2) — involving that party's *own* ephemeral key.
-/

/-- The encryption key in use by `r` has been randomised by `r`'s own ephemeral
key: either through an `ee`, or through the DH between `r`'s ephemeral key and
the peer's static key, or (in PSK mode) through the `MixKey(e.public_key)` that
spec §9.2 performs on `r`'s own ephemeral public key. -/
def EphemeralRandomised (c : Ctx) (r : Role) : Prop :=
  c.ee = true ∨ c.hasDHOf r .e .s = true ∨ (c.psk = true ∧ c.hasKey r .e = true)

/-- **Rule 4 does what the specification says it does.**

If a party may encrypt and a cipher key has been established, then that key
depends on the party's own ephemeral key.  Consequently no party ever encrypts
under a key it did not contribute freshness to — which is exactly the
"catastrophic key reuse" that spec §7.3 rule 4 exists to prevent. -/
theorem canEncrypt_ephemeralRandomised {c : Ctx} {r : Role}
    (h : CanEncrypt c r) (hk : c.hasCipherKey = true) : EphemeralRandomised c r := by
  obtain ⟨initE, initS, respE, respS, ee, es, se, ss, psk⟩ := c
  cases r <;>
    simp only [CanEncrypt, canEncrypt, EphemeralRandomised, Ctx.hasCipherKey,
      Ctx.hasDHOf, Ctx.has, Ctx.hasDH, Ctx.hasKey, Token.dhOf] at h hk ⊢ <;>
    revert h hk <;>
    cases ee <;> cases es <;> cases se <;> cases ss <;> cases psk <;>
      cases initE <;> cases respE <;> simp

/-! ## The executable checker -/

/-- Process one token of a message sent by `sender`, checking spec §7.3 rules
1–4 and §9.3. -/
def stepToken (r : Role) (c : Ctx) : Token → Except ValidityError Ctx
  | .key .e =>
      if c.hasKey r .e then .error (.resentKey r .e)
      else .ok (c.setKey r .e)
  | .key .s =>
      if c.hasKey r .s then .error (.resentKey r .s)
      else match checkEncrypt c r with
        -- spec §5.3: `WriteMessage` appends `EncryptAndHash(s.public_key)`
        | .error e => .error e
        | .ok () => .ok (c.setKey r .s)
  | .dh a b =>
      if !c.hasKey .initiator a then .error (.dhMissingKey a b .initiator)
      else if !c.hasKey .responder b then .error (.dhMissingKey a b .responder)
      else if c.hasDH a b then .error (.repeatedDH a b)
      else .ok (c.setDH a b)
  | .psk => .ok c.setPsk

/-- Process a whole message pattern's tokens, left to right. -/
def stepTokens (r : Role) : Ctx → List Token → Except ValidityError Ctx
  | c, [] => .ok c
  | c, t :: ts =>
      match stepToken r c t with
      | .error e => .error e
      | .ok c' => stepTokens r c' ts

/-- Process a message pattern: its tokens, then the implicit payload, which is
encrypted if a key has been established. -/
def stepMessage (r : Role) (c : Ctx) (m : MessagePattern) : Except ValidityError Ctx :=
  match stepTokens r c m with
  | .error e => .error e
  | .ok c' => match checkEncrypt c' r with
    | .error e => .error e
    | .ok () => .ok c'

/-- Process the handshake messages, alternating direction, starting with `r`. -/
def stepMessages (r : Role) : Ctx → List MessagePattern → Except ValidityError Ctx
  | c, [] => .ok c
  | c, m :: ms =>
      match stepMessage r c m with
      | .error e => .error e
      | .ok c' => stepMessages r.other c' ms

/-- Process a pre-message pattern: the keys it lists become known.  No
encryption happens during `Initialize` (spec §5.3), so rule 4 is not checked
here; only rule 2. -/
def stepPre (r : Role) : Ctx → PreMessagePattern → Except ValidityError Ctx
  | c, [] => .ok c
  | c, k :: ks =>
      if c.hasKey r k then .error (.resentKey r k)
      else stepPre r (c.setKey r k) ks

/-- Rule 4 applied to the transport payloads of every party that may send them
(spec §7.3 rule 4: "must not send a handshake payload **or transport
payload**"). -/
def checkTransport (c : Ctx) : List Role → Except ValidityError Unit
  | [] => .ok ()
  | r :: rs =>
      match checkEncrypt c r with
      | .error e => .error e
      | .ok () => checkTransport c rs

namespace HandshakePattern

/-- Run the validity checker, returning the context reached at the end of the
handshake, or the first violation found. -/
def analyse (hp : HandshakePattern) : Except ValidityError Ctx :=
  if hp.initiatorPre.isWellFormed then
    if hp.responderPre.isWellFormed then
      if hp.messages.isEmpty then .error .noMessages
      else match stepPre .initiator Ctx.empty hp.initiatorPre with
        | .error e => .error e
        | .ok c₀ => match stepPre .responder c₀ hp.responderPre with
          | .error e => .error e
          | .ok c₁ => match stepMessages .initiator c₁ hp.messages with
            | .error e => .error e
            | .ok cf => match checkTransport cf hp.transportSenders with
              | .error e => .error e
              | .ok () => .ok cf
    else .error (.malformedPreMessage .responder)
  else .error (.malformedPreMessage .initiator)

/-- Is this a valid handshake pattern (spec §7.3, §9.3)? -/
def isValid (hp : HandshakePattern) : Bool :=
  match hp.analyse with
  | .ok _ => true
  | .error _ => false

/-- The final context of a valid pattern. -/
def finalCtx (hp : HandshakePattern) : Ctx :=
  match hp.analyse with
  | .ok c => c
  | .error _ => Ctx.empty

/-- The Noise Explorer paper's `MsgPSK` rule additionally forbids a `psk` token
from occurring more than once.  The spec allows it (§9.2, §9.4), so this is
tracked separately. -/
def hasRepeatedPsk (hp : HandshakePattern) : Bool :=
  decide (2 ≤ (hp.tokens.filter (· = Token.psk)).length)

/-- The Noise Explorer paper's additional soft rule: "Noise Handshake Patterns
should not contain key shares that are not subsequently used in any
Diffie-Hellman operation." -/
def usesAllKeys (hp : HandshakePattern) : Bool :=
  let c := hp.finalCtx
  (!c.hasKey .initiator .e || c.ee || c.es) &&
  (!c.hasKey .initiator .s || c.se || c.ss) &&
  (!c.hasKey .responder .e || c.ee || c.se) &&
  (!c.hasKey .responder .s || c.es || c.ss)

end HandshakePattern

/-! ## The declarative presentation

These inductive relations are the Noise Explorer paper's Figure 4, adjusted as
described in the module docstring. -/

/-- One token of a message sent by `r` takes context `c` to context `c'`. -/
inductive TokenStep : Role → Ctx → Token → Ctx → Prop where
  /-- Sending a fresh ephemeral public key.  Rule 2: it must not have been sent
  before.  No encryption occurs (spec §5.3: `MixHash(e.public_key)`). -/
  | ephemeral {r c} :
      c.hasKey r .e = false →
      TokenStep r c Token.e (c.setKey r .e)
  /-- Sending the static public key.  Rule 2 plus rule 4, because
  `EncryptAndHash(s.public_key)` calls `ENCRYPT()` when a key is established. -/
  | static {r c} :
      c.hasKey r .s = false →
      CanEncrypt c r →
      TokenStep r c Token.s (c.setKey r .s)
  /-- Performing a DH.  Rule 1: both public keys must be available.  Rule 3: not
  performed before. -/
  | dh {r c a b} :
      c.hasKey .initiator a = true →
      c.hasKey .responder b = true →
      c.hasDH a b = false →
      TokenStep r c (.dh a b) (c.setDH a b)
  /-- Mixing in the pre-shared key (spec §9.2).  Always permitted; the
  restriction is on subsequent encryption (§9.3). -/
  | psk {r c} :
      TokenStep r c Token.psk c.setPsk

/-- A list of tokens, processed left to right. -/
inductive TokensStep : Role → Ctx → List Token → Ctx → Prop where
  | nil {r c} : TokensStep r c [] c
  | cons {r c t ts c' c''} :
      TokenStep r c t c' → TokensStep r c' ts c'' → TokensStep r c (t :: ts) c''

/-- A message pattern: its tokens, followed by the payload, whose encryption is
subject to rule 4. -/
inductive MessageStep : Role → Ctx → MessagePattern → Ctx → Prop where
  | mk {r c m c'} : TokensStep r c m c' → CanEncrypt c' r → MessageStep r c m c'

/-- The handshake messages, alternating direction. -/
inductive MessagesStep : Role → Ctx → List MessagePattern → Ctx → Prop where
  | nil {r c} : MessagesStep r c [] c
  | cons {r c m ms c' c''} :
      MessageStep r c m c' → MessagesStep r.other c' ms c'' →
      MessagesStep r c (m :: ms) c''

/-- A pre-message pattern. -/
inductive PreStep : Role → Ctx → PreMessagePattern → Ctx → Prop where
  | nil {r c} : PreStep r c [] c
  | cons {r c k ks c'} :
      c.hasKey r k = false → PreStep r (c.setKey r k) ks c' → PreStep r c (k :: ks) c'

/-- A handshake pattern is valid (spec §7.3, §9.3) when its pre-messages are
well formed, it has at least one message, its messages step through the
validity relation, and every party that may send transport messages is allowed
to encrypt them. -/
def PatternValid (hp : HandshakePattern) : Prop :=
  hp.initiatorPre.isWellFormed = true ∧
  hp.responderPre.isWellFormed = true ∧
  hp.messages ≠ [] ∧
  ∃ c₀ c₁ cf,
    PreStep .initiator Ctx.empty hp.initiatorPre c₀ ∧
    PreStep .responder c₀ hp.responderPre c₁ ∧
    MessagesStep .initiator c₁ hp.messages cf ∧
    ∀ r ∈ hp.transportSenders, CanEncrypt cf r

/-! ## Soundness and completeness of the checker -/

theorem stepToken_eq_ok_iff (r : Role) (c : Ctx) (t : Token) (c' : Ctx) :
    stepToken r c t = .ok c' ↔ TokenStep r c t c' := by
  constructor
  · intro h
    match t with
    | .key .e =>
        simp only [stepToken] at h
        split at h
        · exact absurd h (by simp)
        · rename_i hk
          have : c' = c.setKey r .e := by
            simpa using h.symm
          subst this
          exact .ephemeral (by simpa using hk)
    | .key .s =>
        simp only [stepToken] at h
        split at h
        · exact absurd h (by simp)
        · rename_i hk
          split at h
          · exact absurd h (by simp)
          · rename_i hce
            have : c' = c.setKey r .s := by simpa using h.symm
            subst this
            exact .static (by simpa using hk)
              ((checkEncrypt_eq_ok_iff c r).mp (by rw [hce]))
    | .dh a b =>
        simp only [stepToken] at h
        split at h
        · exact absurd h (by simp)
        · rename_i h1
          split at h
          · exact absurd h (by simp)
          · rename_i h2
            split at h
            · exact absurd h (by simp)
            · rename_i h3
              have : c' = c.setDH a b := by simpa using h.symm
              subst this
              exact .dh (by simpa using h1) (by simpa using h2) (by simpa using h3)
    | .psk =>
        simp only [stepToken] at h
        have : c' = c.setPsk := by simpa using h.symm
        subst this
        exact .psk
  · intro h
    cases h with
    | ephemeral hk => simp [stepToken, hk]
    | static hk hce =>
        have := (checkEncrypt_eq_ok_iff c r).mpr hce
        simp [stepToken, hk, this]
    | dh h1 h2 h3 => simp [stepToken, h1, h2, h3]
    | psk => simp [stepToken]

theorem stepTokens_eq_ok_iff (r : Role) (ts : List Token) (c c' : Ctx) :
    stepTokens r c ts = .ok c' ↔ TokensStep r c ts c' := by
  induction ts generalizing c with
  | nil =>
      constructor
      · intro h; have : c = c' := by simpa [stepTokens] using h
        subst this; exact .nil
      · intro h; cases h; rfl
  | cons t ts ih =>
      constructor
      · intro h
        simp only [stepTokens] at h
        split at h
        · exact absurd h (by simp)
        · rename_i c'' hst
          exact .cons ((stepToken_eq_ok_iff r c t c'').mp hst) ((ih c'').mp h)
      · intro h
        cases h with
        | cons hst hrest =>
            rename_i c''
            simp only [stepTokens, (stepToken_eq_ok_iff r c t c'').mpr hst]
            exact (ih c'').mpr hrest

theorem stepMessage_eq_ok_iff (r : Role) (c : Ctx) (m : MessagePattern) (c' : Ctx) :
    stepMessage r c m = .ok c' ↔ MessageStep r c m c' := by
  constructor
  · intro h
    simp only [stepMessage] at h
    split at h
    · exact absurd h (by simp)
    · rename_i c'' hts
      split at h
      · exact absurd h (by simp)
      · rename_i hce
        have : c'' = c' := by simpa using h
        subst this
        exact .mk ((stepTokens_eq_ok_iff r m c c'').mp hts)
          ((checkEncrypt_eq_ok_iff c'' r).mp (by rw [hce]))
  · intro h
    cases h with
    | mk hts hce =>
        simp only [stepMessage, (stepTokens_eq_ok_iff r m c c').mpr hts,
          (checkEncrypt_eq_ok_iff c' r).mpr hce]

theorem stepMessages_eq_ok_iff (r : Role) (ms : List MessagePattern) (c c' : Ctx) :
    stepMessages r c ms = .ok c' ↔ MessagesStep r c ms c' := by
  induction ms generalizing r c with
  | nil =>
      constructor
      · intro h; have : c = c' := by simpa [stepMessages] using h
        subst this; exact .nil
      · intro h; cases h; rfl
  | cons m ms ih =>
      constructor
      · intro h
        simp only [stepMessages] at h
        split at h
        · exact absurd h (by simp)
        · rename_i c'' hst
          exact .cons ((stepMessage_eq_ok_iff r c m c'').mp hst) ((ih r.other c'').mp h)
      · intro h
        cases h with
        | cons hst hrest =>
            rename_i c''
            simp only [stepMessages, (stepMessage_eq_ok_iff r c m c'').mpr hst]
            exact (ih r.other c'').mpr hrest

theorem stepPre_eq_ok_iff (r : Role) (ks : PreMessagePattern) (c c' : Ctx) :
    stepPre r c ks = .ok c' ↔ PreStep r c ks c' := by
  induction ks generalizing c with
  | nil =>
      constructor
      · intro h; have : c = c' := by simpa [stepPre] using h
        subst this; exact .nil
      · intro h; cases h; rfl
  | cons k ks ih =>
      constructor
      · intro h
        simp only [stepPre] at h
        split at h
        · exact absurd h (by simp)
        · rename_i hk
          exact .cons (by simpa using hk) ((ih (c.setKey r k)).mp h)
      · intro h
        cases h with
        | cons hk hrest =>
            simp only [stepPre, hk, if_false, Bool.false_eq_true]
            exact (ih (c.setKey r k)).mpr hrest

theorem checkTransport_eq_ok_iff (c : Ctx) (rs : List Role) :
    checkTransport c rs = .ok () ↔ ∀ r ∈ rs, CanEncrypt c r := by
  induction rs with
  | nil => simp [checkTransport]
  | cons r rs ih =>
      constructor
      · intro h
        simp only [checkTransport] at h
        split at h
        · exact absurd h (by simp)
        · rename_i hce
          intro r' hr'
          rcases List.mem_cons.mp hr' with rfl | hr'
          · exact (checkEncrypt_eq_ok_iff c r').mp (by rw [hce])
          · exact ih.mp h r' hr'
      · intro h
        simp only [checkTransport,
          (checkEncrypt_eq_ok_iff c r).mpr (h r (List.mem_cons_self ..))]
        exact ih.mpr fun r' hr' => h r' (List.mem_cons_of_mem _ hr')

namespace HandshakePattern

theorem isValid_iff_analyse_ok (hp : HandshakePattern) :
    hp.isValid = true ↔ ∃ c, hp.analyse = .ok c := by
  unfold isValid
  cases h : hp.analyse with
  | ok c => simp
  | error e => simp

/-- The analysis succeeds exactly on the patterns admitted by the declarative
rules, and then returns the context reached at the end of the handshake. -/
theorem analyse_eq_ok_iff (hp : HandshakePattern) :
    (∃ c, hp.analyse = .ok c) ↔ PatternValid hp := by
  constructor
  · rintro ⟨c, hc⟩
    rw [analyse] at hc
    split at hc
    · rename_i h1
      split at hc
      · rename_i h2
        split at hc
        · exact absurd hc (by simp)
        · rename_i h3
          split at hc
          · exact absurd hc (by simp)
          rename_i c₀ hs0
          split at hc
          · exact absurd hc (by simp)
          rename_i c₁ hs1
          split at hc
          · exact absurd hc (by simp)
          rename_i cf hsm
          split at hc
          · exact absurd hc (by simp)
          rename_i ht
          exact ⟨h1, h2, by simpa using h3, c₀, c₁, cf,
            (stepPre_eq_ok_iff _ _ _ _).mp hs0,
            (stepPre_eq_ok_iff _ _ _ _).mp hs1,
            (stepMessages_eq_ok_iff _ _ _ _).mp hsm,
            (checkTransport_eq_ok_iff _ _).mp (by rw [ht])⟩
      · exact absurd hc (by simp)
    · exact absurd hc (by simp)
  · rintro ⟨h1, h2, h3, c₀, c₁, cf, p0, p1, pm, pt⟩
    refine ⟨cf, ?_⟩
    rw [analyse, if_pos h1, if_pos h2, if_neg (by simpa using h3)]
    simp only [(stepPre_eq_ok_iff _ _ _ _).mpr p0, (stepPre_eq_ok_iff _ _ _ _).mpr p1,
      (stepMessages_eq_ok_iff _ _ _ _).mpr pm, (checkTransport_eq_ok_iff _ _).mpr pt]

/-- **The checker is sound and complete**: the executable validity checker
accepts exactly the patterns admitted by the declarative rules of spec §7.3
and §9.3. -/
theorem isValid_iff_patternValid (hp : HandshakePattern) :
    hp.isValid = true ↔ PatternValid hp :=
  (isValid_iff_analyse_ok hp).trans (analyse_eq_ok_iff hp)

instance (hp : HandshakePattern) : Decidable (PatternValid hp) :=
  decidable_of_iff _ (isValid_iff_patternValid hp)

end HandshakePattern

/-! ## Applying tokens to a context

The validity checker refuses invalid steps; `applyToken` performs the same update
unconditionally, which is convenient when analysing patterns already known to be
valid.
-/


/-- Apply a token to a context, without checking validity. -/
def applyToken (r : Role) (c : Ctx) : Token → Ctx
  | .key k => c.setKey r k
  | .dh a b => c.setDH a b
  | .psk => c.setPsk

/-- On a valid step, the validity checker and `applyToken` agree. -/
theorem stepToken_eq_applyToken {r : Role} {c : Ctx} {t : Token} {c' : Ctx}
    (h : stepToken r c t = .ok c') : c' = applyToken r c t := by
  match t with
  | .key .e =>
      simp only [stepToken] at h; split at h
      · exact absurd h (by simp)
      · simpa [applyToken] using h.symm
  | .key .s =>
      simp only [stepToken] at h; split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · simpa [applyToken] using h.symm
  | .dh a b =>
      simp only [stepToken] at h
      split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · simpa [applyToken] using h.symm
  | .psk =>
      simp only [stepToken] at h
      simpa [applyToken] using h.symm

/-- Apply a whole message pattern's tokens. -/
def applyTokens (r : Role) (c : Ctx) (m : MessagePattern) : Ctx :=
  m.foldl (applyToken r) c

theorem stepTokens_eq_applyTokens {r : Role} {m : MessagePattern} {c c' : Ctx}
    (h : stepTokens r c m = .ok c') : c' = applyTokens r c m := by
  induction m generalizing c with
  | nil =>
      simp only [stepTokens] at h
      simpa [applyTokens] using h.symm
  | cons t ts ih =>
      simp only [stepTokens] at h
      split at h
      · exact absurd h (by simp)
      · rename_i c'' hst
        rw [stepToken_eq_applyToken hst] at *
        simpa [applyTokens, List.foldl_cons] using ih h

/-! ## The context established by the pre-messages -/

/-- The context reached after `Initialize` has processed both pre-messages
(spec §5.3).  The initiator's keys are recorded first, as the specification
requires. -/
def preCtx (hp : HandshakePattern) : Ctx :=
  hp.responderPre.foldl (fun c k => c.setKey .responder k)
    (hp.initiatorPre.foldl (fun c k => c.setKey .initiator k) Ctx.empty)

theorem preStep_eq (r : Role) (ks : PreMessagePattern) :
    ∀ {c c' : Ctx}, PreStep r c ks c' → c' = ks.foldl (fun c k => c.setKey r k) c := by
  induction ks with
  | nil => intro c c' h; cases h; rfl
  | cons k ks ih =>
      intro c c' h
      cases h with
      | cons _ hrest => simpa using ih hrest

/-- A valid pattern's messages step from the pre-message context. -/
theorem PatternValid.messagesStep {hp : HandshakePattern} (h : PatternValid hp) :
    ∃ cf, MessagesStep .initiator (preCtx hp) hp.messages cf := by
  obtain ⟨-, -, -, c₀, c₁, cf, h0, h1, hm, -⟩ := h
  refine ⟨cf, ?_⟩
  rw [preCtx, ← preStep_eq .initiator _ h0, ← preStep_eq .responder _ h1]
  exact hm

/-! ### What the pre-message context records -/

theorem hasKey_foldl_setKey_same (r : Role) : ∀ (ks : List KeyKind) (c : Ctx) (k : KeyKind),
    (ks.foldl (fun c k => c.setKey r k) c).hasKey r k = true → k ∈ ks ∨ c.hasKey r k = true := by
  intro ks
  induction ks with
  | nil => intro c k h; exact Or.inr h
  | cons k' ks ih =>
      intro c k h
      rcases ih (c.setKey r k') k (by simpa using h) with h' | h'
      · exact Or.inl (List.mem_cons_of_mem _ h')
      · cases k' <;> cases k
        · exact Or.inl (List.mem_cons_self ..)
        · exact Or.inr (by rwa [Ctx.hasKey_setKey_e_s] at h')
        · exact Or.inr (by rwa [Ctx.hasKey_setKey_s_e] at h')
        · exact Or.inl (List.mem_cons_self ..)

theorem hasKey_foldl_setKey_other (r : Role) : ∀ (ks : List KeyKind) (c : Ctx) (k : KeyKind),
    (ks.foldl (fun c k => c.setKey r k) c).hasKey r.other k = c.hasKey r.other k := by
  intro ks
  induction ks with
  | nil => intro c k; rfl
  | cons k' ks ih =>
      intro c k
      rw [List.foldl_cons, ih, Ctx.hasKey_setKey_other_role]

/-- Only keys listed in the initiator's pre-message are recorded for the
initiator. -/
theorem mem_initiatorPre_of_preCtx {hp : HandshakePattern} {k : KeyKind}
    (h : (preCtx hp).hasKey .initiator k = true) : k ∈ hp.initiatorPre := by
  rw [preCtx] at h
  rw [show (Role.initiator : Role) = Role.responder.other from rfl] at h
  rw [hasKey_foldl_setKey_other] at h
  rcases hasKey_foldl_setKey_same .initiator hp.initiatorPre Ctx.empty k h with h' | h'
  · exact h'
  · cases k <;> exact absurd h' (by decide)

/-- Only keys listed in the responder's pre-message are recorded for the
responder. -/
theorem mem_responderPre_of_preCtx {hp : HandshakePattern} {k : KeyKind}
    (h : (preCtx hp).hasKey .responder k = true) : k ∈ hp.responderPre := by
  rw [preCtx] at h
  rcases hasKey_foldl_setKey_same .responder hp.responderPre _ k h with h' | h'
  · exact h'
  · rw [show (Role.responder : Role) = Role.initiator.other from rfl,
      hasKey_foldl_setKey_other] at h'
    cases k <;> exact absurd h' (by decide)

end Noise
