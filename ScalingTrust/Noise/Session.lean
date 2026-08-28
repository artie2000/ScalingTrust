/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.Noise.Correctness

/-!
# Sessions: `Initialize` establishes the matching invariant

`ScalingTrust.Noise.Correctness` proves that a handshake between two *matched*
parties runs correctly.  This file closes the loop by showing that `Initialize`
produces matched parties, and assembles the end-to-end statement.

A `Session.Setup` records everything two parties need to agree on before a
handshake: the pattern, the protocol name, the prologue, the optional
pre-shared key, and the four possible key pairs.  Each party is initialised from
the same setup, holding its own private keys and — following spec §5.3, "Public
keys are only passed in if the handshake_pattern uses pre-messages" — exactly
the peer public keys that the pre-messages announce.
-/

namespace Noise

variable {C : Crypto}

/-- Everything the two parties of a handshake agree on beforehand. -/
structure Setup (C : Crypto) where
  /-- The handshake pattern to execute. -/
  pattern : HandshakePattern
  /-- The full protocol name (spec §8). -/
  protocolName : String
  /-- The prologue (spec §6). -/
  prologue : C.Bytes
  /-- The pre-shared key, for PSK patterns (spec §9). -/
  psk : Option C.Bytes := none
  /-- The initiator's static key pair. -/
  initiatorStatic : Option C.Priv := none
  /-- The initiator's ephemeral key pair, if the pattern pre-shares one. -/
  initiatorEphemeral : Option C.Priv := none
  /-- The responder's static key pair. -/
  responderStatic : Option C.Priv := none
  /-- The responder's ephemeral key pair, if the pattern pre-shares one. -/
  responderEphemeral : Option C.Priv := none

namespace Setup

/-- The private key of the given kind belonging to the given party. -/
def priv (st : Setup C) : Role → KeyKind → Option C.Priv
  | .initiator, .e => st.initiatorEphemeral
  | .initiator, .s => st.initiatorStatic
  | .responder, .e => st.responderEphemeral
  | .responder, .s => st.responderStatic

/-- The pre-message pattern announcing the given party's public keys. -/
def pre (st : Setup C) : Role → PreMessagePattern
  | .initiator => st.pattern.initiatorPre
  | .responder => st.pattern.responderPre

/-- The public keys of `owner` that its peer is given at `Initialize`: exactly
those the pre-messages announce (spec §5.3). -/
def remotePub (st : Setup C) (owner : Role) (k : KeyKind) : Option C.Bytes :=
  if k ∈ st.pre owner then (st.priv owner k).map C.pub else none

/-- The starting `HandshakeState` of the given party. -/
def state (st : Setup C) (r : Role) : Except NoiseError (HandshakeState C) :=
  initializeHandshake C st.pattern st.protocolName r st.prologue
    (st.priv r .s) (st.priv r .e)
    (st.remotePub r.other .s) (st.remotePub r.other .e) st.psk

/-- The state each party starts from before the pre-messages are hashed in. -/
def base (st : Setup C) (r : Role) : HandshakeState C :=
  initialHandshakeState C st.pattern st.protocolName r st.prologue
    (st.priv r .s) (st.priv r .e) (st.remotePub r.other .s) (st.remotePub r.other .e) st.psk

theorem state_eq (st : Setup C) (r : Role) :
    st.state r =
      match (st.base r).resolvePre .initiator st.pattern.initiatorPre with
      | .error e => .error e
      | .ok l₁ =>
          match ((st.base r).mixPreKeys l₁).resolvePre .responder st.pattern.responderPre with
          | .error e => .error e
          | .ok l₂ => .ok (((st.base r).mixPreKeys l₁).mixPreKeys l₂) := rfl

/-- Both parties compute the same value for a pre-message key: its owner
derives it from its own private key, and its peer was handed it at
`Initialize`. -/
theorem preMessageKey_eq (st : Setup C) (owner : Role) (k : KeyKind)
    (hk : k ∈ st.pre owner) (r : Role) :
    (st.base r).preMessageKey owner k =
      (match st.priv owner k with
       | some p => .ok (C.pub p)
       | none => .error (.missingKey owner k)) := by
  cases hp : st.priv owner k with
  | none =>
      cases owner <;> cases r <;> cases k <;>
        simp_all [HandshakeState.preMessageKey, base, initialHandshakeState,
          HandshakeState.ownPriv, HandshakeState.remotePub, remotePub, Role.other, pre]
  | some p =>
      cases owner <;> cases r <;> cases k <;>
        simp_all [HandshakeState.preMessageKey, base, initialHandshakeState,
          HandshakeState.ownPriv, HandshakeState.remotePub, remotePub, Role.other, pre]

/-- The two parties resolve every pre-message key to the same value. -/
theorem preMessageKey_agree (st : Setup C) (owner : Role) (k : KeyKind)
    (hk : k ∈ st.pre owner) :
    (st.base .initiator).preMessageKey owner k = (st.base .responder).preMessageKey owner k := by
  rw [st.preMessageKey_eq owner k hk, st.preMessageKey_eq owner k hk]

end Setup

/-! ## `Initialize` establishes `Matched` -/

/-- **`Initialize` produces matched states.**

Two parties initialised from the same `Setup` — each with its own private keys
and with exactly the peer public keys the pre-messages announce — are matched at
the pre-message context.  In particular they start with the same `ck` and `h`,
as spec §5.3 intends. -/
theorem initialize_matched (st : Setup C) {a b : HandshakeState C}
    (ha : st.state .initiator = .ok a) (hb : st.state .responder = .ok b) :
    Matched (preCtx st.pattern) .initiator a b := by
  -- Both parties resolve the same pre-message key lists.
  rw [Setup.state_eq] at ha hb
  cases h1a : (st.base .initiator).resolvePre .initiator st.pattern.initiatorPre with
  | error e => simp [h1a] at ha
  | ok l₁ =>
  have h1congr : (st.base .responder).resolvePre .initiator st.pattern.initiatorPre
      = (st.base .initiator).resolvePre .initiator st.pattern.initiatorPre :=
    HandshakeState.resolvePre_congr .initiator st.pattern.initiatorPre
      (fun k hk => (st.preMessageKey_agree .initiator k hk).symm)
  have h1b : (st.base .responder).resolvePre .initiator st.pattern.initiatorPre = .ok l₁ := by
    rw [h1congr]; exact h1a
  simp only [h1a] at ha
  simp only [h1b] at hb
  cases h2a : ((st.base .initiator).mixPreKeys l₁).resolvePre .responder
      st.pattern.responderPre with
  | error e => simp [h2a] at ha
  | ok l₂ =>
  have h2congr : ((st.base .responder).mixPreKeys l₁).resolvePre .responder
        st.pattern.responderPre
      = ((st.base .initiator).mixPreKeys l₁).resolvePre .responder st.pattern.responderPre :=
    HandshakeState.resolvePre_congr .responder st.pattern.responderPre (fun k hk => by
      rw [HandshakeState.preMessageKey_mixPreKeys (st.base .responder) l₁ .responder k,
          HandshakeState.preMessageKey_mixPreKeys (st.base .initiator) l₁ .responder k]
      exact (st.preMessageKey_agree .responder k hk).symm)
  have h2b : ((st.base .responder).mixPreKeys l₁).resolvePre .responder
      st.pattern.responderPre = .ok l₂ := by
    rw [h2congr]; exact h2a
  simp only [h2a] at ha
  simp only [h2b] at hb
  simp only [Except.ok.injEq] at ha hb
  subst ha; subst hb
  -- Now assemble the invariant.
  have hsym : (st.base .initiator).sym = (st.base .responder).sym := rfl
  have hpsk : (st.base .initiator).isPsk = (st.base .responder).isPsk := rfl
  refine ⟨by simp [Setup.base, initialHandshakeState], by simp [Setup.base, initialHandshakeState, Role.other], ?_, by simp [Setup.base, initialHandshakeState],
    by simp [Setup.base, initialHandshakeState], by simp [Setup.base, initialHandshakeState], ?_, ?_⟩
  · exact HandshakeState.mixPreKeys_sym_congr l₂
      (HandshakeState.mixPreKeys_sym_congr l₁ hsym hpsk) (by simp [hpsk])
  · -- the initiator's announced keys
    intro k hk
    have hmem : k ∈ st.pattern.initiatorPre := mem_initiatorPre_of_preCtx hk
    obtain ⟨pk, hpk⟩ := HandshakeState.resolvePre_ok .initiator _ h1a k hmem
    have hcontains : k ∈ st.pre .initiator := hmem
    cases hp : st.priv .initiator k with
    | none =>
        exfalso
        cases k <;>
          simp_all [HandshakeState.preMessageKey, Setup.base, initialHandshakeState,
            HandshakeState.ownPriv]
    | some p =>
        refine ⟨p, ?_, ?_⟩
        · cases k <;> simp [Setup.base, initialHandshakeState, HandshakeState.ownPriv, hp]
        · cases k <;>
            simp [Setup.base, initialHandshakeState, HandshakeState.remotePub,
              Setup.remotePub, Role.other, hcontains, hp]
  · -- the responder's announced keys
    intro k hk
    have hmem : k ∈ st.pattern.responderPre := mem_responderPre_of_preCtx hk
    obtain ⟨pk, hpk⟩ := HandshakeState.resolvePre_ok .responder _ h2b k hmem
    have hcontains : k ∈ st.pre .responder := hmem
    cases hp : st.priv .responder k with
    | none =>
        exfalso
        cases k <;>
          simp_all [HandshakeState.preMessageKey, Setup.base, initialHandshakeState,
            HandshakeState.ownPriv]
    | some p =>
        refine ⟨p, ?_, ?_⟩
        · cases k <;> simp [Setup.base, initialHandshakeState, HandshakeState.ownPriv, hp]
        · cases k <;>
            simp [Setup.base, initialHandshakeState, HandshakeState.remotePub,
              Setup.remotePub, Role.other, hcontains, hp]

/-! ## The end-to-end statement -/

/-- **A Noise session is correct.**

Take any valid handshake pattern, any instantiation of the crypto functions
satisfying the two laws of `Noise.Crypto`, and any consistent key setup.
Initialise the two parties and run the whole pattern.  Then

* each party recovers exactly the payload the other sent;
* the two parties finish with the same handshake hash, so the channel binding
  of spec §11.2 is well defined; and
* the two parties finish with the same pair of transport `CipherState`s, so the
  `Split()` of spec §5.2 gives them a working secure channel. -/
theorem session_correct {st : Setup C} (hvalid : PatternValid st.pattern)
    {a b a' b' : HandshakeState C} {ps : List C.Bytes}
    {inputs : List (C.Priv × C.Bytes)}
    (hlen : st.pattern.messages.length = inputs.length)
    (ha : st.state .initiator = .ok a) (hb : st.state .responder = .ok b)
    (hrun : run a b inputs = .ok (a', b', ps)) :
    ps = inputs.map Prod.snd ∧
    a'.sym.getHandshakeHash = b'.sym.getHandshakeHash ∧
    a'.sym.split = b'.sym.split := by
  obtain ⟨cf, hms⟩ := hvalid.messagesStep
  have hmatch := initialize_matched st ha hb
  have hpat : a.messagePatterns = st.pattern.messages := by
    rw [Setup.state_eq] at ha
    split at ha
    · exact absurd ha (by simp)
    split at ha
    · exact absurd ha (by simp)
    · simp only [Except.ok.injEq] at ha
      subst ha
      simp [Setup.base, initialHandshakeState]
  obtain ⟨hps, hfin⟩ := run_correct inputs hmatch hpat hlen hms hrun
  exact ⟨hps, hfin.handshakeHash_eq, hfin.split_eq⟩

end Noise
