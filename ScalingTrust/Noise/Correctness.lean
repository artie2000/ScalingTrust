/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.Noise.Handshake
import ScalingTrust.Noise.Validity

/-!
# Functional correctness of the handshake

The specification describes `WriteMessage` and `ReadMessage` separately, and
asserts — but does not prove — that they fit together: that the two parties end
a handshake holding the same chaining key, the same handshake hash, and the same
pair of transport `CipherState`s, and that each payload arrives as it was sent.

This file proves exactly that, for **every** handshake pattern and **every**
instantiation of the crypto functions, from just the two laws in `Noise.Crypto`.

## The invariant

Two `HandshakeState`s are `Matched c r a b` when they are the two endpoints of
one handshake run in which `a` plays role `r`, and the facts recorded by the
validity context `c` really have happened: same symmetric state, opposite roles,
same remaining pattern, and — the substantive part — every public key that `c`
records as *communicated* really is held by its owner and known, correctly, to
the peer.

`Matched` is preserved by every token, hence by every message.  Its `sym`
component is the conclusion: agreement on `ck`, `h`, `k` and `n`.

## Where validity is used

The invariant only knows about keys the context records as communicated, so the
Diffie–Hellman step lemma needs to know that both keys of a `dh` token have been
communicated.  That is precisely validity rule 1 of spec §7.3, "Parties can only
perform DH between private keys and public keys they possess", which is why
`readToken_writeToken` takes a `TokenStep` hypothesis.  This is the sense in
which the validity rules earn their keep: they are exactly what makes the
handshake run.

The Diffie–Hellman law `Crypto.dh_comm` is used only in `Matched.dhInputOf_eq`,
and AEAD correctness only in the `s`-token and payload cases; nothing else about
the primitives is assumed.
-/

namespace Noise

variable {C : Crypto}

/-! ## The matching invariant -/

/-- Two `HandshakeState`s are *matched at context `c`, with `a` in role `r`*,
when they are the two ends of the same handshake run and `c` describes it
correctly.

The last two fields say that whenever `c` records a public key as having been
communicated, its owner really holds the corresponding private key and the peer
really holds that public key. -/
structure Matched (c : Ctx) (r : Role) (a b : HandshakeState C) : Prop where
  /-- `a` plays role `r`. -/
  aRole : a.role = r
  /-- `b` plays the other role. -/
  bRole : b.role = r.other
  /-- The two parties agree on `ck`, `h`, `k` and `n`. -/
  sym : a.sym = b.sym
  /-- They agree on whether this is a PSK handshake. -/
  isPsk : a.isPsk = b.isPsk
  /-- They are at the same point of the same pattern. -/
  patterns : a.messagePatterns = b.messagePatterns
  /-- They hold the same pre-shared key, if any. -/
  psk : a.psk = b.psk
  /-- Every key of `a`'s that the context records as communicated is held by `a`
  and correctly known to `b`. -/
  aKeys : ∀ k, c.hasKey r k = true →
    ∃ p, a.ownPriv k = some p ∧ b.remotePub k = some (C.pub p)
  /-- Every key of `b`'s that the context records as communicated is held by `b`
  and correctly known to `a`. -/
  bKeys : ∀ k, c.hasKey r.other k = true →
    ∃ p, b.ownPriv k = some p ∧ a.remotePub k = some (C.pub p)

namespace Matched

theorem symm {c : Ctx} {r : Role} {a b : HandshakeState C} (h : Matched c r a b) :
    Matched c r.other b a :=
  ⟨h.bRole, by rw [h.aRole, Role.other_other], h.sym.symm, h.isPsk.symm, h.patterns.symm,
   h.psk.symm, h.bKeys, by rw [Role.other_other]; exact h.aKeys⟩

/-- Matched parties compute the same handshake hash, which is what makes the
channel binding of spec §11.2 well defined. -/
theorem handshakeHash_eq {c : Ctx} {r : Role} {a b : HandshakeState C} (h : Matched c r a b) :
    a.sym.getHandshakeHash = b.sym.getHandshakeHash := by rw [h.sym]

/-- Matched parties compute the same pair of transport `CipherState`s. -/
theorem split_eq {c : Ctx} {r : Role} {a b : HandshakeState C} (h : Matched c r a b) :
    a.sym.split = b.sym.split := by rw [h.sym]

theorem mixEphemeral_eq {c : Ctx} {r : Role} {a b : HandshakeState C} (h : Matched c r a b)
    (pk : C.Bytes) : a.mixEphemeral pk = b.mixEphemeral pk := by
  unfold HandshakeState.mixEphemeral
  rw [h.sym, h.isPsk]

/-- **The Diffie–Hellman step agrees.**  If both keys of a DH have been
communicated, then whatever value a party feeds to `MixKey`, its peer feeds the
same value.

This is the one place `Crypto.dh_comm` is used. -/
theorem dhInputOf_eq {c : Ctx} {r : Role} {a b : HandshakeState C} (h : Matched c r a b)
    (own remote : KeyKind) (h1 : c.hasKey r own = true) (h2 : c.hasKey r.other remote = true) :
    a.dhInputOf own remote = b.dhInputOf remote own := by
  obtain ⟨p, hp, hbp⟩ := h.aKeys own h1
  obtain ⟨q, hq, haq⟩ := h.bKeys remote h2
  unfold HandshakeState.dhInputOf
  rw [hp, haq, hq, hbp, h.aRole, h.bRole]
  cases r <;> simp [HandshakeState.dhKinds, Role.other, C.dh_comm p q]

/-- Both parties feed the same value to `MixKey` for a given DH token, provided
both public keys involved have been communicated (spec §7.3 rule 1). -/
theorem dhInput_eq {c : Ctx} {r : Role} {a b : HandshakeState C} (h : Matched c r a b)
    (α β : KeyKind) (hα : c.hasKey .initiator α = true) (hβ : c.hasKey .responder β = true) :
    a.dhInput α β = b.dhInput α β := by
  unfold HandshakeState.dhInput
  rw [h.aRole, h.bRole]
  cases r with
  | initiator => exact h.dhInputOf_eq α β hα hβ
  | responder => exact h.dhInputOf_eq β α hβ hα

theorem mixDH {c : Ctx} {r : Role} {a b : HandshakeState C} (h : Matched c r a b)
    (α β : KeyKind) (hα : c.hasKey .initiator α = true) (hβ : c.hasKey .responder β = true)
    {a' : HandshakeState C} (hw : a.mixDH α β = .ok a') :
    ∃ ikm, a' = { a with sym := a.sym.mixKey ikm } ∧
      b.mixDH α β = .ok { b with sym := b.sym.mixKey ikm } := by
  have hex : ∃ ikm, a.dhInput α β = .ok ikm := by
    cases hd : a.dhInput α β with
    | ok ikm => exact ⟨ikm, rfl⟩
    | error e => unfold HandshakeState.mixDH at hw; simp [hd, Except.map] at hw
  obtain ⟨ikm, hd⟩ := hex
  refine ⟨ikm, ?_, ?_⟩
  · unfold HandshakeState.mixDH at hw
    simp only [hd, Except.map] at hw
    simpa using hw.symm
  · unfold HandshakeState.mixDH; rw [← h.dhInput_eq α β hα hβ, hd]; rfl

end Matched

/-! ## One token -/

/-- **Reading inverts writing, token by token.**

If a matched party writes a token that the validity rules admit, its peer reads
exactly the fields written, consumes exactly those fields, and the two states
remain matched at the updated context. -/
theorem readToken_writeToken {c c' : Ctx} {r : Role} {a b : HandshakeState C}
    (h : Matched c r a b) (eph : C.Priv) {t : Token} (hv : TokenStep r c t c')
    (rest : Message C) {a' : HandshakeState C} {out : List C.Bytes}
    (hw : a.writeToken eph t = .ok (a', out)) :
    ∃ b', b.readToken t (out ++ rest) = .ok (b', rest) ∧ Matched c' r a' b' := by
  cases hv with
  | ephemeral hk =>
      simp only [HandshakeState.writeToken, Except.ok.injEq, Prod.mk.injEq] at hw
      obtain ⟨h1, h2⟩ := hw
      subst h1; subst h2
      refine ⟨{ b with re := some (C.pub eph), sym := b.mixEphemeral (C.pub eph) }, rfl, ?_⟩
      refine ⟨h.aRole, h.bRole, h.mixEphemeral_eq _, h.isPsk, h.patterns, h.psk, ?_, ?_⟩
      · intro k hk'
        cases k with
        | e => exact ⟨eph, rfl, rfl⟩
        | s => rw [Ctx.hasKey_setKey_e_s] at hk'; exact h.aKeys .s hk'
      · intro k hk'
        rw [Ctx.hasKey_setKey_other_role] at hk'
        exact h.bKeys k hk'
  | static hk hce =>
      simp only [HandshakeState.writeToken] at hw
      cases hs : a.s with
      | none => simp [hs] at hw
      | some sk =>
          simp only [hs] at hw
          cases he : a.sym.encryptAndHash (C.pub sk) with
          | error err => simp [he] at hw
          | ok res =>
              obtain ⟨symA, ct⟩ := res
              simp only [he, Except.ok.injEq, Prod.mk.injEq] at hw
              obtain ⟨h1, h2⟩ := hw
              subst h1; subst h2
              have hd : b.sym.decryptAndHash ct = .ok (symA, C.pub sk) := by
                rw [h.sym] at he
                exact SymmetricState.decryptAndHash_encryptAndHash _ _ he
              refine ⟨{ b with rs := some (C.pub sk), sym := symA }, ?_, ?_⟩
              · simp only [HandshakeState.readToken, List.singleton_append, hd]
              · refine ⟨h.aRole, h.bRole, rfl, h.isPsk, h.patterns, h.psk, ?_, ?_⟩
                · intro k hk'
                  cases k with
                  | e => rw [Ctx.hasKey_setKey_s_e] at hk'; exact h.aKeys .e hk'
                  | s => exact ⟨sk, rfl, rfl⟩
                · intro k hk'
                  rw [Ctx.hasKey_setKey_other_role] at hk'
                  exact h.bKeys k hk'
  | @dh α β h1 h2 h3 =>
      simp only [HandshakeState.writeToken] at hw
      cases hm : a.mixDH α β with
      | error err => simp [hm] at hw
      | ok a₁ =>
          simp only [hm, Except.ok.injEq, Prod.mk.injEq] at hw
          obtain ⟨hq1, hq2⟩ := hw
          subst hq1; subst hq2
          obtain ⟨ikm, ha, hb⟩ := h.mixDH α β h1 h2 hm
          refine ⟨{ b with sym := b.sym.mixKey ikm }, ?_, ?_⟩
          · simp only [HandshakeState.readToken, List.nil_append, hb]
          · subst ha
            exact ⟨h.aRole, h.bRole, by rw [h.sym], h.isPsk, h.patterns, h.psk,
                   fun k hk => h.aKeys k (by simpa using hk),
                   fun k hk => h.bKeys k (by simpa using hk)⟩
  | psk =>
      simp only [HandshakeState.writeToken] at hw
      cases hp : a.psk with
      | none => simp [hp] at hw
      | some key =>
          simp only [hp, Except.ok.injEq, Prod.mk.injEq] at hw
          obtain ⟨h1, h2⟩ := hw
          subst h1; subst h2
          have hbp : b.psk = some key := by rw [← h.psk, hp]
          refine ⟨{ b with sym := b.sym.mixKeyAndHash key }, ?_, ?_⟩
          · simp only [HandshakeState.readToken, List.nil_append, hbp]
          · exact ⟨h.aRole, h.bRole, by rw [h.sym], h.isPsk, h.patterns, hbp.symm,
                   fun k hk => h.aKeys k (by simpa using hk),
                   fun k hk => h.bKeys k (by simpa using hk)⟩

/-! ## One message -/

/-- Reading inverts writing for a whole sequence of tokens. -/
theorem readTokens_writeTokens (eph : C.Priv) (ts : List Token) :
    ∀ {c c' : Ctx} {r : Role} {a b a' : HandshakeState C} {out : List C.Bytes}
      (rest : Message C),
      Matched c r a b → TokensStep r c ts c' →
      HandshakeState.writeTokens eph a ts = .ok (a', out) →
      ∃ b', HandshakeState.readTokens b ts (out ++ rest) = .ok (b', rest) ∧
        Matched c' r a' b' := by
  induction ts with
  | nil =>
      intro c c' r a b a' out rest h hv hw
      cases hv
      simp only [HandshakeState.writeTokens, Except.ok.injEq, Prod.mk.injEq] at hw
      obtain ⟨h1, h2⟩ := hw
      subst h1; subst h2
      exact ⟨b, rfl, h⟩
  | cons t ts ih =>
      intro c c' r a b a' out rest h hv hw
      cases hv with
      | cons hstep hrestv =>
          simp only [HandshakeState.writeTokens] at hw
          cases hwt : a.writeToken eph t with
          | error err => simp [hwt] at hw
          | ok p =>
              obtain ⟨a₁, o₁⟩ := p
              simp only [hwt] at hw
              cases hwr : HandshakeState.writeTokens eph a₁ ts with
              | error err => simp [hwr] at hw
              | ok q =>
                  obtain ⟨a₂, o₂⟩ := q
                  simp only [hwr, Except.ok.injEq, Prod.mk.injEq] at hw
                  obtain ⟨h1, h2⟩ := hw
                  subst h1; subst h2
                  obtain ⟨b₁, hrt, h₁⟩ := readToken_writeToken h eph hstep (o₂ ++ rest) hwt
                  obtain ⟨b₂, hrs, h₂⟩ := ih rest h₁ hrestv hwr
                  refine ⟨b₂, ?_, h₂⟩
                  simp only [HandshakeState.readTokens, List.append_assoc, hrt]
                  exact hrs

/-- **Reading inverts writing, message by message.**

If a matched party writes a handshake message that the validity rules admit, its
peer reads that message successfully, recovers exactly the payload that was
written, obtains the same pair of transport `CipherState`s when the handshake
ends, and the two states remain matched. -/
theorem readMessage_writeMessage {c c' : Ctx} {r : Role} {a b : HandshakeState C}
    {m : MessagePattern} {ms : List MessagePattern} (h : Matched c r a b)
    (hm : a.messagePatterns = m :: ms) (hv : MessageStep r c m c') (eph : C.Priv)
    (payload : C.Bytes) {a' : HandshakeState C} {msg : Message C}
    {sp : Option (CipherState C × CipherState C)}
    (hw : a.writeMessage eph payload = .ok (a', msg, sp)) :
    ∃ b', b.readMessage msg = .ok (b', payload, sp) ∧ Matched c' r a' b' ∧
      a'.messagePatterns = ms := by
  obtain ⟨hts, -⟩ := hv
  simp only [HandshakeState.writeMessage, hm] at hw
  cases hwt : HandshakeState.writeTokens eph a m with
  | error err => simp [hwt] at hw
  | ok p =>
      obtain ⟨a₁, fields⟩ := p
      simp only [hwt] at hw
      cases he : a₁.sym.encryptAndHash payload with
      | error err => simp [he] at hw
      | ok res =>
          obtain ⟨symA, ct⟩ := res
          simp only [he, Except.ok.injEq, Prod.mk.injEq] at hw
          obtain ⟨h1, h2, h3⟩ := hw
          obtain ⟨b₁, hrt, h₁⟩ := readTokens_writeTokens eph m [ct] h hts hwt
          have hbm : b.messagePatterns = m :: ms := by rw [← h.patterns, hm]
          have hd : b₁.sym.decryptAndHash ct = .ok (symA, payload) := by
            rw [h₁.sym] at he
            exact SymmetricState.decryptAndHash_encryptAndHash _ _ he
          subst h1; subst h2; subst h3
          refine ⟨{ b₁ with sym := symA, messagePatterns := ms }, ?_, ?_, rfl⟩
          · simp only [HandshakeState.readMessage, hbm, hrt, hd]
          · exact ⟨h₁.aRole, h₁.bRole, rfl, h₁.isPsk, rfl, h₁.psk, h₁.aKeys, h₁.bKeys⟩

/-! ## A whole handshake -/

/-- Run a handshake between two matched states.  Each element of `inputs` is the
ephemeral key pair the sender would generate together with the payload it sends;
the parties alternate, starting with `a`.

Returns the final state of `a`, the final state of `b`, and the payloads
recovered by the receivers, in order. -/
def run : HandshakeState C → HandshakeState C → List (C.Priv × C.Bytes) →
    Except NoiseError (HandshakeState C × HandshakeState C × List C.Bytes)
  | a, b, [] => .ok (a, b, [])
  | a, b, i :: rest =>
      match a.writeMessage i.1 i.2 with
      | .error err => .error err
      | .ok w =>
          match b.readMessage w.2.1 with
          | .error err => .error err
          | .ok res =>
              -- the parties swap: the reader sends the next message
              match run res.1 w.1 rest with
              | .error err => .error err
              | .ok f => .ok (f.2.1, f.1, res.2.1 :: f.2.2)

/-- **Handshake correctness.**

Let two parties be matched at the start of a handshake pattern whose messages
satisfy the validity rules, and let them run the whole pattern.  Then

* every payload is recovered exactly as it was sent, and
* the two final states are still matched at the final validity context; in
  particular they agree on the chaining key, on the handshake hash (spec §11.2)
  and on the pair of transport `CipherState`s returned by `Split()`.

This holds for every handshake pattern and every instantiation of the crypto
functions satisfying `Crypto.dh_comm` and `Crypto.decrypt_encrypt`. -/
theorem run_correct : ∀ (inputs : List (C.Priv × C.Bytes)) {c cf : Ctx} {r : Role}
      {a b a' b' : HandshakeState C} {ps : List C.Bytes} {ms : List MessagePattern},
      Matched c r a b → a.messagePatterns = ms → ms.length = inputs.length →
      MessagesStep r c ms cf → run a b inputs = .ok (a', b', ps) →
      ps = inputs.map Prod.snd ∧ Matched cf r a' b' := by
  intro inputs
  induction inputs with
  | nil =>
      intro c cf r a b a' b' ps ms h hm hlen hv hr
      cases ms with
      | cons m ms => exact absurd hlen (by simp)
      | nil =>
          cases hv
          simp only [run, Except.ok.injEq, Prod.mk.injEq] at hr
          obtain ⟨h1, h2, h3⟩ := hr
          subst h1; subst h2; subst h3
          exact ⟨rfl, h⟩
  | cons i rest ih =>
      intro c cf r a b a' b' ps ms h hm hlen hv hr
      cases ms with
      | nil => exact absurd hlen (by simp)
      | cons m ms =>
          cases hv with
          | cons hmsg hrestv =>
              simp only [run] at hr
              cases hw : a.writeMessage i.1 i.2 with
              | error err => simp [hw] at hr
              | ok w =>
                  obtain ⟨a₁, msg, sp⟩ := w
                  simp only [hw] at hr
                  obtain ⟨b₁, hrd, h₁, hpat⟩ :=
                    readMessage_writeMessage h hm hmsg i.1 i.2 hw
                  simp only [hrd] at hr
                  cases hrun : run b₁ a₁ rest with
                  | error err => simp [hrun] at hr
                  | ok f =>
                      obtain ⟨b₂, a₂, ps'⟩ := f
                      simp only [hrun, Except.ok.injEq, Prod.mk.injEq] at hr
                      obtain ⟨h1, h2, h3⟩ := hr
                      have hbpat : b₁.messagePatterns = ms := by
                        rw [← h₁.patterns, hpat]
                      obtain ⟨hps, h₂⟩ :=
                        ih h₁.symm hbpat (by simpa using hlen) hrestv hrun
                      subst h1; subst h2; subst h3
                      have hfin : Matched cf r.other.other a₂ b₂ := h₂.symm
                      rw [Role.other_other] at hfin
                      exact ⟨by simp [hps], hfin⟩

/-! ## Message shape

Spec §3: "All Noise messages can be processed without parsing, since there are
no type or length fields."  What licenses this is that the number of fields in a
message is determined by its message pattern. -/

theorem writeTokens_length (eph : C.Priv) (ts : List Token) :
    ∀ {a a' : HandshakeState C} {out : List C.Bytes},
      HandshakeState.writeTokens eph a ts = .ok (a', out) →
      out.length = (ts.filter Token.isKey).length := by
  induction ts with
  | nil =>
      intro a a' out hw
      simp only [HandshakeState.writeTokens, Except.ok.injEq, Prod.mk.injEq] at hw
      obtain ⟨-, h2⟩ := hw
      subst h2; rfl
  | cons t ts ih =>
      intro a a' out hw
      simp only [HandshakeState.writeTokens] at hw
      cases hwt : a.writeToken eph t with
      | error err => simp [hwt] at hw
      | ok p =>
          obtain ⟨a₁, o₁⟩ := p
          simp only [hwt] at hw
          cases hwr : HandshakeState.writeTokens eph a₁ ts with
          | error err => simp [hwr] at hw
          | ok q =>
              obtain ⟨a₂, o₂⟩ := q
              simp only [hwr, Except.ok.injEq, Prod.mk.injEq] at hw
              obtain ⟨-, h2⟩ := hw
              subst h2
              have h1 : o₁.length = (List.filter Token.isKey [t]).length := by
                cases t with
                | key k =>
                    cases k with
                    | e =>
                        simp only [HandshakeState.writeToken, Except.ok.injEq,
                          Prod.mk.injEq] at hwt
                        obtain ⟨-, hh⟩ := hwt
                        subst hh; rfl
                    | s =>
                        simp only [HandshakeState.writeToken] at hwt
                        cases hs : a.s with
                        | none => simp [hs] at hwt
                        | some sk =>
                            simp only [hs] at hwt
                            cases he : a.sym.encryptAndHash (C.pub sk) with
                            | error err => simp [he] at hwt
                            | ok res =>
                                obtain ⟨symA, ct⟩ := res
                                simp only [he, Except.ok.injEq, Prod.mk.injEq] at hwt
                                obtain ⟨-, hh⟩ := hwt
                                subst hh; rfl
                | dh α β =>
                    simp only [HandshakeState.writeToken] at hwt
                    cases hmm : a.mixDH α β with
                    | error err => simp [hmm] at hwt
                    | ok a₃ =>
                        simp only [hmm, Except.ok.injEq, Prod.mk.injEq] at hwt
                        obtain ⟨-, hh⟩ := hwt
                        subst hh; rfl
                | psk =>
                    simp only [HandshakeState.writeToken] at hwt
                    cases hp : a.psk with
                    | none => simp [hp] at hwt
                    | some key =>
                        simp only [hp, Except.ok.injEq, Prod.mk.injEq] at hwt
                        obtain ⟨-, hh⟩ := hwt
                        subst hh; rfl
              simp only [List.length_append, ih hwr, h1, List.filter_cons]
              cases Token.isKey t <;> simp <;> omega

/-- The number of fields in a written message is determined by its message
pattern, so a receiver can parse it without any type or length fields
(spec §3). -/
theorem writeMessage_length {a a' : HandshakeState C} {eph : C.Priv} {payload : C.Bytes}
    {msg : Message C} {sp : Option (CipherState C × CipherState C)} {m : MessagePattern}
    {ms : List MessagePattern} (hm : a.messagePatterns = m :: ms)
    (hw : a.writeMessage eph payload = .ok (a', msg, sp)) :
    msg.length = m.fieldCount := by
  simp only [HandshakeState.writeMessage, hm] at hw
  cases hwt : HandshakeState.writeTokens eph a m with
  | error err => simp [hwt] at hw
  | ok p =>
      obtain ⟨a₁, fields⟩ := p
      simp only [hwt] at hw
      cases he : a₁.sym.encryptAndHash payload with
      | error err => simp [he] at hw
      | ok res =>
          obtain ⟨symA, ct⟩ := res
          simp only [he, Except.ok.injEq, Prod.mk.injEq] at hw
          obtain ⟨-, h2, -⟩ := hw
          subst h2
          simp [MessagePattern.fieldCount, writeTokens_length eph m hwt]

end Noise
