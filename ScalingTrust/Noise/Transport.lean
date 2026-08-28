/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.Noise.Correctness

/-!
# The transport phase

Spec §5:

> Processing the final handshake message returns two `CipherState` objects, the
> first for encrypting transport messages from initiator to responder, and the
> second for messages in the other direction. …
>
> Transport messages are then encrypted and decrypted by calling
> `EncryptWithAd()` and `DecryptWithAd()` on the relevant `CipherState` with
> zero-length associated data.

This file gives a party's view of the transport phase — the two `CipherState`s
it holds, oriented by its role — and proves that a stream of transport messages
round-trips, for arbitrarily many messages in either direction and interleaved
in any order.

The advanced features of §11 are also here: `Rekey` (§11.3) and `SetNonce`
(§11.4), both of which are operations on a single `CipherState` and are already
defined in `ScalingTrust.Noise.State`.
-/

namespace Noise

variable {C : Crypto}

/-- One party's transport state: the `CipherState` it sends with and the one it
receives with. -/
structure Transport (C : Crypto) where
  /-- Used to encrypt outgoing transport messages. -/
  send : CipherState C
  /-- Used to decrypt incoming transport messages. -/
  recv : CipherState C

namespace Transport

/-- Orient the pair returned by `Split()` for a party in the given role
(spec §5.3: the first `CipherState` is "for encrypting transport messages from
initiator to responder"). -/
def ofSplit : Role → CipherState C × CipherState C → Transport C
  | .initiator, p => ⟨p.1, p.2⟩
  | .responder, p => ⟨p.2, p.1⟩

/-- Send one transport message: `EncryptWithAd` with zero-length associated
data (spec §5). -/
def write (t : Transport C) (payload : C.Bytes) :
    Except NoiseError (Transport C × C.Bytes) :=
  match t.send.encryptWithAd C.emptyBytes payload with
  | .error err => .error err
  | .ok (cs, ct) => .ok ({ t with send := cs }, ct)

/-- Receive one transport message: `DecryptWithAd` with zero-length associated
data (spec §5). -/
def read (t : Transport C) (ct : C.Bytes) :
    Except NoiseError (Transport C × C.Bytes) :=
  match t.recv.decryptWithAd C.emptyBytes ct with
  | .error err => .error err
  | .ok (cs, p) => .ok ({ t with recv := cs }, p)

/-- Spec §11.3: "Parties might wish to periodically update their cipherstate
keys using a one-way function."  Rekeying the sending state. -/
def rekeySend (t : Transport C) : Transport C := { t with send := t.send.rekey }

/-- Rekeying the receiving state (spec §11.3). -/
def rekeyRecv (t : Transport C) : Transport C := { t with recv := t.recv.rekey }

/-- Spec §11.4: for out-of-order delivery, "the recipient would call the
`SetNonce()` function on the receiving `CipherState` using the received `n`
value". -/
def setRecvNonce (t : Transport C) (n : Nat) : Transport C :=
  { t with recv := t.recv.setNonce n }

/-- Send a stream of transport messages. -/
def writeStream (t : Transport C) :
    List C.Bytes → Except NoiseError (Transport C × List C.Bytes)
  | [] => .ok (t, [])
  | p :: ps =>
      match t.write p with
      | .error err => .error err
      | .ok (t', ct) =>
          match t'.writeStream ps with
          | .error err => .error err
          | .ok (t'', cts) => .ok (t'', ct :: cts)

/-- Receive a stream of transport messages. -/
def readStream (t : Transport C) :
    List C.Bytes → Except NoiseError (Transport C × List C.Bytes)
  | [] => .ok (t, [])
  | ct :: cts =>
      match t.read ct with
      | .error err => .error err
      | .ok (t', p) =>
          match t'.readStream cts with
          | .error err => .error err
          | .ok (t'', ps) => .ok (t'', p :: ps)

/-- Two transport states are matched when each party's sending `CipherState` is
the other's receiving one. -/
structure Matched (a b : Transport C) : Prop where
  /-- What `a` sends with, `b` receives with. -/
  sendRecv : a.send = b.recv
  /-- What `a` receives with, `b` sends with. -/
  recvSend : a.recv = b.send

theorem Matched.symm {a b : Transport C} (h : Matched a b) : Matched b a :=
  ⟨h.recvSend.symm, h.sendRecv.symm⟩

/-- **The two parties agree on how to orient `Split()`'s output.**  Whatever
pair of `CipherState`s the handshake produced, the initiator's view and the
responder's view of it are matched. -/
theorem matched_ofSplit (p : CipherState C × CipherState C) :
    Matched (ofSplit .initiator p) (ofSplit .responder p) := ⟨rfl, rfl⟩

/-- **One transport message round-trips.** -/
theorem read_write {a b : Transport C} (h : Matched a b) (payload : C.Bytes)
    {a' : Transport C} {ct : C.Bytes} (hw : a.write payload = .ok (a', ct)) :
    ∃ b', b.read ct = .ok (b', payload) ∧ Matched a' b' := by
  unfold write at hw
  cases he : a.send.encryptWithAd C.emptyBytes payload with
  | error err => simp [he] at hw
  | ok res =>
      obtain ⟨cs, ct'⟩ := res
      simp only [he, Except.ok.injEq, Prod.mk.injEq] at hw
      obtain ⟨h1, h2⟩ := hw
      subst h1; subst h2
      have hd : b.recv.decryptWithAd C.emptyBytes ct' = .ok (cs, payload) := by
        rw [← h.sendRecv]
        exact CipherState.decryptWithAd_encryptWithAd _ _ _ he
      exact ⟨{ b with recv := cs }, by simp only [read, hd], ⟨rfl, h.recvSend⟩⟩

/-- **A whole stream of transport messages round-trips**, in order, however
long.  Spec §13 leaves truncation detection to the application, so this says
nothing about an attacker cutting the stream short — only that what does arrive
arrives intact and in order. -/
theorem readStream_writeStream (ps : List C.Bytes) :
    ∀ {a b a' : Transport C} {cts : List C.Bytes},
      Matched a b → a.writeStream ps = .ok (a', cts) →
      ∃ b', b.readStream cts = .ok (b', ps) ∧ Matched a' b' := by
  induction ps with
  | nil =>
      intro a b a' cts h hw
      simp only [writeStream, Except.ok.injEq, Prod.mk.injEq] at hw
      obtain ⟨h1, h2⟩ := hw
      subst h1; subst h2
      exact ⟨b, rfl, h⟩
  | cons p ps ih =>
      intro a b a' cts h hw
      simp only [writeStream] at hw
      cases hwr : a.write p with
      | error err => simp [hwr] at hw
      | ok res =>
          obtain ⟨a₁, ct⟩ := res
          simp only [hwr] at hw
          cases hws : a₁.writeStream ps with
          | error err => simp [hws] at hw
          | ok res' =>
              obtain ⟨a₂, cts'⟩ := res'
              simp only [hws, Except.ok.injEq, Prod.mk.injEq] at hw
              obtain ⟨h1, h2⟩ := hw
              subst h1; subst h2
              obtain ⟨b₁, hr, h₁⟩ := read_write h p hwr
              obtain ⟨b₂, hrs, h₂⟩ := ih h₁ hws
              exact ⟨b₂, by simp only [readStream, hr, hrs], h₂⟩

/-- Rekeying is symmetric: if both parties rekey the `CipherState` they share
for one direction, they stay matched (spec §11.3). -/
theorem matched_rekey {a b : Transport C} (h : Matched a b) :
    Matched a.rekeySend b.rekeyRecv :=
  ⟨by simp only [rekeySend, rekeyRecv, CipherState.rekey, h.sendRecv], h.recvSend⟩

/-- Setting the receiving nonce, as §11.4 prescribes for out-of-order delivery,
undoes itself: after receiving a message sent with nonce `n`, the receiver is
positioned at `n + 1`. -/
theorem setRecvNonce_read {t : Transport C} {n : Nat} {ct : C.Bytes}
    {t' : Transport C} {p : C.Bytes} (hk : t.recv.hasKey = true)
    (h : (t.setRecvNonce n).read ct = .ok (t', p)) : t'.recv.n = n + 1 := by
  unfold read at h
  cases hd : (t.setRecvNonce n).recv.decryptWithAd C.emptyBytes ct with
  | error err => simp [hd] at h
  | ok res =>
      obtain ⟨cs, pl⟩ := res
      simp only [hd, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, -⟩ := h
      subst h1
      exact (CipherState.decryptWithAd_advances hd (by simpa [setRecvNonce, CipherState.hasKey,
        CipherState.setNonce] using hk)).2

end Transport

/-! ## Joining the handshake to the transport phase -/

/-- Both parties of a completed handshake orient `Split()`'s output into matched
transport states, so the secure channel they obtain really is a channel: every
transport message one sends, the other reads, exactly and in order. -/
theorem transport_matched_of_matched {c : Ctx} {r : Role} {a b : HandshakeState C}
    (h : Matched c r a b) :
    Transport.Matched (Transport.ofSplit r a.sym.split) (Transport.ofSplit r.other b.sym.split) := by
  rw [← h.split_eq]
  cases r
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

end Noise
