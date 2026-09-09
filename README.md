# ScalingTrust — the Noise Protocol Framework in Lean 4

A formalisation of [The Noise Protocol Framework](https://noiseprotocol.org/noise.html),
Revision 34 (Trevor Perrin, 2018-07-11), together with the formal treatment given by
Kobeissi, Nicolas and Bhargavan in *Noise Explorer: Fully Automated Modeling and
Verification for Arbitrary Noise Protocols*
([ePrint 2018/766](https://eprint.iacr.org/2018/766), IEEE EuroS&P 2019).

Noise is the key-exchange framework behind WhatsApp, WireGuard, Lightning and
Signal's transport. It describes a family of protocols in a tiny language of
*tokens* (`e`, `s`, `ee`, `es`, `se`, `ss`, `psk`) arranged into *handshake
patterns*, from which all key derivation and state-machine behaviour is
inferred. This library formalises that language, the rules that decide which
patterns are legitimate, the protocol the patterns denote, and the theorem that
the protocol works.

* **No dependencies.** Lean 4 core only (toolchain `leanprover/lean4:v4.33.0`).
  `lake build` from a clean checkout takes well under a minute.
* **No `sorry`, no `native_decide`.** Every result is checked by the kernel;
  the only axioms used are Lean's own `propext`, `Quot.sound` and
  `Classical.choice`.

## What is proved

### The protocol is correct

The specification defines `WriteMessage` and `ReadMessage` separately and
asserts, without proof, that they fit together. `Noise.session_correct` proves
it, for **every** handshake pattern and **every** instantiation of the crypto
functions:

> Take any valid handshake pattern, any DH/cipher/hash functions satisfying
> `DH(a, pub b) = DH(b, pub a)` and `decrypt k n ad (encrypt k n ad p) = some p`,
> and any consistent key setup. Initialise the two parties (§5.3) and run the
> whole pattern. Then each party recovers exactly the payload the other sent,
> the two finish with the same handshake hash — so the channel binding of §11.2
> is well defined — and with the same pair of transport `CipherState`s from
> `Split()`.

The proof is an invariant, `Noise.Matched`, which says that two `HandshakeState`s
are the two ends of one run: equal symmetric state, opposite roles, and each
party's view of the peer's public keys is correct. `Noise.initialize_matched`
establishes it, `Noise.readMessage_writeMessage` preserves it, and
`Noise.run_correct` iterates it.

Two facts about the crypto functions are used and no others: the Diffie–Hellman
equation (only in `Matched.dhInputOf_eq`) and AEAD correctness (only for the `s`
token and the payload). Nothing is assumed about the hash.
`Noise.Symbolic` exhibits a Dolev–Yao model satisfying both, so the interface is
consistent and the theory is not vacuous.

### The validity rules earn their keep

Spec §7.3 gives four validity rules and §9.3 adds a fifth for PSK patterns.
They are formalised twice — as an executable checker with diagnostics, and as an
inductive relation in the style of Figure 4 of the Noise Explorer paper — and
proved equivalent (`HandshakePattern.isValid_iff_patternValid`), so the checker
is sound *and* complete.

They are then shown to do real work:

* Rule 1 ("parties can only perform DH between keys they possess") is exactly
  the hypothesis the correctness proof needs at every `dh` token. This is why
  `readToken_writeToken` takes a `TokenStep` argument.
* `canEncrypt_ephemeralRandomised` turns the stated rationale for rule 4 into a
  theorem: whenever a party is permitted to encrypt and a key has been
  established, that key was randomised by the party's *own* ephemeral key —
  through `ee`, through its ephemeral-static DH, or through the
  `MixKey(e.public_key)` that §9.2 performs in PSK mode. This is precisely the
  "catastrophic key reuse" the rule exists to prevent.
* `Patterns.KXS_not_valid` shows that `KXS`, the pattern for which §6 of the
  Noise Explorer paper exhibits a man-in-the-middle forgery, is rejected — and
  `Patterns.KXS_analyse` reports the exact violation the paper describes.

All sixty patterns the specification names are proved valid (`Patterns.all_valid`)
and all sixty are *executed* end to end in the symbolic model
(`Examples.all_patterns_run`), so the "if the sender succeeds" hypotheses of the
correctness theorems are discharged concretely.

### The secure channel is a channel

The handshake ends by calling `Split()`, which hands each party two
`CipherState`s. `Noise.Transport` orients them by role and proves that the
result is what it claims to be: `Transport.readStream_writeStream` says a stream
of transport messages of any length arrives intact and in order, and
`Noise.transport_matched_of_matched` connects it to the handshake — both parties
of a completed handshake obtain matched transport states. `Transport.rekeySend`
and `Transport.setRecvNonce` implement the `Rekey` of §11.3 and the out-of-order
handling of §11.4, with `Transport.matched_rekey` and
`Transport.setRecvNonce_read` for their basic properties.

Spec §13 leaves detection of a *truncated* stream to the application, and so do
we: the theorem says what arrives is intact and in order, not that everything
sent arrives.

### The pattern tables are reproduced

* `Patterns.derivationTable_correct` — the pattern derivation rules of §18.3
  generate all thirty-eight one-way, fundamental and deferred patterns, exactly
  as §7.4, §7.5 and §18.1 print them.
* `Patterns.pskTable_correct` — the `pskN` modifiers of §9.4 generate all
  twenty-one recommended PSK patterns, names included; and
  `Patterns.psk_modifiers_preserve_validity` confirms §9.4's remark that any
  such modifier can be applied to any listed pattern.
* `Patterns.XXfallback_eq` — the `fallback` modifier of §10.2 turns `XX` into
  `XXfallback`.
* `Patterns.table77_correct` — the payload security grades of §7.7 are
  reproduced for all fifteen one-way and fundamental patterns, including the
  specification's convention for eliding transport rows.

## Two defects found in Revision 34

`Patterns.table182_correct` proves that all twenty-three deferred patterns match
the §18.2 table — but two of its rows had to be corrected first, because
Revision 34 prints them wrongly. Neither affects the protocol; both are
documentation defects in the table.

1. **`NX1`: the arrows on the two transport rows are interchanged.** The printed
   table gives source grade 2 to a transport payload sent by the initiator, but
   `NX1` is an `N` pattern — its initiator has no static key at all, so nothing
   it sends can ever be authenticated. The grade-2 row is the responder's, and
   it comes first, because `NX1`'s last handshake message is the initiator's.
   Swapping the two arrows yields exactly the computed table.

2. **`X1N`: the table omits its last row.** Once the responder has received the
   initiator's first transport payload — which has source grade 2, since `se`
   has by then been performed — the responder's own transport payloads move from
   `(0, 3)` to `(0, 5)`. By the specification's own elision convention that row
   differs from the responder's last handshake payload and must be listed. Noise
   Explorer (Figure 7 of the paper) likewise reports six graded payloads for
   `X1N`.

Both corrections are recorded in the module documentation of
`ScalingTrust.Noise.Security`, alongside the rows as Revision 34 prints them.

## Two places we depart from the paper's Figure 4

Both are recorded in the module documentation of `ScalingTrust.Noise.Validity`.

1. The paper checks rule 4 only at the end of a message, i.e. only for the
   payload. But an `s` token also calls `ENCRYPT()` once a key is established
   (§5.3: `WriteMessage` appends `EncryptAndHash(s.public_key)`), so rule 4
   applies there too. Checking only at the end of a message is strictly weaker:
   it accepts patterns in which the static public key is encrypted under a key
   derived from `ss` alone and a later token repairs the context. We check at
   every `ENCRYPT()`; `Patterns.encrypt_check_at_static_token` exhibits a
   pattern that separates the two readings.
2. The paper's `MsgPSK` rule requires `psk ∉ Γ`, forbidding a repeated `psk`
   token. The specification explicitly allows repetition (§9.2, and §9.4 names
   `XXpsk0+psk3` as legitimate). We follow the specification and expose the
   paper's stricter reading separately as `HandshakePattern.hasRepeatedPsk`.

We additionally apply rule 4 to *transport* payloads, which the rule mentions
explicitly. This is what rejects `KXS`.

## Modelling choices

Two, both documented at their definitions.

* **Key generation is an input.** §5.3 says the `e` token calls
  `GENERATE_KEYPAIR()`; rather than thread randomness we pass the freshly
  generated private key to `writeMessage`. This keeps the model deterministic,
  which is what makes correctness provable, and makes freshness — required by
  §14 — a proof obligation on the caller.
* **Messages are sequences of fields, not bytes.** §3 observes that Noise
  messages need no parsing because the message pattern determines their shape.
  `Noise.writeMessage_length` proves the fact that licenses this: the number of
  fields in a message is a function of its message pattern. Byte-level framing
  and the 65535-byte limit are therefore out of scope.

## Layout

| Module | Contents |
| --- | --- |
| `Noise.Token` | Key kinds, roles, tokens (§2.2, §7.1) |
| `Noise.Pattern` | Message, pre-message and handshake patterns (§7.1) |
| `Noise.Context` | The context `Γ` of the Noise Explorer paper |
| `Noise.Validity` | Validity rules (§7.3, §9.3), checker ≡ inductive relation |
| `Noise.Patterns` | All sixty named patterns, plus `KXS` |
| `Noise.PatternsValid` | Validity proofs and counterexamples |
| `Noise.Derivation` | The derivation rules of §18.3 |
| `Noise.Modifiers` | Protocol names (§8), `pskN` (§9.4), `fallback` (§10.2) |
| `Noise.Security` | Payload security grades (§7.7, §18.2) |
| `Noise.Crypto` | DH, cipher and hash functions (§4) |
| `Noise.Symbolic` | A Dolev–Yao model of them |
| `Noise.State` | `CipherState`, `SymmetricState` (§5.1, §5.2) |
| `Noise.Handshake` | `HandshakeState`, `Initialize`, `WriteMessage`, `ReadMessage` (§5.3) |
| `Noise.Correctness` | The matching invariant and `run_correct` |
| `Noise.Session` | `initialize_matched` and `session_correct` |
| `Noise.Transport` | The transport phase (§5, §11.3, §11.4) |
| `Noise.Examples` | Every pattern executed in the symbolic model |

## Not formalised

Byte-level message framing (§3); the concrete algorithms of §12 (Curve25519,
ChaCha20-Poly1305, SHA-256, BLAKE2 …), which enter only through the `Crypto`
interface; the identity-hiding grades of §7.8, which the Noise Explorer paper
also leaves to future work; the negotiation and switching machinery of compound
protocols (§10.3–§10.5), of which only the `fallback` modifier is formalised;
half-duplex mode (§11.5); and any computational (as opposed to symbolic)
security argument. Rekey and out-of-order delivery (§11.3, §11.4) are
implemented, but *when* to use them is an application policy and is not
modelled. The payload security grades of §7.7 are *computed and checked against
the specification's tables*, not proved from a security model — a proof of that
kind is what ProVerif supplies in the Noise Explorer paper, and it is out of
scope here.

## Building

```sh
lake build
```

To explore, open `ScalingTrust/Noise/Examples.lean` and uncomment the `#eval`
lines at the bottom: they print patterns in the specification's own notation,
run handshakes in the symbolic model, and show the resulting Dolev–Yao terms.
