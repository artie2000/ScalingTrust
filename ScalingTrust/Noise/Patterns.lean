/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.Noise.Validity

/-!
# The handshake patterns of the specification

Every handshake pattern named in Revision 34 of the Noise specification:

* the three one-way patterns of §7.4 (`N`, `K`, `X`);
* the twelve fundamental interactive patterns of §7.5;
* the twenty-three deferred patterns of §18.1;
* the twenty-one recommended PSK patterns of §9.4;

together with `XXfallback` (§10.2) and `KXS`, the deliberately *invalid* pattern
analysed in §6 of the Noise Explorer paper.

Patterns are always stored in **canonical (initiator-first) form** (spec §7.2),
so the first message is the initiator's and directions alternate.  `XXfallback`
is printed by the spec in Bob-initiated form; we store the canonical form,
obtained by reversing the arrows and swapping `es` with `se`.
-/

namespace Noise
namespace Patterns

open HandshakePattern

/-- Convenience constructor. -/
private def mk (name : String) (initiatorPre responderPre : PreMessagePattern)
    (messages : List MessagePattern) : HandshakePattern :=
  { name, initiatorPre, responderPre, messages }

/-! ## One-way patterns (spec §7.4)

> One-way patterns are named with a single character, which indicates the status
> of the sender's static key:
> `N` = No static key for sender, `K` = static key Known to recipient,
> `X` = static key Xmitted to recipient.
-/

/-- `N: <- s ... -> e, es` -/
def N : HandshakePattern := mk "N" [] [.s] [[.e, .es]]

/-- `K: -> s <- s ... -> e, es, ss` -/
def K : HandshakePattern := mk "K" [.s] [.s] [[.e, .es, .ss]]

/-- `X: <- s ... -> e, es, s, ss` -/
def X : HandshakePattern := mk "X" [] [.s] [[.e, .es, .s, .ss]]

/-! ## Fundamental interactive patterns (spec §7.5) -/

/-- `NN: -> e / <- e, ee` -/
def NN : HandshakePattern := mk "NN" [] [] [[.e], [.e, .ee]]

/-- `NK: <- s ... -> e, es / <- e, ee` -/
def NK : HandshakePattern := mk "NK" [] [.s] [[.e, .es], [.e, .ee]]

/-- `NX: -> e / <- e, ee, s, es` -/
def NX : HandshakePattern := mk "NX" [] [] [[.e], [.e, .ee, .s, .es]]

/-- `XN: -> e / <- e, ee / -> s, se` -/
def XN : HandshakePattern := mk "XN" [] [] [[.e], [.e, .ee], [.s, .se]]

/-- `XK: <- s ... -> e, es / <- e, ee / -> s, se` -/
def XK : HandshakePattern := mk "XK" [] [.s] [[.e, .es], [.e, .ee], [.s, .se]]

/-- `XX: -> e / <- e, ee, s, es / -> s, se` -/
def XX : HandshakePattern := mk "XX" [] [] [[.e], [.e, .ee, .s, .es], [.s, .se]]

/-- `KN: -> s ... -> e / <- e, ee, se` -/
def KN : HandshakePattern := mk "KN" [.s] [] [[.e], [.e, .ee, .se]]

/-- `KK: -> s <- s ... -> e, es, ss / <- e, ee, se` -/
def KK : HandshakePattern := mk "KK" [.s] [.s] [[.e, .es, .ss], [.e, .ee, .se]]

/-- `KX: -> s ... -> e / <- e, ee, se, s, es` -/
def KX : HandshakePattern := mk "KX" [.s] [] [[.e], [.e, .ee, .se, .s, .es]]

/-- `IN: -> e, s / <- e, ee, se` -/
def IN : HandshakePattern := mk "IN" [] [] [[.e, .s], [.e, .ee, .se]]

/-- `IK: <- s ... -> e, es, s, ss / <- e, ee, se` -/
def IK : HandshakePattern := mk "IK" [] [.s] [[.e, .es, .s, .ss], [.e, .ee, .se]]

/-- `IX: -> e, s / <- e, ee, se, s, es` -/
def IX : HandshakePattern := mk "IX" [] [] [[.e, .s], [.e, .ee, .se, .s, .es]]

/-! ## Deferred patterns (spec §18.1)

> To name these deferred handshake patterns, the numeral "1" is used after the
> first and/or second character in a fundamental pattern name to indicate that
> the initiator and/or responder's authentication DH is deferred to the next
> message.
-/

/-- `NK1: <- s ... -> e / <- e, ee, es` -/
def NK1 : HandshakePattern := mk "NK1" [] [.s] [[.e], [.e, .ee, .es]]

/-- `NX1: -> e / <- e, ee, s / -> es` -/
def NX1 : HandshakePattern := mk "NX1" [] [] [[.e], [.e, .ee, .s], [.es]]

/-- `X1N: -> e / <- e, ee / -> s / <- se` -/
def X1N : HandshakePattern := mk "X1N" [] [] [[.e], [.e, .ee], [.s], [.se]]

/-- `X1K: <- s ... -> e, es / <- e, ee / -> s / <- se` -/
def X1K : HandshakePattern := mk "X1K" [] [.s] [[.e, .es], [.e, .ee], [.s], [.se]]

/-- `XK1: <- s ... -> e / <- e, ee, es / -> s, se` -/
def XK1 : HandshakePattern := mk "XK1" [] [.s] [[.e], [.e, .ee, .es], [.s, .se]]

/-- `X1K1: <- s ... -> e / <- e, ee, es / -> s / <- se` -/
def X1K1 : HandshakePattern := mk "X1K1" [] [.s] [[.e], [.e, .ee, .es], [.s], [.se]]

/-- `X1X: -> e / <- e, ee, s, es / -> s / <- se` -/
def X1X : HandshakePattern := mk "X1X" [] [] [[.e], [.e, .ee, .s, .es], [.s], [.se]]

/-- `XX1: -> e / <- e, ee, s / -> es, s, se` -/
def XX1 : HandshakePattern := mk "XX1" [] [] [[.e], [.e, .ee, .s], [.es, .s, .se]]

/-- `X1X1: -> e / <- e, ee, s / -> es, s / <- se` -/
def X1X1 : HandshakePattern := mk "X1X1" [] [] [[.e], [.e, .ee, .s], [.es, .s], [.se]]

/-- `K1N: -> s ... -> e / <- e, ee / -> se` -/
def K1N : HandshakePattern := mk "K1N" [.s] [] [[.e], [.e, .ee], [.se]]

/-- `K1K: -> s <- s ... -> e, es / <- e, ee / -> se` -/
def K1K : HandshakePattern := mk "K1K" [.s] [.s] [[.e, .es], [.e, .ee], [.se]]

/-- `KK1: -> s <- s ... -> e / <- e, ee, se, es` -/
def KK1 : HandshakePattern := mk "KK1" [.s] [.s] [[.e], [.e, .ee, .se, .es]]

/-- `K1K1: -> s <- s ... -> e / <- e, ee, es / -> se` -/
def K1K1 : HandshakePattern := mk "K1K1" [.s] [.s] [[.e], [.e, .ee, .es], [.se]]

/-- `K1X: -> s ... -> e / <- e, ee, s, es / -> se` -/
def K1X : HandshakePattern := mk "K1X" [.s] [] [[.e], [.e, .ee, .s, .es], [.se]]

/-- `KX1: -> s ... -> e / <- e, ee, se, s / -> es` -/
def KX1 : HandshakePattern := mk "KX1" [.s] [] [[.e], [.e, .ee, .se, .s], [.es]]

/-- `K1X1: -> s ... -> e / <- e, ee, s / -> se, es` -/
def K1X1 : HandshakePattern := mk "K1X1" [.s] [] [[.e], [.e, .ee, .s], [.se, .es]]

/-- `I1N: -> e, s / <- e, ee / -> se` -/
def I1N : HandshakePattern := mk "I1N" [] [] [[.e, .s], [.e, .ee], [.se]]

/-- `I1K: <- s ... -> e, es, s / <- e, ee / -> se` -/
def I1K : HandshakePattern := mk "I1K" [] [.s] [[.e, .es, .s], [.e, .ee], [.se]]

/-- `IK1: <- s ... -> e, s / <- e, ee, se, es` -/
def IK1 : HandshakePattern := mk "IK1" [] [.s] [[.e, .s], [.e, .ee, .se, .es]]

/-- `I1K1: <- s ... -> e, s / <- e, ee, es / -> se` -/
def I1K1 : HandshakePattern := mk "I1K1" [] [.s] [[.e, .s], [.e, .ee, .es], [.se]]

/-- `I1X: -> e, s / <- e, ee, s, es / -> se` -/
def I1X : HandshakePattern := mk "I1X" [] [] [[.e, .s], [.e, .ee, .s, .es], [.se]]

/-- `IX1: -> e, s / <- e, ee, se, s / -> es` -/
def IX1 : HandshakePattern := mk "IX1" [] [] [[.e, .s], [.e, .ee, .se, .s], [.es]]

/-- `I1X1: -> e, s / <- e, ee, s / -> se, es` -/
def I1X1 : HandshakePattern := mk "I1X1" [] [] [[.e, .s], [.e, .ee, .s], [.se, .es]]

/-! ## Recommended PSK patterns (spec §9.4)

> The modifier `psk0` places a `"psk"` token at the beginning of the first
> handshake message.  The modifiers `psk1`, `psk2`, etc., place a `"psk"` token
> at the end of the first, second, etc., handshake message.
-/

/-- `Npsk0: <- s ... -> psk, e, es` -/
def Npsk0 : HandshakePattern := mk "Npsk0" [] [.s] [[.psk, .e, .es]]

/-- `Kpsk0: -> s <- s ... -> psk, e, es, ss` -/
def Kpsk0 : HandshakePattern := mk "Kpsk0" [.s] [.s] [[.psk, .e, .es, .ss]]

/-- `Xpsk1: <- s ... -> e, es, s, ss, psk` -/
def Xpsk1 : HandshakePattern := mk "Xpsk1" [] [.s] [[.e, .es, .s, .ss, .psk]]

/-- `NNpsk0: -> psk, e / <- e, ee` -/
def NNpsk0 : HandshakePattern := mk "NNpsk0" [] [] [[.psk, .e], [.e, .ee]]

/-- `NNpsk2: -> e / <- e, ee, psk` -/
def NNpsk2 : HandshakePattern := mk "NNpsk2" [] [] [[.e], [.e, .ee, .psk]]

/-- `NKpsk0: <- s ... -> psk, e, es / <- e, ee` -/
def NKpsk0 : HandshakePattern := mk "NKpsk0" [] [.s] [[.psk, .e, .es], [.e, .ee]]

/-- `NKpsk2: <- s ... -> e, es / <- e, ee, psk` -/
def NKpsk2 : HandshakePattern := mk "NKpsk2" [] [.s] [[.e, .es], [.e, .ee, .psk]]

/-- `NXpsk2: -> e / <- e, ee, s, es, psk` -/
def NXpsk2 : HandshakePattern := mk "NXpsk2" [] [] [[.e], [.e, .ee, .s, .es, .psk]]

/-- `XNpsk3: -> e / <- e, ee / -> s, se, psk` -/
def XNpsk3 : HandshakePattern := mk "XNpsk3" [] [] [[.e], [.e, .ee], [.s, .se, .psk]]

/-- `XKpsk3: <- s ... -> e, es / <- e, ee / -> s, se, psk` -/
def XKpsk3 : HandshakePattern :=
  mk "XKpsk3" [] [.s] [[.e, .es], [.e, .ee], [.s, .se, .psk]]

/-- `XXpsk3: -> e / <- e, ee, s, es / -> s, se, psk` -/
def XXpsk3 : HandshakePattern :=
  mk "XXpsk3" [] [] [[.e], [.e, .ee, .s, .es], [.s, .se, .psk]]

/-- `KNpsk0: -> s ... -> psk, e / <- e, ee, se` -/
def KNpsk0 : HandshakePattern := mk "KNpsk0" [.s] [] [[.psk, .e], [.e, .ee, .se]]

/-- `KNpsk2: -> s ... -> e / <- e, ee, se, psk` -/
def KNpsk2 : HandshakePattern := mk "KNpsk2" [.s] [] [[.e], [.e, .ee, .se, .psk]]

/-- `KKpsk0: -> s <- s ... -> psk, e, es, ss / <- e, ee, se` -/
def KKpsk0 : HandshakePattern :=
  mk "KKpsk0" [.s] [.s] [[.psk, .e, .es, .ss], [.e, .ee, .se]]

/-- `KKpsk2: -> s <- s ... -> e, es, ss / <- e, ee, se, psk` -/
def KKpsk2 : HandshakePattern :=
  mk "KKpsk2" [.s] [.s] [[.e, .es, .ss], [.e, .ee, .se, .psk]]

/-- `KXpsk2: -> s ... -> e / <- e, ee, se, s, es, psk` -/
def KXpsk2 : HandshakePattern :=
  mk "KXpsk2" [.s] [] [[.e], [.e, .ee, .se, .s, .es, .psk]]

/-- `INpsk1: -> e, s, psk / <- e, ee, se` -/
def INpsk1 : HandshakePattern := mk "INpsk1" [] [] [[.e, .s, .psk], [.e, .ee, .se]]

/-- `INpsk2: -> e, s / <- e, ee, se, psk` -/
def INpsk2 : HandshakePattern := mk "INpsk2" [] [] [[.e, .s], [.e, .ee, .se, .psk]]

/-- `IKpsk1: <- s ... -> e, es, s, ss, psk / <- e, ee, se` -/
def IKpsk1 : HandshakePattern :=
  mk "IKpsk1" [] [.s] [[.e, .es, .s, .ss, .psk], [.e, .ee, .se]]

/-- `IKpsk2: <- s ... -> e, es, s, ss / <- e, ee, se, psk` -/
def IKpsk2 : HandshakePattern :=
  mk "IKpsk2" [] [.s] [[.e, .es, .s, .ss], [.e, .ee, .se, .psk]]

/-- `IXpsk2: -> e, s / <- e, ee, se, s, es, psk` -/
def IXpsk2 : HandshakePattern :=
  mk "IXpsk2" [] [] [[.e, .s], [.e, .ee, .se, .s, .es, .psk]]

/-! ## Compound protocols (spec §10) -/

/-- `XXfallback` (spec §10.2), in canonical initiator-first form.

The spec prints it in Bob-initiated form:
```
XXfallback:
  -> e
  ...
  <- e, ee, s, es
  -> s, se
```
Converting to canonical form reverses the arrows and swaps `es` with `se`
(spec §7.2), so Alice's pre-message ephemeral becomes the *responder's*
pre-message and the two messages become `-> e, ee, s, se` and `<- s, es`. -/
def XXfallback : HandshakePattern :=
  mk "XXfallback" [] [.e] [[.e, .ee, .s, .se], [.s, .es]]

/-! ## A deliberately invalid pattern -/

/-- `KXS: -> s ... -> e / <- e, ee, s, ss`.

This is the pattern analysed in §6 of the Noise Explorer paper: a variant of
`KX` that uses `ss` in place of `se` and `es`.  It is rejected by spec §7.3
rule 4, and the paper exhibits a concrete man-in-the-middle forgery against it
when invalid Diffie-Hellman public values are not rejected. -/
def KXS : HandshakePattern := mk "KXS" [.s] [] [[.e], [.e, .ee, .s, .ss]]

/-! ## Collections -/

/-- The one-way handshake patterns (spec §7.4). -/
def oneWay : List HandshakePattern := [N, K, X]

/-- The twelve fundamental interactive handshake patterns (spec §7.5). -/
def fundamental : List HandshakePattern :=
  [NN, NK, NX, XN, XK, XX, KN, KK, KX, IN, IK, IX]

/-- The twenty-three deferred handshake patterns (spec §18.1). -/
def deferred : List HandshakePattern :=
  [NK1, NX1, X1N, X1K, XK1, X1K1, X1X, XX1, X1X1,
   K1N, K1K, KK1, K1K1, K1X, KX1, K1X1,
   I1N, I1K, IK1, I1K1, I1X, IX1, I1X1]

/-- The twenty-one recommended PSK handshake patterns (spec §9.4). -/
def psk : List HandshakePattern :=
  [Npsk0, Kpsk0, Xpsk1, NNpsk0, NNpsk2, NKpsk0, NKpsk2, NXpsk2,
   XNpsk3, XKpsk3, XXpsk3, KNpsk0, KNpsk2, KKpsk0, KKpsk2, KXpsk2,
   INpsk1, INpsk2, IKpsk1, IKpsk2, IXpsk2]

/-- Every handshake pattern named in the specification. -/
def all : List HandshakePattern := oneWay ++ fundamental ++ deferred ++ psk ++ [XXfallback]

end Patterns
end Noise
