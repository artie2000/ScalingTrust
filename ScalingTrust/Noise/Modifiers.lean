/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.Noise.PatternsValid

/-!
# Protocol names and pattern modifiers

Spec §8 fixes the shape of a protocol name; §9.4 defines the `pskN` modifiers;
§10.2 defines the `fallback` modifier.  This file implements all three and
checks them against the tables the specification prints.

Spec §8:

> To produce a Noise protocol name for `Initialize()` you concatenate the ASCII
> string `"Noise_"` with four underscore-separated name sections which
> sequentially name the handshake pattern, the DH functions, the cipher
> functions, and then the hash functions.  The resulting name must be 255 bytes
> or less.
-/

namespace Noise

/-! ## Protocol names (spec §8) -/

/-- Spec §8.2: "Each algorithm name must consist solely of alphanumeric
characters and the forward-slash character." -/
def isAlgorithmName (s : String) : Bool :=
  s ≠ "" && s.toList.all (fun c => c.isAlphanum || c = '/')

/-- Split a character list at every occurrence of `sep`, keeping empty groups.
Used instead of `String.splitOn`, which the kernel cannot evaluate. -/
def splitOnChar (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
      if c = sep then [] :: splitOnChar sep cs
      else match splitOnChar sep cs with
        | [] => [[c]]
        | g :: gs => (c :: g) :: gs

/-- Spec §8.2: "Each name section must contain one or more algorithm names
separated by plus signs." -/
def isAlgorithmSection (s : String) : Bool :=
  (splitOnChar '+' s.toList).all
    (fun g => g ≠ [] && g.all (fun c => c.isAlphanum || c = '/'))

/-- Spec §8.1: "The handshake pattern name must be an uppercase ASCII string
containing only alphabetic characters or numerals." -/
def isBasePatternName (s : String) : Bool :=
  s ≠ "" && s.toList.all (fun c => (c.isUpper && c.isAlpha) || c.isDigit)

/-- Spec §8.1: "A pattern modifier is named with a lowercase alphanumeric ASCII
string which must begin with an alphabetic character (not a numeral)." -/
def isModifierName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => c.isLower && c.isAlpha && cs.all (fun c => (c.isLower && c.isAlpha) || c.isDigit)

/-- Spec §8.1:

> The first modifier added onto a base pattern is simply appended.  Thus the
> `"fallback"` modifier, when added to the `"XX"` pattern, produces
> `"XXfallback"`.  Additional modifiers are separated with a plus sign. -/
def patternNameSection (base : String) (modifiers : List String) : String :=
  match modifiers with
  | [] => base
  | m :: ms => base ++ m ++ ms.foldl (fun acc x => acc ++ "+" ++ x) ""

/-- Spec §8: the full protocol name. -/
def protocolName (patternSection dhName cipherName hashName : String) : String :=
  "Noise_" ++ patternSection ++ "_" ++ dhName ++ "_" ++ cipherName ++ "_" ++ hashName

/-- Spec §8: "The resulting name must be 255 bytes or less." -/
def protocolNameWellFormed (patternSection dhName cipherName hashName : String) : Bool :=
  (protocolName patternSection dhName cipherName hashName).length ≤ 255 &&
  isAlgorithmSection dhName && isAlgorithmSection cipherName && isAlgorithmSection hashName

/-! The three examples the specification gives in §8. -/

example : protocolName "XX" "25519" "AESGCM" "SHA256" = "Noise_XX_25519_AESGCM_SHA256" := by
  decide

example : protocolName "N" "25519" "ChaChaPoly" "BLAKE2s" = "Noise_N_25519_ChaChaPoly_BLAKE2s" := by
  decide

example : protocolName "IK" "448" "ChaChaPoly" "BLAKE2b" = "Noise_IK_448_ChaChaPoly_BLAKE2b" := by
  decide

/-- Spec §8.1's own example of modifier composition. -/
example : patternNameSection "XX" ["fallback"] = "XXfallback" := by decide

/-- Spec §8.1: "adding the `psk0` modifier would result in the name section
`XXfallback+psk0`". -/
example : patternNameSection "XX" ["fallback", "psk0"] = "XXfallback+psk0" := by decide

example : protocolName (patternNameSection "XX" ["fallback", "psk0"]) "25519" "AESGCM" "SHA256"
    = "Noise_XXfallback+psk0_25519_AESGCM_SHA256" := by decide

example : isBasePatternName "XX1" = true := by decide
example : isBasePatternName "IK" = true := by decide
example : isModifierName "psk0" = true := by decide
example : isModifierName "fallback" = true := by decide
example : isModifierName "0psk" = false := by decide
example : isAlgorithmName "SHA3/256" = true := by decide

/-- Every pattern the specification names has a well-formed base name section
that can be used with any of the standard algorithm choices. -/
theorem all_protocol_names_wellFormed :
    ∀ hp ∈ Patterns.oneWay ++ Patterns.fundamental ++ Patterns.deferred,
      protocolNameWellFormed hp.name "25519" "ChaChaPoly" "SHA256" = true := by
  decide

/-! ## The `pskN` modifiers (spec §9.4)

> The modifier `psk0` places a `"psk"` token at the beginning of the first
> handshake message.  The modifiers `psk1`, `psk2`, etc., place a `"psk"` token
> at the end of the first, second, etc., handshake message.
-/

/-- Place a `psk` token as the `pskN` modifier prescribes, without renaming. -/
def pskPlace (n : Nat) (hp : HandshakePattern) : HandshakePattern :=
  { hp with
    messages :=
      if n = 0 then
        match hp.messages with
        | [] => []
        | m :: ms => (Token.psk :: m) :: ms
      else
        hp.messages.mapIdx (fun i m => if i + 1 = n then m ++ [Token.psk] else m) }

/-- Apply a sequence of `pskN` modifiers, naming the result as spec §8.1
requires. -/
def pskModifiers (ns : List Nat) (hp : HandshakePattern) : HandshakePattern :=
  { ns.foldl (fun p n => pskPlace n p) hp with
    name := patternNameSection hp.name (ns.map (fun n => "psk" ++ Nat.repr n)) }

/-- Apply a single `pskN` modifier. -/
def pskModifier (n : Nat) (hp : HandshakePattern) : HandshakePattern := pskModifiers [n] hp

namespace Patterns

/-- The table of §9.4: an unmodified pattern on the left, the modifier index,
and the recommended PSK pattern on the right. -/
def pskTable : List (Nat × HandshakePattern × HandshakePattern) :=
  [ (0, N, Npsk0), (0, K, Kpsk0), (1, X, Xpsk1),
    (0, NN, NNpsk0), (2, NN, NNpsk2),
    (0, NK, NKpsk0), (2, NK, NKpsk2),
    (2, NX, NXpsk2),
    (3, XN, XNpsk3), (3, XK, XKpsk3), (3, XX, XXpsk3),
    (0, KN, KNpsk0), (2, KN, KNpsk2),
    (0, KK, KKpsk0), (2, KK, KKpsk2),
    (2, KX, KXpsk2),
    (1, IN, INpsk1), (2, IN, INpsk2),
    (1, IK, IKpsk1), (2, IK, IKpsk2),
    (2, IX, IXpsk2) ]

/-- **The `pskN` modifiers generate the recommended PSK patterns of §9.4**,
names included. -/
theorem pskTable_correct : ∀ e ∈ pskTable, pskModifier e.1 e.2.1 = e.2.2 := by decide

theorem pskTable_length : pskTable.length = 21 := by decide

/-- Spec §9.4 notes that other combinations are legitimate even though the table
does not list them, and names `XXpsk0+psk3` as an example. -/
theorem XXpsk0psk3_derived : pskModifiers [0, 3] XX = XXpsk0psk3 := by decide

/-- Applying a `pskN` modifier to a valid pattern, for any placement the
specification allows (`psk0` through `pskN` where `N` is the number of
messages), always yields a valid pattern.  This is the formal content of spec
§9.4's remark that "any of these PSK modifiers can be safely applied to any
previously named pattern". -/
theorem psk_modifiers_preserve_validity :
    ∀ hp ∈ oneWay ++ fundamental ++ deferred,
      ∀ n ∈ List.range (hp.messages.length + 1), (pskModifier n hp).isValid = true := by
  decide

/-! ## The `fallback` modifier (spec §10.2) -/

end Patterns

/-- Reverse the roles in a DH token: `es` becomes `se` and vice versa, while
`ee` and `ss` are unchanged (spec §7.2). -/
def Token.reverse : Token → Token
  | .dh a b => .dh b a
  | t => t

/-- Reverse the roles throughout a message pattern. -/
def MessagePattern.reverse (m : MessagePattern) : MessagePattern := m.map Token.reverse

/-- Can a message pattern be reinterpreted as a pre-message?  Spec §10.2:
"fallback can only be applied to handshake patterns in Alice-initiated form
where Alice's first message is capable of being interpreted as a pre-message
(i.e. it must be either `"e"`, `"s"`, or `"e, s"`)." -/
def MessagePattern.asPreMessage (m : MessagePattern) : Option PreMessagePattern :=
  let ks := m.filterMap (fun t => match t with | .key k => some k | _ => none)
  if m.length = ks.length && PreMessagePattern.isWellFormed ks then some ks else none

/-- **The `fallback` modifier** (spec §10.2).

> The fallback modifier converts an Alice-initiated pattern to a Bob-initiated
> pattern by converting Alice's initial message to a pre-message that Bob must
> receive through some other means.  After this conversion, the rest of the
> handshake pattern is interpreted as a Bob-initiated handshake pattern.

We store patterns in canonical (initiator-first) form, so the conversion to
Bob-initiated form is carried out here: the roles are exchanged, which swaps the
two pre-messages and reverses every DH token (spec §7.2). -/
def HandshakePattern.fallback (hp : HandshakePattern) : Option HandshakePattern :=
  match hp.messages with
  | [] => none
  | m :: rest =>
      match m.asPreMessage with
      | none => none
      | some ks =>
          some { name := patternNameSection hp.name ["fallback"]
                 initiatorPre := hp.responderPre
                 responderPre := hp.initiatorPre ++ ks
                 messages := rest.map MessagePattern.reverse }

namespace Patterns

/-- **`XXfallback` is the `fallback` modifier applied to `XX`** (spec §10.2). -/
theorem XXfallback_eq : XX.fallback = some XXfallback := by decide

/-- `fallback` cannot be applied to a pattern whose first message is not a
pre-message (spec §10.2). -/
theorem NK_fallback_none : NK.fallback = none := by decide

/-- The Noise Pipe compound protocol of §10.4 consists of a full handshake, a
zero-RTT handshake, and a switch handshake. -/
def noisePipes : HandshakePattern × HandshakePattern × HandshakePattern := (XX, IK, XXfallback)

/-- All three components of a Noise Pipe are valid patterns. -/
theorem noisePipes_valid :
    noisePipes.1.isValid = true ∧ noisePipes.2.1.isValid = true ∧
      noisePipes.2.2.isValid = true := by decide

end Patterns
end Noise
