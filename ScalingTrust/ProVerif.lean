/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.TraceSemantics.Process
import ScalingTrust.ProVerif.TraceSemantics.Term
import ScalingTrust.ProVerif.TraceSemantics.Data
import ScalingTrust.ProVerif.TraceSemantics.Security
import ScalingTrust.ProVerif.TraceSemantics.Query
import ScalingTrust.ProVerif.TraceSemantics.Attack
import ScalingTrust.ProVerif.TraceSemantics.Examples.DenningSacco
import ScalingTrust.ProVerif.TraceSemantics.Examples.NoiseNN
import ScalingTrust.ProVerif.Translation.Model
import ScalingTrust.ProVerif.Translation.Parser
import ScalingTrust.ProVerif.Translation.Compile
import ScalingTrust.ProVerif.Translation.Emit
import ScalingTrust.ProVerif.Translation.Main
import ScalingTrust.ProVerif.Translation.Examples.DenningSacco
import ScalingTrust.ProVerif.Translation.Examples.Features
import ScalingTrust.ProVerif.Translation.Examples.NN
import ScalingTrust.ProVerif.Translation.Examples.XX
import ScalingTrust.ProVerif.TamarinTranslation.Rewriting
import ScalingTrust.ProVerif.TamarinTranslation.Model
import ScalingTrust.ProVerif.TamarinTranslation.Parser
import ScalingTrust.ProVerif.TamarinTranslation.Emit
import ScalingTrust.ProVerif.TamarinTranslation.Examples.FirstExample
import ScalingTrust.ProVerif.TamarinTranslation.Examples.Fragment
import ScalingTrust.ProVerif.Specification.Syntax
import ScalingTrust.ProVerif.Specification.Patterns
import ScalingTrust.ProVerif.Specification.Semantics
import ScalingTrust.ProVerif.Specification.Invariance
import ScalingTrust.ProVerif.Specification.Denotation
import ScalingTrust.ProVerif.Specification.Adequacy
import ScalingTrust.ProVerif.Specification.Attacks
import ScalingTrust.ProVerif.Specification.Correspondence

/-!
# ProVerif in Lean

Every module of `ScalingTrust/ProVerif/`, by subfolder, but
`TamarinTranslation.Main`, whose `main` would clash with that of
`Translation.Main`; it is compiled whenever the Tamarin translator runs. The
README there says what the subfolders are and how they fit together.
-/
