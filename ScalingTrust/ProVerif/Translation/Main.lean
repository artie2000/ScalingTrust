/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import ScalingTrust.ProVerif.Translation.Emit

/-!
# The translator's entry point

```sh
lake env lean --run ScalingTrust/ProVerif/Translation/Main.lean Model.pv Model.lean
```

translates `Model.pv` to `Model.lean`, in a namespace named after the output
file.  It imports `ScalingTrust.ProVerif.Translation.Emit`, so that module must
have been built.
-/

open Lean ProVerif.Translation

unsafe def main (args : List String) : IO UInt32 := do
  let [input, output] := args
    | IO.eprintln "usage: lake env lean --run ScalingTrust/ProVerif/Translation/Main.lean Model.pv Model.lean"
      return 1
  let some ns := (System.FilePath.mk output).fileStem
    | IO.eprintln s!"{output}: no file name"; return 1
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules (imports := #[{module := `ScalingTrust.ProVerif.Translation.Emit}])
    (opts := {}) (loadExts := true)
  match ← translate env input (← IO.FS.readFile input) ns with
  | .ok s => IO.FS.writeFile output s; return 0
  | .error e => IO.eprintln e; return 1
