# ScalingTrust

Formal models of secure-channel protocols and of process calculi. This file is
for people and coding agents alike; it says how the repository is organised and
nothing about any one project.

## The folders under `ScalingTrust/` are independent

Each folder is a self-contained project with its own documentation, conventions
and dependencies. They share the repository, the Lean toolchain and the
lakefile, and nothing else. Do not import across folders, and do not assume
that a definition, a naming convention or a proof style from one folder applies
in another.

Before working in a folder, read its README and the module docstrings of the
files you touch, and keep them accurate when you change the code. Consult the
documentation of the other folders only when a task genuinely spans them.

| Folder | What it is | Language | Documentation |
| --- | --- | --- | --- |
| `ScalingTrust/Noise/` | The Noise Protocol Framework (Revision 34), its validity rules and a correctness proof | Lean 4 core only | `ScalingTrust/Noise/README.md` |
| `ScalingTrust/ProVerif/` | A trace-based semantics of the process calculus behind ProVerif, with the attacker and the queries | Lean 4 with Mathlib | `ScalingTrust/ProVerif/README.md`; `Reference/` there holds the papers, the manual and two Noise Explorer models, with its own README |
| `ScalingTrust/PsiCalculi/Isabelle/` | The AFP entry `Psi_Calculi` (Bengtson), kept for reference | Isabelle/HOL-Nominal | `document/root.tex` in that folder |

## Building

* The toolchain is fixed by `lean-toolchain` (`leanprover/lean4:v4.33.0`).
  Mathlib is pinned to the matching tag in `lakefile.toml`; fetch its prebuilt
  artifacts with `lake exe cache get` rather than compiling it.
* `lake build` builds the default target `ScalingTrust`, whose root module
  `ScalingTrust.lean` currently imports only the Noise modules. That is what
  CI (`.github/workflows/lean_action_ci.yml`) checks.
* The ProVerif modules are built explicitly:
  `lake build ScalingTrust.ProVerif.Examples`.
* The Isabelle theories are not built by Lake.

## Reference material

Papers, manuals and third-party models that a folder's work relies on live in a
`Reference/` subfolder of that folder, as in `ScalingTrust/ProVerif/Reference/`,
with a README saying what each file is and why it is there (PDFs get a text
extraction where that helps searching). Do not keep them in a scratch or
temporary directory.
