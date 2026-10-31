import Lake

open Lake DSL

/-
OSSV-265 slice K1: `libreac/fuzz_knock`'s `plain_halts` on the Lean twin of
rocq-linux-process-semantics `f1006fe8`.

The dependency is the twin, `lean/` at the root of this repository (OSSV-265
scale-up design, slice Z1), three directories up. Until Z1 merges, make `lean/`
a symbolic link to the `lean/` of a checkout of
theorem-labs/linux-process-semantics
`ff0313ba4f2e9baffcf5b5f50bc9d31628ae8556`, which is the same content.
-/
require LinuxProcessSemantics from "../../../lean"

package OssFuzzTheorems where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]
  moreLeanArgs := #["-j2"]

@[default_target]
lean_lib OssFuzzTheorems where
  globs := #[.andSubmodules `OssFuzzTheorems]
