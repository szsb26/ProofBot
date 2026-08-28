import Lake
open Lake DSL

package IMO2026 where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0"

@[default_target]
lean_lib IMO2026 where
  globs := Array.range 6 |>.map fun i ↦ .submodules <| .str `IMO2026 s!"Q{i+1}"
