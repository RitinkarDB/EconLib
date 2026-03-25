import Lake
open Lake DSL

package EconLib where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.28.0"

@[default_target]
lean_lib EconLib where
  roots := #[`EconLib]
