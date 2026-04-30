import Lake
open Lake DSL

package ZcashFormal where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib ZcashFormal where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
