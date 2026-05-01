import Lake
open Lake DSL

package Pasta where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib Pasta where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
