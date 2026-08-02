import Lake
open Lake DSL

require subverso from git "https://github.com/leanprover/subverso.git"@"0076a9e8a3670d83c54c93414b2b26d3a8aba08d"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"v4.32.2"

package examples where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib Examples
