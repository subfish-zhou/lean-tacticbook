import Lake
open Lake DSL

require subverso from git "https://github.com/leanprover/subverso.git"@"main"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"master"

package examples where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib Examples
