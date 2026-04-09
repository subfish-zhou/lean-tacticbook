import Lake

open System Lake DSL

package «lean-auto-book» where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require verso from git "https://github.com/leanprover/verso.git"@"v4.30.0-rc1"

@[default_target]
lean_lib LeanAutoBook where
  srcDir := "."

lean_exe «lean-auto-book» where
  root := `Main
