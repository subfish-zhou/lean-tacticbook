import Lake

open System Lake DSL

package «lean-auto-book» where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require verso from git "https://github.com/leanprover/verso.git"@"v4.30.0-rc1"

private def examplePath : System.FilePath := "../examples"

private def lakeVars :=
  #["LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP",
    "LEAN_SYSROOT", "LEAN_AR", "LEAN_PATH", "LEAN_SRC_PATH",
    "LEAN_GITHASH",
    "ELAN_TOOLCHAIN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"]

input_dir examples where
  path := examplePath
  text := true
  filter := .extension "lean"

target buildExamples (pkg) : Unit := do
  let exs ← examples.fetch
  exs.mapM fun exFiles => do
    let mut list := ""
    for file in exFiles do
      addTrace (← computeTrace <| TextFilePath.mk file)
      list := list ++ s!"{file}\n"
    buildFileUnlessUpToDate' (pkg.buildDir / "examples-built") (text := true) do
      Lake.logInfo s!"Building examples in {examplePath}"
      let out ← captureProc {
        cmd := "lake",
        args := #["build"],
        cwd := examplePath,
        env := lakeVars.map (·, none)
      }
      IO.FS.createDirAll pkg.buildDir
      IO.FS.writeFile (pkg.buildDir / "examples-built") (list ++ "--- Output ---\n" ++ out)

target syncBuildExamples : Unit := do
  .pure <$> (← buildExamples.fetch).await

@[default_target]
lean_lib LeanAutoBook where
  srcDir := "."
  needs := #[syncBuildExamples]

lean_exe «lean-auto-book» where
  root := `Main
