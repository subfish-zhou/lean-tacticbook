import VersoManual
import SubVerso.Highlighting

open Verso Doc Elab Genre.Manual ArgParse Code Highlighted
open Verso Code External
open SubVerso.Highlighting
open Lean

/-- Inline keyword role: renders tactic/keyword names with keyword highlighting. -/
@[role_expander kw]
def kw : RoleExpander
  | args, inls => do
    ArgParse.done.run args
    let kw ← oneCodeStr inls
    let hl : Highlighted := .token ⟨.keyword none none none, kw.getString⟩
    return #[← ``(Inline.other (Inline.lean $(quote hl) {}) #[Inline.code $(quote kw.getString)])]

/-! ## SubVerso Helper for inline Lean elaboration

The `{lean}` role sends code to a SubVerso helper subprocess running in the
`examples/` project environment, which elaborates and highlights it with real
type information.
-/

open System in
open SubVerso.Helper in

private def projectDir : System.FilePath := "../examples/"

private def alphabet := "abcdefghijklmnopqrstuvwxyz0123456789"

private def hashString (n : UInt64) : String := Id.run do
  let mut n : Nat := n.toNat
  let mut out : String := "Example"
  while n > 0 do
    out := out.push ({ byteIdx := n % 36 : String.Pos.Raw} |>.get! alphabet)
    n := n / 36
  return out

structure Helper where
  highlight (term : String) (type? : Option String) : IO Highlighted
  command (cmd : String) : IO Highlighted
  signature (code : String) : IO Highlighted
  name (code : String) : IO Highlighted

open System SubVerso.Helper in
def Helper.fromModule (setup : String) : IO Helper := do
  let codeHash := hash setup
  let modBase := "Interact" ++ hashString codeHash
  let filename := modBase ++ ".lean"
  let mod := "Examples." ++ modBase

  -- Validate project
  let lakefile := projectDir / "lakefile.lean"
  let lakefile' := projectDir / "lakefile.toml"
  if !(← lakefile.pathExists) && !(← lakefile'.pathExists) then
    throw <| .userError s!"Neither {lakefile} nor {lakefile'} exist, couldn't load project"
  let toolchainfile := projectDir / "lean-toolchain"
  let toolchain ← do
    if !(← toolchainfile.pathExists) then
      throw <| .userError s!"File {toolchainfile} doesn't exist, couldn't load project"
    pure (← IO.FS.readFile toolchainfile).trimAscii.copy

  IO.FS.writeFile (projectDir / "Examples" / filename) setup

  let lakeVars :=
    #["LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP",
      "LEAN_SYSROOT", "LEAN_AR", "LEAN_PATH", "LEAN_SRC_PATH",
      "LEAN_GITHASH",
      "ELAN_TOOLCHAIN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"]

  let cmd := "elan"

  -- Build subverso-helper
  let toolchainFile ← IO.FS.Handle.mk toolchainfile .read
  toolchainFile.lock (exclusive := true)
  try
    let args := #["run", "--install", toolchain, "lake", "build", "subverso-helper"]
    let res ← IO.Process.output {
      cmd, args, cwd := projectDir
      env := lakeVars.map (·, none)
    }
    if res.exitCode != 0 then reportFail projectDir cmd args res
  finally
    toolchainFile.unlock

  -- Start helper subprocess
  let setupFile ← IO.FS.Handle.mk (projectDir / "Examples" / filename) .read
  setupFile.lock (exclusive := true)
  try
    let args := #["run", "--install", toolchain, "lake", "env", "subverso-helper", mod]
    let (hlTm, hlCmd, hlSig, hlName) ← do
      let (procIn, proc) ← do
        let proc ← IO.Process.spawn {
          cmd, args, cwd := projectDir
          env := lakeVars.map (·, none)
          stdin := .piped
          stdout := .piped
          stderr := .inherit
        }
        proc.takeStdin
      let mutex ← Std.Mutex.new (IO.FS.Stream.ofHandle procIn, IO.FS.Stream.ofHandle proc.stdout)
      let hlTm := fun (tm : String) (ty? : Option String) => show IO Highlighted from do
        mutex.atomically do
          let (procIn, procOut) ← get
          if let some code ← proc.tryWait then
            throw <| .userError s!"Process terminated: {code}"
          send procIn (Request.term tm ty?)
          match (← receiveThe Response procOut) with
          | some (.result (.highlighted hl)) => pure hl
          | some (.error code e more) =>
            let mut msg := s!"{e} ({code})."
            if let some details := more then
              msg := msg ++ s!" Details:\n  {details}"
            throw <| .userError msg
          | none => throw <| .userError "Helper process no longer running"
      let hlCmd := fun (cmd : String) => show IO Highlighted from do
        mutex.atomically do
          let (procIn, procOut) ← get
          if let some code ← proc.tryWait then
            throw <| .userError s!"Process terminated: {code}"
          send procIn (Request.command cmd)
          match (← receiveThe Response procOut) with
          | some (.result (.highlighted hl)) => pure hl
          | some (.error code e more) =>
            let mut msg := s!"{e} ({code})."
            if let some details := more then
              msg := msg ++ s!" Details:\n  {details}"
            throw <| .userError msg
          | none => throw <| .userError "Helper process no longer running"
      let hlSig := fun (cmd : String) => show IO Highlighted from do
        mutex.atomically do
          let (procIn, procOut) ← get
          if let some code ← proc.tryWait then
            throw <| .userError s!"Process terminated: {code}"
          send procIn (Request.signature cmd)
          match (← receiveThe Response procOut) with
          | some (.result (.highlighted hl)) => pure hl
          | some (.error code e more) =>
            let mut msg := s!"{e} ({code})."
            if let some details := more then
              msg := msg ++ s!" Details:\n  {details}"
            throw <| .userError msg
          | none => throw <| .userError "Helper process no longer running"
      let hlName := fun (cmd : String) => show IO Highlighted from do
        mutex.atomically do
          let (procIn, procOut) ← get
          if let some code ← proc.tryWait then
            throw <| .userError s!"Process terminated: {code}"
          send procIn (Request.name cmd)
          match (← receiveThe Response procOut) with
          | some (.result (.highlighted hl)) => pure hl
          | some (.error code e more) =>
            let mut msg := s!"{e} ({code})."
            if let some details := more then
              msg := msg ++ s!" Details:\n  {details}"
            throw <| .userError msg
          | none => throw <| .userError "Helper process no longer running"
      pure (hlTm, hlCmd, hlSig, hlName)

    return Helper.mk hlTm hlCmd hlSig hlName
  finally
    setupFile.unlock
where
  decorateOut (name : String) (out : String) : String :=
    if out.isEmpty then "" else s!"\n{name}:\n{out}\n"

  reportFail {α} (projectDir : FilePath) (cmd : String) (args : Array String) (res : IO.Process.Output) : IO α := do
    IO.eprintln <|
      "Build process failed." ++
      "\nCWD: " ++ projectDir.toString ++
      "\nCommand: " ++ cmd ++
      "\nArgs: " ++ repr args ++
      "\nExit code: " ++ toString res.exitCode ++
      "\nstdout: " ++ res.stdout ++
      "\nstderr: " ++ res.stderr

    throw <| .userError <|
      "Build process failed." ++
      decorateOut "stdout" res.stdout ++
      decorateOut "stderr" res.stderr

initialize helperExt : EnvExtension (Option Helper) ←
  registerEnvExtension (pure none)

initialize defaultHelperExt : EnvExtension (Option Helper) ←
  registerEnvExtension (pure none)

/-- The `setup` code block expander sets up a default Helper that persists
across the rest of the document. Usage in Verso:
````
```setup
import Mathlib.Tactic
open Lean Elab Tactic Meta
```
````
-/
@[code_block_expander setup]
def setup : CodeBlockExpander
  | args, code => do
    ArgParse.done.run args
    let helper ← Helper.fromModule code.getString
    modifyEnv fun env => defaultHelperExt.setState env (some helper)
    return #[]

def currentHelper : DocElabM Helper := do
  if let some h := helperExt.getState (← getEnv) then pure h
  else if let some h := defaultHelperExt.getState (← getEnv) then pure h
  else
    -- Default setup: import Mathlib.Tactic so most inline Lean code works out of the box
    let helper ← Helper.fromModule "import Mathlib.Tactic\nopen Lean Elab Tactic Meta\n"
    modifyEnv fun env => defaultHelperExt.setState env (some helper)
    pure helper

private def multiVar? (str : String) : Option (Array String × String) := do
  let mut out := #[]
  let mut str := str.trimAscii
  repeat
    let pref1 := str.takeWhile alpha
    let length1 := pref1.positions.length
    if length1 < 1 then failure
    str := str.drop length1
    let pref2 := str.takeWhile (fun c => alpha c || c.isDigit)
    let length2 := pref2.positions.length
    str := str.drop length2
    let pref := pref1.copy ++ pref2.copy
    let c := str.startPos.get?
    if pref.length > 0 && (c.isEqSome ' ' || c.isEqSome ':') then
      out := out.push pref
      str := str.dropWhile (· == ' ')
    else failure

    if str.startPos.get? |>.isEqSome ':' then
      str := str.drop 1
      str := str.dropWhile (· == ' ')
      if str.isEmpty then failure
      return (out, str.copy)
  failure
where
  alpha c := c.isAlpha || c ∈ ['α', 'β', 'γ']

def highlightInline (code : String) (type? : Option String := none) : DocElabM Highlighted := do
  let helper ← currentHelper
  try
    if type?.isSome then throwError "failed"
    let some (vars, type) := multiVar? code
      | throwError "failed"
    let mut out : Highlighted := .empty
    for v in vars do
      out := out ++ (← helper.highlight v (some type)) ++ .text " "
    out := out ++ .text ": "
    out := out ++ (← helper.highlight type none)
    pure out
  catch e1 =>
    try
      let codeStr := "(\n" ++ code ++ "\n)"
      let hl ← helper.highlight codeStr type?
      pure (hl.lines.extract 1 (hl.lines.size - 1) |> Highlighted.seq)
    catch e2 =>
      throwError "Failed to highlight code. Errors:{indentD e1.toMessageData}\nand:{indentD e2.toMessageData}"

/-- The `{lean}` inline role elaborates Lean code in the examples project environment
and renders it with real syntax highlighting and type information. -/
@[role_expander «lean»]
def «lean» : RoleExpander
  | args, inls => do
    let type? ← ArgParse.run (.named `type .string true) args
    let code ← oneCodeStr inls
    let codeStr := code.getString

    try
      let hl ← highlightInline codeStr type?
      return #[← ``(Inline.other (Inline.lean $(quote hl) {}) #[Inline.code $(quote hl.toString)])]
    catch
      | .error refStx e =>
        logErrorAt refStx e
        return #[← ``(sorry)]
      | e => throw e
