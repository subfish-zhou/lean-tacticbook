import VersoManual
import SubVerso.Highlighting
import SubVerso.Highlighting.String

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

/-! ## Recent highlights ring buffer for leanRef support -/

-- A fixed-size ring buffer that keeps the most recent `n` values.
universe u

structure Kept (α : Type u) where
  values : Array α
  next : Nat
  in_bounds : next < values.size
deriving Repr

instance {α : Type u} [Inhabited α] : Inhabited (Kept α) where
  default := ⟨#[default], 0, by simp⟩

def Kept.add {α : Type u} (kept : Kept α) (val : α) : Kept α where
  values := kept.values.set kept.next val (h := kept.in_bounds)
  next := if kept.next = 0 then kept.values.size - 1 else kept.next - 1
  in_bounds := by
    have := kept.in_bounds
    rw [Array.size_set]
    split <;> omega

def Kept.toArray {α : Type u} [Inhabited α] (kept : Kept α) : Array α := Id.run do
  let mut out : Array α := #[]
  for i in [kept.next:kept.values.size] do
    out := out.push kept.values[i]!
  for i in [0:kept.next] do
    out := out.push kept.values[i]!
  return out

initialize recentHighlightsExt : EnvExtension (Kept Highlighted) ←
  registerEnvExtension (pure ⟨.replicate 12 .empty, 0, by simp⟩)

/-- Extracts all proof-state highlights from code for backreference indexing. -/
def allProofInfo (hl : Highlighted) : Array Highlighted :=
  go #[] hl
where
  go (acc : Array Highlighted) : Highlighted → Array Highlighted
    | .seq xs => xs.foldl (init := acc) go
    | .span _ x => go acc x
    | .tactics gs _ _ x => gs.foldl (init := (go acc x)) (fromGoal · ·)
    | .point .. | .text .. | .token .. | .unparsed .. => acc
  fromGoal (acc : Array Highlighted) (g : Highlighted.Goal Highlighted) :=
    g.hypotheses.foldl (init := acc.push g.conclusion) fun acc hyp =>
      let names : Highlighted := hyp.names.foldl (init := .empty) fun hl tok =>
        if hl.isEmpty then .token tok
        else hl ++ .text " " ++ .token tok
      acc.push (names ++ .text " " ++ .token ⟨.unknown, ":"⟩ ++ .text " " ++ hyp.typeAndVal)

/-- Saves a highlighted expression into the recent-highlights ring buffer. -/
def saveBackref (hl : Highlighted) : DocElabM Unit := do
  let hl := allProofInfo hl |>.foldl (init := hl) (· ++ .text "\n" ++ ·)
  modifyEnv (recentHighlightsExt.modifyState · (·.add hl))

/-- Extracts all messages from highlighted code. -/
def allInfo (hl : Highlighted) : Array (Highlighted.Message × Option Highlighted) :=
  match hl with
  | .seq xs => xs.flatMap allInfo
  | .point k str => #[(⟨k, str⟩, none)]
  | .tactics _ _ _ x => allInfo x
  | .span infos x => (infos.map fun (k, str) => (⟨k, str⟩, some x)) ++ allInfo x
  | .text .. | .token .. | .unparsed .. => #[]

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
      saveBackref hl
      return #[← ``(Inline.other (Inline.lean $(quote hl) {}) #[Inline.code $(quote hl.toString)])]
    catch
      | .error refStx e =>
        logErrorAt refStx e
        return #[← ``(sorry)]
      | e => throw e

/-! ## Feature 1: signature code block -/

def highlightSignature (code : String) : DocElabM Highlighted := do
  let helper ← currentHelper
  helper.signature code

def highlightCommand (code : String) : DocElabM Highlighted := do
  let helper ← currentHelper
  helper.command code

def highlightName (code : String) : DocElabM Highlighted := do
  let helper ← currentHelper
  helper.name code

/-- The `signature` code block displays a Lean declaration's type signature
with syntax highlighting. -/
@[code_block_expander signature]
def signatureBlock : CodeBlockExpander
  | args, code => do
    ArgParse.done.run args
    let codeStr := code.getString

    try
      let hl ← highlightSignature codeStr

      saveBackref hl
      for (msg, _) in _root_.allInfo hl do
        let k := match msg.severity with | .info => "info" | .error => "error" | .warning => "warning"
        Verso.Log.logSilentInfo m!"{k}: {msg.toString}"

      return #[← ``(Block.other (Block.lean $(quote hl) {}) #[Block.code $(quote codeStr)])]
    catch
      | .error refStx e =>
        logErrorAt refStx e
        return #[← ``(sorry)]
      | e => throw e

/-! ## Feature 4: leanRef role -/

/-- The `{leanRef}` role finds a previously highlighted expression by name and
reuses its highlighting. Use `{leanRef in="context"}`\`expr\`` to search within
a specific context. -/
@[role_expander leanRef]
def leanRef : RoleExpander
  | args, inls => do
    let in? ← ArgParse.run (.named `in .string true) args
    let code ← oneCodeStr inls
    let codeStr := code.getString

    for prev in (recentHighlightsExt.getState (← getEnv)).toArray do
      if let some «in» := in? then
        if let some hl := prev.matchingExpr? «in» then
          if let some hl := hl.matchingExpr? codeStr then
            return #[← ``(Inline.other (Inline.lean $(quote hl) {}) #[Inline.code $(quote hl.toString)])]
          else continue
      else if let some hl := prev.matchingExpr? codeStr then
        return #[← ``(Inline.other (Inline.lean $(quote hl) {}) #[Inline.code $(quote hl.toString)])]

    throwError "Not found: '{codeStr}'"

/-! ## leanName role (shows a resolved Lean name with hover info) -/

@[role_expander leanName]
def leanName : RoleExpander
  | args, inls => do
    let show? ← ArgParse.run (.named `show .string true) args
    let code ← oneCodeStr inls
    let codeStr := code.getString

    try
      let hl ← highlightName codeStr
      let hl :=
        if let some s := show? then
          if let .token ⟨k, _⟩ := hl then
            .token ⟨k, s⟩
          else hl
        else hl

      saveBackref hl
      match hl with
      | .token ⟨k, _⟩ =>
        match k with
        | .const _ sig doc? _ _ =>
          Verso.Hover.addCustomHover code <|
            s!"```\n{sig}\n```\n" ++
            (doc?.map ("\n\n***\n\n" ++ ·) |>.getD "")
        | .var _ sig _ =>
          Verso.Hover.addCustomHover code <|
            s!"```\n{sig}\n```\n"
        | _ => pure ()
      | _ => pure ()

      return #[← ``(Inline.other (Inline.lean $(quote hl) {}) #[Inline.code $(quote hl.toString)])]
    catch
      | .error refStx e =>
        logErrorAt refStx e
        return #[← ``(sorry)]
      | e => throw e

/-! ## Enhanced lean role with backref saving -/

/-- The `{leanCmd}` inline role elaborates a Lean command and renders it. -/
@[role_expander leanCmd]
def leanCmd : RoleExpander
  | args, inls => do
    let _type? ← ArgParse.done.run args
    let code ← oneCodeStr inls
    let codeStr := code.getString

    try
      let hl ← highlightCommand codeStr

      saveBackref hl
      for (msg, _) in _root_.allInfo hl do
        let k := match msg.severity with | .info => "info" | .error => "error" | .warning => "warning"
        Verso.Log.logSilentInfo m!"{k}: {msg.toString}"

      return #[← ``(Inline.other (Inline.lean $(quote hl) {}) #[Inline.code $(quote hl.toString)])]
    catch
      | .error refStx e =>
        logErrorAt refStx e
        return #[← ``(sorry)]
      | e => throw e

/-- The `leanCmd` code block elaborates a Lean command. -/
@[code_block_expander leanCmd]
def leanCmdBlock : CodeBlockExpander
  | args, code => do
    let _type? ← ArgParse.done.run args
    let codeStr := code.getString

    try
      let hl ← highlightCommand codeStr

      saveBackref hl
      for (msg, _) in _root_.allInfo hl do
        let k := match msg.severity with | .info => "info" | .error => "error" | .warning => "warning"
        Verso.Log.logSilentInfo m!"{k}: {msg.toString}"

      return #[← ``(Block.other (Block.lean $(quote hl) {}) #[Block.code $(quote codeStr)])]
    catch
      | .error refStx e =>
        logErrorAt refStx e
        return #[← ``(sorry)]
      | e => throw e

/-! ## Markdown-style table code block

Write tables in verso using fenced code blocks:

````
```table
| Header1 | Header2 | Header3 |
|---------|---------|---------|
| cell1   | cell2   | cell3   |
| cell4   | cell5   | cell6   |
```
````
-/

private def parseTableRow (line : String) : Array String :=
  let line := line.trimAscii.toString
  let line := if line.startsWith "|" then (line.drop 1).trimAscii.toString else line
  let line := if line.endsWith "|" then (line.dropRight 1).trimAscii.toString else line
  (line.splitOn "|").toArray.map fun s => s.trimAscii.toString

private def isSeparatorRow (line : String) : Bool :=
  line.trimAscii.toString.toList.all fun c => c == '|' || c == '-' || c == ':' || c == ' '

private def tableCss : String := r#"
table.md-table {
  border-collapse: collapse;
  margin: 1em 0;
  width: 100%;
  font-size: 0.95em;
}
table.md-table th,
table.md-table td {
  border: 1px solid #ddd;
  padding: 8px 12px;
  text-align: left;
}
table.md-table thead th {
  background-color: #f5f5f5;
  font-weight: 600;
  border-bottom: 2px solid #ccc;
}
table.md-table tbody tr:nth-child(even) {
  background-color: #fafafa;
}
table.md-table tbody tr:hover {
  background-color: #f0f0f0;
}

/* P1: Visual distinction for compiled vs uncompiled code blocks */
/* Compiled code blocks (from SubVerso) have class hl.lean.block */
code.hl.lean.block {
  border-left: 3px solid #4caf50;
  background-color: #f8fdf8;
}

/* Uncompiled code blocks are plain pre without .hl */
pre:not(:has(code.hl)) {
  border-left: 3px solid #ccc;
}
"#

block_extension Block.mdTable (header : Array String) (rows : Array (Array String)) where
  data := ToJson.toJson (header, rows)
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [tableCss]
  toHtml :=
    open Verso.Output Html in
    open Verso.Output.Html in
    some <| fun _goI _goB _id data _content => do
      match FromJson.fromJson? (α := Array String × Array (Array String)) data with
      | .error _e =>
        return .empty
      | .ok (hdr, bodyRows) =>
        let thCells : Array Html := hdr.map (fun cell => {{<th>{{Html.text true cell}}</th>}})
        let tbodyRows : Array Html := bodyRows.map (fun row =>
          let cells : Array Html := row.map (fun cell => {{<td>{{Html.text true cell}}</td>}})
          {{<tr>{{cells}}</tr>}})
        pure {{
          <table class="md-table">
            <thead><tr>{{thCells}}</tr></thead>
            <tbody>{{tbodyRows}}</tbody>
          </table>
        }}

/-- The `table` code block parses pipe-delimited markdown table syntax
and renders it as an HTML table. -/
@[code_block_expander table]
def tableBlock : CodeBlockExpander
  | args, code => do
    ArgParse.done.run args
    let lines := (code.getString.splitOn "\n").filter (·.trim != "")
    match lines with
    | [] => throwError "Empty table"
    | [_] => throwError "Table needs at least a header and separator row"
    | headerLine :: rest =>
      let header := parseTableRow headerLine
      let dataLines := if rest.length > 0 && isSeparatorRow rest[0]! then rest.drop 1 else rest
      let rows := (dataLines.map parseTableRow).toArray
      return #[← ``(Block.other (Block.mdTable $(quote header) $(quote rows)) #[])]

