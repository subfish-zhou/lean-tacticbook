import VersoManual
import SubVerso.Highlighting
import SubVerso.Highlighting.String

open Verso Doc Elab Genre.Manual ArgParse Code Highlighted
open Verso Code External
open SubVerso.Highlighting
open Lean

/-! ## Labelled code boxes -/

private def codeBoxInfo? (label : String) : Option (String × String) :=
  match label with
  | "可运行" => some ("runnable", label)
  | "示意" => some ("hint", label)
  | "源码节选" => some ("excerpt", label)
  | "伪代码" => some ("pseudo", label)
  | "练习·故意错误" => some ("bug", "练习 · 故意错误")
  | "练习模板" => some ("template", label)
  | _ => none

private def codeBoxCss : String := r#"
:root {
  --verso-code-keyword-color: #a626a4;
  --verso-code-const-color: #005cc5;
  --verso-code-literal-color: #005cc5;
  --verso-code-var-color: #24292e;
  --verso-code-sort-color: #22863a;
  --verso-code-typed-color: #24292e;
}

.hl.lean .token.keyword, .hl.lean .keyword,
pre.hl.lean .token.keyword, pre.hl.lean .keyword {
  color: #a626a4 !important;
  font-weight: bold;
}
.hl.lean .token.const, .hl.lean .const,
pre.hl.lean .token.const, pre.hl.lean .const,
.hl.lean .token.literal, .hl.lean .literal,
pre.hl.lean .token.literal, pre.hl.lean .literal {
  color: #005cc5 !important;
}
.hl.lean .token.sort, .hl.lean .sort,
pre.hl.lean .token.sort, pre.hl.lean .sort {
  color: #22863a !important;
  font-weight: bold;
}
.hl.lean .token.var, .hl.lean .var {
  color: #24292e !important;
  font-style: italic;
}
.hl.lean .token.comment, .hl.lean .comment,
pre.hl.lean .token.comment, pre.hl.lean .comment {
  color: #6a737d !important;
  font-style: italic;
}

.hl.bash .cmd, pre.hl.bash .cmd {
  color: #6f42c1 !important;
  font-weight: bold;
}
.hl.bash .opt, pre.hl.bash .opt { color: #e36209 !important; }
.hl.bash .string, pre.hl.bash .string { color: #22863a !important; }
.hl.bash .comment, pre.hl.bash .comment {
  color: #6a737d !important;
  font-style: italic;
}

.codebox {
  margin: 1em 0;
  border-left: 3px solid #ccc;
  border-radius: 4px;
  overflow: hidden;
}
.codebox-header {
  display: inline-block;
  padding: 1px 10px;
  margin: 0;
  font-size: 0.72em;
  font-weight: 600;
  letter-spacing: 0.03em;
  border-radius: 0 0 6px 0;
  line-height: 1.6;
  vertical-align: top;
}
.codebox pre,
.codebox > code.hl.lean.block {
  margin: 0 !important;
  border-left: none !important;
  border-radius: 0 !important;
}
.codebox > code.hl.lean.block {
  display: block;
  padding: 0.6em 1em;
  background-color: transparent;
}
.codebox > pre {
  padding: 0.6em 1em;
  background-color: transparent;
}

.codebox-runnable,
.codebox-hint,
.codebox-excerpt,
.codebox-bug {
  background-color: #f8fdf8;
  border-left-color: #4caf50;
}
.codebox-runnable > .codebox-header,
.codebox-hint > .codebox-header,
.codebox-excerpt > .codebox-header,
.codebox-bug > .codebox-header {
  color: #fff;
  background-color: #4caf50;
}
.codebox-bug > .codebox-header { background-color: #d9534f; }

.codebox-pseudo {
  background-color: #fffbea;
  border-left-color: #d4a017;
}
.codebox-pseudo > .codebox-header {
  color: #fff;
  background-color: #d4a017;
}

.codebox-template {
  background-color: #fff7ec;
  border-left-color: #e6913a;
}
.codebox-template > .codebox-header {
  color: #fff;
  background-color: #e6913a;
}

.codebox-runnable:has(pre.hl.bash.block) {
  background-color: #f4faff;
  border-left-color: #2196f3;
}
.codebox-runnable:has(pre.hl.bash.block) > .codebox-header {
  background-color: #2196f3;
}
"#

block_extension Block.codeBox (kind : String) (label : String) where
  data := ToJson.toJson (kind, label)
  traverse _ _ _ := pure none
  toTeX := some fun _goI goB _id _data contents => contents.mapM goB
  extraCss := [codeBoxCss]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _goI goB _id data contents => do
      let .ok (kind, label) := FromJson.fromJson? (α := String × String) data
        | reportError "Invalid code box data"
          return .empty
      pure {{
        <div class={{"codebox codebox-" ++ kind}}>
          <div class="codebox-header">{{label}}</div>
          {{← contents.mapM goB}}
        </div>
      }}

structure CodeBoxConfig where
  label : StrLit

instance : FromArgs CodeBoxConfig DocElabM where
  fromArgs := CodeBoxConfig.mk <$> .positional `label .strLit

@[directive]
def codeBox : DirectiveExpanderOf CodeBoxConfig
  | {label}, contents => do
    let label := label.getString
    let some (kind, displayLabel) := codeBoxInfo? label
      | throwError "Unknown code box label {repr label}"
    let blocks ← contents.mapM elabBlock
    ``(Block.other (Block.codeBox $(quote kind) $(quote displayLabel)) #[ $[ $blocks ],* ])

/-! ## Collapsible API boxes -/

private def apiBoxCss : String := r#"
.api-box {
  margin: 1em 0;
  border: 1px solid #8aa6b8;
  border-radius: 4px;
  background: #f7fbfd;
  overflow: hidden;
}
.api-box > summary {
  padding: 0.55em 0.8em;
  cursor: pointer;
  font-weight: 600;
  background: #eaf2f6;
}
.api-box > summary:hover { background: #e1edf2; }
.api-box-content {
  padding: 0.2em 0.8em 0.8em;
  overflow-x: auto;
}
.api-box-content > :first-child { margin-top: 0.6em; }
.api-box-content > :last-child { margin-bottom: 0; }
.api-catalog-table code {
  white-space: pre-wrap;
  overflow-wrap: anywhere;
}
"#

block_extension Block.apiBox (title : String) (opened : Bool) where
  data := ToJson.toJson (title, opened)
  traverse _ _ _ := pure none
  toTeX := some fun _goI goB _id _data contents => contents.mapM goB
  extraCss := [apiBoxCss]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _goI goB _id data contents => do
      let .ok (title, opened) := FromJson.fromJson? (α := String × Bool) data
        | reportError "Invalid API box data"
          return .empty
      let attrs := if opened then #[("open", "")] else #[]
      pure {{
        <details class="api-box" {{attrs}}>
          <summary>{{title}}</summary>
          <div class="api-box-content">{{← contents.mapM goB}}</div>
        </details>
      }}

structure ApiBoxConfig where
  title : StrLit
  opened : Bool := false

def ApiBoxConfig.parse : ArgParse DocElabM ApiBoxConfig :=
  ApiBoxConfig.mk <$> .positional `title .strLit <*> .namedD' `open false

instance : FromArgs ApiBoxConfig DocElabM where
  fromArgs := ApiBoxConfig.parse

@[directive]
def apiBox : DirectiveExpanderOf ApiBoxConfig
  | {title, opened}, contents => do
    let blocks ← contents.mapM elabBlock
    ``(Block.other (Block.apiBox $(quote title.getString) $(quote opened)) #[ $[ $blocks ],* ])

/-! ## Generated API catalogues -/

private def apiDeclKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def apiSourceModule (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some index => env.allImportedModuleNames[index]!
  | none => env.mainModule

private def isPublicApiDecl (name : Name) : Bool :=
  !isPrivateName name && !name.isInternalOrNum

public def apiCatalogDeclarations (env : Environment) (sourceName : Name) :
    Array (Name × ConstantInfo × Name) :=
  env.constants.toList.toArray.qsort (fun (name₁, _) (name₂, _) =>
    name₁.quickCmp name₂ == .lt) |>.filterMap fun (name, info) =>
      let origin := apiSourceModule env name
      if sourceName.isPrefixOf origin && isPublicApiDecl name then
        some (name, info, origin)
      else
        none

private def summarizeApiDoc (doc? : Option String) : String :=
  let summary := doc?.map (·.splitOn "\n\n" |>.headD "") |>.getD "无源码说明"
  let summary := summary.replace "\n" " " |>.replace "\r" " " |>.trimAscii.toString
  if summary.length ≤ 240 then summary
  else String.ofList (summary.toList.take 237) ++ "..."

private def apiMarkers (info : ConstantInfo) (effects : String) : String :=
  let safety := if info.isUnsafe then "unsafe" else "safe"
  let partialMark := if info.isPartial then " · partial" else ""
  s!"{safety}{partialMark} · {effects} · 随 Lean 版本演进"

private def decodeApiCatalogRows (payload : String) :
    Except String (Array (Array (String × Bool))) := do
  let json ← Json.parse payload
  FromJson.fromJson? json

block_extension Block.apiCatalogData (title : String) (payload : String) where
  data := ToJson.toJson (title, payload)
  traverse _ _ _ := pure none
  extraCss := [apiBoxCss]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _goI _goB _id data _contents => do
      let .ok (title, payload) := FromJson.fromJson? (α := String × String) data
        | reportError "Invalid API catalogue data"
          return .empty
      let .ok rows := decodeApiCatalogRows payload
        | reportError "Invalid API catalogue row data"
          return .empty
      let headers := #[
        "API 名称", "种类", "完整签名", "层 / 上下文", "来源模块",
        "用途 / 官方说明", "稳定性与副作用"
      ]
      let headerCells := Output.Html.seq <| headers.map fun header =>
        let header := Output.Html.ofString header
        {{<th>{{header}}</th>}}
      let bodyRows ← rows.mapM fun row => do
        let cells := Output.Html.seq <| row.map fun (value, code) =>
          let value := Output.Html.ofString value
          let cell : Output.Html := if code then {{<code>{{value}}</code>}} else value
          {{<td>{{cell}}</td>}}
        pure {{<tr>{{cells}}</tr>}}
      let bodyRows := Output.Html.seq bodyRows
      pure {{
        <details class="api-box">
          <summary>{{title}}</summary>
          <div class="api-box-content">
            <table class="tabular api-catalog-table">
              <thead><tr>{{headerCells}}</tr></thead>
              <tbody>{{bodyRows}}</tbody>
            </table>
          </div>
        </details>
      }}
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _goI _goB _id data _contents => do
      let .ok (title, payload) := FromJson.fromJson? (α := String × String) data
        | reportError "Invalid API catalogue data"
          return .empty
      let .ok rows := decodeApiCatalogRows payload
        | reportError "Invalid API catalogue row data"
          return .empty
      let renderedRows := rows.map fun row =>
        let line := String.intercalate " | " <| row.toList.map (·.1)
        Output.TeX.seq #[.text line, .paragraphBreak]
      pure <| .seq <| #[.command "textbf" #[] #[.text title], .raw "\n"] ++ renderedRows

structure ApiCatalogConfig where
  title : StrLit
  source : StrLit
  layer : StrLit
  effects : StrLit

instance : FromArgs ApiCatalogConfig DocElabM where
  fromArgs := ApiCatalogConfig.mk
    <$> .positional `title .strLit
    <*> .positional `source .strLit
    <*> .positional `layer .strLit
    <*> .positional `effects .strLit

@[directive]
def apiCatalog : DirectiveExpanderOf ApiCatalogConfig
  | {title, source, layer, effects}, _ => do
    let env ← getEnv
    let sourceName := source.getString.toName
    let declarations := apiCatalogDeclarations env sourceName
    let mut rows := #[]
    let options : Options := {}
    let options := options.setBool `pp.universes true
      |>.setBool `pp.explicit true
      |>.setBool `pp.fullNames true
    for (name, info, origin) in declarations do
      let signature ← liftM <| PrettyPrinter.ppExprLegacy env {} {} options info.type
      let doc? ← liftM <| Lean.findDocString? env name
      rows := rows.push #[
        (name.toString, true),
        (apiDeclKind info, false),
        (signature.pretty 100, true),
        (layer.getString, false),
        (origin.toString, true),
        (summarizeApiDoc doc?, false),
        (apiMarkers info effects.getString, false)
      ]
    if rows.isEmpty then
      throwError "No public declarations found for module prefix {source.getString}"
    let boxTitle := s!"{title.getString}（{rows.size} 项）"
    let payload := (ToJson.toJson rows).compress
    ``(Verso.Doc.Block.other (Block.apiCatalogData $(quote boxTitle) $(quote payload)) #[])

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

private def projectDir : System.FilePath := "examples"

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

/-! ## Shared HTML tokeniser helpers (used by `leanBug`, `bashFence`) -/

/-- Escape `<`, `>`, `&`, quotes for safe HTML text. -/
private def htmlEscape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '<' => acc ++ "&lt;"
    | '>' => acc ++ "&gt;"
    | '&' => acc ++ "&amp;"
    | '"' => acc ++ "&quot;"
    | '\'' => acc ++ "&#39;"
    | _ => acc.push c

private def spanOpen (cls : String) : String :=
  "<span class=\"" ++ cls ++ "\">"

private def spanClose : String := "</span>"

/-! ## Deliberate-error Lean block (`leanBug`)

Runnable examples use Verso's external `anchor` blocks, which are elaborated
in the examples project and abort the build on errors. A `[练习·故意错误]`
snippet is _expected_ to fail elaboration, so it is rendered with light Lean
syntax highlighting without entering that validation path.

`leanBug` uses a small hand-written keyword-list tokeniser (same shape as
`bashFence`). It intentionally does not talk to the helper.
-/

private def leanBugKeywords : Array String := #[
  "import", "open", "namespace", "end", "section", "variable", "universe",
  "def", "theorem", "lemma", "example", "abbrev", "structure", "class",
  "inductive", "instance", "instance*", "elab", "elab_rules", "syntax",
  "macro", "macro_rules", "notation", "infix", "infixl", "infixr", "prefix",
  "postfix", "deriving", "attribute", "export",
  "let", "fun", "match", "with", "do", "if", "then", "else", "return", "pure",
  "have", "show", "by", "at", "in", "for", "while", "where", "mutual",
  "unless", "sorry", "admit", "exact", "intro", "intros", "apply", "cases",
  "induction", "refine", "rw", "simp", "trivial", "ring", "linarith", "omega",
  "constructor", "assumption", "contradiction", "decide", "aesop"
]

private def isLeanIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\''

/-- Tokenise a single Lean line into HTML: keywords → span.keyword,
    "…" → span.literal, `--…` → span.comment. -/
private partial def tokeniseLeanLine (line : String) : String := Id.run do
  let cs : Array Char := line.toList.toArray
  let n := cs.size
  let mut acc : String := ""
  let mut i : Nat := 0
  let sub := fun (a b : Nat) => (cs.extract a b).foldl String.push ""
  while i < n do
    let c := cs[i]!
    -- comment `--…`
    if c == '-' && i + 1 < n && cs[i+1]! == '-' then
      acc := acc ++ "<span class=\"comment\">" ++ htmlEscape (sub i n) ++ "</span>"
      i := n
    -- string "…"
    else if c == '"' then
      let mut j := i + 1
      while j < n && cs[j]! != '"' do j := j + 1
      let endPos := if j < n then j + 1 else j
      acc := acc ++ "<span class=\"literal\">" ++ htmlEscape (sub i endPos) ++ "</span>"
      i := endPos
    -- identifier / keyword
    else if c.isAlpha || c == '_' then
      let mut j := i
      while j < n && isLeanIdentChar cs[j]! do j := j + 1
      let word := sub i j
      if leanBugKeywords.contains word then
        acc := acc ++ "<span class=\"keyword\">" ++ htmlEscape word ++ "</span>"
      else
        acc := acc ++ htmlEscape word
      i := j
    -- digits → literal
    else if c.isDigit then
      let mut j := i
      while j < n && (cs[j]!.isDigit || cs[j]! == '.') do j := j + 1
      acc := acc ++ "<span class=\"literal\">" ++ htmlEscape (sub i j) ++ "</span>"
      i := j
    else
      acc := acc.push c  -- unescaped ASCII punct is fine; & < > handled below via `htmlEscape`
      i := i + 1
  pure acc

private def tokeniseLeanBody (body : String) : String :=
  let ls := body.splitOn "\n"
  String.intercalate "\n" (ls.map tokeniseLeanLine)

/-- CSS piggy-backing on the existing `.hl.lean` palette so bug blocks share
    the same colours as elaborated Lean fences. -/
private def leanBugCss : String := "
pre.hl.lean.block.bug {
  white-space: pre;
  padding: 0.6em 1em;
  overflow-x: auto;
  margin: 1em 0;
  background-color: transparent;
  font-family: var(--verso-code-font-family, monospace);
  font-size: 0.95em;
}
pre.hl.lean.block.bug code { font-family: inherit; font-size: inherit; }
pre.hl.lean.block.bug .keyword { color: #a626a4; font-weight: bold; }
pre.hl.lean.block.bug .literal { color: #005cc5; }
pre.hl.lean.block.bug .comment { color: #6a737d; font-style: italic; }
"

block_extension Block.leanBugCode (body : String) where
  data := ToJson.toJson body
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [leanBugCss]
  toHtml :=
    open Verso.Output Html in
    open Verso.Output.Html in
    some <| fun _goI _goB _id data _content => do
      match FromJson.fromJson? (α := String) data with
      | .error _e => return .empty
      | .ok body =>
        let inner := tokeniseLeanBody body
        pure {{
          <pre class="hl lean block bug"><code>{{Html.text false inner}}</code></pre>
        }}

/-- Placeholder constant so `@[code_block_expander leanBug]` resolves. -/
def leanBug : Unit := ()

/-- Render a Lean snippet that is expected to fail to elaborate. Does not go
    through the helper — uses a simple keyword-list highlighter. -/
@[code_block_expander leanBug]
def leanBugBlock : CodeBlockExpander
  | args, code => do
    ArgParse.done.run args
    let body := code.getString
    return #[← ``(Block.other (Block.leanBugCode $(quote body)) #[Block.code $(quote body)])]

-- Hint variant: keyword-only Lean highlighter, rendered without elaboration.
/-! ## Bash / shell code block (`bashFence`)

A dependency-free shell highlighter. Tokenises each line into:

  * comment (`#` to end-of-line)
  * string (`"…"` and `'…'`)
  * command word (first token if it is a known shell/tool name)
  * option (`-x`, `--long-opt`)
  * env-var assignment (`FOO=bar` before any command)
  * heredoc marker (`<<'EOF'` … `EOF`)
  * plain text (everything else)

Rendered as `<pre class="hl bash block"><code>…</code></pre>` with span classes
that pick up the same CSS variables as the Lean highlighter, so the palette
stays consistent.
-/

private def bashCommandWords : Array String := #[
  "cat", "curl", "wget", "cp", "mv", "rm", "ln", "mkdir", "rmdir", "touch",
  "chmod", "chown", "ls", "cd", "pwd", "pushd", "popd", "echo", "printf",
  "grep", "rg", "sed", "awk", "find", "xargs", "sort", "uniq", "head", "tail",
  "less", "more", "wc", "tar", "zip", "unzip", "gzip", "gunzip", "diff",
  "patch", "cmp", "tr", "cut", "paste",
  "export", "unset", "source", "alias", "which", "env", "set",
  "sh", "bash", "zsh", "sudo", "su",
  "git", "gh", "ssh", "scp", "rsync",
  "make", "cmake", "ninja",
  "python", "python3", "pip", "pip3", "poetry", "conda",
  "npm", "yarn", "pnpm", "node", "npx",
  "go", "cargo", "rustc",
  "docker", "kubectl", "helm",
  "elan", "lake", "lean",
  "systemctl", "journalctl", "service",
  "brew", "apt", "apt-get", "yum", "dnf", "pacman"
]

private def isBashWordChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-' || c == '.' || c == '/' || c == '+'

/-- Tokenise a single shell line into HTML with syntax-class spans.
    Works on `List Char` internally to avoid `String.Pos` API churn. -/
private partial def tokeniseBashLine (line : String) : String := Id.run do
  let cs : Array Char := line.toList.toArray
  let n := cs.size
  let mut acc : String := ""
  let mut i : Nat := 0
  let mut seenCmd : Bool := false
  -- helper: extract substring cs[a..b] as a String
  let sub := fun (a b : Nat) =>
    (cs.extract a b).foldl String.push ""
  -- leading whitespace
  while i < n && (cs[i]! == ' ' || cs[i]! == '\t') do
    acc := acc.push cs[i]!
    i := i + 1
  while i < n do
    let c := cs[i]!
    if c == '#' then
      acc := acc ++ spanOpen "comment" ++ htmlEscape (sub i n) ++ spanClose
      i := n
    else if c == '"' || c == '\'' then
      let quote := c
      let mut j := i + 1
      while j < n && cs[j]! != quote do
        j := j + 1
      let endPos := if j < n then j + 1 else j
      acc := acc ++ spanOpen "string" ++ htmlEscape (sub i endPos) ++ spanClose
      i := endPos
    else if c == ' ' || c == '\t' then
      acc := acc.push c
      i := i + 1
    else if c == '-' && i + 1 < n && (cs[i+1]!.isAlpha || cs[i+1]! == '-') then
      let mut j := i + 1
      while j < n && (isBashWordChar cs[j]! || cs[j]! == '=') do
        j := j + 1
      acc := acc ++ spanOpen "opt" ++ htmlEscape (sub i j) ++ spanClose
      i := j
    else if isBashWordChar c then
      let mut j := i
      while j < n && isBashWordChar cs[j]! do
        j := j + 1
      let word := sub i j
      let isAssign := j < n && cs[j]! == '='
      if isAssign && !seenCmd then
        acc := acc ++ spanOpen "envvar" ++ htmlEscape word ++ spanClose ++ "="
        i := j + 1
      else if !seenCmd && bashCommandWords.contains word then
        acc := acc ++ spanOpen "cmd" ++ htmlEscape word ++ spanClose
        seenCmd := true
        i := j
      else
        acc := acc ++ htmlEscape word
        i := j
    else
      acc := acc.push c
      i := i + 1
  pure acc

/-- Detect a heredoc opener on a line and return the terminator word if any.
    Recognises `<<WORD`, `<<'WORD'`, `<<"WORD"`, `<<-WORD` (with optional
    trailing junk on the same line). Returns `none` if the line has no
    heredoc opener. -/
private def heredocTerminator (line : String) : Option String := Id.run do
  let cs : Array Char := line.toList.toArray
  let n := cs.size
  let mut i := 0
  -- Scan for `<<` (not `<<<`, which is a here-string in bash).
  while i + 1 < n do
    if cs[i]! == '<' && cs[i+1]! == '<' && (i + 2 ≥ n || cs[i+2]! != '<') then
      let mut j := i + 2
      if j < n && cs[j]! == '-' then j := j + 1
      let mut quote : Option Char := none
      if j < n && (cs[j]! == '\'' || cs[j]! == '"') then
        quote := some cs[j]!
        j := j + 1
      let start := j
      match quote with
      | some q =>
        while j < n && cs[j]! != q do j := j + 1
      | none =>
        while j < n && cs[j]!.isAlphanum do j := j + 1
      if j > start then
        let word := (cs.extract start j).foldl String.push ""
        return some word
      else
        return none
    i := i + 1
  return none

/-- Turn a full multi-line body into inner HTML for `<code>`.
    Tracks heredoc state: after `<< 'EOF'` (etc.) subsequent lines are
    emitted as plain escaped text until a line equals the terminator. -/
private def tokeniseBashBody (body : String) : String := Id.run do
  let ls := body.splitOn "\n"
  let mut out : Array String := #[]
  let mut heredoc : Option String := none
  for line in ls do
    match heredoc with
    | some term =>
      -- Inside a heredoc body: emit raw (escaped) text.
      out := out.push (htmlEscape line)
      if line.trimAscii.toString == term then
        heredoc := none
    | none =>
      out := out.push (tokeniseBashLine line)
      heredoc := heredocTerminator line
  pure (String.intercalate "\n" out.toList)

private def bashCss : String := "
pre.hl.bash.block {
  white-space: pre;
  padding: 0.75em 1em;
  border-left: 3px solid #2196f3;
  background-color: #f4faff;
  overflow-x: auto;
  border-radius: 4px;
  margin: 1em 0;
}
pre.hl.bash.block code {
  font-family: var(--verso-code-font-family, monospace);
  font-size: 0.95em;
  color: #2b2b2b;
}
pre.hl.bash.block .cmd {
  color: var(--verso-code-keyword-color, #005cc5);
  font-weight: var(--verso-code-keyword-weight, bold);
}
pre.hl.bash.block .opt {
  color: var(--verso-code-const-color, #6f42c1);
}
pre.hl.bash.block .string {
  color: var(--verso-code-literal-color, #032f62);
}
pre.hl.bash.block .comment {
  color: #6a737d;
  font-style: italic;
}
pre.hl.bash.block .envvar {
  color: var(--verso-code-var-color, #e36209);
  font-weight: 600;
}

/* Give the Lean highlighter the same block-box treatment as bashFence.
   verso emits `<code class=\"hl lean block\">` inline; force it to display
   as a block, padded and framed like the shell blocks. */
code.hl.lean.block {
  display: block;
  padding: 0.75em 1em;
  border-left: 3px solid #4caf50;
  background-color: #f8fdf8;
  overflow-x: auto;
  border-radius: 4px;
  margin: 1em 0;
  font-family: var(--verso-code-font-family, monospace);
  font-size: 0.95em;
}
"

block_extension Block.bashCode (body : String) where
  data := ToJson.toJson body
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [bashCss]
  toHtml :=
    open Verso.Output Html in
    open Verso.Output.Html in
    some <| fun _goI _goB _id data _content => do
      match FromJson.fromJson? (α := String) data with
      | .error _e => return .empty
      | .ok body =>
        let inner := tokeniseBashBody body
        -- Emit raw HTML via `Html.text false` so span markup passes through.
        pure {{
          <pre class="hl bash block"><code>{{Html.text false inner}}</code></pre>
        }}

/-- Placeholder constant so `@[code_block_expander bashFence]` resolves. -/
def bashFence : Unit := ()

/-- The `bashFence` code block renders a shell / bash snippet with light syntax
    highlighting. It does not execute the code. -/
@[code_block_expander bashFence]
def bashFenceBlock : CodeBlockExpander
  | args, code => do
    ArgParse.done.run args
    let body := code.getString
    return #[← ``(Block.other (Block.bashCode $(quote body)) #[Block.code $(quote body)])]

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

Use `\|` for a literal pipe inside a cell. A cell enclosed in single backticks
is rendered as code.
-/

private def splitTableCells (line : String) : Array String :=
  let rec go (chars : List Char) (cell : String) (cells : Array String) : Array String :=
    match chars with
    | '\\' :: '|' :: rest => go rest (cell.push '|') cells
    | '|' :: rest => go rest "" (cells.push cell)
    | char :: rest => go rest (cell.push char) cells
    | [] => cells.push cell
  go line.toList "" #[]

private def parseTableRow (line : String) : Array String :=
  let line := line.trimAscii.toString
  let line := if line.startsWith "|" then (line.drop 1).trimAscii.toString else line
  let line := if line.endsWith "|" then (line.dropEnd 1).toString.trimAscii.toString else line
  (splitTableCells line).map fun s => s.trimAscii.toString

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
        let cellHtml (cell : String) : Html :=
          if cell.startsWith "`" && cell.endsWith "`" then
            {{<code>{{Html.text true (cell.drop 1 |>.dropEnd 1 |>.toString)}}</code>}}
          else
            Html.text true cell
        let thCells : Array Html := hdr.map (fun cell => {{<th>{{cellHtml cell}}</th>}})
        let tbodyRows : Array Html := bodyRows.map (fun row =>
          let cells : Array Html := row.map (fun cell => {{<td>{{cellHtml cell}}</td>}})
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
    let lines := (code.getString.splitOn "\n").filter (·.trimAscii.isEmpty == false)
    match lines with
    | [] => throwError "Empty table"
    | [_] => throwError "Table needs at least a header and separator row"
    | headerLine :: rest =>
      let header := parseTableRow headerLine
      let dataLines := if rest.length > 0 && isSeparatorRow rest[0]! then rest.drop 1 else rest
      let rows := (dataLines.map parseTableRow).toArray
      return #[← ``(Block.other (Block.mdTable $(quote header) $(quote rows)) #[])]
