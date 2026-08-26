import SubVerso.Examples
import Lean
import Lean.Elab.Command
import Lean.Elab.InfoTree.Main
import Lean.Util.CollectAxioms
import Lean.Util.SafeExponentiation

open Lean Elab Command

namespace tacticbook_corem

-- ANCHOR: corem_builtin_print_axioms
#print axioms Classical.choice
#print axioms Nat.add_comm
-- ANCHOR_END: corem_builtin_print_axioms
-- ANCHOR: corem_print_axioms
syntax (name := bookPrintAxioms) "#book_print" "axioms" ident : command

@[command_elab bookPrintAxioms]
def elabBookPrintAxioms : CommandElab
  | `(#book_print axioms $id:ident) => withRef id do
      let constNames ← liftCoreM <| realizeGlobalConstWithInfos id
      for constName in constNames do
        let axs ← collectAxioms constName
        let constMsg := MessageData.ofConstName constName
        if axs.isEmpty then
          logInfo m!"'{constMsg}' does not depend on any axioms"
        else
          let axiomMsgs := axs.qsort Name.lt
            |>.map MessageData.ofConstName
            |>.toList
          logInfo m!"'{constMsg}' depends on axioms: {axiomMsgs}"
  | _ => throwUnsupportedSyntax
-- ANCHOR_END: corem_print_axioms

-- ANCHOR: corem_print_axioms_use
#book_print axioms Classical.choice
#book_print axioms Nat.add_comm
-- ANCHOR_END: corem_print_axioms_use

-- ANCHOR: corem_monad_laws
private def sortedAxioms (name : Name) : CoreM (Array Name) := do
  return (← collectAxioms name).qsort Name.lt

private def renderNames (names : Array Name) : CoreM String :=
  pure s!"{names.toList}"

private structure MonadLawObservation where
  leftViaPure : Array Name
  direct : Array Name
  rightViaBind : Array Name
  leftAssociated : String
  rightAssociated : String

private def observeMonadLaws (name : Name) : CoreM MonadLawObservation := do
  let leftViaPure ← (pure name >>= sortedAxioms)
  let direct ← sortedAxioms name
  let rightViaBind ← (sortedAxioms name >>= pure)
  let leftAssociated ←
    ((sortedAxioms name >>= fun names => pure names) >>= renderNames)
  let rightAssociated ←
    (sortedAxioms name >>= fun names => pure names >>= renderNames)
  return {
    leftViaPure, direct, rightViaBind, leftAssociated, rightAssociated
  }
-- ANCHOR_END: corem_monad_laws

-- ANCHOR: corem_monad_laws_use
elab "#check_corem_laws " id:ident : command => do
  let names ← liftCoreM <| realizeGlobalConstWithInfos id
  for name in names do
    let obs ← liftCoreM <| observeMonadLaws name
    logInfo m!"left identity: {obs.leftViaPure.toList} = {obs.direct.toList}"
    logInfo m!"right identity: {obs.rightViaBind.toList} = {obs.direct.toList}"
    logInfo m!"associativity: {obs.leftAssociated} = {obs.rightAssociated}"

#check_corem_laws Classical.choice
-- ANCHOR_END: corem_monad_laws_use

-- ANCHOR: corem_options_messages
elab "#check_large_exponents" : command => do
  let (first, second) ← liftCoreM do
    let first ← checkExponent 300
    let second ← checkExponent 301
    return (first, second)
  logInfo m!"accepted? first={first}, second={second}"

#check_large_exponents
-- ANCHOR_END: corem_options_messages

-- ANCHOR: corem_fresh_restore
private def freshRestoreProbe : CoreM Bool := do
  let saved ← Core.saveState
  let first ← mkFreshUserName `tmp
  saved.restore
  let second ← mkFreshUserName `tmp
  return first != second

elab "#check_fresh_restore" : command => do
  let distinct ← liftCoreM freshRestoreProbe
  logInfo m!"fresh names remain distinct after ordinary restore: {distinct}"

#check_fresh_restore
-- ANCHOR_END: corem_fresh_restore

-- ANCHOR: corem_exception_probe
private def exceptionProbe : CoreM (Bool × Bool) := do
  let before := (← get).nextMacroScope
  let continued ←
    try
      let _ ← mkFreshUserName `insideFailure
      throwError "expected failure"
      pure true
    catch _ =>
      pure false
  let after := (← get).nextMacroScope
  return (continued, before != after)

elab "#check_corem_exception" : command => do
  let (continued, stateChanged) ← liftCoreM exceptionProbe
  logInfo m!"continued past throw? {continued}; state change survived? {stateChanged}"

#check_corem_exception
-- ANCHOR_END: corem_exception_probe

-- ANCHOR: corem_standalone
private def standaloneAudit : CoreM (Array Name × Bool) := do
  let axs ← collectAxioms ``Classical.choice
  let first ← mkFreshUserName `tmp
  let second ← mkFreshUserName `tmp
  return (axs, first != second)

unsafe def runStandaloneAudit : IO (Array Name × Bool) :=
  Lean.withImportModules #[{ module := `Init }] {} fun env => do
    let ctx : Core.Context := {
      fileName := "<corem-book>"
      fileMap := default
    }
    let state : Core.State := { env }
    let (result, _) ← standaloneAudit.toIO ctx state
    return result
-- ANCHOR_END: corem_standalone

-- ANCHOR: corem_standalone_use
#eval runStandaloneAudit
-- ANCHOR_END: corem_standalone_use

-- ANCHOR: corem_decl_kind_solution
private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient declaration"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

elab "#decl_kind " id:ident : command => withRef id do
  let names ← liftCoreM <| realizeGlobalConstWithInfos id
  let env ← getEnv
  for name in names do
    let some info := env.find? name
      | throwError "unknown declaration '{name}'"
    logInfo m!"{MessageData.ofConstName name}: {declarationKind info}"

#decl_kind Nat.add_comm
-- ANCHOR_END: corem_decl_kind_solution

-- ANCHOR: corem_direct_dependencies
axiom dependencyC : Nat

noncomputable def dependencyB : Nat := dependencyC

noncomputable def dependencyA : Nat := dependencyB

private def directConstants (info : ConstantInfo) : Array Name := Id.run do
  let mut names : NameSet := {}
  for name in info.type.getUsedConstants do
    names := names.insert name
  if let some value := info.value? (allowOpaque := true) then
    for name in value.getUsedConstants do
      names := names.insert name
  return names.toArray.qsort Name.lt

elab "#direct_deps " id:ident : command => withRef id do
  let names ← liftCoreM <| realizeGlobalConstWithInfos id
  let env ← getEnv
  for name in names do
    let some info := env.find? name
      | throwError "unknown declaration '{name}'"
    logInfo m!"direct constants: {directConstants info}"

#direct_deps dependencyA
#book_print axioms dependencyA
-- ANCHOR_END: corem_direct_dependencies

-- ANCHOR: corem_name_resolution
namespace ResolutionDemo
axiom localAxiom : Nat
#book_print axioms localAxiom
end ResolutionDemo

namespace OpenDemo
axiom openedAxiom : Nat
end OpenDemo

open OpenDemo
#book_print axioms openedAxiom
-- ANCHOR_END: corem_name_resolution

-- Exercise 4.3 solution: plain `ofName` output, with no rich constant-name renderer.
syntax (name := plainPrintAxioms) "#plain_print" "axioms" ident : command

@[command_elab plainPrintAxioms]
def elabPlainPrintAxioms : CommandElab
  | `(#plain_print axioms $id:ident) => withRef id do
      let names ← liftCoreM <| realizeGlobalConstWithInfos id
      for constName in names do
        let axs ← collectAxioms constName
        logInfo m!"'{MessageData.ofName constName}': {axs.toList}"
  | _ => throwUnsupportedSyntax

#plain_print axioms Classical.choice

-- Exercise 4.4 solution: predict the fields from the operations that actually run.
private structure CoreStateObservation where
  envSizeUnchanged : Bool
  messageCountIncreased : Bool
  nextMacroScopeIncreased : Bool

private def observeCoreState : CoreM CoreStateObservation := do
  let before ← get
  logInfo "state-observation message"
  let _ ← mkFreshUserName `stateProbe
  let after ← get
  return {
    envSizeUnchanged := before.env.constants.map₁.size == after.env.constants.map₁.size
    messageCountIncreased := before.messages.toList.length < after.messages.toList.length
    nextMacroScopeIncreased := before.nextMacroScope < after.nextMacroScope
  }

elab "#observe_core_state" : command => do
  let obs ← liftCoreM observeCoreState
  logInfo m!"env-size unchanged={obs.envSizeUnchanged}; messages increased={obs.messageCountIncreased}; nextMacroScope increased={obs.nextMacroScopeIncreased}"

#observe_core_state

-- Exercise 4.5 solution: imported declaration → module index → module name.
elab "#decl_module " id:ident : command => do
  let names ← liftCoreM <| realizeGlobalConstWithInfos id
  for name in names do
    let env ← getEnv
    match env.getModuleIdxFor? name with
    | none => logInfo m!"{name}: current module or unknown origin"
    | some idx =>
      let moduleName := env.header.moduleNames[idx.toNat]!
      logInfo m!"{name}: {moduleName}"

#decl_module Nat.add_comm

end tacticbook_corem
