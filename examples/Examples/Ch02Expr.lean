import SubVerso.Examples
import Mathlib.Tactic
open Lean Elab Tactic Meta

-- ANCHOR: show_head
elab "show_head" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.getType
    let head := target.getAppFn
    if head.isConst then
      logInfo m!"Head constant: {head.constName}"
    else
      logInfo m!"Head is not a constant: {← ppExpr head}"

example (n : Nat) : n + 0 = n := by
  show_head   -- 应输出: Head constant: Eq
  simp
-- ANCHOR_END: show_head

-- References for {moduleTerm} in verso
section _mt_refs
#check @Expr
#check @MVarId
#check @FVarId
#check @Name
#check @Level
#check @Syntax
#check @LocalDecl
#check @LocalContext
#check @MetavarContext
#check @CoreM
#check @MetaM
#check @TermElabM
#check @TacticM
#check @Environment
#check @BinderInfo
#check @Literal
#check @MData
#check @inferType
#check @isDefEq
#check @whnf
#check @mkFreshExprMVar
#check @forallTelescope
#check @lambdaTelescope
#check @withLocalDecl
#check @mkApp
#check @mkApp2
#check @mkApp3
#check @mkApp4
#check @mkConst
#check @mkLambda
#check @mkForall
#check @getLCtx
#check @getEnv
#check @ppExpr
#check @getMainGoal
#check @getGoals
#check @setGoals
#check @replaceMainGoal
#check @Lean.throwError
#check @logWarning
#check @logInfo
#check @logInfoAt
#check @evalTactic
#check @Bool
#check @Nat
#check @String
#check @Unit
#check @Option
#check @IO
#check @List
#check @Array
end _mt_refs
