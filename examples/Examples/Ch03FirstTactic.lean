import SubVerso.Examples
import Mathlib.Tactic
open Lean Elab Tactic Meta

-- ANCHOR: my_assumption
elab "my_assumption" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.getType
    let lctx ← getLCtx
    for decl in lctx do
      if decl.isImplementationDetail then continue
      if ← isDefEq decl.type target then
        goal.assign decl.toExpr
        return
    throwTacticEx `my_assumption goal "no matching hypothesis found"
-- ANCHOR_END: my_assumption

-- ANCHOR: split_and
elab "split_and" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.getType
    let_expr And P Q := target | throwTacticEx `split_and goal "goal is not a conjunction"
    let mvarP ← mkFreshExprMVar P
    let mvarQ ← mkFreshExprMVar Q
    let proof := mkApp4 (mkConst ``And.intro) P Q mvarP mvarQ
    goal.assign proof
    let newGoals := [mvarP.mvarId!, mvarQ.mvarId!]
    let others := (← getGoals).erase goal
    setGoals (newGoals ++ others)
-- ANCHOR_END: split_and

-- ANCHOR: my_smart_close
elab "my_smart_close" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.getType
    let lctx ← getLCtx
    for decl in lctx do
      if decl.isImplementationDetail then continue
      if ← isDefEq decl.type target then
        goal.assign decl.toExpr
        return
    try
      evalTactic (← `(tactic| rfl))
      return
    catch _ => pure ()
    throwTacticEx `my_smart_close goal "no hypothesis matches and rfl failed"
-- ANCHOR_END: my_smart_close

-- ANCHOR: my_smart_close_short
elab "my_smart_close₂" : tactic => do
  evalTactic (← `(tactic| first | assumption | rfl))
-- ANCHOR_END: my_smart_close_short

-- ANCHOR: assumption_on_all
elab "assumption_on_all" : tactic => do
  let goals ← getGoals
  let mut remaining : List MVarId := []
  for g in goals do
    if ← g.isAssigned then continue
    let closed ← g.withContext do
      let target ← g.getType
      let lctx ← getLCtx
      for decl in lctx do
        if decl.isImplementationDetail then continue
        if ← isDefEq decl.type target then
          g.assign decl.toExpr
          return true
      return false
    if !closed then
      remaining := remaining ++ [g]
  setGoals remaining
-- ANCHOR_END: assumption_on_all

-- ANCHOR: diagnostics
-- throwTacticEx 会显示目标上下文
-- throwTacticEx `my_tactic goal "expected an equality goal"

-- throwError 是通用错误
-- throwError "my_tactic: internal error"

-- logWarning 不中断执行
-- logWarning "this goal might not be provable by my_tactic"

-- trace 用于调试
-- trace[my_tactic] "trying hypothesis {decl.userName}"
-- ANCHOR_END: diagnostics

-- ANCHOR: register_trace
initialize registerTraceClass `my_tactic
-- ANCHOR_END: register_trace

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
