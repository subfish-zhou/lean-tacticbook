import SubVerso.Examples
import Mathlib.Tactic
open Lean Elab Tactic Meta

-- ANCHOR: trace_goal
syntax "trace_goal" : tactic

elab_rules : tactic
  | `(tactic| trace_goal) => do
    let goal ← getMainGoal           -- 获取第一个目标的 MVarId
    let goalType ← goal.getType      -- 获取目标类型（Expr）
    let goalPP ← ppExpr goalType     -- 美化打印
    logInfo m!"Current goal: {goalPP}"

-- 测试
example (n : Nat) : n + 0 = n := by
  trace_goal  -- 输出: Current goal: n + 0 = n
  simp
-- ANCHOR_END: trace_goal

-- ANCHOR: exact_if_rfl
elab "exact_if_rfl" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  -- 检查目标是否是 a = a 的形式
  let_expr Eq _ lhs rhs := goalType | throwTacticEx `exact_if_rfl goal "goal is not an equality"
  if ← isDefEq lhs rhs then
    goal.assign (← mkEqRefl lhs)  -- 构造 rfl 证明项
  else
    throwTacticEx `exact_if_rfl goal "sides are not definitionally equal"
-- ANCHOR_END: exact_if_rfl

-- ANCHOR: show_type
elab "show_type" : tactic => do
  let goal ← getMainGoal
  -- inferType 是 MetaM 函数，可以直接在 TacticM 中调用
  let goalType ← goal.getType
  let typeOfType ← inferType goalType  -- Expr 的类型
  logInfo m!"Goal type's type: {← ppExpr typeOfType}"
-- ANCHOR_END: show_type

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
#check @getMainGoal
#check @getGoals
#check @setGoals
#check @replaceMainGoal
#check @Lean.throwError
#check @logWarning
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
