import SubVerso.Examples
import Lean

open Lean Elab Tactic Meta

namespace tacticbook_appendix

-- ANCHOR: appendix_inspect_goal
elab "inspect_goal" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  let target ← whnf target
  logInfo m!"goal: {target}"
-- ANCHOR_END: appendix_inspect_goal

-- ANCHOR: appendix_inspect_expr
def inspectExpr (expr : Expr) : MetaM Unit := do
  let type ← inferType expr
  let type ← instantiateMVars type
  logInfo m!"type: {type}"
-- ANCHOR_END: appendix_inspect_expr

-- ANCHOR: appendix_close_or_keep
elab "close_or_keep" : tactic => do
  let goal ← getMainGoal
  if ← goal.isAssigned then
    replaceMainGoal []
  else
    replaceMainGoal [goal]
-- ANCHOR_END: appendix_close_or_keep

-- ANCHOR: appendix_tactic_declarations
syntax "my_assumption" : tactic

macro "my_rfl" : tactic => `(tactic| rfl)

elab_rules : tactic
  | `(tactic| my_assumption) => do
      evalTactic (← `(tactic| assumption))
-- ANCHOR_END: appendix_tactic_declarations

end tacticbook_appendix
