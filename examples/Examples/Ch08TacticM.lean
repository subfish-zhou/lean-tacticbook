import SubVerso.Examples
import Lean

open Lean Meta Elab Tactic

namespace tacticbook_tacticm

-- ANCHOR: tacticm_book_apply
elab "book_apply " t:term : tactic => withMainContext do
  let mut theoremExpr ← instantiateMVars (← elabTermForApply t)
  if theoremExpr.isMVar then
    Term.synthesizeSyntheticMVarsNoPostponing
    theoremExpr ← instantiateMVars theoremExpr
  let newGoals ← (← getMainGoal).apply theoremExpr
  Term.synthesizeSyntheticMVarsNoPostponing
  replaceMainGoal newGoals
-- ANCHOR_END: tacticm_book_apply

-- ANCHOR: tacticm_book_apply_use
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  book_apply And.intro
  case left => exact hP
  case right => exact hQ

example (P Q : Prop) (hP : P) : P ∨ Q := by
  book_apply Or.inl
  exact hP
-- ANCHOR_END: tacticm_book_apply_use

-- ANCHOR: tacticm_queue_xray
elab "queue_xray" : tactic => do
  let goals ← getGoals
  logInfo m!"active goals: {goals.length}"
  for h : i in [0:goals.length] do
    let g := goals[i]
    g.withContext do
      logInfo m!"goal {i + 1}:{indentExpr (← g.getType)}"
-- ANCHOR_END: tacticm_queue_xray

-- ANCHOR: tacticm_queue_xray_use
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  queue_xray
  constructor
  queue_xray
  · exact hP
  · exact hQ
-- ANCHOR_END: tacticm_queue_xray_use

-- ANCHOR: tacticm_focus_sequence
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor <;> queue_xray
  · exact hP
  · exact hQ
-- ANCHOR_END: tacticm_focus_sequence

-- ANCHOR: tacticm_dirty_failure
elab "assign_then_fail" : tactic => withMainContext do
  let g ← getMainGoal
  let target ← g.getType
  g.assign (← mkLabeledSorry target (synthetic := true) (unique := true))
  setGoals []
  logInfo "the failing branch changed mctx and emptied the goal queue"
  throwError "intentional failure after changing both states"

elab "assert_main_unassigned" : tactic => do
  unless (← getGoals).length = 1 do
    throwError "the activity queue was not restored"
  let assigned ← (← getMainGoal).isAssigned
  if assigned then
    throwError "the main goal is still assigned"
  logInfo "the restored main goal is unassigned"
-- ANCHOR_END: tacticm_dirty_failure

-- ANCHOR: tacticm_first_restore
example (P : Prop) (h : P) : P := by
  first
  | assign_then_fail
  | assert_main_unassigned
    exact h
-- ANCHOR_END: tacticm_first_restore

-- ANCHOR: tacticm_goal_tags
elab "show_goal_tags" : tactic => do
  for g in (← getGoals) do
    logInfo m!"goal tag: {← g.getTag}"

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  show_goal_tags
  · exact hP
  · exact hQ
-- ANCHOR_END: tacticm_goal_tags

-- ANCHOR: tacticm_prune_solved
elab "assign_without_pruning " t:term : tactic => withMainContext do
  let g ← getMainGoal
  let proof ← elabTermEnsuringType t (some (← g.getType))
  g.assign proof
  logInfo m!"goal queue length immediately after assignment: {(← getGoals).length}"

example (P : Prop) (h : P) : P := by
  assign_without_pruning h
-- Tactic framework prunes solved goals when the block finishes.
-- ANCHOR_END: tacticm_prune_solved

-- ANCHOR: tacticm_dispatch_fallback
syntax (name := bookFallback) "book_fallback" : tactic

@[tactic bookFallback]
def acceptingBookFallback : Tactic := fun _ => do
  unless (← getGoals).length = 1 do
    throwError "dispatcher did not restore the goal queue"
  if ← (← getMainGoal).isAssigned then
    throwError "dispatcher did not restore the metavariable assignment"
  logInfo "the accepting elaborator ran after fallback"
  evalTactic (← `(tactic| trivial))

@[tactic bookFallback]
def decliningBookFallback : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  g.assign (← mkLabeledSorry (← g.getType) (synthetic := true) (unique := true))
  setGoals []
  throwUnsupportedSyntax

example : True := by
  book_fallback
-- ANCHOR_END: tacticm_dispatch_fallback

-- ANCHOR: tacticm_book_all_goals
syntax "book_all_goals " tacticSeq : tactic

elab_rules : tactic
  | `(tactic| book_all_goals $seq:tacticSeq) => do
      let saved ← saveState
      Tactic.tryCatch
        (do
          let original ← getGoals
          let mut residual := []
          for g in original do
            setGoals [g]
            evalTactic seq
            residual := residual ++ (← getGoals)
          setGoals residual)
        (fun e => do
          saved.restore
          throw e)

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  book_all_goals assumption
-- ANCHOR_END: tacticm_book_all_goals

end tacticbook_tacticm
