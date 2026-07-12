import SubVerso.Examples
import Mathlib.Tactic
open Lean Elab Tactic Meta

-- ANCHOR: rotateGoals
elab "rotate_goals" : tactic => do
  sorry -- 你的实现
-- ANCHOR_END: rotateGoals

-- ANCHOR: countGoals
elab "count_goals" : tactic => do
  sorry -- 你的实现
-- ANCHOR_END: countGoals

-- ANCHOR: tryAssumptionAll
elab "try_assumption_all" : tactic => do
  let goals ← getGoals
  for g in goals do
    try
      evalTactic (← `(tactic| assumption))
    catch _ =>
      pure ()
  -- Bug 在哪里？
-- ANCHOR_END: tryAssumptionAll
