import SubVerso.Examples
import Mathlib.Tactic
open Lean Elab Tactic Meta

-- ANCHOR: profilerBasic
set_option profiler true in
theorem ex1 : (List.range 100).length = 100 := by decide
-- ANCHOR_END: profilerBasic

-- ANCHOR: profilerSimp
set_option profiler true in
theorem my_thm : ∀ n : ℕ, n + 0 = n := by
  intro n; simp
-- ANCHOR_END: profilerSimp
