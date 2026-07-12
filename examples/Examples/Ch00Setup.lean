import SubVerso.Examples
import Mathlib.Tactic

open Lean Elab Tactic Meta

-- ANCHOR: basic_test
#check Nat.add_comm
#eval 2 + 3
-- ANCHOR_END: basic_test

-- ANCHOR: norm_num_example
example : 2 + 3 = 5 := by norm_num
-- ANCHOR_END: norm_num_example

-- ANCHOR: simp_example
example (x : ℝ) : x + 0 = x := by simp
-- ANCHOR_END: simp_example
