import SubVerso.Examples
import Mathlib

namespace tacticbook_grind

-- ANCHOR: grind_congruence
theorem grindCongruence (α : Type) (f : α → α) (a b : α)
    (h : a = b) : f (f a) = f (f b) := by
  grind
-- ANCHOR_END: grind_congruence

-- ANCHOR: grind_ematch
theorem grindEMatch (α : Type) (f : α → α) (a : α)
    (h : ∀ x, f x = x) : f (f a) = a := by
  grind
-- ANCHOR_END: grind_ematch

-- ANCHOR: grind_solver_cooperation
theorem grindCooperation (x y : Int) (h₁ : x ≤ y) (h₂ : y ≤ x)
    (P : Prop) (hP : x = y → P) : P := by
  grind
-- ANCHOR_END: grind_solver_cooperation

-- ANCHOR: grind_split
theorem grindSplit (P Q : Prop) : P ∨ Q → Q ∨ P := by
  grind
-- ANCHOR_END: grind_split

-- ANCHOR: grind_trace_assert
set_option trace.grind.assert true in
theorem grindTrace (α : Type) (f : α → α) (a : α)
    (h : ∀ x, f x = x) : f (f a) = a := by
  grind
-- ANCHOR_END: grind_trace_assert

-- ANCHOR: grind_question
theorem grindQuestion (P Q : Prop) : P ∧ Q → Q ∧ P := by
  grind?
-- ANCHOR_END: grind_question

-- ANCHOR: grind_axiom_probe
#print axioms grindCongruence
#print axioms grindEMatch
#print axioms grindCooperation
-- ANCHOR_END: grind_axiom_probe

end tacticbook_grind
