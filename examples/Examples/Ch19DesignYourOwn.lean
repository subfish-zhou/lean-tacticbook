import SubVerso.Examples
import Mathlib.Tactic
open Lean Elab Tactic Meta

-- ANCHOR: exercise_simp_lemma
example (s t : Finset ℕ) : (s ∪ t).card ≤ s.card + t.card := by
  sorry

example (s : Finset ℕ) : (s ∩ s) = s := by
  sorry
-- ANCHOR_END: exercise_simp_lemma
