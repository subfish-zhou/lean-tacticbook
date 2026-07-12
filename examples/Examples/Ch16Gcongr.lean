import SubVerso.Examples
import Mathlib.Tactic
open Lean Elab Tactic Meta

-- ANCHOR: gcongrBasic
example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by gcongr

example (a b : ℝ) (h : a ≤ b) : a + 1 ≤ b + 1 := by gcongr

example (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 3 ≤ b ^ 3 := by gcongr
-- ANCHOR_END: gcongrBasic

-- ANCHOR: gcongrTwoPositions
example (a b c d : ℝ) (h1 : a ≤ b) (h2 : c ≤ d)
    (ha : 0 ≤ a) (hc : 0 ≤ c) : a * c ≤ b * d := by
  have hb : 0 ≤ b := le_trans ha h1
  gcongr
-- ANCHOR_END: gcongrTwoPositions

-- ANCHOR: gcongrArithmetic
example (a b c d : ℝ) (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by gcongr

example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by gcongr
example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by gcongr

example (a b : ℝ) (ha : 0 ≤ a) (h : a ≤ b) : a ^ 5 ≤ b ^ 5 := by gcongr
-- ANCHOR_END: gcongrArithmetic

-- ANCHOR: gcongrSetsAndSums
example (s t : Set ℝ) (h : s ⊆ t) (f : ℝ → ℝ) : f '' s ⊆ f '' t := by gcongr

example (s : Finset ℕ) (f g : ℕ → ℝ) (h : ∀ i ∈ s, f i ≤ g i) :
    s.sum f ≤ s.sum g := by gcongr; exact h _ ‹_›
-- ANCHOR_END: gcongrSetsAndSums

-- ANCHOR: gcongrPatternTemplates
example (a b c d : ℝ) (h1 : a ≤ b) (h2 : c ≤ d) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    a * c ≤ b * d := by
  have hb : 0 ≤ b := le_trans ha h1
  gcongr ?_ * ?_

example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  gcongr ?_ * c

example (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : (a + 1) ^ 2 ≤ (b + 1) ^ 2 := by
  gcongr (?_ + 1) ^ 2
-- ANCHOR_END: gcongrPatternTemplates

-- ANCHOR: gcongrCalcTransitivity
example (a b c : ℝ) (h1 : a ≤ b) (h2 : b ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 ≤ c ^ 2 := by
  calc a ^ 2
      ≤ b ^ 2 := by gcongr
    _ ≤ c ^ 2 := by gcongr
-- ANCHOR_END: gcongrCalcTransitivity

-- ANCHOR: gcongrCalcMixed
example (a b c : ℝ) (h1 : a < b) (h2 : b ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 < c ^ 2 := by
  calc a ^ 2
      < b ^ 2 := by gcongr
    _ ≤ c ^ 2 := by gcongr
-- ANCHOR_END: gcongrCalcMixed

-- ANCHOR: gcongrSideConditions
example (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) : x ^ 3 ≤ y ^ 3 := by
  gcongr
-- ANCHOR_END: gcongrSideConditions

-- ANCHOR: gcongrExplicitSideConditions
example (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    x ^ 2 * (x + 1) ≤ y ^ 2 * (y + 1) := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  gcongr <;> linarith
-- ANCHOR_END: gcongrExplicitSideConditions

-- ANCHOR: gcongrQuery
example (a b : ℝ) (h : a ≤ b) (ha : 0 ≤ a) : a ^ 2 ≤ b ^ 2 := by
  gcongr
-- ANCHOR_END: gcongrQuery
