import SubVerso.Examples
import Mathlib.Tactic
open Lean Elab Tactic Meta

-- ANCHOR: fieldSimpBasic
example (x : ℝ) (hx : x ≠ 0) : 1 / x * x = 1 := by field_simp

example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    1/a + 1/b = (a + b) / (a * b) := by
  field_simp
  ring

example (x : ℝ) (hx : x ≠ 0) : (x ^ 2 - 1) / x = x - 1 / x := by
  field_simp
-- ANCHOR_END: fieldSimpBasic

-- ANCHOR: fieldSimpNonzeroSources
example (x : ℝ) (hx : x ≠ 0) : 1 / x * x = 1 := by field_simp

example (x : ℝ) (hx : 0 < x) : 1 / x + 1 = (x + 1) / x := by
  field_simp; ring

example (x : ℝ) : x / 2 + x / 3 = 5 * x / 6 := by
  field_simp; ring

example (x y : ℝ) (h : x + y ≠ 0) :
    1 / (x + y) * (x + y) = 1 := by
  field_simp [h]
-- ANCHOR_END: fieldSimpNonzeroSources

-- ANCHOR: fieldSimpThenRing
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    1/a - 1/b = (b - a) / (a * b) := by
  field_simp
-- ANCHOR_END: fieldSimpThenRing

-- ANCHOR: fieldSimpDirect
example (x : ℝ) (hx : x ≠ 0) : x / x = 1 := by
  field_simp
-- ANCHOR_END: fieldSimpDirect

-- ANCHOR: fieldSimpSupplementary
example (a : ℝ) (ha : a ≠ 0) : (a + 1/a) ^ 2 = a ^ 2 + 2 + 1/a ^ 2 := by
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  field_simp
  ring
-- ANCHOR_END: fieldSimpSupplementary

-- ANCHOR: fieldSimpThreeFractions
example (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    1/a + 1/b + 1/c = (b*c + a*c + a*b) / (a*b*c) := by
  field_simp
-- ANCHOR_END: fieldSimpThreeFractions

-- ANCHOR: fieldSimpInequalities
example (x : ℝ) (hx : 1 < x) : 1 / x < 1 := by
  rw [div_lt_one (by linarith : (0 : ℝ) < x)]
  exact hx

example (x : ℝ) (hx : 0 < x) : x / (x ^ 2 + 1) ≤ 1 := by
  rw [div_le_one (by positivity : (0 : ℝ) < x ^ 2 + 1)]
  nlinarith [sq_nonneg (x - 1)]
-- ANCHOR_END: fieldSimpInequalities

-- ANCHOR: fieldSimpCast
example (n : ℕ) (hn : (n : ℝ) ≠ 0) :
    (↑(n + 1) : ℝ) / ↑n = 1 + 1 / ↑n := by
  push_cast; field_simp [hn]
-- ANCHOR_END: fieldSimpCast

-- ANCHOR: fieldSimpExplicitHyp
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) :
    1 / (a + b) + 1 / a = (2 * a + b) / (a * (a + b)) := by
  field_simp [hab]; ring
-- ANCHOR_END: fieldSimpExplicitHyp
