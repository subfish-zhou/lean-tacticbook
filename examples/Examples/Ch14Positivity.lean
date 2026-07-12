import SubVerso.Examples
import Mathlib.Tactic
open Lean Elab Tactic Meta

-- ANCHOR: positivityBasic
example (x : ℝ) : 0 ≤ x ^ 2 := by positivity

example (x : ℝ) (hx : 0 < x) : 0 < x + x ^ 2 := by positivity

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by positivity
-- ANCHOR_END: positivityBasic

-- ANCHOR: positivityNonzero
example (x : ℝ) (hx : x ≠ 0) : 0 < x ^ 2 := by positivity
-- ANCHOR_END: positivityNonzero

-- ANCHOR: positivityCompound
example (x y : ℝ) (hx : 0 < x) (hy : 0 ≤ y) : 0 < x * (y + 1) := by positivity
-- ANCHOR_END: positivityCompound

-- ANCHOR: positivityArithmetic
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by positivity
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by positivity
example (a : ℝ) : 0 ≤ a ^ 4 := by positivity
example (a : ℝ) (ha : 0 ≤ a) : 0 ≤ a ^ 3 := by positivity
-- ANCHOR_END: positivityArithmetic

-- ANCHOR: positivitySpecialFunctions
example (x : ℝ) : 0 ≤ |x| := by positivity
example (x : ℝ) : 0 ≤ Real.sqrt x := by positivity
example (x : ℝ) : 0 < Real.exp x := by positivity
-- ANCHOR_END: positivitySpecialFunctions

-- ANCHOR: positivityCastAndDiv
example (n : ℕ) : 0 ≤ (n : ℝ) := by positivity
example (x : ℝ) (hx : 0 < x) : 0 < 1 / x := by positivity
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) : 0 ≤ x / y := by positivity
-- ANCHOR_END: positivityCastAndDiv

-- ANCHOR: positivityFinsetSum
example (s : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    0 ≤ s.sum f := Finset.sum_nonneg hf
-- ANCHOR_END: positivityFinsetSum

-- ANCHOR: positivityWithGcongr
example (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  gcongr
-- ANCHOR_END: positivityWithGcongr

-- ANCHOR: positivityWithLinarith
example (x : ℝ) (hx : 0 < x) : x / (x + 1) < 1 := by
  have h : 0 < x + 1 := by positivity
  rw [div_lt_one h]
  linarith
-- ANCHOR_END: positivityWithLinarith

-- ANCHOR: positivityComparison
example (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x ^ 2 + x := by positivity

example (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x ^ 2 + x := by nlinarith [sq_nonneg x]

example (a b : ℝ) (ha : 0 ≤ a) (hb : a ≤ b) : 0 ≤ b := by linarith
-- ANCHOR_END: positivityComparison

-- ANCHOR: positivityQuery
example (x : ℝ) (hx : 0 < x) : 0 < x + 1 := by positivity
-- ANCHOR_END: positivityQuery

-- ANCHOR: positivityWithLemmas
example (x : ℝ) (hx : 1 < x) : 0 < (x - 1) * x := by
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x := by linarith
  positivity
-- ANCHOR_END: positivityWithLemmas
