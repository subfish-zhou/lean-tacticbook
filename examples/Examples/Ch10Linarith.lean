import SubVerso.Examples
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

namespace tacticbook_linarith

-- ANCHOR: linarith_basic
theorem antisymmByLinarith (x y : ℚ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  linarith
-- ANCHOR_END: linarith_basic

-- ANCHOR: linarith_strict_certificate
theorem strictContradiction (x y : ℚ) (h₁ : x < y) (h₂ : y ≤ x) : False := by
  linarith only [h₁, h₂]
-- ANCHOR_END: linarith_strict_certificate

-- ANCHOR: linarith_manual_reading
theorem weightedContradiction (x : ℚ) (h₁ : x ≤ 3) (h₂ : 5 ≤ x) : False := by
  linarith only [h₁, h₂]
-- ANCHOR_END: linarith_manual_reading

-- ANCHOR: linarith_linear_combination
theorem explicitLinearCombination (x y : ℚ)
    (h₁ : x + y = 5) (h₂ : x - y = 1) : 2*x = 6 := by
  linear_combination h₁ + h₂
-- ANCHOR_END: linarith_linear_combination

-- ANCHOR: linarith_trace
set_option trace.linarith true in
theorem tracedLinear (x y : ℚ) (h₁ : 2*x + y ≤ 3) (h₂ : 4 ≤ x + y) : x ≤ -1 := by
  linarith
-- ANCHOR_END: linarith_trace

-- ANCHOR: linarith_monomial_as_atom
theorem monomialCancellation (x y : ℚ) (h₁ : x*y ≤ 0) (h₂ : 1 ≤ x*y) : False := by
  linarith
-- ANCHOR_END: linarith_monomial_as_atom

-- ANCHOR: linarith_nonlinear_boundary
example (x : ℚ) (h : x^2 ≤ 0) : x = 0 := by
  fail_if_success linarith
  nlinarith
-- ANCHOR_END: linarith_nonlinear_boundary

-- ANCHOR: linarith_integer_strict
example (x y : ℤ) (h : x < y) : x + 1 ≤ y := by
  linarith
-- ANCHOR_END: linarith_integer_strict

-- ANCHOR: linarith_axiom_probe
#print axioms antisymmByLinarith
#print axioms strictContradiction
-- ANCHOR_END: linarith_axiom_probe

end tacticbook_linarith
