import SubVerso.Examples
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace tacticbook_ring

-- ANCHOR: ring_identity
theorem ringIdentity (x y : ℤ) :
    (x + y)^2 = x^2 + 2*x*y + y^2 := by
  ring
-- ANCHOR_END: ring_identity

-- ANCHOR: ring_unknown_atoms
theorem ringUnknownAtoms (f : ℤ → ℤ) (x : ℤ) :
    (f x + 1)^2 = (f x)^2 + 2 * f x + 1 := by
  ring
-- ANCHOR_END: ring_unknown_atoms

-- ANCHOR: ring_nf_hypothesis
theorem ringNfHypothesis (x y : ℤ) (h : (x + y)^2 = 0) :
    x^2 + 2*x*y + y^2 = 0 := by
  ring_nf at h ⊢
  exact h
-- ANCHOR_END: ring_nf_hypothesis

-- ANCHOR: ring_normalized_residual
example (x y : ℤ) : x * (y + 1) = x*y + x := by
  ring_nf
-- ANCHOR_END: ring_normalized_residual

-- ANCHOR: ring_division_boundary
example (x : ℚ) (hx : x ≠ 0) : x / x = 1 := by
  ring
  field_simp
-- ANCHOR_END: ring_division_boundary

-- ANCHOR: ring_toy_normalizer
inductive ToyExpr where
  | var
  | const (z : ℤ)
  | add (lhs rhs : ToyExpr)
  | mul (lhs rhs : ToyExpr)

def ToyExpr.eval : ToyExpr → ℤ → ℤ
  | .var, x => x
  | .const z, _ => z
  | .add lhs rhs, x => lhs.eval x + rhs.eval x
  | .mul lhs rhs, x => lhs.eval x * rhs.eval x

noncomputable def ToyExpr.toPoly : ToyExpr → Polynomial ℤ
  | .var => Polynomial.X
  | .const z => Polynomial.C z
  | .add lhs rhs => lhs.toPoly + rhs.toPoly
  | .mul lhs rhs => lhs.toPoly * rhs.toPoly

theorem ToyExpr.eval_toPoly (e : ToyExpr) (x : ℤ) :
    e.toPoly.eval x = e.eval x := by
  induction e <;> simp_all [ToyExpr.toPoly, ToyExpr.eval]
-- ANCHOR_END: ring_toy_normalizer

-- ANCHOR: ring_axiom_probe
#print axioms ringIdentity
#print axioms ringUnknownAtoms
-- ANCHOR_END: ring_axiom_probe

end tacticbook_ring
