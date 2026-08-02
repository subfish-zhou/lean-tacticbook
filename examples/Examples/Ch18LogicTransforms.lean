import SubVerso.Examples
import Mathlib.Tactic
open Lean Elab Tactic Meta

-- ANCHOR: pushNegEpsilonDelta
example (f : ℝ → ℝ) (a : ℝ) :
    ¬(∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε) ↔
    ∃ ε > 0, ∀ δ > 0, ∃ x, |x - a| < δ ∧ ε ≤ |f x - f a| := by
  constructor
  · intro h
    push Not at h
    exact h
  · intro h
    push Not
    exact h
-- ANCHOR_END: pushNegEpsilonDelta

-- ANCHOR: contraposeDvd
example (a b : ℤ) : a ∣ b → b ≠ 0 → a ≠ 0 := by
  intro hdvd
  contrapose
  intro ha
  simp [ha] at hdvd
  exact hdvd
-- ANCHOR_END: contraposeDvd

-- ANCHOR: contraposeSquare
example (n : ℕ) : n < 3 → n ^ 2 < 9 := by
  contrapose!
  intro h
  nlinarith
-- ANCHOR_END: contraposeSquare

-- ANCHOR: byContraUnbounded
example : ∀ n : ℕ, ∃ m, m > n := by
  by_contra! h
  obtain ⟨n, hn⟩ := h
  have := hn (n + 1)
  omega
-- ANCHOR_END: byContraUnbounded

-- ANCHOR: pushNegConvergence
example (a : ℕ → ℝ) (L : ℝ)
    (h : ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε) :
    ¬(∃ ε > 0, ∀ N, ∃ n ≥ N, ε ≤ |a n - L|) := by
  push Not
  exact h
-- ANCHOR_END: pushNegConvergence

-- ANCHOR: contraposeStrictMono
example (f : ℝ → ℝ) (hf : StrictMono f) (a b : ℝ) :
    f a = f b → a = b := by
  contrapose!
  exact fun h => hf.injective.ne h
-- ANCHOR_END: contraposeStrictMono

-- ANCHOR: byContraEpsilon
example (a b : ℝ) (h : ∀ ε > 0, a ≤ b + ε) : a ≤ b := by
  by_contra h'
  push Not at h'
  have := h ((a - b) / 2) (by linarith)
  linarith
-- ANCHOR_END: byContraEpsilon

-- ANCHOR: byContraNlinarith
example (n : ℕ) (h : n ^ 2 < 2 * n) : n < 2 := by
  by_contra! h'
  nlinarith [sq_nonneg (n - 2)]
-- ANCHOR_END: byContraNlinarith
