import SubVerso.Examples
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
open Lean Elab Tactic Meta

-- ANCHOR: funPropBasic
example : Continuous (fun x : ℝ => x ^ 2 + 3 * x + 1) := by fun_prop

example : Differentiable ℝ (fun x : ℝ => Real.exp (x ^ 2)) := by fun_prop

example : Measurable (fun x : ℝ => x + 1) := by fun_prop
-- ANCHOR_END: funPropBasic

-- ANCHOR: funPropLegacy
example : Continuous (fun x : ℝ => x ^ 2 + 1) := by fun_prop
example : Continuous (fun x : ℝ => x ^ 2 + 1) := by continuity
example : Measurable (fun x : ℝ => x + 1) := by fun_prop
example : Measurable (fun x : ℝ => x + 1) := by measurability
-- ANCHOR_END: funPropLegacy

-- ANCHOR: funPropNested
example : Continuous (fun x : ℝ => Real.exp (Real.sin (x ^ 2))) := by fun_prop
-- ANCHOR_END: funPropNested

-- ANCHOR: funPropMultiProperty
example : Continuous (fun x : ℝ => x ^ 2 + 1) := by fun_prop
example : Differentiable ℝ (fun x : ℝ => x ^ 3 - x) := by fun_prop
example : Measurable (fun x : ℝ => x * 2) := by fun_prop
-- ANCHOR_END: funPropMultiProperty

-- ANCHOR: funPropCustomDef
noncomputable def quadratic (a b c x : ℝ) : ℝ := a * x ^ 2 + b * x + c

example (a b c : ℝ) : Continuous (quadratic a b c) := by
  unfold quadratic
  fun_prop
-- ANCHOR_END: funPropCustomDef

-- ANCHOR: funPropDisch
example (x : ℝ) (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun y : ℝ => 1 / y) x := by
  fun_prop (disch := assumption)
-- ANCHOR_END: funPropDisch

-- ANCHOR: funPropSimp
example : Continuous (fun x : ℝ => x + 0) := by
  fun_prop
-- ANCHOR_END: funPropSimp

-- ANCHOR: funPropGaussian
example : Continuous (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) := by fun_prop
-- ANCHOR_END: funPropGaussian
