import SubVerso.Examples
import Mathlib.Tactic
open Lean Elab Tactic Meta

-- ANCHOR: grindTransitivity
example {α : Type*} {a b c : α} (h1 : a = b) (h2 : b = c) : a = c := by
  grind
-- ANCHOR_END: grindTransitivity

-- ANCHOR: grindCongruence
example {α : Type*} {β : Type*} {a b : α} {f : β → β} {g : α → β}
    (h : a = b) : f (g a) = f (g b) := by
  grind
-- ANCHOR_END: grindCongruence

-- ANCHOR: grindMultiStep
example {α : Type*} {a b c d : α} {f : α → α}
    (h1 : f a = b) (h2 : f b = c) (h3 : a = d) : f (f d) = c := by
  grind
-- ANCHOR_END: grindMultiStep

-- ANCHOR: grindWithLemma
example {α : Type*} {a b : α} {f : α → α} (h : a = f b) : f a = b := by
  have aux : ∀ x, f (f x) = x := sorry
  grind
-- ANCHOR_END: grindWithLemma

-- ANCHOR: grindPreprocessor
example {α : Type*} {a b c : α} (h : a = b ∧ b = c) : a = c := by
  grind
-- ANCHOR_END: grindPreprocessor

-- ANCHOR: grindFunctionComposition
example {α : Type*} {β : Type*} {γ : Type*} (f : α → β) (g : β → γ)
    {a b c : α} (h1 : a = b) (h2 : b = c) : g (f a) = g (f c) := by
  grind
-- ANCHOR_END: grindFunctionComposition

-- ANCHOR: grindWithCases
example {α : Type*} {a b c d : α}
    (h : a = b ∨ a = c) (h2 : b = d) (h3 : c = d) : a = d := by
  cases h with
  | inl h => grind
  | inr h => grind
-- ANCHOR_END: grindWithCases

-- ANCHOR: grindNoWitness
-- grind 不做 witness 搜索
example : ∃ x : Nat, x + 1 = 2 := by
  exact ⟨1, rfl⟩
-- ANCHOR_END: grindNoWitness

-- ANCHOR: grindNoUnfold
-- grind 不自动展开用户定义
def myf (n : Nat) : Nat := n + 1

example : myf (myf 0) = 2 := by
  unfold myf; omega
-- ANCHOR_END: grindNoUnfold

-- ANCHOR: grindBestScenario
example {α : Type*} {β : Type*} {a b c d e : α} {f : β → β} {g : α → β}
    (h1 : a = b) (h2 : b = c) (h3 : c = d) (h4 : d = e) :
    f (g a) = f (g e) := by
  grind
-- ANCHOR_END: grindBestScenario
