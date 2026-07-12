import SubVerso.Examples
import Mathlib.Tactic
open Lean Elab Tactic Meta

namespace SimpLemmaDemo
-- ANCHOR: simpLemmaEquality
@[simp] theorem add_zero (n : Nat) : n + 0 = n := by omega
-- simp 看到 ?n + 0 就替换为 ?n
-- ANCHOR_END: simpLemmaEquality
end SimpLemmaDemo

-- ANCHOR: simpBackward
example (a b : Nat) (h : a = b + 1) : b + 1 = a := by
  simp [← h]
-- ANCHOR_END: simpBackward

-- ANCHOR: simpOnly
example (n : Nat) : n + 0 + 0 = n := by
  simp only [Nat.add_zero]
-- ANCHOR_END: simpOnly

-- ANCHOR: simpAll
example (a b : Nat) (h1 : a = 0) (h2 : a + b = 5) : b = 5 := by
  simp_all
-- ANCHOR_END: simpAll

-- ANCHOR: dsimpBetaReduce
example : (fun x => x + 1) 3 = 4 := by
  dsimp  -- beta 规约后 rfl
-- ANCHOR_END: dsimpBetaReduce

-- ANCHOR: simpDischarger
example (n : Nat) (h : n > 0) : n - 1 + 1 = n := by
  simp (dsimp := false) (discharger := omega)
-- ANCHOR_END: simpDischarger

-- ANCHOR: contextualSimp
example (p : Prop) [Decidable p] (h : p) (a b : Nat) :
    (if p then a else b) = a := by
  simp [h]
-- ANCHOR_END: contextualSimp

-- ANCHOR: traceSimpRewrite
set_option trace.Meta.Tactic.simp.rewrite true in
example : 0 + 1 = 1 := by simp
-- ANCHOR_END: traceSimpRewrite

-- ANCHOR: traceSimpDischarge
set_option trace.Meta.Tactic.simp.discharge true in
example : 0 + 1 = 1 := by simp
-- ANCHOR_END: traceSimpDischarge

-- ANCHOR: simpQuestion
example : 0 + 1 = 1 := by simp only [Nat.zero_add]
-- simp? 会输出：Try this: simp only [Nat.zero_add]
-- ANCHOR_END: simpQuestion

namespace GoodSimpLemmaDemo
variable {α : Type*}
-- ANCHOR: goodSimpLemmas
@[simp] theorem length_nil : ([] : List α).length = 0 := rfl
@[simp] theorem length_cons (a : α) (l : List α) :
    (a :: l).length = l.length + 1 := rfl
-- ANCHOR_END: goodSimpLemmas
end GoodSimpLemmaDemo

-- ANCHOR: simpWithRw
example (a b : Nat) (h : a = b) : a + 0 = b := by
  rw [h]; simp
-- ANCHOR_END: simpWithRw

-- ANCHOR: simpWithConstructor
example : True ∧ (0 + 1 = 1) := by
  constructor
  · trivial
  · simp
-- ANCHOR_END: simpWithConstructor

-- ANCHOR: exercise1
-- 预测 simp 能否解决以下目标，然后验证。
example : [1, 2, 3].length = 3 := by
  sorry

example (n : Nat) : n + 0 + 0 + 0 = n := by
  sorry
-- ANCHOR_END: exercise1

-- ANCHOR: exercise2
-- 先用 simp? 找出需要的引理，再改写为 simp only 版本。
example (a b : Nat) : a + 0 + (b + 0) = a + b := by
  sorry
-- ANCHOR_END: exercise2

-- ANCHOR: exercise3
def double (n : Nat) := 2 * n

example : double 3 = 6 := by
  try simp  -- simp made no progress!
  sorry
-- ANCHOR_END: exercise3

-- ANCHOR: exercise4
example (n : Nat) (h : n > 0) :
    [n].length + (n - 1 + 1) = n + 1 := by
  sorry
-- ANCHOR_END: exercise4
