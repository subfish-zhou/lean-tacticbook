import SubVerso.Examples
import Mathlib.Tactic
open Lean Elab Tactic Meta

-- ANCHOR: decidableChecks
#check (inferInstance : Decidable (3 = 5))
#check (inferInstance : Decidable (3 < 5))
#check (inferInstance : Decidable (5 ∈ [1,2,3]))
-- ANCHOR_END: decidableChecks

-- ANCHOR: decideBasic
example : 2 + 2 = 4 := by decide

example : ¬ (3 ∈ [1, 2, 5]) := by decide

example : Nat.Prime 7 := by decide

example : ∀ b : Bool, b || !b = true := by decide
-- ANCHOR_END: decideBasic

-- ANCHOR: nativeDecide
example : Nat.Prime 104729 := by native_decide

example : ∀ n : Fin 256, n.val < 256 := by native_decide

example : ((List.range 100).filter Nat.Prime).length = 25 := by native_decide
-- ANCHOR_END: nativeDecide

-- ANCHOR: derivingDecidableEq
inductive Color where
  | red | green | blue
  deriving DecidableEq

example : Color.red ≠ Color.blue := by decide
-- ANCHOR_END: derivingDecidableEq

namespace DecideDvdDemo
-- ANCHOR: decidableDvd
instance (n m : Nat) : Decidable (n ∣ m) :=
  if h : m % n = 0
  then .isTrue (Nat.dvd_of_mod_eq_zero h)
  else .isFalse fun ⟨k, hk⟩ =>
    h (by omega)
-- ANCHOR_END: decidableDvd
end DecideDvdDemo

-- ANCHOR: decidableIsEven
def IsEven (n : Nat) : Prop := n % 2 = 0

instance (n : Nat) : Decidable (IsEven n) :=
  inferInstanceAs (Decidable (n % 2 = 0))
-- ANCHOR_END: decidableIsEven

-- ANCHOR: decidableComposite
example : Decidable (3 < 5 ∧ 7 ≠ 8) := inferInstance
example : Decidable (∀ i : Fin 5, i.val < 10) := inferInstance
example : Decidable (∃ i : Fin 5, i.val = 3) := inferInstance
-- ANCHOR_END: decidableComposite

-- ANCHOR: decideTacticComparison
example : 100 < 200 := by omega
example : 100 < 200 := by decide

example : Nat.Prime 104729 := by norm_num
example : (2 : ℤ) ^ 10 = 1024 := by norm_num

example (n : Nat) : n + 0 = n := by simp
-- example (n : Nat) : n + 0 = n := by decide  -- ✗ n 不是字面量
-- ANCHOR_END: decideTacticComparison

-- ANCHOR: decideFiniteVerification
example : ∀ a b : Fin 3, a + b = b + a := by decide

example : ∀ a b : Fin 20, a + b = b + a := by native_decide
-- ANCHOR_END: decideFiniteVerification

-- ANCHOR: intervalCasesDecide
example (n : ℕ) (h : n < 3) : n * n < 10 := by
  interval_cases n
  all_goals decide
-- ANCHOR_END: intervalCasesDecide

-- ANCHOR: decideLocalLemma
example : True := by
  have h₁ : Nat.Prime 7 := by decide
  have h₂ : 7 ∈ [2, 3, 5, 7] := by decide
  trivial
-- ANCHOR_END: decideLocalLemma
