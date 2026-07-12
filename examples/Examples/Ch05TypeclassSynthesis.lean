import SubVerso.Examples
import Mathlib.Tactic
open Lean Elab Tactic Meta

-- ANCHOR: instancePriority
inductive MyType where
  | mk

instance (priority := 2000) myTypeToStringHigh : ToString MyType where
  toString _ := "MyType(high)"

instance (priority := 100) myTypeToStringLow : ToString MyType where
  toString _ := "MyType(low)"
-- ANCHOR_END: instancePriority

-- ANCHOR: synthInstanceMaxHeartbeats
structure MyComplexType where
  val : Nat

instance : Add MyComplexType where
  add a b := ⟨a.val + b.val⟩

set_option synthInstance.maxHeartbeats 40000 in
example : Add (MyComplexType × MyComplexType) := inferInstance
-- ANCHOR_END: synthInstanceMaxHeartbeats

-- ANCHOR: noInstanceFound
structure Point where
  x : Nat
  y : Nat

-- 忘记注册实例：
-- instance : Add Point where
--   add p q := ⟨p.x + q.x, p.y + q.y⟩

-- 下面会报错：failed to synthesize Add Point
-- #check (inferInstance : Add Point)
-- ANCHOR_END: noInstanceFound

-- ANCHOR: traceSynthInstance
set_option trace.Meta.synthInstance true in
#check (inferInstance : Add Nat)
-- ANCHOR_END: traceSynthInstance
