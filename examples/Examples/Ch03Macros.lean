import SubVerso.Examples
import Lean
import Mathlib.Tactic
open Lean

namespace tacticbook_macros
-- ANCHOR: macro_XOR
macro:10 l:term:10 " XOR " r:term:11 : term => `((!$l && $r) || ($l && !$r))

#eval true XOR true -- false
#eval true XOR false -- true
#eval false XOR true -- true
#eval false XOR false -- false
-- ANCHOR_END: macro_XOR

-- ANCHOR: macro_desugering1
syntax:10 term:10 " XOR₁ " term:11 : term

macro_rules
  | `($l:term XOR₁ $r:term) => `((!$l && $r) || ($l && !$r))
-- ANCHOR_END: macro_desugering1

-- ANCHOR: macro_desugering2
syntax:10 (name := xor2) term:10 " XOR₂ " term:11 : term

@[macro xor2] def xor₂ : Macro
  | `($l:term XOR₂ $r:term) => `((!$l && $r) || ($l && !$r))
  | _ => Macro.throwUnsupported
-- ANCHOR_END: macro_desugering2


-- ANCHOR: macro_rules_trivial
syntax "mytrivial" : tactic -- 避免与`trivial`冲突，用一个新名字

macro_rules | `(tactic| mytrivial) => `(tactic| assumption)
macro_rules | `(tactic| mytrivial) => `(tactic| rfl)
macro_rules | `(tactic| mytrivial) => `(tactic| contradiction)
macro_rules | `(tactic| mytrivial) => `(tactic| decide)
macro_rules | `(tactic| mytrivial) => `(tactic| apply True.intro)
macro_rules | `(tactic| mytrivial) => `(tactic| apply And.intro <;> mytrivial)
-- ANCHOR_END: macro_rules_trivial

-- ANCHOR: macro_trivial
macro "mytrivial₁" : tactic =>
  `(tactic| first  -- 也可以不换行
    | apply True.intro
    | decide
    | contradiction
    | rfl
    | assumption)
-- ANCHOR_END: macro_trivial
end tacticbook_macros
