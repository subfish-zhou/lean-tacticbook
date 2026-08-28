import SubVerso.Examples
import Lean
import Mathlib.Tactic
import Mathlib.Topology.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
open Lean Meta Elab Tactic

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

-- ANCHOR: macro_poly_roots_direct_quadratic
example (x : ℚ) : x^2 - 5*x + 6 = 0 ↔ x = 2 ∨ x = 3 := by
  rw [show x^2 - 5*x + 6 = (x - 2) * (x - 3) by ring]
  simp only [mul_eq_zero, sub_eq_zero]
-- ANCHOR_END: macro_poly_roots_direct_quadratic

-- ANCHOR: macro_poly_roots_direct_cubic
example (x : ℚ) :
    x^3 - 6*x^2 + 11*x - 6 = 0 ↔ x = 1 ∨ x = 2 ∨ x = 3 := by
  rw [show x^3 - 6*x^2 + 11*x - 6 = (x - 1) * ((x - 2) * (x - 3)) by ring]
  simp only [mul_eq_zero, sub_eq_zero]
-- ANCHOR_END: macro_poly_roots_direct_cubic

-- ANCHOR: macro_poly_roots_list_cubic
example (x : ℚ) :
    x^3 - 6*x^2 + 11*x - 6 = 0 ↔ x = 1 ∨ x = 2 ∨ x = 3 := by
  rw [show x^3 - 6*x^2 + 11*x - 6 =
      ([1, 2, 3].map (fun r => x - r)).prod by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    ring]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    mul_eq_zero, sub_eq_zero]
-- ANCHOR_END: macro_poly_roots_list_cubic

-- ANCHOR: macro_poly_roots
syntax "poly_roots " term " with " term " in " term : tactic

macro_rules
  | `(tactic| poly_roots $poly:term with $roots:term in $x:term) =>
      `(tactic|
          rw [show $poly = (($roots).map (fun r => $x - r)).prod by
            simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
            ring] <;>
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
            mul_eq_zero, sub_eq_zero])

example (x : ℚ) : x^2 - 5*x + 6 = 0 ↔ x = 2 ∨ x = 3 := by
  -- ANCHOR: elaboration_old_poly_roots_call
  poly_roots x^2 - 5*x + 6 with [2, 3] in x
  -- ANCHOR_END: elaboration_old_poly_roots_call

example (x : ℚ) :
    x^3 - 6*x^2 + 11*x - 6 = 0 ↔ x = 1 ∨ x = 2 ∨ x = 3 := by
  poly_roots x^3 - 6*x^2 + 11*x - 6 with [1, 2, 3] in x
-- ANCHOR_END: macro_poly_roots

-- ANCHOR: macro_poly_roots_1
syntax "poly_roots₁ " term " with " term:max+ " in " term : tactic

macro_rules
  | `(tactic| poly_roots₁ $poly:term with $roots:term* in $x:term) =>
      `(tactic
        | rw [show $poly = (([$roots,*]).map (fun r => $x - r)).prod by
            simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
            ring] <;>
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
            mul_eq_zero, sub_eq_zero])
example (x : ℚ) : x^2 - 5*x + 6 = 0 ↔ x = 2 ∨ x = 3 := by
  poly_roots₁ x^2 - 5*x + 6 with 2 3 in x
-- ANCHOR_END: macro_poly_roots_1

-- ANCHOR: macro_poly_roots_both
syntax "poly_roots_both " term " with " term:max+ " in " term : tactic

macro_rules
  | `(tactic| poly_roots_both $poly:term with [$roots,*] in $x:term) =>
      `(tactic| poly_roots $poly with [$roots,*] in $x)
  | `(tactic| poly_roots_both $poly:term with $roots:term* in $x:term) =>
      `(tactic| poly_roots $poly with [$roots,*] in $x)

example (x : ℚ) : x^2 - 5*x + 6 = 0 ↔ x = 2 ∨ x = 3 := by
  poly_roots_both x^2 - 5*x + 6 with [2, 3] in x

example (x : ℚ) : x^2 - 5*x + 6 = 0 ↔ x = 2 ∨ x = 3 := by
  poly_roots_both x^2 - 5*x + 6 with 2 3 in x
-- ANCHOR_END: macro_poly_roots_both

-- ANCHOR: macro_environment_query
namespace MacroEnvironmentDemo

def answer := 42

syntax "#resolve_decl " ident : command

macro_rules
  | `(#resolve_decl $name:ident) => do
      -- ANCHOR: macro_environment_namespace
      let ns ← Macro.getCurrNamespace
      -- ANCHOR_END: macro_environment_namespace
      -- ANCHOR: macro_environment_candidates
      let candidates ← Macro.resolveGlobalName name.getId
      -- ANCHOR_END: macro_environment_candidates
      let some (declName, projections) := candidates.head?
        | Macro.throwErrorAt name
            s!"unknown declaration `{name.getId}` in namespace `{ns}`"
      unless projections.isEmpty do
        Macro.throwErrorAt name
          s!"`{name.getId}` was parsed using field notation"
      unless ← Macro.hasDecl declName do
        Macro.throwErrorAt name
          s!"resolved name `{declName}` is not a declaration"
      -- ANCHOR: macro_environment_resolved
      let resolved := mkIdentFrom name declName
      -- ANCHOR_END: macro_environment_resolved
      `(command| #check $resolved)

#resolve_decl answer

end MacroEnvironmentDemo
-- ANCHOR_END: macro_environment_query
/-- error: unsolved goals -/
#guard_msgs (substring := true) in
example (x : ℚ) : x^2 - 5*x + 6 = 0 ↔ x = 2 ∨ x = 4 := by
  poly_roots₁ x^2 - 5*x + 6 with 2 4 in x

/-- error: unsolved goals -/
#guard_msgs (substring := true) in
example (x : ℚ) : x^2 - 5*x + 6 = 0 ↔ x = 3 ∨ x = 2 := by
  poly_roots₁ x^2 - 5*x + 6 with 2 3 in x

-- ANCHOR: macro_defnat
macro "defNat " n:ident " := " v:term : command =>
  `(def $n : Nat := $v)

defNat answer := 42
#check answer
-- ANCHOR_END: macro_defnat

-- ANCHOR: macro_list_demo
syntax:max "listDemo[" term,* "]" : term
macro_rules
  | `(listDemo[$xs,*]) => `([$xs,*])

example : listDemo[1, 2, 3] = ([1, 2, 3] : List Nat) := rfl
-- ANCHOR_END: macro_list_demo

-- ANCHOR: macro_first_rule
open Lean Macro

syntax:max "firstRule" : term

macro_rules
  | `(firstRule) => `(41 + 1)

macro_rules
  | `(firstRule) => Macro.throwUnsupported

example : firstRule = 42 := rfl
-- ANCHOR_END: macro_first_rule

-- ANCHOR: macro_tactic_fallback
syntax "fallbackTac" : tactic

macro_rules
  | `(tactic| fallbackTac) => `(tactic| assumption)

macro_rules
  | `(tactic| fallbackTac) => `(tactic| exact True.intro)

example (P : Prop) (h : P) : P := by
  fallbackTac
-- ANCHOR_END: macro_tactic_fallback

-- ANCHOR: macro_builtin_examples
example (P : Prop) (h : False) : P := by
  exfalso
  exact h

example : Nonempty Nat := by
  infer_instance

example (x y : Rat) (h : x ≤ y) : x ≤ y + 1 := by
  linarith!
-- ANCHOR_END: macro_builtin_examples

-- ANCHOR: macro_controller_examples
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor <;> assumption

example : (1 : Int) + 2 = 3 := by
  ring
-- ANCHOR_END: macro_controller_examples

-- ANCHOR: macro_trivial_use
example (P : Prop) (h : P) : P := by
  trivial

example : True ∧ True := by
  trivial
-- ANCHOR_END: macro_trivial_use

-- ANCHOR: macro_builtin_recursion
example (n : Nat) (h : n > 0) : n - 1 < n := by
  decreasing_trivial

example (n : Nat) : n = n := by
  iterate 1 rfl
-- ANCHOR_END: macro_builtin_recursion

-- ANCHOR: macro_loop_tac
syntax "loopTac" : tactic
macro_rules
  | `(tactic| loopTac) => `(tactic| loopTac)
-- ANCHOR_END: macro_loop_tac

-- ANCHOR: macro_hygienic_let
macro "hygienicLet(" t:term ")" : term =>
  `(let x := 0; ($t, x))

example (x : Nat) : hygienicLet(x + 1) = (x + 1, 0) := rfl
-- ANCHOR_END: macro_hygienic_let

-- ANCHOR: macro_identity_let
macro "identityLet(" n:ident ", " t:term ")" : term =>
  `(let $n := $t; $n)

example : identityLet(y, 7) = 7 := rfl
-- ANCHOR_END: macro_identity_let

-- ANCHOR: macro_external_examples
example : Continuous (fun x : Real => x) := by
  continuity

example : Measurable (fun x : Real => x) := by
  measurability
-- ANCHOR_END: macro_external_examples

-- ANCHOR: macro_trace_use
syntax:max "twiceTrace(" term ")" : term
macro_rules
  | `(twiceTrace($t)) => do
      Macro.trace `Elab.step "expanding twiceTrace"
      `($t + $t)

set_option trace.Elab.step true in
#check twiceTrace(2)
-- ANCHOR_END: macro_trace_use


end tacticbook_macros
