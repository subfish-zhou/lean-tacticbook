import SubVerso.Examples
import Examples.Ch03Macros

open Lean Meta Elab Tactic

namespace tacticbook_macros

-- ANCHOR: elaboration_show_target
syntax "my_show_target" : tactic

elab_rules : tactic
  | `(tactic| my_show_target) => withMainContext do
      logInfo m!"{← getMainTarget}"

set_option linter.unusedTactic false in
example (P : Prop) : P → P := by
  my_show_target
  intro h
  my_show_target
  exact h
-- ANCHOR_END: elaboration_show_target


-- ANCHOR: elaboration_roots_and_variable
private partial def rootsAndVariable? (e : Expr) : Option (Expr × Array Expr) := do
  let e := e.consumeMData
  if e.isAppOfArity ``Or 2 then
    let args := e.getAppArgs
    let (x, roots₁) ← rootsAndVariable? args[0]!
    let (x', roots₂) ← rootsAndVariable? args[1]!
    guard (x == x')
    return (x, roots₁ ++ roots₂)
  else
    guard (e.isAppOfArity ``Eq 3)
    let args := e.getAppArgs
    return (args[1]!, #[args[2]!])
-- ANCHOR_END: elaboration_roots_and_variable

-- ANCHOR: elaboration_my_poly_roots_target
syntax "my_poly_roots_target " term " with " term " in " term : tactic

macro_rules
  | `(tactic| my_poly_roots_target $poly:term with $roots:term in $x:term) =>
      `(tactic|
        rw [show $poly = (($roots).map (fun r => $x - r)).prod by simp <;> ring] <;>
        simp [mul_eq_zero, sub_eq_zero, or_assoc])
-- ANCHOR_END: elaboration_my_poly_roots_target

-- ANCHOR: elaboration_poly_roots_definition
syntax "my_poly_roots " term : tactic

elab_rules : tactic
  | `(tactic| my_poly_roots $poly:term) => withMainContext do
      let target := (← getMainTarget).consumeMData
      unless target.isAppOfArity ``Iff 2 do
        throwError "my_poly_roots: expected an iff target"
      let some (x, roots) := rootsAndVariable? target.getAppArgs[1]!
        | throwError "my_poly_roots: expected the right side to contain equalities with one shared left-hand side"
      let x ← Term.exprToSyntax x
      let roots ← roots.mapM fun root => Term.exprToSyntax root
      let roots : TSyntaxArray `term := roots
      evalTactic (← `(tactic| my_poly_roots_target $poly with [$roots,*] in $x))
-- ANCHOR_END: elaboration_poly_roots_definition

-- ANCHOR: elaboration_poly_roots_examples
-- ANCHOR: elaboration_poly_roots_first_example
example (x : ℚ) : x^2 - 5*x + 6 = 0 ↔ x = 2 ∨ x = 3 := by
  my_poly_roots x^2 - 5*x + 6
-- ANCHOR_END: elaboration_poly_roots_first_example

-- ANCHOR: elaboration_poly_roots_variants
example (x : ℚ) : x - 2 = 0 ↔ x = 2 := by
  my_poly_roots x - 2

example (x : ℚ) :
    x^3 - 6*x^2 + 11*x - 6 = 0 ↔ (x = 1 ∨ x = 2) ∨ x = 3 := by
  my_poly_roots x^3 - 6*x^2 + 11*x - 6
-- ANCHOR_END: elaboration_poly_roots_variants
-- ANCHOR_END: elaboration_poly_roots_examples

/-- error: my_poly_roots: expected an iff target -/
#guard_msgs (substring := true) in
example : True := by
  my_poly_roots 0

/-- error: my_poly_roots: expected the right side -/
#guard_msgs (substring := true) in
example (x y : ℚ) : x^2 - 5*x + 6 = 0 ↔ x = 2 ∨ y = 3 := by
  my_poly_roots x^2 - 5*x + 6

/-- error: unsolved goals -/
#guard_msgs (substring := true) in
example (x : ℚ) : x^2 - 5*x + 7 = 0 ↔ x = 2 ∨ x = 3 := by
  my_poly_roots x^2 - 5*x + 7

/-- error: Tactic `rewrite` failed: Did not find an occurrence of the pattern -/
#guard_msgs (substring := true) in
example (x : ℚ) : x^2 - 5*x + 7 = 0 ↔ x = 2 ∨ x = 3 := by
  my_poly_roots x^2 - 5*x + 6

-- ANCHOR: elaboration_my_assumption
-- ANCHOR: elaboration_my_assumption_definition
private def myFindLocalDeclWithType? (type : Expr) : MetaM (Option FVarId) := do
  (← getLCtx).findDeclRevM? fun localDecl => do
    if localDecl.isImplementationDetail then
      return none
    else if ← isDefEq type localDecl.type then
      return some localDecl.fvarId
    else
      return none

syntax "my_assumption" : tactic

elab_rules : tactic
  | `(tactic| my_assumption) =>
      liftMetaTactic fun goal => do
        goal.checkNotAssigned `my_assumption
        let target ← goal.getType
        let some fvarId ← myFindLocalDeclWithType? target
          | throwError "my_assumption failed, target{indentExpr target}"
        goal.assign (mkFVar fvarId)
        return []
-- ANCHOR_END: elaboration_my_assumption_definition

-- ANCHOR: elaboration_my_assumption_example
example (P : Prop) (h : P) : P := by
  my_assumption
-- ANCHOR_END: elaboration_my_assumption_example
-- ANCHOR_END: elaboration_my_assumption

-- ANCHOR: elaboration_my_exact
syntax "my_exact " term : tactic

elab_rules : tactic
  | `(tactic| my_exact $proof:term) => withMainContext do
      let goal ← getMainGoal
      let target ← instantiateMVars (← goal.getType)
      let proof ← Lean.Elab.Tactic.elabTermEnsuringType proof (some target)
      goal.assign proof
      replaceMainGoal []

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  my_exact And.intro hP hQ

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example (P Q : Prop) (hQ : Q) : P := by
  my_exact hQ
-- ANCHOR_END: elaboration_my_exact

-- ANCHOR: elaboration_my_apply
syntax "my_apply " term : tactic

elab_rules : tactic
  | `(tactic| my_apply $rule:term) => withMainContext do
      let rule ← Lean.Elab.Tactic.elabTermForApply rule
      let newGoals ← (← getMainGoal).apply rule
      replaceMainGoal newGoals

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  my_apply And.intro
  · exact hP
  · exact hQ
-- ANCHOR_END: elaboration_my_apply

-- ANCHOR: elaboration_my_apply_without_queue
syntax "my_apply_without_queue " term : tactic

elab_rules : tactic
  | `(tactic| my_apply_without_queue $rule:term) => withMainContext do
      let rule ← Lean.Elab.Tactic.elabTermForApply rule
      let _newGoals ← (← getMainGoal).apply rule

/-- error: No goals to be solved -/
#guard_msgs (substring := true) in
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  my_apply_without_queue And.intro
  · exact hP
  · exact hQ
-- ANCHOR_END: elaboration_my_apply_without_queue

-- ANCHOR: elaboration_my_step
-- ANCHOR: elaboration_my_step_definition
syntax "my_step" : tactic

elab_rules : tactic
  | `(tactic| my_step) => withMainContext do
      let goal ← getMainGoal
      if ← goal.assumptionCore then
        replaceMainGoal []
      else
        let target ← whnf (← instantiateMVars (← goal.getType))
        if target.isConstOf ``True then
          evalTactic (← `(tactic| trivial))
        else if target.isAppOfArity ``And 2 || target.isAppOfArity ``Iff 2 then
          evalTactic (← `(tactic| constructor))
        else
          match target with
          | .forallE .. => evalTactic (← `(tactic| intro))
          | _ => throwError "my_step does not know how to continue from target{indentExpr target}"
-- ANCHOR_END: elaboration_my_step_definition

-- ANCHOR: elaboration_my_step_examples
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  my_step
  · my_step
  · my_step

example (P : Prop) : P → P := by
  my_step
  my_step
-- ANCHOR_END: elaboration_my_step_examples
-- ANCHOR_END: elaboration_my_step

end tacticbook_macros
