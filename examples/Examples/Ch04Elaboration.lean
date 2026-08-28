import SubVerso.Examples
import Examples.Ch03Macros

open Lean Meta Elab Tactic

namespace tacticbook_macros

-- ANCHOR: elaboration_poly_roots_readers
private def eqSides? (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``Eq 3 then
    let args := e.getAppArgs
    some (args[1]!, args[2]!)
  else
    none

private partial def rootEqualities? (e : Expr) : Option (Array (Expr × Expr)) :=
  let e := e.consumeMData
  if e.isAppOfArity ``Or 2 then
    let args := e.getAppArgs
    return (← rootEqualities? args[0]!) ++ (← rootEqualities? args[1]!)
  else
    return #[← eqSides? e]

private def rootsAndVariable? (e : Expr) : Option (Expr × Array Expr) := do
  let equalities ← rootEqualities? e
  let (x, firstRoot) ← equalities[0]?
  let mut roots := #[firstRoot]
  for (x', root) in equalities[1...*] do
    if x' != x then failure
    roots := roots.push root
  return (x, roots)

private def rootConclusion (target : Expr) : Expr :=
  let target := target.consumeMData
  if target.isAppOfArity ``Iff 2 then target.getAppArgs[1]! else target

-- ANCHOR_END: elaboration_poly_roots_readers

-- ANCHOR: elaboration_poly_roots_target_core
syntax "poly_roots_target_core " term " with " term " in " term : tactic

macro_rules
  | `(tactic| poly_roots_target_core $poly:term with $roots:term in $x:term) =>
      `(tactic|
        rw [show $poly = (($roots).map (fun r => $x - r)).prod by
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] <;>
          ring] <;>
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
          mul_eq_zero, sub_eq_zero, or_assoc])
-- ANCHOR_END: elaboration_poly_roots_target_core

-- ANCHOR: macro_poly_roots_infer_variable
-- ANCHOR: elaboration_poly_roots2_definition
syntax "poly_roots₂ " term " with " term:max+ : tactic

elab_rules : tactic
  | `(tactic| poly_roots₂ $poly:term with $suppliedRoots:term*) => withMainContext do
      let target ← getMainTarget
      let some (x, roots) := rootsAndVariable? (rootConclusion target)
        | throwError "poly_roots₂: expected one or more equations with structurally identical left-hand sides"
      if roots.size != suppliedRoots.size then
        throwError "poly_roots₂: the number of supplied roots does not match the target"
      let x ← Term.exprToSyntax x
      let roots : TSyntaxArray `term := suppliedRoots
      let rootList ← `(term| [$roots,*])
      evalTactic (← `(tactic| poly_roots_target_core $poly with $rootList in $x))
-- ANCHOR_END: elaboration_poly_roots2_definition

example (x : ℚ) : x^2 - 5*x + 6 = 0 ↔ x = 2 ∨ x = 3 := by
  -- ANCHOR: elaboration_poly_roots2_call
  poly_roots₂ x^2 - 5*x + 6 with 2 3
  -- ANCHOR_END: elaboration_poly_roots2_call
-- ANCHOR_END: macro_poly_roots_infer_variable

-- ANCHOR: elaboration_poly_roots_wrong_order
/-- error: unsolved goals -/
#guard_msgs (substring := true) in
example (x : ℚ) : x^2 - 5*x + 6 = 0 ↔ x = 2 ∨ x = 3 := by
  poly_roots₂ x^2 - 5*x + 6 with 3 2
-- ANCHOR_END: elaboration_poly_roots_wrong_order

-- ANCHOR: elaboration_poly_roots2_shapes
example (x : ℚ) : x - 2 = 0 ↔ x = 2 := by
  poly_roots₂ x - 2 with 2

example (x : ℚ) :
    x^3 - 6*x^2 + 11*x - 6 = 0 ↔ (x = 1 ∨ x = 2) ∨ x = 3 := by
  poly_roots₂ x^3 - 6*x^2 + 11*x - 6 with 1 2 3
-- ANCHOR_END: elaboration_poly_roots2_shapes

-- ANCHOR: elaboration_poly_roots_core
-- ANCHOR: elaboration_source_polynomial
private def sourcePolynomial? (target : Expr) (x : Expr) (lctx : LocalContext) : Option Expr := do
  let target := target.consumeMData
  if target.isAppOfArity ``Iff 2 then
    return (← eqSides? target.getAppArgs[0]!).1
  for decl in lctx do
    if !decl.isImplementationDetail then
      if let some (poly, _) := eqSides? decl.type then
        if x.isFVar && poly.containsFVar x.fvarId! then return poly
  failure
-- ANCHOR_END: elaboration_source_polynomial

-- ANCHOR: elaboration_poly_roots_core_tactic
syntax "poly_roots_core " term " with " term " in " term : tactic

macro_rules
  | `(tactic| poly_roots_core $poly:term with $roots:term in $x:term) =>
      `(tactic|
        first
        | poly_roots_target_core $poly with $roots in $x
        | have hpoly : $poly = 0 := by assumption
          rw [show $poly = (($roots).map (fun r => $x - r)).prod by
            simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] <;>
            ring] at hpoly
          simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
            mul_eq_zero, sub_eq_zero, or_assoc] using hpoly)
-- ANCHOR_END: elaboration_poly_roots_core_tactic

-- ANCHOR: elaboration_mk_root_list_syntax
private def mkRootListSyntax (roots : Array Expr) : TacticM (TSyntax `term) := do
  let some firstRoot := roots[0]?
    | throwError "poly_roots: expected at least one root"
  let rootType ← inferType firstRoot
  Term.exprToSyntax (← mkListLit rootType roots.toList)
-- ANCHOR_END: elaboration_mk_root_list_syntax
-- ANCHOR_END: elaboration_poly_roots_core

-- ANCHOR: macro_poly_roots_infer_all
-- ANCHOR: elaboration_poly_roots_public
syntax "poly_roots" : tactic

elab_rules : tactic
  | `(tactic| poly_roots) => withMainContext do
      let target ← getMainTarget
      let some (x, roots) := rootsAndVariable? (rootConclusion target)
        | throwError "poly_roots: expected one or more equations with structurally identical left-hand sides"
      let some poly := sourcePolynomial? target x (← getLCtx)
        | throwError "poly_roots: expected an equation source in the target or local context"
      let poly ← Term.exprToSyntax poly
      let x ← Term.exprToSyntax x
      let rootList ← mkRootListSyntax roots
      evalTactic (← `(tactic| poly_roots_core $poly with $rootList in $x))
-- ANCHOR_END: elaboration_poly_roots_public

-- ANCHOR: elaboration_poly_roots_local_example
example (x : ℚ) (h : x^2 - 5*x + 6 = 0) : x = 2 ∨ x = 3 := by
  poly_roots
-- ANCHOR_END: elaboration_poly_roots_local_example
-- ANCHOR_END: macro_poly_roots_infer_all

-- ANCHOR: macro_poly_roots_cubic
example (x : ℚ) :
    x^3 - 6*x^2 + 11*x - 6 = 0 ↔
      x = 1 ∨ x = 2 ∨ x = 3 := by
  poly_roots
-- ANCHOR_END: macro_poly_roots_cubic

-- ANCHOR: macro_poly_roots_quartic
example (x : ℚ) :
    x^4 - 10*x^3 + 35*x^2 - 50*x + 24 = 0 ↔
      x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by
  poly_roots
-- ANCHOR_END: macro_poly_roots_quartic

-- ANCHOR: elaboration_poly_roots_contract_regression
example (x : ℚ) : (x - 2) * (x - 3) = 0 ↔ x = 2 ∨ x = 3 := by
  poly_roots

example (x : ℚ) (h : x - 2 = 0) : x = 2 := by
  poly_roots
-- ANCHOR_END: elaboration_poly_roots_contract_regression

example (x : ℚ) : x - 2 = 0 ↔ x = 2 := by
  poly_roots

example (x : ℚ) :
    x^3 - 6*x^2 + 11*x - 6 = 0 ↔ (x = 1 ∨ x = 2) ∨ x = 3 := by
  poly_roots

-- ANCHOR: elaboration_show_target
syntax "my_show_target" : tactic

elab_rules : tactic
  | `(tactic| my_show_target) => withMainContext do
      logInfo m!"{← getMainTarget}"

set_option linter.unusedTactic false in
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  my_show_target
  constructor
  · exact hP
  · exact hQ
-- ANCHOR_END: elaboration_show_target

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
