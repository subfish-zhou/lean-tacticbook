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

private def sourcePolynomial? (target : Expr) (x : Expr) (lctx : LocalContext) : Option Expr := do
  let target := target.consumeMData
  if target.isAppOfArity ``Iff 2 then
    return (← eqSides? target.getAppArgs[0]!).1
  for decl in lctx do
    if !decl.isImplementationDetail then
      if let some (poly, _) := eqSides? decl.type then
        if x.isFVar && poly.containsFVar x.fvarId! then return poly
  failure
-- ANCHOR_END: elaboration_poly_roots_readers

private def mkRootListSyntax (roots : Array Expr) : TacticM (TSyntax `term) := do
  let some firstRoot := roots[0]?
    | throwError "poly_roots: expected at least one root"
  let rootType ← inferType firstRoot
  Term.exprToSyntax (← mkListLit rootType roots.toList)

-- ANCHOR: macro_poly_roots_infer_variable
syntax "poly_roots₂ " term " with " term:max+ : tactic

elab_rules : tactic
  | `(tactic| poly_roots₂ $poly:term with $suppliedRoots:term*) => withMainContext do
      let target ← instantiateMVars (← getMainTarget)
      let some (x, roots) := rootsAndVariable? (rootConclusion target)
        | throwError "poly_roots₂: expected a disjunction of equations with one common variable"
      if roots.size != suppliedRoots.size then
        throwError "poly_roots₂: the number of supplied roots does not match the target"
      let x ← Term.exprToSyntax x
      let roots : TSyntaxArray `term := suppliedRoots
      let rootList ← `(term| [$roots,*])
      evalTactic (← `(tactic| poly_roots_core $poly with $rootList in $x))

example (x : ℚ) (h : x^2 - 5*x + 6 = 0) : x = 2 ∨ x = 3 := by
  poly_roots₂ x^2 - 5*x + 6 with 2 3
-- ANCHOR_END: macro_poly_roots_infer_variable

-- ANCHOR: elaboration_poly_roots_wrong_order
/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example (x : ℚ) (h : x^2 - 5*x + 6 = 0) : x = 2 ∨ x = 3 := by
  poly_roots₂ x^2 - 5*x + 6 with 3 2
-- ANCHOR_END: elaboration_poly_roots_wrong_order

-- ANCHOR: macro_poly_roots_infer_all
syntax "poly_roots" : tactic

elab_rules : tactic
  | `(tactic| poly_roots) => withMainContext do
      let target ← instantiateMVars (← getMainTarget)
      let some (x, roots) := rootsAndVariable? (rootConclusion target)
        | throwError "poly_roots: expected a disjunction of equations with one common variable"
      let some poly := sourcePolynomial? target x (← getLCtx)
        | throwError "poly_roots: expected a polynomial equation in the target or local context"
      let poly ← Term.exprToSyntax poly
      let x ← Term.exprToSyntax x
      let rootList ← mkRootListSyntax roots
      evalTactic (← `(tactic| poly_roots_core $poly with $rootList in $x))

example (x : ℚ) (h : x^2 - 5*x + 6 = 0) : x = 2 ∨ x = 3 := by
  poly_roots
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
      liftMetaTactic fun goal => goal.withContext do
        goal.checkNotAssigned `my_assumption
        let some fvarId ← myFindLocalDeclWithType? (← goal.getType)
          | throwError "my_assumption failed"
        goal.assign (mkFVar fvarId)
        return []

example (P : Prop) (h : P) : P := by
  my_assumption
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

-- ANCHOR: elaboration_my_step
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

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  my_step
  · my_step
  · my_step

example (P : Prop) : P → P := by
  my_step
  my_step
-- ANCHOR_END: elaboration_my_step

end tacticbook_macros
