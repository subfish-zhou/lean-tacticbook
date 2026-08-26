import SubVerso.Examples
import Lean

open Lean Meta Elab Tactic

namespace tacticbook_metam

-- ANCHOR: metam_rw_xray
elab "rw_xray " t:term : tactic => do
  let g ← getMainGoal
  let target ← g.getType
  let heq ← elabTerm t none
  let heqType ← inferType heq
  logInfo m!"rewrite theorem type:{indentExpr heqType}"
  logInfo m!"target before:{indentExpr target}"
  let r ← g.rewrite target heq
  logInfo m!"target after:{indentExpr r.eNew}"
  logInfo m!"equality proof type:{indentExpr (← inferType r.eqProof)}"
  logInfo m!"side goals: {r.mvarIds.length}"
  let g' ← g.replaceTargetEq r.eNew r.eqProof
  replaceMainGoal (g' :: r.mvarIds)
-- ANCHOR_END: metam_rw_xray

-- ANCHOR: metam_rw_xray_use
example (x y : Nat) (h : x = y) : x + 1 = y + 1 := by
  rw_xray h
  rfl
-- ANCHOR_END: metam_rw_xray_use

-- ANCHOR: metam_rewrite_side_goal
example (f : Nat → Nat) (x : Nat)
    (h : ∀ n, n > 0 → f n = n + 1) (hx : x > 0) : f x = x + 1 := by
  rw_xray h
  · rfl
  · exact hx
-- ANCHOR_END: metam_rewrite_side_goal

-- ANCHOR: metam_defeq_assignment
elab "observe_defeq_assignment" : tactic => do
  let hole ← mkFreshExprMVar (mkConst ``Nat)
  let holeId := hole.mvarId!
  let before ← holeId.isAssigned
  let ok ← isDefEq hole (mkNatLit 3)
  let after ← holeId.isAssigned
  let value ← instantiateMVars hole
  logInfo m!"before={before}, isDefEq={ok}, after={after}, value={value}"

example : True := by
  observe_defeq_assignment
  trivial
-- ANCHOR_END: metam_defeq_assignment

-- ANCHOR: metam_mctx_restore
elab "observe_mctx_restore" : tactic => do
  let hole ← mkFreshExprMVar (mkConst ``Nat)
  let holeId := hole.mvarId!
  let saved ← getMCtx
  discard <| isDefEq hole (mkNatLit 7)
  let assignedDuring ← holeId.isAssigned
  setMCtx saved
  let assignedAfterRestore ← holeId.isAssigned
  logInfo m!"assigned during branch={assignedDuring}; after restore={assignedAfterRestore}"

example : True := by
  observe_mctx_restore
  trivial
-- ANCHOR_END: metam_mctx_restore

-- ANCHOR: metam_apply_core
elab "apply_core " t:term : tactic => withMainContext do
  let theoremExpr ← elabTermForApply t
  let newGoals ← (← getMainGoal).apply theoremExpr
  Term.synthesizeSyntheticMVarsNoPostponing
  replaceMainGoal newGoals
-- ANCHOR_END: metam_apply_core

-- ANCHOR: metam_apply_core_use
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  apply_core And.intro
  · exact hP
  · exact hQ
-- ANCHOR_END: metam_apply_core_use

-- ANCHOR: metam_expr_spine
elab "inspect_main_target" : tactic => withMainContext do
  let target ← (← getMainGoal).getType
  let fn := target.getAppFn
  let args := target.getAppArgs
  logInfo m!"target:{indentExpr target}"
  logInfo m!"application head: {fn}"
  logInfo m!"number of arguments: {args.size}"

example (x y : Nat) : x + y = y + x := by
  inspect_main_target
  exact Nat.add_comm x y
-- ANCHOR_END: metam_expr_spine

-- ANCHOR: metam_binder_probe
elab "inspect_forall_target" : tactic => withMainContext do
  let target ← (← getMainGoal).getType
  match target with
  | .forallE name domain body binderInfo =>
      logInfo m!"binder={name}; info={repr binderInfo}; domain={domain}; body={body}"
  | _ => throwError "expected a forall target"

example : ∀ n : Nat, n = n := by
  inspect_forall_target
  intro n
  rfl
-- ANCHOR_END: metam_binder_probe

-- ANCHOR: metam_rewrite_failure
example (x y : Nat) (_h : x = y) : 0 = 0 := by
  fail_if_success rw_xray _h
  rfl
-- ANCHOR_END: metam_rewrite_failure

-- ANCHOR: metam_local_rewrite
elab "rw_hyp_xray " t:term " at " h:ident : tactic => do
  let fvarId ← getFVarId h
  Lean.Elab.Tactic.rewriteLocalDecl t false fvarId
  withMainContext do
    let lctx ← getLCtx
    let some decl := lctx.findFromUserName? h.getId
      | throwError "rewritten hypothesis is missing"
    logInfo m!"rewritten hypothesis type: {decl.type}"

example (x y : Nat) (hxy : x = y) (h : x + 1 = 2) : y + 1 = 2 := by
  rw_hyp_xray hxy at h
  exact h
-- ANCHOR_END: metam_local_rewrite

end tacticbook_metam
