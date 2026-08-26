import SubVerso.Examples
import Mathlib.Tactic
import Examples.Ch09Imported

open Lean Meta Elab Tactic
open Lean.Meta.LibrarySearch

namespace tacticbook_exact

set_option linter.unusedTactic false
set_option linter.unusedVariables false

theorem currentToken : tacticbook_exact_imported.SearchToken := .intro

inductive NeedBoth (P Q : Prop) : Prop where
  | intro : P → Q → NeedBoth P Q

theorem makeNeedBoth {P Q : Prop} : P → Q → NeedBoth P Q := .intro

-- ANCHOR: exact_success
example (P Q R : Prop) (hP : P) (hPQ : P → Q) (hQR : Q → R) : R := by
  exact?
-- ANCHOR_END: exact_success

-- ANCHOR: exact_term_success
example (P Q R : Prop) (hP : P) (hPQ : P → Q) (hQR : Q → R) : R :=
  exact?%
-- ANCHOR_END: exact_term_success

-- ANCHOR: exact_frontend_axiom_probe
theorem applyPartialUsesSorry (P Q : Prop) (hP : P) : NeedBoth P Q := by
  apply?

#print axioms applyPartialUsesSorry

set_option linter.unusedVariables false in
theorem exactAllUsesSorry (P : Prop) (hP : P) : P := by
  exact? +all

#print axioms exactAllUsesSorry
-- ANCHOR_END: exact_frontend_axiom_probe

-- ANCHOR: exact_iff_and_symm
example (P Q : Prop) (hPQ : P ↔ Q) (hP : P) : Q := by
  exact?

example (a b : Nat) (h : a = b) : b = a := by
  exact?
-- ANCHOR_END: exact_iff_and_symm

-- ANCHOR: exact_required
example (P Q R : Prop) (hP : P) (hPQ : P → Q) (hQR : Q → R) : R := by
  exact? using hPQ, hQR
-- ANCHOR_END: exact_required

-- ANCHOR: exact_candidate_xray
elab "candidate_xray" : tactic => withMainContext do
  let target ← (← getMainGoal).getType
  let candidates ← libSearchFindDecls target
  logInfo m!"indexed candidates for{indentExpr target}"
  logInfo m!"candidate count: {candidates.size}"
  for (name, modifier) in candidates[:min candidates.size 5] do
    let modifierName := match modifier with
      | .none => "plain"
      | .mp => "Iff.mp"
      | .mpr => "Iff.mpr"
    logInfo m!"  {name} ({modifierName})"

example (a b : Nat) : a = b → b = a := by
  intro h
  candidate_xray
  exact h.symm
-- ANCHOR_END: exact_candidate_xray

-- ANCHOR: exact_partial_probe
elab "partial_search_xray " typeStx:term : tactic => withMainContext do
  let saved ← saveState
  let type ← elabTerm typeStx (some (mkSort .zero))
  let probe ← mkFreshExprMVar type
  let result ← probe.mvarId!.withContext do
    librarySearch probe.mvarId!
  let assigned ← probe.mvarId!.isAssigned
  let summary ← match result with
    | none => pure "complete solution"
    | some suggestions =>
      let sample := (suggestions.extract 0 (min suggestions.size 5)).map (·.1.length)
      pure s!"{suggestions.size} partial suggestion(s), first returned subsidiary-list lengths {sample.toList}"
  saved.restore
  logInfo m!"search result: {summary}; probe assigned after return: {assigned}"

example (P Q : Prop) : True := by
  partial_search_xray (P ∧ Q)
  trivial
-- ANCHOR_END: exact_partial_probe

-- ANCHOR: exact_collect_all_probe
elab "collect_all_xray " typeStx:term : tactic => withMainContext do
  let saved ← saveState
  let type ← elabTerm typeStx (some (mkSort .zero))
  let probe ← mkFreshExprMVar type
  let result ← probe.mvarId!.withContext do
    librarySearch probe.mvarId! (collectAll := true)
  let assigned ← probe.mvarId!.isAssigned
  let summary ← match result with
    | none => pure "unexpected committed solution"
    | some suggestions =>
      let complete := suggestions.countP (·.1.isEmpty)
      pure s!"{suggestions.size} collected suggestion(s), {complete} complete"
  saved.restore
  logInfo m!"collect-all result: {summary}; probe assigned after return: {assigned}"

example : True := by
  collect_all_xray True
  trivial
-- ANCHOR_END: exact_collect_all_probe

-- ANCHOR: exact_module_order_probe
elab "module_order_xray" : tactic => withMainContext do
  let target := mkConst ``tacticbook_exact_imported.SearchToken
  let candidates ← libSearchFindDecls target
  let relevant := candidates.filter fun (name, _) =>
    name == ``currentToken || name == ``tacticbook_exact_imported.importedToken
  logInfo m!"current/imported order: {relevant.map (·.1) |>.toList}"

example : True := by
  module_order_xray
  trivial
-- ANCHOR_END: exact_module_order_probe

-- ANCHOR: exact_toy_search
syntax "book_exact " term,* : tactic

elab_rules : tactic
  | `(tactic| book_exact $[$candidates],*) => do
      let initial ← saveState
      for candidate in candidates do
        initial.restore
        try
          withMainContext do
            let theoremExpr ← elabTermForApply candidate
            let newGoals ← (← getMainGoal).apply theoremExpr
            replaceMainGoal newGoals
          evalTactic (← `(tactic| all_goals assumption))
          if (← getGoals).isEmpty then
            return
        catch _ =>
          pure ()
      initial.restore
      throwError "book_exact exhausted its explicit candidate list"
-- ANCHOR_END: exact_toy_search

-- ANCHOR: exact_toy_search_use
example (P Q R : Prop) (hP : P) (hR : R) : R := by
  book_exact (fun (_ : Q) => hR), (fun (_ : P) => hR)
-- ANCHOR_END: exact_toy_search_use

end tacticbook_exact
