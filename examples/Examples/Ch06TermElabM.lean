import SubVerso.Examples
import Mathlib
import Lean.Elab.Tactic.LibrarySearch

open Lean Meta Elab
open Lean.Elab Term Tactic
open Lean.Meta LibrarySearch
open Lean.Meta.Tactic.TryThis

namespace tacticbook_termelab

-- ANCHOR: termelab_exact_spellings
example : True := exact?%
example : True := by
  exact?
-- ANCHOR_END: termelab_exact_spellings

-- ANCHOR: termelab_book_exact
syntax (name := bookExactTerm) "book_exact?%" : term

@[term_elab bookExactTerm]
def elabBookExactTerm : TermElab := fun stx expectedType? => do
  let `(book_exact?%) := stx | throwUnsupportedSyntax
  withExpectedType expectedType? fun expectedType => do
    logInfo m!"expected type:{indentExpr expectedType}"
    let goal ← mkFreshExprMVar expectedType
    let (_, introdGoal) ← goal.mvarId!.intros
    introdGoal.withContext do
      if let some suggestions ← librarySearch introdGoal then
        if suggestions.isEmpty then
          logError "book_exact?% did not find a relevant declaration"
        else
          logError "book_exact?% found only partial suggestions"
        mkLabeledSorry expectedType (synthetic := true) (unique := true)
      else
        let proof ← instantiateMVars goal
        logInfo m!"proof type:{indentExpr (← inferType proof)}"
        addTermSuggestion stx proof.headBeta
        return proof
-- ANCHOR_END: termelab_book_exact

-- ANCHOR: termelab_book_exact_use
example : True := book_exact?%
example (P : Prop) (h : P) : P := book_exact?%
example (P Q : Prop) : P → Q → P ∧ Q := book_exact?%
-- ANCHOR_END: termelab_book_exact_use

-- ANCHOR: termelab_expected_type_flow
example : True := id book_exact?%
example : True := (book_exact?% : True)
#check id book_exact?%
-- ANCHOR_END: termelab_expected_type_flow

-- ANCHOR: termelab_book_show
syntax (name := bookShow) "book_show " term " from " term : term

@[term_elab bookShow]
def elabBookShow : TermElab := fun stx expectedType? => do
  let `(book_show $typeStx from $valueStx) := stx
    | throwUnsupportedSyntax
  let type ← elabType typeStx
  logInfo m!"type written after show:{indentExpr type}"
  let value ← elabTermEnsuringType valueStx (some type)
  ensureHasType expectedType? value
-- ANCHOR_END: termelab_book_show

-- ANCHOR: termelab_book_show_use
example : Nat := book_show Nat from 3
example : True := book_show True from True.intro
example : Int := book_show Nat from 0
-- ANCHOR_END: termelab_book_show_use

-- ANCHOR: termelab_real_show
example : Int := show Nat from 0
example (x y : Nat) : (x + 0) + y = x + y := by
  rw [show x + 0 = x from rfl]
-- ANCHOR_END: termelab_real_show

-- ANCHOR: termelab_same_syntax_kind
syntax (name := bookDefault) "book_default" : term

@[term_elab bookDefault]
def elabBookDefaultNat : TermElab := fun stx expectedType? => do
  let `(book_default) := stx | throwUnsupportedSyntax
  let some expectedType := expectedType? | throwUnsupportedSyntax
  unless expectedType.isConstOf ``Nat do throwUnsupportedSyntax
  logInfo "Nat elaborator accepted book_default"
  return mkNatLit 0

@[term_elab bookDefault]
def elabBookDefaultBool : TermElab := fun stx expectedType? => do
  let `(book_default) := stx | throwUnsupportedSyntax
  let some expectedType := expectedType? | throwUnsupportedSyntax
  unless expectedType.isConstOf ``Bool do throwUnsupportedSyntax
  logInfo "Bool elaborator accepted book_default"
  return mkConst ``Bool.false

example : Nat := book_default
example : Bool := book_default
-- ANCHOR_END: termelab_same_syntax_kind

-- ANCHOR: termelab_setbuilder_fallback
def smallEvens : Finset (Fin 6) := {x | x.val % 2 = 0}
def oddsFromFinset (s : Finset Nat) : Finset Nat := {x ∈ s | x % 2 = 1}
def oddsFromSet (s : Set Nat) : Set Nat := {x ∈ s | x % 2 = 1}
def noExpectedSet := {x : Nat | x % 2 = 0}
-- ANCHOR_END: termelab_setbuilder_fallback

-- ANCHOR: termelab_synthetic_default
syntax (name := syntheticDefault) "synthetic_default%" : term

@[term_elab syntheticDefault]
def elabSyntheticDefault : TermElab := fun stx expectedType? => do
  let expectedType ← withExpectedType expectedType? pure
  let u ← getLevel expectedType
  let classType := mkApp (mkConst ``Inhabited [u]) expectedType
  let inst ← mkFreshExprMVar classType MetavarKind.synthetic
  registerSyntheticMVar stx inst.mvarId! (.typeClass none)
  let kinds ← (← get).pendingMVars.mapM fun mvarId => do
    return (← getSyntheticMVarDecl? mvarId).map (toString ·.kind) |>.getD "unknown"
  logInfo m!"registered synthetic kinds: {kinds}"
  return mkApp2 (mkConst ``default [u]) expectedType inst

#eval (synthetic_default% : Nat)
-- ANCHOR_END: termelab_synthetic_default

-- ANCHOR: termelab_postpone_resume
syntax (name := needsExpected) "needs_expected% " term : term

@[term_elab needsExpected]
def elabNeedsExpected : TermElab := fun stx expectedType? => do
  let `(needs_expected% $t) := stx | throwUnsupportedSyntax
  let expectedType ← tryPostponeIfHasMVars expectedType?
    "needs_expected% requires a fully known expected type"
  logInfo m!"needs_expected% resumed with: {expectedType}"
  elabTerm t (some expectedType)

def same {α : Type} (x _y : α) : α := x

set_option trace.Elab.postpone true in
#check same (needs_expected% 7) (8 : Nat)
-- ANCHOR_END: termelab_postpone_resume

end tacticbook_termelab
