prelude
import Init.Notation

namespace Lean.Parser.Tactic

syntax "with_annotate_state " rawStx ppSpace tactic : tactic
syntax "(" withoutPosition(tacticSeq) ")" : tactic
syntax "try " tacticSeq : tactic
syntax "with_reducible " tacticSeq : tactic
syntax "rfl" : tactic
syntax "assumption" : tactic

-- ANCHOR: syntax_source_shared
syntax posConfigItem := " +" noWs ident
syntax negConfigItem := " -" noWs ident
syntax valConfigItem := atomic(" (" notFollowedBy(&"discharger" <|> &"disch") ident " := ") withoutPosition(term) ")"
syntax configItem := posConfigItem <|> negConfigItem <|> valConfigItem
syntax optConfig := (colGt configItem)*

syntax locationWildcard := " *"
syntax locationType := patternIgnore(atomic("|" noWs "-") <|> "⊢")
syntax locationHyp := (ppSpace colGt (term:max <|> locationType))+
syntax location := withPosition(ppGroup(" at" (locationWildcard <|> locationHyp)))
-- ANCHOR_END: syntax_source_shared

-- ANCHOR: syntax_source_rewrite
syntax rwRule    := unicode("← ", "<- ")? term
syntax rwRuleSeq := " [" withoutPosition(rwRule,*,?) "]"

syntax (name := rewriteSeq) "rewrite" optConfig rwRuleSeq (location)? : tactic
-- ANCHOR_END: syntax_source_rewrite

-- ANCHOR: syntax_source_rw
macro (name := rwSeq) "rw " c:optConfig s:rwRuleSeq l:(location)? : tactic =>
  match s with
  | `(rwRuleSeq| [$rs,*]%$rbrak) =>
    `(tactic| (rewrite $c [$rs,*] $(l)?; with_annotate_state $rbrak (try (with_reducible rfl))))
  | _ => Macro.throwUnsupported

macro "rwa " rws:rwRuleSeq loc:(location)? : tactic =>
  `(tactic| (rw $rws:rwRuleSeq $[$loc:location]?; assumption))
-- ANCHOR_END: syntax_source_rw

-- ANCHOR: syntax_source_simp
syntax discharger := atomic(" (" patternIgnore(&"discharger" <|> &"disch")) " := " withoutPosition(tacticSeq) ")"

syntax simpPre   := "↓"
syntax simpPost  := "↑"
syntax simpLemma := ppGroup((simpPre <|> simpPost)? unicode("← ", "<- ")? term)
syntax simpErase := "-" term:max
syntax simpStar  := "*"

syntax (name := simp) "simp" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)? : tactic
-- ANCHOR_END: syntax_source_simp

-- ANCHOR: syntax_source_intro
syntax (name := intro) "intro" notFollowedBy("|") (ppSpace colGt term:max)* : tactic
-- ANCHOR_END: syntax_source_intro

-- ANCHOR: syntax_source_elim
syntax inductionAltLHS := ppDedent(ppLine) withPosition("| " (("@"? ident) <|> hole) (colGt (ident <|> hole))*)
syntax inductionAlt  := inductionAltLHS+ (" => " (hole <|> syntheticHole <|> tacticSeq))?
syntax inductionAlts := " with" (ppSpace colGt tactic)? withPosition((colGe inductionAlt)*)

syntax elimTarget := atomic(binderIdent " : ")? term
-- ANCHOR_END: syntax_source_elim

-- ANCHOR: syntax_source_induction
syntax (name := induction) "induction " elimTarget,+ (" using " term)?
  (" generalizing" (ppSpace colGt term:max)+)? (inductionAlts)? : tactic
-- ANCHOR_END: syntax_source_induction

-- ANCHOR: syntax_source_cases
syntax (name := cases) "cases " elimTarget,+ (" using " term)? (inductionAlts)? : tactic
-- ANCHOR_END: syntax_source_cases

end Lean.Parser.Tactic
