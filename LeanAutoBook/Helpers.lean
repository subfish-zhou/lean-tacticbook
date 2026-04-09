import VersoManual
import SubVerso.Highlighting

open Verso Doc Elab Genre.Manual ArgParse Code Highlighted
open Verso Code External
open SubVerso.Highlighting
open Lean

/-- Inline keyword role: renders tactic/keyword names with keyword highlighting. -/
@[role_expander kw]
def kw : RoleExpander
  | args, inls => do
    ArgParse.done.run args
    let kw ← oneCodeStr inls
    let hl : Highlighted := .token ⟨.keyword none none none, kw.getString⟩
    return #[← ``(Inline.other (Inline.lean $(quote hl) {}) #[Inline.code $(quote kw.getString)])]
