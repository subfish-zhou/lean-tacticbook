import SubVerso.Examples
import Lean
import Mathlib.Tactic
open Lean

namespace tacticbook_syntax
-- ANCHOR: syntax_declaration
syntax "MyTerm" : term

#check_failure MyTerm
-- ANCHOR_END: syntax_declaration

-- ANCHOR: syntax_parameter
syntax (name := myexact) "myexact " term : tactic
-- ANCHOR_END: syntax_parameter

example : True := by
  fail_if_success myexact(True.intro)
  exact True.intro

-- ANCHOR: syntax_norm
syntax "‖" term "‖" : term
-- ANCHOR_END: syntax_norm

-- ANCHOR: syntax_congruence
syntax term " ≡ " term " [mod " term "]" : term
-- ANCHOR_END: syntax_congruence

-- ANCHOR: syntax_xor
notation:10 l:10 " XOR " r:11 => (!l && r) || (l && !r)
-- ANCHOR_END: syntax_xor

-- ANCHOR: syntax_norm_notation
class MyNorm (E : Type*) where
  norm : E → ℝ

notation "‖" e "‖" => MyNorm.norm e
-- ANCHOR_END: syntax_norm_notation

-- ANCHOR: syntax_mod
def MyNat.ModEq (n a b : ℕ) :=
  a % n = b % n

notation:50 a " ≡ " b " [MOD " n "]" =>
  MyNat.ModEq n a b
-- ANCHOR_END: syntax_mod

-- ANCHOR: syntax_mixfix
prefix:75 "NEG " => fun n : Int => -n  -- 前缀一元运算符
postfix:max "²" => fun n : Nat => n ^ 2  -- 后缀一元运算符
infix:50 " EVENMOD " => fun a b : Nat => a % 2 = b % 2  -- 不可结合中缀二元运算符
infixl:65 " -ₗ " => fun a b : Int => a - b  -- 左结合中缀二元运算符
infixr:65 " -ᵣ " => fun a b : Int => a - b  -- 右结合中缀二元运算符

#eval NEG 3               -- -3
#eval 5²                  -- 25
example : 5 EVENMOD 3 := by decide
#eval (10 : Int) -ₗ 3 -ₗ 2 -- 5，即 (10 -ₗ 3) -ₗ 2
#eval (10 : Int) -ᵣ 3 -ᵣ 2 -- 9，即 10 -ᵣ (3 -ᵣ 2)
-- ANCHOR_END: syntax_mixfix

-- ANCHOR: syntax_abbrev
syntax simpPre  := "↓"
syntax simpPost := "↑"
syntax simpStar := "*"
-- ANCHOR_END: syntax_abbrev

-- ANCHOR: syntax_lift
syntax (name := MyLift)
  "my_lift " term
  " to " term
  (" using " term)?
  (" with " ident (ppSpace colGt ident)? (ppSpace colGt ident)?)? : tactic
-- ANCHOR_END: syntax_lift

-- ANCHOR: syntax_alternative
syntax larrow := "←" <|> "<-"
-- ANCHOR_END: syntax_alternative

-- ANCHOR: syntax_binderident
syntax binderIdent := ident <|> hole
-- ANCHOR_END: syntax_binderident

-- ANCHOR: syntax_repetition
syntax "my_rw" " [" term,* "]" : term
-- ANCHOR_END: syntax_repetition

-- ANCHOR: syntax_reuse
syntax rwTerm := (larrow)? term
syntax "my_rw2" " [" rwTerm,* "]" : tactic
-- ANCHOR_END: syntax_reuse

-- ANCHOR: syntax_induction_use
example (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih
-- ANCHOR_END: syntax_induction_use

-- ANCHOR: syntax_precedence
notation:10 l:10 " SUBL " r:11 => l - r
notation:10 l:11 " SUBR " r:10 => l - r
notation:10 l:10 " SUBR₂ " r:10 => l - r
notation:10 l:11 " SUBX " r:11 => l - r

#eval 10 SUBL 3 SUBL 2 -- 5，即 (10 SUBL 3) SUBL 2
#eval 10 SUBR 3 SUBR 2 -- 9，即 10 SUBR (3 SUBR 2)
#eval 10 SUBR₂ 3 SUBR₂ 2 -- 9，依然是右结合的
#eval 10 SUBX (3 SUBX 2) -- 9，SUBX 不允许连续使用，必须带括号
-- ANCHOR_END: syntax_precedence

-- ANCHOR: syntax_default_precedence
notation l " SUB₁ " r => l - r
-- 等价于
notation:1022 l:0 " SUB₂ " r:0 => l - r
-- ANCHOR_END: syntax_default_precedence

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

-- ANCHOR: parser_inspect_kind
partial def syntaxKinds : Syntax → Array SyntaxNodeKind
  | .node _ kind args => args.foldl (fun kinds arg => kinds ++ syntaxKinds arg) #[kind]
  | _ => #[]

elab "#inspect_syntax " t:tactic : command => do
  for kind in syntaxKinds t.raw do
    if kind != nullKind then
      logInfo m!"{kind}"

#inspect_syntax myexact True.intro
#inspect_syntax simp only [↓ ← h]
-- ANCHOR_END: parser_inspect_kind

end tacticbook_syntax
