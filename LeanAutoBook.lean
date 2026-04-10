import VersoManual

import LeanAutoBook.Helpers
import LeanAutoBook.Ch00Setup
import LeanAutoBook.Ch01MetaprogrammingModel
import LeanAutoBook.Ch02Expr
import LeanAutoBook.Ch03FirstTactic
import LeanAutoBook.Ch04GoalManagement
import LeanAutoBook.Ch05TypeclassSynthesis
import LeanAutoBook.Ch06Simp
import LeanAutoBook.Ch07Ring
import LeanAutoBook.Ch08Omega
import LeanAutoBook.Ch09Linarith
import LeanAutoBook.Ch10NormNum
import LeanAutoBook.Ch11Aesop
import LeanAutoBook.Ch12Grind
import LeanAutoBook.Ch13Decide
import LeanAutoBook.Ch14Positivity
import LeanAutoBook.Ch15FunProp
import LeanAutoBook.Ch16Gcongr
import LeanAutoBook.Ch17FieldSimp
import LeanAutoBook.Ch18LogicTransforms
import LeanAutoBook.Ch19DesignYourOwn
import LeanAutoBook.Ch20Reflection
import LeanAutoBook.Ch21Performance
import LeanAutoBook.Ch22ExternalTools
import LeanAutoBook.Ch23Methodology
import LeanAutoBook.Ch24TowardsAnalysis

open Verso.Genre Manual
open Verso Code External

-- 《Lean 4 自动化内幕》
#doc (Manual) "Lean 4 自动化内幕" =>
%%%
file := "LeanAutoBook"
authors := ["Ziyu Zhou (子鱼)"]
tag := "lean-automation-internals"
%%%

本书深入讲解 Lean 4 的自动化（tactic）系统内幕：元编程模型、表达式操作、tactic 实现原理，以及 Mathlib 中各种自动化工具的工作机制。

本书假设你已有基本的 Lean 4 使用经验，了解 `theorem`、`by`、`simp` 等基础语法。

_本书校验版本_：Lean 4 `v4.30.0-rc1`，Mathlib 同期主线（2026 年 4 月）。

{include 0 LeanAutoBook.Ch00Setup}

{include 0 LeanAutoBook.Ch01MetaprogrammingModel}

{include 0 LeanAutoBook.Ch02Expr}

{include 0 LeanAutoBook.Ch03FirstTactic}

{include 0 LeanAutoBook.Ch04GoalManagement}

{include 0 LeanAutoBook.Ch05TypeclassSynthesis}

{include 0 LeanAutoBook.Ch06Simp}

{include 0 LeanAutoBook.Ch07Ring}

{include 0 LeanAutoBook.Ch08Omega}

{include 0 LeanAutoBook.Ch09Linarith}

{include 0 LeanAutoBook.Ch10NormNum}

{include 0 LeanAutoBook.Ch11Aesop}

{include 0 LeanAutoBook.Ch12Grind}

{include 0 LeanAutoBook.Ch13Decide}

{include 0 LeanAutoBook.Ch14Positivity}

{include 0 LeanAutoBook.Ch15FunProp}

{include 0 LeanAutoBook.Ch16Gcongr}

{include 0 LeanAutoBook.Ch17FieldSimp}

{include 0 LeanAutoBook.Ch18LogicTransforms}

{include 0 LeanAutoBook.Ch19DesignYourOwn}

{include 0 LeanAutoBook.Ch20Reflection}

{include 0 LeanAutoBook.Ch21Performance}

{include 0 LeanAutoBook.Ch22ExternalTools}

{include 0 LeanAutoBook.Ch23Methodology}

{include 0 LeanAutoBook.Ch24TowardsAnalysis}
