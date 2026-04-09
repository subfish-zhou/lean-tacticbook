import VersoManual

import LeanAutoBook.Ch00Setup
import LeanAutoBook.Ch01MetaprogrammingModel
import LeanAutoBook.Ch02Expr
import LeanAutoBook.Ch03FirstTactic

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
