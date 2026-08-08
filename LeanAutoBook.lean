import VersoManual

import LeanTacticBook.Helpers
import LeanTacticBook.Ch00Setup
import LeanTacticBook.Ch01TacticMentalModel
import LeanTacticBook.Ch01MetaprogrammingModel
import LeanTacticBook.Ch02Expr
import LeanTacticBook.Ch03FirstTactic
import LeanTacticBook.Ch04GoalManagement
import LeanTacticBook.Ch05TypeclassSynthesis
import LeanTacticBook.Ch06Simp
import LeanTacticBook.Ch07Ring
import LeanTacticBook.Ch08Omega
import LeanTacticBook.Ch09Linarith
import LeanTacticBook.Ch10NormNum
import LeanTacticBook.Ch11Aesop
import LeanTacticBook.Ch12Grind
import LeanTacticBook.Ch13Decide
import LeanTacticBook.Ch14Positivity
import LeanTacticBook.Ch15FunProp
import LeanTacticBook.Ch16Gcongr
import LeanTacticBook.Ch17FieldSimp
import LeanTacticBook.Ch18LogicTransforms
import LeanTacticBook.Ch19DesignYourOwn
import LeanTacticBook.Ch20Reflection
import LeanTacticBook.Ch21Performance
import LeanTacticBook.Ch22ExternalTools
import LeanTacticBook.Ch23Methodology
import LeanTacticBook.Ch24TowardsAnalysis
import LeanTacticBook.AppendixApiReference

open Verso.Genre Manual
open Verso Code External

#doc (Manual) "Lean 4 TacticBook" =>
%%%
file := "LeanTacticBook"
authors := ["Ziyu Zhou (子鱼)"]
tag := "lean-tacticbook"
%%%

本书是给以数学为目标的 Lean 4 用户的元编程和 tactic 教程，我希望能尽可能清晰和全面地讲解元编程，Mathlib 中的真实 tactic 设计，并帮助读者设计和实现自己的 tactic。

想深入阅读本书的读者想必已有基本的 Lean 4 使用经验并使用 tactic 证明过一些定理。本书不预设读者有任何除了在 Lean 中写数学证明以外的编程经验，尤其是元编程或函数式编程经验。至少一门 Lean 以外的任何编程语言的使用经验是有益的，因为我自己会写 Python 和 C++，我很有可能会把程序员的思维方式下意识理解成数学家们的常识，尽管我在尽力避免但难保疏漏。

本书还在持续写作当中。笔者水平有限，如果你对本书有任何的意见建议批评或疑问，欢迎在 GitHub 上提交 issue 或 pull request，或者直接发邮件给我：[subfishzhou@gmail.com](mailto:subfishzhou@gmail.com)

_版本基准_：Lean 工具链 `leanprover/lean4:v4.32.2`；Mathlib revision `905b95818eb3`。

本书参考了

* [Lean 4 元编程教程](https://www.leanprover.cn/mp-lean-zh/)
* 和一些社区的快速教程 [Lean 策略编程指南](https://www.leanprover.cn/lean-tactic-programming-guide-zh/)、[Lean 4 元编程 Cookbook](https://www.leanprover.cn/lean-metaprogramming-recipes-zh/)，
* 以及优秀的 Stanford 课程 [CS 99: Functional Programming and Theorem Proving in Lean 4](https://web.stanford.edu/class/cs99/).

作为补充材料，如果你想了解 Lean 4 的其它方面，可以参考

* [Lean 4 定理证明](https://www.leanprover.cn/tp-lean-zh/)
* [Lean 4 函数式编程](https://www.leanprover.cn/fp-lean-zh/)
* [Lean 4 形式化数学](https://www.leanprover.cn/math-in-lean-zh/)
* [Lean 4 手册](https://lean-lang.org/doc/reference/latest/)

*术语翻译的说明*

1. Tactic 惯常译为“策略”，但易与 Strategy 混淆。Tactic 英文原意为“战术”，但“证明战术”文意欠通。另有“策术”译法取平均，只觉拗口生硬，虽为术语仍觉不妥。本书拟译为“证明术”，使用冗长三字实属无奈。由于本书使用新译法，有损传播，故书名和此序言页仍使用 tactic 一词，本书正文将全部使用译名。
2. 元编程中的一个关键步骤称为“elaboration”，旧译繁多，以“繁饰”最为流行，雅但难以顾名思义，

读者如有更佳译法欢迎致邮。

_感谢 [Lean-zh 中文社区](https://www.leanprover.cn/) 的朋友们的支持，感谢 [猫猫](https://github.com/Fulcrum-Nebula) 愿意把本书作为上海交通大学AI4Math暑校讲义使用，让我有动力完成此书。尽管本书是我一个字一个字手打的，但是还是要感谢GPT5.6sol，尤其是基于此的我的Hermes实例Iroha、Kaguya和Yachiyo，它们帮我检索整理素材，以及处理Verso相关的很多工程问题，并写了好几个版本之后促使我放弃偷懒的幻想而坚持古法手作。_

{include 0 LeanTacticBook.Ch00Setup}

{include 0 LeanTacticBook.Ch01TacticMentalModel}

{include 0 LeanTacticBook.Ch01MetaprogrammingModel}

{include 0 LeanTacticBook.Ch02Expr}

{include 0 LeanTacticBook.Ch03FirstTactic}

{include 0 LeanTacticBook.Ch04GoalManagement}

{include 0 LeanTacticBook.Ch05TypeclassSynthesis}

{include 0 LeanTacticBook.Ch06Simp}

{include 0 LeanTacticBook.Ch07Ring}

{include 0 LeanTacticBook.Ch08Omega}

{include 0 LeanTacticBook.Ch09Linarith}

{include 0 LeanTacticBook.Ch10NormNum}

{include 0 LeanTacticBook.Ch11Aesop}

{include 0 LeanTacticBook.Ch12Grind}

{include 0 LeanTacticBook.Ch13Decide}

{include 0 LeanTacticBook.Ch14Positivity}

{include 0 LeanTacticBook.Ch15FunProp}

{include 0 LeanTacticBook.Ch16Gcongr}

{include 0 LeanTacticBook.Ch17FieldSimp}

{include 0 LeanTacticBook.Ch18LogicTransforms}

{include 0 LeanTacticBook.Ch19DesignYourOwn}

{include 0 LeanTacticBook.Ch20Reflection}

{include 0 LeanTacticBook.Ch21Performance}

{include 0 LeanTacticBook.Ch22ExternalTools}

{include 0 LeanTacticBook.Ch23Methodology}

{include 0 LeanTacticBook.Ch24TowardsAnalysis}

{include 0 LeanTacticBook.AppendixApiReference}
