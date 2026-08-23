import VersoManual

import LeanTacticBook.Helpers
import LeanTacticBook.Ch01Introduction
import LeanTacticBook.Ch02Syntax
import LeanTacticBook.Ch03Macros
import LeanTacticBook.AppendixApiReference

open Verso.Genre Manual
open Verso Code External

#doc (Manual) "Lean 4 Tactic纲目" =>
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

* [Lean 4 手册](https://lean-lang.org/doc/reference/latest/)
* [Lean 4 元编程教程](https://www.leanprover.cn/mp-lean-zh/)
* 和一些社区的快速教程 [Lean 策略编程指南](https://www.leanprover.cn/lean-tactic-programming-guide-zh/)、[Lean 4 元编程 Cookbook](https://www.leanprover.cn/lean-metaprogramming-recipes-zh/)，
* 以及优秀的 Stanford 课程 [CS 99: Functional Programming and Theorem Proving in Lean 4](https://web.stanford.edu/class/cs99/).

既然有这些优秀的教程珠玉在前，为什么我还要写这样一本教程呢？第一我希望能在组织材料的方式上有所发挥，元编程的机制很复杂，如果完整展示接口细节容易让读者感到混乱。我希望以例子为先导来呈现内容，这样能让缺乏编程背景的读者能更快理解操作方法及其动机，而不是被接口细节淹没。第二我希望涵盖更全面的内容，尤其是 Mathlib 中许多高级 tactic 的真实设计和实现，例如 grind 等等，这正是本书以“纲目”冠名的野心。

作为补充材料，如果你想了解 Lean 4 的其它方面，可以参考

* [Lean 4 定理证明](https://www.leanprover.cn/tp-lean-zh/)
* [Lean 4 函数式编程](https://www.leanprover.cn/fp-lean-zh/)
* [Lean 4 形式化数学](https://www.leanprover.cn/math-in-lean-zh/)


*术语翻译的说明*

1. Tactic 惯常译为“策略”，但易与 Strategy 混淆。Tactic 英文原意为“战术”，但“证明战术”文意欠通。另有“策术”译法取平均，只觉拗口生硬，虽为术语仍觉不妥。本书拟译为“证明术”，使用冗长三字实属无奈。本书正文将全部使用译名。
2. 元编程中的一个关键步骤称为“elaboration”，旧译繁多，以“繁饰”最为流行，雅但难以顾名思义，笔者考虑过几个译名，例如“精译”，取词根 elab 的“精心制作”之意。笔者最终决定使用“译补”，巧合地是它缩写 elab 的音译“译来补”，但抛去这点不谈只看它是否是地道的中文术语，它既保留了 `Syntax -> Expr` 类型间的“译”意，又能指代推断隐式参数、填补元变量等等elaboration的实际步骤。
3. `Syntax` 翻译成句法，这是让我们能够在讨论“xx的语法”的时候指的是xx功能要如何写。
4. Lean Pretty-Print 功能拟译为“雅印”，意指“雅致的印刷”，即美观的打印输出。
读者如有更佳译法欢迎致邮。

*版本基准*：Lean 工具链 `leanprover/lean4:v4.32.2`；Mathlib revision `905b95818eb3`。元编程 API 可能在小版本间发生不兼容变化。

:::codeBox "可运行"
```bashFence
cat examples/lean-toolchain  -- 显示 leanprover/lean4:v4.32.2
rg -n '905b95818eb3' examples/lake-manifest.json
cd examples
lake env lean --version
```
:::

_感谢 [Lean-zh 中文社区](https://www.leanprover.cn/) 的朋友们的支持，感谢 [猫猫](https://github.com/Fulcrum-Nebula) 愿意把本书作为上海交通大学AI4Math暑校讲义使用，让我有动力完成此书。尽管本书是我一个字一个字手打的，但是还是要感谢GPT5.6sol，尤其是基于此的我的Hermes实例Iroha、Kaguya和Yachiyo，她们帮我检索整理素材，以及处理Verso相关的很多工程问题，并写了好几个版本之后促使我放弃偷懒的幻想而坚持古法手作。_

{include 0 LeanTacticBook.Ch01Introduction}

{include 0 LeanTacticBook.Ch02Syntax}

{include 0 LeanTacticBook.Ch03Macros}

{include 0 LeanTacticBook.AppendixApiReference}
