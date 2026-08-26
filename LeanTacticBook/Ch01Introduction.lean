import VersoManual
import LeanTacticBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "examples"
set_option verso.exampleModule "Examples.Ch01Introduction"

#doc (Manual) "概述" =>
%%%
file := "Ch01Introduction"
tag := "introduction"
%%%

# Lean 编译过程
%%%
tag := "lean-compile-process"
%%%

Lean 从源码到声明，主要经过以下几层：

:::codeBox "pseudocode"
```
source text
→ parser：按语法类别构造 Syntax
→ macro expansion：Syntax → Syntax
→ elaboration：结合预期类型、环境与上下文构造 Expr / declarations
→ kernel：检查声明类型与证明项
→ code generation / evaluation：只在需要运行可执行定义时发生
```
:::

解析器不是用一个“美化的正则表达式”包办全部语法。不同 parser category 各自有规则；解析结果携带 syntax kind，供宏和译补器继续分派。

宏反复把一棵 Syntax 改写成另一棵 Syntax，直到进入不再由该宏展开的形状。宏只处理语法结构，不负责判断生成项是否具有目标类型。

译补也不是凭一个 `name` 找到唯一函数。命令、项和 tactic 有各自的分派入口，同一 syntax kind 还可能注册多个译补器并依次尝试；宏回退、预期类型、局部上下文与环境都会影响结果。译补成功后得到 Expr 或声明，再交给内核检查。

最后要分清“检查”与“执行”。定理的证明项通常由内核做类型检查，并不会因为出现在源码里就转换成机器码执行。只有需要运行定义、生成可执行程序或使用原生求值时，才进入代码生成与运行时；Ch13 会看到这一区分怎样直接改变信任边界。

# 全书结构
%%%
tag := "book-overview"
%%%

:::codeBox "pseudocode"
```
Part I   Ch01–Ch03  心智模型、语法与宏
Part II  Ch04–Ch08  译补入门、CoreM、MetaM、项译补与 TacticM
Part III Ch09–Ch13  exact?、ring、linarith、grind、bv_decide
```
:::

Ch01–Ch08 建立后续章节共用的对象、状态和前端知识，适合按顺序阅读。Ch09–Ch13 每章选择一种生产自动化证明术，沿“问题怎样表示、搜索或计算产生什么、证明如何构造、内核最终检查什么”追到底。
