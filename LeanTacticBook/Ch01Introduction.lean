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

Lean 编译过程可以总结为下图：

![Lean 编译过程](LeanTacticBook/img/lean-compile.png)

首先从字符串形式的 Lean 代码开始。然后它变成 Syntax 对象，然后是 Expr 对象。最后执行它。

因此，编译器看到一串 Lean 代码，例如 "let a := 2"，然后展开以下过程：

应用相关语法规则 ("let a := 2" ➤ Syntax)
在解析步骤中，Lean 尝试将一串 Lean 代码与声明的语法规则之一进行匹配，以便将该字符串转换为 Syntax 对象。语法规则基本上是美化的正则表达式 -- 当您编写与某个语法规则的正则表达式匹配的 Lean 字符串时，该规则将用于处理后续步骤。

循环应用所有宏 (Syntax ➤ Syntax)
在繁饰步骤中，每个宏只是将现有的 Syntax 对象转换为某个新的 Syntax 对象。然后，新的 Syntax 以类似的方式处理（重复步骤 1 和 2），直到没有更多宏可应用。

应用单个 elab (Syntax ➤ Expr)
最后，是时候为你的语法注入意义了 -- Lean 通过 name 参数找到与相应语法规则匹配的 elab（语法规则、宏 和 elabs 都有此参数，并且它们必须匹配）。新发现的 elab 返回特定的 Expr 对象。

这样就完成了繁饰步骤。​​

然后，表达式（Expr）在求值步骤中转换为可执行代码 -- 我们不必以任何方式指定，Lean 编译器将为我们处理此操作。


# 全书结构
%%%
tag := "book-overview"
%%%

:::codeBox "示意"
```leanBug
Part I   Ch1–Ch6    tactic 心智模型、tactic 基础设施、Expr、tactic 编写、目标管理、typeclass
Part II  Ch7–Ch14   simp、ring、omega、linarith、norm_num、aesop、grind、decide
Part III Ch15–Ch20  positivity、fun_prop、gcongr、field_simp、逻辑变换、自定义自动化
Part IV  Ch21–Ch25  反射、性能、外部工具、方法论、分析自动化展望
```
:::

Part I 和 Part II 提供后续章节共用的基础，建议按顺序阅读。Part III 可按任务选择；Part IV 偏重架构和方法论，初读时不必完成所有实现。
