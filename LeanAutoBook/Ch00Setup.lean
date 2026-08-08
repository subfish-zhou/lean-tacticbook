import VersoManual
import LeanTacticBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "examples"
set_option verso.exampleModule "Examples.Ch00Setup"

#doc (Manual) "环境与运行约定" =>
%%%
file := "Ch00Setup"
tag := "ch00-setup"
%%%

> *本章目标*：搭好与本书一致的环境，理解代码块标签，并运行最小示例验证配置。
>
> *版本基准*：Lean 工具链 `leanprover/lean4:v4.32.2`；Mathlib revision `905b95818eb3`。
>
> 本书所有可运行代码均在上述版本上校验。配套仓库 `examples/` 中包含相应示例。元编程 API 可能在小版本间发生不兼容变化。

\[可运行\]
```bashFence
cat examples/lean-toolchain
rg -n '905b95818eb3' examples/lake-manifest.json
cd examples
lake env lean --version
```

`cat` 和 `rg` 应分别显示 `leanprover/lean4:v4.32.2` 与 Mathlib revision `905b95818eb3`。进入 `examples/` 后，`lake env lean --version` 显示项目实际调用的 Lean 版本。


# 你需要什么基础
%%%
tag := "prerequisites"
%%%

打开本书之前，我假设你已经能：

- 看懂 `α → β` 和 `List α` 这类类型写法；
- 写点简单的 Lean 定义、命题和证明；
- 用 `by simp`、`by ring`、`by intro h; exact h` 之类的基础 tactic；
- 在 VS Code 的 Lean Infoview 里看目标和错误。

*不*要求预先掌握 typeclass、monad，也不要求读过函数式编程材料。第一章从 tactic 读取和修改的状态讲起，再逐步引入 monad，而不是从抽象定义开始。

如果你还没有写过 Lean 代码，建议先读完 *Mathematics in Lean* 的前几章。本书的排错过程要求你根据目标状态判断 tactic 执行前后的变化，因此至少应熟悉 `example`、`theorem`、`by` 以及 Infoview 中的目标显示。


# 使用本书的配套项目
%%%
tag := "companion-project"
%%%

装了 Lean 不等于装了 Mathlib。你在一个没配 Mathlib 依赖的目录下写 `import Mathlib`，得到的就是：

\[示意\]
```
unknown module prefix 'Mathlib'
```

本书固定使用配套仓库中的 `examples/` 项目。不要另建一个仅版本相近的项目来验证示例；Lean 元编程 API 对版本差异敏感，声明签名或结构字段的变化都可能使后续代码无法编译。

进入项目，拉缓存：

\[可运行\]
```bashFence
cd examples
lake exe cache get
```

写一个最小测试文件：

\[可运行\]
```bashFence
cat > Test.lean <<'EOF'
import Mathlib

#check Nat.add_comm
EOF
lake env lean Test.lean
```

你应该看到下面的类型，或与之等价的表示：

\[示意\]
```leanBug
Nat.add_comm : ∀ (n m : Nat), n + m = m + n
```

若 `lake env lean Test.lean` 成功退出并显示上述类型，说明项目能够加载 Mathlib 并通过 Lean 检查。

## 常见项目问题
%%%
tag := "project-troubleshooting"
%%%

*问题 1：`lake exe cache get` 下载失败*

Mathlib 缓存需要联网下载。先确认网络连通；如需代理，可只为当前 shell 设置代理变量：

\[可运行\]
```bashFence
export https_proxy=http://your-proxy:port
lake exe cache get
```

代理地址应替换为实际使用的地址。如果无法下载缓存，`lake build` 会改为从源码编译依赖，耗时可能显著增加，具体取决于机器性能。

*问题 2：编译时冒出一大堆 Mathlib 构建任务*

十有八九是缓存没拉全。回到 `examples/` 根目录重新执行：

\[可运行\]
```bashFence
lake exe cache get
```

*问题 3：`import Mathlib` 还是报模块不存在*

检查一下位置和命令：

\[可运行\]
```bashFence
pwd
ls lean-toolchain lake-manifest.json
lake env lean Test.lean
```

第二条列不到这两个文件，说明当前目录不是 `examples/` 项目根目录。


# 术语约定：elaboration 译作"精译"
%%%
tag := "elaboration-translation"
%%%

本书把 *elaboration* 译作 *精译*，首次出现时并列标出英文。先区分它与 parsing，因为后文需要分别讨论两个阶段。

你敲下一段文本之后，Lean 先做 *parsing*：parser 按语法规则把字符序列变成 `Syntax`。比如 `f x` 被识别成一个函数应用语法节点。这一阶段只关心语法结构，还没产出核心表达式 `Expr`。

parsing 之后才是 *精译（elaboration）*。elaborator 拿着 `Syntax`，在环境和预期类型的帮助下做这些事：

- 解析名字指向哪个声明；
- 消解重载，比如决定 `+` 是哪个加法；
- 补齐省略的隐式参数；
- 综合 typeclass 实例；
- 建立并求解类型约束；
- 项精译产出核心 `Expr`；命令精译产出对环境、消息等的副作用。

因此，本文所称"精译"是指 parsing 之后，利用类型信息把 `Syntax` 转换为 `Expr`，或产生相应命令效果的阶段。

中文资料对 elaboration 尚无统一译名。阅读其他资料时，常见译法及其含义差异如下：

- *精译*（本书采用）：强调从表面语法到精确核心表示的转换，适合中文行文；但它不是通行译名，检索旧资料时仍需使用 elaboration 或其他旧译。
- *精化*：已在部分类型论和程序验证资料中使用；但容易与 refinement 及其相关术语混淆，不同资料的适用范围也不一致。
- *繁饰*：在部分旧资料中出现；但字面容易让人误以为主要工作是修饰语法，不能准确覆盖名字解析和约束求解。
- *详述／详释*：接近英文的一般词义；但脱离编译器语境后，译名本身无法标明技术边界。
- *保留 elaboration*：便于检索官方文档和源码；但中文行文会持续夹用英文。

由于"精译"尚非通行译名，检索资料时还应同时使用 elaboration、"精化"和"繁饰"等关键词。我会在本书的术语表、索引以及所维护的 Lean 中文社区术语内容中保留这些对应关系，使新译名与既有资料仍能互相检索。采用新词的短期代价是检索不便，长期收益是本书与社区内容的口径一致。

阅读其他资料时，应根据上下文判断这些词是否指本文定义的 elaboration 阶段。


# tactic 来自哪里
%%%
tag := "tactic-origins"
%%%

"Lean 装好了"和"某个 tactic 能用"是两件事。tactic 可能来自 Lean 自带模块、独立包，也可能来自 Mathlib。哪怕 tactic 本身能用，它能利用的定理集合也取决于你 import 了什么。

下表列出本书环境里的来源和*最小推荐 import*。这里的"推荐"是清楚、稳定优先，不追求把 import 缩到最短：

- `simp`：*主要来源* Lean；*最小推荐 import* `import Lean`；*说明* 核心 `simp` 可用，但能化简哪些定理取决于你 import 了什么
- `omega`：*主要来源* Lean；*最小推荐 import* `import Lean.Elab.Tactic.Omega`；*说明* Presburger 算术
- `grind`：*主要来源* Lean；*最小推荐 import* `import Lean.Elab.Tactic.Grind`；*说明* 通用自动化框架
- `decide`：*主要来源* Lean；*最小推荐 import* `import Lean`；*说明* 通过可判定性构造证明
- `aesop`：*主要来源* 独立 Aesop 包；*最小推荐 import* `import Aesop`；*说明* 不是 Lean 自带；Mathlib 项目一般都依赖了它
- `ring` / `ring_nf`：*主要来源* Mathlib；*最小推荐 import* `import Mathlib.Tactic.Ring`；*说明* 交换半环、环等代数规范化
- `linarith` / `nlinarith`：*主要来源* Mathlib；*最小推荐 import* `import Mathlib.Tactic.Linarith`；*说明* 线性／非线性算术
- `polyrith`：*主要来源* Mathlib；*最小推荐 import* `import Mathlib.Tactic.Polyrith`；*说明* 多项式等式推导
- `norm_num`：*主要来源* Mathlib；*最小推荐 import* `import Mathlib.Tactic.NormNum`；*说明* 数值规范化
- `positivity`：*主要来源* Mathlib；*最小推荐 import* `import Mathlib.Tactic.Positivity`；*说明* 正性目标
- `field_simp`：*主要来源* Mathlib；*最小推荐 import* `import Mathlib.Tactic.FieldSimp`；*说明* 消分母并生成非零条件
- `gcongr`：*主要来源* Mathlib；*最小推荐 import* `import Mathlib.Tactic.GCongr`；*说明* 广义单调性／合同推理
- `fun_prop`：*主要来源* Mathlib；*最小推荐 import* `import Mathlib.Tactic.FunProp`；*说明* 函数性质自动化

本书大部分证明示例直接写：

\[可运行\]
```leanFence
import Mathlib
```

这样会导入 Mathlib 的统一入口，便于学习和实验。编写库代码时再按实际依赖精简 import。


# 本书的代码标注
%%%
tag := "code-conventions"
%%%

书里每个 fenced code block 前都会显式标注类别。*没有"未标注即默认可运行"这条规则*；未标注的代码块视为编辑遗漏，请提交 issue。

- *\[可运行\]*：在指定环境里直接跑得动。依赖前文定义时，正文会说明依赖了哪些。
- *\[示意\]*：语法或输出片段，为了解释某个局部机制；可能省略 import、外围定义或输出中的非关键部分。
- *\[伪代码\]*：讲算法或数据流用的，不是 Lean、shell 或任何真语言的可执行代码。
- *\[练习·故意错误\]*：*故意*写错的代码；任务是先看错误、再动手修。
- *\[源码节选\]*：从 Lean 源码里节选出来的，可能省略与本章无关的字段，或者补齐命名空间方便阅读；不承诺逐字与源码一致，但类型和结构等价。

练习中还会使用 *\[练习模板\]*。它不是独立的代码类别，而是练习标签的补充。模板可以包含 `sorry`，因此文件可能通过编译；只有替换全部 `sorry` 后才算完成练习。代码块会明确标注 *\[练习模板\]*，以区分"能够编译"和"证明已经完成"。

以下示例展示各类标签的用法：

\[可运行\]
```leanFence
import Mathlib

example (x : ℝ) : x + 0 = x := by
  simp
```

\[示意\]
```leanBug
elab "my_tactic" : tactic => do
  let goal ← getMainGoal
  -- 这里省略具体实现
```

\[伪代码\]
```
收集线性约束
规范化每个约束
逐步消去变量
检查是否导出矛盾
```

\[练习·故意错误\]
```leanBug
import Mathlib

example : False := by
  trivial
```

最后一段会在 `trivial` 处失败；它用于展示"故意错误"标签，不是可通过编译的答案。


# 跟着本书跑代码
%%%
tag := "learning-tips"
%%%

1. 先确认当前目录是 `examples/`，用 `lake env lean` 跑，别用裸 `lean`。
2. 先原样运行 `\[可运行\]` 示例，确认通过后再修改。若随后出错，便能区分问题来自原示例还是自己的改动。
3. 遇到 `\[练习·故意错误\]`，先把完整错误信息记下来再动代码。只盯最后一行常常错过真正的类型不匹配位置。
4. 每次只改变一个因素。例如比较 `simp` 和 `ring` 时，不要同时更换类型、修改命题并增加假设，否则无法判断结果由哪项变化造成。
5. 使用 VS Code 的 Go to Definition 和 `#check` 核对 API。元编程函数名称相近，不应仅凭记忆补写参数。


# 全书结构
%%%
tag := "book-overview"
%%%

\[示意\]
```leanBug
Part I   Ch1–Ch6    tactic 心智模型、tactic 基础设施、Expr、tactic 编写、目标管理、typeclass
Part II  Ch7–Ch14   simp、ring、omega、linarith、norm_num、aesop、grind、decide
Part III Ch15–Ch20  positivity、fun_prop、gcongr、field_simp、逻辑变换、自定义自动化
Part IV  Ch21–Ch25  反射、性能、外部工具、方法论、分析自动化展望
```

Part I 和 Part II 提供后续章节共用的基础，建议按顺序阅读。Part III 可按任务选择；Part IV 偏重架构和方法论，初读时不必完成所有实现。


# 环境验证练习
%%%
tag := "setup-exercises"
%%%

## 练习 0.1（热身）：跑通项目、看到输出
%%%
tag := "exercise-0-1"
%%%

\[可运行\]
```leanFence
import Mathlib

#check Nat.add_comm
#eval 2 + 3
```

*做完的样子*：文件编译通过；`#check` 打出 `Nat.add_comm` 的类型；`#eval` 输出 `5`。

## 练习 0.2（热身）：跑两个基础 tactic
%%%
tag := "exercise-0-2"
%%%

\[可运行\]
```leanFence
import Mathlib

example : 2 + 3 = 5 := by
  norm_num

example (n : ℕ) : n + 0 = n := by
  simp
```

*做完的样子*：两个 example 都没有未解决目标，也没有 `sorry`。

## 练习 0.3（debug）：认识 tactic 的适用边界
%%%
tag := "exercise-0-3"
%%%

下面故意使用 `omega` 处理一个非线性整数等式。`omega` 面向 Presburger 算术，可以处理相应的线性加法约束，但不支持变量之间的乘法。因此该证明不会成功：

\[练习·故意错误\]
```leanBug
import Mathlib

example (x y : ℤ) : (x + y) * (x + y) = x * x + 2 * x * y + y * y := by
  omega
```

按下面顺序排错：

1. 查看完整错误信息或剩余目标，确认 `omega` 未能关闭该目标；
2. 用 `#check`、Go to Definition 或文档核对 `omega` 的适用范围；
3. 观察目标中含有变量乘法，并判断它是多项式恒等式；
4. 将 `omega` 替换为适用于多项式规范化的 `ring`。

\[可运行\]
```leanFence
import Mathlib

example (x y : ℤ) : (x + y) * (x + y) = x * x + 2 * x * y + y * y := by
  ring
```

*做完的样子*：故意错误版本不能关闭目标；替换为 `ring` 后，文件编译通过。错误文本的具体措辞可能随版本或调用路径变化。

## 练习 0.4（综合）：看目标挑 tactic
%%%
tag := "exercise-0-4"
%%%

下面的练习模板包含 `sorry`，因此初始文件能够编译。请逐个替换这些占位符；完成时文件中不得保留 `sorry`。

\[练习模板\]
```leanBug
import Mathlib

example : (3 : ℤ) + 4 = 7 := by
  sorry

example : (10 : ℕ) < 20 := by
  sorry

example (n : ℕ) : n + n = 2 * n := by
  sorry
```

从 `norm_num`、`omega`、`simp`、`ring`、`decide` 中为每个目标选择 tactic。对每个目标逐一记录哪些候选能成功、哪些会失败，并说明失败原因。例如，含变量的多项式恒等式通常不适合仅做数值规范化的 `norm_num`。动手前先作判断，运行后再用结果修正自己的适用范围模型。

*做完的样子*：三个 example 均编译通过，文件中没有 `sorry`；五个候选在各目标上的成败都有记录，每项判断都能用目标结构和 tactic 的适用范围解释。
