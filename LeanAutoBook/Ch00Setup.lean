import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch00Setup"

#doc (Manual) "环境与运行约定" =>
%%%
file := "Ch00Setup"
tag := "ch00-setup"
%%%

> **本章目标**：把环境搭到跟本书完全一致，弄清代码块上的那些方框各自什么意思，然后跑一个最小示例确认没问题。
>
> **版本基准**：Lean 工具链 `leanprover/lean4:v4.30.0-rc1`；Mathlib revision `0692ef80fb13`。
>
> 本书所有可运行代码都在这个版本上校验过。以配套仓库 `examples/` 里的 `lean-toolchain` 和 `lake-manifest.json` 为准——它们才是唯一权威，别用你机器上全局装的 Lean 去验证书里的例子，元编程 API 一个小版本就够翻脸。

\[可运行\]
```bashFence
cat examples/lean-toolchain
rg -n '0692ef80fb13' examples/lake-manifest.json
cd examples
lake env lean --version
```

跑完前两条你应该看到 `leanprover/lean4:v4.30.0-rc1` 和那串 Mathlib revision；第三条告诉你项目实际调用的 Lean 是哪个版本。三条都对得上，环境就锁死了。


# 你需要什么基础
%%%
tag := "prerequisites"
%%%

打开本书之前，我假设你已经能：

- 看懂 `α → β` 和 `List α` 这类类型写法；
- 写点简单的 Lean 定义、命题和证明；
- 用 `by simp`、`by ring`、`by intro h; exact h` 之类的基础 tactic；
- 在 VS Code 的 Lean Infoview 里看目标和错误。

**不**要求你懂 typeclass、monad，或者读过任何函数式编程材料。第一章会从"tactic 到底要读什么、要改什么"开始，一步步把 monad 讲出来，不会直接把定义式砸到你脸上。

如果你连 Lean 代码都还没写过，先去过一遍 *Mathematics in Lean* 的头几章再回来。本书后面每一处排错都要你根据目标状态判断刚才那步 tactic 做了什么；如果 `example` / `theorem` / `by` 你都还没习惯，各种困难堆到一起就没法定位。


# 安装 Lean 4
%%%
tag := "install-lean4"
%%%

Lean 靠 `elan` 装。`elan` 是版本管理器，负责下载和切换 Lean 工具链；每个项目根目录下的 `lean-toolchain` 文件决定这个项目用哪个版本。

\[可运行\]
```bashFence
curl https://elan.lean-lang.org/install.sh -sSf | sh
export PATH="$HOME/.elan/bin:$PATH"
elan --version
```

编辑器我推荐 VS Code + Lean 4 扩展。打开项目时**打开整个项目文件夹**，别只打开单个 `.lean` 文件——Lean 扩展需要从项目根目录读 `lean-toolchain` 和 `lakefile.toml`（或 `lakefile.lean`），拿不到就没法加载。

## 常见安装问题
%%%
tag := "install-troubleshooting"
%%%

**问题 1：装完找不到 `lean` 或 `elan`**

`elan` 默认把可执行文件放在 `~/.elan/bin`。把这个目录加进 `PATH`，然后同样一行写进你的 shell 配置（`~/.bashrc` 或 `~/.zshrc`），以后开新终端就不用再手动 export 了。

\[可运行\]
```bashFence
export PATH="$HOME/.elan/bin:$PATH"
```

**问题 2：`lean --version` 报 `no default toolchain configured`**

说明 elan 装好了，但当前目录没有 `lean-toolchain`、本机也没设默认工具链。别慌，也别急着 `elan default` 去选一个——那样很容易挑错版本，跟本书对不上。正确做法是 `cd` 进配套仓库的 `examples/` 目录再运行，`elan` 会看着那里的 `lean-toolchain` 自动下载对应版本：

\[可运行\]
```bashFence
lake env lean --version
```

**问题 3：VS Code 扩展没加载项目**

按顺序自检：

1. 打开的是项目**目录**，不是单个 `.lean` 文件；
2. 项目根目录有 `lean-toolchain`；
3. 项目根目录有 Lake 配置（`lakefile.toml` 或 `lakefile.lean`）；
4. 右下角状态栏没长期停在 `Loading...`；
5. 终端里 `lake env lean --version` 跑得通。

一条一条来，通常在 1 或 2 就能发现问题。

**问题 4：VS Code 里能 `import Mathlib`，终端里不行**

多半是你在终端里没进项目根目录，或者直接跑了裸 `lean File.lean` 而不是 `lake env lean File.lean`。裸 `lean` 不走 Lake 配置，找不到依赖模块。


# 使用本书的配套项目
%%%
tag := "companion-project"
%%%

装了 Lean 不等于装了 Mathlib。你在一个没配 Mathlib 依赖的目录下写 `import Mathlib`，得到的就是：

\[示意\]
```
unknown module prefix 'Mathlib'
```

本书**唯一**的固定运行环境是配套仓库的 `examples/` 项目。不要自己另建一个"差不多版本"的项目验证书里的代码——Lean 元编程 API 对版本非常敏感，签名一个字段变了下游全炸。这不是保守，是被坑出来的经验。

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

你应该看到这样的类型（或者字面等价的）：

\[示意\]
```
Nat.add_comm : ∀ (n m : Nat), n + m = m + n
```

看到这个，环境就通了。

## 常见项目问题
%%%
tag := "project-troubleshooting"
%%%

**问题 1：`lake exe cache get` 下载失败**

Mathlib 缓存从网络下载。先检查网络、再看代理。需要代理时可以只对当前 shell 设一次：

\[可运行\]
```bashFence
export https_proxy=http://your-proxy:port
lake exe cache get
```

代理地址请换成你自己的。缓存完全拉不下来时，`lake build` 会退化成从源码编译依赖，可能会很久，也可能非常久，取决于机器——反正你会有充足时间去干点别的。

**问题 2：编译时冒出一大堆 Mathlib 构建任务**

十有八九是缓存没拉全。回到 `examples/` 根目录重新执行：

\[可运行\]
```bashFence
lake exe cache get
```

**问题 3：`import Mathlib` 还是报模块不存在**

检查一下位置和命令：

\[可运行\]
```bashFence
pwd
ls lean-toolchain lake-manifest.json
lake env lean Test.lean
```

第二条列不到那两个文件，说明你根本没在 `examples/` 项目根目录。


# 术语约定：elaboration 译作"精译"
%%%
tag := "elaboration-translation"
%%%

本书把 **elaboration** 译作 **精译**，第一次出现时英文并列写出。开工之前，先把它跟 parsing 划清界限——因为后面章节这两者要分开谈。

你敲下一段文本之后，Lean 先做 **parsing**：parser 按语法规则把字符序列变成 `Syntax`。比如 `f x` 被识别成一个函数应用语法节点。这一阶段只关心语法结构，还没产出核心表达式 `Expr`。

parsing 之后才是 **精译（elaboration）**。elaborator 拿着 `Syntax`，在环境和预期类型的帮助下做这些事：

- 解析名字指向哪个声明；
- 消解重载，比如决定 `+` 是哪个加法；
- 补齐省略的隐式参数；
- 综合 typeclass 实例；
- 建立并求解类型约束；
- 项精译产出核心 `Expr`；命令精译产出对环境、消息等的副作用。

所以本书说"精译"，指的是 parsing **之后**、从 `Syntax` 到 `Expr`（或到环境效果）的那一段带类型信息的处理。后文说"把语法精译成表达式"，说的就是这段。

中文界对 elaboration 没有完全统一的译名。下面只列你阅读时会遇到的主要选择——每一条都同时写它的优点和它的代价：

- **精译**（本书采用）：**优点**——强调"从表面语法到精确核心表示的翻译"这层意思，中文行文顺；**代价**——是新词，读者短期检索命中率低，搜旧资料时不容易匹配。
- **精化**：**优点**——已在部分类型论和程序验证资料中出现，有点读者基础；**代价**——和 refinement 及其相关术语容易搞混，各资料的使用范围也不统一。
- **繁饰**：**优点**——历史用法留了痕迹，读旧文时能对上；**代价**——字面像"给语法加装饰"，会误导初学者以为主要工作是修饰，覆盖不了名字解析和约束求解。
- **详述／详释**：**优点**——接近英文一般词义；**代价**——脱离编译器语境，光看译名判断不出技术边界。
- **保留 elaboration**：**优点**——查官方文档、源码标识、英文搜索都直接对得上；**代价**——中文行文中英夹杂，读者还得记英文词形。

选"精译"的代价是明摆着的：它不是现成共识，读者初期查资料会不顺手。我同时在维护 Lean 中文社区的相关术语内容，会在术语表、索引、社区资料里把"精化""繁饰"这些旧译对齐到"精译"，并保留英文 elaboration 作为检索入口。这是一次性的短期代价，换本书、术语表、社区内容三处口径一致的长期收益。

你在别的资料里看到 elaboration、精化、繁饰时，请先根据上下文判断作者说的到底是哪一段过程；在本书里，它们都对应上面定义的、parsing 之后到 `Expr`（或命令效果）之前的这一段。


# tactic 来自哪里
%%%
tag := "tactic-origins"
%%%

"Lean 装好了"和"某个 tactic 能用"是两件事。tactic 可能来自 Lean 自带模块、独立包，也可能来自 Mathlib。哪怕 tactic 本身能用，它能利用的定理集合也取决于你 import 了什么。

下表列出本书环境里的来源和**最小推荐 import**。这里的"推荐"是清楚、稳定优先，不追求把 import 缩到最短：

- `simp`：**主要来源** Lean；**最小推荐 import** `import Lean`；**说明** 核心 `simp` 可用，但能化简哪些定理取决于你 import 了什么
- `omega`：**主要来源** Lean；**最小推荐 import** `import Lean.Elab.Tactic.Omega`；**说明** Presburger 算术
- `grind`：**主要来源** Lean；**最小推荐 import** `import Lean.Elab.Tactic.Grind`；**说明** 通用自动化框架
- `decide`：**主要来源** Lean；**最小推荐 import** `import Lean`；**说明** 通过可判定性构造证明
- `aesop`：**主要来源** 独立 Aesop 包；**最小推荐 import** `import Aesop`；**说明** 不是 Lean 自带；Mathlib 项目一般都依赖了它
- `ring` / `ring_nf`：**主要来源** Mathlib；**最小推荐 import** `import Mathlib.Tactic.Ring`；**说明** 交换半环、环等代数规范化
- `linarith` / `nlinarith`：**主要来源** Mathlib；**最小推荐 import** `import Mathlib.Tactic.Linarith`；**说明** 线性／非线性算术
- `polyrith`：**主要来源** Mathlib；**最小推荐 import** `import Mathlib.Tactic.Polyrith`；**说明** 多项式等式推导
- `norm_num`：**主要来源** Mathlib；**最小推荐 import** `import Mathlib.Tactic.NormNum`；**说明** 数值规范化
- `positivity`：**主要来源** Mathlib；**最小推荐 import** `import Mathlib.Tactic.Positivity`；**说明** 正性目标
- `field_simp`：**主要来源** Mathlib；**最小推荐 import** `import Mathlib.Tactic.FieldSimp`；**说明** 消分母并生成非零条件
- `gcongr`：**主要来源** Mathlib；**最小推荐 import** `import Mathlib.Tactic.GCongr`；**说明** 广义单调性／合同推理
- `fun_prop`：**主要来源** Mathlib；**最小推荐 import** `import Mathlib.Tactic.FunProp`；**说明** 函数性质自动化

本书大部分证明示例直接写：

\[可运行\]
```leanFence
import Mathlib
```

这样一次性把 Mathlib 大接口全拉进来，学习和实验都方便。真正写库代码时你可以再按依赖精简 import。


# 本书的代码标注
%%%
tag := "code-conventions"
%%%

书里每一个 fenced code block 前都会显式标一个类别。**没有"不标就默认可运行"这条规则**——凡是没标的都当我漏了，请提 issue。

- **\[可运行\]**：在指定环境里直接跑得动。依赖前文定义时，正文会说明依赖了哪些。
- **\[示意\]**：语法或输出片段，为了解释某个局部机制；可能省略 import、外围定义或输出中的非关键部分。
- **\[伪代码\]**：讲算法或数据流用的，不是 Lean、shell 或任何真语言的可执行代码。
- **\[练习·故意错误\]**：**故意**写错的代码；任务是先看错误、再动手修。
- **\[源码节选\]**：从 Lean 源码里节选出来的，可能省略与本章无关的字段，或者补齐命名空间方便阅读；不承诺逐字与源码一致，但类型和结构等价。

练习中还会看到 **\[练习模板\]**。它不是独立类别，而是练习标签的补充：模板里可以有 `sorry`，所以文件本身能编译过，但你必须替换掉 `sorry` 才算完成练习。代码块本身会明确写 `\[练习模板\]`，防止你把"能编译"误当成"证完了"——`sorry` 特别擅长制造这种虚假的平静。

来看每种标签实际的样子：

\[可运行\]
```leanFence
import Mathlib

example (x : ℝ) : x + 0 = x := by
  simp
```

\[示意\]
```
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

最后这段肯定报错——它是练习示例，不是可以复制走的答案。


# 跟着本书跑代码
%%%
tag := "learning-tips"
%%%

1. 先确认当前目录是 `examples/`，用 `lake env lean` 跑，别用裸 `lean`。
2. 先**原样**跑 `\[可运行\]` 例子，跑通了再动手改。这样出错时你知道是"原例的问题"还是"改坏了"。
3. 遇到 `\[练习·故意错误\]`，先把完整错误信息记下来再动代码。只盯最后一行常常错过真正的类型不匹配位置。
4. 每次只改一个变量。比较 `simp` 和 `ring` 时不要同时换类型、改命题、加假设——三个变量一起动，任何结论都不可靠。
5. 用 VS Code 的 Go to Definition 和 `#check` 核对 API。元编程函数名字长得很像，凭印象补参数的成功率不值得赌。


# 全书结构
%%%
tag := "book-overview"
%%%

\[示意\]
```
Part I   Ch1–Ch5    元编程模型、Expr、tactic 编写、目标管理、typeclass
Part II  Ch6–Ch13   simp、ring、omega、linarith、norm_num、aesop、grind、decide
Part III Ch14–Ch19  positivity、fun_prop、gcongr、field_simp、逻辑变换、自定义自动化
Part IV  Ch20–Ch24  反射、性能、外部工具、方法论、分析自动化展望
```

Part I 和 Part II 是后面所有章节的共同基础，建议按顺序读。Part III 按任务挑着看；Part IV 更偏架构和方法论，第一遍读不需要每个都动手实现。


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

**做完的样子**：文件编译通过；`#check` 打出 `Nat.add_comm` 的类型；`#eval` 输出 `5`。

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

**做完的样子**：两个 example 都没有未解决目标，也没有 `sorry`。

## 练习 0.3（debug）：认识 tactic 的适用边界
%%%
tag := "exercise-0-3"
%%%

下面**故意**拿 `omega` 去处理一个非线性整数等式。`omega` 只处理 Presburger 算术——线性的部分，不允许变量乘变量。所以这段肯定不行：

\[练习·故意错误\]
```leanBug
import Mathlib

example (x y : ℤ) : (x + y) * (x + y) = x * x + 2 * x * y + y * y := by
  omega
```

按下面顺序排错：

1. 看错误或剩余目标，确认它抱怨的是变量乘法 `x * y`；
2. 用 `#check` 或文档确认 `omega` 只处理线性算术；
3. 判断出目标是个多项式恒等式；
4. 把 `omega` 换成 `ring`。

\[可运行\]
```leanFence
import Mathlib

example (x y : ℤ) : (x + y) * (x + y) = x * x + 2 * x * y + y * y := by
  ring
```

**做完的样子**：故意错误版本关不了目标，报错跟"非线性"或"tactic 失败"有关；修好的版本编译通过。

## 练习 0.4（综合）：看目标挑 tactic
%%%
tag := "exercise-0-4"
%%%

下面是含 `sorry` 的练习模板。`sorry` 让整个文件先能编译过；你的任务是逐个替换掉，交作业时文件里不能剩 `sorry`。

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

从 `norm_num`、`omega`、`simp`、`ring`、`decide` 里挑。不光要挑对，还要记下哪个能成、哪个失败——失败的写一句原因，比如"目标是变量的代数恒等式，`norm_num` 只做数值规范化，管不了"。练手的意义不在得答案，在于每次挑 tactic 之前脑子里能预判它能不能干这活。

**做完的样子**：三个 example 都编译通过；文件里没有 `sorry`；每一个你选的 tactic，你能说清它利用了目标的哪种结构。
