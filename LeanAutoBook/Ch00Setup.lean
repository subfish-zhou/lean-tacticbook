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

> **本章目标**：搭好与本书一致的 Lean 环境，理解代码标注制度，并确认最小示例可以编译。
>
> **固定校验基准**：Lean 工具链 `leanprover/lean4:v4.30.0-rc1`；Mathlib revision `0692ef80fb13`。
>
> 本书对版本相关的命令、API 和 tactic 行为，只承诺与配套仓库 `examples/` 目录中的 `lean-toolchain` 和 `lake-manifest.json` 一致。遇到差异时，以这两个文件为准，不以本机全局安装的 Lean 版本为准。

\[可运行\]
```bashFence
cat examples/lean-toolchain
rg -n '0692ef80fb13' examples/lake-manifest.json
cd examples
lake env lean --version
```

第一条命令应显示 `leanprover/lean4:v4.30.0-rc1`；第二条应在 Mathlib 条目中找到 revision `0692ef80fb13`。第三条显示当前项目真正调用的 Lean 版本。


# 你需要什么基础
%%%
tag := "prerequisites"
%%%

本书假设你已经能：

- 看懂函数类型 `α → β` 和参数化类型 `List α`；
- 写简单的 Lean 定义、定理和证明；
- 使用 `by simp`、`by ring`、`by intro h; exact h` 一类基础证明；
- 在 VS Code 的 Lean Infoview 中查看目标和错误信息。

本书不要求你预先理解 typeclass、monad 或函数式编程术语。第一章会从 tactic 需要读取什么、修改什么开始解释 monad，不把定义式直接扔到你脸上然后假装教学已经完成。

如果你没有写过 Lean 代码，先学习 *Mathematics in Lean* 的前几章，再回到这里。后文会频繁要求你根据目标状态判断 tactic 做了什么；如果 `example`、`theorem`、`by` 仍然陌生，后面的困难会混在一起，不利于排错。


# 安装 Lean 4
%%%
tag := "install-lean4"
%%%

Lean 通常通过 `elan` 管理。`elan` 负责下载并切换 Lean 工具链；项目根目录中的 `lean-toolchain` 决定该项目使用哪一个版本。

\[可运行\]
```bashFence
curl https://elan.lean-lang.org/install.sh -sSf | sh
export PATH="$HOME/.elan/bin:$PATH"
elan --version
```

安装后，建议使用 VS Code 和 Lean 4 扩展。打开项目时要打开整个项目目录，而不是只打开一个 `.lean` 文件。Lean 扩展需要从项目目录读取 `lean-toolchain`、`lakefile.toml` 或 `lakefile.lean` 等配置。

## 常见安装问题
%%%
tag := "install-troubleshooting"
%%%

**问题 1：安装后找不到 `lean` 或 `elan`**

`elan` 默认把可执行文件放在 `~/.elan/bin`。把这个目录加入 `PATH`，并将同一行写入你的 shell 配置文件，例如 `~/.bashrc` 或 `~/.zshrc`。

\[可运行\]
```bashFence
export PATH="$HOME/.elan/bin:$PATH"
```

**问题 2：`lean --version` 报 `no default toolchain configured`**

这表示 `elan` 已安装，但当前目录没有项目工具链，本机也没有默认工具链。进入带有 `lean-toolchain` 的项目目录后，`elan` 会按文件内容选择并下载对应版本。对本书而言，应进入配套仓库的 `examples/` 目录，再运行：

\[可运行\]
```bashFence
lake env lean --version
```

**问题 3：VS Code 扩展没有加载项目**

依次检查：

1. VS Code 打开的是项目目录；
2. 项目根目录存在 `lean-toolchain`；
3. 项目根目录存在 Lake 配置；
4. 右下角 Lean 状态没有长期停在 `Loading...`；
5. 终端中的 `lake env lean --version` 能正常运行。

**问题 4：VS Code 中能导入模块，终端中却失败**

先确认终端位于同一个项目根目录，再使用 `lake env lean File.lean`。裸命令 `lean File.lean` 可能没有使用 Lake 项目配置。


# 使用本书的配套项目
%%%
tag := "companion-project"
%%%

仅安装 Lean 不等于安装 Mathlib。不在配置了 Mathlib 依赖的 Lake 项目中写 `import Mathlib`，通常会得到：

\[示意\]
```
unknown module prefix 'Mathlib'
```

本书的固定运行环境是配套仓库中的 `examples/` 项目。不要另建一个“差不多版本”的项目来验证本书代码；Lean 元编程 API 对版本较敏感，一个小版本差异就可能让函数签名变化。

进入项目并获取缓存：

\[可运行\]
```bashFence
cd examples
lake exe cache get
```

新建一个最小测试文件：

\[可运行\]
```bashFence
cat > Test.lean <<'EOF'
import Mathlib

#check Nat.add_comm
EOF
lake env lean Test.lean
```

你应看到与下面相同或等价的类型：

\[示意\]
```
Nat.add_comm : ∀ (n m : Nat), n + m = m + n
```

## 常见项目问题
%%%
tag := "project-troubleshooting"
%%%

**问题 1：`lake exe cache get` 下载失败**

Mathlib 缓存通过网络下载。先检查网络和代理配置。需要代理时，可以只对当前 shell 设置：

\[可运行\]
```bashFence
export https_proxy=http://your-proxy:port
lake exe cache get
```

代理地址必须替换成你实际使用的地址。若缓存无法取得，`lake build` 会尝试从源码构建依赖，耗时通常明显更长。

**问题 2：编译时出现大量 Mathlib 构建任务**

这通常说明缓存没有完整下载。重新在 `examples/` 根目录执行：

\[可运行\]
```bashFence
lake exe cache get
```

**问题 3：`import Mathlib` 仍然报模块不存在**

检查当前目录和实际命令：

\[可运行\]
```bashFence
pwd
ls lean-toolchain lake-manifest.json
lake env lean Test.lean
```

如果第二条命令找不到文件，你不在本书的 `examples/` 项目根目录。


# 术语约定：elaboration 译作“精译”
%%%
tag := "elaboration-translation"
%%%

本书把 **elaboration** 译作 **精译**，并在第一次出现时保留英文。先划清它与 parsing 的边界。

你写下文本后，Lean 首先由 parser 进行 **parsing**：parser 按语法规则把字符序列变成 `Syntax`。例如，字符 `f x` 会先被识别为函数应用语法。这个阶段主要关心语法结构，还没有产出核心表达式 `Expr`。

随后才进入本书所说的 **精译（elaboration）**。elaborator 在当前环境和预期类型的帮助下处理 `Syntax`，包括：

- 解析名字指向哪个声明；
- 消解重载，例如决定 `+` 是哪一个加法；
- 插入省略的隐式参数；
- 综合所需的 typeclass 实例；
- 建立并求解类型约束；
- 对项产生核心 `Expr`，或对命令产生相应的环境、消息等效果。

因此，本书的“精译”特指 parsing 之后的 elaboration 阶段，不把 parsing 算在其中。后文说“把语法精译成表达式”，指的是 `Syntax → Expr` 这一段带有类型信息的处理。

中文资料对 elaboration 没有完全统一的译名。下面只比较阅读时会遇到的主要选择：

- **精译**（本书采用）：**优点**：强调从表面语法到精确核心表示的翻译；中文句子较连贯；**代价或局限**：是新词；短期生态兼容性较差；读者直接搜索旧资料时不容易命中
- **精化**：**优点**：已见于部分类型论和程序验证资料；读者可能熟悉；**代价或局限**：容易与 refinement 及其相关术语混淆；不同资料中的使用范围也不完全一致
- **繁饰**：**优点**：有历史使用痕迹，能帮助识别旧文献；**代价或局限**：字面容易让初学者误以为主要工作是给语法“添加装饰”，不能自然覆盖名字解析和约束求解
- **详述／详释**：**优点**：接近英文的一般词义；**代价或局限**：编译器语境不够明确，难以单凭译名判断技术边界
- **保留 elaboration**：**优点**：便于对照官方文档、源码标识和英文搜索结果；**代价或局限**：中文行文会在中英文之间频繁切换，初学者还要额外记住英文词形

采用“精译”有明确代价：它不是现成共识，初期检索会更麻烦。本书作者同时维护 Lean 中文社区的相关术语内容，会在术语表、索引和社区资料中同步覆盖“精化”“繁饰”等旧译，并保留英文 elaboration 作为检索入口。作者的取舍是：承担短期检索成本，换取长期教材、术语表和社区内容中的一致表达。

你在其他资料中看到 elaboration、精化或繁饰时，应先根据上下文判断其范围；在本书中，它们对应这里定义的 parsing 之后、核心表达式或命令效果之前的精译阶段。


# tactic 来自哪里
%%%
tag := "tactic-origins"
%%%

“Lean 已安装”与“某个 tactic 可用”不是同一件事。一个 tactic 可能来自 Lean 自带模块、独立包，或 Mathlib。即使 tactic 本身已经导入，它可利用的定理集合仍取决于当前文件导入了什么。

下表给出本书环境中的来源和**最小推荐 import**。这里的“推荐”以清楚、稳定为目标，不追求把 import 缩到理论上的最小字符数。

- `simp`：**主要来源**：Lean；**最小推荐 import**：`import Lean`；**说明**：核心 `simp` 可用，但可化简定理集合取决于 imports
- `omega`：**主要来源**：Lean；**最小推荐 import**：`import Lean.Elab.Tactic.Omega`；**说明**：Presburger 算术
- `grind`：**主要来源**：Lean；**最小推荐 import**：`import Lean.Elab.Tactic.Grind`；**说明**：通用自动化框架
- `decide`：**主要来源**：Lean；**最小推荐 import**：`import Lean`；**说明**：通过可判定性构造证明
- `aesop`：**主要来源**：独立 Aesop 包；**最小推荐 import**：`import Aesop`；**说明**：不是 Lean core 自带组件；Mathlib 项目通常已经依赖它
- `ring` / `ring_nf`：**主要来源**：Mathlib；**最小推荐 import**：`import Mathlib.Tactic.Ring`；**说明**：交换半环、环等代数规范化
- `linarith` / `nlinarith`：**主要来源**：Mathlib；**最小推荐 import**：`import Mathlib.Tactic.Linarith`；**说明**：线性／非线性算术
- `polyrith`：**主要来源**：Mathlib；**最小推荐 import**：`import Mathlib.Tactic.Polyrith`；**说明**：多项式等式推导
- `norm_num`：**主要来源**：Mathlib；**最小推荐 import**：`import Mathlib.Tactic.NormNum`；**说明**：数值规范化
- `positivity`：**主要来源**：Mathlib；**最小推荐 import**：`import Mathlib.Tactic.Positivity`；**说明**：正性目标
- `field_simp`：**主要来源**：Mathlib；**最小推荐 import**：`import Mathlib.Tactic.FieldSimp`；**说明**：消去分母并生成非零条件
- `gcongr`：**主要来源**：Mathlib；**最小推荐 import**：`import Mathlib.Tactic.GCongr`；**说明**：广义单调性／合同推理
- `fun_prop`：**主要来源**：Mathlib；**最小推荐 import**：`import Mathlib.Tactic.FunProp`；**说明**：函数性质自动化

本书多数证明示例使用：

\[可运行\]
```leanFence
import Mathlib
```

这会导入较大的 Mathlib 接口，适合学习和实验。编写库代码时，你可以再按实际依赖缩小 import。


# 本书的代码标注
%%%
tag := "code-conventions"
%%%

每个 fenced code block 前必须显式标出以下类别之一。没有“未标注默认可运行”的规则。

- **\[可运行\]**：可在指定环境中直接执行或编译。若依赖前文定义，正文会说明依赖范围。
- **\[示意\]**：语法或输出片段，用来解释局部机制；可能省略 import、外围定义或实际输出中的非关键部分。
- **\[伪代码\]**：表达算法和数据流，不是 Lean、shell 或其他语言的可执行程序。
- **\[练习·故意错误\]**：代码有意不能通过；任务是观察错误并修复。
- **\[源码节选\]**：节选 Lean 源码，可能省略与本章无关字段，或补齐命名空间以便阅读；不保证逐字与源码一致，但类型与结构与源码等价。

练习中还会出现 **\[练习模板\]**。它不是独立的代码性质类别，而是对练习用途的补充说明：模板可以含 `sorry`，因此文件可能通过编译，但你必须替换 `sorry` 才算完成练习。代码块仍会明确写 `\[练习模板\]`，避免把“能编译”误当成“已经证明”。`sorry` 很擅长制造这种虚假的平静。

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
```
import Mathlib

example : False := by
  trivial
```

最后一段应报错；它展示的是练习类型，不是待复制进正式代码的答案。


# 跟着本书运行代码
%%%
tag := "learning-tips"
%%%

1. 先确认当前目录是 `examples/`，并使用 `lake env lean`。
2. 先原样运行 `\[可运行\]` 代码，再修改输入。这样出现错误时，你能区分“原例有问题”和“修改引入了问题”。
3. 对 `\[练习·故意错误\]`，先记录完整错误，再动代码。只看最后一行常会错过真正的类型不匹配位置。
4. 每次只改一个因素。例如比较 `simp` 与 `ring` 时，不要同时换类型、改命题、增加假设。
5. 用 VS Code 的 Go to Definition 和 `#check` 核对 API。元编程函数名相近，凭印象补参数的成功率并不值得信赖。


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

Part I 和 Part II 是后续章节的共同基础，建议按顺序阅读。Part III 可按任务选择；Part IV 更偏架构和方法，不要求第一次阅读时完成所有实现。


# 环境验证练习
%%%
tag := "setup-exercises"
%%%

## 练习 0.1（热身）：检查项目和输出
%%%
tag := "exercise-0-1"
%%%

\[可运行\]
```leanFence
import Mathlib

#check Nat.add_comm
#eval 2 + 3
```

**验收标准**：文件编译成功；`#check` 显示 `Nat.add_comm` 的类型；`#eval` 输出 `5`。

## 练习 0.2（热身）：运行两个基础 tactic
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

**验收标准**：两个 example 都没有未解决目标，也没有 `sorry`。

## 练习 0.3（debug）：识别 tactic 的边界
%%%
tag := "exercise-0-3"
%%%

下面故意用 `omega` 处理非线性整数等式。`omega` 处理 Presburger 算术，其中不允许变量与变量相乘。

\[练习·故意错误\]
```
import Mathlib

example (x y : ℤ) : (x + y) * (x + y) = x * x + 2 * x * y + y * y := by
  omega
```

按以下顺序排错：

1. 读错误或剩余目标，确认问题含有变量乘法 `x * y`；
2. 用 `#check` 或 tactic 文档确认 `omega` 的适用范围是线性整数／自然数算术；
3. 判断目标是多项式恒等式；
4. 把 `omega` 换成 `ring`。

\[可运行\]
```leanFence
import Mathlib

example (x y : ℤ) : (x + y) * (x + y) = x * x + 2 * x * y + y * y := by
  ring
```

**验收标准**：故意错误版本不能关闭目标，并给出与非线性项或 tactic 失败有关的信息；修复版本编译成功。

## 练习 0.4（综合）：根据目标选 tactic
%%%
tag := "exercise-0-4"
%%%

下面是含 `sorry` 的练习模板。`sorry` 允许模板通过编译；你要逐个替换它，最终文件中不得保留 `sorry`。

\[练习模板\]
```
import Mathlib

example : (3 : ℤ) + 4 = 7 := by
  sorry

example : (10 : ℕ) < 20 := by
  sorry

example (n : ℕ) : n + n = 2 * n := by
  sorry
```

可以从 `norm_num`、`omega`、`simp`、`ring`、`decide` 中选择，并记录哪些 tactic 成功、哪些失败。不要只记答案；对失败项写一句原因，例如“目标含变量的代数恒等式，`norm_num` 只做数值规范化”。

**验收标准**：三个 example 都编译成功；文件中没有 `sorry`；你能为每个所选 tactic 说明它利用了目标的哪一种结构。
