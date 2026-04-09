import VersoManual

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch01MetaprogrammingModel"

#doc (Manual) "第零章 环境与运行约定" =>
%%%
file := "Ch00Setup"
tag := "ch00-setup"
%%%

*本章目标*：搭好动手环境，让你能跑通本书所有示例。

*本书校验版本*：Lean 4 `v4.30.0-rc1`，Mathlib 同期主线（2026 年 4 月）。较新的 Lean/Mathlib 版本通常也适用，但个别 API 或 tactic 行为可能有变化——遇到编译错误时，先检查你的版本是否与本书一致。

查看当前版本：

```
cat lean-toolchain          # 项目使用的 Lean 版本
lake env lean --version     # 实际运行的 Lean 版本
```

# 你需要什么基础
%%%
tag := "prerequisites"
%%%

本书假设你：
- 会基本的数学（本科水平的代数、分析即可）
- 在 Lean 4 中写过简单的形式化证明（`by simp`、`by ring`、`by intro h; exact h` 这类）
- 了解 `theorem`、`example`、`by` 的基本语法

如果你还没写过任何 Lean 代码，建议先完成 Mathematics in Lean 的前几章。

# 安装 Lean 4
%%%
tag := "install-lean4"
%%%

如果你还没安装 Lean 4：

```
# 安装 elan（Lean 版本管理器）
curl https://elan.lean-lang.org/install.sh -sSf | sh

# 验证安装
lean --version
```

推荐使用 VS Code + Lean 4 插件作为编辑器——你可以实时看到目标状态和错误信息。

## 常见安装问题
%%%
tag := "install-troubleshooting"
%%%

*问题 1：`elan` 安装后 `lean` 命令找不到*

```
# elan 默认安装到 ~/.elan/bin，需要把它加到 PATH
export PATH="$HOME/.elan/bin:$PATH"
# 建议写入 ~/.bashrc 或 ~/.zshrc，然后重新打开终端
```

*问题 2：`lean --version` 报错 `no default toolchain configured`*

这说明 elan 装好了，但还没指定默认工具链。不用担心——创建项目时 {lit}`lean-toolchain` 文件会自动指定版本。

*问题 3：VS Code 插件安装后没反应*

检查：
- 是否打开的是*文件夹*（不是单个 `.lean` 文件）
- 文件夹根目录是否有 {lit}`lakefile.lean` 或 `lakefile.toml`
- 右下角状态栏是否显示 Lean 版本号（如果显示 "Loading..." 等一会儿）

*问题 4：VS Code 里能 {lit}`import Mathlib`，终端里不行*

大概率是你没有在项目根目录下运行，或者没用 {lit}`lake env lean`。确保：
- 终端 `cd` 到了有 {lit}`lakefile.lean` 的目录
- 用 {lit}`lake env lean YourFile.lean` 而不是裸 `lean YourFile.lean`

# 创建本书的配套项目
%%%
tag := "create-project"
%%%

*这一步非常重要*——本书大部分示例依赖 Mathlib 库。如果你直接新建一个 `.lean` 文件写 {lit}`import Mathlib`，会报错。

## 方式一：用 lake 创建 Mathlib 项目（推荐）
%%%
tag := "create-with-lake"
%%%

```
# 创建项目
lake new LeanAutoBook math
cd LeanAutoBook

# 获取 Mathlib 缓存（避免从源码编译，节省大量时间）
lake exe cache get
```

验证环境——写一个最小测试文件：

```
cat > Test.lean <<'EOF'
import Mathlib
#check Nat.add_comm
EOF
lake env lean Test.lean
```

如果看到 `Nat.add_comm : ∀ (n m : ℕ), n + m = m + n`（或类似输出），说明环境搭建成功。

成功后，你就有了一个能 {lit}`import Mathlib` 的项目。在 `LeanAutoBook/` 目录下新建 `.lean` 文件即可开始跟着本书做实验。

## 常见项目创建问题
%%%
tag := "project-troubleshooting"
%%%

*问题 1：{lit}`lake exe cache get` 失败，报网络错误*

```
# Mathlib 缓存托管在 GitHub Releases，如果网络不通可以设代理：
export https_proxy=http://your-proxy:port
lake exe cache get
```

如果完全无法下载缓存，可以从源码编译（但非常慢，30 分钟到几小时）：

```
lake build
```

*问题 2：{lit}`lake new LeanAutoBook math` 报错 `unknown template 'math'`*

你的 `lake` 版本可能太旧。运行 `elan update` 更新，或者手动创建项目后在 {lit}`lakefile.lean` 中添加 Mathlib 依赖：

```
-- lakefile.lean
require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
```

然后运行 {lit}`lake update && lake exe cache get`。

*问题 3：编译/类型检查极慢（每个文件几十秒）*

大概率是缓存没下好。检查：

```
# 如果输出大量 "Building ..." 说明缓存缺失
lake build --log-level=info 2>&1 | head -20

# 重新获取缓存
lake exe cache get
```

## 方式二：克隆本书配套仓库
%%%
tag := "clone-companion-repo"
%%%

```
git clone https://github.com/your-org/lean-auto-book-code.git
cd lean-auto-book-code
lake exe cache get
```

（配套仓库包含每章的示例文件和练习题，后续会提供。）

# 哪些 tactic 来自哪里
%%%
tag := "tactic-origins"
%%%

一个初学者常见的困惑：为什么有的 tactic 不需要 import 就能用，有的需要 {lit}`import Mathlib`？

- {moduleTerm}`simp`：Lean core，不需要 import（但 `@[simp]` 引理大部分来自 Mathlib）
- `ring`：Mathlib，{lit}`import Mathlib.Tactic.Ring`
- `omega`：Lean core（v4.8+），不需要 import
- `linarith`：Mathlib，{lit}`import Mathlib.Tactic.Linarith`
- `nlinarith`：Mathlib，{lit}`import Mathlib.Tactic.Linarith`
- `polyrith`：Mathlib，{lit}`import Mathlib.Tactic.Polyrith`
- `norm_num`：Mathlib，{lit}`import Mathlib.Tactic.NormNum`
- `aesop`：Lean core + Mathlib 规则，{lit}`import Aesop`（core）或 Mathlib
- `grind`：Lean core（v4.14+），不需要 import
- `decide`：Lean core，不需要 import
- `positivity`：Mathlib，{lit}`import Mathlib.Tactic.Positivity`
- `field_simp`：Mathlib，{lit}`import Mathlib.Tactic.FieldSimp`
- `gcongr`：Mathlib，{lit}`import Mathlib.Tactic.GCongr`
- `fun_prop`：Mathlib，{lit}`import Mathlib.Tactic.FunProp`

*简单规则*：如果 {lit}`import Mathlib` 能跑通，以上全部可用。本书示例默认在 Mathlib 项目环境中运行。

# 本书的代码约定
%%%
tag := "code-conventions"
%%%

本书中的代码分为三类，请注意区分：

## 可运行示例
%%%
tag := "runnable-examples"
%%%

标注为 *\[可运行\]* 或没有特殊标注的代码块。你可以直接复制到 `.lean` 文件中运行。

```
-- [可运行] 复制到你的 .lean 文件试试
example (x : ℝ) : x + 0 = x := by simp
```

## 示意代码
%%%
tag := "illustrative-code"
%%%

标注为 *\[示意\]*。展示内部机制或模式，可能省略了 import、辅助定义等。不保证直接编译。

```
-- [示意] 展示 tactic 内部的模式，省略了部分细节
elab "my_tactic" : tactic => do
  let goal ← getMainGoal
  -- ... 略去具体实现 ...
```

## 伪代码
%%%
tag := "pseudocode"
%%%

标注为 *\[伪代码\]*。只用于解释算法流程，不是 Lean 代码。

```
-- [伪代码] omega 算法的高层流程
1. 收集线性不等式假设
2. 规范化为标准形
3. 变量消去（Fourier-Motzkin + 整数修正）
4. 检查矛盾
```

# 跟着本书学的建议
%%%
tag := "learning-tips"
%%%

1. *先跑再看*：每章的示例，先复制到 VS Code 里跑一遍，看目标状态的变化
2. *改着玩*：把例子里的数字、函数、条件改一改，看 tactic 还能不能工作
3. *故意破坏*：把 {moduleTerm}`simp` 换成 `ring`，看报错信息——理解"为什么不行"和"为什么行"一样重要
4. *做练习*：每章末尾的练习是学习闭环的关键，不要跳过
5. *查源码*：想深入理解某个 tactic 时，用 VS Code 的 "Go to Definition" 跳到源码

# 全书结构概览
%%%
tag := "book-overview"
%%%

```
Part I:  基础（Ch1-5）     — 元编程模型、Expr、写 tactic、目标管理、typeclass
Part II: 核心自动化（Ch6-13）— simp, ring, omega, linarith, norm_num, aesop, grind, decide
Part III:领域自动化（Ch14-19）— positivity, fun_prop, gcongr, field_simp, 逻辑变换, 设计自己的
Part IV: 高级专题（Ch20-24） — 反射, 性能, 外部工具, 方法论, 分析自动化展望
```

*Part I-II 是核心*，建议按顺序读。Part III-IV 可以按需跳读。

# 环境验证练习
%%%
tag := "setup-exercises"
%%%

在进入下一章之前，完成以下练习确认你的环境搭建成功。

## 练习 0.1（热身）：Hello, Lean!
%%%
tag := "exercise-0-1"
%%%

在你的项目中新建 {lit}`Hello.lean`，写入以下内容：

```
-- [可运行]
import Mathlib

#check Nat.add_comm
#eval 2 + 3
```

在 VS Code 中打开这个文件。你应该能看到：
- `#check` 输出 `Nat.add_comm : ∀ (n m : ℕ), n + m = m + n`（或类似）
- `#eval` 输出 `5`

如果看不到输出，检查 VS Code 右侧的 "Lean Infoview" 面板是否打开（快捷键 `Ctrl+Shift+P` → "Lean 4: Infoview: Toggle"）。

## 练习 0.2（热身）：第一个证明
%%%
tag := "exercise-0-2"
%%%

```
-- [可运行]
import Mathlib

example : 2 + 3 = 5 := by norm_num

example (n : ℕ) : n + 0 = n := by simp
```

复制到 `.lean` 文件，确认没有红色波浪线。如果有——恭喜，你遇到了第一个 debug 机会！把光标移到红线上，看 Lean Infoview 里的错误信息。

## 练习 0.3（debug 练习）：故意出错
%%%
tag := "exercise-0-3"
%%%

以下代码有一个故意的错误，找出来并修复：

```
-- [可运行] 这段代码有错，你能找到吗？
import Mathlib

example (x : ℝ) : x * 1 = x := by
  ring_nf
```

提示：`ring_nf` 会化简但不一定能关闭目标。想想该用什么 tactic 替代？（答案：`ring` 可以直接关闭等式目标。试试把 `ring_nf` 换成 `ring`。）

## 练习 0.4（综合）：选对 tactic
%%%
tag := "exercise-0-4"
%%%

尝试分别用不同的 tactic 证明以下命题。哪个能用，哪个不能？

```
-- [可运行]
import Mathlib

-- 试试分别用 simp、ring、omega、decide 证明以下命题
-- 哪些能成功？哪些会失败？失败时报什么错？

example : (3 : ℤ) + 4 = 7 := by sorry  -- 替换 sorry

example : (10 : ℕ) < 20 := by sorry  -- 替换 sorry

example (n : ℕ) : n + n = 2 * n := by sorry  -- 替换 sorry
```

这个练习没有唯一正确答案——关键是体验不同 tactic 的适用范围。到本书结束时，你会对每个 tactic 的能力边界了如指掌。

准备好了？翻到下一章，我们从 Lean 4 的元编程模型开始。
