import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch23Methodology"

#doc (Manual) "第二十三章 从证明模式到自动化：方法论" =>
%%%
file := "Ch23Methodology"
tag := "ch23-methodology"
%%%

*本章目标*：掌握从"手动证明中发现模式"到"实现自动化"的系统方法，
理解自动化层级选择（macro / `simp` 扩展 / `elab`）的决策依据，
学会用迭代—测试—回归的流程逐步改进 tactic，
并建立"何时值得自动化"的判断标准。

前二十二章介绍了 Lean 4 自动化的完整技术栈——
从 `simp` 到 `MetaM`，从反射到外部工具。
但技术能力不等于方法论：面对一组手动证明，
*如何系统地判断能不能自动化、用哪种方案、做到什么程度？*
本章给出可操作的框架。

*关于本章代码*：标注 `[示意]` 的代码块仅用于展示设计思路和提炼模式，
*不能直接复制编译*——它们省略了 `import`、`open`、辅助定义等依赖，
部分还使用了 `...` 省略号。请关注代码*传达的策略*，而非逐行语法。

# 23.1 自动化的发现流程
%%%
tag := "discovery-process"
%%%

自动化的起点不是"我要写一个 tactic"，而是*重复劳动让你感到厌烦*。
系统的发现流程如下：

```
❶ 积累素材：写 10–20 个同类证明
❷ 提取模式：哪些 tactic 反复出现？顺序固定吗？
❸ 分类步骤：机械步骤 vs 需要创造性的步骤
❹ 确定边界：哪些输入会让模式失效？
❺ 选择层级：macro / simp 扩展 / elab（见 §23.4）
❻ 实现—测试—迭代
```

*❶ 是前提条件*——没有足够的素材就急于自动化，
容易过度设计（为不存在的模式建框架）或欠缺设计（漏掉关键变体）。

## 示例：模式发现记录
%%%
tag := "pattern-discovery-example"
%%%

假设你在 Mathlib 中反复写关于 `Finset.sum` 上界的证明：

```
-- [示意] 素材 1：常数上界
example (f : ℕ → ℝ) (s : Finset ℕ) (hf : ∀ i ∈ s, f i ≤ 1) :
    ∑ i ∈ s, f i ≤ s.card := by
  calc ∑ i ∈ s, f i
      ≤ ∑ i ∈ s, (1 : ℝ) := Finset.sum_le_sum hf   -- ❶ 逐项估计
    _ = s.card := by simp                             -- ❷ 化简

-- [示意] 素材 2：函数上界
example (f g : ℕ → ℝ) (s : Finset ℕ) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i := by
  exact Finset.sum_le_sum hfg                         -- 只有 ❶

-- [示意] 素材 3：带绝对值
example (f : ℕ → ℝ) (s : Finset ℕ) (hf : ∀ i ∈ s, |f i| ≤ 2) :
    |∑ i ∈ s, f i| ≤ 2 * s.card := by
  calc |∑ i ∈ s, f i|
      ≤ ∑ i ∈ s, |f i| := norm_sum_le_of_le ...      -- ❶' 三角不等式
    _ ≤ ∑ i ∈ s, (2 : ℝ) := Finset.sum_le_sum hf     -- ❷ 逐项估计
    _ = 2 * s.card := by ring                          -- ❸ 化简
```

从三个素材中提取模式：

| 步骤 | 出现频率 | 机械性 |
|------|---------|--------|
| `Finset.sum_le_sum` + 逐项假设 | 3/3 | 高——只要假设在上下文中就能匹配 |
| `simp` / `ring` / `norm_cast` 收尾 | 3/3 | 高 |
| 三角不等式 `norm_sum_le` | 1/3 | 中——需要识别绝对值/范数 |

结论：*核心模式是 `Finset.sum_le_sum` + 收尾化简*，可自动化。
三角不等式是变体，可作为第二阶段扩展。

# 23.2 从模式到实现：Finset.sum 估计
%%%
tag := "pattern-to-implementation"
%%%

## 第一版：macro
%%%
tag := "first-version-macro"
%%%

最简单的自动化——把重复的 tactic 序列封装为 macro：

```
-- [示意] ❶ 第一版：纯 tactic 组合
macro "bound_sum" : tactic =>
  `(tactic| (
    first
    | (apply Finset.sum_le_sum; intro i hi;
       first | assumption | linarith | positivity)
    | (calc_step using norm_sum_le_of_le)  -- 三角不等式变体
  ))
```

*优点*：实现成本极低（5 行）。
*缺点*：不灵活——`first` 的分支顺序硬编码，
遇到新变体就要改 macro 源码。

*注意*：macro 中的 tactic 组合对括号、分号敏感。
如果编译报错，优先检查语法层面——
`first | a | b` 和 `first | (a; b) | c` 含义不同。

## 第二版：引理集扩展
%%%
tag := "second-version-lemma-set"
%%%

如果变体可以用引理集统一归类，定义自定义 tag
让用户用 `@[bound_sum_lemmas]` 注册新引理，macro 不用改。
但注意 `simp` 是等式重写器——`Finset.sum_le_sum` 是不等式，
需要 `gcongr` 或 `aesop` 风格的策略，不能直接用 `simp only`。

## 第三版：elab（进阶）
%%%
tag := "third-version-elab"
%%%

本小节涉及 `MetaM` 编程，初学者可跳过，先掌握 macro 和引理集扩展。

当 macro 和 simp 扩展都不够用时，进入 `MetaM`：

```
-- [示意] ❸ MetaM 端实现
elab "bound_sum" : tactic => do
  let goal ← getMainTarget
  -- ❶ 检查目标形状：∑ i ∈ s, f i ≤ bound
  let some (lhs, rhs) ← matchLe? goal | throwError "not ≤ goal"
  let some (s, f) ← matchFinsetSum? lhs | throwError "not Finset.sum"
  -- ❷ 在上下文中搜索逐项估计
  let hyps ← getLocalHyps
  for h in hyps do
    if ← isPointwiseBound h s f rhs then
      -- ❸ 应用 Finset.sum_le_sum
      let proof ← mkAppM ``Finset.sum_le_sum #[h]
      closeMainGoal proof
      return
  -- ❹ fallback：尝试 simp + linarith
  evalTactic (← `(tactic| (simp; linarith)))
```

*优点*：精确控制逻辑——可以搜索假设、处理变体。
*缺点*：实现成本高（20+ 行 MetaM），需要调试 `Expr` 匹配。

# 23.3 案例：单调性引理链
%%%
tag := "monotone-chain-case"
%%%

第二个案例展示更复杂的模式——需要*链式推理*。

## 素材
%%%
tag := "monotone-examples"
%%%

```
-- [示意] 反复出现的单调性证明
example (hf : Monotone f) (hg : Monotone g) :
    Monotone (f ∘ g) := hf.comp hg

example (hf : Monotone f) (hg : Monotone g) (hh : Monotone h) :
    Monotone (f ∘ g ∘ h) := hf.comp (hg.comp hh)

-- 变体：加上 StrictMono
example (hf : StrictMono f) (hg : Monotone g) :
    Monotone (f ∘ g) := hf.monotone.comp hg
```

## 实现选择
%%%
tag := "monotone-implementation-choice"
%%%

模式：递归拆解 `∘`，对每个分量查找 `Monotone`/`StrictMono` 假设，
用 `.comp` 链接，必要时用 `.monotone` 做类型转换。
这适合 `aesop`——注册规则即可：

```
-- [示意] 用 aesop 规则集处理单调性链
attribute [aesop safe apply] Monotone.comp
attribute [aesop safe apply] StrictMono.monotone

-- 使用
example (hf : Monotone f) (hg : Monotone g) (hh : Monotone h) :
    Monotone (f ∘ g ∘ h) := by aesop
```

*和 `fun_prop`（第十五章）的关系*：`fun_prop` 正是以这种方式
处理函数性质的链式推理。如果目标属于 `fun_prop` 支持的性质类，
直接使用 `fun_prop` 即可——不需要自己实现。

*设计原则*：在自己实现之前，检查现有 tactic 是否已经覆盖你的模式。
重复造轮子的维护成本远高于学习现有工具。

# 23.4 自动化层级选择
%%%
tag := "automation-level-selection"
%%%

选择错误的层级是最常见的方法论失误——
用 `elab` 做 macro 能解决的事，或者用 macro 去做需要 `MetaM` 的事。

| 层级 | 适用场景 | 实现成本 | 灵活性 |
|------|---------|---------|--------|
| *macro* | tactic 序列的固定组合 | 极低（1-10 行） | 低 |
| *simp/aesop 扩展* | 可用引理集覆盖的模式 | 低（注册引理） | 中 |
| *elab + MetaM* | 需要检查目标结构或搜索假设 | 中（20-100 行） | 高 |
| *反射*（进阶） | 可判定问题，需要高性能 | 高（200+ 行） | 域特定 |
| *外部工具*（进阶） | 超出 Lean 计算能力 | 高 | 域特定 |

## 决策流程
%%%
tag := "decision-flow"
%%%

```
目标是固定的 tactic 序列？
  ├─ 是 → macro
  └─ 否 → 模式可以用引理集覆盖？
           ├─ 是 → simp/aesop 扩展
           └─ 否 → 需要检查 Expr 结构？
                    ├─ 是 → elab + MetaM
                    └─ 否 → 问题可判定且需要高性能？
                             ├─ 是 → 反射（第二十章）
                             └─ 否 → 外部工具（第二十二章）
```

*常见错误*：跳过 macro 直接写 `elab`。
实际上，Mathlib 中大量实用 tactic 是 macro——
`positivity`、`gcongr` 的许多入口点都是 macro 层面的组合。

# 23.5 迭代改进
%%%
tag := "iterative-improvement"
%%%

第一版自动化通常只覆盖 60–70% 的目标案例。
以下是系统化的迭代方法。

## 阶段 1：收集失败案例
%%%
tag := "collect-failures"
%%%

```
-- [示意] 用 try/catch 记录失败
elab "bound_sum_debug" : tactic => do
  try
    evalTactic (← `(tactic| bound_sum))
  catch e =>
    logWarning m!"bound_sum failed on: {← getMainTarget}"
    evalTactic (← `(tactic| sorry))  -- fallback 以继续编译
```

在开发阶段用 debug 版本替换正式 tactic，
编译整个项目后统计失败分布——比逐个手动测试高效得多。

## 阶段 2：分析失败原因
%%%
tag := "analyze-failures"
%%%

失败通常归入四类：

| 类别 | 示例 | 解决方案 |
|------|------|---------|
| *引理缺失* | 缺少 `norm_sum_le_of_le` 的变体 | 注册新引理 |
| *模式不匹配* | 目标用 `∑ i ∈ s, ...` 但 tactic 只识别 `Finset.sum s f` | 扩展模式匹配 |
| *前提不满足* | 逐项估计在上下文中但格式不同 | 添加预处理（`simp` 规范化） |
| *超出范围* | 目标涉及条件求和 `∑ i ∈ s.filter p, ...` | 标记为不支持，给出清晰错误 |

## 阶段 3：扩展 + 回归测试
%%%
tag := "extend-and-regress"
%%%

每次修改 tactic 后运行全部测试——
包括*应通过*的案例（基本 + 新变体 + 边界）和*应失败*的案例
（确保不 over-match）。
*回归测试是自动化维护的核心*——没有测试的 tactic 会在引理库更新后悄然失效。

测试应分三层：*单元测试*（每个辅助函数如 `matchFinsetSum?`）、
*集成测试*（10-20 个应通过 + 5-10 个应失败的完整 tactic 测试）、
*性能基准*（`set_option maxHeartbeats 2000 in example ...`，
超时则需优化，见第二十一章）。

# 23.6 何时停止
%%%
tag := "when-to-stop"
%%%

自动化的边际收益递减。三个停止信号：

## 信号 1：覆盖率回报递减
%%%
tag := "diminishing-returns"
%%%

```
版本 1：覆盖 60% 的案例（投入 2 小时）
版本 2：覆盖 80%（再投入 3 小时）
版本 3：覆盖 85%（再投入 5 小时）
         ↑ 该停了
```

*80/20 规则*：自动化覆盖 80% 的常见情况就足够了。
剩下 20% 要么太罕见不值得，要么需要创造性步骤无法机械化。

## 信号 2：维护成本超过收益
%%%
tag := "maintenance-cost"
%%%

经验法则：*tactic 实现的代码量不应超过它替代的手动证明总量的 1/3*。
如果实现比手动证明更难理解和维护，自动化适得其反。

## 信号 3：可读性下降
%%%
tag := "readability-decline"
%%%

```
-- ✗ 过度自动化：证明不可读
example : ... := by mega_solver  -- 做了什么？why does it work？

-- ✓ 适度自动化：关键步骤可见
example : ... := by
  apply Finset.sum_le_sum  -- 逐项估计（人能看懂意图）
  intro i hi
  bound_elem               -- 自动化辅助（每项的估计）
```

证明不只是给编译器看的——你的合作者（包括未来的自己）也要读。

# 23.7 方法论检查清单
%%%
tag := "methodology-checklist"
%%%

动手实现之前，回答以下问题：

| 检查项 | 问题 |
|--------|------|
| *素材充分* | 有 10+ 个同类证明吗？是否覆盖了主要变体？ |
| *现有工具* | `simp`/`aesop`/`omega`/`fun_prop` 已经能做吗？ |
| *模式稳定* | 模式会随引理库更新而改变吗？ |
| *层级选择* | macro 够用还是必须 elab？（见 §23.4 决策流程） |
| *边界清晰* | 什么输入会失败？失败信息是否清晰？ |
| *测试计划* | 有 10+ 应通过案例和 5+ 应失败案例吗？ |
| *维护预算* | 谁来维护？引理库更新后谁来修？ |

# 23.8 失败模式
%%%
tag := "failure-modes"
%%%

## 失败 1：过早自动化
%%%
tag := "premature-automation"
%%%

```
-- ✗ 只写了 3 个证明就开始自动化 → 覆盖 3 个案例但漏掉 15 个变体
-- ✓ 先积累 10-20 个素材，提取稳定的模式后再动手
```

*过早自动化是最大的时间浪费*——不如等模式清晰后一次做对。

## 失败 2：层级选择错误
%%%
tag := "wrong-level-selection"
%%%

```
-- ✗ 用 elab + MetaM 实现了一个本质上是 tactic 序列的组合
elab "my_tactic" : tactic => do
  evalTactic (← `(tactic| simp))
  evalTactic (← `(tactic| ring))
-- ✓ 直接用 macro
macro "my_tactic" : tactic => `(tactic| (simp; ring))
```

反过来也是错误——用 macro 实现需要检查 `Expr` 结构的 tactic，
导致大量 `first | ... | ...` 分支和脆弱的匹配。

## 失败 3：没有回归测试
%%%
tag := "no-regression-tests"
%%%

```
-- ✗ Mathlib 更新了 Finset.sum_le_sum 的类型签名
-- tactic 默默失效，直到用户发现才知道
-- ✓ CI 中跑测试套件，引理库更新后立即发现
```

## 失败 4：错误信息不清晰
%%%
tag := "unclear-error-messages"
%%%

```
-- ✗ "tactic 'bound_sum' failed, there are unsolved goals" ——不知道原因
-- ✓ "bound_sum: goal is not of the form ∑ i ∈ s, f i ≤ bound"
-- ✓ "bound_sum: found Finset.sum but no pointwise bound in context"
```

用 `throwError` 提供针对性的失败信息——这是 macro（无法做到）
和 elab（可以做到）的重要区别。

## 失败 5：over-match
%%%
tag := "over-match"
%%%

```
-- ✗ tactic 太激进，在不应该成功的目标上"成功"了
-- 例如：把 ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i 证明为 trivial
-- 但实际上需要 f ≤ g 的假设（上下文中恰好有一个无关的不等式被误用）
-- ✓ 精确匹配：检查假设确实是关于 f 和 s 的逐项估计
```

*over-match 比 under-match 更危险*——Lean 的类型检查保证逻辑正确性，
但证明的*结构*可能不符合用户意图（依赖了不该依赖的假设）。

# 23.9 练习
%%%
tag := "ch23-exercises"
%%%

## 练习 1（设计）：模式提取
%%%
tag := "exercise-pattern-extraction"
%%%

以下三个证明有共同模式。提取模式，并判断应该用 macro 还是 elab 实现：

```
-- [示意]
-- (a)
example (h : ∀ n, a n ≤ b n) (hb : Summable b) : Summable a := by
  exact Summable.of_nonneg_of_le (fun n => le_trans ... (h n)) h hb

-- (b)
example (h : ∀ n, |a n| ≤ b n) (hb : Summable b) : Summable a := by
  exact Summable.of_norm_bounded b hb h

-- (c)
example (h : ∀ n, a n ≤ c * b n) (hb : Summable b) (hc : 0 ≤ c) :
    Summable a := by
  exact Summable.of_nonneg_of_le ... (Summable.of_const_mul hb)
```

*提示*：共同模式是"比较判据 + 在上下文中查找可和性假设"。
判断 macro vs elab 的关键：是否需要检查假设的形状（`≤` vs `|·| ≤` vs `≤ c * ·`）。

## 练习 2（设计）：层级选择
%%%
tag := "exercise-level-selection"
%%%

对以下场景，选择 macro / simp 扩展 / elab / 反射 / 外部工具，说明理由：

```
(a) 目标总是 `a ∣ b` 形式，证明策略总是 norm_num + decide 的组合。
(b) 目标是 `Continuous (fun x => f (g x))`，需要链式查找连续性引理。
(c) 目标是有限域上的多项式等式，变量 ≤ 5 个。
(d) 证明有限图的着色数 ≤ k，需要展示具体着色方案。
```

*提示*：(a) macro；(b) fun_prop 已覆盖，不需要自己写；
(c) 反射（encode 多项式、范式化、decide）；
(d) 外部工具（SAT 编码 + 证书验证）或 native_decide。

## 练习 3（进阶）：迭代设计
%%%
tag := "exercise-iterative-design"
%%%

假设你实现了以下 `mono_chain` tactic 的第一版，
它只处理 `Monotone (f ∘ g)` 的形式：

```
-- [示意] 第一版
macro "mono_chain" : tactic =>
  `(tactic| (apply Monotone.comp <;> assumption))
```

列出三个它会失败的变体，并为每个变体设计修复方案
（是扩展 macro、改为 elab、还是注册 aesop 规则？）：

```
(a) Monotone (f ∘ g ∘ h)       ——三层组合
(b) StrictMono (f ∘ g)         ——StrictMono 而非 Monotone
(c) Monotone (fun x => f x + g x) ——不是组合而是逐点运算
```

*提示*：(a) macro 可用 `repeat` 扩展；
(b) 需要 `StrictMono.comp` 和类型转换，macro 仍可行；
(c) 超出组合模式——需要 `Monotone.add` 等引理，
转为 aesop 规则集是更好的选择。

# 23.10 小结
%%%
tag := "ch23-summary"
%%%

| 概念 | 要点 |
|------|------|
| 发现流程 | 10+ 素材 → 提取模式 → 分类步骤 → 确定边界 |
| 层级选择 | macro（序列组合）→ simp/aesop（引理集）→ elab（结构检查）→ 反射/外部 |
| 常见错误 | 过早自动化、层级过高、缺少回归测试 |
| 迭代方法 | 收集失败 → 分类原因 → 扩展 + 回归测试 |
| 停止准则 | 80/20 覆盖率、维护成本、可读性 |
| 测试策略 | 应通过 + 应失败 + 性能基准，三层覆盖 |
| 检查在前 | 实现之前先查 simp/aesop/`fun_prop` 是否已覆盖 |
| 主要陷阱 | 过早自动化、层级错误、over-match、错误信息不清晰 |

*一句话总结*：好的自动化方法论是"先观察，再选择，小步迭代，及时停止"——
技术能力只决定你*能*做什么，方法论决定你*该*做什么。

## 现在就能做的三件事
%%%
tag := "three-things-to-do-now"
%%%

如果你读完本章想立刻动手，建议按以下顺序起步：

1. *从 `simp only [...]` 开始*——把手动证明中反复出现的 `simp` 引理
   整理到一个引理集（`@[simp]` 或自定义 `simp` set），
   这是零成本的自动化，见效最快。
2. *写一个小 macro*——把 3 行以上的固定 tactic 序列封装成一行调用，
   不需要任何 `MetaM` 知识，5 分钟内可完成。
3. *给现有 tactic 添加测试*——为你已经在用的 `simp` / `aesop` 调用
   补上 5 个 `example`，既是文档也是回归保护。

*不要*一上来就写完整的搜索 tactic 或 `elab`——
那是在前三步都做熟之后才需要考虑的事。

下一章展望数学分析领域的自动化前沿——
当前最具挑战性的形式化领域，也是自动化最有潜力产生影响的方向。
