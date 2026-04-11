import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch24TowardsAnalysis"

#doc (Manual) "迈向分析自动化" =>
%%%
file := "Ch24TowardsAnalysis"
tag := "ch24-towards-analysis"
%%%

*本章目标*：理解数学分析领域自动化的现状与瓶颈，
掌握现有工具（`fun_prop`、`positivity`、`gcongr`、`norm_num`）的组合使用，
并了解 ε-δ 管理、估计链、紧致性论证等前沿方向的设计思路。

*阅读定位*：本章是架构视野章，重在设计思路而非全部动手实现。
核心收获是理解"为什么分析难自动化"以及"如何用现有工具走得更远"。

数学分析是形式化数学中自动化程度最低的领域之一。
前二十三章的 tactic 能高效处理代数等式、线性不等式、可判定问题——
但遇到 ε-δ 论证、估计链、紧致性论证时，自动化支持骤降。
本章分析差距的根源，展示现有工具的组合策略，并展望突破方向。

# 24.1 分析自动化的现状
%%%
tag := "analysis-automation-status"
%%%

## 现有工具清单
%%%
tag := "existing-tools-list"
%%%

- 工具：`fun_prop` —— 能力：函数性质的链式推理 —— 典型用途：`Continuous (f ∘ g)` —— 章节：第十五章
- 工具：`positivity` —— 能力：表达式非负/正 —— 典型用途：`0 < ε` —— 章节：第十四章
- 工具：`gcongr` —— 能力：不等式的同余推理 —— 典型用途：保序运算下传递不等式 —— 章节：第十六章
- 工具：`norm_num` —— 能力：具体数值计算 —— 典型用途：`(3 : ℝ) / 2 > 1` —— 章节：第十章
- 工具：`linarith` / `nlinarith` —— 能力：线性/非线性算术 —— 典型用途：从假设推导不等式 —— 章节：第九章
- 工具：`field_simp` —— 能力：消去分母 —— 典型用途：`ε / 2 + ε / 2 = ε` —— 章节：第十七章

## 覆盖率估计
%%%
tag := "coverage-estimate"
%%%

以 Mathlib 的 `Analysis.SpecificLimits` 典型证明为参考：

```
步骤类型              占比      自动化程度
─────────────────────────────────────────
代数化简（ring/simp）   ~25%     高 ✓
不等式传递（linarith）  ~20%     高 ✓
函数性质（fun_prop）    ~15%     高 ✓
非负性（positivity）    ~10%     高 ✓
ε/δ 选取               ~15%     低 ✗
估计链构造              ~10%     低 ✗
结构论证（紧致性等）     ~5%     低 ✗
```

问题集中在最后三项——恰好是最需要"数学直觉"的部分。

# 24.2 现有工具的组合
%%%
tag := "tool-combinations"
%%%

没有通用分析 tactic，但组合现有工具已能覆盖相当多场景。

## 组合 1：`gcongr` + `linarith`
%%%
tag := "combo-gcongr-linarith"
%%%

```
-- [示意] 逐步估计
example (hf : ∀ x ∈ s, ‖f x‖ ≤ M) (hM : M ≤ K) (hx : x ∈ s) :
    ‖f x‖ ≤ K := by
  calc ‖f x‖ ≤ M := hf x hx
    _ ≤ K := hM
```

`calc` 提供结构，`gcongr` 处理保序运算，`linarith` 关闭算术目标。

## 组合 2：`positivity` + `ring`——ε 算术
%%%
tag := "combo-positivity-ring"
%%%

```
-- [示意] ε 算术的典型模式
example (hε : 0 < ε) : ε / 2 + ε / 2 = ε := by ring
example (hε : 0 < ε) : 0 < ε / 2 := by positivity
example (hε : 0 < ε) (hδ : δ = ε / 3) : 3 * δ ≤ ε := by
  subst hδ; ring_nf; linarith
```

## 组合 3：`fun_prop` + `filter_upwards`——函数性质与 filter
%%%
tag := "combo-funprop-filter"
%%%

```
-- [示意] filter_upwards 简化 ∀ᶠ 目标
example (h₁ : ∀ᶠ x in l, P x) (h₂ : ∀ᶠ x in l, Q x) :
    ∀ᶠ x in l, P x ∧ Q x := by
  filter_upwards [h₁, h₂] with x hp hq   -- 自动合并 filter 条件
  exact ⟨hp, hq⟩
```

*注意*：`filter_upwards` 是分析证明中的关键 tactic——
它自动化了 `∀ᶠ` 的交、单调性等规则，大幅减少 filter 推理的手动步骤。

## 组合的局限
%%%
tag := "combination-limitations"
%%%

这些组合覆盖了*每个步骤内部*的自动化，
但无法自动化*步骤之间的连接*——
选择什么中间量、按什么顺序估计、ε 如何分配。

# 24.3 瓶颈分析
%%%
tag := "bottleneck-analysis"
%%%

## 瓶颈 1：ε 的选取
%%%
tag := "bottleneck-epsilon"
%%%

分析证明的核心挑战：给定目标 `... < ε`，需要*逆向*推导出 δ 的值。

```
-- [示意] Lean 中的 ε-δ 证明
example (hε : 0 < ε) (hf : Continuous f) :
    ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε := by
  -- ❶ 从 Continuous 的 ε-δ 定义中提取 δ
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuous_iff.mp hf a (ε / 2) (by positivity)
  -- ❷ 手动指定 δ
  exact ⟨δ, hδ_pos, fun x hx => by
    calc |f x - f a| < ε / 2 := hδ x hx
      _ < ε := by linarith⟩
```

*为什么难自动化*：搜索空间巨大（δ 可以是 `ε/2`、`min(ε,1)`、`ε²` 等），
需要逆向推理（从目标倒推余量），且依赖领域知识（选 δ 需预判后续步骤）。
最可行的方向是从假设中*提取* δ，而非猜测。

## 瓶颈 2：估计链
%%%
tag := "bottleneck-estimation-chain"
%%%

```
-- [示意] 三角不等式 + 逐段估计
example (h1 : ‖f x - f y‖ ≤ ε / 2) (h2 : ‖f y - L‖ ≤ ε / 2) :
    ‖f x - L‖ ≤ ε := by
  calc ‖f x - L‖
      = ‖(f x - f y) + (f y - L)‖ := by ring_nf   -- ❶ 重写
    _ ≤ ‖f x - f y‖ + ‖f y - L‖ := norm_add_le .. -- ❷ 三角不等式
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2          -- ❸ 逐段估计
    _ = ε := by ring                                 -- ❹ 化简
```

- `选择中间点`：搜索空间无限——哪个中间量能让两段都可估计？
- `三角不等式变体`：`norm_add_le`、`dist_triangle` 等变体众多
- `ε 预算分配`：等分是最简单情况，不等分需要更复杂的约束求解

## 瓶颈 3：紧致性与存在性论证
%%%
tag := "bottleneck-compactness"
%%%

```
-- [示意] 紧致性论证的典型步骤
-- ❶ 序列 (xₙ) 在紧集 K 中
-- ❷ 由紧致性，存在子列 xₙₖ 和极限 x ∈ K
-- ❸ 证明极限 x 满足所需性质
-- Lean 中需要 IsCompact.isSeqCompact + Filter.Tendsto 子列版本
-- 每步都需要手动选择引理和实例化
```

不是单一 tactic 能解决的——需要*多步结构推理*
（选子列 → 取极限 → 传递性质），中间量需要从存在性引理中提取。

# 24.4 设计方向 1：ε 管理器
%%%
tag := "design-epsilon-manager"
%%%

用第二十三章的方法论分析 ε 选取问题。

## 素材与模式提取
%%%
tag := "epsilon-patterns"
%%%

```
-- [示意] ε 选取的三种常见模式

-- 模式 A：直接从假设提取
obtain ⟨δ, hδ_pos, hδ⟩ := hf ε hε

-- 模式 B：等分
use ε / 2; constructor; · positivity

-- 模式 C：取最小值
use min δ₁ δ₂; constructor; · exact lt_min hδ₁ hδ₂
```

- 模式：从假设提取 —— 频率：高 —— 机械性：高 —— 自动化难度：低——直接 `obtain`
- 模式：等分 `ε/n` —— 频率：高 —— 机械性：高 —— 自动化难度：低——枚举 n
- 模式：`min`/`max` 组合 —— 频率：中 —— 机械性：高 —— 自动化难度：中——需要分析子目标数量
- 模式：非线性选取（`ε²`、`√ε`） —— 频率：低 —— 机械性：低 —— 自动化难度：高——需要领域知识

## 设计草案
%%%
tag := "epsilon-design-draft"
%%%

```
-- [伪代码] epsilon_manager 的核心逻辑
procedure epsilon_manager(goal):
  ❶ 识别目标中的 ∃ δ > 0, ... 结构
  ❷ 收集上下文中所有 ∃ δ > 0, ... 形式的假设
  ❸ 假设中有匹配的 δ → 直接 obtain + use
  ❹ 目标需要多个 bound → use ε / n + positivity
  ❺ 需要 min → use min δ₁ δ₂ + min 引理
  ❻ fallback：留给用户手动指定
```

*设计原则*：不试图猜测所有 δ，而是自动化*最机械的部分*，
把真正需要创造性的选取留给用户。这符合 §23.6 的 80/20 原则。

# 24.5 设计方向 2：估计链搜索
%%%
tag := "design-estimation-search"
%%%

## 问题建模
%%%
tag := "estimation-problem-modeling"
%%%

估计链问题可以建模为*图搜索*：

```
-- [伪代码] 估计链图
节点：表达式（f x、f y、L、...）
边：假设中的不等式（‖a - b‖ ≤ c 对应 a → b，权重 c）
目标：从起点到终点找路径，使总权重 ≤ ε
算法：
  ❶ 建图：从假设中提取 ‖a - b‖ ≤ c 形式的不等式
  ❷ BFS 搜索路径
  ❸ 检查总 bound（linarith 判定）
  ❹ 生成 calc 证明
```

- `建图`：可行——模式匹配 `‖a - b‖ ≤ c` 是标准 `Expr` 操作
- `搜索`：可行——假设数量有限，图很小
- `ε 预算`：困难——需要符号化的不等式求和
- `calc 生成`：可行但复杂——需要构造正确的 proof term

## 最小可行版本
%%%
tag := "estimation-mvp"
%%%

不实现完整图搜索，而是处理最常见的*两段估计*：

```
-- [示意] 两段估计的自动化
-- 目标：‖a - c‖ ≤ bound
-- 搜索：上下文中有 ‖a - b‖ ≤ e₁ 和 ‖b - c‖ ≤ e₂ 使 e₁ + e₂ ≤ bound
elab "estimate₂" : tactic => do
  -- ❶ 匹配目标 ‖lhs - rhs‖ ≤ bound
  -- ❷ 枚举假设中的 ‖· - ·‖ ≤ · 形式
  -- ❸ 寻找公共中间量
  -- ❹ 应用 norm_sub_le + linarith
  sorry
```

两段估计覆盖约 60% 的三角不等式使用场景。
三段及以上可通过嵌套调用处理。

# 24.6 设计方向 3：证明模板
%%%
tag := "design-proof-templates"
%%%

另一个方向不是写通用 tactic，而是提供*半自动化模板*——
用户提供策略选择，tactic 填充机械步骤。

```
-- [示意] 连续性证明模板——用户只需填写 ★ 部分
macro "prove_continuous_at" δ:term : tactic =>
  `(tactic| (
    intro ε hε
    use $δ                              -- ★ 用户提供 δ
    constructor
    · positivity                         -- 自动证明 δ > 0
    · intro x hx; sorry                  -- ★ 用户证明估计
  ))

-- [示意] 夹逼定理模板
macro "squeeze" lower:term upper:term : tactic =>
  `(tactic| (
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le $`lower `upper
    <;> first | assumption | intro n; linarith | fun_prop
  ))
```

*注意*：模板不是全自动——它把"想出证明策略"的负担留给用户，
自动化"实现策略"中的机械步骤。
在分析领域，这种半自动化可能比全自动化更实用。

# 24.7 LLM + ITP 混合方法
%%%
tag := "llm-itp-hybrid"
%%%

近年来最有前景的方向：让 LLM 生成证明策略骨架，Lean 验证和填补细节。

```
-- [伪代码] LLM + Lean 混合工作流
❶ 用户提供目标（Lean 类型签名）
❷ LLM 生成策略骨架："取 δ = ε/2，用三角不等式拆为两段"
❸ 骨架翻译为 Lean tactic 序列（带 sorry）
❹ Lean 验证每一步，对 sorry 调用自动化 tactic
❺ 失败的 sorry → 反馈给 LLM 修正
```

LLM 擅长需要"直觉"的步骤选择，Lean 的类型检查提供安全网。

## 当前局限
%%%
tag := "llm-limitations"
%%%

- 失败模式：引理名不存在 —— 原因：LLM hallucination —— 应对：引理检索系统（RAG over Mathlib）
- 失败模式：ε 分配不一致 —— 原因：缺乏全局约束 —— 应对：约束传播 + 验证
- 失败模式：语法错误 —— 原因：训练数据含 Lean 3 —— 应对：语法后处理或 fine-tuning

# 24.8 注意事项
%%%
tag := "ch24-pitfalls"
%%%

## 注意事项 1：`norm_num` vs `ring` 的适用范围
%%%
tag := "pitfall-norm-num-vs-ring"
%%%

```
-- ✗ norm_num 处理不了含变量的表达式
example (hε : 0 < ε) : ε / 2 + ε / 2 = ε := by
  norm_num  -- 失败：ε 是变量，不是数值字面量
-- ✓ 用 ring
example (hε : 0 < ε) : ε / 2 + ε / 2 = ε := by ring
```

*规则*：`norm_num` 处理*具体数值*，`ring`/`linarith` 处理*含变量的表达式*。

## 注意事项 2：`positivity` 的边界
%%%
tag := "pitfall-positivity-boundary"
%%%

```
-- ✗ positivity 不一定处理 0 < ε → 0 ≤ ε 的转换
example (hε : 0 < ε) : 0 ≤ ε := by
  positivity  -- 可能失败
-- ✓ 显式转换
example (hε : 0 < ε) : 0 ≤ ε := le_of_lt hε
```

## 注意事项 3：`filter_upwards` 的 `with` 子句
%%%
tag := "pitfall-filter-upwards-with"
%%%

```
-- ✗ 忘记 with，需要额外 intro
example (h : ∀ᶠ x in l, P x) : ∀ᶠ x in l, P x ∨ Q x := by
  filter_upwards [h]       -- 目标变成 ∀ x, P x → P x ∨ Q x
-- ✓ 用 with 直接命名
example (h : ∀ᶠ x in l, P x) : ∀ᶠ x in l, P x ∨ Q x := by
  filter_upwards [h] with x hx
  exact Or.inl hx
```

## 注意事项 4：`calc` 中混用 `≤` 和 `<`
%%%
tag := "pitfall-calc-mixed-relations"
%%%

Lean 能处理 `a ≤ b → b < c → a < c`，但不处理所有组合。
`calc` 报错时检查传递性实例——保持关系一致最安全。

## 注意事项 5：自动化设计中的 over-match
%%%
tag := "pitfall-over-match-design"
%%%

估计链 tactic 太激进时可能选错中间量——
宁可 under-match，存在歧义时要求用户显式指定（参考 §23.8 失败 5）。

# 24.9 开放问题
%%%
tag := "open-problems"
%%%

1. *通用 ε 管理*：能否用约束求解（SMT/LP）自动分配 ε 预算？
   线性分配可用 `linarith` 验证，非线性（`√ε`、`ε²`）需要更强求解器。

2. *估计链复杂度*：假设增多时候选路径指数增长，
   能否用启发式（优先三角不等式、优先匹配假设中的中间量）剪枝？

3. *结构论证的 DSL*：紧致性等多步论证，能否设计 domain-specific language
   让用户声明论证结构、tactic 自动填充细节？

4. *LLM + ITP 交互*：LLM 应生成 proof term 还是 tactic 序列？
   反馈循环应在 tactic 级别还是 subgoal 级别？

5. *跨领域迁移*：ε 管理、估计链的设计模式能否迁移到
   概率论（几乎处处收敛）、PDE（Sobolev 估计）？

# 24.10 练习
%%%
tag := "ch24-exercises"
%%%

## 练习 1（设计）：ε 分配方案
%%%
tag := "exercise-epsilon-allocation"
%%%

以下证明需要将 ε 分为三份。设计分配方案并写出 `use` 语句：

```
-- [示意]
example (hε : 0 < ε)
    (h₁ : ∃ N₁, ∀ n ≥ N₁, ‖a n - L₁‖ < ε / 3)
    (h₂ : ‖L₁ - L₂‖ < ε / 3)
    (h₃ : ∃ N₃, ∀ n ≥ N₃, ‖b n - L₂‖ < ε / 3) :
    ∃ N, ∀ n ≥ N, ‖a n - b n‖ < ε := by
  -- ❶ 从 h₁ 和 h₃ 提取 N₁ 和 N₃
  -- ❷ use max N₁ N₃
  -- ❸ 三角不等式 + linarith
  sorry
```

*提示*：`use max N₁ N₃`，对 `n ≥ max N₁ N₃` 用
`le_of_max_le_left` / `le_of_max_le_right` 拆分。
三角不等式拆为三段，每段 `< ε/3`，`linarith` 合并。

## 练习 2（设计）：模式分类
%%%
tag := "exercise-pattern-classification"
%%%

按 §24.3 的瓶颈分类（ε 选取 / 估计链 / 结构论证），
并判断哪些可用现有工具组合覆盖：

```
(a) "取 δ = min(1, ε/M)，则 |f(x) - f(a)| ≤ M·|x-a| < M·δ ≤ ε"
(b) "由 Bolzano-Weierstrass 定理，存在收敛子列..."
(c) "‖Sₙ - S‖ ≤ ‖Sₙ - Sₘ‖ + ‖Sₘ - S‖ ≤ ε/2 + ε/2"
(d) "取 N 使得 n ≥ N 时 |aₙ - L| < ε，因为 aₙ → L"
```

*提示*：(a) ε 选取（`min`），部分覆盖；(b) 结构论证，几乎无自动化；
(c) 估计链，`calc` + `linarith` 覆盖；(d) ε 选取（从假设提取），`obtain` 即可。

## 练习 3（进阶）：估计链 tactic 原型
%%%
tag := "exercise-estimation-tactic"
%%%

设计只处理 `‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖` 形式的 tactic，
写出 `elab` 伪代码骨架并说明：

```
(a) 如何匹配目标中的 ‖lhs - rhs‖ ≤ bound？
(b) 如何在假设中搜索公共中间量 b？
(c) 如何处理 bound 不是显式和而是 ε 的情况？
(d) 失败时应给出什么错误信息？
```

*提示*：(a) `matchLe?` + `matchNorm?` 递归匹配；
(b) 收集 `‖· - ·‖ ≤ ·` 假设建立端点索引，查找公共端点；
(c) 应用 `norm_sub_le` 后用 `linarith` 检查 bound；
(d) `"estimate₂: no intermediate point found connecting {lhs} to {rhs}"`。

# 24.11 小结
%%%
tag := "ch24-summary"
%%%

- `分析自动化现状`：代数/算术步骤自动化高，ε-δ/估计链/结构论证低
- `现有工具组合`：`gcongr`+`linarith`、`positivity`+`ring`、`fun_prop`+`filter_upwards`
- `三大瓶颈`：ε 选取（搜索空间）、估计链（中间量）、紧致性（多步存在量词）
- `ε 管理器`：从假设提取 > 等分 > min 组合 > 用户指定
- `估计链`：建模为图搜索，最小版本处理两段估计
- `证明模板`：半自动化——用户提供策略，tactic 填充机械步骤
- `LLM + ITP`：LLM 提供直觉，Lean 提供安全网
- `设计原则`：自动化机械部分，保留创造性部分；宁可 under-match

*一句话总结*：分析自动化的关键不是追求全自动，
而是把 80% 的机械步骤自动化，让人专注于真正需要数学直觉的 20%。

_全书完。_

_从 `CoreM` 到 `grind`，从 `simp` 的重写引擎到分析自动化的前沿——
这本书试图展示 Lean 4 自动化的全景。
希望它能帮助你不只是使用 tactic，而是理解它们、改进它们、创造新的自动化。_

_数学的形式化还在路上，自动化是加速这段旅程的引擎。_
