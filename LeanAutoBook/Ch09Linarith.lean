import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch09Linarith"

#doc (Manual) "第九章 linarith、nlinarith 与 polyrith" =>
%%%
file := "Ch09Linarith"
tag := "ch09-linarith"
%%%

*本章目标*：掌握三个算术判定 tactic 的内部原理、适用边界与失败模式，能够根据目标形状选择正确的 tactic 并在失败时给出有效提示。

# 全局图景
%%%
tag := "global-overview"
%%%

三个 tactic 解决的问题类型不同，但共享一个思路——把目标归约到某种代数判定过程：

- tactic：`linarith` —— 输入：线性不等式 / 等式 —— 判定方法：Farkas 引理 —— 外部依赖：无
- tactic：`nlinarith` —— 输入：多项式不等式 —— 判定方法：Positivstellensatz + `linarith` —— 外部依赖：无
- tactic：`polyrith` —— 输入：多项式等式 —— 判定方法：Gröbner 基 —— 外部依赖：Sage 服务器

它们在 Mathlib 中的位置：`Mathlib.Tactic.Linarith`（linarith, nlinarith）、`Mathlib.Tactic.Polyrith`（polyrith）。

选择规则：*等式用 `ring` 或 `polyrith`，线性不等式用 `linarith`，非线性不等式用 `nlinarith`*。本章重点是这条规则背后的"为什么"以及它在哪里失效。

# linarith：线性算术判定
%%%
tag := "linarith-linear-arithmetic"
%%%

## 基本用法
%%%
tag := "linarith-basic-usage"
%%%

`linarith` 证明有序域（`LinearOrderedField` 或 `LinearOrderedCommRing`）上的线性不等式：

```
-- 最简单的情况：假设的线性组合直接蕴含目标
example (x y : ℝ) (h1 : x ≤ 3) (h2 : y ≤ 4) : x + y ≤ 7 := by
  linarith
  -- ▶ 取 1 * h1 + 1 * h2 得 x + y ≤ 7

-- 传递性：linarith 自动串联不等式链
example (a b c : ℝ) (h1 : a < b) (h2 : b ≤ c) (h3 : c < 0) : a < 0 := by
  linarith
  -- ▶ 从 a < b ≤ c < 0 得 a < 0

-- 等式也可以：linarith 把 = 拆成 ≤ 和 ≥
example (x : ℝ) (h : x = 5) : x ≤ 10 := by
  linarith
```

## 内部原理：Farkas 引理
%%%
tag := "linarith-farkas-lemma"
%%%

`linarith` 的核心是 *Farkas 引理*：一组线性不等式无解，当且仅当存在非负系数的线性组合导出 `0 < 0`。

具体流程：

1. *否定目标*加入假设：要证 `a ≤ b`，假设 `a > b`
2. *收集线性假设*：从 context 中提取形如 `c₁x₁ + c₂x₂ + … ≤ k` 的假设
3. *搜索非负系数* `λᵢ ≥ 0`，使得 `Σ λᵢ · (假设ᵢ)` 化简为 `0 < 0`
4. *构造证明项*：把找到的组合翻译成 Lean 证明

```
示例推导：假设集 {x ≤ 3, y ≤ 4, x + y > 7}
取 λ₁ = 1, λ₂ = 1：
  1·(x ≤ 3) + 1·(y ≤ 4) 得 x + y ≤ 7
  与 x + y > 7 矛盾 → 0 < 0 ✓
```

预处理步骤：① 严格不等式 `a < b` 转为 `b - a > 0`；② `norm_num` 化简具体数值；③ 展开 `max`/`min`。

## 带额外提示
%%%
tag := "linarith-with-hints"
%%%

当 context 中的假设不够时，可以手动传入引理：

```
example (x y : ℝ) (h : x + y = 10) : x ≤ 10 - y := by
  linarith [h]
  -- ▶ 方括号中的项被加入假设集
```

## 失败模式
%%%
tag := "linarith-failure-modes"
%%%

*失败 1：非线性项*

```
example (x : ℝ) (h : x ≥ 2) : x ^ 2 ≥ 4 := by
  linarith  -- ✗ x ^ 2 不是 x 的线性函数
  -- 修复：nlinarith [sq_nonneg (x - 2)]
```

*失败 2：类型不支持*

```
example (n : ℕ) (h : n ≥ 1) : n + 1 ≥ 2 := by
  linarith  -- ✗ ℕ 不是有序域
  -- 修复：omega
```

> *工作规则*：遇到 `ℕ` 或 `ℤ` 上的线性算术目标，优先尝试 `omega` 而非 `linarith`。`omega` 原生支持自然数减法截断等语义，而 `linarith` 要求有序域结构。

*失败 3：假设不可见*

```
-- 如果关键假设藏在结构体字段中，linarith 看不到
-- 需要先 obtain 解构或手动传入方括号
```

# nlinarith：非线性算术
%%%
tag := "nlinarith-nonlinear-arithmetic"
%%%

## 基本用法
%%%
tag := "nlinarith-basic-usage"
%%%

`nlinarith` 处理多项式不等式。核心策略：生成假设的乘积项，然后调用 `linarith`。

```
-- 平方非负
example (x : ℝ) : x ^ 2 ≥ 0 := by
  nlinarith [sq_nonneg x]
  -- ▶ sq_nonneg x 提供 x ^ 2 ≥ 0 作为假设

-- AM-GM 的特殊情况
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * y ≤ (x ^ 2 + y ^ 2) / 2 := by
  nlinarith [sq_nonneg (x - y)]
  -- ▶ (x - y)² ≥ 0 展开为 x² - 2xy + y² ≥ 0
  --   即 x² + y² ≥ 2xy，除以 2 得结论
```

## 内部原理：Positivstellensatz
%%%
tag := "nlinarith-positivstellensatz"
%%%

*Positivstellensatz*：若多项式 `p` 在 `g₁ ≥ 0, …, gₘ ≥ 0` 定义的半代数集上严格正，则 `p` 可写成平方和多项式与约束多项式乘积之和。

`nlinarith` 的简化实现：

1. 把假设记为 `h₁, …, hₙ`（各自 `≥ 0` 或 `> 0`）
2. *枚举乘积*：生成 `hᵢ · hⱼ`、`hᵢ²` 等二次乘积
3. 把这些乘积作为新假设加入集合
4. 对增广后的假设集调用 `linarith`

## 提供手动提示
%%%
tag := "nlinarith-manual-hints"
%%%

默认只枚举二次乘积。更复杂的不等式需要手动提示：

```
-- 三次不等式：默认枚举不到
example (x : ℝ) (hx : x ≥ 1) : x ^ 3 ≥ x := by
  nlinarith [sq_nonneg x, sq_nonneg (x - 1), mul_self_nonneg (x - 1)]

-- 多变量：ab ≤ 1/4 当 a+b ≤ 1
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    a * b ≤ 1 / 4 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1)]
```

## 失败模式
%%%
tag := "nlinarith-failure-modes"
%%%

*失败 1：乘积阶数过高*

```
example (x : ℝ) (hx : x ≥ 2) : x ^ 4 ≥ 16 := by
  nlinarith  -- ✗ 默认只枚举二次乘积
  -- 修复：nlinarith [sq_nonneg (x^2 - 4), sq_nonneg x, sq_nonneg (x - 2)]
```

*失败 2：搜索空间爆炸*

`n` 个假设产生 `O(n²)` 个乘积。超过 ~8 个假设时性能下降。应对：用 `nlinarith [具体提示]` 跳过枚举，或先 `have` 推导中间不等式。

*失败 3：除法 / 分式*

```
example (x : ℝ) (hx : x > 0) : 1 / x > 0 := by
  nlinarith  -- ✗ 不理解除法语义
  -- 修复：positivity 或 exact div_pos one_pos hx
```

# polyrith：多项式等式的外部求解
%%%
tag := "polyrith-polynomial-equality"
%%%

> *⚠️ 高级工具 / 环境敏感*：`polyrith` 依赖外部 Sage 服务器，需要网络连接才能运行。它不属于本章前述可直接上手的核心 tactic，而是一个*辅助发现工具*——用于探索阶段求解系数，求解成功后应立即将输出替换为 `linear_combination`，不要将 `polyrith` 调用作为最终提交形态。CI、离线环境、或 Sage 服务器不可用时 `polyrith` 会直接失败。

## 基本用法
%%%
tag := "polyrith-basic-usage"
%%%

`polyrith` 用 Gröbner 基方法证明多项式等式，调用外部 Sage 服务器计算系数，生成 `linear_combination` 证明。

```
example (x y : ℚ) (h1 : x + y = 3) (h2 : x - y = 1) : x = 2 := by
  polyrith
  -- ▶ 输出：linear_combination (1/2) * h1 + (1/2) * h2

example (x y : ℚ) (h1 : x + y = 3) (h2 : x * y = 2) :
    x ^ 2 + y ^ 2 = 5 := by
  polyrith
  -- ▶ x² + y² = (x+y)² - 2xy = 9 - 4 = 5
```

## 内部原理：Gröbner 基
%%%
tag := "polyrith-groebner-basis"
%%%

工作流程：

1. *编码*：把假设 `hᵢ : pᵢ = 0` 和目标 `q = 0` 编码为理想成员问题 `q ∈ ⟨p₁, …, pₙ⟩`
2. *调用 Sage*：计算系数 `cᵢ` 使得 `q = Σ cᵢ pᵢ`
3. *生成证明*：输出 `linear_combination c₁ * h₁ + c₂ * h₂ + …`
4. *本地验证*：`linear_combination` 内部用 `ring` 验证

关键：*外部求解器只发现系数，证明由 Lean 本地验证*，正确性不依赖 Sage。

## 替换为 `linear_combination`
%%%
tag := "polyrith-replace-linear-combination"
%%%

`polyrith` 成功后会打印 `linear_combination` 调用。*强烈建议替换*：

```
-- 替换前（需要网络）
example (a b : ℚ) (h : a + b = 4) : 2 * a + 2 * b = 8 := by polyrith
-- 替换后（纯本地，编译更快，CI 不会因 Sage 不可用而失败）
example (a b : ℚ) (h : a + b = 4) : 2 * a + 2 * b = 8 := by
  linear_combination 2 * h
```

## 失败模式
%%%
tag := "polyrith-failure-modes"
%%%

*失败 1：无网络* — CI 或离线环境直接失败。先本地运行记录输出。

*失败 2：不等式* — `polyrith` 只处理等式，不等式用 `linarith`/`nlinarith`。

*失败 3：非 ℚ 系数* — Gröbner 基在 ℚ 上精确，ℝ 上可能找不到系数。

*失败 4：高次多变量* — Gröbner 基最坏双指数复杂度，可能超时。

# 比较与选择
%%%
tag := "comparison-and-selection"
%%%

## 决策树
%%%
tag := "decision-tree"
%%%

```
目标类型？
├─ 等式
│  ├─ 纯代数恒等式（无假设） → ring
│  ├─ 需要假设推导 → polyrith → 替换为 linear_combination
│  └─ ℤ / ℕ → omega 或 ring
│
└─ 不等式 / 序关系
   ├─ 线性（无乘积项）
   │  ├─ ℝ / ℚ → linarith
   │  └─ ℤ / ℕ → omega
   │
   └─ 非线性（有乘积 / 幂次）
      ├─ 仅需证非负 → positivity
      └─ 一般不等式 → nlinarith [提示]
         └─ 仍然失败 → 手动 have + nlinarith
```

## 与 omega 的边界
%%%
tag := "comparison-with-omega"
%%%

`omega` 处理 *Presburger 算术*（ℤ/ℕ 线性算术），`linarith` 处理*有序域线性算术*（ℝ/ℚ）。

```
example (n : ℕ) (h : n ≥ 3) : n + 1 ≥ 4 := by omega     -- ℕ → omega
example (x : ℝ) (h : x ≥ 3) : x + 1 ≥ 4 := by linarith  -- ℝ → linarith
```

# 进阶技巧
%%%
tag := "advanced-techniques"
%%%

## 组合使用
%%%
tag := "ch09-combining-tactics"
%%%

```
example (x y : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hsum : x + y = 1) :
    x ^ 2 + y ^ 2 ≥ 1 / 2 := by
  nlinarith [sq_nonneg (x - y), hsum]
  -- ▶ (x-y)² ≥ 0 → x²-2xy+y² ≥ 0
  --   结合 x+y=1 得 x²+y² ≥ 1/2
```

## 调试失败的 linarith
%%%
tag := "debugging-linarith"
%%%

诊断步骤：① 检查目标是否线性；② 检查假设是否在 context 中；③ 手动提供缺失假设。

下面是一个示意型 debug 场景——绝对值本身已超出 `linarith` 的直接适用范围，这里展示的是"拆解后再调用"的 debug 思路：

```
-- 示意：|x| 不是线性项，需要先拆成分支再用 linarith
example (x : ℝ) (h : |x| ≤ 1) : -1 ≤ x := by
  linarith  -- ✗ 不理解绝对值
  -- 修复：先拆开绝对值，让每个分支变成线性目标
  cases abs_cases x with
- inl h' => linarith [h'.1, h'.2]：inr h' => linarith [h'.1, h'.2]
```

## 在 meta 编程中调用
%%%
tag := "metaprogramming-usage"
%%%

```
-- 依次尝试多个算术 tactic
macro "auto_ineq" : tactic =>
  `(tactic| first | linarith | nlinarith | positivity | omega)
```

# 常见模式速查
%%%
tag := "common-patterns-reference"
%%%

```
-- 模式 1：传递性  h1 : a ≤ b, h2 : b ≤ c ⊢ a ≤ c
by linarith

-- 模式 2：线性组合  h1 : 2*x+y ≤ 10, h2 : x+3*y ≤ 15 ⊢ ...
by linarith

-- 模式 3：平方非负  ⊢ x^2 + y^2 ≥ 0
by positivity  -- 首选；或 nlinarith [sq_nonneg x, sq_nonneg y]

-- 模式 4：从等式假设推等式  h1 : a+b = s, h2 : a-b = d ⊢ a = (s+d)/2
by linarith

-- 模式 5：乘积保号  hx : x ≥ 0, hy : y ≥ 0 ⊢ x*y ≥ 0
by positivity

-- 模式 6：polyrith → linear_combination 工作流
-- 先 polyrith 发现系数，再替换为 linear_combination 固化证明
```

# 练习
%%%
tag := "ch09-exercises"
%%%

*练习 9.1*（linarith 基础）：

```
example (x y z : ℝ) (h1 : x + y ≤ 5) (h2 : y + z ≤ 7) (h3 : z ≤ 3) :
    x + y + z ≤ 8 := by
  sorry

example (a b : ℝ) (h1 : 2 * a + b ≤ 10) (h2 : a + 2 * b ≤ 14)
    (ha : a ≥ 0) (hb : b ≥ 0) : a + b ≤ 8 := by
  sorry
```

*练习 9.2*（nlinarith 提示）：

```
-- 为 nlinarith 找到正确的提示
example (x : ℝ) (hx : x ≥ 3) : x ^ 2 ≥ 9 := by
  nlinarith [sorry]  -- 替换 sorry 为合适的提示

example (x y : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) :
    x ^ 2 + x * y + y ^ 2 ≥ 0 := by
  nlinarith [sorry, sorry]  -- 提示：考虑 (x + y)² 和 x², y²
```

*练习 9.3*（选择正确的 tactic）：

```
-- 选择最合适的 tactic（linarith / nlinarith / omega / ring / positivity）
example (n : ℤ) (h : n ≥ 5) : 2 * n ≥ 10 := by sorry
example (x : ℝ) : (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by sorry
example (a b : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) : a ^ 2 * b ≥ 0 := by sorry
example (x y : ℚ) (h : x + y = 0) : x = -y := by sorry
```

*练习 9.4*（诊断失败）：

```
-- 以下 linarith 调用都会失败，解释原因并修复
-- (a) 非线性
example (x : ℝ) : x ^ 2 + 1 > 0 := by linarith
-- (b) ℕ 不是有序域
example (n : ℕ) (h : n + 3 ≥ 5) : n ≥ 2 := by linarith
-- (c) x*x 不是线性项
example (x : ℝ) (h : x * x ≤ 4) : x ≤ 2 := by linarith
```

*练习 9.5*（polyrith → `linear_combination`）：

```
-- 用 polyrith 求解，然后写出 linear_combination 版本
-- ⚠️ polyrith 的输出必须被记录并替换为 linear_combination，
--   不要将 polyrith 调用留在最终提交的代码中。
example (a b : ℚ) (h1 : 3 * a + 2 * b = 12) (h2 : a - b = 1) :
    a = 2 := by
  polyrith  -- 运行后记录输出，替换为 linear_combination ???
```

# 小结
%%%
tag := "ch09-summary"
%%%

- tactic：`linarith` —— 适用范围：有序域上的线性不等式/等式 —— 原理：Farkas 引理 —— 主要限制：非线性项无法处理
- tactic：`nlinarith` —— 适用范围：多项式不等式 —— 原理：Positivstellensatz 枚举 —— 主要限制：高次/多变量搜索爆炸
- tactic：`polyrith` —— 适用范围：多项式等式 —— 原理：Gröbner 基 —— 主要限制：需网络；仅处理等式

*实战建议*：

- `linarith` 是第一选择，快且可靠
- `nlinarith` 失败时先加提示，不要盲目等待枚举
- `polyrith` 的输出应替换为 `linear_combination`
- ℤ/ℕ 优先用 `omega`，非负性优先用 `positivity`

下一章：`norm_num`——精确数值计算框架。
