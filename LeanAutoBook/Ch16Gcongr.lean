import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch16Gcongr"

#doc (Manual) "第十六章 gcongr：广义合同性" =>
%%%
file := "Ch16Gcongr"
tag := "ch16-gcongr"
%%%

*本章目标*：理解 `gcongr` 如何将不等式目标分解为逐分量的子目标，
掌握 `@[gcongr]` 引理库的覆盖范围与模式匹配机制，
识别常见失败模式并学会修复，在 `calc` 链和 `positivity` 配合中高效使用 `gcongr`。

数学推理中最常见的一步：

已知 a ≤ b，而 f 单调递增，则 f(a) ≤ f(b)。

这看起来简单，但在 Lean 中手动完成时需要精确引用单调性引理并提供侧条件——
当表达式变复杂时极其繁琐。`gcongr`（*g*eneralized *congr*uence）自动完成这一过程：
分析目标两侧的公共结构，找出不同的子表达式，搜索匹配的单调性引理将目标拆解。

# 16.1 gcongr 解决什么问题
%%%
tag := "gcongr-what-it-solves"
%%%

`gcongr` 证明形如 `f(a₁, ..., aₙ) ≤ f(b₁, ..., bₙ)` 的目标，
其中 `f` 是某种关于每个参数单调的运算：

```anchor gcongrBasic
example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by gcongr

example (a b : ℝ) (h : a ≤ b) : a + 1 ≤ b + 1 := by gcongr

example (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 3 ≤ b ^ 3 := by gcongr
```

核心思想：*不手动引理，让 gcongr 搜索和分解*。它把目标两侧
当作"带洞的模板"对齐，找出不同的位置，然后用注册的单调性引理逐个填充。

# 16.2 分解机制详解
%%%
tag := "gcongr-decomposition-detail"
%%%

## 基本流程
%%%
tag := "gcongr-basic-flow"
%%%

`gcongr` 的工作分为三步：

```
目标: a₁ * c ≤ b₁ * c          （假设 h : a₁ ≤ b₁, hc : 0 ≤ c）

第一步 —— 对齐: (·) * c ≤ (·) * c
  不同位置: 左侧 a₁  vs  右侧 b₁            -- ❶
  相同位置: c = c

第二步 —— 搜索引理:
  在 @[gcongr] 引理中找到:                    -- ❷
  mul_le_mul_of_nonneg_right : a ≤ b → 0 ≤ c → a * c ≤ b * c

第三步 —— 生成子目标:
  · a₁ ≤ b₁   （由 h 关闭）                  -- ❸
  · 0 ≤ c      （由 hc 关闭）
```

- *❶* 对齐两侧结构，定位差异的子表达式。
- *❷* 在 `@[gcongr]` 标记的引理库中搜索匹配的单调性定理。
- *❸* 将原目标拆成更简单的子目标，尝试自动关闭或留给用户。

## 多位置分解
%%%
tag := "gcongr-multi-position"
%%%

当两侧有多个不同位置时，`gcongr` 逐一分解：

```anchor gcongrTwoPositions
example (a b c d : ℝ) (h1 : a ≤ b) (h2 : c ≤ d)
    (ha : 0 ≤ a) (hc : 0 ≤ c) : a * c ≤ b * d := by
  have hb : 0 ≤ b := le_trans ha h1
  gcongr
```

分解树：

```
目标: a * c ≤ b * d

对齐: (·) * (·) ≤ (·) * (·)
├── 位置 1: a vs b → 子目标 a ≤ b             -- ❶
├── 位置 2: c vs d → 子目标 c ≤ d             -- ❷
├── 侧条件: 0 ≤ a （由 ha 自动关闭）          -- ❸
└── 侧条件: 0 ≤ c （由 hc 自动关闭）          -- ❹
```

- *❶❷* 主要不等式子目标。*❸❹* 单调性引理所需的侧条件。

*注意*：`gcongr` 不只是"照着原假设机械拆分"——它搜索的单调性引理
可能引入*你意想不到的额外 side goals*。例如，目标 `a * c ≤ b * d`
拆分时，引理可能要求 `0 ≤ a` 或 `0 ≤ c`，即使你的假设中并没有
直接提供这些条件。遇到 `gcongr` 留下未关闭的子目标时，
用 `gcongr?` 查看它实际调用了哪条引理，以理解额外条件的来源。

# 16.3 `@[gcongr]` 引理库
%%%
tag := "gcongr-lemma-library"
%%%

`gcongr` 的能力完全取决于注册的引理。Mathlib 注册了数百条，覆盖常见运算：

## 算术运算
%%%
tag := "gcongr-arithmetic-operations"
%%%

```anchor gcongrArithmetic
example (a b c d : ℝ) (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by gcongr

example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by gcongr
example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by gcongr

example (a b : ℝ) (ha : 0 ≤ a) (h : a ≤ b) : a ^ 5 ≤ b ^ 5 := by gcongr
```

## 其他运算
%%%
tag := "gcongr-other-operations"
%%%

`gcongr` 还覆盖集合（`⊆`）、求和（`Finset.sum`）、积分等：

```anchor gcongrSetsAndSums
example (s t : Set ℝ) (h : s ⊆ t) (f : ℝ → ℝ) : f '' s ⊆ f '' t := by gcongr

example (s : Finset ℕ) (f g : ℕ → ℝ) (h : ∀ i ∈ s, f i ≤ g i) :
    s.sum f ≤ s.sum g := by gcongr; exact h _ ‹_›
```

## 注册自定义引理
%%%
tag := "gcongr-register-custom-lemmas"
%%%

```
-- [示意] 为自定义函数注册单调性
@[gcongr]
theorem myFunc_le_myFunc (h : a ≤ b) (ha : 0 ≤ a) : myFunc a ≤ myFunc b := ...
```

`@[gcongr]` 的要求：结论必须是 `_ ≤ _`、`_ < _` 或 `_ ⊆ _` 形式，
且参数中变化的部分对应相同的关系。

# 16.4 模式模板：用 `gcongr` 指定对齐
%%%
tag := "gcongr-pattern-templates"
%%%

有时 `gcongr` 无法自动对齐两侧结构。可以用*模式模板*显式指定，
`?_` 标记变化位置，固定部分写具体表达式：

```anchor gcongrPatternTemplates
example (a b c d : ℝ) (h1 : a ≤ b) (h2 : c ≤ d) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    a * c ≤ b * d := by
  have hb : 0 ≤ b := le_trans ha h1
  gcongr ?_ * ?_

example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  gcongr ?_ * c

example (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : (a + 1) ^ 2 ≤ (b + 1) ^ 2 := by
  gcongr (?_ + 1) ^ 2
```

- *❶* 两个占位符，`gcongr` 对两个位置分别生成子目标。
- *❷* 固定 `c`，只分解乘法左侧。
- *❸* 嵌套模式——整个 `(· + 1) ^ 2` 结构固定，只有底数变化。

*提醒*：模式模板只帮你指定"哪些位置变化"，并不保证 side goals 会变简单。
引理本身的侧条件仍然会出现，你仍需自行关闭它们。

# 16.5 gcongr 与 calc 链
%%%
tag := "gcongr-calc-chains"
%%%

`gcongr` 与 `calc` 是天然搭档——`calc` 建立不等式链，
`gcongr` 证明链中每一步的单调性推理：

```anchor gcongrCalcTransitivity
example (a b c : ℝ) (h1 : a ≤ b) (h2 : b ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 ≤ c ^ 2 := by
  calc a ^ 2
      ≤ b ^ 2 := by gcongr
    _ ≤ c ^ 2 := by gcongr
```

- *❶* `gcongr` 使用 `h1` 和 `ha`。*❷* 使用 `h2` 和 `hb`。

## 混合关系链
%%%
tag := "gcongr-mixed-relation-chain"
%%%

```anchor gcongrCalcMixed
example (a b c : ℝ) (h1 : a < b) (h2 : b ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 < c ^ 2 := by
  calc a ^ 2
      < b ^ 2 := by gcongr
    _ ≤ c ^ 2 := by gcongr
```

`gcongr` 同时支持 `≤` 和 `<`，自动搜索严格/非严格版本的单调性引理。

# 16.6 gcongr 与 positivity 的协作
%%%
tag := "gcongr-positivity-cooperation"
%%%

`gcongr` 的单调性引理常常需要侧条件如 `0 ≤ a`，
这正是 `positivity` 的专长——两者形成高效组合：

```anchor gcongrSideConditions
example (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) : x ^ 3 ≤ y ^ 3 := by
  gcongr
```

当侧条件不是简单的假设时：

```anchor gcongrExplicitSideConditions
example (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    x ^ 2 * (x + 1) ≤ y ^ 2 * (y + 1) := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  gcongr <;> linarith
```

侧条件关闭策略：上下文中有直接假设 → 自动关闭；结构化表达式 → `positivity`；
需要推理 → `linarith`。

# 16.7 gcongr 的五种失败模式
%%%
tag := "gcongr-failure-modes"
%%%

## 失败 1：两侧结构不匹配
%%%
tag := "failure-structure-mismatch"
%%%

```
-- [会报错] 两侧的函数头不同
example (a b : ℝ) (h : a ≤ b) : a ^ 2 ≤ b ^ 3 := by gcongr
  -- ▸ gcongr failed: 左侧 (·)^2 vs 右侧 (·)^3，结构不一致
  -- ▸ 修复：用 calc 拆成两步，或直接用 nlinarith
```

`gcongr` 要求两侧有*相同的外层结构*——只有"洞"里的值不同。
`a ^ 2` 和 `b ^ 3` 的指数不同，无法对齐。

## 失败 2：缺少侧条件
%%%
tag := "failure-missing-side-conditions"
%%%

```
-- [会报错] 乘法单调性需要非负条件
example (a b c : ℝ) (h : a ≤ b) : a * c ≤ b * c := by gcongr
  -- ▸ gcongr failed: 缺少 0 ≤ c
  -- ▸ 修复：添加假设 (hc : 0 ≤ c) 或在上下文中提供
```

这是最常见的失败——单调性引理有侧条件（如底数非负、乘数非负），
但上下文中找不到对应的假设。

```
-- [会报错] 幂需要底数非负
example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by gcongr
  -- ▸ 修复：添加 (ha : 0 ≤ a)
```

## 失败 3：找不到注册的引理
%%%
tag := "failure-no-registered-lemma"
%%%

```
-- [会报错] 目标关系没有对应的 @[gcongr] 引理
example (a b : ℝ) (h : a ≤ b) : Real.log a ≤ Real.log b := by gcongr
  -- ▸ 修复：log 的单调性需要 0 < a 的条件且可能没有注册 @[gcongr]
  -- ▸ 改用 Real.log_le_log 手动引用
```

不是所有函数都注册了 `@[gcongr]` 引理。可在 Mathlib 中搜索确认。

## 失败 4：目标不是不等式
%%%
tag := "failure-not-inequality"
%%%

```
-- [会报错] gcongr 只处理 ≤、<、⊆ 等序关系
example (a b : ℝ) (h : a = b) : a + 1 = b + 1 := by gcongr
  -- ▸ 修复：等式用 congr 或 rw，不用 gcongr
```

`gcongr` 是*不等式*的合同性工具。等式有专门的 `congr` tactic。

## 失败 5：表达式方向反了
%%%
tag := "failure-wrong-direction"
%%%

```
-- [会报错] 假设方向和目标不一致
example (a b c : ℝ) (h : b ≤ a) (hc : 0 ≤ c) : a * c ≤ b * c := by gcongr
  -- ▸ gcongr 需要 a ≤ b，但假设是 b ≤ a
  -- ▸ 修复：目标方向可能有误，或用 gcongr; exact h.le / linarith
```

`gcongr` 不会翻转假设方向。如果目标需要 `a ≤ b` 但只有 `b ≤ a`，
需要手动检查目标是否正确。

# 16.8 调试技巧
%%%
tag := "gcongr-debugging-tips"
%%%

## 技巧 1：用 gcongr? 查看分解
%%%
tag := "tip-gcongr-question-mark"
%%%

```anchor gcongrQuery
example (a b : ℝ) (h : a ≤ b) (ha : 0 ≤ a) : a ^ 2 ≤ b ^ 2 := by
  gcongr
```

`gcongr?` 输出具体的引理调用，可用于理解分解过程或替换为显式证明。

## 技巧 2：用 calc 拆步定位失败
%%%
tag := "tip-calc-step-failure-location"
%%%

```
-- [示意] 一次性 gcongr 失败时，拆成两步定位问题
example (a b c d : ℝ) (h1 : a ≤ b) (h2 : c ≤ d)
    (ha : 0 ≤ a) (hc : 0 ≤ c) :
    a ^ 2 * c ≤ b ^ 2 * d := by
  calc a ^ 2 * c
      ≤ b ^ 2 * c := by gcongr    -- ✓ 先处理底数
    _ ≤ b ^ 2 * d := by gcongr    -- ✓ 再处理乘数
```

# 16.9 gcongr vs 其他不等式 tactic
%%%
tag := "gcongr-vs-other-tactics"
%%%

- 场景：`f(a) ≤ f(b)`，单调函数 —— 推荐 tactic：`gcongr` —— 原因：自动搜索单调性引理
- 场景：`0 ≤ e` 或 `0 < e` —— 推荐 tactic：`positivity` —— 原因：符号分析，非单调性
- 场景：线性不等式组合 —— 推荐 tactic：`linarith` —— 原因：线性算术
- 场景：非线性不等式 —— 推荐 tactic：`nlinarith` —— 原因：非线性算术，可能需要提示

# 16.10 练习
%%%
tag := "ch16-exercises"
%%%

## 练习 1（基础）：判断 gcongr 能否成功
%%%
tag := "exercise-16-1"
%%%

判断以下哪些能被 `gcongr` 证明，不能的说明原因：

```
example (a b : ℝ) (h : a ≤ b) : a + 3 ≤ b + 3 := by sorry          -- (a)
example (a b : ℝ) (h : a ≤ b) : a * b ≤ b * b := by sorry          -- (b)
example (a b : ℝ) (h : a ≤ b) : a ^ 2 ≤ b ^ 3 := by sorry          -- (c)
example (a b c : ℝ) (h : a ≤ b) : a * c ≤ b * c := by sorry        -- (d)
example (a b : ℝ) (h : a ≤ b) (ha : 0 ≤ a) : a ^ 4 ≤ b ^ 4 := by sorry -- (e)
```

*提示*：(a) ✓ 加法无条件单调；(b) 需要 `0 ≤ b` 作为侧条件；
(c) ✗ 指数不同，结构不匹配；(d) 需要 `0 ≤ c` 侧条件；
(e) ✓ 有底数非负假设。

## 练习 2（calc 链）：分步不等式
%%%
tag := "exercise-16-2"
%%%

```
example (a b c : ℝ) (h1 : a ≤ b) (h2 : b ≤ c)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a ^ 2 + a ≤ c ^ 2 + c := by
  sorry
```

*提示*：用 `gcongr` 直接尝试，或用 `calc` 拆成 `a^2+a ≤ b^2+b ≤ c^2+c`，
每步用 `gcongr` + `linarith`。

## 练习 3（侧条件修复）：补充假设
%%%
tag := "exercise-16-3"
%%%

```
-- 添加最少的假设使 gcongr 成功
example (a b c d : ℝ) (h1 : a ≤ b) (h2 : c ≤ d)
    /- 补充假设 -/ : a * c ≤ b * d := by
  gcongr
```

*提示*：需要 `(ha : 0 ≤ a) (hc : 0 ≤ c)`——乘法两侧都需非负。
注意是较小的那侧（`a` 和 `c`）需要非负，不是较大侧。

## 练习 4（positivity 配合）：复合不等式
%%%
tag := "exercise-16-4"
%%%

```
example (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    x ^ 2 * Real.exp x ≤ y ^ 2 * Real.exp y := by
  sorry
```

*提示*：`gcongr` 可以分解，侧条件由 `positivity` 或 `linarith` 关闭。
注意 `exp` 的单调性可能需要 `Real.exp_le_exp.mpr`。

## 练习 5（实战）：从 calc 链构建证明
%%%
tag := "exercise-16-5"
%%%

```
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
    a ^ 3 + a ^ 2 ≤ b ^ 3 + b ^ 2 := by
  sorry
```

*提示*：`gcongr` 直接在 `+` 上分解：`a^3 ≤ b^3` 和 `a^2 ≤ b^2`，
每个子目标再由 `gcongr` 或 `gcongr; assumption` 处理。

## 练习 6（进阶）：模式模板
%%%
tag := "exercise-16-6"
%%%

```
example (a b c : ℝ) (h : a ≤ b) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    (a + c) ^ 2 ≤ (b + c) ^ 2 := by
  sorry
```

*提示*：使用 `gcongr (?_ + c) ^ 2` 指定只有 `?_` 位置变化，
然后关闭子目标 `a ≤ b` 和侧条件 `0 ≤ a + c`（用 `linarith` 或 `positivity`）。

# 16.11 小结
%%%
tag := "ch16-summary"
%%%

- `核心功能`：将 `f(a) ≤ f(b)` 分解为逐分量的 `aᵢ ≤ bᵢ` 子目标
- `分解机制`：对齐两侧结构，定位不同的子表达式，搜索 `@[gcongr]` 引理
- `引理要求`：结论为 `≤`、`<`、`⊆` 形式的单调性定理
- `模式模板`：`gcongr ?_ * c` 显式指定哪些位置变化
- `侧条件`：乘法/幂需要非负条件，通常由 `positivity` 或假设关闭
- `主要陷阱`：结构不匹配、缺侧条件、无注册引理、方向反了
- `calc 协作`：建立不等式链，每步由 `gcongr` 证明
- `positivity 协作`：`positivity` 提供 `0 ≤ a` 等侧条件
- `调试`：`gcongr?` 查看引理，`calc` 拆步定位，`exact?` 搜索引理

`gcongr` 是不等式工具链中的*结构分解专家*——不做算术推理，
只做"两侧结构相同时，逐位置传递不等式"。理解其本质，才能与 `linarith`、`positivity`、`calc` 有效组合。
