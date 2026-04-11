import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch15FunProp"

#doc (Manual) "`fun_prop`：函数性质的自动证明" =>
%%%
file := "Ch15FunProp"
tag := "ch15-fun-prop"
%%%

*本章目标*：理解 `fun_prop` 如何通过函数分解 + 规则搜索自动证明
连续性、可微性、可测性等函数性质，
掌握引理注册机制与常见失败模式，在分析证明中高效使用 `fun_prop`。

数学分析中最常见的"体力活"之一：证明一个复合函数连续、可微或可测。
推理模式几乎总是相同的——把函数拆开，逐个确认子函数满足性质，
再用"性质对组合封闭"的引理拼回来。`fun_prop` 把这个过程完全自动化。

# 15.1 `fun_prop` 解决什么问题
%%%
tag := "fun-prop-what-it-solves"
%%%

```anchor funPropBasic
example : Continuous (fun x : ℝ => x ^ 2 + 3 * x + 1) := by fun_prop

example : Differentiable ℝ (fun x : ℝ => Real.exp (x ^ 2)) := by fun_prop

example : Measurable (fun x : ℝ => x + 1) := by fun_prop
```

核心思想：*递归分解函数结构*。
把 `fun x => f (g x) + h x` 拆成 `f`、`g`、`h`，
逐个在 `@[fun_prop]` 引理库中搜索，再用组合规则拼出整体证明。

## 历史背景
%%%
tag := "fun-prop-history"
%%%

在 `fun_prop` 之前，Mathlib 有独立的 `continuity`（连续性）和 `measurability`（可测性）tactic，
各自维护规则集。`fun_prop` 将它们统一为一个框架：

```anchor funPropLegacy
example : Continuous (fun x : ℝ => x ^ 2 + 1) := by fun_prop
example : Continuous (fun x : ℝ => x ^ 2 + 1) := by continuity
example : Measurable (fun x : ℝ => x + 1) := by fun_prop
example : Measurable (fun x : ℝ => x + 1) := by measurability
```

- *❶❷* 旧 tactic 目前仍然可用，但其内部实现和兼容性可能随版本变化。
  *新代码应统一使用 `fun_prop`*。

*注意*：`fun_prop` 是 *tactic*（在 `by` 后使用），不是 term-level 常量。

# 15.2 工作原理
%%%
tag := "fun-prop-how-it-works"
%%%

## 四步流程
%%%
tag := "fun-prop-four-steps"
%%%

1. *识别目标类型*：检查目标是否形如 `P f`（`Continuous`、`Differentiable ℝ`、`Measurable` 等）
2. *函数分解*：把 `f` 拆成基本函数的组合——识别 lambda 结构、复合、算术运算
3. *规则搜索*：在 `@[fun_prop]` 引理库中查找匹配规则
4. *递归证明*：对每个子函数递归执行步骤 1–3

## 分解过程详解
%%%
tag := "fun-prop-decomposition-detail"
%%%

以 `Continuous (fun x : ℝ => Real.exp (x ^ 2 + 1))` 为例：

```
目标: Continuous (fun x => exp (x ^ 2 + 1))

第一层: 复合 exp ∘ (fun x => x ^ 2 + 1)
├── 外层: exp
│   └── Real.continuous_exp → ✓                     -- ❶
├── 内层: fun x => x ^ 2 + 1
│   第二层: 加法 (·) + (·)
│   ├── 左: fun x => x ^ 2
│   │   ├── 底: fun x => x → continuous_id → ✓     -- ❷
│   │   └── Continuous.pow → ✓                      -- ❸
│   ├── 右: fun _ => 1 → continuous_const → ✓       -- ❹
│   └── Continuous.add → ✓                          -- ❺
└── Continuous.comp → ✓                             -- ❻
```

- *❶* `exp` 连续是已注册的基本事实。*❷❸* 恒等函数连续，连续函数的幂连续。
- *❹* 常数函数连续。*❺* 连续函数之和连续。*❻* 复合规则组合最终证明。

## Lambda 分解：与 aesop 的核心区别
%%%
tag := "fun-prop-lambda-decomposition"
%%%

`fun_prop` 的核心能力是*理解 lambda 表达式的结构*——
识别 `fun x => f (g x)` 是 `f ∘ g`，`fun x => f x + g x` 是逐点加法。
`aesop` 是通用搜索，不理解函数组合的特殊结构，因此通常无法处理这类目标。

```anchor funPropNested
example : Continuous (fun x : ℝ => Real.exp (Real.sin (x ^ 2))) := by fun_prop
```

# 15.3 `@[fun_prop]` 引理注册
%%%
tag := "fun-prop-lemma-registration"
%%%

`fun_prop` 的能力完全取决于注册的引理库。Mathlib 中注册了数百条引理，分三类。

*类型 1：基本函数*

```
-- @[fun_prop]
-- theorem continuous_id : Continuous (id : α → α)           -- ❶ 恒等函数

-- @[fun_prop]
-- theorem continuous_const : Continuous (fun _ : α => c)     -- ❷ 常数函数

-- @[fun_prop]
-- theorem Real.continuous_exp : Continuous Real.exp           -- ❸ 领域特定
```

- *❶❷* 所有性质都需要的基础规则。*❸* 特定函数的基本事实。

*类型 2：组合规则*

```
-- @[fun_prop]
-- theorem Continuous.comp (hg : Continuous g) (hf : Continuous f) :
--     Continuous (g ∘ f)                                     -- ❶ 复合

-- @[fun_prop]
-- theorem Continuous.add (hf : Continuous f) (hg : Continuous g) :
--     Continuous (fun x => f x + g x)                        -- ❷ 加法

-- @[fun_prop]
-- theorem Continuous.mul (hf : Continuous f) (hg : Continuous g) :
--     Continuous (fun x => f x * g x)                        -- ❸ 乘法
```

- *❶* 复合规则是核心——分解函数结构后靠它拼回来。

*类型 3：带条件的规则*

```
-- @[fun_prop]
-- theorem Continuous.div (hf : Continuous f) (hg : Continuous g)
--     (h0 : ∀ x, g x ≠ 0) :                                -- ❶ 需要分母非零
--     Continuous (fun x => f x / g x)
```

- *❶* 带条件的规则产生*侧目标*——`fun_prop` 尝试自动处理，失败则留给用户。

## 支持的性质
%%%
tag := "fun-prop-supported-properties"
%%%

`fun_prop` 不硬编码特定性质，通过引理注册支持任意性质。
Mathlib 中已注册的主要性质包括：
`Continuous`、`Differentiable ℝ`、`Measurable`、`AEMeasurable`、
`AEStronglyMeasurable`、`LipschitzWith K` 等。

```anchor funPropMultiProperty
example : Continuous (fun x : ℝ => x ^ 2 + 1) := by fun_prop
example : Differentiable ℝ (fun x : ℝ => x ^ 3 - x) := by fun_prop
example : Measurable (fun x : ℝ => x * 2) := by fun_prop
```

# 15.4 `fun_prop` 的五种失败模式
%%%
tag := "fun-prop-failure-modes"
%%%

## 失败 1：性质未注册
%%%
tag := "failure-unregistered-property"
%%%

```
-- [会报错] 自定义性质没有 fun_prop 引理
def MySmooth (f : ℝ → ℝ) : Prop := Continuous f ∧ Differentiable ℝ f

example : MySmooth (fun x : ℝ => x ^ 2) := by fun_prop
  -- ▸ fun_prop failed: MySmooth 不是已注册的函数性质
  -- ▸ 修复：分别证明两个分量
example : MySmooth (fun x : ℝ => x ^ 2) := by
  exact ⟨by fun_prop, by fun_prop⟩
```

## 失败 2：自定义函数未展开
%%%
tag := "failure-custom-function-not-unfolded"
%%%

```
-- [会报错] fun_prop 不自动展开定义
noncomputable def mySpecialFun (x : ℝ) : ℝ := Real.exp (Real.sin x)

example : Continuous (fun x : ℝ => mySpecialFun x + 1) := by fun_prop
  -- ▸ 修复方案 1：先 unfold
example : Continuous (fun x : ℝ => mySpecialFun x + 1) := by
  unfold mySpecialFun; fun_prop                            -- ❶

-- ▸ 修复方案 2：一次性注册引理（更好）
-- @[fun_prop]
-- theorem continuous_mySpecialFun : Continuous mySpecialFun := by
--   unfold mySpecialFun; fun_prop                         -- ❷
```

- *❶* `unfold` 暴露内部结构。*❷* 注册后以后都不用 `unfold`。

## 失败 3：侧目标无法自动解决
%%%
tag := "failure-side-goal-unsolved"
%%%

```
-- [会报错] 除法需要分母非零，fun_prop 无法自动证明
example : Continuous (fun x : ℝ => 1 / x) := by fun_prop
  -- ▸ 产生侧目标 ∀ x, x ≠ 0，但无法证明
  -- ▸ 修复：限制定义域或用 disch 提供条件
```

## 失败 4：非 lambda 形式
%%%
tag := "failure-non-lambda-form"
%%%

```
-- [会报错] Function.comp 形式不易分解
example : Continuous (Function.comp Real.exp Real.sin) := by fun_prop
  -- ▸ 修复：用 show 转换为 lambda 形式
example : Continuous (Function.comp Real.exp Real.sin) := by
  show Continuous (fun x => Real.exp (Real.sin x))         -- ❶
  fun_prop
```

- *❶* `fun_prop` 针对 `fun x => ...` 优化，`show` / `change` 可帮助转换。

## 失败 5：性质间依赖
%%%
tag := "failure-property-dependency"
%%%

```
-- [示意] fun_prop 不自动利用 "Differentiable 蕴含 Continuous" 的关系
-- 自定义性质中要注意：只注册了 P 的引理，不会自动推出蕴含的性质 Q
```

# 15.5 调试技巧
%%%
tag := "fun-prop-debugging-tips"
%%%

## 技巧 1：trace 查看搜索过程
%%%
tag := "tip-trace-search-process"
%%%

```
set_option trace.Meta.Tactic.fun_prop true in
example : Continuous (fun x : ℝ => x ^ 2 + 1) := by fun_prop
```

trace 输出显示每一步分解和规则匹配：

```
[Meta.Tactic.fun_prop] Continuous (fun x => x ^ 2 + 1)
  [Meta.Tactic.fun_prop] Continuous (fun x => x ^ 2)      -- ❶
    [Meta.Tactic.fun_prop] Continuous (fun x => x)         -- ❷
    [Meta.Tactic.fun_prop] ✓ continuous_id
  [Meta.Tactic.fun_prop] Continuous (fun _ => 1)           -- ❸
    [Meta.Tactic.fun_prop] ✓ continuous_const
  [Meta.Tactic.fun_prop] ✓ Continuous.add
```

- *❶* 分解加法左侧。*❷* 分解幂的底数。*❸* 分解加法右侧。

## 技巧 2：逐步分解定位失败
%%%
tag := "tip-stepwise-failure-location"
%%%

```
-- [示意] 大表达式失败时，拆开逐个测试
example : Continuous (fun x : ℝ => Real.exp (1 / Real.sin x)) := by
  -- fun_prop 失败——拆开定位：
  -- have h1 : Continuous Real.exp := by fun_prop                 -- ✓
  -- have h2 : Continuous (fun x => 1 / Real.sin x) := by fun_prop  -- ✗
  -- 原因：sin x 可能为零，除法需要分母非零条件
  sorry
```

## 技巧 3：unfold + show 暴露结构
%%%
tag := "tip-unfold-show-structure"
%%%

```anchor funPropCustomDef
noncomputable def quadratic (a b c x : ℝ) : ℝ := a * x ^ 2 + b * x + c

example (a b c : ℝ) : Continuous (quadratic a b c) := by
  unfold quadratic
  fun_prop
```

# 15.6 与其他 tactic 的协作
%%%
tag := "fun-prop-cooperation"
%%%

## 模式 1：disch 处理侧目标
%%%
tag := "pattern-disch-side-goals"
%%%

`fun_prop` 的 `disch` 参数指定侧目标处理策略：

```anchor funPropDisch
example (x : ℝ) (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun y : ℝ => 1 / y) x := by
  fun_prop (disch := assumption)
```

- *❶* `disch` 告诉 `fun_prop`：遇到侧目标时用指定 tactic 解决。

## 模式 2：simp 化简后收尾
%%%
tag := "pattern-simp-then-fun-prop"
%%%

```anchor funPropSimp
example : Continuous (fun x : ℝ => x + 0) := by
  fun_prop
```

## 模式 3：分析证明中的组合链
%%%
tag := "pattern-analysis-composition-chain"
%%%

```anchor funPropGaussian
example : Continuous (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) := by fun_prop
```

## 选择速查表
%%%
tag := "fun-prop-selection-table"
%%%

- 场景：`Continuous f`、`Differentiable ℝ f` 等 —— 推荐 tactic：`fun_prop` —— 原因：专门为此设计
- 场景：连续性 + 旧代码兼容 —— 推荐 tactic：`continuity` —— 原因：目前仍可用，兼容性可能变化
- 场景：`0 ≤ e` 或 `0 < e` —— 推荐 tactic：`positivity` —— 原因：符号判定，不是函数性质
- 场景：分母 `≠ 0` 作为侧目标 —— 推荐 tactic：`positivity` / `norm_num` —— 原因：与 `disch` 配合

# 15.7 进阶：注册自定义引理
%%%
tag := "fun-prop-register-custom-lemmas"
%%%

```
-- [示意] 证明并注册自定义函数的连续性
noncomputable def softplus (x : ℝ) : ℝ := Real.log (1 + Real.exp x)

@[fun_prop]
theorem continuous_softplus : Continuous softplus := by    -- ❶
  unfold softplus
  fun_prop                                                 -- ❷ 自举：用 fun_prop 证明

-- 注册后 fun_prop 能自动处理包含 softplus 的表达式
-- example : Continuous (fun x : ℝ => softplus x + x) := by fun_prop
```

- *❶* `@[fun_prop]` 标注使引理进入搜索库。
- *❷* 证明本身用 `fun_prop`（`unfold` 之后）——这是自举。

# 15.8 练习
%%%
tag := "ch15-exercises"
%%%

## 练习 1（基础）：判断 `fun_prop` 能否成功
%%%
tag := "exercise-15-1"
%%%

```
example : Continuous (fun x : ℝ => x ^ 2 + 1) := by sorry          -- (a)
example : Continuous (fun x : ℝ => 1 / x) := by sorry              -- (b)
example : Differentiable ℝ (fun x : ℝ => Real.exp x) := by sorry   -- (c)
example : Continuous (fun x : ℝ => if x > 0 then x else 0) := by sorry  -- (d)
example : Measurable (fun x : ℝ => x * 3 + 2) := by sorry          -- (e)
```

*提示*：(a) 多项式 ✓；(b) 分母可能为零 ✗；(c) exp 可微 ✓；
(d) 分段函数不是标准组合结构 ✗；(e) 线性函数可测 ✓。

## 练习 2（unfold 技巧）：处理自定义函数
%%%
tag := "exercise-15-2"
%%%

```
noncomputable def kinetic_energy (m v : ℝ) : ℝ := m * v ^ 2 / 2

example (m : ℝ) : Continuous (kinetic_energy m) := by
  sorry
```

*提示*：先 `unfold kinetic_energy`，再 `fun_prop`。

## 练习 3（组合推理）：嵌套复合
%%%
tag := "exercise-15-3"
%%%

```
example : Continuous (fun x : ℝ => Real.exp (Real.sin x + Real.cos x)) := by
  sorry
```

*提示*：`fun_prop` 直接可用——逐层分解复合结构。

## 练习 4（修复失败）：补充条件
%%%
tag := "exercise-15-4"
%%%

```
-- 添加缺少的假设使 fun_prop 成功
example (f : ℝ → ℝ) : Continuous (fun x => f x + x) := by fun_prop
```

*提示*：需要假设 `(hf : Continuous f)`。`fun_prop` 不能凭空得知 `f` 连续。

## 练习 5（disch）：处理侧目标
%%%
tag := "exercise-15-5"
%%%

```
example (x : ℝ) (hx : x > 0) :
    DifferentiableAt ℝ (fun y : ℝ => Real.log y) x := by
  sorry
```

*提示*：`fun_prop (disch := linarith)` 或
先 `have : x ≠ 0 := by linarith` 再 `fun_prop (disch := assumption)`。

## 练习 6（实战）：分母非零
%%%
tag := "exercise-15-6"
%%%

```
example : Continuous (fun x : ℝ => (Real.exp x - 1) / Real.exp x) := by
  sorry
```

*提示*：分母 `exp x > 0` 恒成立。
尝试 `fun_prop (disch := positivity)`。

# 15.9 小结
%%%
tag := "ch15-summary"
%%%

- `目标形式`：`P f`，其中 `P` 是已注册的函数性质
- `工作原理`：函数分解 + `@[fun_prop]` 规则搜索 + 递归证明
- `统一框架`：新代码统一用 `fun_prop`，旧 tactic 兼容性可能随版本变化
- `三类引理`：基本函数、组合规则、带条件规则
- `Lambda 分解`：理解 lambda 结构，这是与 `aesop` 的核心区别
- `主要陷阱`：自定义函数未展开、分母非零条件、非 lambda 形式
- `disch` 参数：指定侧目标处理策略（`assumption` / `positivity` / `norm_num`）
- `调试`：`set_option trace.Meta.Tactic.fun_prop true` 查看搜索过程

`fun_prop` 是分析证明中的*函数性质专家*——不做计算，只回答"这个函数是否满足某性质"。
理解其分解机制和引理注册系统，是高效使用它的关键。
