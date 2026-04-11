import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch17FieldSimp"

#doc (Manual) "`field_simp`：分式化简" =>
%%%
file := "Ch17FieldSimp"
tag := "ch17-field-simp"
%%%

*本章目标*：理解 `field_simp` 如何消除分母并收集非零条件，
掌握它与 `ring`、`positivity` 的典型组合模式，
识别常见失败模式并学会修复，在分式等式与不等式证明中高效使用 `field_simp`。

数学中的分式化简看似简单——通分、约分、消分母——
但在 Lean 中手动完成时，需要反复引用 `div_add_div`、`div_eq_iff` 等引理，
还要为每一步提供分母非零的证明。当嵌套分式变深时，手动证明迅速失控。
`field_simp` 自动完成整个流程：收集非零条件、通分、消分母，
把含分式的目标化归为*无分母的多项式等式*，交给 `ring` 收尾。

# 17.1 `field_simp` 解决什么问题
%%%
tag := "field-simp-what-it-solves"
%%%

`field_simp` 证明含除法/分式的等式（或化简含分式的目标）：

```anchor fieldSimpBasic
example (x : ℝ) (hx : x ≠ 0) : 1 / x * x = 1 := by field_simp

example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    1/a + 1/b = (a + b) / (a * b) := by
  field_simp
  ring

example (x : ℝ) (hx : x ≠ 0) : (x ^ 2 - 1) / x = x - 1 / x := by
  field_simp
```

- *❶* `field_simp` 把含 `/x` 的等式化为不含除法的等式。
- *❷* 消分母后的目标是纯多项式等式，`ring` 是完备决策过程。

核心思想：*`field_simp` 负责消分母，`ring` 负责多项式等式*——两者分工明确。

# 17.2 内部原理
%%%
tag := "field-simp-internals"
%%%

`field_simp` 本质上是 `simp` 加载了一套*分式化简引理集*。
其工作分为三步：

```
目标: 1/a + 1/b = (a + b) / (a * b)    （假设 ha : a ≠ 0, hb : b ≠ 0）

第一步 —— 收集非零条件:
  扫描上下文，建立非零事实集合:               -- ❶
  { a ≠ 0 (from ha), b ≠ 0 (from hb), a * b ≠ 0 (derived) }

第二步 —— 应用通分/消分母引理:
  div_add_div: 1/a + 1/b = (1*b + a*1)/(a*b)  -- ❷
  div_eq_div_iff: LHS/(a*b) = RHS/(a*b)
    ↔ LHS = RHS  (使用 a*b ≠ 0)

第三步 —— 化简:
  目标变为: b + a = a + b                      -- ❸
  （或更一般的多项式等式，留给后续 tactic）
```

- *❶* 非零条件的收集是自动的——不仅扫描假设，还推导组合非零性。
- *❷* 核心引理：`div_add_div`（通分）、`div_eq_iff`（消分母）。
- *❸* 消分母后的目标可能被 `simp` 直接关闭，或留给 `ring`。

## 关键引理
%%%
tag := "field-simp-key-lemmas"
%%%

```
-- field_simp 使用的核心引理（来自 Mathlib）
theorem div_add_div (a : α) (c : α) {b d : α}          -- ❶
    (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b + c / d = (a * d + b * c) / (b * d)

theorem div_eq_iff {b : α} (hb : b ≠ 0) :              -- ❷
    a / b = c ↔ a = c * b

theorem div_div {a b c : α} :                           -- ❸
    a / b / c = a / (b * c)
```

- *❶* 通分引理：两个分式相加。
- *❷* 消分母引理：等式两侧同乘分母。
- *❸* 嵌套除法引理：`(a/b)/c` 化为 `a/(b*c)`。

# 17.3 非零条件的来源
%%%
tag := "field-simp-nonzero-sources"
%%%

`field_simp` 在消分母前必须确认分母非零。它从四类来源自动收集：

```anchor fieldSimpNonzeroSources
example (x : ℝ) (hx : x ≠ 0) : 1 / x * x = 1 := by field_simp

example (x : ℝ) (hx : 0 < x) : 1 / x + 1 = (x + 1) / x := by
  field_simp; ring

example (x : ℝ) : x / 2 + x / 3 = 5 * x / 6 := by
  field_simp; ring

example (x y : ℝ) (h : x + y ≠ 0) :
    1 / (x + y) * (x + y) = 1 := by
  field_simp [h]
```

- *❶* `field_simp` 内部从 `0 < x`、`x < 0` 等推出 `x ≠ 0`。
- *❷* 字面量分母（如 `2`、`3`）由内部 `norm_num` 验证非零。
- *❸* `a + b ≠ 0` 等复合条件无法自动推导，但 `a * b ≠ 0` 可以从 `a ≠ 0` 和 `b ≠ 0` 自动推导。

# 17.4 典型工作流
%%%
tag := "field-simp-workflows"
%%%

## 情况 1：`field_simp` → `ring`
%%%
tag := "field-simp-then-ring"
%%%

最常见的模式——`field_simp` 消分母，`ring` 处理多项式等式：

```anchor fieldSimpThenRing
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    1/a - 1/b = (b - a) / (a * b) := by
  field_simp
```

## 情况 2：`field_simp` 直接关闭
%%%
tag := "field-simp-closes-directly"
%%%

有时消分母后目标直接成立，不需要 `ring`：

```anchor fieldSimpDirect
example (x : ℝ) (hx : x ≠ 0) : x / x = 1 := by
  field_simp
```

*注意*：如果 `field_simp` 已经关闭目标，再写 `ring` 会报 `no goals`。
先试 `field_simp`，看是否还有剩余目标再决定后续步骤。

## 情况 3：需要补充非零条件
%%%
tag := "field-simp-supplement-nonzero"
%%%

```anchor fieldSimpSupplementary
example (a : ℝ) (ha : a ≠ 0) : (a + 1/a) ^ 2 = a ^ 2 + 2 + 1/a ^ 2 := by
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  field_simp
  ring
```

- *❶* `a ^ 2 ≠ 0` 不总能被自动推导，有时需要手动提供。

## 工作流决策树
%%%
tag := "field-simp-decision-tree"
%%%

```
field_simp 之后：
  │
  ├─ 目标已关闭？     → 结束（不要写 ring）
  │
  ├─ 剩余多项式等式？ → 接 ring
  │
  ├─ 剩余不等式？     → 接 linarith / nlinarith / positivity
  │
  └─ 产生 side goals（x ≠ 0 等）？ → 用假设 / positivity / norm_num 关闭
```

# 17.5 `field_simp` 的五种失败模式
%%%
tag := "field-simp-failure-modes"
%%%

## 失败 1：缺少非零条件
%%%
tag := "field-simp-fail-missing-nonzero"
%%%

```
-- [会报错] 分母非零性无法推导
example (x : ℝ) : 1 / x * x = 1 := by field_simp
  -- ▸ field_simp 无法证明 x ≠ 0
  -- ▸ 修复：添加假设 (hx : x ≠ 0)
```

这是最常见的失败。`field_simp` 不会"假设"分母非零——
它必须从上下文中*证明*每一个分母非零。

## 失败 2：复合分母不被识别
%%%
tag := "field-simp-fail-compound-denom"
%%%

```
-- [会报错] x + y 的非零性无法自动推导
example (x y : ℝ) : 1 / (x + y) + 1 = (x + y + 1) / (x + y) := by
  field_simp
  -- ▸ 修复方案 1：添加假设 (h : x + y ≠ 0)
  -- ▸ 修复方案 2：field_simp [show x + y ≠ 0 from ...]
```

`field_simp` 能自动推导 `a * b ≠ 0`（从 `a ≠ 0` 和 `b ≠ 0`），
但对 `a + b ≠ 0` 这类条件需要显式提供。

## 失败 3：ring 收尾失败
%%%
tag := "field-simp-fail-ring-mismatch"
%%%

```
-- [会报错] field_simp 成功但 ring 无法关闭
example (x : ℝ) (hx : x ≠ 0) (h : x > 1) :
    1 / x < 1 := by
  field_simp
  -- ⊢ 1 < x （这不是多项式等式！）
  -- ring  -- ❌ ring 只处理等式
  linarith  -- ✓ 不等式用 linarith
```

`field_simp` 后不一定接 `ring`——要看剩余目标的类型选择合适的 tactic。

## 失败 4：目标中没有分式
%%%
tag := "field-simp-fail-no-fraction"
%%%

```
-- [不会报错但无效果] 没有分母可消
example (a b : ℝ) : a + b = b + a := by
  field_simp     -- ▸ 什么都没做，目标不变
  ring           -- ▸ 实际由 ring 完成
```

`field_simp` 在没有分式的目标上是空操作（no-op），不会报错但浪费一行。
如果目标已经是多项式等式，直接用 `ring`。

## 失败 5：除法语义冲突（ℕ / ℤ 上的整除）
%%%
tag := "field-simp-fail-nat-div"
%%%

```
-- [会报错] 自然数除法是截断除法，不是域除法
-- example (n : ℕ) (hn : n ≠ 0) : n / n = 1 := by field_simp
  -- ▸ field_simp 需要域结构（Field），ℕ 不是域
  -- ▸ 修复：用 Nat.div_self（自然数除法引理）或转换到 ℚ/ℝ
example (n : ℕ) (hn : 0 < n) : n / n = 1 := Nat.div_self hn
```

`field_simp` 只在 `Field`（或 `DivisionRing`）上工作。
`ℕ` 和 `ℤ` 上的 `/` 是整数除法，不在其适用范围内。

# 17.6 与其他 tactic 的协作
%%%
tag := "field-simp-collaboration"
%%%

## 模式 1：`field_simp` + `ring`（最常见）
%%%
tag := "ch17-field-simp-plus-ring"
%%%

```anchor fieldSimpThreeFractions
example (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    1/a + 1/b + 1/c = (b*c + a*c + a*b) / (a*b*c) := by
  field_simp
```

## 模式 2：不等式用 rw + 消分母引理
%%%
tag := "field-simp-inequality-rw"
%%%

```anchor fieldSimpInequalities
example (x : ℝ) (hx : 1 < x) : 1 / x < 1 := by
  rw [div_lt_one (by linarith : (0 : ℝ) < x)]
  exact hx

example (x : ℝ) (hx : 0 < x) : x / (x ^ 2 + 1) ≤ 1 := by
  rw [div_le_one (by positivity : (0 : ℝ) < x ^ 2 + 1)]
  nlinarith [sq_nonneg (x - 1)]
```

- *❶* `field_simp` 对不等式支持有限，`rw [div_lt_one h]` 更直接。
- *❷* `positivity` 证明 `x ^ 2 + 1 > 0`，为 `div_le_one` 提供侧条件。

## 模式 3：`push_cast` + `field_simp` + `ring`
%%%
tag := "field-simp-push-cast"
%%%

```anchor fieldSimpCast
example (n : ℕ) (hn : (n : ℝ) ≠ 0) :
    (↑(n + 1) : ℝ) / ↑n = 1 + 1 / ↑n := by
  push_cast; field_simp [hn]
```

# 17.7 调试技巧
%%%
tag := "field-simp-debugging"
%%%

## 技巧 1：用 `field_simp?` 查看使用的引理
%%%
tag := "field-simp-debug-question-mark"
%%%

```
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    1/a + 1/b = (a + b) / (a * b) := by
  field_simp?    -- ▸ 建议：simp only [one_div, ne_eq, ...]; ring
```

## 技巧 2：检查 Infoview 中的剩余目标
%%%
tag := "field-simp-debug-infoview"
%%%

`field_simp` 之后把光标放在下一行，查看剩余目标——
这决定了该用 `ring`（多项式等式）、`linarith`（不等式）还是其他 tactic。

## 技巧 3：显式传入非零条件
%%%
tag := "field-simp-debug-explicit-nonzero"
%%%

```anchor fieldSimpExplicitHyp
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) :
    1 / (a + b) + 1 / a = (2 * a + b) / (a * (a + b)) := by
  field_simp [hab]; ring
```

- *❶* `field_simp` 无法自动推导 `a + b ≠ 0`，用 `[hab]` 显式提供。

# 17.8 `field_simp` vs 手动引理
%%%
tag := "field-simp-vs-manual"
%%%

- 场景：分式等式（通分后比较） —— 推荐方式：`field_simp; ring` —— 原因：自动化，不需手动引理
- 场景：分式不等式 —— 推荐方式：`rw [div_le_iff h]` 等 —— 原因：`field_simp` 对不等式支持有限
- 场景：单个分母消除 —— 推荐方式：`field_simp` 或 `rw [div_eq_iff h]` —— 原因：简单情况手动更精确
- 场景：ℕ / ℤ 上的除法 —— 推荐方式：`omega` / `Nat.div_*` 引理 —— 原因：`field_simp` 不适用
- 场景：嵌套复杂分式 —— 推荐方式：`field_simp; ring` —— 原因：手动几乎不可能

# 17.9 练习
%%%
tag := "field-simp-exercises"
%%%

## 练习 1（基础）：`field_simp` + `ring`
%%%
tag := "field-simp-exercise-1"
%%%

```
-- (a) 通分
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    a / b + b / a = (a ^ 2 + b ^ 2) / (a * b) := by
  sorry

-- (b) 嵌套分式
example (x : ℝ) (hx : x ≠ 0) :
    1 / (1 + 1 / x) = x / (x + 1) := by
  sorry
  -- 提示：可能需要 field_simp [show x + 1 ≠ 0 from ...]
```

*提示*：(a) 直接 `field_simp; ring`。
(b) 需要 `x + 1 ≠ 0` 的假设或证明。

## 练习 2（判断）：`field_simp` 能否成功
%%%
tag := "field-simp-exercise-2"
%%%

判断以下哪些 `field_simp` 能处理（假设非零条件已提供），不能的说明原因：

```
example (x : ℝ) (hx : x ≠ 0) : x / x = 1 := by sorry              -- (a)
example (n : ℕ) (hn : 0 < n) : n / n = 1 := by sorry               -- (b)
example (x : ℝ) (hx : x ≠ 0) : 1/x + 1/x = 2/x := by sorry       -- (c)
example (x : ℝ) (hx : 0 < x) : 1/x > 0 := by sorry                -- (d)
```

*提示*：(a) ✓ 域上的除法；(b) ✗ ℕ 不是域；
(c) ✓ `field_simp; ring`；(d) 部分——`field_simp` 可消分母但剩余不等式需 `linarith`。

## 练习 3（非零条件）：补充假设
%%%
tag := "field-simp-exercise-3"
%%%

```
-- 添加最少的假设使证明成立
example (a b : ℝ) /- 补充假设 -/ :
    1 / a + 1 / b = (a + b) / (a * b) := by
  field_simp
  ring
```

*提示*：需要 `(ha : a ≠ 0) (hb : b ≠ 0)`。
注意 `a * b ≠ 0` 可以从这两个条件自动推导。

## 练习 4（组合 tactic）：分式不等式
%%%
tag := "field-simp-exercise-4"
%%%

```
example (x : ℝ) (hx : 2 ≤ x) : 1 / x ≤ 1 / 2 := by
  sorry
```

*提示*：用 `div_le_div_of_nonneg_left` 或
`rw [div_le_div_iff]` 消分母后用 `linarith`。
注意需要证明 `0 < x` 和 `0 < 2`。

## 练习 5（实战）：复合分式等式
%%%
tag := "field-simp-exercise-5"
%%%

```
example (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    1 / x + 1 / y - 1 / (x + y) =
    (x ^ 2 + x * y + y ^ 2) / (x * y * (x + y)) := by
  sorry
```

*提示*：`field_simp [hxy]; ring`。`hxy` 必须显式传入，
因为 `field_simp` 无法从 `hx` 和 `hy` 推导 `x + y ≠ 0`。

## 练习 6（进阶）：`field_simp` 在假设上
%%%
tag := "field-simp-exercise-6"
%%%

```
example (x : ℝ) (hx : x ≠ 0) (h : 1 / x + x = 5 / 2) :
    2 * x ^ 2 - 5 * x + 2 = 0 := by
  sorry
```

*提示*：先 `field_simp at h` 对假设消分母，
然后 `linarith` 或 `nlinarith` 从化简后的 `h` 得到结论。

# 17.10 小结
%%%
tag := "field-simp-summary"
%%%

- `核心功能`：消除分母，把分式等式化归为多项式等式
- `内部机制`：特化的 `simp`，加载 `div_add_div`、`div_eq_iff` 等分式引理
- `典型流程`：`field_simp` → `ring`（最常见），或 → `linarith` / `nlinarith`
- `非零条件来源`：假设 `x ≠ 0`、推导 `0 < x → x ≠ 0`、数值 `norm_num`、显式传入
- `适用范围`：`Field` / `DivisionRing` 类型（ℚ、ℝ、ℂ），不适用于 ℕ / ℤ
- `主要陷阱`：缺非零条件、复合分母、ring 后接不等式、ℕ 整除混淆
- `协作`：`ring`（多项式）、`positivity`（非零性）、`push_cast`（类型转换）
- `调试`：`field_simp?` 查看引理、检查 Infoview 剩余目标、显式传入 `[h]`

`field_simp` 是代数工具链中的*分母消除专家*——不做多项式推理，
只做"把分式问题化归为无分母问题"。理解其分工边界，
才能与 `ring`、`linarith`、`positivity` 有效组合。
