import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch14Positivity"

#doc (Manual) "第十四章 positivity：符号非负性推理" =>
%%%
file := "Ch14Positivity"
tag := "ch14-positivity"
%%%

*本章目标*：理解 `positivity` 的三值符号追踪与递归分解策略，
掌握内置规则的覆盖范围与插件扩展机制，
识别常见失败模式并学会修复，在不等式证明中高效组合 `positivity`。

数学证明中经常需要确认某个表达式*非负*或*为正*——
`gcongr` 需要 `0 ≤ a` 作为前提，`field_simp` 需要分母 `≠ 0`，
`div_le_div` 需要分母为正。手动拼凑这些事实既繁琐又容易出错。
`positivity` 通过*递归分解表达式结构*，自动完成这类推理。

# 14.1 positivity 解决什么问题
%%%
tag := "positivity-what-it-solves"
%%%

`positivity` 证明形如 `0 ≤ e` 或 `0 < e` 的目标：

```
-- [可运行] 三种典型场景
example (x : ℝ) : 0 ≤ x ^ 2 := by positivity
  -- ▸ 平方非负，直接由 sq_nonneg 得到

example (x : ℝ) (hx : 0 < x) : 0 < x + x ^ 2 := by positivity
  -- ▸ x 为正 + x² 非负 → 和为正

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by positivity
  -- ▸ 两个非负数的乘积非负
```

核心思想：*不是查表，而是递归分解*。把复杂表达式拆成子表达式，
逐个判断符号，再按组合规则得出整体的符号。

# 14.2 三值符号追踪
%%%
tag := "three-value-sign-tracking"
%%%

`positivity` 对每个子表达式返回三种状态之一：

```
Positive  : 0 < e    -- 严格为正
Nonneg    : 0 ≤ e    -- 非负（可以为零）
Nonzero   : e ≠ 0    -- 非零（可正可负，但不为零）
```

为什么需要三种？看这个例子：

```
-- [可运行] Nonzero 在除法中的作用
example (x : ℝ) (hx : x ≠ 0) : 0 < x ^ 2 := by positivity
  -- ▸ x ≠ 0 → x² ≠ 0 → x² > 0（在有序域中，非零的平方为正）
```

如果只跟踪 Positive / Nonneg，`x ≠ 0` 这样的假设就无法利用。
Nonzero 状态使得 `positivity` 能从 `x ≠ 0` 推出 `x ^ 2 > 0`。

## 组合规则
%%%
tag := "combination-rules"
%%%

| 操作 | Pos × Pos | Pos × Nn | Nn × Nn | 备注 |
|------|-----------|----------|---------|------|
| `a + b` | Pos | Pos | Nn | 一侧为正即拉正 |
| `a * b` | Pos | Nn | Nn | 需两侧均正才保正 |

| 一元操作 | 输出 | 条件 |
|---------|------|------|
| `a ^ n`（偶数） | Nn | 无条件 |
| `a ^ n`（奇数） | 保持输入 | 需输入 Nn 或 Pos |
| `\|a\|`、`‖a‖`、`sqrt` | Nn | 无条件 |
| `exp a` | Pos | 无条件 |

# 14.3 递归分解的执行过程
%%%
tag := "recursive-decomposition-process"
%%%

以 `0 ≤ (x ^ 2 + 1) * |y|` 为例，`positivity` 的分解过程：

```
目标: 0 ≤ (x ^ 2 + 1) * |y|

第一层: 乘法 (·) * (·)
├── 左: x ^ 2 + 1
│   第二层: 加法 (·) + (·)
│   ├── 左: x ^ 2
│   │   第三层: 幂 (·) ^ 2                    -- ❶
│   │   └── 偶数幂 → Nonneg (sq_nonneg x)
│   ├── 右: 1
│   │   └── 字面量 1 > 0 → Positive           -- ❷
│   └── Nonneg + Positive → Positive           -- ❸
├── 右: |y|
│   └── 绝对值 → Nonneg (abs_nonneg y)        -- ❹
└── Positive × Nonneg → Nonneg ✅              -- ❺
```

- *❶* 偶数幂 → Nonneg。*❷* 正字面量 → Positive。
- *❸* Nonneg + Positive → Positive。*❹* 绝对值 → Nonneg。
- *❺* Positive × Nonneg → Nonneg，满足 `0 ≤ ...`。

## 假设扫描
%%%
tag := "hypothesis-scanning"
%%%

递归分解前，`positivity` 自动扫描上下文假设：

```
-- [可运行] 假设提供符号信息
example (x y : ℝ) (hx : 0 < x) (hy : 0 ≤ y) : 0 < x * (y + 1) := by positivity
  -- ▸ hx → x Positive; hy → y Nonneg, y+1 Positive; Pos × Pos → Pos
```

识别的假设形式：`0 < x` → Positive，`0 ≤ x` → Nonneg，`x ≠ 0` → Nonzero。

# 14.4 内置规则覆盖范围
%%%
tag := "builtin-rules-coverage"
%%%

`positivity` 内置了数十条规则，覆盖常见数学运算：

## 基本算术
%%%
tag := "basic-arithmetic"
%%%

```
-- [可运行] 加法、乘法、幂
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by positivity
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by positivity
example (a : ℝ) : 0 ≤ a ^ 4 := by positivity      -- ❶ 偶数幂
example (a : ℝ) (ha : 0 ≤ a) : 0 ≤ a ^ 3 := by positivity  -- ❷ 奇数幂需假设
```

- *❶* 偶数幂总是非负，不需要任何假设。
- *❷* 奇数幂保持符号，需要参数非负的假设。

## 分析函数
%%%
tag := "analysis-functions"
%%%

```
-- [可运行] 绝对值、范数、sqrt、exp
example (x : ℝ) : 0 ≤ |x| := by positivity
example (x : ℝ) : 0 ≤ Real.sqrt x := by positivity
example (x : ℝ) : 0 < Real.exp x := by positivity   -- ❶ exp 总是严格正
```

- *❶* `Real.exp` 返回 Positive（不只是 Nonneg），这是正确的数学性质。

## 类型转换与除法
%%%
tag := "type-cast-and-division"
%%%

```
-- [可运行] Nat.cast 保持符号，除法保持符号
example (n : ℕ) : 0 ≤ (n : ℝ) := by positivity
example (x : ℝ) (hx : 0 < x) : 0 < 1 / x := by positivity
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) : 0 ≤ x / y := by positivity
```

## 有限求和
%%%
tag := "finite-sums"
%%%

```
-- [可运行] 每项非负 → 和非负
example (s : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    0 ≤ s.sum f := by positivity
```

# 14.5 插件扩展系统
%%%
tag := "plugin-extension-system"
%%%

`positivity` 通过 `@[positivity]` 属性注册新规则，可为任意函数扩展符号判定：

```
-- [示意] 注册处理 abs 的插件
@[positivity abs _]
def evalAbs : Positivity.PositivityExt where
  eval {u α} _zα _pα e := do
    let .app (.app (.const ``abs _) _) a := e   -- ❶ 模式匹配：e 是 abs a 吗？
      | throwError "not abs"
    return .nonneg (← mkAppM ``abs_nonneg #[a]) -- ❷ 返回 Nonneg + 证明项
```

- *❶* 检查表达式头部是否为 `abs`，不匹配就跳过让其他插件处理。
- *❷* 匹配成功则返回符号状态和证明项（此处引用 `abs_nonneg` 引理）。

## 扩展自定义函数
%%%
tag := "extending-custom-functions"
%%%

```
-- [示意] 为自定义函数注册 positivity 插件
noncomputable def myNorm (x : ℝ) : ℝ := x ^ 2 + 1
lemma myNorm_pos (x : ℝ) : 0 < myNorm x := by unfold myNorm; positivity

@[positivity myNorm _]
def evalMyNorm : Positivity.PositivityExt where
  eval {u α} _zα _pα e := do
    let .app (.const ``myNorm _) a := e | throwError "not myNorm"
    return .positive (← mkAppM ``myNorm_pos #[a])
```

注册后，`positivity` 能自动处理包含 `myNorm` 的表达式。

# 14.6 positivity 的六种失败模式
%%%
tag := "positivity-failure-modes"
%%%

## 失败 1：目标形式不对
%%%
tag := "failure-wrong-goal-form"
%%%

```
-- [会报错] positivity 只接受 0 ≤ e 或 0 < e 形式
example (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : a ≤ b := by positivity
  -- ▸ positivity failed: the goal is not of the form `0 ≤ _` or `0 < _`
  -- ▸ 修复：这不是符号判定问题，用 exact hab 或 linarith
```

`positivity` 不做一般不等式推理——它只回答"这个表达式相对于零的符号是什么"。

## 失败 2：缺少假设 / 奇数幂
%%%
tag := "failure-missing-hypothesis"
%%%

```
-- [会报错] x 的符号未知
example (x : ℝ) : 0 ≤ x := by positivity
  -- ▸ 修复：需要假设 (hx : 0 ≤ x)

-- [会报错] 奇数幂不自动非负（偶数幂 x^2、x^4 无条件非负）
example (x : ℝ) : 0 ≤ x ^ 3 := by positivity
  -- ▸ 修复：添加 (hx : 0 ≤ x)
```

## 失败 4：减法
%%%
tag := "failure-subtraction"
%%%

```
-- [会报错] 减法破坏符号推理
example (a b : ℝ) (ha : 0 ≤ a) : 0 ≤ a - b := by positivity
  -- ▸ 修复：需要 b ≤ a 的假设，或改用 linarith
```

`a ≥ 0` 不保证 `a - b ≥ 0`。`positivity` 需要上下文中有 `0 ≤ a - b` 等直接假设。

## 失败 5：不认识的函数
%%%
tag := "failure-unknown-function"
%%%

```
-- [会报错] 自定义函数没有注册插件
noncomputable def myFunc (x : ℝ) : ℝ := x ^ 2 + 1
example (x : ℝ) : 0 < myFunc x := by positivity
  -- ▸ positivity failed: ...
  -- ▸ 修复：先 unfold myFunc，再 positivity
example (x : ℝ) : 0 < myFunc x := by unfold myFunc; positivity  -- ✓
```

`positivity` 不会自动展开定义。要么先 `unfold`，要么注册 `@[positivity]` 插件。

## 失败 6：表达式可能为零
%%%
tag := "failure-possibly-zero"
%%%

```
-- [会报错] x² 在 x=0 时为零，无法证 ≠ 0
example (x : ℝ) : x ^ 2 ≠ 0 := by positivity
  -- ▸ 修复：需要 (hx : x ≠ 0)
example (x : ℝ) (hx : x ≠ 0) : x ^ 2 ≠ 0 := by positivity  -- ✓
```

# 14.7 与其他 tactic 的协作
%%%
tag := "cooperation-with-other-tactics"
%%%

## 模式 1：为 gcongr 提供侧目标
%%%
tag := "pattern-gcongr-side-goals"
%%%

```
-- [可运行] gcongr 产生的非负性侧目标由 positivity 收尾
example (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  gcongr          -- ❶ 产生侧目标 0 ≤ a
  · positivity    -- ❷ 从 ha 得到 0 ≤ a
```

- *❶* `gcongr` 需要底数非负。*❷* `positivity` 从 `ha` 直接收尾。

## 模式 2：为 `field_simp` 准备分母非零
%%%
tag := "pattern-field-simp-denominator"
%%%

```
-- [可运行] 先证分母为正，再化简
example (x : ℝ) (hx : 0 < x) : x / (x + 1) < 1 := by
  have h : 0 < x + 1 := by positivity    -- ❶ 证明分母为正
  rw [div_lt_one h]                       -- ❷ 利用 h 化简
  linarith                                -- ❸ 线性算术收尾
```

## 选择速查表
%%%
tag := "positivity-selection-table"
%%%

| 场景 | 推荐 tactic | 原因 |
|------|-------------|------|
| `0 ≤ e` 或 `0 < e`，结构化表达式 | `positivity` | 递归分解，利用代数结构 |
| `0 ≤ e` 或 `0 < e`，纯数值 | `norm_num` | 直接计算 |
| `a ≤ b` 一般不等式 | `linarith` / `gcongr` | 线性推理或单调性 |
| 分母 `≠ 0` | `positivity`（若可推出为正） | `0 < e → e ≠ 0` |
| 乘积 / 除法符号 | `positivity` | 组合规则直接适用 |

```
-- [可运行] positivity vs nlinarith
example (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x ^ 2 + x := by positivity
  -- ▸ 递归分解：x² Nonneg, x Nonneg → 和 Nonneg
example (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x ^ 2 + x := by nlinarith [sq_nonneg x]
  -- ▸ nlinarith 也行，但需要手动提供 sq_nonneg 提示

-- [可运行] positivity 做不到，linarith 可以
example (a b : ℝ) (ha : 0 ≤ a) (hb : a ≤ b) : 0 ≤ b := by linarith
  -- ▸ 一般不等式推理，不是符号分析
```

# 14.8 调试技巧
%%%
tag := "positivity-debugging-tips"
%%%

## 技巧 1：用 positivity? 查看证明项
%%%
tag := "tip-positivity-question-mark"
%%%

```
-- [可运行] positivity? 展示内部推理
example (x : ℝ) (hx : 0 < x) : 0 < x + 1 := by positivity?
  -- ▸ 建议：exact add_pos hx one_pos
```

`positivity?` 输出具体的证明项，可用于理解推理过程或替换为显式证明。

## 技巧 2：逐步分解定位失败
%%%
tag := "tip-stepwise-decomposition"
%%%

```
-- [示意] 定位失败位置
example (x : ℝ) (hx : 0 < x) : 0 < (x - 1) * x := by
  -- positivity 失败——哪个子表达式有问题？
  -- have h1 : 0 < x := hx           -- ✓ x 为正
  -- have h2 : 0 < x - 1 := ???      -- ✗ x-1 可能为负！
  -- 原因：x > 0 不保证 x - 1 > 0
  sorry
```

## 技巧 3：添加中间假设
%%%
tag := "tip-add-intermediate-hypotheses"
%%%

```
-- [可运行] 补充 positivity 需要的假设
example (x : ℝ) (hx : 1 < x) : 0 < (x - 1) * x := by
  have h1 : 0 < x - 1 := by linarith   -- ❶ 补充关键事实
  have h2 : 0 < x := by linarith        -- ❷ 补充关键事实
  positivity                              -- ❸ 现在 positivity 成功
```

- *❶❷* 用 `linarith` 建立中间事实，让 `positivity` 能从上下文读取符号信息。

# 14.9 练习
%%%
tag := "ch14-exercises"
%%%

## 练习 1（基础）：判断 positivity 能否成功
%%%
tag := "exercise-14-1"
%%%

判断以下哪些能被 `positivity` 证明，不能的说明原因：

```
example (x : ℝ) : 0 ≤ x ^ 2 := by sorry                    -- (a)
example (x : ℝ) : 0 ≤ x := by sorry                         -- (b)
example (x : ℝ) : 0 < Real.exp x := by sorry                -- (c)
example (a b : ℝ) (ha : 0 ≤ a) : 0 ≤ a - b := by sorry     -- (d)
example (x : ℝ) (hx : x ≠ 0) : 0 < |x| := by sorry         -- (e)
```

*提示*：(a) 偶数幂无条件非负 ✓；(b) 缺假设 ✗；(c) exp 总为正 ✓；
(d) 减法需要更多信息 ✗；(e) 非零的绝对值为正 ✓。

## 练习 2（组合推理）：多步符号分析
%%%
tag := "exercise-14-2"
%%%

```
example (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) : 0 < a ^ 2 + a * b + 1 := by
  sorry
```

*提示*：`positivity` 直接可用——a² Positive, a\*b Nonneg, 1 Positive。

## 练习 3（修复失败）：补充假设让 positivity 成功
%%%
tag := "exercise-14-3"
%%%

```
-- 添加最弱的假设使 positivity 成功
example (x y : ℝ) /- 补充假设 -/ : 0 < x * y := by positivity
```

*提示*：需要 `(hx : 0 < x) (hy : 0 < y)` 或 `(hx : x < 0) (hy : y < 0)`。
`positivity` 只处理第一种（两个 Positive 的乘积）。

## 练习 4（unfold 技巧）：处理自定义函数
%%%
tag := "exercise-14-4"
%%%

```
noncomputable def energy (v : ℝ) (m : ℝ) : ℝ := m * v ^ 2 / 2

example (v : ℝ) (m : ℝ) (hm : 0 < m) : 0 ≤ energy v m := by
  sorry
```

*提示*：先 `unfold energy`，再 `positivity`。

## 练习 5（实战）：为 gcongr 提供侧目标
%%%
tag := "exercise-14-5"
%%%

```
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≤ y) :
    x ^ 3 ≤ y ^ 3 := by
  sorry
```

*提示*：`gcongr` 会产生 `0 ≤ x` 等侧目标，用 `positivity` 或 `assumption` 收尾。

## 练习 6（进阶）：分段证明
%%%
tag := "exercise-14-6"
%%%

```
example (x : ℝ) (hx : 2 ≤ x) : 0 < x ^ 2 - x := by
  sorry
```

*提示*：`positivity` 直接失败（减法）。用 `have : 0 < x * (x - 1) := by ...`
建立中间事实，或用 `nlinarith`。

# 14.10 小结
%%%
tag := "ch14-summary"
%%%

| 概念 | 关键点 |
|------|--------|
| 目标形式 | 只处理 `0 ≤ e` 或 `0 < e`，不做一般不等式推理 |
| 三值追踪 | Positive / Nonneg / Nonzero，组合规则覆盖 +、×、^、\|·\|、exp 等 |
| 递归分解 | 自底向上分析表达式结构，逐层组合符号状态 |
| 假设利用 | 自动扫描上下文中 `0 < x`、`0 ≤ x`、`x ≠ 0` 形式的假设 |
| 插件系统 | `@[positivity head]` 注册，可为自定义函数扩展 |
| 主要陷阱 | 减法、奇数幂无假设、自定义函数未展开 |
| 协作模式 | 为 `gcongr` / `field_simp` / `div_le_div` 提供非负性前提 |
| 调试 | `positivity?` 查看证明项，逐步分解定位失败子表达式 |

`positivity` 是不等式工具链中的*符号判定专家*——不解不等式，只回答符号。
理解其能力边界，才能与 `linarith`、`gcongr`、`nlinarith` 有效组合。
