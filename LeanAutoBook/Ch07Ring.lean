import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch07Ring"

#doc (Manual) "第七章 ring 和 `ring_nf`：代数范式化" =>
%%%
file := "Ch07Ring"
tag := "ch07-ring"
%%%

*本章目标*：理解 `ring` 的决策过程，掌握 `ring_nf` 的化简用法，学会诊断常见失败模式。

# ring 解决什么问题
%%%
tag := "ring-what-it-solves"
%%%

`ring` 证明*交换（半）环*上的多项式恒等式。它是一个*完备决策过程*：
对于交换环公理可推出的任何多项式等式，`ring` 一定能判定。

```
-- 基础展开
example (x y : ℤ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring
  -- ✅ ring 把两边规范化为同一个 Horner 范式，得到 rfl

-- 因式分解方向同样成立
example (a b : ℝ) : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by
  ring
  -- ✅ 方向无关：ring 总是规范化到唯一范式再比较

-- 多变量高次
example (a b c : ℚ) :
    (a + b + c) ^ 3 =
      a ^ 3 + b ^ 3 + c ^ 3 +
      3 * (a ^ 2 * b + a ^ 2 * c + b ^ 2 * a + b ^ 2 * c + c ^ 2 * a + c ^ 2 * b) +
      6 * a * b * c := by
  ring
  -- ✅ 变量数和次数不影响正确性，只影响性能
```

`ring` 的三条核心边界：

1. *不处理序*——`ring` 不能证明 `x + 1 > x`，那是 `linarith` / `positivity` 的领域
2. *不展开函数*——`ring` 把 `sin x`、`f n` 等当作不透明原子
3. *不处理除法*——`x / y * y = x` 需要 `y ≠ 0`，超出环公理

# 内部原理：Horner 范式
%%%
tag := "horner-normal-form"
%%%

## 什么是 Horner 范式
%%%
tag := "what-is-horner-nf"
%%%

多项式 $`a_0 + a_1 x + a_2 x^2 + \cdots + a_n x^n` 的 Horner 形式是：

$`a_0 + x \cdot (a_1 + x \cdot (a_2 + \cdots + x \cdot a_n))`

这种嵌套表示有两个优势：

- *唯一性*——同一个多项式只有一种 Horner 范式（在固定变量序下）
- *高效求值*——只需 $`n` 次乘法 + $`n` 次加法，不需要幂运算

## ring 的证明策略
%%%
tag := "ring-proof-strategy"
%%%

`ring` 的工作分为三步：

```
            规范化                    比较                    规范化
LHS ────────────→ nf_lhs ═══════════════════ nf_rhs ←──────────── RHS
    proof₁: LHS = nf_lhs    nf_lhs ≡ nf_rhs    proof₂: RHS = nf_rhs
                              (结构相等)
```

1. 对 LHS 递归应用环公理（结合律、交换律、分配律），产生 `proof₁ : LHS = nf_lhs`
2. 对 RHS 做同样处理，产生 `proof₂ : RHS = nf_rhs`
3. 检查 `nf_lhs` 与 `nf_rhs` 是否结构相同（`rfl`）
4. 若相同，组合得到 `LHS = RHS`；若不同，报错

关键点：第 3 步是*纯粹的语法比较*——不需要搜索或回溯。
与搜索型 tactic 不同，`ring` 没有回溯搜索空间，因此不会因搜索爆炸而超时。
但规范化本身产生的项数可能随变量数和次数急剧增长（见 7.8），所以高次多变量场景下 `ring` 依然可能很慢。

## 多变量情形
%%%
tag := "multivariate-case"
%%%

对于多变量多项式，`ring` 选定一个变量序（通常按出现顺序），
然后递归地把系数本身视为"内层"多项式。例如 $`2xy + 3x + y` 以 $`x` 为主变量时：

$`x \cdot (2y + 3) + y`

内层系数 $`2y + 3` 和 $`y` 再以 $`y` 为主变量做 Horner 规范化。

# `ring_nf`：只做范式化
%%%
tag := "ring-nf-normalization-only"
%%%

`ring_nf` 执行与 `ring` 相同的规范化过程，但*不要求两边相等*。
它把目标（或假设）中的代数子表达式化简为 Horner 范式。

## 化简目标
%%%
tag := "ring-nf-simplify-goal"
%%%

```
example (x : ℤ) : (x + 1) ^ 2 - 1 = x ^ 2 + 2 * x := by
  ring_nf
  -- ring_nf 把两边分别化简为范式
  -- 如果化简后两边相同，目标自动关闭
  -- 如果不同，留下化简后的目标供后续 tactic 处理
```

## 化简假设
%%%
tag := "ring-nf-simplify-hypothesis"
%%%

```
example (x : ℤ) (h : (x + 1) ^ 2 = 9) : x ^ 2 + 2 * x = 8 := by
  ring_nf at h
  -- h 从 (x + 1) ^ 2 = 9 变为 x ^ 2 + 2 * x + 1 = 9
  linarith
  -- ⊢ x ^ 2 + 2 * x = 8，由 h 和 linarith 解决
```

## `ring_nf` 与 ring 的选择
%%%
tag := "ring-nf-vs-ring"
%%%

- `证明 `LHS = RHS`，两边都是多项式`：`ring`
- `化简后交给其他 tactic`：`ring_nf` 然后接后续 tactic
- `化简假设中的代数表达式`：`ring_nf at h`
- `只想看化简结果（探索性）`：`ring_nf`

经验法则：如果你认为等式纯粹是代数恒等式，先用 `ring`。
如果 `ring` 失败，再考虑 `ring_nf` + 其他 tactic 的组合。

# 支持的代数结构
%%%
tag := "supported-algebraic-structures"
%%%

## 结构总览
%%%
tag := "structure-overview"
%%%

- 结构：交换环 `CommRing` —— 典型类型：`ℤ`, `ℚ`, `ℝ`, `ℂ`, `ZMod n` —— 注意事项：完整支持
- 结构：交换半环 `CommSemiring` —— 典型类型：`ℕ` —— 注意事项：减法受限（见 7.5）
- 结构：交换代数 —— 典型类型：`R[X]`（多项式环） —— 注意事项：系数环需是 `CommRing`
- 结构：域 `Field` —— 典型类型：`ℚ`, `ℝ`, `ℂ` —— 注意事项：不处理除法（用 `field_simp` + `ring`）

## ℕ 上的减法陷阱
%%%
tag := "nat-subtraction-trap"
%%%

自然数上的减法是截断减法（`a - b = 0` 当 `a ≤ b`），不满足环公理。
`ring` 可以处理 `ℕ` 上的加法和乘法，但涉及减法时经常失败：

```
-- ✅ 没有减法，ring 正常工作
example (n : ℕ) : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring

-- ❌ 有减法，ring 可能失败
-- example (n : ℕ) : (n + 1) - 1 = n := by ring  -- fails
-- 正确做法：用 omega
example (n : ℕ) : (n + 1) - 1 = n := by omega
```

*实践规则*：在 `ℕ` 上，只要目标含有减法，就不要首先想到 `ring`——优先考虑 `omega` 或先转换到 `ℤ`。

## 不支持的结构
%%%
tag := "unsupported-structures"
%%%

- *非交换环*（如矩阵环）——用 `noncomm_ring`
- *除法环上的除法*——用 `field_simp` 先消除分母，再用 `ring`

```
-- field_simp + ring 的经典组合
example (x : ℝ) (hx : x ≠ 0) : (x ^ 2 - 1) / x = x - 1 / x := by
  field_simp
  -- ⊢ x ^ 2 - 1 = x * x - 1（消除分母后）
  ring
```

# 常见失败模式与诊断
%%%
tag := "common-failures-and-diagnostics"
%%%

## 目标不是等式
%%%
tag := "goal-not-equality"
%%%

```
-- ❌ ring 只能证明等式，不能证明不等式
-- example (x : ℤ) : x ^ 2 ≥ 0 := by ring
-- 错误信息：ring failed, ring expressions not equal
-- 修复：用 nlinarith 或 positivity
example (x : ℤ) : x ^ 2 ≥ 0 := by positivity
```

`ring` 的错误信息 `ring expressions not equal` 可能误导：
它并不意味着等式不成立，只是说 `ring` 的规范化后两边不同。
对于不等式，`ring` 的规范化根本不适用。

## 等式依赖假设
%%%
tag := "equality-depends-on-hypothesis"
%%%

```
-- ❌ ring 不使用任何假设
-- example (x y : ℤ) (h : x = y) : x ^ 2 = y ^ 2 := by ring
-- ring 看不到 h，只看到 x ^ 2 和 y ^ 2 是不同的范式
-- 修复方案 1：先 subst
example (x y : ℤ) (h : x = y) : x ^ 2 = y ^ 2 := by subst h; ring
-- 修复方案 2：用 linear_combination
example (x y : ℤ) (h : x = y) : x ^ 2 = y ^ 2 := by
  linear_combination (x + y) * h
  -- 思路：用假设 h 乘以 (x + y)，生成一个可供 ring 验证的新恒等式
  -- linear_combination 把目标变成 x^2 - y^2 - (x+y)*(x-y) = 0
  -- 然后用 ring 验证
```

## 含有不透明函数
%%%
tag := "opaque-functions"
%%%

```
-- ❌ ring 不展开 abs
-- example (x : ℤ) : |x| ^ 2 = x ^ 2 := by ring
-- ring 把 |x| 当作原子 a，看到 a^2 ≠ x^2
-- 修复：需要分情况讨论或用专门引理
example (x : ℤ) : |x| ^ 2 = x ^ 2 := sq_abs x
```

## 类型不匹配
%%%
tag := "type-mismatch"
%%%

```
-- ❌ 混合 ℕ 和 ℤ
-- example (n : ℕ) : (n : ℤ) + 1 = ↑n + 1 := by ring
-- 有时 coercion 会导致 ring 看到不同的表达式
-- 修复：用 push_cast 统一类型后再 ring
example (n : ℕ) : (↑(n + 1) : ℤ) = ↑n + 1 := by push_cast; ring
```

## 诊断流程图
%%%
tag := "diagnostic-flowchart"
%%%

当 `ring` 失败时，按以下顺序检查：

```
ring 失败
  │
  ├─ 目标是不等式？ ──→ 用 linarith / nlinarith / positivity
  │
  ├─ 等式依赖假设？ ──→ 用 linear_combination / subst / rw 先处理
  │
  ├─ 含有函数调用？ ──→ 用 simp 先展开，或手动 rw 相关引理
  │
  ├─ ℕ 上有减法？   ──→ 用 omega 或转换到 ℤ
  │
  ├─ 含有除法？     ──→ 用 field_simp 先消分母
  │
  └─ 类型 coercion？ ──→ 用 push_cast / pull_cast 统一类型
```

# 与 ring 相关的 tactic
%%%
tag := "related-tactics"
%%%

## `linear_combination`
%%%
tag := "linear-combination"
%%%

`linear_combination` 是 `ring` 最重要的搭档。
给定等式假设 $`h_1, \ldots, h_k`，找到系数使目标成为这些假设的线性组合 + `ring` 恒等式：

```
example (a b : ℤ) (h1 : a + b = 5) (h2 : a - b = 1) : a = 3 := by
  linear_combination (h1 + h2) / 2
  -- 内部步骤：把目标改写为 LHS - RHS - (展开) = 0，用 ring 验证
```

## `field_simp` + ring
%%%
tag := "field-simp-plus-ring"
%%%

处理含分式的等式：先用 `field_simp` 消分母，再用 `ring`：

```
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a + 1 / b = (a + b) / (a * b) := by
  field_simp; ring
```

## `push_cast` + ring
%%%
tag := "push-cast-plus-ring"
%%%

类型转换（`ℕ → ℤ` 等）会阻碍 `ring`。`push_cast` 把 cast 推到最内层：

```
example (m n : ℕ) : ((m + n : ℕ) : ℤ) = (m : ℤ) + (n : ℤ) := by
  push_cast; ring
```

# 在元编程中调用 ring
%%%
tag := "metaprogramming-ring"
%%%

## 通过 evalTactic
%%%
tag := "via-eval-tactic"
%%%

```
import Mathlib.Tactic.Ring

elab "try_ring" : tactic => do
  try
    Lean.Elab.Tactic.evalTactic (← `(tactic| ring))
    --                           ^^^^^^^^^^^^^^^^
    --  syntax quotation：构造 `ring` 的 Syntax 对象
  catch _ =>
    Lean.logInfo "ring failed, skipping"
```

## 底层 API
%%%
tag := "low-level-api"
%%%

```
open Lean Elab Tactic in
elab "ring_diagnose" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let some (_, _, lhs, rhs) := target.eq?
    --  eq? 返回 (level, type, lhs, rhs)；非等式返回 none
- throwError "ring_diagnose: goal is not an equality"
  logInfo m!"LHS: {lhs}"
  logInfo m!"RHS: {rhs}"
  try
    evalTactic (← `(tactic| ring))
    logInfo "ring succeeded!"
  catch e =>
    logInfo m!"ring failed: {e.toMessageData}"
```

# 性能考量
%%%
tag := "performance-considerations"
%%%

`ring` 的复杂度与表达式大小多项式相关，但高次幂会导致项数爆炸：

```
-- ✅ 快速：变量少、次数低
example (x : ℤ) : (x + 1) ^ 4 = x ^ 4 + 4 * x ^ 3 + 6 * x ^ 2 + 4 * x + 1 := by
  ring

-- ⚠️ 较慢：(a + b + c + d + e) ^ 10 可能需要数秒
```

性能提示：太慢时先手动化简子表达式，或拆分证明步骤。

# 练习
%%%
tag := "ch07-exercises"
%%%

## 练习 7.1：基础展开（⭐）
%%%
tag := "exercise-7-1"
%%%

证明以下等式：

```
-- (a) 立方和公式
example (a b : ℤ) :
    a ^ 3 + b ^ 3 = (a + b) * (a ^ 2 - a * b + b ^ 2) := by
  sorry

-- (b) 完全立方展开
example (x y : ℤ) :
    (x - y) ^ 3 = x ^ 3 - 3 * x ^ 2 * y + 3 * x * y ^ 2 - y ^ 3 := by
  sorry
```

## 练习 7.2：`ring_nf` 化简（⭐）
%%%
tag := "exercise-7-2"
%%%

使用 `ring_nf` 化简假设后完成证明：

```
-- 提示：ring_nf at h 化简假设，然后用 linarith
example (x : ℤ) (h : (x + 2) ^ 2 = (x + 1) ^ 2 + 5) : x = 1 := by
  sorry
```

## 练习 7.3：`linear_combination`（⭐⭐）
%%%
tag := "exercise-7-3"
%%%

使用 `linear_combination` 完成以下证明。关键是找到正确的系数：

```
-- (a)
example (a b : ℤ) (h1 : a + b = 10) (h2 : a - b = 4) : a = 7 := by
  sorry
  -- 提示：h1 和 h2 应该以什么系数组合？

-- (b)
example (x y : ℤ) (h1 : x + y = 5) (h2 : x * y = 6) :
    x ^ 2 + y ^ 2 = 13 := by
  sorry
  -- 提示：x^2 + y^2 = (x+y)^2 - 2*x*y
```

## 练习 7.4：`field_simp` + ring（⭐⭐）
%%%
tag := "exercise-7-4"
%%%

消分母后用 `ring` 完成：

```
example (x : ℝ) (hx : x ≠ 0) :
    (x + 1 / x) ^ 2 = x ^ 2 + 2 + 1 / x ^ 2 := by
  sorry
  -- 提示：field_simp 然后 ring
```

## 练习 7.5：诊断失败（⭐⭐）
%%%
tag := "exercise-7-5"
%%%

以下 `ring` 调用都会失败。为每个找出失败原因并给出正确证明：

```
-- (a) 为什么失败？用什么替代？
-- example (n : ℕ) : n * (n + 1) / 2 + (n + 1) = (n + 1) * (n + 2) / 2 := by ring

-- (b) 为什么失败？用什么替代？
-- example (x : ℤ) (h : x > 0) : x ^ 2 > 0 := by ring

-- (c) 为什么失败？用什么替代？
-- example (x y : ℤ) (h : x = y + 1) : x ^ 2 = y ^ 2 + 2 * y + 1 := by ring
```

## 练习 7.6：组合 tactic（⭐⭐⭐）
%%%
tag := "exercise-7-6"
%%%

综合运用本章所学完成证明：

```
-- 提示：可能需要 push_cast, ring_nf, linarith 等多个 tactic 的组合
example (n : ℕ) : (2 * n + 1) ^ 2 - 1 = 4 * n * (n + 1) := by
  sorry
  -- 注意：这里是 ℕ 上的减法！
```

# 小结
%%%
tag := "ch07-summary"
%%%

- `ring` 原理：规范化为 Horner 范式，做纯语法比较
- `适用范围`：交换（半）环上的多项式恒等式
- `ring_nf`：只做范式化，不要求相等；可作用于假设
- `linear_combination`：利用等式假设 + `ring` 证明依赖假设的等式
- `field_simp` + `ring`：先消分母再证多项式等式
- `push_cast` + `ring`：先统一类型转换再证等式
- `常见失败`：不等式、假设依赖、函数不透明、ℕ 减法、除法、类型转换

下一章：`omega`——线性整数/自然数算术的完备决策过程。
