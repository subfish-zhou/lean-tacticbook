import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch08Omega"

#doc (Manual) "第八章 omega：Presburger 算术决策过程" =>
%%%
file := "Ch08Omega"
tag := "ch08-omega"
%%%

*本章目标*：理解 `omega` 的理论基础、能力边界和常见失败模式，
学会在 tactic 编程中正确使用它。

# 8.1 omega 解决什么问题
%%%
tag := "omega-what-it-solves"
%%%

`omega` 是 Lean 4 内置的 *Presburger 算术* 决策过程。
它能自动证明关于 `ℕ` 和 `ℤ` 的*线性算术*命题——
即只涉及加法、常数乘法和比较的等式与不等式。

```
-- 基本不等式
example (n : ℕ) : n + 1 > n := by
  omega                          -- ⊢ n + 1 > n，线性，直接判定

-- 整数线性约束
example (a b : ℤ) (h : a < b) : a + 1 ≤ b := by
  omega                          -- 从 h : a < b 推出 a + 1 ≤ b

-- 多变量线性组合
example (x y : ℕ) (h1 : x ≤ 10) (h2 : y ≤ 10) : x + y ≤ 20 := by
  omega                          -- 把 h1, h2 收集为线性约束系统
```

"Presburger 算术" 是整数上只允许加法和比较（不允许变量间乘法）的一阶理论。
Presburger 在 1929 年证明了该理论的*可判定性*，
意味着存在算法能判定任意 Presburger 公式的真假。
`omega` tactic 实现的正是这样一个决策过程。

# 8.2 理论基础：Omega 算法
%%%
tag := "omega-theory"
%%%

Lean 4 使用的 omega 算法基于 Pugh (1991)。
核心思路：把目标和假设归约为整数线性不等式系统，
通过*变量消去*判定系统是否有解。

## 变量消去
%%%
tag := "variable-elimination"
%%%

给定不等式系统 `{aᵢ x + bᵢ y + ⋯ ≤ cᵢ}`，算法逐步消去变量：

1. *选择变量* x
2. *分离约束*：找到所有关于 x 的下界 `ℓⱼ ≤ x` 和上界 `x ≤ uₖ`
3. *组合*：对每对 `(ℓⱼ, uₖ)`，生成新约束 `ℓⱼ ≤ uₖ`
4. *整数修正*：对整数情形，添加 "dark shadow" 约束以保证精确性
5. *递归*：对消去后的系统重复以上步骤

当所有变量被消去后，系统退化为常数不等式。
如果出现矛盾（如 $0 \leq -1$），则原系统无整数解——目标得证。

## 与 Fourier-Motzkin 消去的区别
%%%
tag := "fourier-motzkin-difference"
%%%

Fourier-Motzkin 消去适用于*实数*，只做步骤 1-3。
omega 算法额外处理*整数约束*（步骤 4），
因为实数解存在不意味着整数解存在：

```
-- x + y = 1, x + y = 2 在实数上无解，整数上也无解
-- 但 2x = 3 在实数上有解 x = 1.5，整数上无解
example : ¬ ∃ x : ℤ, 2 * x = 3 := by
  omega                          -- omega 知道 2x = 3 无整数解
```

## Lean 中的执行流程
%%%
tag := "lean-execution-flow"
%%%

1. *收集*：从 `LocalContext` 自动提取所有线性算术假设
2. *规范化*：统一到 ℤ 域，处理 Nat.sub，化为标准形 $a_1 x_1 + \cdots \leq c$
3. *判定*：运行 omega 算法
4. *输出*：矛盾 → 构造证明项关闭目标；有解 → 报错并给出反例

# 8.3 omega 的能力范围
%%%
tag := "omega-capabilities"
%%%

## 能处理的命题
%%%
tag := "omega-can-handle"
%%%

```
-- [1] 线性等式与不等式
example (a b c : ℤ) (h : a + b ≤ c) : a ≤ c - b := by
  omega                          -- 线性重排

-- [2] 常数系数乘法（不是变量乘变量）
example (x : ℤ) (h : 3 * x ≤ 9) : x ≤ 3 := by
  omega                          -- 3 * x 中 3 是常数，OK

-- [3] 整除与模运算
example (n : ℤ) (h : n % 2 = 0) : ∃ k, n = 2 * k := by
  omega                          -- omega 理解 % 的语义

-- [4] 析取（通过分支搜索）
example (n : ℕ) : n % 2 = 0 ∨ n % 2 = 1 := by
  omega                          -- 穷举 n mod 2 的可能值

-- [5] Nat 的截断减法
example (n : ℕ) : n - n = 0 := by
  omega                          -- 知道 Nat.sub 截断到 0

-- [6] max / min
example (a b : ℕ) : max a b ≥ a := by
  omega                          -- omega 展开 max 的定义
```

## 不能处理的命题
%%%
tag := "omega-cannot-handle"
%%%

```
-- [1] 变量乘法（非线性）
-- example (x y : ℤ) (h : x * y = 0) : x = 0 ∨ y = 0 := by omega
-- ✗ omega 不处理 x * y（两个变量相乘）

-- [2] 指数 / 幂运算
-- example (n : ℕ) : 2 ^ n ≥ 1 := by omega
-- ✗ 2 ^ n 不是线性的，需要归纳法

-- [3] 实数或其他域
-- example (x : ℝ) : x + 1 > x := by omega
-- ✗ omega 只处理 ℕ 和 ℤ

-- [4] 带量词交替的复杂公式
-- ∀ x, ∃ y, P(x, y) 形式的嵌套量词超出处理范围
```

# 8.4 Nat.sub 的特殊处理
%%%
tag := "nat-sub-handling"
%%%

自然数减法是截断的：`a - b = 0` 当 `a < b`。
这让 `ℕ` 上的推理比 `ℤ` 复杂，但 `omega` 内置了对此的处理。

## 转换策略
%%%
tag := "nat-sub-conversion"
%%%

omega 把 `ℕ` 表达式翻译到 `ℤ` 时，遵循以下规则：

| ℕ 表达式 | ℤ 翻译 | 附加约束 |
|----------|--------|----------|
| `(n : ℕ)` | `n` | `n ≥ 0` |
| `a - b` (Nat) | `max(a - b, 0)` | — |
| `a / k` (Nat) | 整数除法 | `0 ≤ a / k` |
| `a % k` (Nat) | `a - k * (a / k)` | `0 ≤ a % k < k` |

## 示例
%%%
tag := "nat-sub-examples"
%%%

```
-- 截断减法的典型场景
example (n m : ℕ) (h : m ≤ n) : n - m + m = n := by
  omega                          -- h : m ≤ n 保证不截断

example (n : ℕ) (h : n ≥ 1) : n - 1 + 1 = n := by
  omega                          -- h 保证 n - 1 不截断

-- omega 知道截断的全部语义
example (n : ℕ) : n - (n + 1) = 0 := by
  omega                          -- n < n + 1，截断到 0

-- 不需要前置条件也能处理
example (a b : ℕ) : a - b ≤ a := by
  omega                          -- 无论是否截断都成立
```

# 8.5 常见失败模式
%%%
tag := "common-failure-modes"
%%%

理解 omega 何时会失败，以及*为什么*失败，是高效使用它的关键。

## 失败模式 1：非线性项
%%%
tag := "failure-nonlinear"
%%%

```
-- omega 拒绝包含变量乘法的目标
example (n : ℕ) (h : n * n = 4) : n = 2 := by
  omega  -- ✗ omega does not handle multiplication of variables
         -- 修复：nlinarith 或 interval_cases + omega
```

*诊断*：错误信息通常包含 "omega does not handle" 或
"could not prove"。检查目标和假设中是否有变量间相乘的项。

## 失败模式 2：目标中有不支持的类型
%%%
tag := "failure-unsupported-type"
%%%

```
-- omega 只支持 ℕ 和 ℤ
example (x : Fin 5) (h : x.val < 3) : x.val + 2 < 5 := by
  omega  -- ✓ x.val : ℕ，omega 可以处理
         -- 但如果目标直接涉及 Fin 的运算（取模），可能失败
```

*诊断*：如果 omega 报错说无法处理某个表达式，
检查是否需要先用 `simp` 或手动 `show` 把类型转换为 ℕ/ℤ。

## 失败模式 3：假设不足
%%%
tag := "failure-insufficient-hypotheses"
%%%

```
-- omega 只使用上下文中已有的假设
example (n : ℕ) : n - 1 + 1 = n := by
  omega  -- ✗ 需要 n ≥ 1 但上下文中没有
         -- omega 会给出反例：n = 0
```

*诊断*：omega 的报错通常会给出反例。
检查反例是否暴露了缺失的前置条件。

## 失败模式 4：隐藏在定义背后的线性关系
%%%
tag := "failure-hidden-definition"
%%%

```
def myDouble (n : ℕ) := 2 * n

-- omega 不会展开自定义定义
example (n : ℕ) : myDouble n ≥ n := by
  omega  -- ✗ omega 看到的是 myDouble n，不知道它等于 2 * n
         -- 修复：先 unfold myDouble，再 omega
```

*诊断*：如果目标"看起来"是线性的但 omega 失败，
检查是否有未展开的定义。用 `unfold` 或 `simp only [myDouble]` 先展开。

## 失败模式 5：变量太多导致超时
%%%
tag := "failure-too-many-variables"
%%%

omega 算法的复杂度随变量数指数增长。
虽然实际中很少触发，但当假设中包含大量不相关变量时，
omega 可能显著变慢。

```
-- 如果上下文有 20+ 个线性假设，omega 可能变慢
-- 修复：在调用前用 clear 清除不相关假设
example (a b c d e f : ℕ)
    (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d)
    (h4 : d ≤ e) (h5 : e ≤ f) : a ≤ f := by
  omega                          -- 变量不多，正常工作
```

# 8.6 在 tactic 编程中使用 omega
%%%
tag := "omega-in-tactic-programming"
%%%

## 直接调用
%%%
tag := "omega-direct-call"
%%%

```
-- 在 tactic block 中调用
evalTactic (← `(tactic| omega))
```

这是最简单的方式：生成 `omega` 的 syntax 对象，然后执行它。
如果 omega 无法关闭目标，`evalTactic` 会抛出异常。

## 探测性调用
%%%
tag := "omega-probing-call"
%%%

有时你想*尝试* omega 但不希望失败中断流程：

```
-- 尝试用 omega 关闭目标，失败则返回 false
def tryOmega (goal : MVarId) : MetaM Bool := do
  try
    let (remaining, _) ←              -- remaining : 剩余子目标列表
      Lean.Elab.runTactic goal         -- 在 goal 上运行 tactic
        (← `(tactic| omega))
    return remaining.isEmpty           -- 全部关闭则返回 true
  catch _ =>
    return false                       -- omega 失败，静默返回 false
```

## 与其他 tactic 组合
%%%
tag := "omega-combining-tactics"
%%%

omega 经常作为 "收尾" tactic 出现在组合策略中：

```
-- 先简化，再尝试 omega
macro "simp_omega" : tactic =>
  `(tactic| (simp <;> try omega))

-- 在 decide 策略中作为后备
macro "auto_arith" : tactic =>
  `(tactic| first | omega | norm_num | simp [Nat.add_comm])
```

## 在 discharger 中使用
%%%
tag := "omega-as-discharger"
%%%

许多 tactic 接受 discharger 参数来关闭 side goal。
omega 是线性算术 side goal 的理想 discharger：

```
-- simp 产生的算术 side goal 由 omega 关闭
example (xs : List ℕ) (h : xs.length > 2) :
    xs.length - 1 > 0 := by
  simp (config := { decide := false }) at *
  omega                          -- 关闭 simp 留下的算术目标
```

# 8.7 omega 与其他算术 tactic 的对比
%%%
tag := "omega-vs-other-tactics"
%%%

| tactic | 理论域 | 强项 | 弱项 |
|--------|--------|------|------|
| `omega` | ℕ, ℤ（线性） | 整除、模运算、Nat.sub | 非线性、实数 |
| `linarith` | 任意 ordered field | 实数线性、可扩展 | 不懂整除、不处理 Nat.sub |
| `nlinarith` | 同上 + 非线性提示 | 非线性（带 hint） | 需要手动提供非线性项 |
| `norm_num` | 具体数值 | 计算确定值 | 不处理变量 |
| `decide` | Decidable 实例 | 有限类型穷举 | 无限类型 |
| `ring` | 交换环 | 多项式等式 | 不等式 |

*选择原则*：ℕ/ℤ 线性 → `omega`；实数线性 → `linarith`；
非线性 → `nlinarith`；纯数值 → `norm_num`；多项式等式 → `ring`。

## 组合示例
%%%
tag := "combination-examples"
%%%

```
-- 非线性目标，omega 不行，用 nlinarith
example (n : ℕ) (h : n ≥ 2) : n * n ≥ 4 := by
  nlinarith [sq_nonneg (n - 2)]

-- omega 处理模运算（linarith 做不到）
example (a b : ℤ) (h : a % 2 = 0) (h2 : b % 2 = 0) :
    (a + b) % 2 = 0 := by
  omega                          -- omega 的整除推理能力

-- omega 自动展开 Nat.succ
example (n : ℕ) (h : Nat.succ n > 3) : n ≥ 3 := by
  omega                          -- 知道 Nat.succ n = n + 1
```

## 实用技巧
%%%
tag := "practical-tips"
%%%

omega 会自动扫描 `LocalContext` 中所有线性算术假设，
*无需手动指定*。但自定义定义不会被展开——
调用前先 `unfold` 或 `simp only [...]`。

`norm_num` 擅长具体计算（如 `100 * 99 / 2 = 4950`），
`omega` 擅长带变量的线性推理。两者互补，几乎不重叠。

# 8.8 练习
%%%
tag := "ch08-exercises"
%%%

## 练习 1：基础线性推理
%%%
tag := "exercise-8-1"
%%%

判断以下哪些目标 `omega` 能直接证明，并尝试证明它们。

```
-- (a) 能否用 omega 证明？
example (n : ℕ) (h : n > 0) : 2 * n ≥ 2 := by
  sorry

-- (b) 能否用 omega 证明？
example (a b : ℤ) (h1 : a + b = 10) (h2 : a - b = 4) : a = 7 := by
  sorry

-- (c) 能否用 omega 证明？
example (n : ℕ) : n * (n + 1) / 2 ≥ 0 := by
  sorry

-- (d) 能否用 omega 证明？
example (x : ℤ) (h : x % 3 = 0) : x % 6 = 0 ∨ x % 6 = 3 := by
  sorry
```

*提示*：(a) 和 (d) 是线性的，(b) 看起来线性但检查一下解，
(c) 包含变量乘法。

## 练习 2：诊断失败
%%%
tag := "exercise-8-2"
%%%

以下每个 `omega` 调用都会失败。解释失败原因，并给出修复方案。

```
-- (a) 为什么失败？如何修复？
example (n : ℕ) : n ^ 2 ≥ 0 := by
  omega

-- (b) 为什么失败？如何修复？
def triple (n : ℕ) := 3 * n
example (n : ℕ) : triple n ≥ n := by
  omega

-- (c) 为什么失败？如何修复？
example (n : ℕ) : n - 3 + 3 = n := by
  omega
```

*提示*：(a) 非线性项，(b) 未展开的定义，(c) 缺少前置条件。

## 练习 3：tactic 编程
%%%
tag := "exercise-8-3"
%%%

编写一个 tactic `omega_or_sorry`，尝试用 omega 关闭目标，
如果失败则用 `sorry` 关闭并在 info log 中输出警告。

```
-- 骨架
elab "omega_or_sorry" : tactic => do
  sorry -- 你的实现
```

*提示*：使用 `try`/`catch` 包裹 `evalTactic`，
在 `catch` 分支中调用 `logWarning` 后再执行 `sorry`。

## 练习 4：omega 与 linarith 的边界
%%%
tag := "exercise-8-4"
%%%

找出一个命题，使得 `omega` 能证明但 `linarith` 不能，
以及一个命题，使得 `linarith` 能证明但 `omega` 不能。
解释原因。

*提示*：考虑整除性（omega 的强项）和实数域（linarith 的强项）。

# 8.9 小结
%%%
tag := "ch08-summary"
%%%

| 概念 | 关键点 |
|------|--------|
| 理论基础 | Presburger 算术——整数上只有加法的一阶理论，可判定 |
| 算法核心 | 变量消去 + dark shadow 整数修正 |
| 适用范围 | ℕ 和 ℤ 上的线性等式、不等式、整除、模运算 |
| Nat.sub | 自动处理截断语义，翻译为 max(a-b, 0) |
| 能力边界 | 变量乘法、指数、实数 → 超出范围 |
| 失败诊断 | 检查非线性项、未展开定义、缺失假设、不支持的类型 |
| 编程使用 | `evalTactic` 直接调用，`try`/`catch` 探测性调用 |
| 与 linarith | omega 处理整数整除，linarith 处理实数有序域 |

下一章将介绍 `linarith`、`nlinarith` 和 `polyrith`——从线性到非线性的算术自动化。
