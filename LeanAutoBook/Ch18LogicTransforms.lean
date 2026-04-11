import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch18LogicTransforms"

#doc (Manual) "push_neg、contrapose、by_contra" =>
%%%
file := "Ch18LogicTransforms"
tag := "ch18-logic-transforms"
%%%

*本章目标*：掌握三个逻辑变换 tactic 的工作原理、适用场景与失败模式，
学会在分析学证明中正确选择和组合它们。

# 18.1 问题：否定与逆否的手工拆解
%%%
tag := "logic-transforms-problem"
%%%

分析学中充斥着"否定一个带量词的命题"的需求。
例如证明某函数不连续，需要否定 ε-δ 定义：

```
¬(∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε)
```

手工展开需要反复应用 De Morgan 律和量词否定，
同时把 `¬(a < b)` 翻译成 `b ≤ a`——枯燥且容易出错。

`push_neg`、`contrapose`、`by_contra` 为三类场景设计：

- `push_neg`：把 `¬` 向内推到原子公式
- `contrapose`：把 `P → Q` 变为 `¬Q → ¬P`
- `by_contra`：假设目标的否定，转为推导矛盾

# 18.2 `push_neg`：否定下推
%%%
tag := "push-neg"
%%%

## 基本行为
%%%
tag := "push-neg-basic"
%%%

`push_neg` 对目标或假设中的否定做 De Morgan 展开，
直到否定落在原子公式上：

```anchor pushNegEpsilonDelta
example (f : ℝ → ℝ) (a : ℝ) :
    ¬(∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε) ↔
    ∃ ε > 0, ∀ δ > 0, ∃ x, |x - a| < δ ∧ ε ≤ |f x - f a| := by
  constructor
  · intro h
    push_neg at h
    exact h
  · intro h
    push_neg
    exact h
```

变换规则一览：

- `¬(P ∧ Q)`：`¬P ∨ ¬Q`
- `¬(P ∨ Q)`：`¬P ∧ ¬Q`
- `¬(∀ x, P x)`：`∃ x, ¬P x`
- `¬(∃ x, P x)`：`∀ x, ¬P x`
- `¬(a ≤ b)`：`b < a`
- `¬(a < b)`：`b ≤ a`
- `¬¬P`：`P`（需要 Classical）

## 内部机制
%%%
tag := "push-neg-internals"
%%%

`push_neg` 是一个*特化的 `simp`*，使用 `@[push_neg]` 引理集：

```
-- Mathlib 核心引理（简化）
@[push_neg] theorem not_and_or : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q   -- ❶ De Morgan
@[push_neg] theorem not_or     : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q   -- ❷ De Morgan
@[push_neg] theorem not_forall : (¬∀ x, P x) ↔ ∃ x, ¬P x  -- ❸ 量词翻转
@[push_neg] theorem not_exists : (¬∃ x, P x) ↔ ∀ x, ¬P x  -- ❹ 量词翻转
@[push_neg] theorem not_le     : ¬(a ≤ b) ↔ b < a     -- ❺ 序关系
```

能力完全由引理集决定——自定义类型需注册 `@[push_neg]` 引理。

作用位置：`push_neg`（目标）、`push_neg at h`（假设）、
`push_neg at h ⊢`（两者）、`push_neg at *`（全部）。

# 18.3 contrapose：逆否变换
%%%
tag := "contrapose"
%%%

当目标形如 `P → Q` 时，`contrapose` 将其变为 `¬Q → ¬P`：

```anchor contraposeDvd
example (a b : ℤ) : a ∣ b → b ≠ 0 → a ≠ 0 := by
  intro hdvd
  contrapose
  intro ha
  simp [ha] at hdvd
  exact hdvd
```

## contrapose! 变体
%%%
tag := "contrapose-bang"
%%%

`contrapose!` = `contrapose` + `push_neg`，
否定中含 `≤`、`<`、量词时特别有用：

```anchor contraposeSquare
example (n : ℕ) : n < 3 → n ^ 2 < 9 := by
  contrapose!
  intro h
  nlinarith
```

如果 context 中有假设 `h : P` 且目标是 `Q`，
`contrapose h` 会把 `h` 消耗并变为 `¬Q → ¬P`。

# 18.4 `by_contra`：反证法
%%%
tag := "by-contra"
%%%

`by_contra` 假设目标的否定，将目标变为 `False`：

```anchor byContraUnbounded
example : ∀ n : ℕ, ∃ m, m > n := by
  by_contra! h
  obtain ⟨n, hn⟩ := h
  have := hn (n + 1)
  omega
```

## 与 Classical.em 的关系
%%%
tag := "by-contra-classical"
%%%

`by_contra` 依赖排中律——本质上等价于：

```
rcases Classical.em P with h | h
· exact h              -- ❶ 若 P 成立，直接用
· exfalso; ...         -- ❷ 若 ¬P，推矛盾
```

因此 `by_contra` 是*非构造性的*。
`Decidable` 实例可用时 Lean 会用可判定版本代替。

# 18.5 组合模式
%%%
tag := "logic-transforms-combinations"
%%%

## 模式 A：`push_neg` 消除否定前缀
%%%
tag := "combination-push-neg-prefix"
%%%

```anchor pushNegConvergence
example (a : ℕ → ℝ) (L : ℝ)
    (h : ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε) :
    ¬(∃ ε > 0, ∀ N, ∃ n ≥ N, ε ≤ |a n - L|) := by
  push_neg
  exact h
```

## 模式 B：contrapose! + 算术
%%%
tag := "combination-contrapose-arith"
%%%

```anchor contraposeStrictMono
example (f : ℝ → ℝ) (hf : StrictMono f) (a b : ℝ) :
    f a = f b → a = b := by
  contrapose!
  exact fun h => hf.injective.ne h
```

## 模式 C：by_contra + push_neg + 分步推理
%%%
tag := "combination-by-contra-push-neg"
%%%

```anchor byContraEpsilon
example (a b : ℝ) (h : ∀ ε > 0, a ≤ b + ε) : a ≤ b := by
  by_contra h'
  push_neg at h'
  have := h ((a - b) / 2) (by linarith)
  linarith
```

## 模式 D：`by_contra!` + obtain + omega
%%%
tag := "combination-by-contra-obtain"
%%%

```anchor byContraNlinarith
example (n : ℕ) (h : n ^ 2 < 2 * n) : n < 2 := by
  by_contra! h'
  nlinarith [sq_nonneg (n - 2)]
```

# 18.6 判断：何时用哪个
%%%
tag := "logic-transforms-when-to-use"
%%%

```
目标含 ¬ 或需要否定展开？
  ├─ 是 → push_neg（或 push_neg at h）
  └─ 否 → 目标形如 P → Q？
           ├─ 是，且逆否更自然 → contrapose / contrapose!
           └─ 否，或正面证明困难 → by_contra / by_contra!
```

*经验法则*：
- 否定展开后直接匹配假设 → `push_neg`
- 逆否方向更容易 → `contrapose`
- 需要制造矛盾 → `by_contra`
- 带 `!` 的变体在含 `≤`/`<`/量词时省去手动 `push_neg`

*不该用的场景*：
- 目标有直接证明路径——不要为了"保险"加 `by_contra`
- `by_contra` 引入的 `¬P` 无法被利用——说明应该走直接证明

# 18.7 失败模式
%%%
tag := "logic-transforms-failures"
%%%

## 失败 1：`push_neg` 遇到无注册引理的类型
%%%
tag := "logic-fail-unregistered-type"
%%%

```
example (a b : MyOrder) : ¬(a ≤ₘ b) := by
  push_neg   -- ❌ 目标不变——不知道 ¬(≤ₘ) 等于什么
```

*诊断*：`push_neg` 不报错但目标不变。
*修复*：注册 `@[push_neg] theorem not_myLe : ¬(a ≤ₘ b) ↔ b <ₘ a`。

## 失败 2：contrapose 的目标不是蕴含
%%%
tag := "logic-fail-contrapose-not-implication"
%%%

```
example : P ∧ Q := by
  contrapose   -- ❌ goal is not an implication
```

*修复*：用 `by_contra` 代替。

## 失败 3：contrapose 对嵌套蕴含的意外行为
%%%
tag := "logic-fail-contrapose-nested"
%%%

```
example : P → Q → R := by
  contrapose    -- 对整个 (P → Q → R) 做逆否，变为 ¬R → ¬(P → Q)
```

*修复*：先 `intro` 到需要的位置，再 `contrapose`。

## 失败 4：`push_neg` 不处理 ↔ 的否定
%%%
tag := "logic-fail-push-neg-iff"
%%%

```
example : ¬(P ↔ Q) := by
  push_neg    -- ❌ 无化简规则
```

*修复*：先 `rw [not_iff]` 手动拆解。

## 失败 5：`by_contra!` 展开不完全
%%%
tag := "logic-fail-by-contra-incomplete"
%%%

`by_contra!` 内部调用 `push_neg`，若 `push_neg` 无法处理某层否定，
展开会在中途停止。检查 `h` 的类型是否符合预期。

# 18.8 调试
%%%
tag := "logic-transforms-debugging"
%%%

*检查 `push_neg` 做了什么*：在 `push_neg` 后暂停，观察 Infoview。
如果目标不变，原因有三：否定已在原子位置；缺少 `@[push_neg]` 引理；
表达式模式不匹配。

*查看使用的引理*：

```
set_option trace.Meta.Tactic.simp true in
example : ¬(∀ x, P x) := by push_neg; sorry
-- trace 显示使用了 not_forall 等引理
```

*contrapose 前后对比*：

```
example : P → Q := by
  trace_state; contrapose; trace_state; sorry
```

# 18.9 与相关 tactic 的比较
%%%
tag := "logic-transforms-comparison"
%%%

- 简洁度 —— `push_neg`：高 —— `simp only [not_forall, ...]`：中 —— 手动 `rw`：低
- 可控性 —— `push_neg`：低（全部展开） —— `simp only [not_forall, ...]`：高（选引理） —— 手动 `rw`：最高

- 前提 —— `contrapose`：目标是蕴含 —— `by_contra`：任意
- 构造性 —— `contrapose`：是 —— `by_contra`：否（排中律）
- 产出 —— `contrapose`：新蕴含目标 —— `by_contra`：`h : ¬Goal ⊢ False`

# 18.10 练习
%%%
tag := "logic-transforms-exercises"
%%%

## 练习 1（基础 · `push_neg`）
%%%
tag := "logic-exercise-1"
%%%

```
example : ¬(∀ n : ℕ, n = 0) → ∃ n : ℕ, n ≠ 0 := by
  sorry
```

提示：`push_neg` 一步到位后 `exact`。

## 练习 2（基础 · contrapose）
%%%
tag := "logic-exercise-2"
%%%

```
example (m n : ℕ) : m * n = 0 → m = 0 ∨ n = 0 := by
  contrapose
  sorry
```

提示：逆否后 `push_neg`，然后用 `Nat.mul_ne_zero`。

## 练习 3（判断 · 选择 tactic）
%%%
tag := "logic-exercise-3"
%%%

以下三个目标分别最适合 `push_neg`、`contrapose`、`by_contra` 中的哪个？

```
-- (a) 直接证明
example (f : ℝ → ℝ) (hf : Monotone f) : ∀ a b, a ≤ b → f a ≤ f b := by sorry

-- (b) 否定展开
example : ¬(∃ n : ℕ, ∀ m, m < n) := by sorry

-- (c) 反证法
example (n : ℕ) (h : ∀ d, d ∣ n → d = 1 ∨ d = n) (hn : n ≥ 2) :
    Nat.Prime n := by sorry
```

## 练习 4（进阶 · 组合）
%%%
tag := "logic-exercise-4"
%%%

用 `by_contra!` 开头。

```
example (a : ℕ → ℝ) (h : ∀ n, a n < a (n + 1)) :
    ∀ m n, m < n → a m < a n := by
  sorry
```

## 练习 5（进阶 · 分析学）
%%%
tag := "logic-exercise-5"
%%%

证明：`a ≤ b + ε` 对所有正 `ε` 成立则 `a ≤ b`。

```
example (a b : ℝ) (h : ∀ ε > 0, a ≤ b + ε) : a ≤ b := by
  sorry
```

## 练习 6（挑战 · 稠密性）
%%%
tag := "logic-exercise-6"
%%%

```
example (a b : ℝ) (hab : a < b) : ∃ q : ℚ, a < ↑q ∧ ↑q < b := by
  sorry
```

提示：`by_contra!` 不是唯一路径，考虑 Mathlib 的 `exists_rat_btwn`。

# 18.11 小结
%%%
tag := "logic-transforms-summary"
%%%

- tactic：`push_neg` —— 作用：否定下推到原子公式 —— 内部机制：特化 `simp` + `@[push_neg]` 引理集 —— 变体：`at h`、`at *`
- tactic：`contrapose` —— 作用：蕴含 → 逆否 —— 内部机制：逻辑等价变换 —— 变体：`contrapose!`（+ push\_neg）
- tactic：`by_contra` —— 作用：反证法 —— 内部机制：排中律 `Classical.em` —— 变体：`by_contra!`（+ push\_neg）

*核心要点*：
- `push_neg` 的能力取决于 `@[push_neg]` 引理集——自定义类型需注册
- `contrapose` 要求目标是蕴含形式
- `by_contra` 是非构造性的，尽量只在直接证明困难时使用
- 带 `!` 的变体自动 `push_neg`，在含 `≤`/`<`/量词时省去手动步骤
