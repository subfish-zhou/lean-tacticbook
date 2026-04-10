import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch13Decide"

#doc (Manual) "第十三章 decide 与 `native_decide`：有限计算判定" =>
%%%
file := "Ch13Decide"
tag := "ch13-decide"
%%%

*本章目标*：理解 `Decidable` 类型类如何同时携带判定结果与证据，
掌握 `decide` 与 `native_decide` 的执行路径、可信度差异与失败模式，
学会为自定义命题编写 `Decidable` 实例，在实际证明中做出合理选择。

`simp` 做符号重写，`omega` 解线性算术，`norm_num` 算大数——
当问题可以归约为*有限计算*时，`decide` 和 `native_decide` 是最直接的武器：
把命题变成布尔值，算出 `true`，证明完毕。

# 13.1 Decidable 类型类
%%%
tag := "decidable-typeclass"
%%%

`decide` 系列 tactic 的根基是核心库中的 `Decidable`：

```
-- [定义] 来自 Init.Prelude
-- class inductive Decidable (p : Prop) where
--   | isFalse (h : ¬p) : Decidable p   -- ❶ 判定为假，携带反证
--   | isTrue  (h : p)  : Decidable p   -- ❷ 判定为真，携带正证
```

- *❶* 不只说"假"，还给出 `¬p` 的构造性证明。
- *❷* 不只说"真"，还给出 `p` 的构造性证明。

与 `Bool` 的本质区别：`Bool` 只记录结果，`Decidable` 同时记录*结果与证据*。
这使得判定结果可以被内核直接用作证明项。

Lean 核心库为大量命题注册了 `Decidable` 实例。
`DecidableEq α` 是 `∀ (a b : α), Decidable (a = b)` 的缩写，
大多数具体数据类型（`Nat`、`Int`、`String`、`List α`）都自动拥有此实例。

```anchor decidableChecks
#check (inferInstance : Decidable (3 = 5))
#check (inferInstance : Decidable (3 < 5))
#check (inferInstance : Decidable (5 ∈ [1,2,3]))
```

## Prop 与 Bool 的桥梁
%%%
tag := "prop-bool-bridge"
%%%

`Decidable` 连接 `Prop` 世界和 `Bool` 世界：

```
-- [签名] 核心库关键定义
#check @Decidable.decide  -- {p : Prop} → [Decidable p] → Bool  -- ❶ 命题 → 布尔
-- of_decide_eq_true : decide p = true → p               -- ❷ 布尔真 → 命题真
```

- *❶* 把命题"降级"为布尔值，供 `if` / `match` 使用。
- *❷* 若内核规约 `decide p` 到 `true`，`rfl` 即证 `decide p = true`，
  再经 `of_decide_eq_true rfl` 得到 `p` 的证明——这正是 `decide` tactic 的核心。

# 13.2 decide：内核规约证明
%%%
tag := "decide-kernel-reduction"
%%%

`decide` tactic 的执行路径分四步：

1. *查找实例*：对目标 `P`，typeclass search 搜索 `Decidable P`。
2. *构造项*：生成 `@Decidable.decide P inst`。
3. *内核规约*：Lean kernel 对该项执行 δ/ι/ζ reduction。
4. *提取证明*：若结果为 `true`，构造 `of_decide_eq_true rfl` 作为证明项。

```anchor decideBasic
example : 2 + 2 = 4 := by decide

example : ¬ (3 ∈ [1, 2, 5]) := by decide

example : Nat.Prime 7 := by decide

example : ∀ b : Bool, b || !b = true := by decide
```

*绝对可信*：`decide` 的证明只依赖 Lean kernel——系统中最小的 trusted computing base，
不涉及编译器、运行时或任何外部 axiom。

# 13.3 decide 的五种失败模式
%%%
tag := "decide-failure-modes"
%%%

## 失败 1：缺少 Decidable 实例
%%%
tag := "failure-missing-instance"
%%%

```
-- [会报错] p 是任意命题，无法合成实例
-- example (p : Prop) : p ∨ ¬p := by decide
--   -- ▸ failed to synthesize Decidable (p ∨ ¬p)
--   -- ▸ 修复：用 Classical.em p，或为 p 提供 Decidable 实例
```

`p ∨ ¬p` 在经典逻辑中成立（`Classical.em`），但 `decide` 只处理*构造性可判定*的命题。

## 失败 2：内核超时（计算量过大）
%%%
tag := "failure-kernel-timeout"
%%%

```
-- [会超时] 内核解释器需要试除到 √1000003 ≈ 1000
-- example : Nat.Prime 1000003 := by decide
--   -- ▸ 修复：改用 native_decide 或 norm_num
```

*经验法则*：`decide` 不宜超过几万步 reduction，超过应换 tactic。

## 失败 3：命题为假
%%%
tag := "failure-false-proposition"
%%%

```
-- [会报错] 4 不是质数
-- example : Nat.Prime 4 := by decide
--   -- ▸ decide evaluated to false
--   -- ▸ 这不是 tactic 的问题，而是命题本身不成立
```

`decide` 只能证明*为真*的可判定命题。报告 `evaluated to false` 本身是有用的诊断。

## 失败 4：目标含自由变量
%%%
tag := "failure-free-variables"
%%%

```
-- [会报错] n 不是字面量，无法规约
-- example (h : n = 3) : n + 1 = 4 := by decide
--   -- ▸ decide 只做封闭项（closed term）的计算
--   -- ▸ 修复：先 subst h 消除 n，再 decide
-- example (h : n = 3) : n + 1 = 4 := by subst h; decide  -- ✓
```

## 失败 5：实例存在但计算量不可行
%%%
tag := "failure-infeasible-computation"
%%%

```
-- [会超时] 实例存在 ≠ 计算可行
-- example : (Finset.range 10000).card = 10000 := by decide
--   -- ▸ 修复：native_decide 或 simp [Finset.card_range]
```

# 13.4 `native_decide`：编译到原生代码
%%%
tag := "native-decide-compilation"
%%%

`native_decide` 解决 `decide` 的性能瓶颈，但执行路径完全不同：

1. *查找实例*：同 `decide`，搜索 `Decidable P` 实例。
2. *编译*：将判定过程通过 Lean 编译器编译为*原生机器码*。
3. *执行*：运行编译后的代码，得到 `Bool` 结果。
4. *桥接*：若结果为 `true`，通过 axiom `Lean.ofReduceBool` 构造证明。

```anchor nativeDecide
example : Nat.Prime 104729 := by native_decide

example : ∀ n : Fin 256, n.val < 256 := by native_decide

example : ((List.range 100).filter Nat.Prime).length = 25 := by native_decide
```

## 可信度代价
%%%
tag := "native-decide-trust"
%%%

`decide` 的证明完全在内核中完成，可信边界仅限于 Lean kernel 本身。
`native_decide` 则依赖编译器将判定过程编译为原生代码再执行——
如果编译器存在 bug（错误优化、代码生成缺陷），理论上可能把
实际为 `false` 的计算"证明"为 `true`。因此 `native_decide` 的可信边界
比 `decide` 更宽：它信任的不仅是内核，还有编译执行路径。

*Mathlib 策略*：能用 `decide` 就不用 `native_decide`，
能用 `norm_num` / `omega` 等专用 tactic 就优先使用。

## `native_decide` 的失败模式
%%%
tag := "native-decide-failure-modes"
%%%

```
-- [会报错] 同样需要 Decidable 实例
-- example (p : Prop) : p ∨ ¬p := by native_decide
--   -- ▸ failed to synthesize Decidable (p ∨ ¬p)

-- [会报错] 命题为假
-- example : Nat.Prime 4 := by native_decide
--   -- ▸ native_decide evaluated to false

-- [会报错] 代码链中含 sorry 或 partial 导致编译失败
-- partial def foo : Nat → Bool := fun _ => true
-- instance : Decidable P := if foo 0 then .isTrue sorry else .isFalse sorry
-- example : P := by native_decide  -- failed to compile
```

`native_decide` 不能绕过 `Decidable` 的要求，也不能证明假命题。
包含 `sorry` 或 `partial` 的代码链会导致编译失败。

# 13.5 编写 Decidable 实例
%%%
tag := "writing-decidable-instances"
%%%

## 方式 1：deriving 自动派生
%%%
tag := "instance-deriving"
%%%

```anchor derivingDecidableEq
inductive Color where
  | red | green | blue
  deriving DecidableEq

example : Color.red ≠ Color.blue := by decide
```

- *❶* 结构体、枚举、带参数的归纳类型都支持 `deriving DecidableEq`。

## 方式 2：dependent if 手动构造
%%%
tag := "instance-dependent-if"
%%%

```anchor decidableDvd
instance (n m : Nat) : Decidable (n ∣ m) :=
  if h : m % n = 0
  then .isTrue (Nat.dvd_of_mod_eq_zero h)
  else .isFalse fun ⟨k, hk⟩ =>
    h (by omega)
```

- *❶* `if h : cond` 是 dependent if——分支中 `h` 分别绑定 `cond` 和 `¬cond`。
- *❷* 正分支利用库引理构造整除证明。*❸* 负分支推出矛盾。

## 方式 3：归约到已有可判定命题
%%%
tag := "instance-reduction"
%%%

```anchor decidableIsEven
def IsEven (n : Nat) : Prop := n % 2 = 0

instance (n : Nat) : Decidable (IsEven n) :=
  inferInstanceAs (Decidable (n % 2 = 0))
```

- *❶* `inferInstanceAs` 告诉 typeclass search `IsEven n` 就是 `n % 2 = 0`。

## 方式 4：组合逻辑连接词
%%%
tag := "instance-logical-combinators"
%%%

`Decidable` 对逻辑连接词封闭——`p ∧ q`、`p ∨ q`、`¬p`、`p → q`
在两侧可判定时自动可判定。对有限量词 `∀ x : α, P x` 和 `∃ x : α, P x`，
需要 `α` 是 `Fintype` 且 `P` 对每个 `x` 可判定：

```anchor decidableComposite
example : Decidable (3 < 5 ∧ 7 ≠ 8) := inferInstance
example : Decidable (∀ i : Fin 5, i.val < 10) := inferInstance
example : Decidable (∃ i : Fin 5, i.val = 3) := inferInstance
```

# 13.6 与其他 tactic 的对比
%%%
tag := "comparison-with-other-tactics"
%%%

```anchor decideTacticComparison
example : 100 < 200 := by omega
example : 100 < 200 := by decide

example : Nat.Prime 104729 := by norm_num
example : (2 : ℤ) ^ 10 = 1024 := by norm_num

example (n : Nat) : n + 0 = n := by simp
-- example (n : Nat) : n + 0 = n := by decide  -- ✗ n 不是字面量
```

## 选择速查表
%%%
tag := "tactic-selection-table"
%%%

- 场景：小规模有限穷举（< 100 种） —— 推荐 tactic：`decide` —— 原因：内核可信，无额外假设
- 场景：大规模有限穷举（> 100 种） —— 推荐 tactic：`native_decide` —— 原因：编译执行，快几个数量级
- 场景：`Nat`/`Int` 线性算术 —— 推荐 tactic：`omega` —— 原因：专用 decision procedure
- 场景：具体数值计算、素性、整除 —— 推荐 tactic：`norm_num` —— 原因：meta 层高效归约 + 证书
- 场景：含变量的等式 / 不等式 —— 推荐 tactic：`simp` / `ring` / `linarith` —— 原因：符号化简

# 13.7 实战模式与调试
%%%
tag := "practical-patterns-debugging"
%%%

## 模式 1：有限案例验证
%%%
tag := "pattern-finite-case-verification"
%%%

```anchor decideFiniteVerification
example : ∀ a b : Fin 3, a + b = b + a := by decide

example : ∀ a b : Fin 20, a + b = b + a := by native_decide
```

## 模式 2：`interval_cases` + decide 联用
%%%
tag := "pattern-interval-cases"
%%%

```anchor intervalCasesDecide
example (n : ℕ) (h : n < 3) : n * n < 10 := by
  interval_cases n
  all_goals decide
```

## 模式 3：在 have 中建立局部事实
%%%
tag := "pattern-have-local-facts"
%%%

```anchor decideLocalLemma
example : True := by
  have h₁ : Nat.Prime 7 := by decide
  have h₂ : 7 ∈ [2, 3, 5, 7] := by decide
  trivial
```

## 调试技巧 1：用 #eval 预判
%%%
tag := "debug-eval-preview"
%%%

```
-- #eval Nat.Prime 7          -- true  → decide 应能证明
-- #eval Nat.Prime 1000003    -- true  → 但 decide 会超时，用 native_decide
#eval (4 : Nat) ∣ 6        -- false → decide 会失败（命题为假）
```

先 `#eval` 确认真假和计算量，再选 tactic。

## 调试技巧 2：检查实例 + 调整心跳
%%%
tag := "debug-instance-check-heartbeats"
%%%

```
#check (inferInstance : Decidable (3 < 5))      -- OK
#check (inferInstance : DecidableEq Color)      -- 报错则需 deriving 或手写

-- set_option maxHeartbeats 400000 in
-- example : Nat.Prime 997 := by decide
--   -- ▸ 默认 200000，可临时提高；若需大幅增加，应换 tactic
```

# 13.8 练习
%%%
tag := "ch13-exercises"
%%%

## 练习 1（基础）：decide 能证什么
%%%
tag := "exercise-13-1"
%%%

判断以下哪些能用 `decide` 证明，不能的说明原因并给出替代方案：

```
example : 10 * 10 = 100 := by sorry              -- (a) 基础算术
-- example : ¬ Nat.Prime 15 := by sorry              -- (b) 否定命题
example (n : Nat) : n + 0 = n := by sorry         -- (c) 含自由变量
example : ∀ b : Bool, b && true = b := by sorry   -- (d) Bool 穷举
-- example : Nat.Prime 104729 := by sorry             -- (e) 大素数
```

> *提示*：(a)(b)(d) 直接 `decide`；(c) 含变量用 `simp`；(e) 超时用 `native_decide` 或 `norm_num`。

## 练习 2（编写实例）：自定义 Decidable
%%%
tag := "exercise-13-2"
%%%

```
def IsPalindrome (l : List Char) : Prop := l = l.reverse
instance (l : List Char) : Decidable (IsPalindrome l) := sorry
-- 验证
-- example : IsPalindrome ['a', 'b', 'a'] := by decide
-- example : ¬ IsPalindrome ['a', 'b', 'c'] := by decide
```

> *提示*：用 `inferInstanceAs (Decidable (l = l.reverse))` 归约到 `DecidableEq`。

## 练习 3（性能选择）：为每题选择最合适的 tactic
%%%
tag := "exercise-13-3"
%%%

```
-- example : Nat.Prime 10007 := by sorry             -- (a) 大素数
example : ∀ n : Nat, n < n + 1 := by sorry        -- (b) 全称线性不等式
example : ∀ a b : Fin 4, a * b = b * a := by sorry -- (c) 有限穷举
example : (3 : ℤ) ^ 5 = 243 := by sorry           -- (d) 数值幂运算
```

> *提示*：(a) `norm_num`；(b) `omega`；(c) `decide`；(d) `norm_num`。

## 练习 4（调试）：修复失败的 decide
%%%
tag := "exercise-13-4"
%%%

```
-- (a) 为什么超时？给出两种修复方案。
-- example : Nat.Prime 1000003 := by decide
-- (b) 为什么失败？只改 tactic 前面的代码。
-- example (h : n = 5) : n + 1 = 6 := by decide
```

> *提示*：(a) 换 `native_decide` 或 `norm_num`；(b) 在 `decide` 前加 `subst h;`。

## 练习 5（进阶）：组合判定实例
%%%
tag := "exercise-13-5"
%%%

```
def InRange (lo hi n : Nat) : Prop := lo ≤ n ∧ n < hi
instance (lo hi n : Nat) : Decidable (InRange lo hi n) := sorry
-- 验证
-- example : InRange 3 10 5 := by decide
-- example : ¬ InRange 3 10 2 := by decide
```

> *提示*：展开后是 `lo ≤ n ∧ n < hi`，用 `inferInstanceAs` 归约到 `And` 的组合实例。

# 13.9 小结
%%%
tag := "ch13-summary"
%%%

- `Decidable`：类型类，编码"可计算的真假判定 + 证据"，是 `Prop`/`Bool` 的桥梁
- `decide`：内核规约，绝对可信（仅依赖 kernel），但速度受限于解释执行
- `native_decide`：编译到原生代码，快几个数量级，但引入 `ofReduceBool` 公理
- `失败诊断`：缺实例 → 检查 `Decidable`；超时 → 换 tactic；含变量 → 先化简；假命题 → 检查逻辑
- `编写实例`：`deriving`、dependent if、`inferInstanceAs` 归约、逻辑组合
- `选择原则`：小穷举 `decide`，大穷举 `native_decide`，算术 `omega`/`norm_num`

`decide` 和 `native_decide` 是 Lean 自动化的"兜底手段"——
当问题可以归约为有限计算时，它们总能给出答案。
理解它们的能力边界与失败模式，才能在实战中高效组合各种 tactic。
