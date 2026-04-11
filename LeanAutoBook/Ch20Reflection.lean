import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch20Reflection"

#doc (Manual) "反射证明模式" =>
%%%
file := "Ch20Reflection"
tag := "ch20-reflection"
%%%

*定位说明*：本章是一章*高级设计视角 / 架构章*——
目标不是让你立刻动手实现完整的反射 tactic，
而是建立反射这条路径的*整体认知框架*。
其中 §20.2 的布尔重言式例子是唯一需要完整读懂的核心示例；
其余部分提供设计视野和参考，可按需深入。

*本章目标*：理解反射（reflection）如何把证明义务转化为计算，
掌握"语法—语义—范式化—正确性引理"的四步核心模式，
了解 `decide` / `native_decide` 的工作原理与性能特征，
并通过完整示例体验反射 tactic 的设计全流程。

在第十九章，模式 D（完整决策过程）提到两条构造证明的路径：
逐步构造（用 `mkApp` 拼装证明项）和反射（编码为可判定数据，用 `decide`）。
本章展开反射这条路径。

反射的核心洞察：*如果你能写一个可计算的判定函数，
就不需要手动构造复杂的证明项——让 Lean 的计算引擎替你验证*。

# 20.1 反射的核心思想
%%%
tag := "reflection-core-idea"
%%%

传统 tactic 在 `MetaM` 中*手动构造证明项*——
拆解目标、匹配引理、用 `mkApp` 拼装，每一步都要处理
universe、typeclass、unification 等细节。反射走完全不同的路：

```
传统方式: 目标 → 在 MetaM 中逐步构造证明项 → 内核检查
反射方式: 目标 → 编码为数据 → 计算出 true → 正确性引理 → QED
```

反射把*证明的复杂性转移到正确性引理的一次性证明上*——
一旦正确性引理证毕，每次使用只需做一次计算。

## 四步模式
%%%
tag := "four-step-pattern"
%%%

几乎所有反射 tactic 都遵循同一套模式：

```
❶ 定义语法（syntax）：  用归纳类型表示表达式
❷ 定义语义（semantics）：语法 → 实际数学对象（解释函数）
❸ 范式化（normalization）：把语法化简为范式
❹ 正确性引理（soundness）：范式化保持语义
```

使用时：把 Lean 表达式 *quote* 为语法对象 → 范式化 →
用 `decide` 验证范式 → 用正确性引理得到原始命题的证明。

# 20.2 一个最小例子：布尔重言式
%%%
tag := "bool-tautology-example"
%%%

```
-- [示意] ❶ 语法
inductive BExpr
- var (i : Fin n)：true_ —— false_
- var (i : Fin n)：and (a b : BExpr)
- var (i : Fin n)：or  (a b : BExpr)
- var (i : Fin n)：not (a : BExpr)

-- [示意] ❷ 语义——给定变量赋值，求值为 Bool
def BExpr.eval (env : Fin n → Bool) : BExpr → Bool
- .var i     => env i：.true_     => true
- .var i     => env i：.false_    => false
- .var i     => env i：.and a b   => a.eval env && b.eval env
- .var i     => env i：.or  a b   => a.eval env —— b.eval env
- .var i     => env i：.not a     => !(a.eval env)

-- [示意] ❸ 判定——穷举所有赋值
def BExpr.isTaut (e : BExpr) : Bool :=
  (Finset.univ).forall fun env => e.eval env
  -- ▸ 对所有可能的 env 检查 eval 返回 true

-- [示意] ❹ 正确性引理
theorem isTaut_sound (e : BExpr) (h : e.isTaut = true) :
    ∀ env, e.eval env = true := by
  simp [BExpr.isTaut, Finset.forall_mem_univ] at h; exact h
```

使用时：要证 `p ∨ ¬p`，把它反射为 `BExpr.or (.var 0) (.not (.var 0))`，
计算 `isTaut` 得 `true`，`isTaut_sound` 给出证明。
*证明的复杂度从"构造项"变成了"执行函数"*——
`isTaut_sound` 只需证明一次，之后每个重言式都是纯计算。

# 20.3 完整示例：整数表达式等价
%%%
tag := "integer-expr-equivalence"
%%%

*扩展阅读*：本节展示更接近实际 tactic 规模的设计。
初次阅读可浏览结构，不必逐行理解——核心模式已在 §20.2 中完整呈现。

目标：自动判定整数多项式表达式等价——更接近实际 tactic 的规模。

## ❶ 语法 + ❷ 语义
%%%
tag := "iexpr-syntax-semantics"
%%%

```
-- [示意]
inductive IExpr
- lit (n : ℤ)          -- 字面量：var (i : ℕ)          -- 第 i 个变量
- lit (n : ℤ)          -- 字面量：add (a b : IExpr)
- lit (n : ℤ)          -- 字面量：mul (a b : IExpr)
- lit (n : ℤ)          -- 字面量：neg (a : IExpr)

abbrev IEnv := ℕ → ℤ    -- 环境：变量赋值

def IExpr.denote (env : IEnv) : IExpr → ℤ
- .lit n     => n：.var i     => env i
- .lit n     => n：.add a b   => a.denote env + b.denote env
- .lit n     => n：.mul a b   => a.denote env * b.denote env
- .lit n     => n：.neg a     => -(a.denote env)
```

## ❸ 范式化
%%%
tag := "iexpr-normalization"
%%%

选 Horner 形式（`a * x + b` 的递归表示）作为范式：

```
-- [示意] Horner Normal Form
inductive HNF
- const (n : ℤ)                        -- 常数：horner (p : HNF) (i : ℕ) (q : HNF)  -- p * x_i + q

def IExpr.toHNF : IExpr → HNF := ...     -- ❶ 转换算法
def HNF.denote (env : IEnv) : HNF → ℤ := ... -- ❷ 范式的语义
instance : DecidableEq HNF := ...        -- ❸ 结构相等，可判定
```

- *❶* 转换算法把 `IExpr` 递归化为 Horner 范式，合并同类项。
- *❸* `DecidableEq` 使得 `decide` 可以比较两个范式。

## ❹ 正确性引理
%%%
tag := "iexpr-soundness"
%%%

```
-- [示意] 核心：范式化保持语义
theorem toHNF_sound (e : IExpr) (env : IEnv) :
    e.toHNF.denote env = e.denote env := by
  induction e with                       -- 对语法结构归纳
- lit n => simp [IExpr.toHNF, HNF.denote, IExpr.denote]：add a b iha ihb =>
    simp [*, IExpr.toHNF, HNF.denote, IExpr.denote]; ring
- mul a b iha ihb =>
    simp [*, IExpr.toHNF, HNF.denote, IExpr.denote]; ring
- _ => simp [*, IExpr.toHNF, HNF.denote, IExpr.denote]; ring

-- 推论：范式相等 → 语义相等（tactic 实际使用的引理）
theorem eq_of_toHNF_eq (e1 e2 : IExpr) (env : IEnv)
    (h : e1.toHNF = e2.toHNF) :
    e1.denote env = e2.denote env := by
  have := toHNF_sound e1 env
  have := toHNF_sound e2 env
  rw [h] at *; linarith
```

正确性引理只需证明一次——之后每个等式判定都是纯计算。

## 组装 tactic
%%%
tag := "iexpr-assemble-tactic"
%%%

```
-- [示意] MetaM 端的工作极少
elab "int_ring" : tactic => do
  let goal ← getMainTarget
  -- 1. 解析目标 e1 = e2
  -- 2. quote: 把 e1, e2 反射为 IExpr 值
  -- 3. 构造 e1.toHNF = e2.toHNF 的 decide 证明
  -- 4. 用 eq_of_toHNF_eq 得到原始等式的证明
  sorry -- 完整实现需要 quote 机制，见 §20.4
```

*纯反射方案*在 MetaM 中几乎不做计算，所有验证交给内核。
实现简单但性能受限——见 §20.6。

# 20.4 反射的关键步骤：quote
%%%
tag := "reflection-quote"
%%%

*概念说明*：本节介绍 quote 的设计思路，而非要求你手写完整的 quote 函数。
理解"要把 `Expr` 编码成内部语法树"这一概念即可。

*Quote*（反射/引用）把 Lean 的 `Expr` 编码为归纳类型的值。
其核心逻辑是模式匹配目标表达式，递归编码为语法类型：

```
quote 的工作流程（以 IExpr 为例）：
  ❶ 遇到整数字面量 → IExpr.lit n
  ❷ 遇到加法 a + b  → IExpr.add (quote a) (quote b)
  ❸ 遇到乘法 a * b  → IExpr.mul (quote a) (quote b)
  ❹ 遇到未知表达式  → IExpr.var i（分配一个新变量编号）
```

实现上，quote 函数在 `MetaM` 中执行，接收 Lean 的 `Expr` 并输出
归纳类型的值（同样是 `Expr`），同时维护一个变量映射表
记录已见过的不透明子表达式。

quote 的覆盖范围*直接决定反射 tactic 的能力边界*——
不能识别的构造会被当作不透明变量，范式化无法深入分析。

# 20.5 decide、`native_decide` 与 Decidable
%%%
tag := "decide-native-decide"
%%%

反射的最后一步是验证计算结果。这依赖 `Decidable` 类型类和两种执行机制。

## Decidable 的角色
%%%
tag := "decidable-role"
%%%

```
-- [示意] Decidable 的定义
inductive Decidable (p : Prop) where
- isTrue  (h : p)     -- p 成立，附带证明：isFalse (h : ¬p)    -- p 不成立，附带反证

-- decide 的工作原理：
-- 1. 找到 Decidable p 的实例
-- 2. 内核对该实例做 whnf 归约
-- 3. 归约到 isTrue h → h 就是证明；归约到 isFalse _ → 失败
```

反射的本质是*把不一定可判定的问题转化为可判定的问题*：
原始目标 `e1.denote env = e2.denote env` 可能不可判定，
但反射后的 `e1.toHNF = e2.toHNF`（结构相等）一定是 `DecidableEq`。
正确性引理桥接两者。

## decide vs `native_decide`
%%%
tag := "decide-vs-native-decide"
%%%

```
-- [示意]
example : (3 + 4 : ℕ) = 7 := by decide
  -- ▸ 内核归约 3 + 4 得到 7，然后 rfl——慢但可信度最高

example : (10 ^ 20 + 1 : ℕ) ≠ 10 ^ 20 := by native_decide
  -- ▸ 编译为原生代码执行——快但信任编译器
```

- 执行方式 —— `decide`：内核归约（解释执行） —— `native_decide`：编译为原生代码
- 速度 —— `decide`：慢 —— `native_decide`：快（几个数量级）
- 可信度 —— `decide`：最高（内核检查每一步） —— `native_decide`：较低（信任编译器）
- 适用规模 —— `decide`：小实例（< 1000 步） —— `native_decide`：大实例
- Mathlib 接受度 —— `decide`：总是接受 —— `native_decide`：谨慎使用

*经验法则*：先试 `decide`；超时则换 `native_decide`。

# 20.6 反射 vs 逐步构造
%%%
tag := "reflection-vs-stepwise"
%%%

这是设计反射 tactic 时最重要的决策。

## 纯反射
%%%
tag := "pure-reflection"
%%%

```
Lean Expr → quote → 内部表示 → 范式化（内核计算）→ decide
```

*优点*：实现简单——MetaM 端只做 quote，验证全在内核中。
*缺点*：内核要执行范式化算法——对大表达式极慢。

## 逐步构造
%%%
tag := "stepwise-construction"
%%%

```
Lean Expr → 解析 → MetaM 中运行算法 → 逐步用 mkApp 构造证明项
```

*优点*：MetaM 中的计算是编译后的代码，速度快。
*缺点*：每一步变换都要构造对应的证明项，实现复杂。

## 混合方案（实际选择）
%%%
tag := "hybrid-approach"
%%%

真实 tactic 通常*混合两种方案*——在 MetaM 中做范式化（快），
用反射验证范式等价（简单）：

```
-- [示意] ring 的实际策略（简化版）
-- ❶ MetaM 中范式化为 Horner 形式（编译后的代码，快）
-- ❷ 反射验证：范式 = 原始表达式（正确性引理 + rfl）
-- ❸ MetaM 中比较两个范式（结构相等）
-- ❹ Eq.trans 串联：lhs = norm = rhs
```

`norm_num`（第十章）也遵循这个模式：在 MetaM 中做数值计算，
用反射验证结果。对素性测试等复杂运算，
把 `Nat.Prime 37` 转化为可计算的判定函数。

- 实现难度 —— 纯反射：低 —— 逐步构造：高 —— 混合：中
- 性能 —— 纯反射：慢（内核计算） —— 逐步构造：快 —— 混合：快
- 可信度 —— 纯反射：高 —— 逐步构造：中（依赖实现） —— 混合：高
- 典型代表 —— 纯反射：教学示例 —— 逐步构造：— —— 混合：`ring`、`norm_num`

*设计建议*：原型阶段用纯反射（快速验证算法正确性），
性能不足时迁移到混合方案。

# 20.7 失败模式
%%%
tag := "reflection-failure-modes"
%%%

## 失败 1：Decidable 实例缺失
%%%
tag := "failure-decidable-missing"
%%%

```
-- [示意]
-- ✗ 函数外延性不可判定
example : (fun x : ℕ => x + 1) = (fun x => 1 + x) := by decide
  -- 错误：failed to synthesize Decidable instance
  -- ✓ 修复：用 funext 和 omega
```

`decide` 只能处理有 `Decidable` 实例的命题。

## 失败 2：内核计算超时
%%%
tag := "ch20-failure-kernel-timeout"
%%%

```
-- [示意]
-- ✗ decide 在大实例上超时
example : (List.range 10000).length = 10000 := by decide
  -- 内核展开 10000 次 List.cons → 超时
  -- ✓ 修复 1：native_decide
  -- ✓ 修复 2：simp [List.length_range]（引理推理优于暴力计算）
```

*优先选择引理推理而非暴力计算*。

## 失败 3：quote 不完整
%%%
tag := "failure-incomplete-quote"
%%%

```
-- [示意]
-- ✗ quote 无法识别 max 函数，把 max a b 当作不透明变量
-- 结果：max a b + 0 和 max a b 的范式不同
-- ✓ 修复：扩展 quote 识别 max，或先 simp 消除 + 0
```

遇到"应该能证但不能证"，首先检查 quote 是否识别了所有构造。

## 失败 4：`native_decide` 的信任问题
%%%
tag := "failure-native-decide-trust"
%%%

```
-- [示意]
-- native_decide 的证明不被内核检查计算过程
-- 如果编译器有 bug，可能产生错误的证明
-- ✓ 建议：开发阶段用 native_decide 加速，最终验证用 decide
```

`native_decide` 的可信基础包括 Lean 编译器，
比纯 `decide`（只信任内核）多一层信任。Mathlib 对其使用有严格限制。

## 失败 5：范式化不完备
%%%
tag := "failure-normalization-incomplete"
%%%

```
-- [示意]
-- ✗ 范式化不处理除法：(a * b) / b 和 a 的范式不同
-- ✓ 这不是 bug——范式化的运算集合是有限的
-- ▸ 设计时明确边界：范式化能处理什么运算？
```

# 20.8 设计检查清单
%%%
tag := "reflection-design-checklist"
%%%

动手前逐项回答：

- *判定性*：问题可判定吗？能写出 `→ Bool` 的函数吗？
- *范式*：用什么范式？范式相等是否容易判定？
- *正确性*：范式化保持语义的证明是否可行？（最难的部分）
- *quote 范围*：需要识别哪些构造？不识别的怎么处理？
- *性能*：`decide` 够用还是需要 `native_decide` / 混合方案？
- *边界*：超出能力范围时，错误信息如何提示用户？

*正确性引理是整个开发中最耗时的部分*——
先用小例子验证范式化算法，再投入大量时间写证明。

# 20.9 落地总结：本章的核心收获
%%%
tag := "reflection-takeaways"
%%%

读完本章，你应该带走三件事：

1. *四步模式是反射的骨架*（§20.1–20.2）：语法 → 语义 → 范式化 → 正确性引理。
   布尔重言式例子（§20.2）已完整展示了这个模式——如果你只精读一节，读这节。

2. *设计决策比实现细节更重要*（§20.6）：纯反射 vs 逐步构造 vs 混合方案，
   决定了 tactic 的性能和实现复杂度。实际项目几乎总是走混合路线。

3. *quote 和范式化是能力边界*（§20.4, §20.7）：反射 tactic 能证什么、不能证什么，
   取决于 quote 识别了哪些构造、范式化覆盖了哪些运算。

其余内容（整式反射的完整骨架、`Decidable` 的内部机制、`quoteIExpr` 的实现细节）
属于进阶参考——当你真正要实现反射 tactic 时再回来查阅。

# 20.10 练习
%%%
tag := "reflection-exercises"
%%%

## 练习 1（基础 · §20.2 复习）：识别四步模式
%%%
tag := "exercise-identify-four-steps"
%%%

标出以下代码中哪些部分对应 ❶语法、❷语义、❸范式化、❹正确性：

```
-- [示意]
inductive PExpr                    -- (?)
- var (i : Nat)：add (a b : PExpr)

def PExpr.eval (env : Nat → ℕ) : PExpr → ℕ     -- (?)
- .var i => env i：.add a b => a.eval env + b.eval env

def PExpr.sort : PExpr → PExpr := ...            -- (?)

theorem sort_sound (e : PExpr) (env : Nat → ℕ) : -- (?)
    (e.sort).eval env = e.eval env := ...
```

## 练习 2（设计）：选择反射 vs 逐步构造
%%%
tag := "exercise-choose-approach"
%%%

对以下场景，判断应用纯反射、逐步构造还是混合方案，说明理由：

```
(a) 验证 8-bit 位运算等式（如 x &&& (x ||| y) = x）
    变量最多 3 个，结果空间 2^24 = 16M。

(b) 验证 ℝ 上的多项式恒等式，变量最多 20 个。

(c) 验证有限群的元素阶，群的阶 ≤ 100。
```

*提示*：(a) 穷举可行但边界——`native_decide` 可能需要；
(b) 穷举不可行，必须范式化；(c) 穷举可行，纯 `decide` 可能够用。

## 练习 3（进阶）：设计正确性引理
%%%
tag := "exercise-design-soundness"
%%%

为"列表排序等价性"反射设计正确性引理的*陈述*（不需要证明）：

```
-- [示意] 判定两个列表是否是同一个 multiset
-- 语法：List ℕ
-- 范式化：排序
-- 判定：排序后结构相等
-- 请写出 sort_perm_sound 的类型签名：
-- theorem sort_perm_sound : ???
```

*提示*：`List.sort l₁ = List.sort l₂ → l₁ ~ l₂`（`~` 是 `List.Perm`）。

# 20.11 小结
%%%
tag := "reflection-summary"
%%%

- `反射核心思想`：命题 → 可计算数据 → 计算验证 → 正确性引理桥接
- `四步模式`：语法 → 语义 → 范式化 → 正确性引理
- `quote`：把 Lean Expr 编码为归纳类型值；覆盖范围决定能力边界
- `decide`：内核归约，慢但可信度最高
- `native_decide`：编译执行，快但信任编译器
- `纯反射 vs 混合`：原型用纯反射，生产用混合（MetaM 范式化 + 反射验证）
- `正确性引理`：最耗时的部分——先用小例子验证算法再投入证明
- `相关章节`：`ring`（第七章）、`norm_num`（第十章）、`decide`（第十三章）
- `主要陷阱`：Decidable 缺失、内核超时、quote 不完整、范式化不完备

*一句话总结*：反射把"构造证明的复杂性"转移为"一次性证明正确性引理的复杂性"——
如果你的问题可判定，反射几乎总是比逐步构造更简单的起点。

下一章讨论性能工程——当 `decide` 超时、证明项过大时如何诊断和优化。
