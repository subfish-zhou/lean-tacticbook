import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch06Simp"

#doc (Manual) "第六章 simp：重写引擎" =>
%%%
file := "Ch06Simp"
tag := "ch06-simp"
%%%

*本章目标*：深入理解 `simp` 的工作原理——重写规则集、方向性、优先级——并掌握配置、调试和避坑技巧。

在前面的章节中，你已经学会了手写 tactic：`rw`、`apply`、`intro`、`cases`……
它们精确、可控，但面对一连串"显然"的化简步骤时，手写每一步既繁琐又脆弱。
`simp` 正是从"手写 tactic"过渡到"自动化"的第一站：
把一大批等式引理打包成一个*重写规则集*，自动、反复地应用，直到目标无法再化简。
理解 `simp` 的内部机制，是后续章节（`ring`、`omega`、`aesop`、自定义 tactic）的基础。

# 6.1 simp 的核心思想
%%%
tag := "simp-core-idea"
%%%

`simp` 是一个*项重写系统（term rewriting system）*，工作流程概括为四步：

```
-- [示意]
loop:
  1. 在目标（或假设）中找到一个子项 t
  2. 在规则集中找到一条引理  lhs = rhs  使得 t 匹配 lhs
  3. 把 t 替换为 rhs
  4. 如果目标发生了变化，回到 1；否则停止
```

停止的条件有两个：*收敛*（没有规则能继续应用）或*超时*（超过 heartbeat / maxSteps 限制）。

# 6.2 重写规则集：simp lemmas
%%%
tag := "simp-lemmas"
%%%

任何被标记了 `@[simp]` 的定理都会被加入全局 simp 规则集。Lean 4 的 Mathlib 中有*数千条* simp lemma，覆盖自然数、列表、集合、逻辑连接词等大量日常化简。

## 四种引理形式
%%%
tag := "four-lemma-forms"
%%%

*等式引理*——最常见：

```anchor simpLemmaEquality
@[simp] theorem add_zero (n : Nat) : n + 0 = n := by omega
-- simp 看到 ?n + 0 就替换为 ?n
```

*条件等式*——带前提的重写：

```
-- [示意]
@[simp] theorem if_pos {p : Prop} [Decidable p] (h : p) :
    (if p then a else b) = a
-- simp 必须先证明前提 h : p，才会应用这条规则
```

*命题引理*——化简为 `True` 或 `False`：

```
-- [示意]
@[simp] theorem Nat.lt_irrefl (n : Nat) : ¬(n < n)
-- simp 遇到 n < n 时化为 False
```

*iff 引理*——等价替换：

```
-- [示意]
@[simp] theorem not_and {p q : Prop} : ¬(p ∧ q) ↔ (p → ¬q)
```

## 候选选择
%%%
tag := "candidate-selection"
%%%

当目标中出现可重写的子项时，simp 会先用 DiscrTree 索引按 LHS 骨架筛选候选引理，再对候选逐一做 `isDefEq` 匹配和方向检查，第一条匹配成功的引理立即应用。候选来源大致包括三类：用户在 tactic 中显式传入的引理（`simp \[foo, bar\]`）、局部假设、以及全局 `@[simp]` 集。其中*用户显式传入的引理最可控*——你确切知道它们会被考虑，不依赖索引是否恰好命中。

> *注意*：simp 内部的候选排序属于实现细节，不同 Lean 版本可能调整。编写证明时不要依赖特定的选择顺序，而应通过 `simp only [...]` 或 `simp [extra_lemma]` 显式控制引理集。

# 6.3 方向性：只从左到右
%%%
tag := "directionality-lhs-to-rhs"
%%%

*这是理解 simp 最关键的一点。*

simp 只会把引理的 *LHS 重写为 RHS*，永远不会反过来。对于 `@[simp] theorem foo : A = B`，simp 把 `A` 替换为 `B`，但不会把 `B` 替换为 `A`。

这决定了 simp lemma 的*编写原则*：

| 原则 | 说明 |
|------|------|
| LHS 比 RHS 复杂 | 化简应让表达式变"简单" |
| RHS 不引入新变量 | RHS 的自由变量必须都出现在 LHS 中 |
| 不能左右对称 | `a + b = b + a` 会导致无限循环 |
| 一致的范式方向 | 同一概念的多条引理应朝同一范式化简 |

如果你需要*反方向*使用某条 simp lemma，可以用 `←`：

```anchor simpBackward
example (a b : Nat) (h : a = b + 1) : b + 1 = a := by
  simp [← h]
```

# 6.4 内部索引：DiscrTree
%%%
tag := "internal-index-discrtree"
%%%

simp 用 *discrimination tree（DiscrTree）* 来加速查找。注册引理时，提取 LHS 的"骨架"（head symbol + arity）组织成前缀树；查找时，用子项骨架快速定位候选集，再对候选做 `isDefEq` 精确匹配。

这意味着大多数引理在索引阶段就被过滤掉了。引理的 LHS 越具体，索引效率越高；LHS 是纯 metavariable 的引理会匹配所有子项，效率极差。

# 6.5 遍历策略
%%%
tag := "traversal-strategy"
%%%

simp 对目标表达式采用*由外向内（outermost-first）+ 不动点迭代*：

```
-- [伪代码]
function simp(term):
  loop:
    if apply_rules(term) succeeds:
      term ← result; continue     -- 根节点变了，重新开始
    for each subterm: simp(subterm)  -- 递归化简子项
    if apply_rules(term) succeeds:
      term ← result; continue     -- 子项变化使根节点可化简
    else: break                    -- 不动点，停止
```

子项化简后根节点可能变得可化简，因此整个过程反复迭代。`maxSteps` 限制总重写步数。

# 6.6 simp 的变体
%%%
tag := "simp-variants"
%%%

## simp only
%%%
tag := "simp-only"
%%%

`simp only \[lemma1, lemma2, ...\]` *只使用指定引理*，不加载全局 `@[simp]` 集。

```anchor simpOnly
example (n : Nat) : n + 0 + 0 = n := by
  simp only [Nat.add_zero]
```

优点：可预测（不随 import 变化）、性能好（引理集小）、Mathlib 风格指南推荐。

## `simp_all`
%%%
tag := "simp-all"
%%%

`simp_all` 化简目标*和所有假设*，允许假设间相互化简：

```anchor simpAll
example (a b : Nat) (h1 : a = 0) (h2 : a + b = 5) : b = 5 := by
  simp_all
```

假设化简为 `True` 则丢弃，化简为 `False` 则 `contradiction` 结束。由于 `simp_all` 会改写假设本身，它比裸 `simp` 更强，但也更需要谨慎——假设被改写后可能变得难以阅读或在后续 tactic 中不易引用。

## dsimp
%%%
tag := "dsimp"
%%%

`dsimp` 只做 definitional equality 下的化简（beta、eta、iota 规约和 proof 为 `rfl` 的等式），开销更小。

```anchor dsimpBetaReduce
example : (fun x => x + 1) 3 = 4 := by
  dsimp  -- beta 规约后 rfl
```

# 6.7 Discharger：条件引理的证明器
%%%
tag := "discharger-conditional-lemmas"
%%%

当 simp 应用条件引理 `h : p → lhs = rhs` 时，需要证明前提 `p`。默认 simp 递归调用自身作为 discharger，递归深度由 `maxDischargeDepth`（默认 2）控制。

你也可以指定自定义 discharger：

```anchor simpDischarger
example (n : Nat) (h : n > 0) : n - 1 + 1 = n := by
  simp (dsimp := false) (discharger := omega)
```

# 6.8 simp 的配置
%%%
tag := "simp-config"
%%%

```
-- [示意]
structure Simp.Config where
  maxSteps          : Nat  := 100000  -- 最大重写步数
  maxDischargeDepth : Nat  := 2       -- 条件证明的递归深度
  contextual        : Bool := false   -- 上下文化简（if 分支）
  memoize           : Bool := true    -- 缓存子项结果
  zeta              : Bool := true    -- 展开 let 绑定
  beta              : Bool := true    -- β 规约
  eta               : Bool := true    -- η 规约
  iota              : Bool := true    -- match/recursor 规约
  decide            : Bool := false   -- 用 decide 证明条件
  failIfUnchanged   : Bool := true    -- 目标不变则报错
```

在 tactic 中传入：

```anchor contextualSimp
example (p : Prop) [Decidable p] (h : p) (a b : Nat) :
    (if p then a else b) = a := by
  simp [h]
```

*contextual simp* 默认关闭但很有用：在 `if` 的 `then` 分支中 simp 假设条件为真，`else` 分支中假设为假。

# 6.9 调试 simp
%%%
tag := "debugging-simp"
%%%

```anchor traceSimpRewrite
set_option trace.Meta.Tactic.simp.rewrite true in
example : 0 + 1 = 1 := by simp
```

```anchor traceSimpDischarge
set_option trace.Meta.Tactic.simp.discharge true in
example : 0 + 1 = 1 := by simp
```

trace 输出示例：

```
-- [示意]
[Meta.Tactic.simp.rewrite] 0 + 1 ==> 1    using theorem Nat.zero_add
```

引理没触发的常见原因：LHS 不匹配（差一个 unfold）、条件无法 discharge、引理不在 simp 集中。

## simp?
%%%
tag := "simp-query"
%%%

`simp?` 告诉你 simp 实际使用了哪些引理，方便改写为 `simp only [...]`：

```anchor simpQuestion
example : 0 + 1 = 1 := by simp only [Nat.zero_add]
-- simp? 会输出：Try this: simp only [Nat.zero_add]
```

# 6.10 常见失败模式
%%%
tag := "ch06-common-failure-patterns"
%%%

## 失败模式 1：simp 循环
%%%
tag := "failure-simp-loop"
%%%

*症状*：`(deterministic) timeout` 或 heartbeat 耗尽。

```
-- [示意]
@[simp] theorem comm : a + b = b + a
-- simp 不断交换：a + b → b + a → a + b → ...
```

*修复*：不要把交换律标 `@[simp]`。需要时用 `rw [add_comm]`，或用 `ring`/`ac_rfl`。

## 失败模式 2：simp 改变不了目标
%%%
tag := "failure-simp-no-progress"
%%%

*症状*：`simp made no progress`。

```
-- [示意]
def myFun (n : Nat) := n + 1
example : myFun 3 = 4 := by simp        -- 失败！simp 不认识 myFun
example : myFun 3 = 4 := by simp [myFun] -- ✅ 告诉 simp 展开 myFun
```

其他原因：条件引理的前提无法 discharge，或引理根本不在 simp 集中。

## 失败模式 3：意外展开
%%%
tag := "failure-unexpected-unfolding"
%%%

*症状*：目标变成一大堆底层表达式。

*修复*：用 `simp only [...]` 控制引理集，或关闭特定规约：

```
-- [示意]
simp (config := { iota := false })  -- 关闭 match 展开
simp (config := { zeta := false })  -- 关闭 let 展开
```

## 失败模式 4：simp 太慢
%%%
tag := "failure-simp-too-slow"
%%%

*原因*：全局 `@[simp]` 集太大、目标表达式太大、或 LHS 太泛的引理。

*修复*：用 `simp only` 减小引理集；先 `rw` 手动化简关键步骤再 simp。

# 6.11 在元程序中调用 simp
%%%
tag := "simp-in-metaprograms"
%%%

最简单的方式是 `evalTactic`：

```
-- [可运行]
import Lean.Elab.Tactic.Simp

evalTactic (← `(tactic| simp \[my_lemma\]))
evalTactic (← `(tactic| simp only [Nat.add_zero, Nat.mul_one]))
evalTactic (← `(tactic| simp (config := { failIfUnchanged := false }) \[my_lemma\]))
```

> *底层 API*：`Lean.Meta.simp` 提供更底层接口（`Simp.Context` → `Simp.Result`），但随版本变化较大。大多数 tactic 开发用 `evalTactic` 足够。

# 6.12 @\[simp\] 标注的最佳实践
%%%
tag := "simp-annotation-best-practices"
%%%

*好的 simp lemma：*

```anchor goodSimpLemmas
@[simp] theorem length_nil : ([] : List α).length = 0 := rfl
@[simp] theorem length_cons (a : α) (l : List α) :
    (a :: l).length = l.length + 1 := rfl
```

*危险的 simp lemma：*

```
-- [示意]
@[simp] theorem bad_comm : a + b = b + a       -- ❌ 循环
@[simp] theorem bad_var : f a = g a b           -- ❌ b 不在 LHS 中
@[simp] theorem bad_direction : n = n + 0       -- ❌ 方向反了
```

如果引理只在特定场景有用，不标 `@[simp]`，需要时 `simp \[my_lemma\]` 局部传入。

# 6.13 simp 与其他 tactic 的协作
%%%
tag := "simp-collaboration-with-tactics"
%%%

```anchor simpWithRw
example (a b : Nat) (h : a = b) : a + 0 = b := by
  rw [h]; simp
```

```anchor simpWithConstructor
example : True ∧ (0 + 1 = 1) := by
  constructor
  · trivial
  · simp
```

常用模式：`simp only [...]` 做预处理，化简目标后交给 `exact`、`omega` 等收尾。

# 6.14 小结
%%%
tag := "ch06-summary"
%%%

| 概念 | 关键点 |
|------|--------|
| 核心机制 | 项重写系统，DiscrTree 索引，不动点迭代 |
| 方向性 | 只从 LHS 到 RHS；用 `← lemma` 反转 |
| 引理形式 | 等式、条件等式、iff、命题 |
| 变体 | `simp only`（精确）、`simp_all`（含假设）、`dsimp`（definitional） |
| Discharger | 条件引理的前提证明器，可自定义 |
| 配置 | `Simp.Config`：maxSteps、contextual、zeta、iota 等 |
| 调试 | `trace.Meta.Tactic.simp.*`、`simp?` |
| 避坑 | 不标交换律、不引入新变量、`simp only` 优于裸 `simp` |

# 6.15 练习
%%%
tag := "ch06-exercises"
%%%

## 练习 1（热身）：基本 simp
%%%
tag := "exercise-6-1"
%%%

```anchor exercise1
-- 预测 simp 能否解决以下目标，然后验证。
example : [1, 2, 3].length = 3 := by
  sorry

example (n : Nat) : n + 0 + 0 + 0 = n := by
  sorry
```

## 练习 2（热身）：simp only
%%%
tag := "exercise-6-2"
%%%

```anchor exercise2
-- 先用 simp? 找出需要的引理，再改写为 simp only 版本。
example (a b : Nat) : a + 0 + (b + 0) = a + b := by
  sorry
```

## 练习 3（debug）：为什么 simp 失败了？
%%%
tag := "exercise-6-3"
%%%

```anchor exercise3
def double (n : Nat) := 2 * n

example : double 3 = 6 := by
  try simp  -- simp made no progress!
  sorry
```

提示：simp 不认识 `double`。你需要告诉它展开。

## 练习 4（综合）：组合化简
%%%
tag := "exercise-6-4"
%%%

```anchor exercise4
example (n : Nat) (h : n > 0) :
    [n].length + (n - 1 + 1) = n + 1 := by
  sorry
```

# 6.16 下一章预告
%%%
tag := "ch06-next-chapter"
%%%

`simp` 擅长"逐步重写化简"，但有些等式它处理不了——比如多项式恒等式 `(a + b)² = a² + 2ab + b²`。
下一章进入 `ring`：基于*范式化（normalization）* 的判定过程，专门解决可交换环上的等式问题。
