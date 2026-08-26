import VersoManual
import LeanTacticBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "examples"
set_option verso.exampleModule "Examples.Ch11Grind"

#doc (Manual) "grind：共享推理状态上的饱和搜索" =>
%%%
file := "Ch11Grind"
tag := "ch11-grind"
%%%

> *本章目标*：从一份“发现新事实就写回去”的工作板开始。先用三个小证明观察不同推理步骤怎样互相接力，再逐步命名等价类、规则匹配、饱和与分支；最后才对应到 Grind 的生产数据结构。
>
> *版本基准*：Lean `leanprover/lean4:v4.32.2`，commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`；Mathlib revision `905b95818eb32af7874a58b427f50c1711a5e96c`。

有些目标既不是找一条现成定理，也不是一次多项式或线性算术计算能解决。证明过程可能先用等式改写，再实例化一个局部全称命题，接着让算术推出新等式，最后才触发逻辑蕴含。若每一步都由用户手工安排，脚本会充满重复的“小步搬运”。

Grind 的基本想法是维护一份共享工作板。每种推理机制从板上读取自己认识的事实，推出新事实后再写回去；其它机制随后可以继续使用。

# 三个例子先看“谁把什么交给谁”
%%%
tag := "ch11-s01"
%%%

第一例只有一个等式 `a = b`。把相等的参数放进同一个函数，结果仍相等；这里连续把规则用在 `f a` 和 `f (f a)` 上：

```anchor grind_congruence
theorem grindCongruence (α : Type) (f : α → α) (a b : α)
    (h : a = b) : f (f a) = f (f b) := by
  grind
```

第二例给出局部规则 `h : ∀ x, f x = x`。要证明 `f (f a) = a`，先把 `x` 取成 `a` 得到 `f a = a`，再把 `x` 取成 `f a` 得到 `f (f a) = f a`，两式接起来即可：

```anchor grind_ematch
theorem grindEMatch (α : Type) (f : α → α) (a : α)
    (h : ∀ x, f x = x) : f (f a) = a := by
  grind
```

第三例需要两个不同步骤接力：先由 `x ≤ y` 和 `y ≤ x` 得到 `x = y`，再把这个等式交给局部蕴含 `x = y → P`：

```anchor grind_solver_cooperation
theorem grindCooperation (x y : Int) (h₁ : x ≤ y) (h₂ : y ≤ x)
    (P : Prop) (hP : x = y → P) : P := by
  grind
```

第三例最能说明共享工作板：算术部分不必知道怎样证明 `P`，逻辑规则也不必重新证明整数反对称性。双方只需要用同一种方式登记和读取新事实。

# 写上工作板之前，先统一表达式外形
%%%
tag := "ch11-s03"
%%%

同一个表达式若以许多表面写法进入工作板，后面的匹配会反复做无用功。Grind 因此先做 preprocessing（预处理）：用自己的一组化简规则统一常见外形，折叠投影，并让相同子表达式尽量共享。生产实现还处理 reducible 展开、universe level 规范化、nested proof 与 subsingleton 标记；这些名称第一遍可以略过。

预处理的目标不是直接证明定理，而是让语义相同或结构相近的表达式尽早共享表示。这样后续规则不必分别认识许多等价写法。

# 把已知相等的表达式放进同一类
%%%
tag := "ch11-s04"
%%%

已知 `a = b` 后，可以把 `a`、`b` 放进同一个 equivalence class（等价类），表示系统已经有证明说明它们相等。表达式及其应用关系组成的结构叫 E-graph（等式图）。概念图里，一个 e-node（等式图节点）可看成“头函数 + 各参数所在的等价类”。

如果 `a` 与 `b` 在同一类，那么 `f a` 与 `f b` 的头函数相同，参数类也相同，于是它们也应合并。这条不断补齐函数同余后果的过程叫 congruence closure（同余闭包）：

:::codeBox "pseudocode"
```
class(a) = class(b)
⇒ signature(f, class(a)) = signature(f, class(b))
⇒ class(f a) = class(f b)
```
:::

生产 `ENode` 没有把概念图逐字存成字段，而是保存完整 `Expr` 以及 root、next、congruence 和 proof 等信息，再动态读取应用结构。第一遍先用概念模型推理，源码字段留到纵切阅读。

命题也可进入图。证明一个命题，相当于用证明把它与 `True` 联系起来；证明其否定则与 `False` 联系起来。矛盾必须携带可用于构造 Lean 证明的数据，不能只是一个 `closed = true` 标志。

# 合并两个类时必须保存理由
%%%
tag := "ch11-s05"
%%%

快速维护等价类通常使用 union-find（并查集）。它能回答两个节点是否已有相同 representative（代表元），却不会自动给出它们为何相等的 Lean 证明。Grind 因此在每次 merge（合并）时增量保存证明数据：`NewFact` 直接携带 proof Expr；E-class 路径保存等式证明或延迟 congruence placeholder；theorem instantiation 与 theory solver 也直接生成 proof；split 另有分支结构和来源信息。

`Proof.lean` 沿 E-class 路径组合 `Eq.trans`，并在需要时实现 congruence placeholder；分支层再组合各支证明。若只实现 union-find 而不保存这些数据，你得到的是快速判等器，不是证明术。

# 局部全称规则怎样找到可用实例
%%%
tag := "ch11-s06"
%%%

第二个例子中的规则 `∀ x, f x = x` 要在已知项 `a`、`f a` 上分别取实例。把规则左边可变化的位置写成 `?x`，就得到 pattern（模式）`f ?x`。从工作板中寻找让模式成立的项，并允许已知相等项互相替代，这个过程叫 E-matching（等价类匹配）。

Grind 不会把全库所有 theorem 都放进 matcher（匹配器）。只有已激活的 grind theorem、局部 `∀` 假设和用户显式提供的规则参与。实现先按头符号从 `appMap` 找可能项，再在等价类中约束模式变量；有多个取值时，用 choice stack 记录待尝试选择。

:::codeBox "pseudocode"
```
pattern: f ?x = ?x
known terms: f a, a, b
known equality: a = b

matching may instantiate ?x with class(a)=class(b)
```
:::

新实例又可能产生新项，进而触发更多实例。为防止无限增长，generation bound 限制实例能依赖多“新”的项，instance cache 避免重复生成同一实例。达到轮数或实例数上限，只说明本次有界搜索停止，不能推出规则不适用。

# Trace 看到的是断言流
%%%
tag := "ch11-s07"
%%%

```anchor grind_trace_assert
set_option trace.grind.assert true in
theorem grindTrace (α : Type) (f : α → α) (a : α)
    (h : ∀ x, f x = x) : f (f a) = a := by
  grind
```

锁定输出为：

:::codeBox "code"
```
[grind.assert] ∀ x, f x = x
[grind.assert] ¬ f (f a) = a
[grind.assert] f a = a
```
:::

第二条是目标取反。第三条是 local forall 在 `a` 上的实例。随后 `f (f a)` 可借实例、congruence 与等价类信息归约到 `a`，与否定目标冲突。

# 两类其它工作者：局部传播规则与专用求解器
%%%
tag := "ch11-s08"
%%%

propagator（传播器）监听某类新事实或等价类合并，一旦触发条件满足，就执行一个较小的局部规则，例如拆逻辑连接词、使用构造子的单射性或传播不等关系。theory solver（理论求解器）则负责一整类专门问题，例如整数算术、线性算术、交换环或序关系。两者都把所得证明和新事实写回共享工作板。

以整数反对称性为例，职责链是：`x ≤ y` 与 `y ≤ x` 先成为共享 facts；整数算术 solver 在自身状态中消费两条约束并构造 `x = y` 的证明；新等式再断言回 E-graph，触发目标命题与 `True` 的合并，最终用保存的等式 proof 关闭原目标。这里讲的是生产模块间的 proof-producing 数据流，不冒充逐事件 trace；其余 solver 也按“读共享 facts、构造新证明、写回共享状态”的共同接口理解。

# 无法直接推出时，分别尝试有限种情况
%%%
tag := "ch11-s09"
%%%

```anchor grind_split
theorem grindSplit (P Q : Prop) : P ∨ Q → Q ∨ P := by
  grind
```

析取交换需要分别讨论输入来自左支还是右支。case split（情况分裂）为每个分支加入对应局部假设，然后在该分支上继续运行全部推理机制。实现把“分支建立后接着做什么”作为函数参数传入；这种写法叫 continuation-passing style（续延传递风格，CPS）。

:::codeBox "pseudocode"
```
split P:
  branch P      → continue all solvers/instantiation
  branch ¬P     → continue all solvers/instantiation
combine branch proofs
```
:::

每个分支有自己的状态快照；只在某一分支成立的事实不能泄漏到兄弟分支。生产实现还能在可识别的 `False` 证明形状中判断矛盾不依赖新分支假设，从而跳过不必要的 split。这项 non-chronological backtracking（非时间顺序回溯）只覆盖特定证明形状，不是一般的依赖分析算法。

# 当没有新事实时停止：饱和主循环
%%%
tag := "ch11-s02"
%%%

反复读取已有事实并写回新事实，直到再也产生不了新事实，这种过程叫 saturation（饱和）。Grind 的主循环可按已经学过的概念读成：

:::codeBox "pseudocode"
```
预处理假设，并把目标的否定写入工作板
在资源限制内反复：
  运行专用求解器
  用已激活的全称规则产生实例
  传播新事实和新合并
  必要时分情况，并在每支继续完整循环
直到得到矛盾、达到饱和，或耗尽资源
```
:::

生产调度可概括为 `solvers <|> instantiate <|> splitNext <|> mbtc`。此处 `<|>` 组织“当前哪类工作还能产生进展”；分支则通过前节的 CPS 把完整后续调度带进每个子分支。`mbtc` 是 model-based theory combination（基于模型的理论组合），第一次阅读只需把它看作另一种让多个理论求解器交换信息的收尾尝试。

# 与 Library Search 的关系
%%%
tag := "ch11-s10"
%%%

```table
- 维度
- `exact?`
- `grind`
---
- 主结构
- 逐个主引理候选
- 共享事实饱和
---
- 索引
- 声明结论 discrimination tree
- active theorem patterns 与 appMap
---
- 等式
- apply/unification 与对称候选
- E-graph congruence closure
---
- 分支
- solveByElim DFS，深度 6
- CPS split 与非时间顺序回溯
---
- 全库
- 直接搜索 Library Search 索引
- 默认不扫描全库
```

`grind +suggestions` 才调用 `LibrarySuggestions.select` 选择可能有用的库 theorem。Lean core 本身不注册 selector；在本书 `import Mathlib`、因而传递导入 `Lean.LibrarySuggestions.Default` 的锁定环境中，注册的 selector 将 Sine Qua Non 结果与当前文件 theorem 交错。无论哪种环境，默认 Grind 核心都不扫描全库。

# `grind?` 输出脚本
%%%
tag := "ch11-s11"
%%%

```anchor grind_question
theorem grindQuestion (P Q : Prop) : P ∧ Q → Q ∧ P := by
  grind?
```

`grind?` 执行推理并提取更具体脚本。锁定例子建议 `grind only`。生成建议有 replay check，但某些 replay failure 只给 warning；看到 `Try this` 后仍要替换并独立重编译。

Trace 模式还可能在未解分支使用 `sorry` 展示脚本骨架。建议文本和无公理闭合不是一回事。

# Proof reconstruction
%%%
tag := "ch11-s12"
%%%

成功路径可以来自假设、定理实例、E-class merge、solver proof 和 case split。Grind 的 proof 数据是分散而增量的：事实携带 proof Expr，E-class 边保存等式 proof 或延迟 congruence 标记，solver 与实例化直接生成证明，split 保存分支组合所需结构。大 proof 可以抽成辅助声明以控制项大小，但辅助声明仍由 kernel 检查。

:::codeBox "pseudocode"
```
contradiction fact and its proof
→ follow E-class equality paths where needed
→ realize delayed congruence placeholders
→ reuse theorem-instance and solver proofs
→ combine split branches
→ assign original goal
```
:::

E-graph、matcher、scheduler 和 heuristics 都可以不受信；它们不能只返回“closed = true”。必须给后续 proof construction 足够的普通 Lean 证明数据。`Origin` 与 `SplitSource` 还服务 theorem tracking、诊断和脚本生成，但不是覆盖所有推理的统一证明 DAG。

# 有界性与失败含义
%%%
tag := "ch11-s13"
%%%

Grind 配置限制 splits、E-match rounds、generation、instances 和其它 counters。达到上限时的结论是“本次有界运行没有构造出 proof”，不是目标为假。

锁定版本的主要默认值如下；它们是版本事实，不是语义契约：

```table
- 界限
- 默认值
---
- `splits`
- 9
---
- `ematch`
- 5
---
- `gen` / `genLocal`
- 8 / 8
---
- `instances`
- 1000
---
- `ringSteps` / `ringMaxDegree`
- 100000 / 1024
---
- `acSteps`
- 1000
---
- 主循环 `maxIterationsDefault`
- 10000
```

这些局部计数器还要与全局 heartbeat、recDepth 分开理解。

```table
- 现象
- 检查项
---
- local forall 没实例化
- theorem 是否激活、pattern 头、generation、instance limit
---
- 等式没传播到应用
- 项是否 internalized、signature、preprocessing
---
- 算术事实不回写
- 对应 solver 是否开启、载体是否支持
---
- split 爆炸
- splits bound、是否有更强 lemma 避免枚举
---
- `+suggestions` 很慢
- LibrarySuggestions 是额外层，不是默认核心
```

# 信任账本与公理锥
%%%
tag := "ch11-s14"
%%%

```anchor grind_axiom_probe
#print axioms grindCongruence
#print axioms grindEMatch
#print axioms grindCooperation
```

锁定环境中三个 theorem 的公理锥均为 `[propext, Classical.choice, Quot.sound]`。这不是未来版本契约；它只说明这些具体 proofs 没有 tactic-specific“相信 Grind”公理。

```table
- 部件
- 出错后果
---
- preprocessing / E-graph / E-matching
- 漏事实、慢、生成坏 reconstruction data
---
- solvers / split heuristics
- 漏解、爆炸、产生不可检 proof
---
- proof data / construction
- 生成普通 proof Expr
---
- kernel
- 拒绝错误 Expr
```

# 源码纵切
%%%
tag := "ch11-s15"
%%%

:::codeBox "pseudocode"
```
Lean/Meta/Tactic/Grind/Main.lean       参数与初始化
Types.lean                              E-node/classes/queues/state
Simp.lean                               预处理
Core.lean                               merge 与 facts
EMatch.lean                             pattern 与实例化
Action.lean / Finish.lean               CPS 与总调度
Split.lean                              分支与 non-chronological backtracking（非时间顺序回溯，NCB）
Lean/Elab/Tactic/Grind/Main.lean        用户前端、+suggestions、grind?
Init/Grind/Config.lean                  当前默认 bounds
```
:::

先沿 `grindTrace` 追 local forall 的一次实例化，再沿 `grindSplit` 追一个分支。不要用一个“大而全”例子同时解释全部 solver。

# 练习
%%%
tag := "ch11-s16"
%%%

## 基础：画 E-classes
%%%
tag := "ch11-s17"
%%%

给定 `a=b`、terms `f a`、`f b`，画 merge 前后 classes 与 application signatures，并标出 congruence proof 的来源。

## 进阶：E-match modulo equality
%%%
tag := "ch11-s18"
%%%

为 pattern `f ?x = ?x` 和 equality `a=b` 枚举可能实例，说明 instance cache 应按什么数据去重。

## 进阶：分支隔离
%%%
tag := "ch11-s19"
%%%

实现两个分支各自 merge 同一对 classes 的 toy E-graph；故意共用 mutable state，构造兄弟分支污染，再改成 saved-state isolation。

## 挑战：最小饱和器
%%%
tag := "ch11-s20"
%%%

只支持常量、unary applications、equalities 和一条 forall rewrite。要求保存 merge reason，最终输出等式 proof，而不是 Bool。

# 本章边界
%%%
tag := "ch11-s21"
%%%

Grind 的所有计算仍在 Lean 进程内部，成功后重建 proof。下一章 `bv_decide` 把搜索推进到外部 CaDiCaL，并用 LRAT certificate 把结果带回；但 Lean 4.32.2 的最终 checker-equals-true premise又经过 `nativeEqTrue` axiom bridge，实际信任边界比“外部 solver 不可信、内核检查一切”更复杂。
