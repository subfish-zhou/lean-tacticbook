import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch21Performance"

#doc (Manual) "第二十一章 性能工程" =>
%%%
file := "Ch21Performance"
tag := "ch21-performance"
%%%

*本章目标*：学会在 Lean 4 中诊断和解决常见的证明性能问题。

当 `decide` 超时、`simp` 跑了几秒钟、或整个文件编译卡住时，
你需要的不是换一个 tactic，而是*找到瓶颈在哪里*。
本章提供从普通用户到 tactic 作者的分层诊断方法。

不要过早优化。大部分证明不需要性能调优。
只有当编译*确实变慢*（heartbeats 超限、IDE 卡顿）时才需要本章的工具。
先写对，再写快。

*本章结构——三层递进*：
- *第一层（21.1–21.4）：普通用户排障*——profiler 定位、`simp?` → `simp only`、避免暴力 `decide`。大部分读者只需要这一层。
- *第二层（21.5）：常见瓶颈模式*——typeclass 爆炸、coercion 链、unification 超时。遇到深层性能问题时再来查阅。
- *第三层（21.6）：tactic 作者专属*——MetaM 缓存、`isDefEq` 控制、proof term 体积。仅面向编写自定义 tactic 的开发者。

# 第一层：普通用户排障
%%%
tag := "tier1-user-troubleshooting"
%%%

# 21.1 性能模型：时间花在哪里
%%%
tag := "performance-model"
%%%

一个 `by ...` 证明从输入到内核接受，经历三个阶段：

```
源码 ──→ ❶ elaboration ──→ ❷ tactic 执行 ──→ ❸ 内核验证 ──→ 通过
         (语法 → Expr)     (Expr → 证明项)     (检查证明项)
```

- 阶段：❶ elaboration —— 主要开销：type class synthesis、unification —— 典型瓶颈：深层 typeclass 层级、高阶 unification
- 阶段：❷ tactic 执行 —— 主要开销：`simp` 重写、`aesop` 搜索 —— 典型瓶颈：引理集过大、搜索空间爆炸
- 阶段：❸ 内核验证 —— 主要开销：检查最终证明项 —— 典型瓶颈：证明项过大（`decide` 展开、`simp` 冗长项）

*关键认知*：大部分"慢证明"的瓶颈在 ❷，
但 ❸ 也可能成为瓶颈——尤其是反射证明生成的巨大证明项。

# 21.2 Heartbeats：平台无关的计算量度量
%%%
tag := "heartbeats"
%%%

Lean 用 *heartbeats* 度量计算量——每次内核归约或 MetaM 操作消耗若干 heartbeats，
与 CPU 速度无关，保证同一证明在不同机器上给出一致的度量。

```
-- [可运行] 查看实际消耗
set_option profiler true in
theorem ex1 : (List.range 100).length = 100 := by decide
-- ▸ profiler 输出中包含 heartbeats 消耗

-- [示意] 加倍预算——应急手段，不是长期方案
set_option maxHeartbeats 400000 in  -- 默认 200000
theorem slow_thm : ... := by ...

-- [示意] 无限制——**仅限短暂调试，绝对不能提交到代码库**
set_option maxHeartbeats 0 in
-- ▸ maxHeartbeats 0 关闭了所有超时保护
-- ▸ 在 CI 中可能导致编译永远不结束
-- ▸ 调试完毕后必须删除此行，然后优化证明本身
```

*Mathlib 的 heartbeats 纪律*：默认 200000（约 1-2 秒），
PR 不应需要提高预算。如果 tactic 太慢，优化证明而非加预算。
heartbeats 预算是*质量门禁*——迫使开发者写高效的证明。

*注意*：`maxHeartbeats 0` 不是"让证明跑完"，而是"允许无限循环"。
它只能用于*调试时短暂开启*，帮你看到完整的 profiler/trace 输出。
找到瓶颈后，必须删除它并优化证明——它不是修复方案。

# 21.3 诊断工具箱
%%%
tag := "diagnostic-toolbox"
%%%

## profiler：整体耗时
%%%
tag := "profiler"
%%%

```
-- [可运行] 开启 profiler
set_option profiler true in
theorem my_thm : ∀ n : ℕ, n + 0 = n := by
  intro n; simp
-- ▸ 输出形如：
-- elaboration of my_thm took 12.3ms
-- typecheck of my_thm took 0.8ms
```

*第一步永远是 profiler*——先定位是哪个声明慢，再深入分析。

## trace：细粒度追踪
%%%
tag := "trace"
%%%

```
-- [示意] 追踪 simp 的每一步重写
set_option trace.Meta.Tactic.simp.rewrite true in
theorem ex2 : 0 + n = n := by simp
-- ▸ [Meta.Tactic.simp.rewrite] Nat.zero_add:1000, 0 + n ==> n

-- [示意] 追踪 type class synthesis
set_option trace.Meta.synthInstance true in
-- ▸ 显示 typeclass 搜索树，包括尝试和回溯

-- [示意] 追踪 unification
set_option trace.Meta.isDefEq true in
-- ▸ 显示每次 definitional equality 检查
```

*常用 trace 选项速查*：

- `trace.Meta.Tactic.simp.rewrite`：simp 应用了哪些引理
- `trace.Meta.Tactic.simp.discharge`：simp 的 discharge 尝试
- `trace.Meta.synthInstance`：typeclass synthesis 过程
- `trace.Meta.isDefEq`：unification 过程（*输出极大，慎用*）
- `trace.profiler.threshold`：只显示超过阈值的步骤

*二分定位*：profiler → 哪个 theorem 慢 → 逐行 sorry → 哪行 tactic 慢 → trace 深入。

# 21.4 优化 simp
%%%
tag := "optimizing-simp"
%%%

`simp` 是最常见的性能瓶颈来源——功能强大，也最容易被滥用。

## 全局 simp vs simp only
%%%
tag := "simp-vs-simp-only"
%%%

```
-- [示意] ❌ 全局 simp——加载所有 @[simp] 引理
simp
-- ▸ Mathlib 环境下 @[simp] 引理有数千条
-- ▸ 复杂度 ≈ O(子表达式数 × 引理数 × 重写轮数)

-- [示意] ✅ simp only——只用必要的引理
simp only [Nat.add_zero, Nat.mul_one]
-- ▸ 引理集从数千条缩减到 2 条
```

## simp? 工作流
%%%
tag := "simp-question-workflow"
%%%

```
-- [示意] 开发时的最佳实践
-- ❶ 先用 simp 探索（开发阶段）
-- ❷ 用 simp? 获取实际使用的引理列表
-- ❸ 替换为 simp only [...]（提交前）

example : 0 + n + 0 = n := by
  simp?
  -- ▸ 建议: simp only [Nat.zero_add, Nat.add_zero]
```

## 其他 simp 调优
%%%
tag := "simp-other-tuning"
%%%

```
-- [示意] 关闭 discharge（simp 不尝试放电侧条件）
simp (config := { decide := false })

-- ❌ @[simp] 同时标记 a = b 和 b = a → 无限循环
-- ✓ @[simp] 引理应保证重写方向一致（左边"更复杂"）
```

# 第二层：常见瓶颈模式
%%%
tag := "tier2-bottleneck-patterns"
%%%

以下内容面向遇到深层性能问题的用户。如果第一层的 `simp only` 和 profiler 已经解决了你的问题，可以跳过本节。

# 21.5 优化 Unification 和 Elaboration
%%%
tag := "optimizing-unification"
%%%

## 高阶 unification
%%%
tag := "higher-order-unification"
%%%

```
-- [示意] ❌ 让 Lean 推断太多类型参数
exact some_very_polymorphic_lemma
-- ▸ 最坏情况下 unification 是不可判定的

-- [示意] ✅ 显式提供关键类型参数
exact @some_lemma ℝ _ _ a b
-- ▸ @ 关闭隐式参数，_ 让 Lean 推断简单的 typeclass 参数
```

## typeclass synthesis 爆炸
%%%
tag := "typeclass-explosion"
%%%

```
-- [示意]
-- 深层实例链：Ring ℝ → AddCommMonoid ℝ → AddMonoid ℝ → ...
-- ▸ 搜索树可能指数级增长

-- ✅ 策略 1：提供局部实例
have inst : Ring ℝ := inferInstance
-- ▸ 后续 tactic 直接用 inst，不再搜索

-- ✅ 策略 2：控制搜索深度
set_option synthInstance.maxSize 256 in  -- 默认 128
```

*coercion 链*：`ℕ → ℤ → ℚ → ℝ` 的隐式转换触发多层 synthesis。
用 `(↑n : ℝ)` 显式标注最终类型，或在证明开头 `push_cast`。

# 第三层：tactic 作者专属
%%%
tag := "tier3-tactic-authors"
%%%

以下内容仅面向*编写自定义 tactic 的开发者*。普通证明用户可以跳过 21.6。

# 21.6 优化 MetaM 端代码
%%%
tag := "optimizing-metam"
%%%

编写自定义 tactic 时，MetaM 端代码质量直接影响性能。

## 缓存与避免重复
%%%
tag := "caching-avoid-duplication"
%%%

```
-- [示意] ❌ 重复调用
let t1 ← goal.getType
doSomething t1
let t2 ← goal.getType        -- 浪费

-- [示意] ✅ 缓存
let target ← goal.getType
doSomething target
doSomethingElse target
```

## 避免不必要的 whnf
%%%
tag := "avoid-unnecessary-whnf"
%%%

```
-- [示意] ❌ whnf 可能展开大量定义
let t ← whnf (← goal.getType)
-- ▸ whnf 递归展开直到头部是构造子——代价可能很高

-- [示意] ✅ 用 matchApp? 等结构化匹配代替
let target ← goal.getType
if let some (f, args) ← matchApp? target then ...
-- ▸ 只检查头部函数，不做深层展开
```

## 控制 isDefEq
%%%
tag := "control-isdefeq"
%%%

```
-- [示意] isDefEq 是 MetaM 中最昂贵的操作之一
-- ❌ 盲目尝试
for lemma in lemmas do
  if ← isDefEq lemmaConcl target then return lemma

-- ✅ 廉价预筛选 + 精确匹配
for lemma in lemmas do
  if quickCheck lemma target then       -- 头符号匹配
    if ← isDefEq lemmaConcl target then return lemma
```

*注意*：`isDefEq` 有*副作用*——它会给 metavariable 赋值。
即使最终不用该引理，赋值已经发生。
用 `withoutModifyingState` 隔离探索性调用。

# 21.7 编译时间 vs 运行时间
%%%
tag := "compile-vs-runtime"
%%%

Lean 同时承担*证明检查器*和*编程语言*双重角色，
有两种完全不同的性能关注维度。

- 关注对象 —— 编译时间：tactic 执行速度 —— 运行时间：编译后程序速度
- 优化手段 —— 编译时间：`simp only`、类型标注、缓存 —— 运行时间：算法选择、内联、尾递归
- 度量工具 —— 编译时间：heartbeats、profiler —— 运行时间：基准测试、`timeit`
- 主要场景 —— 编译时间：数学证明库（Mathlib） —— 运行时间：程序验证、可执行代码

```
-- [示意] #eval vs #reduce 的区别
#eval  (List.range 10000).length  -- 快：编译后执行
#reduce (List.range 10000).length -- 极慢：内核归约（展开每一步）
-- ▸ 除非需要看内核归约的中间步骤，否则永远用 #eval
```

# 21.8 证明项大小与增量编译
%%%
tag := "proof-term-size"
%%%

## 证明项膨胀
%%%
tag := "proof-term-bloat"
%%%

```
-- [示意] simp 生成的证明项可能非常大
-- 每一步重写记录：应用的引理、类型参数实例化、局部变量
-- 100 步重写可能生成数万个 Expr 节点
-- decide 更严重：证明项包含完整的归约过程
```

*缓解策略*：
- `native_decide` 生成更紧凑的证明项（不记录归约过程）
- 拆分大证明为多个中间引理（每段 simp 链较短）
- 用引理推理代替暴力计算（`simp [List.length_range]` 优于 `decide`）

证明项大小影响 `.olean` 文件大小，
进而影响所有下游文件的加载时间。

## 增量编译与文件组织
%%%
tag := "incremental-compilation"
%%%

```
-- [示意] ❌ 粗粒度 import
import Mathlib               -- 加载整个 Mathlib

-- [示意] ✅ 细粒度 import
import Mathlib.Tactic.Ring   -- 只加载需要的模块
import Mathlib.Data.Nat.Basic
```

```
文件依赖图：
        A.lean
       / \
      B    C        ← B 和 C 可以并行编译
       \ /
        D.lean      ← D 必须等 B 和 C 都编译完
```

*优化原则*：减少文件间依赖；把慢定义和快定义分开文件；
用 `lake build +A +B` 并行编译无依赖模块。

Mathlib 在 CI 中对每个 PR 测量编译时间差异，
显著增加编译时间的 PR 需要优化后再合并。

# 21.9 实战：优化一个慢证明
%%%
tag := "optimize-slow-proof"
%%%

## 原始版本（慢）
%%%
tag := "slow-version"
%%%

```
-- [示意]
set_option maxHeartbeats 800000 in  -- 需要 4 倍预算
theorem slow_example (a b c : ℕ) :
    (a + b) * c + 0 = c * a + c * b := by
  simp [Nat.add_mul, Nat.mul_comm, Nat.add_comm, Nat.add_zero]
  ring
```

## 诊断过程
%%%
tag := "diagnosis-process"
%%%

```
-- [示意]
-- ❶ profiler → simp 占 90% 时间
-- ❷ trace.simp → Nat.mul_comm 导致循环（a*b → b*a → a*b）
-- ❸ 分析 → 只需 Nat.add_zero 消除 + 0，剩下交给 ring
```

## 优化版本（快）
%%%
tag := "fast-version"
%%%

```
-- [示意] 不需要额外 heartbeats
theorem fast_example (a b c : ℕ) :
    (a + b) * c + 0 = c * a + c * b := by
  simp only [Nat.add_zero]   -- 只消除 + 0
  ring                        -- ring 处理交换律和分配律
```

heartbeats 从 ~600000 降到 ~5000（100x 改善）。

*优化检查清单*：

```
□ profiler 定位瓶颈（simp？unification？typeclass？）
□ simp 瓶颈 → simp? → simp only
□ unification 瓶颈 → 添加类型标注
□ typeclass 瓶颈 → 缓存实例或限制搜索
□ decide 瓶颈 → native_decide 或引理推理
□ 优化后 heartbeats ≤ 200000？
```

# 21.10 失败模式汇总
%%%
tag := "performance-failure-modes"
%%%

## 失败 1：maxHeartbeats 军备竞赛
%%%
tag := "failure-heartbeats-arms-race"
%%%

```
-- [示意]
-- ❌ 每次超时就加 maxHeartbeats
set_option maxHeartbeats 400000 in   -- 第一次
set_option maxHeartbeats 800000 in   -- Lean 升级后又超时
set_option maxHeartbeats 1600000 in  -- 加了一条引理又超时
-- ✓ 正确做法：优化证明本身
```

## 失败 2：trace 输出导致 IDE 卡死
%%%
tag := "failure-trace-ide-hang"
%%%

```
-- [示意]
-- ❌ 在大文件上开 trace.Meta.isDefEq → 输出几十万行
-- ✓ 先用 sorry 缩小范围，只对单个 tactic 开 trace
```

## 失败 3：#reduce 代替 #eval
%%%
tag := "failure-reduce-vs-eval"
%%%

```
-- [示意]
#reduce (List.range 1000).length  -- ❌ 极慢：内核归约
#eval (List.range 1000).length    -- ✓ 瞬间：编译后执行
```

## 失败 4：无数据支撑的优化
%%%
tag := "failure-blind-optimization"
%%%

```
-- [示意]
-- ❌ "simp 可能慢，我全换成 simp only"
-- ❌ "加类型标注总没错"
-- ▸ 没有数据支撑的优化可能无效，还降低可读性
-- ✓ 先 profiler，再 trace，最后优化——data-driven
```

# 21.11 练习
%%%
tag := "performance-exercises"
%%%

## 练习 1（诊断）：读 profiler 输出
%%%
tag := "exercise-read-profiler"
%%%

以下 profiler 输出说明了什么？应该优先优化什么？

```
elaboration of slow_lemma took 3.2s
  tactic execution took 2.8s
    simp took 2.6s
  typecheck took 0.3s
```

*提示*：simp 占 81%——应优化 simp（`simp?` → `simp only`）。
typecheck 0.3s 也较高——可能是证明项过大，但优先处理 simp。

## 练习 2（设计）：分析性能权衡
%%%
tag := "exercise-performance-tradeoffs"
%%%

对以下场景，分析瓶颈在哪个阶段（elaboration / tactic / typecheck），
并建议优化方向：

```
(a) 用 decide 证明 100 以内所有素数的 Goldbach 猜想

(b) 在深层 typeclass 层级上使用 15 步 simp 链

(c) 自定义 tactic 在 MetaM 中对 200 个候选引理逐一尝试 isDefEq
```

*提示*：
(a) tactic（`decide` 穷举）+ typecheck（证明项大）→ `native_decide` 或拆引理。
(b) elaboration（typeclass）+ tactic（simp）→ 缓存实例，`simp only`。
(c) tactic（`isDefEq` 昂贵）→ 头符号预筛选，`withoutModifyingState` 隔离。

# 21.12 小结
%%%
tag := "performance-summary"
%%%

- `性能三阶段`：elaboration → tactic 执行 → 内核验证
- `heartbeats`：平台无关的计算量度量；默认 200000
- `profiler`：第一步永远是 profiler——先定位再优化
- `trace`：细粒度追踪 simp、typeclass、unification
- `simp only`：最常见的优化——限制引理集
- `类型标注`：减少 unification 和 typeclass 搜索
- `证明项大小`：影响 typecheck 和 .olean 文件大小
- `编译 vs 运行`：证明库关注编译时间，程序验证两者都关注
- `增量编译`：细粒度 import、合理的文件依赖图
- `优化原则`：data-driven：先度量，再优化
- `主要陷阱`：heartbeats 军备竞赛、trace 卡 IDE、盲目优化

*一句话总结*：性能优化的第一原则是*先度量，再行动*——
profiler 告诉你在哪里花时间，trace 告诉你为什么，然后才是对症下药。

*落地行动清单——按层级递进*：

1. *普通用户*（80% 的情况在这里解决）：
   - 证明慢了？开 `set_option profiler true`，找到最慢的那行。
   - `simp` 慢？用 `simp?` 拿到引理列表，替换为 `simp only [...]`。
   - `decide` 超时？换 `native_decide`，或用引理推理代替暴力穷举。
   - `maxHeartbeats` 只加不减？停下来优化证明本身。

2. *进阶用户*（typeclass / unification 瓶颈）：
   - 开 `trace.Meta.synthInstance` 看 typeclass 搜索树。
   - 给多态引理加 `@` 和显式类型参数。
   - coercion 链用 `push_cast` 或显式标注。

3. *tactic 作者*：
   - 缓存 `goal.getType` 结果、避免盲目 `whnf`。
   - `isDefEq` 前做头符号预筛选，探索性调用用 `withoutModifyingState` 隔离。

下一章讨论对接外部工具——当 Lean 内部 tactic 不够用时，
如何调用 SAT/SMT 求解器并安全地集成结果。
