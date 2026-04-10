import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch11Aesop"

#doc (Manual) "第十一章 aesop：可配置的搜索引擎" =>
%%%
file := "Ch11Aesop"
tag := "ch11-aesop"
%%%

*本章目标*：理解 `aesop` 的搜索架构，学会配置规则集、编写自定义规则，并能诊断搜索失败。

# 11.1 aesop 解决什么问题
%%%
tag := "aesop-what-it-solves"
%%%

`aesop`（Automated Extensible Search for Obvious Proofs）是 Lean 4 / Mathlib 中最灵活的自动化 tactic，实现*可配置的最佳优先搜索*在规则集上做前向/后向推理。

```
-- 逻辑推理：aesop 的主场
example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) (hp : P) : R := by
  aesop                       -- ▸ apply h2, apply h1, exact hp

-- 结构拆分 + 构造
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  aesop                       -- ▸ cases h → constructor → exact

example : List.length ([] : List Nat) = 0 := by
  aesop                       -- ▸ norm 阶段 simp 直接化简
```

*与 `simp` 的区别*：`simp` 是重写引擎（等式/iff 替换）；`aesop` 是搜索引擎（`intro`、`apply`、`cases`、`constructor` 等结构操作）。两者互补不互替。

> *类型标注提醒*：涉及 `Set`、`Finset` 等 typeclass 密集类型时，必须显式标注
> （如 `s t : Set α`），否则 elaboration 卡在 typeclass synthesis——这不是 aesop 的问题。

# 11.2 搜索架构
%%%
tag := "search-architecture"
%%%

aesop 对每个目标执行三阶段搜索：

1. *Normalization*：执行 `norm` 规则，将目标化为标准形式。
2. *Safe rules*：执行 `safe` 规则——保证不引入死路，直接应用不分支。
3. *Unsafe rules*：尝试 `unsafe` 规则，每条产生一个搜索分支。

```
目标: a ∈ s ∩ t → a ∈ s
  ├─ [norm] simp → 无变化
  ├─ [safe] intro h               ← 假设 h : a ∈ s ∩ t
  │   └─ [safe] exact h.1 → ✅   ← And.left 取出
  └─ (unsafe 分支未展开)
```

*最佳优先*：unsafe 规则有 `successProbability` 得分，优先队列展开高分分支。
*有界搜索*：`maxRuleApplications`（默认 200）和 `maxDepth`（默认 30）防止爆炸。

# 11.3 规则类型
%%%
tag := "rule-types"
%%%

## `@[aesop norm]` — 规范化规则
%%%
tag := "aesop-norm-rules"
%%%

每个搜索节点开头运行，将目标化为标准形式：

```
@[aesop norm simp]
theorem List.length_nil : ([] : List α).length = 0 := by simp
-- ▸ 效果 = 每个节点插入 simp only [List.length_nil]

@[aesop norm tactic (rule_sets := [Arith])]
def omega_norm : Aesop.RuleTac := fun _ => `(tactic| omega)
-- ▸ norm 阶段尝试 omega
```

## `@[aesop safe]` — 安全规则
%%%
tag := "aesop-safe-rules"
%%%

适用时直接执行，不分支不回溯：

```
@[aesop safe apply]
theorem And.intro {a b : Prop} (ha : a) (hb : b) : a ∧ b := ⟨ha, hb⟩
-- ▸ 目标 P ∧ Q 时立即 apply

@[aesop safe forward]
theorem Set.mem_of_mem_inter_left : a ∈ s ∩ t → a ∈ s := And.left
-- ▸ 假设有 h : a ∈ s ∩ t 时，自动添加 a ∈ s
```

> *经验法则*：只有*必定不丢失信息*时才标 `safe`。

优先级用整数标注（越大越先）：`@[aesop safe 100 apply]`。

## `@[aesop unsafe N%]` — 不安全规则
%%%
tag := "aesop-unsafe-rules"
%%%

可能失败，需要回溯。百分比影响搜索优先级：

```
@[aesop unsafe 70% apply]
theorem mem_inter_iff : a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t := Iff.rfl
-- ▸ 70% 优先于 50% 展开

@[aesop unsafe 20% apply]
theorem Classical.em (p : Prop) : p ∨ ¬p := ...
-- ▸ 低优先级后备
```

百分比指南：80–100% 几乎总有效；50–80% 通常有效；20–50% 偶尔有效；<20% 极少有效。

# 11.4 规则动作
%%%
tag := "rule-actions"
%%%

| 动作 | 说明 | 用途 |
|------|------|------|
| `apply` | apply 目标 | 后向推理 |
| `forward` | 从假设推新事实，*保留*原假设 | 丰富上下文 |
| `destruct` | 从假设推新事实，*消耗*原假设 | 避免重复 |
| `cases` | 对项做 cases | 枚举拆分 |
| `simp` | simp 化简 | 仅 `norm` |
| `tactic` | 执行任意 tactic | 灵活慎用 |

```
@[aesop safe apply]
theorem Or.inl : a → a ∨ b := fun h => .inl h
-- ▸ 目标 a ∨ b → 变为 a

@[aesop unsafe 50% tactic]
def try_ring : Aesop.RuleTac := fun _ => `(tactic| ring)
-- ▸ 搜索中尝试 ring，失败回溯
```

# 11.5 配置 aesop
%%%
tag := "configuring-aesop"
%%%

## 内联配置
%%%
tag := "inline-configuration"
%%%

```
-- 限制搜索深度
aesop (config := { maxDepth := 10 })

-- 临时添加/移除规则
aesop (add safe apply my_lemma)
aesop (add unsafe 60% apply another_lemma)
aesop (erase Aesop.BuiltinRules.assumption)
```

## 规则集
%%%
tag := "rule-sets"
%%%

```
declare_aesop_rule_sets [MyDomain]           -- 1. 声明

@[aesop safe apply (rule_sets := [MyDomain])]
theorem my_key_lemma : ... := ...             -- 2. 注册

example : ... := by
  aesop (rule_sets := [MyDomain])             -- 3. 使用

macro "my_aesop" : tactic =>
  `(tactic| aesop (rule_sets := [MyDomain]))  -- 4. 简化调用
```

## 常用配置选项摘录
%%%
tag := "common-config-options"
%%%

| 选项 | 默认值 | 说明 |
|------|--------|------|
| `maxDepth` | 30 | 搜索树最大深度 |
| `maxRuleApplications` | 200 | 规则应用次数上限 |
| `enableSimp` | true | norm 阶段是否运行 simp |
| `terminal` | false | true = 必须完全关闭目标 |

> *`terminal` 模式*：生产代码推荐开启——aesop 无法关闭目标就报错，避免"部分成功"隐患。

# 11.6 案例：Finset 的 aesop 规则集
%%%
tag := "finset-rule-set-example"
%%%

```
-- Mathlib 中 Finset 规则（简化版）
@[aesop safe apply (rule_sets := [Finset])]
theorem Finset.mem_union : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t := ...

@[aesop safe apply (rule_sets := [Finset])]
theorem Finset.mem_inter : a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t := ...

@[aesop unsafe 70% apply (rule_sets := [Finset])]
theorem Finset.subset_union_left : s ⊆ s ∪ t := ...

-- 使用效果
example (h : a ∈ s) : a ∈ s ∪ (t ∩ u) := by
  aesop (rule_sets := [Finset])
  -- 1. [safe]   mem_union.mpr → 目标: a ∈ s ∨ a ∈ t ∩ u
  -- 2. [unsafe] Or.inl        → 目标: a ∈ s
  -- 3. [safe]   exact h       → ✅
```

# 11.7 调试 aesop
%%%
tag := "debugging-aesop"
%%%

## trace 选项
%%%
tag := "trace-options"
%%%

```
set_option trace.aesop true in       -- 完整搜索过程
set_option trace.aesop.ruleSet true in -- 只看规则集
```

> trace option 名称随版本变化。报 "unknown option" 时试 `trace.aesop` 查看子选项。

## 阅读错误信息
%%%
tag := "reading-error-messages"
%%%

```
aesop: failed to prove the goal after exhaustive search.
  Searched 47 nodes, max depth reached: 15
  Final goals:  ⊢ a ∈ t
```

- *Searched N nodes*：太少 = 规则不够，太多 = 规则太泛
- *max depth reached*：考虑增加 `maxDepth`
- *Final goals*："差了哪一步"的线索

## `aesop?` — 提取证明脚本
%%%
tag := "aesop-suggest"
%%%

```
example {α : Type} (a : α) (s t : Set α) (h : a ∈ s) : a ∈ s ∪ t := by
  aesop?   -- ▸ Try this: exact Set.mem_union_left t h
```

输出是*稳定的手写证明*。推荐替换场景：编译速度、跨版本稳定、可读性。

# 11.8 常见失败模式
%%%
tag := "ch11-common-failure-patterns"
%%%

## 失败 1：类型信息不足
%%%
tag := "failure-insufficient-type-info"
%%%

```
-- ❌ a, s, t 类型未知
-- example (a : _) (s t : _) (h : a ∈ s) : a ∈ s ∪ t := by aesop
-- ✅ 显式标注
example {α : Type} (a : α) (s t : Set α) (h : a ∈ s) : a ∈ s ∪ t := by aesop
```

*诊断*：目标简单但失败 → 检查 metavariable（`?m`）或未解析 typeclass。

## 失败 2：缺少关键规则
%%%
tag := "failure-missing-rules"
%%%

```
-- ❌ 默认规则集没有 Nat.add_comm
-- example (n m : Nat) : n + m = m + n := by aesop
-- ✅ 方案 A：aesop (add safe simp Nat.add_comm)
-- ✅ 方案 B（更好）：这本来就不是 aesop 的活 → omega
```

*诊断*：查 Final goals → 确认缺什么引理 → `add` 补充。
但更重要的判断是：*这个目标是否属于 aesop 的能力范围？* 等式推理、算术、重写链等目标即使补了规则也事倍功半——应直接换用 `omega`、`ring`、`simp` 等专用 tactic。

## 失败 3：搜索空间爆炸
%%%
tag := "failure-search-space-explosion"
%%%

```
-- ❌ 超时
-- example : deeply_nested_prop := by aesop
-- ✅ 手动 have 关键步骤 + 限制深度
-- example : deeply_nested_prop := by
--   have key := key_lemma
--   aesop (config := { maxDepth := 10 })
```

*诊断*：大量节点仍失败 → unsafe 分支太多。
策略：`have` 中间步骤 / 降低 `maxRuleApplications` / `erase` 不相关规则。

## 失败 4：safe 规则过度激进
%%%
tag := "failure-safe-rules-too-aggressive"
%%%

```
-- ❌ destruct 消耗假设丢失信息
-- @[aesop safe destruct]
-- theorem bad : P ∨ Q → True := fun _ => trivial
-- ✅ 改为 forward 或降级 unsafe
```

*诊断*：假设充足仍失败 → `trace.aesop` 检查 safe 规则是否"吃掉"有用假设。

## 失败 5：forward 规则循环
%%%
tag := "failure-forward-rule-cycles"
%%%

```
-- ❌ 互相触发产生无限新假设
-- @[aesop safe forward] theorem fwd  : R a b → R b a := ...
-- @[aesop safe forward] theorem back : R b a → R a b := ...
-- ✅ 只保留一个方向，或改用 destruct
```

*诊断*：超时或 `maxRuleApplications` 耗尽 → 检查 forward 规则是否形成环。

# 11.9 局限与最佳实践
%%%
tag := "limitations-and-best-practices"
%%%

| 不擅长 | 原因 | 替代 |
|--------|------|------|
| 等式推理 | 不做重写链 | `simp`、`ring` |
| 线性算术 | 不做数值决策 | `omega`、`linarith` |
| 深度组合 | 搜索爆炸 | 手动分步 + aesop 收尾 |
| 高阶 unification | 只做一阶匹配 | `exact?`、手动 `apply` |

*最佳实践*——"人工搭骨架，aesop 填细节"：

```
theorem complex_theorem : P := by
  obtain ⟨a, ha⟩ := existence_lemma    -- 人工：关键存在性
  have key : Q := crucial_step a ha     -- 人工：关键步骤
  aesop                                  -- aesop：收尾
```

# 11.10 与其他 tactic 组合
%%%
tag := "combining-with-other-tactics"
%%%

```
-- simp + aesop：先化简再搜索
simp only [some_def]; aesop

-- aesop 作为后备
first | decide | aesop

-- 分工
constructor
· omega    -- 算术
· aesop    -- 逻辑
```

# 11.11 小结
%%%
tag := "ch11-summary"
%%%

| 概念 | 关键点 |
|------|--------|
| 搜索架构 | norm → safe → unsafe 三阶段最佳优先搜索 |
| 规则类型 | `norm`（规范化）、`safe`（确定性）、`unsafe`（分支） |
| 动作类型 | `apply`、`forward`、`destruct`、`cases`、`simp`、`tactic` |
| 规则集 | `declare_aesop_rule_sets` + `rule_sets` |
| 调试 | `trace.aesop.*`、`aesop?`、Final goals |

# 练习
%%%
tag := "ch11-exercises"
%%%

## 练习 11.1（基础）：aesop 能力边界
%%%
tag := "exercise-11-1"
%%%

判断以下哪些 `aesop` 可以直接证明，不行的给出替代方案：

```
-- (a) 集合成员
example {α : Type} (a : α) (s t : Set α) (h : a ∈ s ∩ t) : a ∈ s := by sorry
-- (b) 算术
example (n : Nat) : n + 0 = n := by sorry
-- (c) 逻辑链
example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) (hp : P) : R := by sorry
-- (d) 列表长度
example : (List.cons 1 [2, 3]).length = 3 := by sorry
```

> *提示*：(a)(c) 是 aesop 主场；(b) 用 `omega`；(d) 看 norm 阶段是否化简。

## 练习 11.2（进阶）：自定义规则集
%%%
tag := "exercise-11-2"
%%%

为图论领域定义 aesop 规则集。将 `symm` 注册为 safe forward，添加 transitivity 作为 unsafe 70%。
思考：symm 作为 safe forward 会不会循环？（参考 11.8 失败 5）
*核心教训*：规则工程（选什么规则、标什么优先级、用什么动作）往往比搜索参数调优更关键——一条错误的 safe forward 就能让整个搜索失控。

## 练习 11.3（诊断）：修复失败
%%%
tag := "exercise-11-3"
%%%

```
-- 为什么失败？用 trace.aesop 诊断，用 (add ...) 修复
-- example {α : Type} (P Q : α → Prop) (a : α)
--     (h1 : ∀ x, P x → Q x) (h2 : P a) : Q a := by aesop
```

## 练习 11.4（实战）：aesop? 替换
%%%
tag := "exercise-11-4"
%%%

在你的项目中用 `aesop?` 提取手写证明，比较编译速度，记录哪些值得保留、哪些应替换。

下一章：`grind`——E-matching 和 congruence closure。
