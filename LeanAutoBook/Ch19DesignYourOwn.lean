import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch19DesignYourOwn"

#doc (Manual) "第十九章 设计你自己的领域自动化" =>
%%%
file := "Ch19DesignYourOwn"
tag := "ch19-design-your-own"
%%%

*本章目标*：综合 Part III 介绍的各 tactic 设计模式，
给出"从需求到实现"的完整方法论——
如何选型、如何组合、如何测试、如何让用户扩展，
并通过一个完整的微型 tactic 示例串联全过程。

# 19.1 何时需要领域自动化
%%%
tag := "when-domain-automation"
%%%

不是每个重复操作都值得写 tactic。
判断标准是*重复度 × 出错率 × 受益人数*：

```
                 高出错率
                    │
          ③ 值得    │    ④ 必须
                    │
  ─────────────────┼──────────────── 高重复度
                    │
          ① 不值得  │    ② 考虑
                    │
                 低出错率
```

| 象限 | 例子 | 建议 |
|------|------|------|
| ① 低重复 × 低出错 | 偶尔用一次的代数化简 | 手写即可 |
| ② 高重复 × 低出错 | `simp` 已够用的化简 | 收集 `@[simp]` 引理 |
| ③ 低重复 × 高出错 | 复杂的 `norm_num` 扩展 | 写插件，但投入有限 |
| ④ 高重复 × 高出错 | 反复手拼非负性/单调性 | 必须自动化 |

`positivity`（第十四章）和 `gcongr`（第十六章）都诞生于象限 ④。

# 19.2 四种设计模式
%%%
tag := "four-design-patterns"
%%%

前几章的 tactic 可归纳为四种模式，复杂度依次递增：

## 模式 A：simp 引理集
%%%
tag := "pattern-a-simp"
%%%

不写新 tactic，只收集领域引理标注 `@[simp]`。

```
-- [示意] 为测度论收集 simp 引理
attribute [simp] MeasureTheory.Measure.map_apply
attribute [simp] MeasureTheory.Measure.restrict_apply

example (μ : Measure α) (s : Set α) (hs : MeasurableSet s) :
    μ.restrict s s = μ s := by simp [hs]
  -- ▸ simp 自动找到 restrict_apply 完成化简
```

*适用*：*等式化简*，引理方向明确（左→右）。
*局限*：不能搜索、不能结构分解、不能处理不等式。

## 模式 B：aesop 规则集
%%%
tag := "pattern-b-aesop"
%%%

声明规则集，注册 safe/unsafe 规则，让 aesop 搜索。

```
-- [示意] 为集合论推理定义规则集
declare_aesop_rule_sets [SetReasoning]

@[aesop safe apply (rule_sets := [SetReasoning])]
theorem inter_subset_left (s t : Set α) : s ∩ t ⊆ s := Set.inter_subset_left

@[aesop unsafe 70% apply (rule_sets := [SetReasoning])]
theorem subset_union_left (s t : Set α) : s ⊆ s ∪ t := Set.subset_union_left

macro "set_reason" : tactic =>
  `(tactic| aesop (rule_sets := [SetReasoning])
                   (config := { maxDepth := 10 }))
```

*适用*：*多步推理*，每步是已知引理的实例化。
*局限*：搜索空间指数增长；对结构化分解无能为力。

## 模式 C：递归分解（positivity 模式）
%%%
tag := "pattern-c-recursive"
%%%

递归遍历表达式结构，自底向上收集信息。

```
-- [示意] positivity 的核心递归骨架
partial def analyzeSign (e : Expr) : MetaM SignResult := do
  if let some r ← findHypothesis e then return r    -- ❶ 找假设
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b =>
    combineAdd (← analyzeSign a) (← analyzeSign b)  -- ❷ 递归 + 组合
  | HMul.hMul _ _ _ _ a b =>
    combineMul (← analyzeSign a) (← analyzeSign b)
  | HPow.hPow _ _ _ a n =>
    combinePow (← analyzeSign a) n                   -- ▸ 偶数幂→非负
  | _ => throwError "positivity: 无法分析 {e}"
```

*适用*：目标可*按表达式结构递归分解*，组合规则明确。
*局限*：只能处理预定义的构造子。

## 模式 D：完整决策过程
%%%
tag := "pattern-d-decision"
%%%

实现完整算法（如 `ring`、`omega`），架构三步：
① 解析 Lean Expr → 内部表示；② 运行判定算法；③ 构造证明项。
步骤 ③ 有两条路——*反射*（编码为可判定数据，用 `decide`，简单但慢）
和*逐步构造*（用 `mkApp` 等拼装，快但实现复杂）。

*适用*：有*完备判定算法*。*局限*：实现成本最高。

# 19.3 选型决策树
%%%
tag := "design-decision-tree"
%%%

```
你的目标是什么？
│
├─ 等式化简，引理方向明确？ → 模式 A（simp 引理集）
├─ 多步推理，每步是现成引理？ → 模式 B（aesop 规则集）
├─ 分析表达式结构？（符号、单调性）→ 模式 C（递归分解）
├─ 完备的判定过程？ → 模式 D（完整算法）
└─ 以上都不匹配？ → 组合多种模式（见 §19.6）
```

*经验法则*：先尝试最简单的模式。
simp 引理集够用就不要写递归分解——简单方案更容易维护。

# 19.4 完整示例：微型 `mono_add` tactic
%%%
tag := "mono-add-example"
%%%

设计一个小 tactic：给定 `a ≤ b`、`c ≤ d`，自动证明 `a + c ≤ b + d`。
属于模式 C（递归分解），但大幅简化。

## 第一步：明确边界
%%%
tag := "mono-add-boundary"
%%%

能处理：`a + c ≤ b + d`（上下文有 `a ≤ b` 和 `c ≤ d`）、
嵌套加法（递归）、自反 `a ≤ a`（`le_refl`）。
不处理：乘法/减法/除法单调性、需要 `linarith` 的间接推理。

## 第二步：核心递归
%%%
tag := "mono-add-core-recursion"
%%%

```
-- [示意] mono_add 核心逻辑
partial def proveLE (lhs rhs : Expr) : TacticM Expr := do
  -- ❶ 相等 → le_refl
  if ← isDefEq lhs rhs then
    mkAppM ``le_refl #[lhs]
  -- ❷ 加法 → 拆解两边
  else if let some (a, c) ← matchAdd lhs then
    if let some (b, d) ← matchAdd rhs then
      let hab ← proveLE a b       -- 递归证明 a ≤ b
      let hcd ← proveLE c d       -- 递归证明 c ≤ d
      mkAppM ``add_le_add #[hab, hcd]
    else searchHypothesis lhs rhs
  -- ❸ 回退 → 在上下文中搜索匹配假设
  else searchHypothesis lhs rhs
```

## 第三步：搜索假设与包装
%%%
tag := "mono-add-search-wrap"
%%%

```
-- [示意] 在上下文中查找 lhs ≤ rhs 的证明
def searchHypothesis (lhs rhs : Expr) : TacticM Expr := do
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    if let some (_, l, r) ← matchLE (← instantiateMVars decl.type) then
      if (← isDefEq l lhs) && (← isDefEq r rhs) then
        return decl.toExpr
  throwError "mono_add: 找不到 {lhs} ≤ {rhs} 的证明"
  -- ▸ 错误信息具体——告诉用户缺什么假设

-- [示意] 注册为 tactic
elab "mono_add" : tactic => withMainContext do
  let target ← getMainTarget
  match_expr target with
  | LE.le _ _ lhs rhs =>
    closeMainGoal `mono_add (← proveLE lhs rhs)
  | _ => throwError "mono_add: 目标不是 _ ≤ _ 形式"
```

## 第四步：测试
%%%
tag := "mono-add-testing"
%%%

```
-- [示意] 正例
example (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by mono_add
  -- ▸ 拆解加法，匹配 h1 和 h2

example (h1 : a ≤ b) (h2 : c ≤ d) (h3 : e ≤ f) :
    a + c + e ≤ b + d + f := by mono_add
  -- ▸ 递归拆解两层加法

example : a + c ≤ a + c := by mono_add
  -- ▸ le_refl 处理

-- [示意] 反例（应当失败并给出明确错误）
example (h1 : a ≤ b) : a * c ≤ b * c := by mono_add
  -- ✗ "mono_add: 找不到 a * c ≤ b * c 的证明"
```

# 19.5 错误信息设计
%%%
tag := "error-message-design"
%%%

好的错误信息是领域 tactic 的核心竞争力。
`tactic failed` 无法 debug；
`positivity: 无法分析 f x，f 不在已注册函数列表中` 就知道怎么修。

## 三层错误信息
%%%
tag := "three-layer-errors"
%%%

```
层次 1（必须）：说明失败位置
  "mono_add: 找不到 a ≤ b 的证明"

层次 2（推荐）：给出修复建议
  "mono_add: 找不到 a ≤ b 的证明，尝试在上下文中添加此假设"

层次 3（理想）：展示推理过程
  "mono_add: 分析 a + c ≤ b + d
     ├─ a ≤ b: 失败——上下文中未找到
     └─ c ≤ d: ✓ 已找到 (hcd : c ≤ d)"
```

用 `trace` 实现层次 3：

```
-- [示意] 用 trace 输出推理链
trace[mono_add] "分析 {lhs} ≤ {rhs}"
-- 用户用 set_option trace.mono_add true 查看
```

# 19.6 组合多种模式
%%%
tag := "combining-patterns"
%%%

实际的领域 tactic 常*混合使用*多种模式：

| 组合方式 | 例子 | 各模式分工 |
|---------|------|-----------|
| 递归 + simp 收尾 | `field_simp`（第十七章） | 模式 C 消分母 → 模式 A 化简 |
| 搜索 + 递归子程序 | `fun_prop`（第十五章） | 模式 B 选规则 → 模式 C 验证 |
| 前处理 + 核心算法 | `linarith`（第九章） | `push_neg` 标准化 → 模式 D 判定 |

*设计原则*：每种模式处理它擅长的部分，
通过管线（pipeline）串联，不要用一种模式硬撑所有场景。

# 19.7 可扩展性与性能
%%%
tag := "extensibility-performance"
%%%

## 让用户添加规则
%%%
tag := "user-extensibility"
%%%

好的领域 tactic 允许用户扩展，不需要改源码：

```
-- [示意] 方式 1：attribute 注册（模式 A/B）
initialize monoAddExt : SimpExtension ←
  registerSimpAttr `mono_add_lemma "Lemmas for mono_add"

@[mono_add_lemma]
theorem sub_le_sub_right (h : a ≤ b) (c : ℕ) : a - c ≤ b - c := ...

-- [示意] 方式 2：插件系统（模式 C）
@[positivity MyFunc]
def evalMyFunc : PositivityExt where
  eval {u α} _zα _pα (e : Q($α)) := do
    return .nonneg (← proveMyFuncNonneg e)

-- [示意] 方式 3：规则集（模式 B）
@[aesop safe apply (rule_sets := [SetReasoning])]
theorem my_new_set_lemma : ... := ...
```

模式 A/B 用 attribute 或规则集（零代价）；
模式 C/D 需要设计插件接口（需要定义返回类型和协议）。

## 索引而不是线性搜索
%%%
tag := "discr-tree-indexing"
%%%

当引理集增长到数百条时，线性遍历成为瓶颈。
用 `DiscrTree`（discrimination tree）做索引：

```
-- [示意]
-- ✗ 线性搜索——O(n) 遍历
def findLemma (target : Expr) (lemmas : Array Expr) : MetaM (Option Expr) := do
  for l in lemmas do
    if ← isDefEq (← inferType l) target then return some l
  return none

-- ✓ DiscrTree——O(log n) 查找
def findLemma' (target : Expr) (tree : DiscrTree Expr) : MetaM (Array Expr) :=
  tree.getMatch target
```

`simp`、`aesop`、`fun_prop` 都使用 `DiscrTree`。
*经验法则*：引理超过 20 条就用 `DiscrTree`。

# 19.8 常见失败模式
%%%
tag := "design-failure-modes"
%%%

## 失败 1：规则集污染
%%%
tag := "design-fail-rule-pollution"
%%%

```
-- [示意]
@[aesop safe apply (rule_sets := [MyDomain])]
theorem exists_of_ne_empty (h : s ≠ ∅) : ∃ x, x ∈ s := ...
  -- ✗ 几乎匹配所有 ∃ 目标，导致搜索爆炸
```

*修复*：宽泛引理标 `unsafe`，或提高匹配精确度。

## 失败 2：递归不终止
%%%
tag := "design-fail-nontermination"
%%%

```
-- [示意]
partial def analyze (e : Expr) : MetaM Result := do
  match_expr e with
  | f a => analyze a
  | _ => analyze e     -- ✗ 对同一个表达式无限递归！
```

*修复*：每个分支要么返回结果，要么对*严格更小*的子表达式递归。

## 失败 3：错误信息丢失
%%%
tag := "design-fail-error-swallowed"
%%%

```
-- [示意]
-- ✗ 吞掉原始错误
try doSomething
catch _ => throwError "myTactic failed"

-- ✓ 保留上下文
try doSomething
catch e => throwError "myTactic: 分析 {expr} 时失败：{e.toMessageData}"
```

## 失败 4：忽略 universe 多态
%%%
tag := "design-fail-universe-poly"
%%%

```
-- [示意]
def myLemma := @add_le_add Nat ...
  -- ✗ 硬编码 Nat，对 ℝ 等类型失败
  -- ✓ 修复：用 mkAppM 而非 mkApp，自动处理 universe 统一
```

# 19.9 设计清单
%%%
tag := "design-checklist"
%%%

动手写代码之前，逐项回答：

- *边界*：能处理什么？不能处理什么？（写下正例和反例）
- *选型*：模式 A/B/C/D？需要组合吗？
- *错误信息*：失败时用户看到什么？（至少层次 1）
- *可扩展性*：用户能否添加新规则？
- *性能*：引理集会增长到多大？（>20 条 → `DiscrTree`）
- *测试*：至少 3 个正例 + 2 个反例

# 19.10 与下一章的衔接
%%%
tag := "bridge-to-next-chapter"
%%%

本章讨论 *tactic 层面*的设计方法论。
下一章（第二十章）进入 *Part IV*，介绍反射证明模式——
把命题反射为可计算的布尔判定，用 `native_decide` 一步完成。

| | 模式 D（逐步构造） | 反射 |
|---|---|---|
| 证明构造 | 在 MetaM 中拼装 | 编译期求值 `decide` |
| 性能瓶颈 | 证明项大小 | 求值速度 |
| 典型代表 | `ring`、`omega` | `Decidable` 实例 |

如果判定算法可表达为 Lean 可计算函数，
反射往往比逐步构造简单得多——这是第二十章的主题。

# 19.11 练习
%%%
tag := "design-exercises"
%%%

## 练习 1（热身）：simp 引理集
%%%
tag := "design-exercise-1"
%%%

```
-- [可运行]
-- 为以下场景找到正确的 simp 引理，使 `simp [...]` 一步完成。
example (s t : Finset ℕ) : (s ∪ t).card ≤ s.card + t.card := by
  sorry -- 用 simp + 哪条引理？

example (s : Finset ℕ) : (s ∩ s) = s := by
  sorry -- 用 simp + 哪条引理？
```

## 练习 2（热身）：aesop 规则集
%%%
tag := "design-exercise-2"
%%%

```
-- [示意]
-- 为以下推理链设计 aesop 规则集。
-- 回答：哪些引理标 safe？哪些标 unsafe？优先级如何？
--
-- 推理链：h : x ∈ s, h2 : s ⊆ t  ⊢  x ∈ t ∪ u
--   步骤 1：由 h2 h 得 x ∈ t
--   步骤 2：由 mem_union_left 得 x ∈ t ∪ u
```

## 练习 3（debug）：修复错误信息
%%%
tag := "design-exercise-3"
%%%

```
-- [示意]
-- 以下 tactic 失败时用户看不到有用信息，找出问题并修复。
elab "bad_tactic" : tactic => do
  let target ← getMainTarget
  try
    let proof ← someFancyProof target
    closeMainGoal `bad_tactic proof
  catch _ =>
    throwError "bad_tactic failed"
-- 问题：____________
-- 修复：____________
```

## 练习 4（综合）：设计 `nontrivial_by` tactic
%%%
tag := "design-exercise-4"
%%%

```
-- 设计（不需要完整实现，写设计文档即可）：
-- 自动证明 Nontrivial α，即类型 α 至少有两个不同元素。
--
-- 回答：
-- 1. 属于哪种模式？（A/B/C/D）
-- 2. 核心策略？（搜索假设？分解类型结构？）
-- 3. 需要哪些引理？
-- 4. 失败时报什么错误？
-- 5. 用户如何为自定义类型扩展？
```

# 19.12 小结
%%%
tag := "design-summary"
%%%

| 模式 | 实现成本 | 能力 | 可扩展性 | 典型代表 |
|------|---------|------|---------|---------|
| A：simp 引理集 | 低 | 等式化简 | `@[simp]` | 领域 simp 集 |
| B：aesop 规则集 | 低–中 | 多步搜索 | `@[aesop]` | 集合论推理 |
| C：递归分解 | 中 | 结构分析 | 插件接口 | `positivity`、`fun_prop` |
| D：完整决策过程 | 高 | 完备判定 | 通常不可扩展 | `ring`、`omega` |

*核心原则*：

- *先简单后复杂*——能用 simp 集解决的不要写递归分解
- *错误信息即文档*——用户最常看到的不是 docstring，而是报错
- *可扩展性是生命力*——`positivity` 因为有插件系统才能覆盖上百种函数
- *组合优于重造*——利用已有的 simp/aesop/linarith 作为子程序

下一章进入 Part IV：反射证明模式。
