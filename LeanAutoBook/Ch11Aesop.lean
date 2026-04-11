import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch11Aesop"

#doc (Manual) "aesop：可配置的启发式搜索" =>
%%%
file := "Ch11Aesop"
tag := "ch11-aesop"
%%%

**本章目标**：前半章掌握 `aesop` 家族的用法、规则配置与调试技巧；后半章从 Aesop 真实源码层面拆解完整实现——搜索树数据结构、best-first 主循环、三类规则系统、规范化阶段、脚本生成——面向想深入理解内部机制的读者。

`aesop`（Automated Extensible Search for Obvious Proofs）是 Lean 4 / Mathlib 中最灵活的自动化 tactic，实现**可配置的最佳优先搜索**在规则集上做前向/后向推理。作者是 Jannis Limperg，作为 Mathlib 的依赖发布，源码在 `.lake/packages/aesop/` 中。

**定位说明**：aesop 的设计哲学与 `simp`、`omega` 有本质不同。`simp` 是确定性的重写引擎——给定引理集和表达式，重写路径基本唯一。`omega` 是判定过程——在线性算术的完备片段内保证有解就找到。`aesop` 既不是确定性重写，也不是完备判定——它是一个**可配置的启发式搜索框架**，用 best-first search 在用户定义的规则空间中寻找证明。它的核心价值不在于算法的数学深度，而在于将搜索策略、规则管理、proof reconstruction 三者精巧地组合成一个可扩展的自动化平台。

# 用法详解
%%%
tag := "ch11-usage"
%%%

## aesop 解决什么问题
%%%
tag := "ch11-what-aesop-solves"
%%%

aesop 擅长**逻辑推理**和**结构操作**——`intro`、`apply`、`cases`、`constructor`、`assumption` 等组合搜索：

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

**与 `simp` 的区别**：`simp` 是重写引擎（等式/iff 替换）；`aesop` 是搜索引擎（结构操作组合）。两者互补不互替。

**类型标注提醒**：涉及 `Set`、`Finset` 等 typeclass 密集类型时，必须显式标注（如 `s t : Set α`），否则 elaboration 卡在 typeclass synthesis——这不是 aesop 的问题。

## aesop 不能做什么
%%%
tag := "ch11-aesop-limitations"
%%%

aesop 是启发式搜索，不是决策过程。即使目标在当前规则集下"理论上可证"，aesop 也可能找不到证明：

- **等式推理**：不做重写链——用 `simp`、`ring`
- **线性算术**：不做数值决策——用 `omega`、`linarith`
- **深度组合**：搜索爆炸——手动分步 + aesop 收尾
- **高阶 unification**：只做一阶匹配——用 `exact?`、手动 `apply`

搜索失败通常不是 bug，而是需要调整规则集或搜索参数。

## aesop 家族：aesop / aesop? / aesop\_nonterminal
%%%
tag := "ch11-aesop-family"
%%%

| 变体 | 行为 |
|------|------|
| `aesop` | 默认非 terminal——未完全证明时返回剩余目标 |
| `aesop?` | 同 `aesop`，但输出 `Try this:` 脚本建议 |
| `aesop (config := { terminal := true })` | 必须完全证明，否则报错 |

**`aesop?` 的用途**：生成可复制的 tactic 脚本。输出是**稳定的手写证明**，适合替换到正式代码中——编译更快、跨版本稳定、可读性更好。

## 规则类型：norm / safe / unsafe
%%%
tag := "ch11-rule-types"
%%%

aesop 对每个目标执行三阶段搜索：

1. **Normalization**：执行 `norm` 规则，将目标化为标准形式
2. **Safe rules**：执行 `safe` 规则——匹配即 commit，不分支不回溯
3. **Unsafe rules**：尝试 `unsafe` 规则，每条产生一个搜索分支

```
目标: a ∈ s ∩ t → a ∈ s
  ├─ [norm] simp → 无变化
  ├─ [safe] intro h               ← 假设 h : a ∈ s ∩ t
  │   └─ [safe] exact h.1 → ✅   ← And.left 取出
  └─ (unsafe 分支未展开)
```

### `@[aesop norm]` — 规范化规则
%%%
tag := "ch11-norm-rules"
%%%

每个搜索节点开头运行，将目标化为标准形式。典型构建器是 `simp` 和 `unfold`：

```
@\[aesop norm simp]
theorem List.length_nil : ([] : List α).length = 0 := by simp
-- ▸ 效果 = 每个节点插入 simp only [List.length_nil]

@\[aesop norm unfold]
def myDef := 42
-- ▸ norm 阶段展开 myDef
```

优先级用整数标注——penalty 越小越先执行。penalty < 0 的 norm 规则在 simp 之前运行，penalty ≥ 0 的在 simp 之后。

### `@[aesop safe]` — 安全规则
%%%
tag := "ch11-safe-rules"
%%%

适用时直接 commit——**不分支、不回溯**。这是 aesop 最重要的搜索空间裁剪机制：

```
@\[aesop safe apply]
theorem And.intro {a b : Prop} (ha : a) (hb : b) : a ∧ b := ⟨ha, hb⟩
-- ▸ 目标 P ∧ Q 时立即 apply

@\[aesop safe forward]
theorem Set.mem_of_mem_inter_left : a ∈ s ∩ t → a ∈ s := And.left
-- ▸ 假设有 h : a ∈ s ∩ t 时，自动添加 a ∈ s
```

**经验法则**：只有**必定不丢失信息**时才标 `safe`。优先级用整数标注（penalty 越小越先执行）：`@\[aesop safe 1 apply]`。

**术语澄清**：safe / unsafe 的区别**不是**"这条规则逻辑上是否安全"——所有规则都是 sound 的。区别在于**搜索控制语义**：safe 意味着"采纳这一步几乎不会后悔"，unsafe 意味着"这一步有用但可能需要撤回"。

### `@[aesop unsafe N%]` — 不安全规则
%%%
tag := "ch11-unsafe-rules"
%%%

可能失败，需要回溯。百分比影响搜索优先级：

```
@\[aesop unsafe 70% apply]
theorem mem_inter_iff : a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t := Iff.rfl
-- ▸ 70% 优先于 50% 展开

@\[aesop unsafe 20% apply]
theorem Classical.em (p : Prop) : p ∨ ¬p := ...
-- ▸ 低优先级后备
```

百分比指南：80–100% 几乎总有效；50–80% 通常有效；20–50% 偶尔有效；<20% 极少有效。成功概率沿搜索路径**累乘**：根目标 100%，经过 `unsafe 80%` 变为 0.8，再经过 `unsafe 50%` 变为 0.4。

## 规则动作（Builder）
%%%
tag := "ch11-rule-builders"
%%%

构建器决定规则如何应用到目标或假设上：

| 构建器 | 行为 | 用途 |
|--------|------|------|
| `apply` | apply 定理到目标 | 后向推理 |
| `forward` | 从假设推新事实，**保留**原假设 | 丰富上下文 |
| `destruct` | 从假设推新事实，**消耗**原假设 | 避免重复 |
| `cases` | 对项做 cases | 枚举拆分 |
| `constructors` | 应用归纳类型的构造子 | 构造证明 |
| `simp` | 添加到 norm simp 集 | 仅 `norm` 阶段 |
| `unfold` | norm 阶段展开定义 | 仅 `norm` 阶段 |
| `tactic` | 执行任意 tactic | 灵活慎用 |
| `default` | 自动选择 | 省略构建器时的默认行为 |

`default` 构建器根据声明类型自动选择：归纳类型 → `constructors`；命题 → `apply`（safe/unsafe）或 `simp`（norm）。这就是为什么 `@\[aesop safe]` 不需要显式指定构建器。

```
@\[aesop safe apply]
theorem Or.inl : a → a ∨ b := fun h => .inl h

@\[aesop unsafe 50% tactic]
def try_ring : Aesop.RuleTac := fun _ => `(tactic| ring)
-- ▸ 搜索中尝试 ring，失败回溯
```

## 配置 aesop
%%%
tag := "ch11-config"
%%%

### 内联配置
%%%
tag := "ch11-inline-config"
%%%

```
-- 限制搜索深度
aesop (config := { maxRuleApplicationDepth := 10 })

-- 临时添加/移除规则
aesop (add safe apply my_lemma)
aesop (add unsafe 60% apply another_lemma)
aesop (erase Aesop.BuiltinRules.assumption)

-- simp 配置
aesop (simp_config := { decide := false })
```

### 规则集
%%%
tag := "ch11-rule-sets"
%%%

```
declare_aesop_rule_sets [MyDomain]           -- 1. 声明

@\[aesop safe apply (rule_sets := [MyDomain])]
theorem my_key_lemma : ... := ...             -- 2. 注册

example : ... := by
  aesop (rule_sets := [MyDomain])             -- 3. 使用

macro "my_aesop" : tactic =>
  `(tactic| aesop (rule_sets := [MyDomain]))  -- 4. 简化调用
```

`default := false` 表示规则集默认不启用，需要在 `aesop` 调用时显式列出。这允许构建领域特定的规则库而不影响通用的 `aesop`。

### 常用配置选项
%%%
tag := "ch11-common-options"
%%%

| 选项 | 默认值 | 说明 |
|------|--------|------|
| `strategy` | `bestFirst` | 搜索策略（也可 `depthFirst` / `breadthFirst`） |
| `maxRuleApplicationDepth` | 30 | 单分支最大深度 |
| `maxRuleApplications` | 200 | 总规则应用数上限 |
| `maxGoals` | 0（无限） | 总目标数上限 |
| `maxNormIterations` | 100 | 规范化最大迭代 |
| `terminal` | false | true = 必须完全证明 |
| `enableSimp` | true | norm 阶段是否运行 simp |
| `useSimpAll` | true | 使用 `simp_all` vs `simp at *` |
| `useDefaultSimpSet` | true | 是否包含全局 `@\[simp]` 集 |

**`terminal` 模式**：生产代码推荐开启——aesop 无法关闭目标就报错，避免"部分成功"隐患。

## 与 simp / omega / auto 的区别
%%%
tag := "ch11-comparison"
%%%

| 维度 | aesop | simp | omega | tauto/itauto |
|------|-------|------|-------|-------------|
| 类型 | 启发式搜索 | 确定性重写 | 判定过程 | 固定回溯 |
| 操作 | apply/cases/intro... | 等式改写 | 线性消元 | 命题逻辑 |
| 可扩展 | 完全（规则集） | 有（`@[simp]`） | 无 | 无 |
| 概率引导 | 有 | 无 | 不适用 | 无 |
| 完备性 | 无 | 在其片段内 | 在 Presburger 内 | 在命题逻辑内 |

与 Isabelle 的 `auto` 相比，aesop 的最大特点是**概率引导的 best-first search**（而非固定的 depth-first）和**显式的三类规则分类**（norm / safe / unsafe）。

## 与其他 tactic 组合
%%%
tag := "ch11-combos"
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

**最佳实践**——"人工搭骨架，aesop 填细节"：

```
theorem complex_theorem : P := by
  obtain ⟨a, ha⟩ := existence_lemma    -- 人工：关键存在性
  have key : Q := crucial_step a ha     -- 人工：关键步骤
  aesop                                  -- aesop：收尾
```

# 源码全景
%%%
tag := "ch11-source-overview"
%%%

aesop 的源码分布在 `Aesop/` 目录下。核心文件：

| 文件 | 内容 | 行数 |
|------|------|------|
| `Main.lean` | tactic 入口 `evalAesop` | ~48 |
| `Search/Main.lean` | 搜索主循环 `searchLoop` | ~291 |
| `Search/Expansion.lean` | 目标展开 `expandGoal` | ~267 |
| `Tree/Data.lean` | 搜索树数据结构（Goal/Rapp/MVarCluster） | ~925 |
| `Rule.lean` | 规则类型定义 | ~210 |
| `RuleSet.lean` | 规则集层次 | ~616 |
| `Frontend/RuleExpr.lean` | `@\[aesop]` 属性解析 | ~618 |
| `Script/Main.lean` | 脚本生成 | ~84 |
| `Options/Public.lean` | 配置选项 | ~211 |

aesop 的工程复杂度远超核心搜索算法本身。复杂度主要来自三个方面：

**(a) 搜索空间控制。** 三类规则分类、成功概率累乘、深度/总量限制、安全规则的 commit 语义——这些机制共同构成搜索空间裁剪策略。

**(b) Metavariable 耦合。** Lean 4 的 metavariable 语义使得搜索树中不同目标之间可能存在隐式耦合。aesop 引入 `MVarCluster` 显式追踪这种耦合。每个搜索节点还必须保存独立的 `Meta.SavedState`。

**(c) Proof reconstruction。** aesop 必须从成功的搜索路径中提取 Lean 内核可检查的证明项。`aesop?` 还需要将搜索轨迹翻译为人可读的 tactic 脚本。

## 架构全景图
%%%
tag := "ch11-architecture"
%%%

```
┌─────────────────────────────────────────────────────────┐
│                    用户接口层                             │
│  aesop / aesop?  ──→  TacticConfig.parse                │
│  @\[aesop]        ──→  AttrConfig.elab                   │
│  declare_aesop_rule_sets / add_aesop_rules              │
└────────────┬────────────────────────────────────────────┘
             ▼
┌─────────────────────────────────────────────────────────┐
│                    规则管理层                             │
│  GlobalRuleSet ←── @\[aesop] 注册                        │
│  mkLocalRuleSet (合并多个 GlobalRuleSet → LocalRuleSet)  │
│  Index (DiscrTree 索引：target / hyps / unindexed)      │
└────────────┬────────────────────────────────────────────┘
             ▼
┌─────────────────────────────────────────────────────────┐
│                    搜索引擎层                             │
│  search → SearchM.run → searchLoop                      │
│            ┌──────────┼──────────┐                       │
│            ▼          ▼          ▼                       │
│      checkProven  expandGoal  checkLimits                │
│                       │                                  │
│            ┌──────────┼──────────┐                       │
│            ▼          ▼          ▼                       │
│       normalize   runSafe    runUnsafe                   │
└────────────┬────────────────────────────────────────────┘
             ▼
┌─────────────────────────────────────────────────────────┐
│                    搜索树层                               │
│  Goal (OR) ←→ Rapp (AND) ←→ MVarCluster                │
│  状态传播：自底向上 (proven / unprovable)                  │
│  IO.Ref：原地可变更新                                     │
└────────────┬────────────────────────────────────────────┘
             ▼
┌─────────────────────────────────────────────────────────┐
│                    输出层                                 │
│  extractProof → 证明项（MetaM 赋值 mvar）               │
│  extractScript → tactic 脚本（aesop?）                  │
│  expandSafePrefix → 剩余目标（部分证明）                  │
└─────────────────────────────────────────────────────────┘
```

**推荐源码阅读顺序**：如果你准备对照源码阅读本章后半部分，建议按以下顺序：

1. `Aesop/Rule/Name.lean` — 先读命名体系。`PhaseName`、`BuilderName`、`RuleName` 是理解整个系统的"词汇表"
2. `Aesop/Rule/Basic.lean` + `Aesop/RuleTac/Descr.lean` — 规则结构与 tactic 描述
3. `Aesop/RuleSet.lean` — 规则集层次
4. `Aesop/Tree/Data.lean` — 搜索树节点的互递归定义
5. `Aesop/Search/Expansion.lean` — `expandGoal` 是搜索的核心单步
6. `Aesop/Search/Main.lean` — 主循环 `searchLoop`
7. `Aesop/Frontend/Attribute.lean` + `Aesop/Frontend/Tactic.lean` — 用户接口层

## 入口：evalAesop
%%%
tag := "ch11-eval-aesop"
%%%

当你写下 `aesop` 或 `aesop?`，Lean 的 elaborator 经过以下调用链把它交给搜索引擎。入口定义在 `Aesop/Main.lean`：

```
-- [Aesop, Aesop/Main.lean:20-47]
@\[tactic Frontend.Parser.aesopTactic, tactic Frontend.Parser.aesopTactic?]
meta def evalAesop : Tactic := λ stx => do
  let goal ← getMainGoal
  goal.withContext do
    let (solved, stats) ← go stx goal |>.run ∅
    ...
where
  go (stx : Syntax) (goal : MVarId) : StateRefT Stats TacticM Bool :=
      ...
      let config ← Frontend.TacticConfig.parse stx goal
      let ruleSet ← config.getRuleSet goal
      let (goals, stats) ←
        search goal ruleSet config.options config.simpConfig
          config.simpConfigSyntax? (← getStats)
      replaceMainGoal goals.toList
      ...
```

`evalAesop` 做三件事：(1) 解析 tactic 语法为 `TacticConfig`；(2) 从环境构建 `LocalRuleSet`；(3) 调用 `search` 进入搜索引擎。其中 `TacticConfig.parse` 处理 `(add ...)` / `(erase ...)` / `(rule_sets := [...])` / `(config := ...)` 等子句。

```
用户写 `aesop (add safe apply foo)`
  → Parser 生成 Syntax
    → TacticConfig.parse (解析 clause)
      → getRuleSet (合并全局+局部规则 → LocalRuleSet)
        → search (MetaM 层入口)
          → SearchM.run (初始化搜索树+队列)
            → searchLoop (best-first search 主循环)
              → expandGoal (规范化+规则应用)
```

# 搜索树：三层节点
%%%
tag := "ch11-search-tree"
%%%

aesop 的搜索树是一个 **AND-OR 树**，由三种互递归的节点类型组成。这是理解整个搜索过程的基础。

## Goal / Rapp / MVarCluster 的真实定义
%%%
tag := "ch11-tree-data"
%%%

```
-- [Aesop, Aesop/Tree/Data.lean:316-352]
structure GoalData (Rapp MVarCluster : Type) : Type where
  id : GoalId
  parent : IO.Ref MVarCluster
  children : Array (IO.Ref Rapp)        -- 子节点：规则应用
  state : GoalState                     -- unknown/provenByRuleApplication/
                                        -- provenByNormalization/unprovable
  preNormGoal : MVarId                  -- 规范化前的目标
  normalizationState : NormalizationState
  mvars : UnorderedArraySet MVarId      -- 未赋值的 metavariable
  successProbability : Percent          -- 累积成功概率
  unsafeQueue : UnsafeQueue             -- 待尝试的 unsafe 规则队列
  failedRapps : Array RegularRule       -- 已失败的规则（避免重试）
  depth : Nat
  addedInIteration : Iteration
  lastExpandedInIteration : Iteration
  forwardState : ForwardState           -- 前向推理状态
  forwardRuleMatches : ForwardRuleMatches
  unsafeRulesSelected : Bool
  ...
```

```
-- [Aesop, Aesop/Tree/Data.lean:362-384]
structure RappData (Goal MVarCluster : Type) : Type where
  id : RappId
  parent : IO.Ref Goal
  children : Array (IO.Ref MVarCluster) -- 子节点：MVar 簇
  state : NodeState                     -- proven | unprovable | unknown
  appliedRule : RegularRule             -- 应用的规则
  scriptSteps? : Option (Array Script.LazyStep)
  originalSubgoals : Array MVarId
  successProbability : Percent
  metaState : Meta.SavedState           -- 规则应用后的 meta 状态快照
  introducedMVars : UnorderedArraySet MVarId
  assignedMVars : UnorderedArraySet MVarId
  ...
```

```
-- [Aesop, Aesop/Tree/Data.lean:354-359]
structure MVarClusterData (Goal Rapp : Type) : Type where
  parent? : Option (IO.Ref Rapp)        -- 根簇无父节点
  goals : Array (IO.Ref Goal)           -- 共享 mvar 的目标组
  isIrrelevant : Bool
  state : NodeState
```

## AND-OR 语义
%%%
tag := "ch11-and-or-semantics"
%%%

```
Goal (OR 节点) ── 只要一个子 Rapp proven → Goal proven
  ├── Rapp₁ (AND 节点) ── 所有子 MVarCluster proven → Rapp proven
  │     └── MVarCluster₁ ── 所有子 Goal proven → MVarCluster proven
  │           ├── Goal₁₁
  │           └── Goal₁₂
  └── Rapp₂ (AND 节点)
        └── MVarCluster₂
              └── Goal₂₁
```

- **Goal 是 OR 节点**：多条规则都可以证明同一个目标，只要一条成功即可
- **Rapp 是 AND 节点**：一条规则应用后产生的所有子目标都必须证明
- **MVarCluster 是分组节点**：将共享 metavariable 的子目标聚合在一起

**为什么需要 MVarCluster？** 在 Lean 4 中，一条规则可能产生多个子目标，它们通过 metavariable 隐式耦合。例如 `apply And.intro` 对目标 `⊢ ?a ∧ ?a` 产生两个子目标 `⊢ ?a`（左）和 `⊢ ?a`（右），共享同一个 metavar `?a`。如果搜索先在左子目标上赋值 `?a := True`，那么右子目标也变成 `⊢ True`。MVarCluster 将这种耦合显式化，确保一侧的赋值能正确传播到另一侧。

## unsafe inductive 实现
%%%
tag := "ch11-unsafe-inductive"
%%%

由于三个类型互递归，Lean 4 的归纳类型系统无法直接表达。aesop 使用 `unsafe inductive` + `opaque` 的惯用模式：

```
-- [Aesop, Aesop/Tree/Data.lean:386-395]
mutual
  unsafe inductive GoalUnsafe
    | mk (d : GoalData RappUnsafe MVarClusterUnsafe)
  unsafe inductive MVarClusterUnsafe
    | mk (d : MVarClusterData GoalUnsafe RappUnsafe)
  unsafe inductive RappUnsafe
    | mk (d : RappData GoalUnsafe MVarClusterUnsafe)
end
```

通过 `TreeSpec` 和 `opaque tree : TreeSpec` 包装，对外暴露安全的 `Goal`、`Rapp`、`MVarCluster` 类型。树中的节点通过 `IO.Ref`（可变引用）连接，使得状态更新可以原地修改而不需要函数式更新整棵树。

```
-- [Aesop, Aesop/Tree/Data.lean:426-433]
def Goal        := tree.Goal
def Rapp        := tree.Rapp
def MVarCluster := tree.MVarCluster

abbrev GoalRef        := IO.Ref Goal
abbrev RappRef        := IO.Ref Rapp
abbrev MVarClusterRef := IO.Ref MVarCluster
```

## 节点状态与传播
%%%
tag := "ch11-node-state"
%%%

```
-- [Aesop, Aesop/Tree/Data.lean:198-253]
inductive GoalState
  | unknown                    -- 尚未确定
  | provenByRuleApplication    -- 被某条规则的搜索路径证明
  | provenByNormalization      -- 在规范化阶段被直接证明
  | unprovable                 -- 所有规则都失败
```

状态自底向上传播：

1. 叶子 Goal 被证明 → 其 MVarCluster 检查是否所有 Goal 都 proven
2. MVarCluster 所有 Goal proven → 其父 Rapp 检查所有 MVarCluster
3. Rapp 所有 MVarCluster proven → 其父 Goal 标记 proven
4. Goal 所有子 Rapp unprovable → Goal 标记 unprovable

`GoalState` 比通用的 `NodeState`（proven/unprovable/unknown）更细——区分了 `provenByRuleApplication` 和 `provenByNormalization`，这个区分对脚本生成至关重要。

## 优先级计算
%%%
tag := "ch11-priority"
%%%

`priority` 不是简单的成功概率——它受未赋值 metavariable 数量的惩罚：

```
-- [Aesop, Aesop/Tree/Data.lean:863-864]
def priority (g : Goal) : Percent :=
  g.successProbability * unificationGoalPenalty ^ g.mvars.size
```

直觉是"目标越具体，越容易证明"。含未赋值 metavar 的目标被降权，搜索引擎优先处理形态确定的目标。

# 搜索单子 SearchM
%%%
tag := "ch11-search-monad"
%%%

aesop 的搜索逻辑运行在专用的 monad 栈 `SearchM` 中：

```
-- [Aesop, Aesop/Search/SearchM.lean]
abbrev SearchM Q [Aesop.Queue Q] :=
  ReaderT SearchM.Context $ StateRefT (SearchM.State Q) $
    StateRefT TreeM.State BaseM
```

| 层 | 类型 | 职责 |
|----|------|------|
| 最外层 | `ReaderT SearchM.Context` | 只读访问规则集、simp 上下文、选项 |
| 中间层 | `StateRefT (SearchM.State Q)` | 可变的迭代计数、搜索队列 |
| 内层 | `StateRefT TreeM.State` | 可变的搜索树状态 |
| 基础 | `BaseM` | 底层是 `MetaM` 的变体 |

```
-- Context 包含只读配置
structure Context where
  ruleSet : LocalRuleSet
  normSimpContext : NormSimpContext
  options : Aesop.Options'

-- State 包含可变搜索状态
structure State (Q) [Aesop.Queue Q] where
  iteration : Iteration
  queue : Q
  maxRuleApplicationDepthReached : Bool
```

`SearchM.run` 负责初始化：创建包含根目标的搜索树、从规则集中的 simp 引理构建 `NormSimpContext`、将根目标入队。

`search` 函数是 `SearchM` 层的入口：

```
-- [Aesop, Aesop/Search/Main.lean:268-289]
def search (goal : MVarId) (ruleSet? : Option LocalRuleSet := none)
     (options : Aesop.Options := {}) (simpConfig : Simp.Config := {})
     (simpConfigSyntax? : Option Term := none) (stats : Stats := {}) :
     MetaM (Array MVarId × Stats) := do
  goal.checkNotAssigned `aesop
  let options ← options.toOptions'
  let ruleSet ← match ruleSet? with
    | none => ...              -- 从环境获取默认规则集
    | some ruleSet => pure ruleSet
  let ⟨Q, _⟩ := options.queue  -- 根据策略选择队列类型
  let go : SearchM Q _ := do
    try searchLoop
    finally
      collectGoalStatsIfEnabled
      freeTree                  -- 释放搜索树内存
  let ((goals, _, _), stats) ←
    go.run ruleSet options simpConfig simpConfigSyntax? goal |>.run stats
  return (goals, stats)
```

注意 `finally` 中的 `freeTree`——搜索树通过 `IO.Ref` 互相连接，形成循环引用，无法被 GC 自动回收，需要显式释放。

## 搜索队列：优先级与策略
%%%
tag := "ch11-search-queue"
%%%

```
-- Queue 类型类支持多种搜索策略
class Queue (Q : Type) where
  init : BaseIO Q
  addGoals : Q → Array GoalRef → BaseIO Q
  popGoal : Q → BaseIO (Option GoalRef × Q)
```

三种策略：

| 策略 | 队列类型 | 底层数据结构 | 特征 |
|------|----------|-------------|------|
| `bestFirst`（默认） | `BestFirstQueue` | `BinomialHeap` | 概率引导 |
| `depthFirst` | `LIFOQueue` | `Array`（栈） | 深度优先 |
| `breadthFirst` | `FIFOQueue` | `Array`（队列） | 广度优先 |

默认的 best-first 队列按三级字典序排列目标优先级：

```
-- [Aesop, Aesop/Search/Queue.lean]
-- 1. priority 更高的目标优先（高成功概率的路径先探索）
-- 2. 上次展开迭代更早的目标优先（公平性，防饥饿）
-- 3. 添加迭代更早的目标优先（稳定性）
protected def le (g h : ActiveGoal) : Bool :=
  g.priority > h.priority ||
    (g.priority == h.priority &&
      (g.lastExpandedInIteration ≤ h.lastExpandedInIteration ||
        ...))
```

**注意**：best-first 不是在寻找"最短证明"或"最低成本证明"——它是在启发式意义上优先展开"看起来更可能成功"的分支。搜索一旦找到任意一条完整证明路径就终止，不保证该路径是最优的。

# 搜索主循环
%%%
tag := "ch11-search-loop"
%%%

## searchLoop：best-first search
%%%
tag := "ch11-search-loop-impl"
%%%

```
-- [Aesop, Aesop/Search/Main.lean:251-266]
partial def searchLoop : SearchM Q (Array MVarId) :=
  withIncRecDepth do
    checkSystem "aesop"
    if let (some err) ← checkRootUnprovable then
      handleNonfatalError err
    else if ← finishIfProven then
      return #[]
    else if let (some err) ← checkGoalLimit then
      handleNonfatalError err
    else if let (some err) ← checkRappLimit then
      handleNonfatalError err
    else
      expandNextGoal
      checkInvariantsIfEnabled
      incrementIteration
      searchLoop
```

每次迭代执行五步检查 + 一步展开：

1. `checkRootUnprovable`：根节点是否已被标记 unprovable（exhaustive search 失败）
2. `finishIfProven`：根节点是否已 proven（成功，提取证明并返回）
3. `checkGoalLimit`：总目标数是否超过 `maxGoals`
4. `checkRappLimit`：总规则应用数是否超过 `maxRuleApplications`
5. `expandNextGoal`：从队列弹出优先级最高的目标并展开
6. 尾递归

搜索终止的三种情况：根目标 proven（成功返回空目标列表）、根目标 unprovable（尝试安全前缀后报错）、超过资源限制（尝试安全前缀）。

## expandNextGoal：弹出并展开
%%%
tag := "ch11-expand-next-goal"
%%%

```
-- [Aesop, Aesop/Search/Main.lean:39-62]
def expandNextGoal : SearchM Q Unit := do
  let gref ← nextActiveGoal           -- 从队列弹出优先级最高的活跃目标
  ...
  let maxRappDepth := (← read).options.maxRuleApplicationDepth
  if maxRappDepth != 0 && (← gref.get).depth >= maxRappDepth then
    gref.markForcedUnprovable          -- 深度超限 → 标记不可证
    setMaxRuleApplicationDepthReached
    return .failed
  let result ← expandGoal gref        -- 核心：展开目标
  ...
  if ← (← gref.get).isActive then
    enqueueGoals #[gref]               -- 目标仍然活跃 → 重新入队
```

注意：如果目标仍然活跃（例如 unsafe 规则队列未用完），它会被**重新入队**——下次弹出时从上次停下的地方继续尝试 unsafe 规则。

## expandGoal：三阶段展开
%%%
tag := "ch11-expand-goal"
%%%

`expandGoal` 是搜索的核心单步——对一个目标依次执行规范化、安全规则、不安全规则：

```
-- [Aesop, Aesop/Search/Expansion.lean:228-265]
def expandGoal (gref : GoalRef) : SearchM Q RuleResult := do
  -- 阶段 1：规范化
  let provedByNorm ←
    withAesopTraceNode .steps fmtNorm (normalizeGoalIfNecessary gref)
  if provedByNorm then return .proved #[]

  -- 阶段 2：安全规则
  let safeResult ←
    withAesopTraceNode .steps fmtSafe (runFirstSafeRule gref)
  match safeResult with
  | .succeeded newRapps => return .succeeded newRapps
  | .proved newRapps => return .proved newRapps
  | .failed postponedSafeRules => doUnsafe postponedSafeRules
  | .skipped => doUnsafe #[]
  where
    -- 阶段 3：不安全规则
    doUnsafe (postponedSafeRules : Array PostponedSafeRule) :
        SearchM Q RuleResult := do
      withAesopTraceNode .steps fmtUnsafe do
        runFirstUnsafeRule postponedSafeRules gref
```

三阶段的逻辑：
- **规范化**先行：确保目标处于标准形态，改善后续规则的 DiscrTree 索引匹配
- **安全规则**优先于不安全规则：匹配即 commit，大幅裁剪搜索空间
- **不安全规则**最后：按成功概率排序逐个尝试

## 安全规则的 commit 与推迟语义
%%%
tag := "ch11-safe-commit"
%%%

```
-- [Aesop, Aesop/Search/Expansion.lean:179-196]
def runFirstSafeRule (gref : GoalRef) : SearchM Q SafeRulesResult := do
  if (← gref.get).unsafeRulesSelected then return .skipped
  gref.updateForwardState .safe
  let g ← gref.get
  let rules ← selectSafeRules g
  let mut postponedRules := {}
  for r in rules do
    let result ← runSafeRule gref r
    match result with
    | .regular .failed => continue                -- 失败：尝试下一条
    | .regular (.proved newRapps) => return .proved newRapps   -- 成功：commit
    | .regular (.succeeded newRapps) => return .succeeded newRapps
    | .postponed r => postponedRules := postponedRules.push r  -- 推迟
  return .failed postponedRules
```

**推迟机制**：如果一条安全规则会赋值父目标的 metavariable（即影响搜索树中其他目标），它不会立即 commit，而是被"推迟"到 unsafe 阶段处理。这是安全和灵活性之间的精巧折中——参见 `runSafeRule` 中的检查：

```
-- [Aesop, Aesop/Search/Expansion.lean:132-154]
def runSafeRule (parentRef : GoalRef) (matchResult : IndexMatchResult SafeRule) :
    SearchM Q SafeRuleResult := do
  ...
      let anyParentMVarAssigned ← rapps.anyM λ rapp => do
        rapp.postState.runMetaM' do
          parentMVars.anyM (·.isAssignedOrDelayedAssigned)
      if anyParentMVarAssigned then
        aesop_trace[steps] "Safe rule assigned metavariables, so we postpone it"
        return .postponed ⟨rule, output⟩
      else
        return .regular (← addRapps parentRef (.safe rule) rapps)
```

## 不安全规则的选择与执行
%%%
tag := "ch11-unsafe-execution"
%%%

不安全规则按成功概率排序，与推迟的安全规则一起放入 `UnsafeQueue`，逐个尝试：

```
-- [Aesop, Aesop/Search/Expansion.lean:203-227]
partial def runFirstUnsafeRule (postponedSafeRules : Array PostponedSafeRule)
    (parentRef : GoalRef) : SearchM Q RuleResult := do
  parentRef.updateForwardState .unsafe
  let queue ← selectUnsafeRules postponedSafeRules parentRef
  let (remainingQueue, result) ← loop queue
  parentRef.modify λ g => g.setUnsafeQueue remainingQueue
  if remainingQueue.isEmpty then
    ...
    if ← pure (! parent.state.isProven) <&&> parent.isUnprovableNoCache then
      parentRef.markUnprovable
  return result
  where
    loop (queue : UnsafeQueue) : SearchM Q (UnsafeQueue × RuleResult) := do
      let (some (r, queue)) := Subarray.popHead? queue
        | return (queue, RuleResult.failed)
      match r with
      | .unsafeRule r =>
        let result ← runUnsafeRule parentRef r
        match result with
        | .proved .. => return (queue, result)
        | .succeeded .. => return (queue, result)
        | .failed => loop queue
      | .postponedSafeRule r =>
        return (queue, ← applyPostponedSafeRule r parentRef)
```

注意 `remainingQueue` 会保存回 Goal 节点——下次展开同一目标时，从上次停下的地方继续尝试。队列为空且无 proven 子节点时，目标被标记为 `unprovable`。

## 安全前缀：优雅退化
%%%
tag := "ch11-safe-prefix"
%%%

当搜索未能找到完整证明（超限或 unprovable）时，aesop 不立即放弃——它调用 `handleNonfatalError`：

```
-- [Aesop, Aesop/Search/Main.lean:229-249]
def handleNonfatalError (err : MessageData) : SearchM Q (Array MVarId) := do
  let safeExpansionSuccess ← expandSafePrefix   -- 从根开始展开所有安全规则
  let safeGoals ← extractSafePrefix             -- 提取安全前缀剩余目标
  ...
  if opts.terminal then
    throwAesopEx ...                             -- terminal 模式：必须完全证明
  if ! (← treeHasProgress) then
    throwAesopEx ... "made no progress"          -- 无进展：报错
  safeGoals.mapM (clearForwardImplDetailHyps ·)  -- 返回剩余目标
```

安全前缀的意义：即使 aesop 无法完全证明目标，它仍会尽可能应用安全规则来简化目标——返回的剩余目标可以供用户手动处理。这就是 `aesop` 默认非 terminal 模式的行为。

# 规范化阶段
%%%
tag := "ch11-normalization"
%%%

在尝试规则之前，aesop 先对目标进行规范化——可能直接证明目标或简化目标形式以改善索引匹配。

## 四步不动点循环
%%%
tag := "ch11-norm-four-steps"
%%%

```
-- [Aesop, Aesop/Search/Expansion/Norm.lean]
partial def normalizeGoalMVar (goal : MVarId)
    (mvars : UnorderedArraySet MVarId) : NormM NormSeqResult := do
  let mut normSteps := #[
    NormStep.runPreSimpRules mvars,    -- ① penalty < 0 的 norm 规则
    NormStep.unfold,                    -- ② 展开 @\[aesop unfold] 定义
    NormStep.simp mvarsHashSet,         -- ③ simp / simp_all
    NormStep.runPostSimpRules mvars     -- ④ penalty ≥ 0 的 norm 规则
  ]
  runNormSteps goal normSteps ...
```

| 步骤 | 执行内容 | 典型用途 |
|------|---------|---------|
| ① Pre-simp norm 规则 | penalty < 0 的 norm 规则 | 在 simp 之前做必要的预处理 |
| ② Unfold | 展开 `@\[aesop unfold]` 定义 | 暴露内部结构给 simp |
| ③ Simp | 调用 `simp` 或 `simp_all` | 主要的化简手段 |
| ④ Post-simp norm 规则 | penalty ≥ 0 的 norm 规则 | simp 之后的清理工作 |

`runNormSteps` 循环执行这四步，直到所有步骤都 `unchanged` 或达到 `maxNormIterations`（默认 100）。

## NormalizationState 缓存
%%%
tag := "ch11-normalization-state"
%%%

```
-- [Aesop, Aesop/Tree/Data.lean:256-262]
inductive NormalizationState
  | notNormal                     -- 尚未规范化
  | normal (postGoal ...) (script ...)      -- 规范化后的目标
  | provenByNormalization (postState ...) (script ...)  -- 规范化直接证明
```

每个目标只规范化一次——结果缓存在 `NormalizationState` 中。如果目标被重新入队（例如因为 unsafe 规则队列未用完），不会重复规范化。

规范化阶段的 simp 使用独立的引理集——由 `@\[aesop norm simp]` 标注的引理加上（可选的）全局 `@\[simp]` 集。配置选项 `useDefaultSimpSet` 控制是否包含全局 `@\[simp]` 集，`useSimpAll` 控制使用 `simp_all` 还是 `simp at *`。

# 规则系统
%%%
tag := "ch11-rule-system"
%%%

## Rule 结构与 RuleName
%%%
tag := "ch11-rule-structure"
%%%

每条规则由名称、索引模式、附加信息和 tactic 描述组成。三类规则共用同一个参数化结构 `Rule α`：

```
-- [Aesop, Aesop/Rule.lean:20-39]
structure NormRuleInfo where
  penalty : Int                        -- 越小越先执行
abbrev NormRule := Rule NormRuleInfo

-- [Aesop, Aesop/Rule.lean:59-77]
structure SafeRuleInfo where
  penalty : Int
  safety : Safety                      -- safe | almostSafe
abbrev SafeRule := Rule SafeRuleInfo

-- [Aesop, Aesop/Rule.lean:83-103]
structure UnsafeRuleInfo where
  successProbability : Percent         -- 成功概率
abbrev UnsafeRule := Rule UnsafeRuleInfo
```

`RegularRule` 是 safe 和 unsafe 的联合类型，用于搜索树节点中记录应用的规则：

```
-- [Aesop, Aesop/Rule.lean:108-146]
inductive RegularRule
  | safe (r : SafeRule)
  | «unsafe» (r : UnsafeRule)

def successProbability : RegularRule → Percent
  | safe _ => Percent.hundred          -- safe 规则概率视为 100%
  | «unsafe» r => r.extra.successProbability
```

`RuleName` 是四维标识——同一个声明可以在不同阶段注册为不同规则：

```
-- 四维组合确保唯一性
structure RuleName where
  name : Name             -- 声明名（如 `Nat.add_zero`）
  builder : BuilderName   -- 构建方式（apply / cases / forward / ...）
  phase : PhaseName        -- 阶段（norm / safe / unsafe）
  scope : ScopeName        -- 作用域（global / local）
```

## BaseRuleSet / GlobalRuleSet / LocalRuleSet
%%%
tag := "ch11-rule-set-hierarchy"
%%%

规则集分三层。`BaseRuleSet` 是核心存储，`GlobalRuleSet` 和 `LocalRuleSet` 在其上扩展：

```
-- [Aesop, Aesop/RuleSet.lean:29-80]
structure BaseRuleSet where
  normRules : Index NormRuleInfo       -- DiscrTree 索引
  unsafeRules : Index UnsafeRuleInfo
  safeRules : Index SafeRuleInfo
  unfoldRules : PHashMap Name (Option Name)
  forwardRules : ForwardIndex          -- 前向规则单独索引
  forwardRuleNames : PHashSet RuleName
  rulePatterns : RulePatternIndex
  erased : PHashSet RuleName           -- 已擦除的规则
  ruleNames : PHashMap Name (UnorderedArraySet RuleName)  -- 名称缓存
```

```
-- [Aesop, Aesop/RuleSet.lean:88-128]
structure GlobalRuleSet extends BaseRuleSet where
  simpTheorems : SimpTheorems          -- norm 阶段的 simp 引理
  simprocs : Simprocs

structure LocalRuleSet extends BaseRuleSet where
  simpTheoremsArray : Array (Name × SimpTheorems)
  simprocsArray : Array (Name × Simprocs)
  localNormSimpRules : Array LocalNormSimpRule
```

**GlobalRuleSet** 通过 `@\[aesop]` 属性注册，存储在环境扩展中，跨文件持久。**LocalRuleSet** 是每次 `aesop` 调用时从多个全局规则集合并而来的临时结构——合并过程中会应用 `add` 和 `erase` 子句。

合并过程在 `mkLocalRuleSet` 中：

```
-- [Aesop, Aesop/RuleSet.lean:580-614]
def mkLocalRuleSet (rss : Array (GlobalRuleSet × Name × Name))
    (options : Options') : CoreM LocalRuleSet := do
  let mut result := ∅
  let simpTheorems ← getSimpTheorems
  ...
  for (rs, simpExtName, simprocExtName) in rss do
    result := { result with
      toBaseRuleSet := result.toBaseRuleSet.merge rs.toBaseRuleSet
      simpTheoremsArray :=
        result.simpTheoremsArray.push (simpExtName, rs.simpTheorems)
      ...
    }
  ...
```

## IndexingMode 与 DiscrTree 索引
%%%
tag := "ch11-indexing"
%%%

规则通过 `IndexingMode` 指定如何被索引以实现高效匹配：

```
-- IndexingMode 的主要变体
inductive IndexingMode
  | unindexed                              -- 不索引（每个目标都会考虑）
  | target (keys : Array DiscrTree.Key)    -- 按目标结论索引
  | hyps (keys : Array DiscrTree.Key)      -- 按假设索引
  | or (imodes : Array IndexingMode)       -- 多种模式的析取
```

`target` 模式最常见——规则结论编码为 DiscrTree key 序列，只有当前目标结论的 head symbol 匹配时才考虑该规则。原理与 simp 的 DiscrTree 索引相同。

**性能要点**：`unindexed` 规则每次都会被考虑——O(n) 级别开销。应尽量避免。如果你的自定义规则始终被标记为 `unindexed`，检查其类型签名是否足够具体——aesop 需要看到结论的 head symbol 才能建立索引。

## `@[aesop]` 属性解析
%%%
tag := "ch11-attribute-parsing"
%%%

`@\[aesop]` 属性的语法支持丰富的组合。解析过程定义在 `Frontend/RuleExpr.lean`：

```
-- [Aesop, Aesop/Frontend/RuleExpr.lean:33-36]
-- 优先级语法
syntax num "%" : Aesop.priority       -- 百分比（unsafe）
syntax "-"? num : Aesop.priority      -- 整数（norm/safe）

-- [Aesop, Aesop/Frontend/RuleExpr.lean:81-86]
-- 阶段语法
syntax "safe" : Aesop.phase
syntax "norm" : Aesop.phase
syntax "unsafe" : Aesop.phase

-- [Aesop, Aesop/Frontend/RuleExpr.lean:100-109]
-- 构建器语法
syntax "apply" : Aesop.builder_name
syntax "simp" : Aesop.builder_name
syntax "unfold" : Aesop.builder_name
syntax "tactic" : Aesop.builder_name
syntax "forward" : Aesop.builder_name
syntax "destruct" : Aesop.builder_name
syntax "cases" : Aesop.builder_name
syntax "default" : Aesop.builder_name
```

`RuleConfig` 收集所有特征（phase、priority、builder、builder options、rule\_sets）后调用对应的 `RuleBuilder` 生成规则：

```
-- [Aesop, Aesop/Frontend/RuleExpr.lean:387-394]
structure RuleConfig where
  term? : Option Term
  phase? : Option PhaseName
  priority? : Option Priority
  builder? : Option DBuilderName
  builderOptions : RuleBuilderOptions
  ruleSets : RuleSets
```

`DBuilderName.toRuleBuilder` 将构建器名映射到实际的规则构建逻辑：

```
-- [Aesop, Aesop/Frontend/RuleExpr.lean:144-154]
def toRuleBuilder : DBuilderName → RuleBuilder
  | .regular .apply => RuleBuilder.apply
  | .regular .cases => RuleBuilder.cases
  | .regular .constructors => RuleBuilder.constructors
  | .regular .destruct => RuleBuilder.forward (isDestruct := true)
  | .regular .forward => RuleBuilder.forward (isDestruct := false)
  | .regular .simp => RuleBuilder.simp
  | .regular .tactic => RuleBuilder.tactic
  | .regular .unfold => RuleBuilder.unfold
  | .default => RuleBuilder.default
```

## 内建规则
%%%
tag := "ch11-builtin-rules"
%%%

aesop 注册了一批默认规则（`Aesop/BuiltinRules/`）：

| 规则 | 阶段 | 行为 |
|------|------|------|
| `assumption` | safe | 类似 `assumption` tactic |
| `applyHyps` | unsafe | 尝试将所有假设 apply 到目标 |
| `intros` | safe | 引入 ∀ binder |
| `rfl` | safe | 关闭自反性目标 |
| `split` | safe | 分解 `∧`、`↔` 目标 |
| `subst` | norm | 用等式替换变量 |
| `destructProducts` | norm | 分解 `∧`/`×` 假设 |
| `ext` | safe | 函数外延性 |

内建规则的阶段选择蕴含设计智慧——`intros` 是 safe（引入变量永远不丢失信息）、`applyHyps` 是 unsafe（随意 apply 假设可能走错方向）、`subst` 是 norm（等式替换是纯化简）。

## Norm simp 规则与 Unfold 规则
%%%
tag := "ch11-norm-simp-unfold"
%%%

Norm 阶段除了普通的 norm 规则外，还有两类特殊规则：

**NormSimpRule**：添加到 norm 阶段的 simp 引理集。通过 `@\[aesop norm simp]` 注册：

```
-- [Aesop, Aesop/Rule.lean:156-169]
structure NormSimpRule where
  name : RuleName
  entries : Array SimpEntry       -- SimpEntry 表示 simp 集的一个成员
```

**UnfoldRule**：在 norm 阶段展开的定义。通过 `@\[aesop norm unfold]` 注册：

```
-- [Aesop, Aesop/Rule.lean:194-210]
structure UnfoldRule where
  decl : Name
  unfoldThm? : Option Name       -- 缓存的展开等式定理
```

# 脚本生成
%%%
tag := "ch11-script-generation"
%%%

## Proof reconstruction vs 脚本生成
%%%
tag := "ch11-proof-vs-script"
%%%

搜索成功后需要两个不同的"输出"：

1. **Proof reconstruction**（`extractProof`）——给**内核**检查的：遍历已证明的搜索路径，将各节点的 `Meta.SavedState` 串联，构建完整证明项并赋值给根 goal 的 metavariable

2. **脚本生成**（`extractScript` + `UScript.optimize`）——给**人**看的：将搜索轨迹翻译为 tactic 脚本，通过 `Try this:` 输出建议

```
-- [Aesop, Aesop/Search/Main.lean:117-127]
def finalizeProof : SearchM Q Unit := do
  (← getRootMVarId).withContext do
    extractProof
    let (some proof) ← getProof? | throwError
      "aesop: internal error: root goal is proven but ..."
    if (← instantiateMVars proof).hasExprMVar then
      ...  -- 内部错误：证明中不应有未赋值的 mvar
```

## UScript.optimize：结构化脚本
%%%
tag := "ch11-script-optimize"
%%%

`aesop?` 生成的脚本经过优化：搜索过程中每个操作产生 `Script.LazyStep`，记录在节点的 `scriptSteps?` 字段中。搜索成功后，`extractScript` 收集步骤，`UScript.optimize` 转换为结构化语法：

```
-- [Aesop, Aesop/Script/Main.lean:22-57]
def UScript.optimize (uscript : UScript) (proofHasMVar : Bool)
    (preState : Meta.SavedState) (goal : MVarId) :
    MetaM (Option (TSyntax ``tacticSeq × ScriptGenerated)) := do
  let structureResult? ← do
    let opts ← getOptions
    if aesop.dev.dynamicStructuring.get opts &&
       ! (aesop.dev.optimizedDynamicStructuring.get opts && ! proofHasMVar) then
      structureDynamic
    else
      structureStatic
  let some (sscript, gen) := structureResult?
    | return none
  let tacticSeq ← `(tacticSeq| $(← sscript.render):tactic*)
  let tacticSeq ← optimizeSyntax tacticSeq
  return some (tacticSeq, gen)
```

两种结构化策略：
- **Static structuring**：基于搜索树结构直接映射为 tactic 序列
- **Dynamic structuring**：在 TacticState 上重放步骤，动态确定分支结构

如果证明不含 metavar，优先使用 static structuring（更简单高效）。

# 调试手册
%%%
tag := "ch11-debugging"
%%%

## Trace 选项
%%%
tag := "ch11-trace-options"
%%%

```
set_option trace.aesop true in                  -- 所有 aesop trace
set_option trace.aesop.steps true in            -- 搜索步骤（最常用）
set_option trace.aesop.ruleSet true in          -- 规则集内容
set_option trace.aesop.normalization true in    -- 规范化过程
set_option trace.aesop.tree true in             -- 搜索树
set_option trace.aesop.forward true in          -- 前向推理
```

`trace.aesop.steps` 的输出使用 emoji 标记每步结果：✅ 规则应用成功且目标被证明；☑️ 规则应用成功，产生新子目标；❌ 规则应用失败；⏩ 规则被跳过。

## 阅读错误信息
%%%
tag := "ch11-reading-errors"
%%%

```
aesop: failed to prove the goal after exhaustive search.
Initial goal:
  ⊢ ...
Remaining goals after safe rules:
  ⊢ a ∈ t
```

- **exhaustive search**：所有规则都失败，搜索树耗尽
- **max rule applications reached**：总量限制截断——调大 `maxRuleApplications`
- **max rule application depth reached**：深度限制——调大 `maxRuleApplicationDepth`
- **Remaining goals after safe rules**："差了哪一步"的线索

## 症状 → 诊断 → 修复
%%%
tag := "ch11-symptom-diagnosis"
%%%

### 症状：aesop 超时 / 极慢
%%%
tag := "ch11-symptom-slow"
%%%

**诊断**：开 `trace.aesop.steps`，观察搜索是否在某个分支上反复深入。常见原因：

1. **unsafe 规则概率过高**：某条不太有用的规则概率设为 90%，导致优先深探错误分支
2. **unindexed 规则过多**：每个目标都要尝试所有 unindexed 规则
3. **规范化死循环**：norm 规则互相触发

**修复**：降低可疑 unsafe 规则概率 / 检查 unindexed 规则 / 限制 `maxNormIterations`

### 症状：aesop 找不到证明
%%%
tag := "ch11-symptom-not-found"
%%%

**诊断**：

1. 规则不在启用的规则集中——开 `trace.aesop.ruleSet` 确认
2. 规范化改变目标——开 `trace.aesop.normalization`
3. 索引失配——norm simp 改变了 head symbol，DiscrTree 匹配失败
4. 深度不够——调大 `maxRuleApplicationDepth`

**修复**：`aesop (rule_sets := [MyRules])` / `aesop (config := { maxRuleApplicationDepth := 50 })` / `aesop (add unsafe 50% apply myLemma)`

### 症状：类型信息不足
%%%
tag := "ch11-symptom-type-info"
%%%

```
-- ❌ a, s, t 类型未知
-- example (a : _) (s t : _) (h : a ∈ s) : a ∈ s ∪ t := by aesop
-- ✅ 显式标注
example {α : Type} (a : α) (s t : Set α) (h : a ∈ s) : a ∈ s ∪ t := by aesop
```

目标简单但失败 → 检查 metavariable（`?m`）或未解析 typeclass。

### 症状：safe 规则过度激进
%%%
tag := "ch11-symptom-safe-aggressive"
%%%

```
-- ❌ destruct 消耗假设丢失信息
-- @\[aesop safe destruct]
-- theorem bad : P ∨ Q → True := fun _ => trivial
-- ✅ 改为 forward 或降级 unsafe
```

Safe 规则有 commit 语义——如果一条更早的 safe 规则先匹配并 commit，后续 safe 规则不会被尝试。调整 penalty 值或将干扰规则改为 unsafe。

### 症状：forward 规则循环
%%%
tag := "ch11-symptom-forward-cycle"
%%%

```
-- ❌ 互相触发产生无限新假设
-- @\[aesop safe forward] theorem fwd  : R a b → R b a := ...
-- @\[aesop safe forward] theorem back : R b a → R a b := ...
-- ✅ 只保留一个方向，或改用 destruct
```

超时或 `maxRuleApplications` 耗尽 → 检查 forward 规则是否形成环。

### 症状：规则已注册但从不触发
%%%
tag := "ch11-symptom-rule-never-fires"
%%%

最常见的原因是 **norm 阶段先改写了目标或假设**，导致规范化后的目标形态与规则的 DiscrTree 索引不再匹配。例如：你注册了 `@\[aesop unsafe apply] theorem foo : A → B`，但 norm simp 将目标中的 `B` 化简为 `B'`，于是 `foo` 的索引 key（基于 `B` 的 head symbol）永远匹配不上。

**修复**：(a) 将规则索引改为 `unindexed`（牺牲性能换正确性）；(b) 将规则注册为 norm 阶段；(c) 重新设计规则使其结论匹配规范化后的形态。

## aesop? 脚本不工作
%%%
tag := "ch11-aesop-script-issues"
%%%

`aesop?` 生成的脚本可能依赖特定的上下文条件：

1. 脚本中的 `simp` 调用可能依赖某些 `@\[simp]` 引理，在其他上下文中不存在
2. 定理名可能因 `open` 语句不同而无法解析

**修复**：手动调整脚本中的 `simp` 调用，显式列出引理。

# 扩展点
%%%
tag := "ch11-extension-points"
%%%

## 自定义规则（最常见）
%%%
tag := "ch11-custom-rules"
%%%

```
-- 安全规则：constructors 构建器自动注册所有构造子
@\[aesop safe [constructors]]
inductive MyInductive where | mk : Nat → MyInductive

-- 不安全规则：50% 成功概率，apply 构建器
@\[aesop unsafe 50% apply]
theorem my_lemma : ∀ n, n + 0 = n := Nat.add_zero

-- 规范化规则：添加到 norm simp 集
@\[aesop norm simp]
theorem my_simp_lemma : ∀ n, n + 0 = n := Nat.add_zero

-- 规范化规则：unfold 定义
@\[aesop norm unfold]
def myDef₂ := 42
```

## 自定义 RuleTac
%%%
tag := "ch11-custom-rule-tac"
%%%

如果内建构建器不够用，可以注册自定义的 `RuleTac`——实现 `RuleTacInput → BaseM RuleTacOutput` 签名：

```
-- RuleTac 的类型签名
def RuleTac := RuleTacInput → BaseM RuleTacOutput

structure RuleTacInput where
  goal : MVarId
  mvars : UnorderedArraySet MVarId
  indexMatchLocations : Array IndexMatchLocation
  ...

structure RuleApplication where
  goals : Array Subgoal
  postState : Meta.SavedState
  successProbability? : Option Percent     -- 可选：动态覆盖概率
```

在 `input.goal` 上执行自定义逻辑，返回 `RuleApplication` 数组。

## TacGen：机器学习接口
%%%
tag := "ch11-tacgen"
%%%

`TacGen` 是 aesop 为 ML 模型预留的接口——接收当前目标，返回 `(tactic 字符串, 置信度)` 数组。aesop 将每条建议包装为 unsafe 规则应用，置信度转化为成功概率，使外部神经网络可以无缝接入搜索框架。

## 自定义规则集
%%%
tag := "ch11-custom-rule-sets"
%%%

```
declare_aesop_rule_sets [MyDomainRules] (default := false)

-- 往规则集中添加规则
@\[aesop safe apply (rule_sets := [MyDomainRules])]
theorem domain_lemma : ... := ...

-- 使用时显式启用
example : ... := by aesop (rule_sets := [MyDomainRules])
```

aesop 的架构高度模块化——搜索策略、队列、规则构建器、规范化步骤都可以替换或扩展。如果你在构建领域特定的自动化 tactic，考虑复用 aesop 的搜索框架（通过 `Aesop.search` API）而不是从零编写。

# 关键设计决策总结
%%%
tag := "ch11-design-decisions"
%%%

回顾 aesop 的几个核心设计决策：

**AND-OR 树 + MVarCluster**：引入 MVarCluster 处理 Lean 4 中 metavariable 共享——一个目标的赋值可能影响同簇的另一个目标。经典 AND-OR 树假设子目标独立，但 Lean 4 的 metavar 语义打破了这个假设。

**安全规则的 commit 语义**：匹配成功即 commit，大幅剪枝搜索空间。推迟赋值 mvar 的安全规则兼顾效率与灵活性。这是 aesop 与简单 backtracking prover 的关键区别。

**规范化先于规则应用**：先规范化确保 DiscrTree 索引准确匹配。但这也意味着 norm 阶段可能改变目标形态，导致某些规则的索引失配——这是调试中最常见的陷阱之一。

**概率引导搜索**：成功概率沿路径累乘，偏好"每步高概率"的路径。`unificationGoalPenalty` 对含未赋值 metavar 的目标施加额外惩罚。为 unsafe 规则选择合理的成功概率至关重要——概率过高（如 90%）导致过早深入错误分支，过低（如 1%）则可能永远轮不到。实践中 50%–80% 是常见的合理区间。

**IO.Ref 可变搜索树**：搜索树节点通过可变引用连接，状态更新原地修改。自底向上的状态传播配合 `IO.Ref`，比函数式更新整棵树效率高得多——但也意味着需要显式 `freeTree` 来避免内存泄漏。

**关键源码文件索引**：

| 文件 | 内容 |
|------|------|
| `Aesop/Main.lean` | tactic 入口 `evalAesop` |
| `Aesop/Search/Main.lean` | `searchLoop`、`expandNextGoal`、`handleNonfatalError` |
| `Aesop/Search/Expansion.lean` | `expandGoal`、`runSafeRule`、`runUnsafeRule` |
| `Aesop/Search/Expansion/Norm.lean` | 规范化四步循环 |
| `Aesop/Tree/Data.lean` | `GoalData`、`RappData`、`MVarClusterData`、`GoalState` |
| `Aesop/Rule.lean` + `Aesop/Rule/Basic.lean` | 规则结构 |
| `Aesop/RuleSet.lean` | 规则集层次 |
| `Aesop/Frontend/RuleExpr.lean` | 属性语法解析 |
| `Aesop/Options/Public.lean` | 配置选项 |
| `Aesop/Script/Main.lean` | 脚本生成 |

# 练习
%%%
tag := "ch11-exercises"
%%%

## 练习 1（基础）：aesop 能力边界
%%%
tag := "ch11-exercise-1"
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

**提示**：(a)(c) 是 aesop 主场；(b) 用 `omega`；(d) 看 norm 阶段是否化简。

## 练习 2（进阶）：自定义规则集
%%%
tag := "ch11-exercise-2"
%%%

为图论领域定义 aesop 规则集。将 `symm` 注册为 safe forward，添加 transitivity 作为 unsafe 70%。思考：symm 作为 safe forward 会不会循环？（参考调试手册中 forward 规则循环的讨论）

**核心教训**：规则工程（选什么规则、标什么优先级、用什么动作）往往比搜索参数调优更关键——一条错误的 safe forward 就能让整个搜索失控。

## 练习 3（诊断）：修复失败
%%%
tag := "ch11-exercise-3"
%%%

```
-- 为什么失败？用 trace.aesop 诊断，用 (add ...) 修复
-- example {α : Type} (P Q : α → Prop) (a : α)
--     (h1 : ∀ x, P x → Q x) (h2 : P a) : Q a := by aesop
```

**提示**：`h1` 是全称量化的蕴含——默认 `applyHyps` 能否匹配？考虑 `add unsafe apply h1` 或者思考为什么 `aesop` 的内建规则覆盖不到这个模式。

## 练习 4（源码阅读）：搜索队列
%%%
tag := "ch11-exercise-4"
%%%

阅读 `Aesop/Search/Queue.lean`，回答：

1. `BestFirstQueue` 的底层数据结构是什么？
2. 排序的三级字典序是什么含义？
3. 为什么需要 `lastExpandedInIteration` 作为第二排序键？（提示：公平性）

## 练习 5（实战）：aesop? 替换
%%%
tag := "ch11-exercise-5"
%%%

在你的项目中用 `aesop?` 提取手写证明，比较编译速度，记录哪些值得保留、哪些应替换为 `aesop?` 输出的脚本。

下一章：`grind`——E-matching 和 congruence closure。
