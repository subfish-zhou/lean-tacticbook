import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch01MetaprogrammingModel"

#doc (Manual) "第十二章 grind：E-matching 与 Congruence Closure" =>
%%%
file := "Ch12Grind"
tag := "ch12-grind"
%%%

*本章目标*：掌握 `grind` 的 E-graph 架构、`@[grind]` 引理注册机制、
常见失败模式及调试方法。

`aesop` 擅长搜索，但面对散落在上下文中的等式假设时力不从心。
`grind` 把所有等式丢进一个共享的 *E-graph*，让 congruence closure 自动发现隐含关系。

# 12.1 grind 是什么
%%%
tag := "grind-what-is-it"
%%%

`grind` 是 Lean 4 (v4.14+) 内置的 SMT 风格 tactic。
核心能力是*等式传递推理*——给定若干等式假设，自动推导目标等式。

```
-- [可运行] 最简场景：两步等式传递
example (h1 : a = b) (h2 : b = c) : a = c := by
  grind
  -- ▸ 将 a, b, c 加入 E-graph
  -- ▸ 由 h1 合并 {a, b}，由 h2 合并 {b, c}
  -- ▸ 传递得 {a, b, c} 同一等价类，目标成立
```

```
-- [可运行] congruence：等式穿过函数
example (h : a = b) : f (g a) = f (g b) := by
  grind
  -- ▸ a = b → merge(a,b)
  -- ▸ congruence: g(a), g(b) 参数同类 → merge(g(a), g(b))
  -- ▸ congruence: f(g(a)), f(g(b)) 参数同类 → 目标成立
```

与 `simp` 的根本区别：`simp` 做*有向重写*（lhs → rhs），
`grind` 做*无向等式合并*（把两个项放进同一等价类）。
`a = b` 和 `b = a` 对 `grind` 完全等价。

# 12.2 核心算法：Congruence Closure
%%%
tag := "congruence-closure-algorithm"
%%%

## E-graph 数据结构
%%%
tag := "e-graph-data-structure"
%%%

`grind` 内部维护一个 *E-graph*（equality graph），由两部分组成：

- *Union-Find*：维护等价类，支持 `merge(a, b)` 和 `find(a)`
- *Term DAG*：记录项的结构，如 `f(a)` 是 `f` applied to `a`

关键不变量：*congruence rule*——若 `find(a₁) = find(b₁)`，
则 `merge(f(a₁), f(b₁))`。每次 merge 后都检查此条件并传播。

## 推理示例
%%%
tag := "reasoning-example"
%%%

```
-- [示意] 假设: {a = b, g(f(a)) = c}，目标: g(f(b)) = c

Step 1 — 初始化：每个子项各自一个等价类
Step 2 — merge(a, b)
  → congruence: f(a) vs f(b) → merge(f(a), f(b))
    → congruence: g(f(a)) vs g(f(b)) → merge(g(f(a)), g(f(b)))
Step 3 — merge(g(f(a)), c) → find(g(f(b))) = find(c) ✓
```

复杂度 *O(n log n)*（n = 项数量），依赖路径压缩 union-find。

# 12.3 E-matching：量化引理的实例化
%%%
tag := "e-matching-quantified-lemmas"
%%%

`grind` 的第二项能力是*自动实例化量化引理*——让外部知识参与 E-graph 推理。

用 `@[grind]` 标记引理后，`grind` 提取其*模式*（如 `f (g ?x)`），
运行时在 E-graph 中搜索匹配项，找到则实例化引理、加入新等式。
新等式可能触发更多 congruence 和 E-matching，直到 fixpoint。

```
-- [示意型工作流] 注册一条 E-matching 引理（具体行为可能随版本变化）
@[grind] theorem fg_inv : ∀ x, f (g x) = x := sorry

example (h : y = g a) : f y = a := by
  grind
  -- ▸ 由 h: merge(y, g(a)) → congruence: merge(f(y), f(g(a)))
  -- ▸ E-match: f(g(a)) 匹配 f(g(?x))，x := a
  -- ▸ 实例化 fg_inv: merge(f(g(a)), a)
  -- ▸ f(y) ~ f(g(a)) ~ a → 目标成立 ✓
```

## `@[grind]` vs `@[simp]`
%%%
tag := "grind-vs-simp-attributes"
%%%

| 属性 | 引理用法 | 方向性 |
|------|----------|--------|
| `@[simp]` | 有向重写 lhs → rhs | 单向，lhs 必须是"大"的 |
| `@[grind]` | E-matching pattern trigger | 无向，按模式匹配 |

一条引理可同时标记 `@[simp, grind]`，各在各的引擎中生效。

# 12.4 使用 grind
%%%
tag := "using-grind"
%%%

## 基本调用
%%%
tag := "basic-usage"
%%%

```
-- [可运行] 多步传递 + congruence
example (h1 : f a = b) (h2 : f b = c) (h3 : a = d) : f (f d) = c := by
  grind
  -- ▸ a = d → f(a) = f(d)     (congruence)
  -- ▸ f(a) = b → f(d) = b     (传递)
  -- ▸ f(f(d)) = f(b) = c      ✓
```

## 传入临时引理
%%%
tag := "passing-temporary-lemmas"
%%%

```
-- [可运行] 用方括号传入不带 @[grind] 的引理
theorem aux : ∀ x, f (f x) = x := sorry

example (h : a = f b) : f a = b := by
  grind [aux]
  -- ▸ aux 作为临时 E-matching trigger（仅本次生效）
  -- ▸ 实例化 aux[x := b] 得 f(f(b)) = b
  -- ▸ a = f(b) → f(a) = f(f(b)) = b ✓
```

> *要点*：`grind [lemma]` 中的引理不需要 `@[grind]` 标记。
> 这是控制 E-matching 作用域的推荐方式——避免全局注册带来的爆炸风险。

## 配置参数
%%%
tag := "configuration-options"
%%%

```
-- [示意]
set_option grind.maxSteps 20000 in   -- 步数上限
set_option grind.maxEmatch 2000 in   -- E-matching 实例化上限
example : ... := by grind
```

> *经验法则*：需要 `maxSteps` > 50000 时，通常意味着目标不适合 `grind`。

# 12.5 grind 的内部结构概览
%%%
tag := "grind-internal-structure"
%%%

`grind` 大致由三个阶段组成：*预处理*（拆分 `And`/`Or`、展开 `match`、β/η 规范化）→ *E-graph + congruence closure* → *E-matching 实例化*。此外还集成了简化版线性算术（类似 `omega`）处理偏移量子目标。

预处理解释了为什么 `grind` 能处理不像"纯等式"的目标：

```
-- [可运行] preprocessor 拆开 And
example (h : a = b ∧ b = c) : a = c := by
  grind  -- ▸ preprocessor 拆 h 为 h.1 : a = b, h.2 : b = c，然后 CC 完成
```

# 12.6 grind vs simp vs aesop
%%%
tag := "grind-vs-simp-vs-aesop"
%%%

| 维度 | grind | simp | aesop |
|------|-------|------|-------|
| 核心算法 | congruence closure + E-matching | term rewriting | best-first search |
| 擅长 | 等式传递链、congruence | 化简到 normal form | forward/backward 搜索 |
| 引理方向 | 无向 | 有向 (lhs → rhs) | 按规则类型 |
| 量化引理 | E-matching 实例化 | conditional rewrite | `apply` / `intro` |
| 终止机制 | 步数上限 | fixpoint | 深度上限 |

*用 grind*：等式目标 + 多步等式链；congruence 穿透；自动实例化 `∀` 引理。
*不用 grind*：化简 → `simp`；结构操作 → `aesop`；纯算术 → `omega`；命题逻辑 → `tauto`。

## 组合使用
%%%
tag := "ch12-combining-tactics"
%%%

```
-- [可运行] grind 单独搞定 congruence + 传递
example (f : α → β) (g : β → γ)
    (h1 : a = b) (h2 : b = c) : g (f a) = g (f c) := by
  grind
  -- ▸ a = b = c → f(a) = f(c) → g(f(a)) = g(f(c)) ✓
```

```
-- [可运行] 先用结构化 tactic 拆分，再让 grind 收尾
example (h : a = b ∨ a = c) (h2 : b = d) (h3 : c = d) : a = d := by
  cases h with
  | inl h => grind  -- ▸ a = b = d
  | inr h => grind  -- ▸ a = c = d
```

# 12.7 常见失败模式
%%%
tag := "ch12-common-failure-patterns"
%%%

## 失败 1：目标不是等式
%%%
tag := "failure-non-equality-goal"
%%%

```
-- [可运行] ✗ grind 不做 witness 搜索
example : ∃ x : Nat, x + 1 = 2 := by
  grind  -- 失败：不知道 x 应该取什么值
  -- 修复：exact ⟨1, rfl⟩
```

> *诊断线索*：目标形如 `∃ x, ...` 或 `P ∨ Q`（需要选边）→ `grind` 无能为力。

## 失败 2：定义未展开
%%%
tag := "failure-definition-not-unfolded"
%%%

```
-- [可运行] ✗ grind 不自动展开用户定义
def myf (n : Nat) : Nat := n + 1

example : myf (myf 0) = 2 := by
  grind  -- 失败：E-graph 中 myf 是黑盒
  -- 修复 A：unfold myf; omega
  -- 修复 B：simp [myf]
```

> *核心规则*：`grind`（和 `simp` 一样）*不自动 unfold 用户定义*。
> 要么 `@[grind]` 注册等式引理，要么手动 `unfold`，要么 `simp [f]` 先化简。

## 失败 3：E-matching 爆炸
%%%
tag := "failure-e-matching-explosion"
%%%

```
-- [示意] ✗ 宽泛的 trigger 导致组合爆炸
@[grind] theorem bad_trigger : ∀ x y, f x = g y → h x y = 0 := sorry
-- n 个 f 项 × m 个 g 项 → n×m 次实例化 → 超时
```

*诊断*：`set_option trace.grind.ematch true` 看实例化次数——同一引理上百次 = 太宽泛。
*修复*：移除 `@[grind]`，改用 `grind [specific_instance]` 手动传入；或缩窄模式。

## 失败 4：需要 case split
%%%
tag := "failure-needs-case-split"
%%%

```
-- [可运行] ✗ grind 对 if/match 的 case split 有限
example (h : if b then a = 1 else a = 2) : a = 1 ∨ a = 2 := by
  grind  -- 可能失败
  -- 修复：cases b <;> simp_all
```

> 涉及 `if`/`match` 分支时，先 `split_ifs` 或 `cases` 拆开再让 `grind` 收尾。

## 失败 5：高阶 / dependent types
%%%
tag := "failure-higher-order-dependent-types"
%%%

```
-- [示意] ✗ E-graph 是一阶数据结构
example (h : ∀ f : Nat → Nat, f 0 = 0) : id 0 = 0 := by
  grind  -- 可能失败：量化变量是函数类型
  -- 修复：exact h id
```

E-graph 是一阶结构，量化变量本身是函数时 E-matching 可能找不到合适实例。

# 12.8 调试 grind
%%%
tag := "debugging-grind"
%%%

## Trace 选项
%%%
tag := "ch12-trace-options"
%%%

```
-- [示意]
set_option trace.grind true in        -- 全部推理过程
set_option trace.grind.ematch true in  -- 只看 E-matching 实例化
set_option trace.grind.eqc true in     -- 只看等价类合并
set_option trace.grind.split true in   -- 只看 case split
example : ... := by grind
```

## 调试流程
%%%
tag := "debugging-workflow"
%%%

```
 grind 失败
   │
   ├─ 开 trace.grind true
   │   ├─ E-graph 缺关键项？ → 补引理 grind [lemma] 或 unfold
   │   ├─ 关键等式未合并？   → 检查是否缺中间等式假设
   │   ├─ E-matching 未触发？ → 检查 @[grind] 注册和模式
   │   └─ 实例化爆炸？       → 移除 @[grind]，改手动传入
   │
   └─ 修复后关闭 trace（显著拖慢编译）
```

> *技巧*：先用 `trace.grind.ematch` 单独看，输出比 `trace.grind` 小得多。

# 12.9 实用模式
%%%
tag := "practical-patterns"
%%%

## 模式 A：长等式链 + 深 congruence
%%%
tag := "pattern-long-equality-chain"
%%%

```
-- [可运行] grind 的最佳场景
example (h1 : a = b) (h2 : b = c) (h3 : c = d)
    (h4 : d = e) : f (g a) = f (g e) := by
  grind
  -- ▸ 4 步传递 + 2 层 congruence，一步搞定
  -- ▸ 用 calc 需手写每一步，用 simp 需标注方向
```

## 模式 B：注册领域引理
%%%
tag := "pattern-domain-lemma-registration"
%%%

```
-- [示意] 为代数结构注册引理
@[grind] theorem mul_comm_ab : ∀ (a b : MyGroup), a * b = b * a := sorry
@[grind] theorem mul_assoc_ab : ∀ (a b c : MyGroup),
    a * b * c = a * (b * c) := sorry

example (a b c : MyGroup) : a * b * c = c * (b * a) := by
  grind  -- ▸ E-matching 实例化交换律和结合律
```

> *警告*：交换律 + 结合律是 E-matching 爆炸经典诱因，实践中改用 `ring`/`group`。

## 模式 C：手动拆分 + grind 收尾
%%%
tag := "pattern-manual-split-then-grind"
%%%

手动处理分支逻辑（`Or`/`if`/`match`），每个分支内让 `grind` 完成等式推理。

# 12.10 练习
%%%
tag := "ch12-exercises"
%%%

## 练习 1：基础等式链 ★
%%%
tag := "exercise-12-1"
%%%

```
-- 用一个 tactic 关闭目标
example (h1 : a = b) (h2 : b = c) (h3 : c = d) : f a = f d := by
  sorry
```

等式链 + congruence 是 `grind` 的标准场景。

## 练习 2：传入临时引理 ★★
%%%
tag := "exercise-12-2"
%%%

```
-- 定义引理并传入 grind 使 example 通过
-- theorem my_lemma : ∀ x, f (g x) = x := sorry

example (h : y = g (g a)) : f y = g a := by
  sorry  -- 用 grind [...]
```

需要 `f (g ?x) = ?x`。E-matching 实例化 `x := g(a)` 得 `f(g(g(a))) = g(a)`，
配合 `h` 的 congruence 完成。

## 练习 3：诊断并修复失败 ★★
%%%
tag := "exercise-12-3"
%%%

```
-- 以下 grind 调用会失败，解释原因并修复
def double (n : Nat) : Nat := n + n

example : double 3 = 6 := by
  grind  -- 失败！
```

`grind` 不展开 `double`。修复：`unfold double; omega` 或 `simp [double]`。
展开后是纯算术 `3 + 3 = 6`，`omega` 比 `grind` 更合适。

## 练习 4：控制 E-matching 爆炸 ★★★
%%%
tag := "exercise-12-4"
%%%

```
-- 以下代码可能导致 grind 超时，分析原因并修复
@[grind] theorem inj_f : ∀ x y, f x = f y → x = y := sorry
@[grind] theorem expand_f : ∀ x, f x = g (h x) := sorry

example (h1 : a = b) (h2 : g (h a) = c) : f b = c := by
  grind  -- 可能超时
```

`inj_f` 的 trigger `f ?x = f ?y` 在 `expand_f` 引入新 `f` 项后被反复触发。
修复：移除 `inj_f` 的 `@[grind]`，只保留 `expand_f`：

```
attribute [-grind] inj_f
example (h1 : a = b) (h2 : g (h a) = c) : f b = c := by
  grind [expand_f]
```

> *教训*：全局 `@[grind]` 注册的引理会影响所有 `grind` 调用点，爆炸风险远高于局部 `grind [lemma]`。
> 除非确认引理的 trigger 足够窄，否则优先使用 `grind [lemma]` 按需传入。

## 练习 5：组合 tactic ★★★
%%%
tag := "exercise-12-5"
%%%

```
-- 用 cases + grind 的组合关闭目标
example (h : (a = b ∧ c = d) ∨ (a = d ∧ c = b))
    : f a c = f b d ∨ f a c = f d b := by
  sorry
```

`cases h` 拆 `Or`，每个分支 `obtain ⟨h1, h2⟩ := h` 拆 `And`，
然后 `left; grind` 或 `right; grind`。

# 12.11 小结
%%%
tag := "ch12-summary"
%%%

| 概念 | 要点 |
|------|------|
| grind 定位 | SMT 风格 tactic，擅长等式传递推理 |
| E-graph | union-find + term DAG，O(n log n) congruence closure |
| congruence | `a = b → f(a) = f(b)`，自动穿透任意深度嵌套 |
| E-matching | 在 E-graph 中搜索量化引理的 pattern 并实例化 |
| `@[grind]` | 注册 E-matching trigger，无向（区别于 `@[simp]`） |
| `grind [l]` | 临时传入引理，不污染全局注册，推荐用法 |
| 配置 | `maxSteps`、`maxEmatch`，超限说明目标可能不适合 grind |
| 主要失败 | 非等式目标、缺引理/展开、E-matching 爆炸、case split、高阶项 |
| 调试 | `trace.grind`、`trace.grind.ematch`、`trace.grind.eqc` |
| 组合策略 | 手动拆分分支 + 每分支内 grind 收尾 |

*下一章*：`decide` / `native_decide`——可判定性与内核计算。
