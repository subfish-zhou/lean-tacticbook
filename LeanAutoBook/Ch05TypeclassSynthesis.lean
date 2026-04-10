import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch05TypeclassSynthesis"

#doc (Manual) "第五章 Type Class Synthesis" =>
%%%
file := "Ch05TypeclassSynthesis"
tag := "ch05-typeclass-synthesis"
%%%

*本章目标*：理解 type class synthesis 的搜索机制，掌握在 tactic 元编程中调用、控制和调试实例搜索的方法。

# 5.0 回顾与动机
%%%
tag := "recap-and-motivation"
%%%

在第四章中，你学习了如何在 tactic 框架里管理多个目标——创建子目标、聚焦、切换、合并。
这些操作让你能够把复杂的证明任务分解成若干小步骤。

但 tactic 做的不仅仅是拆分目标。很多自动化 tactic（`simp`、`ring`、`omega`、`aesop`）
在工作时需要*自动发现当前类型具备哪些代数性质*——比如 `Nat` 上有加法，`List α` 上有
`Append` 操作。这些性质通过 *type class instance* 注册，发现它们的过程叫做
*type class synthesis*（实例合成）。

本章回答三个问题：

1. Lean 是怎样自动找到 type class 实例的？（搜索机制）
2. 在元编程中如何主动调用这个搜索？（API 使用）
3. 搜索失败时怎么诊断和修复？（常见失败模式）

下一章讲的 `simp` 正是建立在实例搜索之上——`simp` 需要知道当前类型满足哪些
simp lemma，而 lemma 的适用性往往由 type class 实例判定。

# 5.1 Type Class 的双重角色
%%%
tag := "typeclass-dual-role"
%%%

Type class 在 Lean 4 中同时扮演两个角色：

*角色一：接口抽象。* 定义类型需要支持的操作，类似其他语言的 interface / trait。

```
-- [示意] type class 的基本定义形式
class Add (α : Type) where
  add : α → α → α
```

*角色二：自动搜索。* 当编译器看到方括号参数 `[Add α]` 时，它会在已注册的实例中自动寻找匹配项。

```
-- [示意] 方括号参数触发自动搜索
def double [Add α] (x : α) : α := Add.add x x
-- 写 `double 3` 时，Lean 自动搜索 `Add Nat` 的实例并填入
```

对 tactic 编写者来说，*第二个角色更重要*——很多 tactic 需要在运行时动态查询当前类型满足哪些性质。`ring` 需要知道类型是否构成交换环，`simp` 需要知道有哪些化简规则可用。这些查询的底层机制就是 type class synthesis。

# 5.2 Synthesis 的搜索过程
%%%
tag := "synthesis-search-process"
%%%

当 Lean 需要寻找一个 type class 实例（比如 `Add (Fin n)`）时，搜索按以下步骤进行。

## 第一步：查缓存
%%%
tag := "step-check-cache"
%%%

Lean 使用 *tabled resolution*（带记忆化的搜索）。之前搜索过的结果会被缓存，同一个实例可能在一次编译中被请求成千上万次，缓存避免了重复搜索。

## 第二步：展开候选实例
%%%
tag := "step-expand-candidates"
%%%

缓存未命中时，Lean 遍历所有 `@[instance]` 声明，逐一尝试 *unification*。

```
-- [伪代码] 搜索 Add (Fin n)
目标：Add (Fin n)
  ├─ 候选 instAddFin : Add (Fin n)     ← unify 成功！
  ├─ 候选 instAddNat : Add Nat         ← unify 失败（Fin n ≠ Nat）
  └─ ...
```

## 第三步：递归搜索前提
%%%
tag := "step-recursive-search"
%%%

如果候选实例依赖其他 type class（有 `[...]` 参数），Lean 递归搜索这些前提。

```
-- [示意] 有前提的实例
instance [Add α] : Add (Option α) where
  add
    | some a, some b => some (Add.add a b)
    | _, _ => none
```

搜索 `Add (Option Nat)` 时，Lean 发现需要先找 `Add Nat`，触发递归：

```
-- [伪代码] 递归搜索
目标：Add (Option Nat)
  └─ 候选 instAddOption : [Add α] → Add (Option α)
       ├─ unify：α := Nat
       └─ 递归目标：Add Nat  ← 成功！
```

## 第四步：深度限制
%%%
tag := "step-depth-limit"
%%%

Lean 通过两个参数控制搜索规模：
- *`synthInstance.maxHeartbeats`*：最大计算步数（默认 20000）
- *`synthInstance.maxSize`*：搜索树最大节点数

超限后搜索终止报错，防止循环依赖导致无限搜索。

> *注意*：Synthesis 不只搜索全局注册的 `@[instance]` 声明，也会考虑当前*局部上下文*中的实例——例如函数签名里的 `[Add α]` 参数、`haveI` 引入的实例、以及 `withNewLocalInstance` 临时注册的实例，都会参与搜索。

## 优先级
%%%
tag := "instance-priority"
%%%

每个实例有一个优先级数值（`@[instance N]`），N 越大越优先，默认 1000。

```anchor instancePriority
inductive MyType where
  | mk

instance (priority := 2000) myTypeToStringHigh : ToString MyType where
  toString _ := "MyType(high)"

instance (priority := 100) myTypeToStringLow : ToString MyType where
  toString _ := "MyType(low)"
```

当你对同一类型有通用实例和特化实例时，给特化实例更高优先级可以控制选择偏好。

> *提醒*：重叠实例加优先级是为*不可避免的冲突*而设计的应急手段，不鼓励主动制造同头实例。优先设计不重叠的实例结构；只有在库兼容性等外部约束下无法避免时，再用优先级消歧。

# 5.3 在 MetaM 中调用 Synthesis
%%%
tag := "synthesis-in-metam"
%%%

编写 tactic 时，你经常需要在 `MetaM` 中手动触发实例搜索。

## `synthInstance`：失败即报错
%%%
tag := "synth-instance-throws"
%%%

```
-- [示意]
synthInstance (type : Expr) : MetaM Expr
```

传入 type class 类型的 `Expr`，返回找到的实例项。搜索失败时抛异常。

```
-- [示意] 在 tactic 中搜索 Add Nat
elab "demo_synth" : tactic => do
  let addNatType ← mkAppM ``Add #[mkConst ``Nat]
  let inst ← synthInstance addNatType
  logInfo m!"找到实例：{inst}"
```

这里 `mkAppM` 会自动处理 universe 和隐式参数，比手动 `mkApp` + `mkConst` 更安全。

## `synthInstance?`：失败返回 `none`
%%%
tag := "synth-instance-optional"
%%%

```
-- [示意]
synthInstance? (type : Expr) : MetaM (Option Expr)
```

当你需要*探测*实例是否存在而非一定要找到它时，用这个版本。

```
-- [示意] 根据 Decidable 实例选择策略
elab "smart_decide" : tactic => withMainContext do
  let target ← getMainTarget
  let decType ← mkAppM ``Decidable #[target]
  match ← synthInstance? decType with
  | some _ => logInfo "目标可判定，使用 decide"
  | none   => logInfo "目标不可判定，需要其他方法"
```

## `isInstance`：检查声明是否是实例
%%%
tag := "is-instance-check"
%%%

```
-- [示意]
isInstance (declName : Name) : CoreM Bool
```

遍历环境中的声明并筛选实例时会用到。

# 5.4 实际应用：检查交换律
%%%
tag := "practical-check-commutativity"
%%%

下面用一个*语义示意*来展示 synthesis 在 tactic 中的典型调用模式。注意：这段代码侧重演示"从目标提取信息 → 构造搜索目标 → 探测实例"的流程，并非推荐的落地模板——实际 tactic 需要处理更多边界情况（如隐式参数、universe level 等）。

```
-- [示意·语义演示，非落地模板] 检查运算是否满足交换律
elab "check_comm" : tactic => withMainContext do
  let target ← getMainTarget
  let some (α, lhs, _rhs) := target.eq?
    | throwError "目标不是等式"
  match lhs with
  | .app (.app f _a) _b =>
    let commType ← mkAppM ``Commutative #[f]
    match ← synthInstance? commType with
    | some _ => logInfo "运算满足交换律！"
    | none   => logInfo "未找到交换律实例"
  | _ => throwError "左侧不是二元运算应用的形式"
```

这展示了典型模式：从目标提取类型 → `mkAppM` 构造搜索目标 → `synthInstance?` 探测 → 根据结果分支。

# 5.5 Synthesis 与其他查找机制
%%%
tag := "synthesis-vs-other-lookup"
%%%

Type class synthesis 不是唯一的"按类型查找"机制。理解区别帮你选对工具。

*DiscrTree*（discrimination tree）：按表达式骨架索引，`simp` 和 `aesop` 用它匹配引理。和 synthesis 的区别——synthesis 返回唯一实例项，DiscrTree 返回候选列表。

```
-- [示意]
DiscrTree.getMatch (dt : DiscrTree α) (e : Expr) : MetaM (Array α)
```

*`getEqnsFor?`*：获取函数的展开方程式引理，不涉及 type class。

```
-- [示意]
let eqns ← Meta.getEqnsFor? declName
-- eqns : Option (Array Name)
```

| 需求 | 用什么 |
|------|--------|
| 查找 type class 实例 | `synthInstance` / `synthInstance?` |
| 按表达式形状匹配引理 | `DiscrTree.getMatch` |
| 获取函数展开方程 | `getEqnsFor?` |

# 5.6 控制 Synthesis 行为
%%%
tag := "controlling-synthesis-behavior"
%%%

## 调整搜索预算
%%%
tag := "adjust-search-budget"
%%%

```
-- [示意] 临时增加搜索预算
withOptions (fun o => o.set `synthInstance.maxHeartbeats 80000) do
  let inst ← synthInstance goalType
```

注意：*盲目增大预算不是正解*。超时通常说明实例注册有问题（见 5.7 节）。

## 临时添加局部实例
%%%
tag := "temporary-local-instance"
%%%

```
-- [示意]
-- withNewLocalInstance (className : Name) (fvar : Expr) (body : MetaM α)
-- 在 body 执行期间，把 fvar 注册为 className 的临时实例
```

典型用途：把 hypothesis 中的 type class 约束临时注册为实例，让后续 synthesis 能找到它。

## 用户侧控制
%%%
tag := "user-side-control"
%%%

```anchor synthInstanceMaxHeartbeats
structure MyComplexType where
  val : Nat

instance : Add MyComplexType where
  add a b := ⟨a.val + b.val⟩

set_option synthInstance.maxHeartbeats 40000 in
example : Add (MyComplexType × MyComplexType) := inferInstance
```

# 5.7 常见失败模式
%%%
tag := "common-failure-patterns"
%%%

## 失败一：找不到实例（No Instance Found）
%%%
tag := "failure-no-instance-found"
%%%

*症状*：`failed to synthesize instance Add MyType`。

常见原因：忘记定义实例、没有 import 实例所在模块、类型参数含有未解决的 metavariable。

```anchor noInstanceFound
structure Point where
  x : Nat
  y : Nat

-- 忘记注册实例：
-- instance : Add Point where
--   add p q := ⟨p.x + q.x, p.y + q.y⟩

-- 下面会报错：failed to synthesize Add Point
-- #check (inferInstance : Add Point)
```

*诊断*：用 `#check (inferInstance : TargetClass TargetType)` 手动测试。成功则问题在 `Expr` 构造，失败则问题在实例注册。

## 失败二：实例歧义 / Diamond Problem
%%%
tag := "failure-diamond-problem"
%%%

*症状*：找到多个实例无法决定，或多重继承路径不一致。

```
-- [示意] Diamond problem
class A (α : Type)
class B (α : Type) extends A α
class C (α : Type) extends A α
class D (α : Type) extends B α, C α
-- D → B → A 和 D → C → A 必须 definitionally equal
```

*诊断*：`set_option trace.Meta.synthInstance true` 查看完整搜索过程。

```anchor traceSynthInstance
set_option trace.Meta.synthInstance true in
#check (inferInstance : Add Nat)
```

## 失败三：循环依赖导致超时
%%%
tag := "failure-cyclic-dependency"
%%%

*症状*：`maxHeartbeats` 超限。

```
-- [示意] 循环实例——不要这样写！
instance [B α] : A α where ...
instance [A α] : B α where ...
-- A α → B α → A α → ... 无限循环
```

Tabled resolution 能处理某些循环（缓存命中时），但如果每步涉及新类型参数，缓存帮不上忙。

*修复*：打破循环——去掉一个方向的实例，或改成非 instance 的普通定义。

## 补充陷阱：Universe 与 Out-parameter
%%%
tag := "pitfall-universe-out-param"
%%%

用 `mkConst` 时需提供 universe level 参数，遗漏会导致错误。推荐用 `mkAppM` 自动处理：

```
-- [示意] mkAppM 自动推导 universe
let type ← mkAppM ``Add #[mkConst ``Nat]
```

对有 *out-parameter* 的 type class（如 `HAdd`），synthesis 完成后要读取 metavariable 赋值来获取推断出的输出类型。

# 5.8 练习
%%%
tag := "ch05-exercises"
%%%

## 练习 1（热身）：探测 BEq 实例
%%%
tag := "exercise-5-1"
%%%

编写 `elab` 命令 `has_beq`，接受一个类型名，报告该类型是否有 `BEq` 实例。

```
-- [示意] 实现后的预期调用形式
-- #has_beq Nat         →  "Nat 有 BEq 实例"
-- #has_beq (Nat → Nat) →  "Nat → Nat 没有 BEq 实例"
```

提示：`synthInstance?` + `mkAppM` 构造 `BEq` 类型。

## 练习 2（热身）：观察搜索过程
%%%
tag := "exercise-5-2"
%%%

用 trace 选项观察实例搜索，回答：搜索 `Add (List Nat)` 触发了几次递归？

```
-- [可运行]
set_option trace.Meta.synthInstance true in
#check (inferInstance : Add (List Nat))
```

## 练习 3（Debug）：诊断超时
%%%
tag := "exercise-5-3"
%%%

下面的代码会导致 synthesis 超时，解释原因并修复。

```
-- [示意] 超时代码
class Serialize (α : Type) where
  serialize : α → String

class Deserialize (α : Type) where
  deserialize : String → Option α

instance [Deserialize α] : Serialize α where
  serialize _ := "serialized"

instance [Serialize α] : Deserialize α where
  deserialize _ := none

-- 超时：example : Serialize Nat := inferInstance
```

提示：画依赖箭头找环。修复方案：可以为 `Nat` 提供直接的 base instance 打破循环，也可以去掉形成环的某条 instance 边（改为普通 `def`），根据实际需求选择。

## 练习 4（综合）：自动交换律改写
%%%
tag := "exercise-5-4"
%%%

编写 tactic `comm_rw`：

1. 检查目标是否是等式 `a op b = c op d`
2. 用 `synthInstance?` 检查 `op` 是否满足 `Commutative`
3. 满足则用交换律改写左侧为 `b op a`；不满足则报错

```
-- [示意] 预期行为
-- example (a b : Nat) : a + b = b + a := by comm_rw; rfl
```

提示：结合第三章 `Expr` 操作、第四章目标管理、本章 `synthInstance?`。

# 5.9 小结
%%%
tag := "ch05-summary"
%%%

| 概念 | 关键点 | 何时用到 |
|------|--------|----------|
| Type class synthesis | tabled resolution + 优先级 | 涉及 `[...]` 参数时 |
| `synthInstance` | 搜索实例，失败报错 | 确定实例必须存在 |
| `synthInstance?` | 失败返回 `none` | 探测/分支策略 |
| 优先级 | `@[instance N]`，N 越大越优先 | 控制候选选择顺序 |
| `withOptions` | 临时调整搜索参数 | 搜索预算不足 |
| `withNewLocalInstance` | 临时注册局部实例 | 把 hypothesis 变成实例 |
| DiscrTree | 按表达式骨架索引引理 | `simp`/`aesop` 式匹配 |
| `trace.Meta.synthInstance` | 打印搜索过程 | 诊断 synthesis 问题 |

*三条实用原则*：

1. *先用 `synthInstance?` 探测，再决定策略。* 不要假设实例一定存在。
2. *超时时先查循环，再考虑加预算。* 加预算是治标不治本。
3. *用 trace 诊断。* `set_option trace.Meta.synthInstance true` 是调试利器。

# 下一章预告
%%%
tag := "ch05-next-chapter"
%%%

你现在理解了 Lean 如何自动发现类型的性质。下一章深入讲解 *`simp`*——Lean 4 中最常用的自动化 tactic。`simp` 的工作依赖 simp lemma 数据库，而哪些 lemma 适用于当前目标，往往由 type class synthesis 来判断。掌握本章知识，你将更容易理解 `simp` 内部的匹配和改写逻辑。
