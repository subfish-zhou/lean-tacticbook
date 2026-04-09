import VersoManual

open Verso.Genre Manual

#doc (Manual) "第一章 Lean 4 元编程模型" =>
%%%
file := "Ch01MetaprogrammingModel"
tag := "ch01-metaprogramming-model"
%%%

*本章目标*：理解 Lean 4 的元编程层次结构，建立"tactic 是什么、在哪里运行、怎么工作"的心智模型。

# 1.1 为什么要理解元编程模型？

当你写下 `simp` 或 `linarith`，你调用的不只是一个函数——你在执行一段 *元程序*：一段在 Lean 的推导引擎内部运行、操作证明状态的程序。

理解 tactic 的实现，第一步是理解它们运行的"操作系统"：Lean 4 的元编程 monad 栈。

# 1.2 Monad 栈：从底层到顶层

Lean 4 的元编程由四层 monad 组成，从底到顶依次叠加：

```
CoreM          ← 基础层：环境 + 名字生成器 + 选项
  └─ MetaM     ← 元变量 + 局部上下文 + 类型检查
      └─ TermElabM  ← 项的精化（elaboration）
          └─ TacticM    ← tactic 框架：目标列表管理
```

每一层的定义都能在 Lean 源码中找到：

```
-- Lean/CoreM.lean
abbrev CoreM := ReaderT Context <| StateRefT State (EIO Exception)

-- Lean/Meta/Basic.lean
abbrev MetaM := ReaderT Context $ StateRefT State CoreM

-- Lean/Elab/Term.lean
abbrev TermElabM := ReaderT Context $ StateRefT State MetaM

-- Lean/Elab/Tactic/Basic.lean
abbrev TacticM := ReaderT Context $ StateRefT State TermElabM
```

每一层都是 `ReaderT Context (StateRefT State ...)` 的模式：有只读的 `Context`（配置/环境），有可变的 `State`（当前状态）。

## CoreM：基础层

`CoreM` 是整个系统的地基。它的 `State` 包含：

```
structure State where
  env           : Environment      -- 当前环境（所有定义/定理）
  nextMacroScope: MacroScope       -- 宏展开用的作用域计数器
  ngen          : NameGenerator    -- 唯一名字生成器
  traceState    : TraceState       -- trace 信息
  messages      : MessageLog       -- 错误/警告消息
```

它的 `Context` 包含：

```
structure Context where
  fileName      : String           -- 当前文件名
  options       : Options          -- 用户选项（set_option）
  currNamespace : Name             -- 当前命名空间
  maxHeartbeats : Nat              -- 超时限制
  currMacroScope: MacroScope       -- 当前宏作用域
```

`CoreM` 能做什么：查询/修改环境、生成新名字、记录消息、读取选项。*不能*做类型检查或创建元变量。

## MetaM：元变量与类型检查

`MetaM` 在 `CoreM` 之上添加了：

- *`LocalContext`*：当前的局部变量（free variables, `FVarId`）
- *`MetavarContext`*：所有元变量（`MVarId`）的声明和赋值
- *类型检查缓存*：`inferType`、`isDefEq`、`whnf` 的结果缓存

`MetaM` 是 Lean 元编程的核心层。以下关键操作都在 `MetaM` 中：

| 操作 | 说明 |
|------|------|
| `inferType e` | 推断表达式 `e` 的类型 |
| `isDefEq e1 e2` | 判断两个表达式是否定义等价（可能赋值元变量） |
| `whnf e` | 将表达式规约到弱头范式 |
| `mkFreshExprMVar t` | 创建类型为 `t` 的新元变量 |
| `forallTelescope T f` | 展开 `∀` 类型，进入其 body |
| `lambdaTelescope e f` | 展开 `λ` 表达式，进入其 body |

## TermElabM：项的精化

`TermElabM` 处理从语法到表达式的转换（elaboration）。当你写 `x + 1`，elaborator 负责：
- 推断 `x` 的类型
- 找到合适的 `+` 实例
- 插入隐式参数

对于 tactic 编写者，`TermElabM` 主要用于在 tactic 中使用 `elabTerm` 将语法片段精化为表达式。

## TacticM：目标管理

`TacticM` 是 tactic 的直接运行环境。它的 `State` 核心很简单：

```
-- Lean/Elab/Tactic/Basic.lean
structure State where
  goals : List MVarId   -- 当前待证目标列表

abbrev TacticM := ReaderT Context $ StateRefT State TermElabM
abbrev Tactic  := Syntax → TacticM Unit
```

*关键心智模型*：一个 tactic 接收一个 `goals : List MVarId`，执行某些操作后产生新的 `goals`。"证明完成"就是 `goals` 变为空列表。

基本的目标操作：

```
def getGoals : TacticM (List MVarId)      -- 获取当前所有目标
def setGoals (gs : List MVarId) : TacticM Unit  -- 设置目标列表
def getMainGoal : TacticM MVarId          -- 获取第一个目标
def getMainTarget : TacticM Expr          -- 获取第一个目标的类型（命题）
```

# 1.3 关键类型速览

理解元编程需要熟悉这几个核心类型：

## Name

Lean 中一切都有名字。`Name` 是一个层次化的标识符：

```
-- `Nat.add` 表示为：
Name.str (Name.str Name.anonymous "Nat") "add"
-- 或用反引号语法：
``Nat.add
```

在元程序中，你会频繁用到反引号语法来引用名字。

## Expr

表达式树，Lean 中所有项的内部表示。详见第二章。

## FVarId 与 MVarId

- *`FVarId`*（free variable id）：局部上下文中的变量的唯一标识。当你在证明中引入假设 `h : P`，`h` 就是一个 `FVarId`。
- *`MVarId`*（metavariable id）：元变量的唯一标识。每个未解决的证明目标就是一个 `MVarId`。

# 1.4 tactic 是怎么注册和调用的

## 注册：`elab` 和 `macro`

在 Lean 4 中，注册一个新 tactic 有两条路：

*方式一：`macro`*（语法糖，展开为其他 tactic）

```
macro "my_rfl" : tactic => `(tactic| rfl)
```

`macro` 在语法层面展开，不进入 `TacticM`。适合简单的 tactic 组合。

*方式二：`elab`*（完整的语义实现）

```
syntax "my_assumption" : tactic

elab_rules : tactic
  | `(tactic| my_assumption) => do
    let goal ← getMainGoal
    let lctx ← getLCtx
    for decl in lctx do
      if ← isDefEq decl.type (← goal.getType) then
        goal.assign decl.toExpr
        return
    throwTacticEx `my_assumption goal "no matching hypothesis"
```

`elab_rules` 进入 `TacticM`，可以完整访问证明状态。

## 调用流程

当 Lean 解析 `by simp` 时：
1. `by` 关键字触发 tactic block 的解析
2. `simp` 被匹配到它注册的 `elab_rules`
3. 当前目标列表作为 `TacticM` 的状态传入
4. `simp` 的实现运行，修改目标列表
5. 剩余目标继续处理后续 tactic

# 1.5 第一个 tactic：从零开始

来写一个有实际功能的最小 tactic。目标：实现 `trace_goal`，打印当前目标然后什么都不做。

```
-- [可运行]
import Lean
open Lean Elab Tactic Meta

syntax "trace_goal" : tactic

elab_rules : tactic
  | `(tactic| trace_goal) => do
    let goal ← getMainGoal           -- 获取第一个目标的 MVarId
    let goalType ← goal.getType      -- 获取目标类型（Expr）
    let goalPP ← ppExpr goalType     -- 美化打印
    logInfo m!"Current goal: {goalPP}"

-- 测试
example (n : Nat) : n + 0 = n := by
  trace_goal  -- 输出: Current goal: n + 0 = n
  simp
```

*注意*：`trace_goal` 只打印信息、不改变目标，所以 Lean 可能会显示 `"tactic does nothing"` 的 linter 警告。这不是 bug——tactic 确实运行了，只是没有修改 goal 状态。忽略这个警告即可。

再写一个稍复杂的：`exact_if_rfl`，如果目标是 `a = a` 就用 `rfl` 关闭，否则报错。

```
elab "exact_if_rfl" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  -- 检查目标是否是 a = a 的形式
  let_expr Eq _ lhs rhs := goalType | throwTacticEx `exact_if_rfl goal "goal is not an equality"
  if ← isDefEq lhs rhs then
    goal.assign (← mkEqRefl lhs)  -- 构造 rfl 证明项
  else
    throwTacticEx `exact_if_rfl goal "sides are not definitionally equal"
```

# 1.6 层次之间的穿越

有时你需要从 `TacticM` 调用 `MetaM` 的函数。由于 `TacticM` 包含了 `MetaM`，可以直接调用：

```
elab "show_type" : tactic => do
  let goal ← getMainGoal
  -- inferType 是 MetaM 函数，可以直接在 TacticM 中调用
  let goalType ← goal.getType
  let typeOfType ← inferType goalType  -- Expr 的类型
  logInfo m!"Goal type's type: {← ppExpr typeOfType}"
```

反过来，在 `MetaM` 中运行 `TacticM` 代码，需要手动提供目标：

```
def runTacticInMeta (mvarId : MVarId) (tac : TacticM Unit) : MetaM (List MVarId) :=
  Lean.Elab.Tactic.run mvarId tac
```

# 1.7 小结

| Monad | 核心状态 | 典型操作 |
|-------|---------|---------|
| `CoreM` | `Environment`, `NameGenerator` | 查询定义、生成名字 |
| `MetaM` | `LocalContext`, `MetavarContext` | 类型检查、创建元变量 |
| `TermElabM` | 精化上下文 | 语法→表达式 |
| `TacticM` | `goals : List MVarId` | 操作证明目标 |

*核心原则*：
- tactic 的本质是：接收目标列表，返回（更小的）目标列表
- 每个未解决目标是一个 `MVarId`（元变量）
- 解决目标 = 给元变量赋值一个正确的证明项

# 1.8 常见失败模式与 debug

## 失败 1：`unknown identifier 'getMainGoal'`

忘记 `open` 相关命名空间了。确保文件顶部有：

```
-- [可运行]
import Lean
open Lean Elab Tactic Meta
```

这四个命名空间覆盖了日常 tactic 编写的绝大多数 API。

## 失败 2：`elab_rules` 里的模式匹配报错

语法声明和 `elab_rules` 的模式名字不一致。检查：

```
-- [示意]
syntax "my_tac" : tactic     -- 这里叫 my_tac

elab_rules : tactic
  | `(tactic| my_tac) => do  -- 这里也必须是 my_tac，不能写成 mytac 或 my-tac
    ...
```

## 失败 3：`goal.assign` 之后还有目标报错

`goal.assign e` 只关闭了 `goal` 这一个目标，但 `setGoals` 里还留着它。正确做法：赋值后 `return`（让框架自动清理），或者手动从 goals 列表中移除。

## 失败 4：`isDefEq` 意外修改了元变量

`isDefEq` 是*有副作用*的——它会在成功时给元变量赋值。如果你只是想探查相等性而不想赋值，用 `withoutModifyingState` 包裹：

```
-- [示意]
let equal ← withoutModifyingState (isDefEq a b)
```

# 1.9 练习

## 练习 1.1（热身）：跑通 `trace_goal`

在你的 Mathlib 项目里新建 `Ch01.lean`，复制 1.5 节的 `trace_goal` 实现，然后验证它能输出当前目标：

```
-- [可运行]
import Lean
open Lean Elab Tactic Meta

syntax "trace_goal" : tactic

elab_rules : tactic
  | `(tactic| trace_goal) => do
    let goal ← getMainGoal
    let goalType ← goal.getType
    let goalPP ← ppExpr goalType
    logInfo m!"Current goal: {goalPP}"

example (n : Nat) : n + 0 = n := by
  trace_goal
  simp
```

打开 VS Code 的 Lean Infoview，把光标放在 `trace_goal` 那一行，你应该能看到目标输出。

## 练习 1.2（热身）：识别 Monad 层次

以下操作各属于哪个 Monad 层？填写括号：

```
 inferType (e : Expr)          → (        )
 logInfo m!"hello"             → (        )
 getMainGoal                   → (        )
 elabTerm stx none             → (        )
 mkFreshExprMVar T             → (        )
```

参考答案：MetaM、CoreM、TacticM、TermElabM、MetaM。

## 练习 1.3（debug）：找出并修复错误

以下 tactic 实现有两处错误，找出来并修复：

```
-- [可运行] 这段代码有错误，修复后应该能关闭 n = n 这类目标
import Lean
open Lean Elab Meta

elab "close_rfl" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let_expr Eq _ lhs rhs := goalType | throwError "not an equality"
  if ← isDefEq lhs rhs then
    goal.assign (mkConst ``Eq.refl)  -- 错误 1
  else
    throwError "not reflexive"

example : (42 : Nat) = 42 := by close_rfl
```

提示：
- *错误 1* 是 proof term 构造错误——`Eq.refl` 需要显式传入类型和值两个参数（用 `mkApp2`）
- *错误 2* 是命名空间可见性错误——`getMainGoal` 在 `Tactic` 命名空间里，`open Lean Elab Meta` 少了 `Tactic`

这两类错误性质不同：一个是 API 调用不完整，一个是符号找不到。以后遇到类似报错时，先判断是哪一类再对症下药。

## 练习 1.4（综合）：实现 `my_rfl`

不用 `macro`，用完整的 `elab_rules` 实现一个 `my_rfl` tactic：如果目标是定义等价的等式（`a = b` 且 `a` 和 `b` 定义等价），用 `rfl` 关闭；否则给出清晰的错误信息（包含目标内容）。

测试用例：

```
-- [可运行] 实现 my_rfl 后，以下应全部通过
example : (2 : Nat) + 3 = 5 := by my_rfl     -- 应通过（计算等价）
example : (0 : Nat) + n = n := by my_rfl       -- 应通过（定义等价）
example (h : n = m) : n = m := by my_rfl       -- 应失败
```

最后一个例子解释：这里的命题 `n = m` 当然是可证的（用 `exact h` 就行），但 `my_rfl` 只能关闭「两侧定义等价」的等式目标，它不会搜索假设中的 `h`。*tactic 的失败不代表命题假，只代表这个 tactic 的适用边界到了*。这种边界意识在后面设计和选用 tactic 时非常重要。

下一章，我们深入 `Expr`——Lean 4 中所有项的内部表示。
