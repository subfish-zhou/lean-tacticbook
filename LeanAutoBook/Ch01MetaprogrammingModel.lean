import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch01MetaprogrammingModel"

#doc (Manual) "Lean 4 元编程模型" =>
%%%
file := "Ch01MetaprogrammingModel"
tag := "ch01-metaprogramming-model"
%%%

> **本章目标**：理解 Lean 4 元编程的四层 monad，能读懂最小 tactic 实现，并知道一段操作为什么能在某一层运行、为什么不能直接反向运行。
>
> **版本基准**：Lean `leanprover/lean4:v4.30.0-rc1`，Mathlib revision `0692ef80fb13`。本章 API 和源码路径均按此版本说明。


# tactic 是一段操作证明状态的元程序
%%%
tag := "tactic-metaprogram"
%%%

当你写 `simp`、`constructor` 或 `linarith` 时，Lean 不只是调用一个数学定理。它会运行一段元程序：读取当前目标和局部假设，构造或检查表达式，更新待证目标，必要时报告失败。

要读 tactic 源码，你需要回答四个问题：

1. 当前代码运行在哪一种 monad 中？
2. 这一层能读取哪些上下文？
3. 这一层能修改哪些状态？
4. 调用下层操作或运行上层操作时，需要怎样转换？

Lean 把这些能力分成 `CoreM`、`MetaM`、`TermElabM`、`TacticM` 四层。先不看定义式。我们从一个 tactic 实际需要什么开始。


# Monad：把返回值与计算效果一起组织
%%%
tag := "monad-effects"
%%%

## 一个 tactic 需要带着哪些东西
%%%
tag := "tactic-required-context"
%%%

先想想一个 tactic 在运行时需要访问和修改什么。假设你要实现一个很简单的 `my_assumption`：它扫描局部假设，找到一个类型与当前目标定义等价的假设，然后用它关闭目标。

这段程序至少需要：

- 当前目标；
- 当前局部上下文，其中含有局部变量和假设；
- 元变量状态，因为定义等价检查可能给元变量赋值；
- 全局环境，因为名字、常量和类型检查依赖已声明内容；
- 选项和消息系统；
- 失败通道，例如“没有找到可用假设”。

为了先看清类型形状，我们用三个概念占位符：

\[伪代码\]
```
Goal   = 当前待证目标的概念占位符
Proof  = 构造出的证明的概念占位符
Error  = 失败信息的概念占位符
```

这里的 `Goal`、`Proof`、`Error` 不是 Lean 已经定义好的类型。它们只是帮助我们讨论接口。

类型 `Goal → Proof` 太窄：它只能表达“给一个目标，直接得到一个证明”，不能在类型中表达环境依赖、状态更新和失败。仍然可以只用普通函数显式编码，但签名会扩展成类似下面的形状：

\[伪代码\]
```
runTactic : Environment → LocalContext → MetaState → Goal
          → Error ⊕ (Proof × MetaState)
```

读这行时按参数顺序走：先给全局环境，再给局部上下文和旧元变量状态，再给目标；失败时返回 `Error`，成功时返回证明和新状态。真实 Lean 的结构更细，参数也不止这些。问题不在于普通函数“做不到”，而在于如果每个辅助函数都显式接收和返回这些内容，组合代码会反复拆包、传参、再装包。

Monad 提供统一接口，把“结果类型”和“运行这段计算所需的效果”放在同一个类型构造器中。`TacticM α` 可以先读作：

> 一段在 tactic 环境中运行的计算；成功结束时产生一个 `α`。

例如：

\[示意\]
```
getMainGoal : TacticM MVarId
getMainTarget : TacticM Expr
setGoals : List MVarId → TacticM Unit
```

第一行运行后得到主目标的 `MVarId`；第二行得到主目标类型的 `Expr`；第三行更新目标列表，返回值只是 `Unit`。

## pure、bind 与显式状态传递
%%%
tag := "pure-bind-state-passing"
%%%

这里说的“副作用”采用广义的 **计算效果（effect）** 含义：失败、读取环境、读写状态和 IO 都算。它不特指修改全局变量，也不意味着代码不纯或不可推理。

一个 monad 主要提供两种组合操作：

\[示意\]
```
pure : α → M α
(>>=) : M α → (α → M β) → M β
```

`pure a` 把普通值 `a` 放入 `M` 计算中，不增加新的效果。`ma >>= f` 先运行 `ma` 得到 `a`，再运行 `f a`。Lean 的 `do` 语法把这种连续的 `>>=` 写得更易读。

`pure` 和 `bind` 还要满足三条 monad laws：左单位律、右单位律和结合律。

- 左单位律：`pure a >>= f = f a`
- 右单位律：`m >>= pure = m`
- 结合律：`(m >>= f) >>= g = m >>= (fun a => f a >>= g)`

这些等式意味着不同的 `do` 括号写法组合出的行为一致。本书不用它们证明什么，但它们是 `bind` 组合可预测的保证。

`do` 中尾位置的 `return a` 精确地表示当前 monad 的 `pure a`，因此最后一行也可以直接写 `pure a`。但 `return a` 出现在非尾位置时，例如 `for`、`if` 或 `match` 的分支中，它是 `do` 语法的提前返回：会跳出整个 `do` block，并以 `pure a` 作为结果。这个控制流类似命令式语言的 `return`，但返回值仍处在当前 monad 中。

状态 monad 最适合展示 `bind` 到底传了什么。先用一个简化定义：

> **本节以下四个 `\[可运行\]` 代码块按顺序放在同一 `.lean` 文件中：`CounterM`、`tick`、`twoTicks`、`twoTicksExpanded`、`twoTicksDo` 是同一份代码的连续片段，后块依赖前块。若你分别复制会报 `unknown identifier`。**

\[可运行\]
```leanFence
abbrev CounterM (α : Type) := StateM Nat α


def tick : CounterM Nat := fun oldState =>
  (oldState, oldState + 1)
```

`tick` 接收旧状态 `oldState`，返回结果 `oldState` 和新状态 `oldState + 1`。现在连续运行两次 `tick`：

\[可运行\]
```leanFence
def twoTicks : CounterM (Nat × Nat) :=
  tick >>= fun first =>
  tick >>= fun second =>
  pure (first, second)

#eval twoTicks.run 10
```

输出是 `((10, 11), 12)`：计算结果是 `(10, 11)`，最终状态是 `12`。下面不使用 `>>=`，把同一过程手动展开：

\[可运行\]
```leanFence
def twoTicksExpanded : CounterM (Nat × Nat) := fun oldState =>
  let (first, stateAfterFirst) := tick oldState
  let (second, stateAfterSecond) := tick stateAfterFirst
  let result := (first, second)
  (result, stateAfterSecond)

#eval twoTicksExpanded.run 10
```

逐行看状态如何移动：

1. `oldState` 是整段计算收到的初始状态 `10`。
2. 第一次 `tick oldState` 返回结果 `10`，并产生 `stateAfterFirst = 11`。
3. 第二次调用没有再使用 `oldState`，而是接收 `stateAfterFirst`，因此返回结果 `11`，产生 `stateAfterSecond = 12`。
4. 普通返回值组合成 `(10, 11)`。
5. 整段计算把结果与最后状态一起返回。

`bind` 做的关键工作就是把上一步产生的新状态交给下一步。`do` 语法隐藏了这条管线，但没有删除它：

\[可运行\]
```leanFence
def twoTicksDo : CounterM (Nat × Nat) := do
  let first ← tick
  let second ← tick
  return (first, second)
```

这也是后面看到 `let goal ← getMainGoal` 时应采用的读法：运行右侧计算，自动沿 monad 传递上下文与状态，把普通结果绑定到左侧名字。

## Reader、State 与 Except
%%%
tag := "reader-state-except"
%%%

### Reader：读取固定上下文
%%%
tag := "reader-context"
%%%

`ReaderT ρ m α` 表示一段运行时可以读取上下文 `ρ`、最终在下层 monad `m` 中得到 `α` 的计算。它不会通过 Reader 接口修改这份上下文。

在 `CoreM` 中，`Options`、当前文件名、当前命名空间等位于 `Core.Context`，适合作为 Reader 能力的例子。下面用一个独立小例子展示读取选项：

\[可运行\]
```leanFence
import Lean
open Lean

abbrev OptionsReader (α : Type) := ReaderM Options α


def readTraceFlag : OptionsReader Bool := do
  let options ← read
  return options.getBool `trace.Meta.Tactic.simp.rewrite false
```

`read` 得到当前 `Options`。这段计算只读取它；若要临时换一份上下文，应使用局部运行或 `withReader`（在一小段子计算中临时替换只读上下文，函数体外恢复原样）一类操作，而不是把 Reader 当作可写状态。

全局 `Environment` 不能用作“只在 `Core.Context` 中读取”的例子，因为它实际位于 `Core.State`，Core 操作可以更新环境。

### State：读取并更新状态
%%%
tag := "state-updates"
%%%

`StateM σ α` 可以理解为函数 `σ → α × σ`：输入旧状态，输出普通结果和新状态。`StateT σ m α` 把同一结构叠在下层 monad `m` 上。

\[可运行\]
```leanFence
abbrev NatState (α : Type) := StateM Nat α


def bumpTwice : NatState Nat := do
  modify (· + 1)
  modify (· + 1)
  get

#eval bumpTwice.run 40
```

结果是 `(42, 42)`：返回值为 `42`，最终状态也是 `42`。

Lean 元编程常用 `StateRefT`。它与纯 `StateT` 的状态传递接口相似，但基于 `ST.Ref`（可变引用；`get` 读、`set` 写，原地更新保存的值不复制状态）实现，以减少大状态频繁复制的成本。`Meta.State` 中的 `MetavarContext` 和 `Tactic.State` 中的目标列表都需要更新。

### Except：成功或失败
%%%
tag := "except-failure"
%%%

`Except ε α` 表示一个基础计算结果：要么是 `.ok a`，要么是 `.error e`。`ExceptT ε m α` 则把这种失败能力叠到已有下层 monad `m` 上。

下面读取一个字符串并解析整数；失败分支与返回类型一致，不再出现“先读 `Nat`，再检查它是否小于零”这种不可能条件。

\[可运行\]
```leanFence

def parseInt (input : String) : Except String Int := do
  match input.toInt? with
  | some value => return value
  | none => throw s!"not an integer: {input}"

#eval parseInt "-12"
#eval parseInt "twelve"
```

在 tactic 中，“目标不是等式”“没有主目标”“没有找到匹配假设”都可以通过异常通道报告。异常传播意味着某一步失败后，后续 `do` 步骤不再执行。

## 把能力叠成 monad transformer 栈
%%%
tag := "monad-transformer-stack"
%%%

真实 tactic 同时需要读上下文、写状态和失败。可以把这些能力逐层叠加：

\[可运行\]
```leanFence
abbrev MyM (α : Type) :=
  ReaderT String (StateT Nat (Except String)) α
```

从外向内读：

1. `ReaderT String ...` 增加只读 `String` 上下文；
2. `StateT Nat ...` 增加可写 `Nat` 状态；
3. 最内层 `Except String` 提供失败通道；
4. `α` 是成功时的普通结果。

最内层使用 `Except String`，而不是 `ExceptT String m`，因为这里已经到达基础 monad，不再有需要保留的下层 `m`。如果还要在 IO 上增加异常，才会写成 `ExceptT String IO α` 一类结构。

`ReaderT`、`StateT`、`ExceptT` 名字末尾的 `T` 表示 transformer：它接收一个已有 monad，并在外面增加一种计算结构。说“每加一层 `XxxT` 就多一种能力”时要附带前提：相应的 lifting 和 typeclass 实例存在。否则外层代码未必能直接调用下层操作，也未必能用统一的 `read`、`get` 或 `throw` 接口。

## 为什么 Lean 用 monad 组织这些能力
%%%
tag := "why-lean-uses-monads"
%%%

不用 monad 也能显式传递所有参数和状态。Lean 选择 monad，主要得到以下工程性质：

1. **签名集中表达能力层**：`getMainGoal : TacticM MVarId` 暴露它运行在 `TacticM` 中，不展开环境、状态、异常和 IO 的几十个细节参数。
2. **状态按组合顺序传递**：`bind` 把前一步的新状态交给后一步，`do` 语法负责组织这条管线。
3. **异常自动传播**：中间步骤失败时，后续步骤不执行，错误沿调用链返回。
4. **局部控制可回溯状态**：`withoutModifyingState` 可以运行一次探查并丢弃该 monad 管理的状态修改；`withLCtx` 可以在局部上下文中运行一段 Meta 计算。
5. **层次之间可以 lifting**：当实例存在时，外层 monad 可以直接调用下层操作，调用方不必手写每一次封装。

第四点有边界：回滚 monad 的可回溯状态不等于回滚世界。已经打印到终端的文本、写入文件的内容或其他 IO 效果不会因为状态恢复而消失。打印出去的话比元变量更难收回来，这一点很符合日常经验。

## 读 do 代码的四条规则
%%%
tag := "reading-do-notation"
%%%

1. `M α` 表示“一段在 `M` 中运行、成功后产生 `α` 的计算”。`MetaM Expr` 不是一个 `Expr`，而是一段会得到 `Expr` 的 Meta 计算。
2. `let x := e` 不运行 monadic 计算，只把右侧表达式本身绑定给 `x`。例如 `let x := getMainGoal` 之后，`x : TacticM MVarId`。
3. `let x ← e` 运行 `e`，并把普通结果绑定给 `x`。例如 `let x ← getMainGoal` 之后，`x : MVarId`。
4. 尾位置的 `return a` 等于当前 monad 的 `pure a`；非尾位置的 `return a` 会提前结束整个 `do` block，并以 `pure a` 作为结果。

再加一条执行规则：`do` 从上到下组合步骤；某一步抛出异常后，后面的步骤不会运行。


# 四层 monad 栈
%%%
tag := "four-monad-layers"
%%%

Lean v4.30 的四层定义可以写成下面的结构。先解释三种语法：

- `abbrev A := B` 声明可展开的类型别名；它给复杂类型一个短名字。
- `f <| x` 与 `f x` 相同；`<|` 是低优先级的右结合应用，常用来减少括号。
- `f $ x` 也表示低优先级应用。Lean 源码中两种写法都可能出现，本章展开时统一写括号。

每一层都叫 `Context` 和 `State`，但它们属于不同命名空间：`Core.Context`、`Meta.Context`、`TermElab.Context`、`Tactic.Context` 不是同一个类型；四个 `State` 也同理。源码打开相应命名空间后会省略前缀，初读时很容易把四个同名结构看成一家四胞胎。

\[源码节选\]
```
-- Lean/CoreM.lean
abbrev CoreM := ReaderT Core.Context (StateRefT Core.State (EIO Exception))

-- Lean/Meta/Basic.lean
abbrev MetaM := ReaderT Meta.Context (StateRefT Meta.State CoreM)

-- Lean/Elab/Term/TermElabM.lean
abbrev TermElabM :=
  ReaderT TermElab.Context (StateRefT TermElab.State MetaM)

-- Lean/Elab/Tactic/Basic.lean
abbrev TacticM :=
  ReaderT Tactic.Context (StateRefT Tactic.State TermElabM)
```

这是按本章讲解补全命名空间后的等价写法；源码在打开命名空间后常写成较短的 `Context`、`State`。

把括号全部写出来：

\[示意\]
```
CoreM α
= ReaderT Core.Context
    (StateRefT Core.State
      (EIO Exception)) α

MetaM α
= ReaderT Meta.Context
    (StateRefT Meta.State
      CoreM) α

TermElabM α
= ReaderT TermElab.Context
    (StateRefT TermElab.State
      MetaM) α

TacticM α
= ReaderT Tactic.Context
    (StateRefT Tactic.State
      TermElabM) α
```

外层 monad 可以在 lifting 实例存在时直接调用内层操作。例如 `TacticM` 中可以调用 `MetaM` 的 `inferType`。反过来，`MetaM` 没有 `TermElab.Context`、`TermElab.State`、`Tactic.Context` 和 `Tactic.State`，因此不能凭空运行 `TacticM`；反向运行必须显式提供缺少的上下文和状态。

## CoreM：环境、选项与消息
%%%
tag := "corem-environment"
%%%

`CoreM` 是元编程公共基础。下面只列与本章相关的字段；真实源码还有其他字段。

\[源码节选\]
```
structure Core.State where
  env      : Environment
  messages : MessageLog
  -- 省略若干本章不使用的字段

-- 省略 Core.Context 的部分字段
structure Core.Context where
  fileName      : String
  options       : Options
  currNamespace : Name
  maxHeartbeats : Nat
```

`Environment` 在 `Core.State` 中，因此 Core 计算可以产生更新后的环境。`Options`、`fileName` 和 `currNamespace` 在 `Core.Context` 中，通过 Reader 读取。

`CoreM` 支持查询声明、读取选项、生成名字和记录消息。类型推断、定义等价检查和元变量操作属于上面的 `MetaM` 层。

## MetaM：局部上下文、元变量与类型检查
%%%
tag := "metam-metavariables"
%%%

`MetaM` 在 `CoreM` 外再加一层 `Meta.Context` 和 `Meta.State`。两种经常混淆的数据分属不同位置：

- `LocalContext`：**所在位置**：`Meta.Context`；**读写性质**：Reader；在一段计算中只读；**典型变化**：进入 telescope 或局部绑定时，用新的上下文运行子计算
- `MetavarContext`：**所在位置**：`Meta.State`；**读写性质**：State；可更新；**典型变化**：创建元变量、赋值元变量、定义等价检查求解约束时变化

`LocalContext` 记录当前局部声明。进入 `∀ x, ...` 的 body 时，`forallTelescope` 会用扩展后的局部上下文运行回调；离开回调后，外层上下文仍是原来的那一份。

`MetavarContext` 记录元变量的声明和赋值。调用 `mkFreshExprMVar` 会加入新元变量；`isDefEq` 可能给现有元变量赋值，因此它不是只读判断。

常用 Meta 操作包括：

\[示意\]
```
inferType e
isDefEq e₁ e₂
whnf e
mkFreshExprMVar type
forallTelescope type callback
lambdaTelescope expr callback
```

它们的完整类型会随参数和隐式参数展开得较长。学习 API 时使用 `#check`，不要只记表中的短写。

## TermElabM：预期类型驱动的精译
%%%
tag := "termelabm-elaboration"
%%%

Parser 先把文本变成 `Syntax`；`TermElabM` 再结合环境、局部上下文和预期类型，把 term syntax 精译成 `Expr`。它处理名字解析、重载消解、隐式参数插入、typeclass 综合和约束求解。

同一段语法 `3` 在不同预期类型下会得到不同表达式。下面在命令精译环境中分别要求 `Nat` 和 `Real`：

\[可运行\]
```
import Mathlib
open Lean Elab Term Meta

elab "show_elab_examples" : command => do
  Command.liftTermElabM do
    let natExpr ← elabTerm (← `(3)) (some (mkConst ``Nat))
    let realType ← elabTerm (← `(Real)) none
    let realExpr ← elabTerm (← `(3)) (some realType)
    logInfo m!"Nat expression: {← ppExpr natExpr}"
    logInfo m!"Real expression: {← ppExpr realExpr}"

show_elab_examples
```

第一处预期类型是 `Nat`，数字字面量被精译为自然数表达式。第二处预期类型是 `Real`，精译器需要选择适用于 `Real` 的数字字面量机制，并插入相关隐式信息。表面上都打印成 `3`，内部类型不同；用 `inferType` 可以进一步核对。

隐式参数插入也依赖预期类型。考虑多态函数：

\[可运行\]
```leanFence
import Mathlib

#check @id
#check (id 3 : Nat)
#check (id 3 : Real)
```

`id` 的类型参数没有写在表面语法中。精译 `id 3` 时，Lean 根据参数和预期类型求出隐式类型参数；Nat 版本和 Real 版本插入的类型参数不同。`TermElabM` 负责的正是这类从有省略、有重载的语法到完整核心项的工作。

## TacticM：目标列表管理
%%%
tag := "tacticm-goals"
%%%

`TacticM` 在 `TermElabM` 外增加 tactic 自己的上下文与状态。核心状态是待处理目标列表：

\[源码节选\]
```
-- Lean/Elab/Tactic/Basic.lean；省略 Tactic.State 的其他实现细节
structure Tactic.State where
  goals : List MVarId

abbrev Tactic := Syntax → TacticM Unit
```

常用目标操作：

\[示意\]
```
getGoals : TacticM (List MVarId)
setGoals : List MVarId → TacticM Unit
getMainGoal : TacticM MVarId
getMainTarget : TacticM Expr
```

一个 tactic 读取并更新目标列表。目标数不保证减少：`constructor` 可以把一个合取目标变成两个子目标，`skip` 保持目标不变，重排类 tactic 可以改变顺序。tactic 成功返回也不表示它关闭了目标；整个 tactic block 完成时目标列表必须为空，证明才结束。


# Name、Expr、FVarId 与 MVarId
%%%
tag := "key-metaprogramming-types"
%%%

## Name
%%%
tag := "name-type"
%%%

`Name` 是 Lean 声明和标识符的结构化名字。完全限定名 `Nat.add` 可以用双反引号引用：

\[可运行\]
```leanFence
import Lean
open Lean

#check ``Nat.add
#check `Nat.add
```

双反引号通常表示解析完全限定的声明名；单反引号语法会考虑当前语法和命名空间语境。后续构造常量表达式时会频繁使用 `mkConst` 配合双反引号形式的 `Nat.add`。

## Expr
%%%
tag := "expr-type"
%%%

`Expr` 是 Lean 核心表达式树。常量、函数应用、lambda、forall、自由变量和元变量都以 `Expr` 构造子表示。第二章会逐个展开。

## FVarId
%%%
tag := "fvarid-type"
%%%

`FVarId` 是局部声明的内部标识。用户在证明状态中看到的 `h` 是名字以及对应的局部声明，不等于 `FVarId` 本身。引用这个局部声明的核心表达式写成 `.fvar fvarId`。

例如，局部上下文中可以存在显示名相同或经过改名的声明；内部 id 用来稳定地区分它们。显示名适合给人看，`FVarId` 适合元程序精确引用。

## MVarId
%%%
tag := "mvarid-type"
%%%

`MVarId` 是元变量的内部标识。一个未解决证明目标通常由一个 `MVarId` 表示；引用该元变量的表达式是 `.mvar mvarId`。给目标赋值，就是在 `MetavarContext` 中记录这个元变量由哪个证明表达式解决。


# tactic 的注册、宏展开与执行
%%%
tag := "tactic-registration-execution"
%%%

Lean 需要先知道一段文本属于 tactic 语法，再决定如何处理它。常见入口是 `syntax`、`macro`、`elab` 和 `elab_rules`。

`macro` 做语法到语法的改写。宏本身不进入 `TacticM`，也不直接读取当前目标；但宏展开得到的 tactic 语法仍会交给 tactic elaborator，后者在 `TacticM` 中执行。

\[可运行\]
```leanFence
import Lean

macro "my_assumption_macro" : tactic => `(tactic| assumption)

example (P : Prop) (h : P) : P := by
  my_assumption_macro
```

这段宏只把 `my_assumption_macro` 改写为 `assumption`。真正扫描局部假设的是展开后的 `assumption` tactic。

`elab` 或 `elab_rules` 可以直接注册 tactic elaborator。下面的实现进入 `TacticM`，读取目标与局部上下文：

\[可运行\]
```leanFence
import Lean
open Lean Elab Tactic Meta

elab "my_assumption" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  let localContext ← getLCtx
  for localDecl in localContext do
    unless localDecl.isImplementationDetail do
      let localType ← inferType localDecl.toExpr
      if ← isDefEq localType target then
        goal.assign localDecl.toExpr
        return
  throwError "no matching local assumption"

example (P Q : Prop) (hP : P) (hQ : Q) : P := by
  my_assumption
```

逐行说明如下：

- `let goal ← getMainGoal` 与 `let target ← goal.getType`：取得当前主目标及其类型。
- `let localContext ← getLCtx`：拿到当前局部上下文，也就是可扫描的假设列表。
- `for localDecl in localContext do`：依次遍历每个局部声明。
- `unless localDecl.isImplementationDetail do`：跳过实现细节声明，只检查用户可见的候选假设。
- `let localType ← inferType localDecl.toExpr`：取得这个局部声明对应证明项的类型。
- `if ← isDefEq localType target then`：探查该类型是否与目标定义等价。
- `goal.assign localDecl.toExpr; return`：命中后把该假设作为证明项赋给目标，然后立即跳出整个 `do`。
- 循环结束仍未找到时，`throwError` 报告失败。

这里的 `return` 就是前面提到的非尾位置提前返回：它跳出整个 elaborator，而不是仅仅完成当前迭代。

调用流程可以按下面顺序读：

\[伪代码\]
```
源文本
→ parser 产生 tactic Syntax
→ macro 展开语法（若命中宏）
→ tactic elaborator 根据 Syntax 选择实现
→ 实现在 TacticM 中读取并更新目标
→ elaborator 返回后，框架清理已经解决的目标
```


# 两个最小 tactic
%%%
tag := "minimal-tactics"
%%%

## 打印当前目标：trace\_goal
%%%
tag := "trace-goal-tactic"
%%%

\[可运行\]
```
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

逐步看类型：

1. `getMainGoal : TacticM MVarId`，所以 `goal : MVarId`。
2. `goal.getType` 是 Meta 操作；由于 `TacticM` 能 lift `MetaM`，这里可直接调用，得到 `goalType : Expr`。
3. `ppExpr goalType` 得到用于显示的格式化结果。
4. `logInfo` 把消息加入 Lean 的消息系统。
5. `trace_goal` 没有改目标；下一行 `simp` 负责关闭它。

在 Lean `v4.30.0-rc1` 上运行本例，你会看到目标被打印出来，同时命令行/编辑器给出一条 linter 警告 `'trace_goal' tactic does nothing`。这条警告的意思是：linter 观察到 `trace_goal` 前后目标状态未变，怀疑你不小心写了空 tactic。我们这里的 `trace_goal` 确实是**故意**不改目标的调试工具，忽略警告即可；若想彻底关掉，在文件顶部加 `set_option linter.unusedTactic false`。

## 定义等价时关闭等式：exact\_if\_rfl
%%%
tag := "exact-if-rfl-tactic"
%%%

\[可运行\]
```leanFence
import Lean
open Lean Elab Tactic Meta

elab "exact_if_rfl" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  let_expr Eq _ lhs rhs := target |
    throwError "expected an equality goal"
  unless ← isDefEq lhs rhs do
    throwError "the two sides are not definitionally equal"
  goal.assign (← mkEqRefl lhs)

example : (2 : Nat) + 3 = 5 := by
  exact_if_rfl
```

这个 tactic 检查目标是否为等式，并检查两侧是否定义等价。它不是只匹配表面上写成 `a = a` 的目标；计算规约后相同的两侧也可以通过。`mkEqRefl lhs` 负责构造反身等式证明，并正确处理类型及 universe 信息。


# 层次之间如何调用与运行
%%%
tag := "cross-layer-execution"
%%%

## 外层调用内层：lifting
%%%
tag := "lifting-inner-layers"
%%%

`TacticM` 的下层依次是 `TermElabM`、`MetaM`、`CoreM`。相应实例存在时，外层代码可以直接调用内层操作：

\[可运行\]
```
import Lean
open Lean Elab Tactic Meta

elab "trace_main_target_type" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  let targetType ← inferType target
  logInfo m!"target: {← ppExpr target}"
  logInfo m!"target type: {← ppExpr targetType}"

example : True := by
  trace_main_target_type
  trivial
```

`getMainGoal` 属于 Tactic 层；`goal.getType`、`inferType`、`ppExpr` 属于 Meta 层；`logInfo` 来自更低的公共能力。代码能写在同一个 `do` 中，是因为 lifting 实例把内层计算提升到 `TacticM`。

## 反向运行：必须提供外层所需上下文
%%%
tag := "running-with-context"
%%%

Lean v4.30 中，`Lean.Elab.Tactic.run` 的完整类型是：

\[可运行\]
```leanFence
import Lean
open Lean Elab

#check Lean.Elab.Tactic.run
```

完整签名是 `Tactic.run (mvarId : MVarId) (x : TacticM Unit) : TermElabM (List MVarId)`。`run` 接收一个初始目标和一段已经构造好的 tactic 计算，在 `TermElabM` 中运行，并返回剩余目标列表。它不是 `MetaM (List MVarId)`。若你手里的是 tactic syntax，还需要先经过相应的 tactic elaboration 入口，不能把 `Syntax` 直接当作这里的 `TacticM Unit`。

原因可以从栈定义直接推出。要运行 `TacticM`，需要：

- `Tactic.Context`；
- 初始 `Tactic.State`，其中含目标列表；
- 下层 `TermElabM` 环境；
- 而 `TermElabM` 又依赖 `MetaM` 和 `CoreM` 的 Context/State。

因此，“我在 `MetaM` 中有一个 `MVarId`，所以可以直接运行任意 tactic”不成立。一个目标 id 只标识元变量，不包含 term elaborator 需要的预期类型、待处理元变量、合成信息、语法位置等上下文。反向运行必须显式建立或进入 `TermElabM` 环境，再调用 `Tactic.run`。

可以把方向画成：

\[示意\]
```
TacticM  --lift--> TermElabM --lift--> MetaM --lift--> CoreM 操作

MetaM --不能仅凭一个 MVarId直接运行--> TacticM
      --先提供 TermElabM 与 Tactic 的 Context/State--> 才能运行
```

这也是为什么库 API 会把 `Tactic.run` 放在 `TermElabM` 返回类型中：它保留了运行 tactic syntax 所需的精译上下文，而不是假设 Meta 层已经拥有这些信息。


# 四层职责对照
%%%
tag := "layer-responsibilities"
%%%

- `CoreM`：**主要 Context**：选项、文件名、当前命名空间等；**主要 State**：环境、消息、名字生成器等；**典型工作**：查询／更新环境，记录消息，读取选项
- `MetaM`：**主要 Context**：`LocalContext`、Meta 配置等；**主要 State**：`MetavarContext`、缓存等；**典型工作**：类型推断、定义等价、规约、创建和赋值元变量
- `TermElabM`：**主要 Context**：预期类型和 term elaboration 配置等；**主要 State**：待处理元变量、合成信息等；**典型工作**：把 term `Syntax` 精译为 `Expr`
- `TacticM`：**主要 Context**：tactic 语法与执行上下文；**主要 State**：当前目标列表；**典型工作**：读取并更新目标列表，组织 tactic 执行

Tactic 的成功返回不等于目标数减少。它可以增加、保持或重排目标。整个 tactic block 结束时，目标列表必须为空，证明才完整。


# 常见失败模式与排错
%%%
tag := "ch01-common-failure-patterns"
%%%

## 失败 1：unknown identifier 'getMainGoal'
%%%
tag := "failure-get-main-goal"
%%%

`getMainGoal` 位于 `Lean.Elab.Tactic` 命名空间。确认导入和 `open`：

\[可运行\]
```leanFence
import Lean
open Lean Elab Tactic Meta

#check getMainGoal
```

高频漏项是只写 `open Lean Elab Meta`，少了 `Tactic`。错误发生在名字解析阶段，还没有运行 tactic。

## 失败 2：语法名与 elaborator 模式不一致
%%%
tag := "failure-elaborator-mode"
%%%

\[练习·故意错误\]
```
import Lean
open Lean Elab Tactic

syntax "my_tac" : tactic

elab_rules : tactic
  | `(tactic| mytac) => pure ()
```

`syntax` 注册的是 `my_tac`，模式却写成 `mytac`。修复时让两处语法完全一致。连字符、下划线和空格都属于语法，不是排版建议。

## 失败 3：goal.assign 后仍看到旧目标
%%%
tag := "failure-stale-goals"
%%%

`goal.assign proof` 在 `MetavarContext` 中解决对应元变量，但 `return` 本身不删除 `Tactic.State.goals` 中的条目。tactic elaborator 返回后，框架会 prune 已经解决的目标。

因此，简单 tactic 在赋值后直接结束通常可行；如果同一 tactic 还要继续手工遍历和操作目标列表，就应明确调用获取／设置目标的 API，并考虑哪些目标已经解决。

## 失败 4：探查 isDefEq 时状态被修改
%%%
tag := "failure-is-def-eq-state"
%%%

`isDefEq` 可能给元变量赋值。只想测试而不保留赋值时，可以回滚可回溯状态：

\[示意\]
```
let equal ← withoutModifyingState (isDefEq lhs rhs)
```

`withoutModifyingState` 只能回滚该 monad 管理的可回溯状态，不能撤销打印、文件写入或其他 IO 效果。参见 §1.2.5 第 4 点。

## 失败 5：把 monadic 计算当成普通结果
%%%
tag := "failure-monadic-binding"
%%%

\[练习·故意错误\]
```
import Lean
open Lean Elab Tactic Meta

elab "bad_type" : tactic => do
  let goal := getMainGoal
  let goalType ← goal.getType
  logInfo m!"{← ppExpr goalType}"
```

第一行后 `goal : TacticM MVarId`，不是 `MVarId`。改成 `let goal ← getMainGoal`。

## 失败 6：少打开 Tactic 命名空间
%%%
tag := "failure-namespace"
%%%

下面代码导入了 Lean，也打开了 `Elab` 和 `Meta`，但 `getMainGoal` 仍不可见：

\[练习·故意错误\]
```
import Lean
open Lean Elab Meta

elab "missing_namespace" : tactic => do
  let goal ← getMainGoal
  logInfo m!"{goal.name}"
```

修复为 `open Lean Elab Tactic Meta`，或使用完全限定名。排错时先区分“名字不可见”和“函数参数不对”；两者都可能显示为红线，但发生阶段不同。


# 练习
%%%
tag := "chapter-exercises"
%%%

## 练习 1.1（热身）：运行 trace\_goal
%%%
tag := "exercise-1-1"
%%%

\[可运行\]
```
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

**验收标准**：文件编译成功；Infoview 日志包含当前目标 `n + 0 = n`；`simp` 后没有剩余目标。

## 练习 1.2（热身）：用 #check 验证层次
%%%
tag := "exercise-1-2"
%%%

不要只填写层名。把下面代码放进文件，让 Lean 显示每个函数的完整类型，再记录其返回 monad。

\[可运行\]
```leanFence
import Lean
open Lean Elab Term Tactic Meta

#check inferType
#check logInfo
#check getMainGoal
#check elabTerm
#check mkFreshExprMVar
```

回答：

1. 哪些函数返回 `MetaM`？
2. 哪个函数返回 `TacticM`？
3. 哪个函数返回 `TermElabM`？
4. 哪个函数属于“多态（要求 `MonadLog` 等实例，四层 monad 都可用）”？
5. 为什么 `inferType` 和 `logInfo` 能直接写在 `TacticM` 的 `do` block 中？

解释第五问时应写出：`TacticM` 以 `TermElabM` 为下层，后者再以 `MetaM`、`CoreM` 为下层；相应 `MonadLift`／typeclass 实例把内层操作提升到外层。

<details>
<summary>参考答案</summary>

`inferType → MetaM`，`mkFreshExprMVar → MetaM`，`getMainGoal → TacticM`，`elabTerm → TermElabM`，`logInfo → 多态 m Unit`。`logInfo` 在满足 `MonadLog`、`AddMessageContext`、`MonadOptions` 等相应 typeclass 的 monad 中都可用，因此不属于四层之一。

</details>

**验收标准**：文件编译成功；你保存了五条 `#check` 输出；答案同时包含函数所属层和 lifting 原因。

## 练习 1.3（debug）：命名空间与 proof term 构造
%%%
tag := "exercise-1-3"
%%%

下面有两处错误。

\[练习·故意错误\]
```
import Lean
open Lean Elab Meta

elab "close_rfl" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let_expr Eq _ lhs rhs := goalType |
    throwError "not an equality"
  if ← isDefEq lhs rhs then
    goal.assign (mkConst ``Eq.refl)
  else
    throwError "not reflexive"

example : (42 : Nat) = 42 := by
  close_rfl
```

**分级提示 1**：一处错误属于命名空间可见性；另一处属于 proof term 构造。

<details>
<summary>分级提示 2</summary>

打开 `Tactic` 命名空间。不要手工给 `Eq.refl` 拼 universe level 和隐式参数；使用 Meta API `mkEqRefl lhs`。

</details>

<details>
<summary>参考修复</summary>

\[可运行\]
```leanFence
import Lean
open Lean Elab Tactic Meta

elab "close_rfl" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let_expr Eq _ lhs rhs := goalType |
    throwError "not an equality"
  if ← isDefEq lhs rhs then
    goal.assign (← mkEqRefl lhs)
  else
    throwError "not reflexive"

example : (42 : Nat) = 42 := by
  close_rfl
```

</details>

**验收标准**：分两步排错：

1. 第一次编译：预期看到 `unknown identifier 'getMainGoal'` 一类错误。修 `open`，加入 `Tactic`。
2. 第二次编译：预期看到 `Eq.refl` 类型不匹配或参数数错。用 `mkEqRefl lhs` 修复。

最终 example 编译成功，且实现中使用 `mkEqRefl lhs`。

## 练习 1.4（debug）：:= 与 ←
%%%
tag := "exercise-1-4"
%%%

\[练习·故意错误\]
```
import Lean
open Lean Elab Tactic Meta

elab "bad_type" : tactic => do
  let goal ← getMainGoal
  let target := goal.getType     -- ← 这里错了什么？
  logInfo m!"{← ppExpr target}"
```

解释 `target` 的类型，以及为什么 `ppExpr target` 会类型错误。修复时只改一个符号。

**验收标准**：故意错误版本不能编译；你的解释明确写出 `target : MetaM Expr`；改为 `let target ← goal.getType` 后代码编译成功。

## 练习 1.5（综合）：实现 my\_rfl
%%%
tag := "exercise-1-5"
%%%

实现一个 `my_rfl` tactic：

- 目标不是等式时，错误信息包含当前目标；
- 两侧定义等价时，用 `mkEqRefl lhs` 关闭；
- 两侧不定义等价时，报告边界错误。

下面模板中的 `my_rfl` 尚未定义，所以标签是 `\[练习模板\]`。先在同一文件前面补实现。

\[练习模板\]
```
import Lean
open Lean Elab Tactic Meta

-- 在这里定义 my_rfl

example : (2 : Nat) + 3 = 5 := by
  my_rfl

example (n : Nat) : (0 : Nat) + n = n := by
  my_rfl
```

成功用例应正常编译。失败边界单独放在注释中，完成实现后取消注释观察：

\[练习模板\]
```
-- 取消注释后应失败：假设 h 能证明目标，但两侧 n 与 m 不定义等价。
-- example (n m : Nat) (h : n = m) : n = m := by
--   my_rfl
```

预期错误应由你的 tactic 报出，内容说明两侧不定义等价；它不应变成“unknown tactic”或命名空间错误。这个失败说明 tactic 的适用边界，不说明命题为假，因为 `exact h` 可以证明该命题。

**验收标准**：前两个 example 编译成功；取消注释第三个 example 后，编译在 `my_rfl` 处失败并显示你设计的边界错误；重新注释失败例后，文件无 `sorry`、无未解决目标。
