import VersoManual
import LeanTacticBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "examples"
set_option verso.exampleModule "Examples.Ch01MetaprogrammingModel"

#doc (Manual) "Lean 中的 tactic 基础设施" =>
%%%
file := "Ch01MetaprogrammingModel"
tag := "ch01-metaprogramming-model"
%%%

> *本章目标*：把上一章的抽象模型对应到 Lean 的实际实现，包括四层 monad、Reader/State/Except、目标列表、局部上下文、元变量上下文与 lifting，并说明抽象模型省略的实现细节及其技术后果。
>
> *版本基准*：Lean `leanprover/lean4:v4.32.2`，Mathlib revision `905b95818eb3`。本章的 API 签名和源码路径都按这个版本对齐。


# 从发明回到现实：一张对照表

%%%
tag := "tactic-metaprogram"
%%%

上一章把 tactic 抽象为带环境、状态与失败通道的证明状态变换。本章把这些成分对应到 Lean 的实际类型，并指出模型没有表示的实现细节。

先看对应关系：

| 上一章发明的零件 | Lean 现实中的对应物 |
| --- | --- |
| `Machine A` 那个 `Env → State → 结果` 的形状 | `CoreM`/`MetaM`/`TermElabM`/`TacticM` 四层 monad |
| 只读背景 `Env` | 各层的 `Context`（`ReaderT` 承载） |
| 可变状态 `State` | 各层的 `State`（`StateRefT` 承载） |
| 失败通道 `Error` | 最底层的 `Except`/`EIO Exception` |
| `pure` / `bind` | Lean 的 `pure` / `>>=`，以及 `do` 记法 |
| “每加一种能力就叠一层” | `ReaderT` / `StateT` / `ExceptT` transformer 栈 |
| 目标列表 `goals` | `Tactic.State.goals : List MVarId` |
| 局部假设 | `LocalContext`（住在 `Meta.Context`，只读） |
| 带洞证明里“同一个构造子的洞” | `MetavarContext` 里的元变量与赋值（住在 `Meta.State`，可写） |
| `assumption` 里那句含糊的“命题相同” | `isDefEq`：定义等价，且*有副作用* |
| “靠预期类型补全表面语法” | `TermElabM` 的精译（elaboration） |
| 值语义下通过保留旧状态实现回滚 | 可回溯状态的存档/恢复，以及 `TacticM` 在失败分支上的恢复策略 |

阅读 tactic 源码时，需要回答四个问题：

1. 这段代码运行在哪一层 monad 里？
2. 这一层能读到哪些上下文（对应玩具里的 `Env`）？
3. 这一层能改哪些状态（对应玩具里的 `State`）？
4. 想调下层操作、或者反过来在下层跑上层操作，各自需要怎么转换（对应玩具里“能力叠层”的方向性）？

下文依次考察 `CoreM`、`MetaM`、`TermElabM` 和 `TacticM`，并说明层间转换的方向。


# Monad：把返回值和计算效果放在一起
%%%
tag := "monad-effects"
%%%

## 上一章那个 `my_assumption`，现实需要什么

%%%
tag := "tactic-required-context"
%%%

真实的 `assumption` 需要在当前目标的局部上下文中寻找与目标定义等价的假设。为此，计算至少涉及以下信息和效果：

- 当前目标；
- 当前局部上下文，其中保存局部变量和假设（对应玩具里的 `Goal.hypotheses`）；
- 元变量状态，因为定义等价检查可能给元变量赋值（对应玩具里证明骨架的洞）；
- 全局环境，名字、常量和类型检查都依赖已声明的内容；
- 选项和消息系统；
- 一条报告“没有匹配假设”的失败通道（对应玩具里的 `Error`）。

先用摊平的普通函数签名表示这些依赖，再与 Lean 的 monadic 接口比较。以下三个名字只是概念占位符：

\[伪代码\]
```
Goal   = 当前待证目标的概念占位符
Proof  = 构造出的证明的概念占位符
Error  = 失败信息的概念占位符
```

此处的 `Goal`、`Proof`、`Error` *不是* Lean 已定义的类型，只用于描述接口。

类型 `Goal → Proof` 只表示“给定目标，直接得到证明”，无法容纳环境依赖、状态更新和失败。若用普通函数显式传递这些信息，签名会写成下面的摊平形式：

\[伪代码\]
```
runTactic : Environment → LocalContext → MetaState → Goal
          → Error ⊕ (Proof × MetaState)
```

按参数顺序读：先给全局环境，再给局部上下文、旧元变量状态和目标；失败时返回 `Error`，成功时返回证明与新状态。真实 Lean 的结构更细。普通函数当然可以表达这些依赖；问题是每个辅助函数都必须重复传递并重组环境、状态与错误结果，组合成本很高。

Monad 给的是*统一接口*：把"结果类型"和"这段计算需要的效果"打包进同一个类型构造器里。看到 `TacticM α`，先这么读：

> 一段在 tactic 环境里跑的计算；成功结束时会得到一个 `α`。

举几个例子：

\[示意\]
```leanBug
getMainGoal : TacticM MVarId
getMainTarget : TacticM Expr
setGoals : List MVarId → TacticM Unit
```

第一行：跑一下能拿到主目标的 `MVarId`。第二行：跑一下能拿到主目标类型的 `Expr`。第三行：更新目标列表，没什么好返回的，就是 `Unit`。

## pure、bind，兑现你上一章造的那两个操作

%%%
tag := "pure-bind-state-passing"
%%%

这一节把 `pure` 和 `bind` 对应到 Lean 的真实签名，并用可运行示例展开 `bind` 所传递的状态。

本章所称“副作用”是广义的*计算效果（effect）*，包括失败、读取环境、读写状态与 IO。它不特指修改全局变量，也不表示代码不可推理。

Lean 中的 monad 主要提供两个操作：

\[示意\]
```leanBug
pure : α → M α
(>>=) : M α → (α → M β) → M β
```

`pure a` 把普通值 `a` 装进 `M` 计算里，不带额外的效果（就是你的“把值塞进机器”）。`ma >>= f` 先跑 `ma` 拿到 `a`，再把 `a` 喂给 `f` 跑下一步（就是你的“接起来”）。Lean 的 `do` 语法就是这条流水线的糖衣。

monad laws 在 Lean 中写成：

- 左单位律：`pure a >>= f = f a`
- 右单位律：`m >>= pure = m`
- 结合律：`(m >>= f) >>= g = m >>= (fun a => f a >>= g)`

这些定律保证插入或消去无效果的 `pure`，以及重新结合一串 `bind`，不会改变计算含义。因此，把若干 tactic 步骤抽成辅助函数或重组 `do` 块时，可以据此保持行为不变。

在 `do` 的尾位置，`return a` 等价于当前 monad 的 `pure a`。在 `for`、`if` 或 `match` 的非尾分支中，`return a` 会提前结束整个 `do` 块；返回值仍由当前 monad 的 `pure` 包装。

要看清 `bind` 到底传了什么，State monad 是最好的例子。先用一个简化版：

> *下面四个 `\[可运行\]` 代码块按顺序放在同一个 `.lean` 文件里*：`CounterM`、`tick`、`twoTicks`、`twoTicksExpanded`、`twoTicksDo` 是同一段代码的连续片段，后块依赖前块。分别复制会报 `unknown identifier`。

\[可运行\]
```leanFence
abbrev CounterM (α : Type) := StateM Nat α


def tick : CounterM Nat := fun oldState =>
  (oldState, oldState + 1)
```

`tick` 拿到旧状态 `oldState`，返回一对：结果是 `oldState`，新状态是 `oldState + 1`。连续跑两次 `tick`：

\[可运行\]
```leanFence
def twoTicks : CounterM (Nat × Nat) :=
  tick >>= fun first =>
  tick >>= fun second =>
  pure (first, second)

#eval twoTicks.run 10
```

输出是 `((10, 11), 12)`：结果是 `(10, 11)`，最终状态是 `12`。下面把同一过程手动展开，不用 `>>=`：

\[可运行\]
```leanFence
def twoTicksExpanded : CounterM (Nat × Nat) := fun oldState =>
  let (first, stateAfterFirst) := tick oldState
  let (second, stateAfterSecond) := tick stateAfterFirst
  let result := (first, second)
  (result, stateAfterSecond)

#eval twoTicksExpanded.run 10
```

逐行看状态怎么流动：

1. `oldState` 是整段计算收到的初始状态 `10`。
2. 第一次 `tick oldState`：结果 `10`，新状态 `stateAfterFirst = 11`。
3. 第二次调用*没用* `oldState`，用的是 `stateAfterFirst`，所以结果 `11`、新状态 `stateAfterSecond = 12`。
4. 结果组合成 `(10, 11)`。
5. 整段计算把结果和最后状态一起返回。

`bind` 的核心工作就是：*把上一步产生的新状态，交给下一步*。`do` 语法把这条管线藏起来了，但没删掉：

\[可运行\]
```leanFence
def twoTicksDo : CounterM (Nat × Nat) := do
  let first ← tick
  let second ← tick
  return (first, second)
```

`do` 记法隐藏了上述状态传递；`let goal ← getMainGoal` 运行右侧的 monadic 计算，并把普通结果绑定到 `goal`。

## Reader、State、Except：你发明的三种效果，各有一个 transformer
%%%
tag := "reader-state-except"
%%%

Lean 分别用 `ReaderT`、`StateT` 和 `ExceptT` 表示只读背景、可变状态与失败通道。

### Reader：读一份固定的上下文（你的“只读背景 Env”）
%%%
tag := "reader-context"
%%%

`ReaderT ρ m α` 表示一段可读取上下文 `ρ`，并在下层 monad `m` 中返回 `α` 的计算。Reader 接口不提供写回新上下文的操作。

在 `CoreM` 中，`Options`、当前文件名和当前命名空间等信息位于 `Core.Context`。下面读取一个选项：

\[可运行\]
```leanFence
import Lean
open Lean

abbrev OptionsReader (α : Type) := ReaderM Options α


def readTraceFlag : OptionsReader Bool := do
  let options ← read
  return options.getBool `trace.Meta.Tactic.simp.rewrite false
```

`read` 取得当前 `Options`。若子计算需要临时更换上下文，可以使用 `withReader` 一类的局部替换操作；子计算结束后恢复原上下文。Reader 仍不提供持久写入。

在 `MetaM` 中，`withLCtx` 承担相近但更具体的工作：它在给定的 `LocalContext` 与局部实例下运行一段 Meta 计算，结束后恢复外层上下文。`withReader` 说明 Reader 的一般作用域语义，`withLCtx` 则是局部上下文这一实际数据的专用入口。

全局 `Environment` 不能作为 Reader 的例子，因为它位于 `Core.State`，Core 计算可以更新它。

### State：能读也能改
%%%
tag := "state-updates"
%%%

`StateM σ α` 可以看成函数 `σ → α × σ`：输入旧状态，输出普通结果和新状态。`StateT σ m α` 就是把这个结构叠在下层 monad `m` 上。

\[可运行\]
```leanFence
abbrev NatState (α : Type) := StateM Nat α


def bumpTwice : NatState Nat := do
  modify (· + 1)
  modify (· + 1)
  get

#eval bumpTwice.run 40
```

输出 `(42, 42)`：返回值 `42`，最终状态也是 `42`。

Lean 元编程常用 `StateRefT`。它的接口接近纯 `StateT`，底层却基于 `ST.Ref`：`get` 读取可变引用，`set` 原地更新，而不复制整份状态。`Meta.State` 中的 `MetavarContext` 和 `Tactic.State` 中的目标列表更新频繁，因此采用这条路径。

原地更新也改变了回滚成本。`StateRefT` 的通用异常实例不会自动把引用恢复到旧值；Lean 另行提供可回溯状态的存档和恢复机制。`withoutModifyingState` 在子计算结束后无条件丢弃其中的可回溯修改，适合只探查而不提交。其他尝试或异常组合器可以在成功时提交、失败时恢复，`TacticM` 的尝试分支也采用先存档、失败后恢复的策略。恢复范围只包括被指定为可回溯的状态，不包括 IO 等外部效果。回滚是额外的事务策略，不由 monad 或 `StateRefT` 自动提供。

### Except：要么成功要么失败
%%%
tag := "except-failure"
%%%

`Except ε α` 是一个基础计算结果：要么 `.ok a`，要么 `.error e`。`ExceptT ε m α` 是把这种失败能力叠到下层 monad `m` 上。

下面用 `String.toInt?` 解析整数字符串。返回类型使用 `Int`，因此示例能够接受负数字面量：

\[可运行\]
```leanFence

def parseInt (input : String) : Except String Int := do
  match input.toInt? with
  | some value => return value
  | none => throw s!"not an integer: {input}"

#eval parseInt "-12"
#eval parseInt "twelve"
```

在 tactic 里，"目标不是等式"、"没有主目标"、"没找到匹配假设"都可以通过异常通道报告。异常传播的意思是：某一步 `throw` 之后，后面的 `do` 步骤自动跳过，错误沿调用链冒泡。

## 把能力叠成 monad transformer 栈
%%%
tag := "monad-transformer-stack"
%%%

真实 tactic 同时需要读上下文、写状态、能失败。这几种能力可以逐层叠：

\[可运行\]
```leanFence
abbrev MyM (α : Type) :=
  ReaderT String (StateT Nat (Except String)) α
```

从外往内读：

1. `ReaderT String ...` 加一层只读 `String` 上下文；
2. `StateT Nat ...` 加一层可写 `Nat` 状态；
3. 最内层 `Except String` 提供失败通道；
4. `α` 是成功时的普通返回值。

最内层写 `Except String`，而不是 `ExceptT String m`，因为这里已经到基础 monad，没有下层 `m`。若要在 IO 上增加异常层，则使用 `ExceptT String IO α`。

`ReaderT`、`StateT`、`ExceptT` 名字末尾的 `T` 就是 transformer 的意思：它接收一个已有 monad，在外面再包一种计算结构。

transformer 的叠加描述计算结构：每层 `XxxT` 增加一种能力。外层能否直接使用 `read`、`get`、`throw` 等统一接口，还取决于相应的 lifting 和 typeclass 实例；仅仅堆叠类型并不能自动打通所有操作。

## 为什么 Lean 用 monad 组织这些能力
%%%
tag := "why-lean-uses-monads"
%%%

不用 monad 也可以显式传递环境、状态和错误结果，如本节开头的摊平签名所示。Lean 使用 monad 是工程选择，主要理由如下：

1. *签名只暴露能力层*：`getMainGoal : TacticM MVarId` 告诉你它跑在 `TacticM` 里，不用展开几十个环境、状态、异常、IO 参数。
2. *状态按顺序传递*：`bind` 帮你把前一步的新状态交给后一步，`do` 管理这条管线。
3. *异常自动传播*：中间某步失败，后面的自动跳过，错误一路冒泡到调用者。
4. *局部控制可回溯状态*：`withoutModifyingState` 无论成功失败都丢弃子计算的可回溯修改；其他提交或异常组合器可以采用成功提交、失败恢复的策略。
5. *层之间可 lifting*：只要实例存在，外层 monad 直接调下层操作，你不用手写每一层的封装。

第 4 点只涉及可回溯状态。它不保证恢复所有内部缓存，也不会撤销终端输出、文件写入或网络请求。

异常通道本身不可靠地区分两类失败。“没有匹配假设”“目标不是等式”通常是搜索中的预期失败，可以触发 `orElse`；类型不正确的环境更新或内核拒绝则是严重错误，不应被选择组合器吞掉。一个异常是否可回溯取决于调用位置和捕获它的组合器，因此捕获范围应限制在预期失败的最小区域。

## 读 do 代码的四条实用规则
%%%
tag := "reading-do-notation"
%%%

1. `M α` = "一段在 `M` 里跑、成功后得 `α` 的计算"。`MetaM Expr` *不是*一个 `Expr`，是一段会给你 `Expr` 的 Meta 计算。
2. `let x := e` 不运行 monadic 计算，只把右侧表达式本身绑给 `x`。写 `let x := getMainGoal` 之后，`x : TacticM MVarId`，不是 `MVarId`。
3. `let x ← e` 运行 `e`，把普通结果绑给 `x`。写 `let x ← getMainGoal` 之后，`x : MVarId`。
4. 尾位置的 `return a` = 当前 monad 的 `pure a`；非尾位置的 `return a` 提前跳出整个 `do` block，结果是 `pure a`。

再加一条执行规则：`do` 从上到下组合步骤；某一步 `throw`，后面的步骤不再运行。

规则 2 和规则 3 的区别是初学最高频错误之一。有没有那个 `←`，`x` 的类型差一整层。


# 四层 monad 栈
%%%
tag := "four-monad-layers"
%%%

Lean 的元编程接口分为四层。每层在前一层外加入 `ReaderT` 与 `StateRefT`，分别增加只读上下文和可变状态。查看真实定义前，先说明三种语法：

- `abbrev A := B` 声明一个"可展开的类型别名"；给复杂类型起个短名字，展开时和原类型完全一样。
- `f <| x` 和 `f x` 等价；`<|` 是低优先级右结合的应用运算符，常用来省括号。
- `f $ x` 也是低优先级应用。Lean 源码两种写法都会出现，本章我在展开时统一写括号。

四层各自定义了名为 `Context` 和 `State` 的结构。`Core.Context`、`Meta.Context`、`TermElab.Context`、`Tactic.Context` 是不同类型，四个 `State` 也一样。源码打开命名空间后常省略前缀，阅读时应根据命名空间还原完整名称。

\[源码节选\]
```leanBug
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

这是我按本章讲解补全命名空间后的等价写法；源码里打开命名空间之后一般写成短的 `Context`、`State`。

把括号全展开，长这样：

\[示意\]
```leanBug
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

在相应 lifting 实例存在时，外层可以调用内层操作。例如，`TacticM` 可以调用 `MetaM` 的 `inferType`。反向运行则必须显式提供上层新增的上下文和状态；`MetaM` 本身没有 `Tactic.Context` 或 `Tactic.State`，因而不能直接运行 `TacticM`。

## CoreM：环境、选项、消息
%%%
tag := "corem-environment"
%%%

`CoreM` 是元编程的公共底座。下面只列跟本章相关的字段；真实源码里字段更多。

\[源码节选\]
```leanBug
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

`Environment` 位于 `Core.State`，属于可写状态，Core 计算可以更新它，例如添加声明。`Options`、`fileName`、`currNamespace` 位于 `Core.Context`，通过 Reader 读取。

`CoreM` 可以查询声明、读取选项、生成名字和记录消息。类型推断、定义等价检查与元变量创建属于上层 `MetaM`。

## MetaM：局部上下文、元变量、类型检查
%%%
tag := "metam-metavariables"
%%%

`MetaM` 在 `CoreM` 外增加 `Meta.Context` 和 `Meta.State`。需要区分两类位置和可变性不同的数据：

- `LocalContext`：当前 Meta 计算从 `Meta.Context.lctx` 读取它；在单次计算中属于只读背景。进入 telescope 或局部绑定时，子计算在扩展后的上下文中运行。它对应玩具模型中的 `Goal.hypotheses`，但不同目标并不共用同一份 `LocalContext`。
- `MetavarContext`：位于 `Meta.State`，可以更新。创建或赋值元变量、定义等价检查求解约束时都会修改它。它承载玩具模型中证明骨架里的洞。

`constructor` 产生的两个子目标各对应一个元变量，例如同一个 `And.intro` 证明项中的两个洞。它们的 id 不同，却通过共享的 `MetavarContext` 和约束关联；求解一个元变量可能同时确定另一个。玩具模型保留了洞的身份，但没有表示这种跨目标依赖。

`LocalContext` 出现在两个相关层次：

- 当前 Meta 计算从 `Meta.Context.lctx` 读取此刻使用的局部上下文；
- 每个目标的 `MetavarDecl` 保存该目标自己的 `lctx` 和局部实例，因为不同目标可使用的假设不同；
- `MVarId.withContext` 将目标保存的 `lctx` 装入 `Meta.Context`，使子计算在该目标的上下文中运行。

因此，“局部假设是只读背景”应理解为：每个目标保存自己的只读上下文，进入目标时临时安装该上下文，而不是所有目标共享一份全局 `LocalContext`。`forallTelescope` 进入 `∀ x, ...` 的主体时也会在扩展后的上下文中运行回调；回调结束后，外层上下文恢复原状。

`MetavarContext` 记录元变量的声明和赋值。`mkFreshExprMVar` 创建元变量；`isDefEq` 可能给现有元变量赋值，因此不是纯判断。定义等价检查会设置检查点，返回 `false` 或抛出异常时恢复相关状态，成功时才提交求解所得的赋值。这个事务边界避免多个候选之间相互污染。

Meta 常用操作：

\[示意\]
```leanBug
inferType e
isDefEq e₁ e₂
whnf e
mkFreshExprMVar type
forallTelescope type callback
lambdaTelescope expr callback
```

它们完整的类型签名（带上参数和隐式参数）会长得很长。学 API 时用 `#check` 看完整签名，别只记表里的短写。

`isDefEq e₁ e₂` 判断定义等价，而不是字符相等；例如 `Nat` 与 `ℕ`、`n + 0` 与 `n` 可被判为等价。成功检查可能给元变量赋值并修改 `MetavarContext`，失败检查则撤回试探性修改。因此，`isDefEq` 是一次带检查点的约束求解操作，不是无状态的布尔比较。

## TermElabM：由预期类型驱动的精译
%%%
tag := "termelabm-elaboration"
%%%

parser 先把文本转换为 `Syntax`。`TermElabM` 再结合环境、局部上下文与*预期类型*，把 term syntax 精译为 `Expr`，期间执行名字解析、重载消解、隐式参数插入、typeclass 综合和约束求解。上一章的模型直接使用证明对象，没有表示这一阶段。

看一下"预期类型"的意思：同一段语法 `3`，在 `Nat` 预期下和 `Real` 预期下会被精译成不同表达式。下面在命令精译里分别要求这两种：

\[可运行\]
```leanFence
import Mathlib
open Lean Elab Term Meta

elab "show_elab_examples" : command => do
  Command.liftTermElabM do
    let natExpr ← Lean.Elab.Term.elabTerm (← `(3)) (some (mkConst ``Nat))
    let realType ← Lean.Elab.Term.elabTerm (← `(Real)) none
    let realExpr ← Lean.Elab.Term.elabTerm (← `(3)) (some realType)
    logInfo m!"Nat expression: {← ppExpr natExpr}"
    logInfo m!"Real expression: {← ppExpr realExpr}"

show_elab_examples
```

第一处预期类型是 `Nat`，数字字面量被精译为自然数表达式。第二处预期类型是 `Real`，精译器选择适用于 `Real` 的数字字面量机制并插入隐式信息。两者表面上都打印成 `3`，内部结构不同，可以用 `inferType` 核对。

隐式参数插入也依赖预期类型。看这个多态例子：

\[可运行\]
```leanFence
import Mathlib

#check @id
#check (id 3 : Nat)
#check (id 3 : Real)
```

`id` 的类型参数没有出现在表面语法中。精译 `id 3` 时，Lean 根据实参和预期类型求出省略的类型参数，因此 Nat 版与 Real 版得到不同的实例化结果。

## TacticM：目标列表管理
%%%
tag := "tacticm-goals"
%%%

`TacticM` 在 `TermElabM` 外增加 tactic 自己的上下文和状态。核心状态包含待处理目标列表，对应玩具模型中的 `State.goals`：

\[源码节选\]
```leanBug
-- Lean/Elab/Term/TermElabM.lean；省略 Tactic.State 的其他细节
structure Tactic.State where
  goals : List MVarId

-- Lean/Elab/Tactic/Basic.lean
abbrev Tactic := Syntax → TacticM Unit
```

`goals : List MVarId` 是元变量标识组成的工作队列。它可能暂时包含已经赋值的元变量；`pruneSolvedGoals` 或 `getUnsolvedGoals` 才会过滤出尚未解决的目标。因此，工作队列与未填洞集合通常同步，却不保证每个时刻字面相等。

常用目标操作：

\[示意\]
```leanBug
getGoals : TacticM (List MVarId)
setGoals : List MVarId → TacticM Unit
getMainGoal : TacticM MVarId
getMainTarget : TacticM Expr
```

一个 tactic 读写目标工作队列，并在共享的元变量状态中推进证明。成功返回不保证未解决目标减少：`constructor` 增加目标，`skip` 保持不变，`swap` 只重排。只有 tactic block 结束后，清理所得的未解决目标为空，证明才完整；中间阶段的 raw `goals` 仍可能含有已赋值项。

因此，tactic 不是把目标列表映射到更短列表的函数，而是在共享元变量状态上合法推进证明。目标列表可以增长、缩短或重排。

`goals` 和 `MetavarContext` 都经可变状态层更新，因此 `orElse`（Lean 中 `<|>` 一类组合器）不能依赖 `StateRefT` 自动撤销。`TacticM` 的尝试或异常路径会先保存可回溯状态，并在分支失败时恢复；`withoutModifyingState` 则连成功分支的可回溯修改也丢弃，用于只观察而不提交的探查。

# 现在你能读什么源码，还缺什么

%%%
tag := "what-you-can-read-now"
%%%

本章已经把抽象模型对应到四层 monad、上下文与状态、元变量、定义等价检查、目标工作队列和显式回滚机制。

基于这些接口，可以读懂最小 tactic 的控制流程：`getMainGoal` 取得主目标的 `MVarId`，`getType` 读取待证命题，`inferType` 与 `isDefEq` 在 `MetaM` 中完成检查，最后更新证明状态。更新状态时必须区分填入证明洞与修改工作队列：

- `MVarId.assign` 把表达式写入元变量上下文。它不做类型检查或 occurs check，也不检查元变量是否已经赋值；再次调用还可能覆盖旧值。调用方必须先保证证明表达式类型正确、无循环且目标尚未赋值，再执行赋值，最终仍由后续类型检查与内核把关。玩具模型中的“填洞”对应先检查再赋值的完整过程，而不是一次裸写操作。
- `setGoals`（以及 `replaceMainGoal` 等）只更新 tactic 的工作队列，也就是接下来处理哪些目标，本身不构造证明。即使 `setGoals []` 清空队列，只要对应元变量尚未赋值，证明仍不完整，最终会因未解决目标或元变量未赋值而被拒。
- `pruneSolvedGoals`/`getUnsolvedGoals` 能做的，是从*当前工作队列*里过滤掉已经被赋值的目标；它们不会遍历整张证明、也找不回曾被 `setGoals` 错误删掉但仍未赋值的洞。因此工作队列本身也必须维护正确：过滤操作负责清走“已经解决但还留在队列里的项”，不能修复“未解决项被提前丢出队列”的 bug。

检查并赋值负责填入证明洞；`setGoals` 只维护工作队列。二者缺一不可，也不能互相替代。

本章把 `getMainTarget` 返回的目标类型视为不透明的 `Expr`。并非每个 tactic 都需要检查其内部结构：`assumption` 通常遍历局部声明，并用 `isDefEq` 比较声明类型与目标类型；`intro`、`constructor` 等操作则需要识别目标的外层形式。到这里，上一章的 `my_assumption` 伪代码已经可以按这些接口翻成 Lean。

下一章介绍 `Expr` 的构造子、模式匹配与构造方法，为需要显式检视或构造表达式的 tactic 提供基础。
