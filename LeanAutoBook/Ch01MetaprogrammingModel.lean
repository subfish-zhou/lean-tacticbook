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

> *本章目标*：理解 Lean 4 元编程的四层 monad，能读懂最小 tactic 实现，弄清一段操作"为什么能在这一层跑"、"为什么不能反着跑"。
>
> *版本基准*：Lean `leanprover/lean4:v4.30.0-rc1`，Mathlib revision `0692ef80fb13`。本章的 API 签名和源码路径都按这个版本对齐。


# tactic 是一段操作证明状态的元程序
%%%
tag := "tactic-metaprogram"
%%%

你写 `simp`、`constructor` 或 `linarith` 的时候，Lean 不只是"调了一个数学定理"。它跑了一段元程序：这段程序读当前目标、看局部假设、构造或检查表达式、更新待证目标列表，需要的时候还得报告失败。

看懂 tactic 源码，你要能回答四个问题：

1. 这段代码运行在哪一层 monad 里？
2. 这一层能读到哪些上下文？
3. 这一层能改哪些状态？
4. 想调下层操作、或者反过来在下层跑上层操作，各自需要怎么转换？

Lean 把这些能力分成 `CoreM`、`MetaM`、`TermElabM`、`TacticM` 四层。先别看定义式——我们从"一个 tactic 实际需要什么"开始，反过来推为什么要分成这四层。


# Monad：把返回值和计算效果放在一起
%%%
tag := "monad-effects"
%%%

## 一个 tactic 要带着哪些东西
%%%
tag := "tactic-required-context"
%%%

假设你要实现一个非常简单的 tactic `my_assumption`：扫一遍局部假设，找一个类型跟当前目标定义等价的假设，用它关掉目标。就这么点事，它得能拿到：

- 当前目标；
- 当前局部上下文——里面装着局部变量和假设；
- 元变量状态——因为定义等价检查可能会给元变量赋值；
- 全局环境——名字、常量、类型检查都要看已声明的内容；
- 选项和消息系统；
- 一条失败通道——用来说"没找到合适的假设"。

为了先看清接口形状，我用三个概念占位符：

\[伪代码\]
```
Goal   = 当前待证目标的概念占位符
Proof  = 构造出的证明的概念占位符
Error  = 失败信息的概念占位符
```

强调一下：`Goal`、`Proof`、`Error` *不是* Lean 已经定义好的类型，别去搜。它们只是帮我们讨论接口的名字。

现在看类型 `Goal → Proof`——它太窄了：这个签名只说"给一个目标，直接得到一个证明"，装不下环境依赖、状态更新和失败。你当然还可以坚持"就用普通函数"，把这些都显式塞进参数和返回值，签名会长成这样：

\[伪代码\]
```
runTactic : Environment → LocalContext → MetaState → Goal
          → Error ⊕ (Proof × MetaState)
```

按参数顺序读：先给全局环境，再给局部上下文和旧的元变量状态，再给目标；失败时返回 `Error`，成功时返回证明加新状态。真实 Lean 的结构比这更细，参数也不止这几个。问题不在于"普通函数做不到"——理论上做得到。问题是每个辅助函数都得这么写，组合起来就是不停地拆包、传参、装包、传参……写十行代码你就想反悔。

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

## pure、bind、以及"状态到底传了什么"
%%%
tag := "pure-bind-state-passing"
%%%

我这里说的"副作用"是*广义*的*计算效果（effect）*：失败、读环境、读写状态、IO 都算。它不特指"改全局变量"，也不是说代码"不纯净"。函数式圈子对"effect"这个词的态度和 Java 圈子对"副作用"的态度不太一样，先把口径统一。

一个 monad 主要提供两个操作：

\[示意\]
```leanBug
pure : α → M α
(>>=) : M α → (α → M β) → M β
```

`pure a` 把普通值 `a` 装进 `M` 计算里，不带额外的效果。`ma >>= f` 先跑 `ma` 拿到 `a`，再把 `a` 喂给 `f` 跑下一步。Lean 的 `do` 语法就是这条流水线的糖衣。

`pure` 和 `bind` 还得满足三条 *monad laws*：左单位律、右单位律、结合律。

- 左单位律：`pure a >>= f = f a`
- 右单位律：`m >>= pure = m`
- 结合律：`(m >>= f) >>= g = m >>= (fun a => f a >>= g)`

它们保证不同的 `do` 括号写法组合出来行为一致。本书不用它们证明什么，但你可以把它们记成"bind 的组合是可预测的"这条承诺。

关于 `return`：`do` 里尾位置的 `return a` *精确地*就是当前 monad 的 `pure a`——最后一行也可以直接写 `pure a`，等价。但 `return a` 出现在非尾位置（`for`、`if`、`match` 的分支里）时，它是 `do` 语法的*提前返回*：跳出整个 `do` block，结果是 `pure a`。这个控制流跟命令式语言的 `return` 类似，但返回值仍然在当前 monad 里。你会在后面的 `my_assumption` 里看到非尾位置的 `return`，那时就是这个意思。

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

以后看到 `let goal ← getMainGoal`，就用这个读法：跑右边那段计算，让 monad 自动传递上下文和状态，把普通结果绑到左边的名字。

## Reader、State、Except
%%%
tag := "reader-state-except"
%%%

### Reader：读一份固定的上下文
%%%
tag := "reader-context"
%%%

`ReaderT ρ m α` 表示：一段运行时能读上下文 `ρ`、最终在下层 monad `m` 里拿到 `α` 的计算。它*不会*通过 Reader 接口去改这份上下文——Reader 的语义就是"只读"。

在 `CoreM` 里，`Options`、当前文件名、当前命名空间等信息放在 `Core.Context`——这些是 Reader 能力的典型例子。举个独立的小例子，读一个选项：

\[可运行\]
```leanFence
import Lean
open Lean

abbrev OptionsReader (α : Type) := ReaderM Options α


def readTraceFlag : OptionsReader Bool := do
  let options ← read
  return options.getBool `trace.Meta.Tactic.simp.rewrite false
```

`read` 拿到当前 `Options`。这段计算只读它。想在一小段子计算里临时换一份上下文，用 `withReader` 一类的局部替换操作——它在子计算里临时换只读上下文，函数体一出来就恢复原样，不要把 Reader 当可写状态用。

*注意*：全局 `Environment` *不能*当 Reader 例子，因为它实际住在 `Core.State` 里——Core 计算是可以更新环境的。这是初学者最容易记错的一点，先把它钉住。

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

Lean 元编程里常见的是 `StateRefT`——它的接口跟纯 `StateT` 类似，底层却基于 `ST.Ref`（可变引用；`get` 读、`set` 写，原地更新那个保存值，不复制整份状态）。`Meta.State` 里的 `MetavarContext` 和 `Tactic.State` 里的目标列表都要频繁更新，复制大状态会拖累性能，所以走 `ST.Ref` 路径。

### Except：要么成功要么失败
%%%
tag := "except-failure"
%%%

`Except ε α` 是一个基础计算结果：要么 `.ok a`，要么 `.error e`。`ExceptT ε m α` 是把这种失败能力叠到下层 monad `m` 上。

下面这段解析整数字符串。失败分支和返回类型对得上——不会出现"先读 `Nat` 再检查它是不是负数"这种不可能条件：

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

注意最内层写的是 `Except String`，*不是* `ExceptT String m`——因为已经到基础 monad 了，没有再往下的 `m` 需要保留。如果还想在 IO 上再加异常层，就写成 `ExceptT String IO α` 那种形状。

`ReaderT`、`StateT`、`ExceptT` 名字末尾的 `T` 就是 transformer 的意思：它接收一个已有 monad，在外面再包一种计算结构。

一句话心智模型：*tactic 的运行环境 = 一堆效果能力的叠层，每加一层 `XxxT` 就多一种能力*。

不过要加个小括号——"每加一层就多一种能力"有个前提：相应的 lifting 和 typeclass 实例得存在。乱堆一通不保证外层能直接用 `read`、`get`、`throw` 这套统一接口，Lean 只是*在实例存在时*帮你打通。

## 为什么 Lean 用 monad 组织这些能力
%%%
tag := "why-lean-uses-monads"
%%%

不用 monad 也能显式传参数和状态——就像本节开头那个 20 参数的签名。Lean 用 monad 不是逻辑必然，是工程选择。理由是这几条：

1. *签名只暴露能力层*：`getMainGoal : TacticM MVarId` 告诉你它跑在 `TacticM` 里，不用展开几十个环境、状态、异常、IO 参数。
2. *状态按顺序传递*：`bind` 帮你把前一步的新状态交给后一步，`do` 管理这条管线。
3. *异常自动传播*：中间某步失败，后面的自动跳过，错误一路冒泡到调用者。
4. *局部控制可回溯状态*：`withoutModifyingState` 能跑一次探查然后丢掉这段的状态修改；`withLCtx` 能在临时局部上下文里跑一段 Meta 计算。
5. *层之间可 lifting*：只要实例存在，外层 monad 直接调下层操作，你不用手写每一层的封装。

第 4 点有边界：*回滚 monad 状态不等于回滚世界*。已经打印到终端的字符、写到文件的内容、走出去的网络请求，都不会因为你恢复了状态而消失。打印出去的话比元变量更难收回来——这一点跟日常经验完全对得上。

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

来看真实定义。先把三个可能拦路的语法讲一下：

- `abbrev A := B` 声明一个"可展开的类型别名"；给复杂类型起个短名字，展开时和原类型完全一样。
- `f <| x` 和 `f x` 等价；`<|` 是低优先级右结合的应用运算符，常用来省括号。
- `f $ x` 也是低优先级应用。Lean 源码两种写法都会出现，本章我在展开时统一写括号。

四层里每一层都有自己叫 `Context` 和 `State` 的类型，但*它们是不同命名空间下的四个不同结构*：`Core.Context`、`Meta.Context`、`TermElab.Context`、`Tactic.Context` 不是同一个类型；四个 `State` 同理。你在源码里看到只写 `Context`、`State`，那是打开命名空间后省了前缀。第一次读很容易看成"一家四胞胎"，其实是一家四个不同的孩子。

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

方向的事说清楚：外层 monad 在有 lifting 实例时可以直接调内层操作，例如 `TacticM` 里可以直接调 `MetaM` 的 `inferType`。反过来不行——`MetaM` 没有 `TermElab.Context`、`TermElab.State`、`Tactic.Context`、`Tactic.State`，凭空跑不了 `TacticM`；想反过来跑，你得显式把缺的上下文和状态补上。

我不用"内核态/用户态"那种类比——它容易让人搞反方向。请就按"外层能力更多、能包容内层；内层不带外层的信息、不能凭空反跑"来记。

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

划重点：`Environment` 在 `Core.State` 里——*是可写状态*，Core 计算可以更新环境（比如添加声明）。`Options`、`fileName`、`currNamespace` 在 `Core.Context` 里，走 Reader。别记反。

`CoreM` 能干什么：查声明、读选项、生成新名字、记录消息。类型推断、定义等价检查、创建元变量都不在这一层——那些活儿归上面的 `MetaM`。

## MetaM：局部上下文、元变量、类型检查
%%%
tag := "metam-metavariables"
%%%

`MetaM` 在 `CoreM` 外再叠一层 `Meta.Context` 和 `Meta.State`。有两个特别容易混的数据，位置不一样：

- `LocalContext`：*在哪* `Meta.Context`；*性质* Reader，单次计算里只读；*典型变化* 进 telescope 或局部绑定时，在扩展后的上下文里跑子计算
- `MetavarContext`：*在哪* `Meta.State`；*性质* State，可更新；*典型变化* 创建元变量、赋值元变量、定义等价检查求解约束时都会变

`LocalContext` 记录当前的局部声明。进 `∀ x, ...` 的 body 时，`forallTelescope` 会在扩展后的局部上下文里跑你给的回调；回调跑完，外层看到的还是原来那份上下文。这就是"进函数体临时借一份，出来还回去"的意思。

`MetavarContext` 记录元变量的声明和赋值。`mkFreshExprMVar` 会加新元变量；`isDefEq` *可能*给现有元变量赋值——所以它不是纯粹的判断，是有副作用的。后面 §常见失败模式会专门讲这一条。

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

## TermElabM：由预期类型驱动的精译
%%%
tag := "termelabm-elaboration"
%%%

parser 先把文本变成 `Syntax`；`TermElabM` 再结合环境、局部上下文、*预期类型*把 term syntax 精译成 `Expr`。这一层负责名字解析、重载消解、隐式参数插入、typeclass 综合、约束求解——一整套。

看一下"预期类型"的意思：同一段语法 `3`，在 `Nat` 预期下和 `Real` 预期下会被精译成不同表达式。下面在命令精译里分别要求这两种：

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

第一处预期类型是 `Nat`，数字字面量直接被精译成自然数表达式。第二处预期类型是 `Real`，精译器要挑对适用于 `Real` 的数字字面量机制、插入相关隐式信息。表面上都打印成 `3`，内部结构不一样——用 `inferType` 可以进一步核对。

隐式参数插入也依赖预期类型。看这个多态例子：

\[可运行\]
```leanFence
import Mathlib

#check @id
#check (id 3 : Nat)
#check (id 3 : Real)
```

`id` 的类型参数没写在表面语法里。精译 `id 3` 时，Lean 根据参数和预期类型求出隐式类型参数；Nat 版和 Real 版插入的类型参数不同。`TermElabM` 干的就是这类"从有省略、有重载的表面语法到完整核心项"的活。

## TacticM：目标列表管理
%%%
tag := "tacticm-goals"
%%%

`TacticM` 在 `TermElabM` 外再加 tactic 自己的上下文和状态。核心状态就是*待处理目标列表*：

\[源码节选\]
```leanBug
-- Lean/Elab/Tactic/Basic.lean；省略 Tactic.State 的其他细节
structure Tactic.State where
  goals : List MVarId

abbrev Tactic := Syntax → TacticM Unit
```

常用目标操作：

\[示意\]
```leanBug
getGoals : TacticM (List MVarId)
setGoals : List MVarId → TacticM Unit
getMainGoal : TacticM MVarId
getMainTarget : TacticM Expr
```

心智模型：*一个 tactic 读并更新目标列表*。但要注意——*目标数不保证变少*。`constructor` 会把一个合取目标拆成两个子目标，`skip` 保持不变，`swap` 只重排。tactic 成功返回也不代表它"关掉"了目标；只有整个 tactic block 结束时目标列表*必须*为空，证明才算完整。

这是 GPT 版最早的错——它说 "tactic 的本质是接收目标列表返回更小的目标列表"。别学那个，那话是错的。


# Name、Expr、FVarId、MVarId
