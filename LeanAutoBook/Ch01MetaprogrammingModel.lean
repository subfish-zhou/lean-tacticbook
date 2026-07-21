import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch01MetaprogrammingModel"

#doc (Manual) "Lean 中的 tactic 基础设施" =>
%%%
file := "Ch01MetaprogrammingModel"
tag := "ch01-metaprogramming-model"
%%%

> *本章目标*：拿上一章亲手造的那台玩具机器当地图，逐个零件对到 Lean 的真实实现上——四层 monad、Reader/State/Except、目标列表、局部上下文、元变量上下文、lifting。核对哪里同构、哪里现实更狠，把上一章挖的六个坑一个个填掉。
>
> *版本基准*：Lean `leanprover/lean4:v4.30.0-rc1`，Mathlib revision `0692ef80fb13`。本章的 API 签名和源码路径都按这个版本对齐。


# 从发明回到现实：一张对照表

%%%
tag := "tactic-metaprogram"
%%%

上一章我们没碰 Lean 一行真代码，却把 tactic 这台机器造了出来：证明状态管理*一列*目标；每个目标是局部假设加待证命题；tactic 是*状态转移*，成功不承诺目标变少；关目标等于往一张带洞的证明里合法填结构；顺序接力靠 `pure`/`bind` 抽象，而 `orElse`/`repeat` 还另需选择与回滚语义；效果分只读背景、可变状态、失败、IO 四种。最后我们发现，这个被逼出来的顺序组合形状，名字叫 monad。

这一章把每个发明的零件，对到 Lean 现实里的名字。先给全表，本章其余部分就是逐行展开它、并核对“现实比玩具多了什么”：

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
| “扔副本白嫖回滚” | 可回溯状态的存档/恢复，以及 `TacticM` 在失败分支上的恢复策略 |

看懂 tactic 源码，你要能回答四个问题，它们正是上一章“状态怎么传、背景怎么读”那套追问的现实版：

1. 这段代码运行在哪一层 monad 里？
2. 这一层能读到哪些上下文（对应玩具里的 `Env`）？
3. 这一层能改哪些状态（对应玩具里的 `State`）？
4. 想调下层操作、或者反过来在下层跑上层操作，各自需要怎么转换（对应玩具里“能力叠层”的方向性）？

Lean 把这些能力分成 `CoreM`、`MetaM`、`TermElabM`、`TacticM` 四层。我们仍按上一章的顺序走——从"一个 tactic 实际需要什么"出发，只不过这次每一步都能落到真实的类型和源码上。


# Monad：把返回值和计算效果放在一起
%%%
tag := "monad-effects"
%%%

## 上一章那个 `my_assumption`，现实需要什么

%%%
tag := "tactic-required-context"
%%%

上一章我们造过 `assumption`：扫一遍局部假设，找一个跟目标匹配的，用它关掉目标。现在给它换上真实需求——找的不是“逐字符相同”，而是“定义等价”的假设。就这么点事，它得能拿到：

- 当前目标；
- 当前局部上下文——里面装着局部变量和假设（对应玩具里 `Goal.hypotheses`）；
- 元变量状态——因为定义等价检查可能会给元变量赋值（对应玩具里“带洞证明的洞”）；
- 全局环境——名字、常量、类型检查都要看已声明的内容；
- 选项和消息系统；
- 一条失败通道——用来说"没找到合适的假设"（对应玩具里的 `Error`）。

上一章我们已经论证过：把这些全塞进参数显式传，签名会失控。这里再快速复核一遍那个结论，然后直接对到 Lean 的类型上。先用三个概念占位符看接口形状：

\[伪代码\]
```
Goal   = 当前待证目标的概念占位符
Proof  = 构造出的证明的概念占位符
Error  = 失败信息的概念占位符
```

强调一下：`Goal`、`Proof`、`Error` *不是* Lean 已经定义好的类型，别去搜。它们只是帮我们讨论接口的名字。

现在看类型 `Goal → Proof`——它太窄了：这个签名只说"给一个目标，直接得到一个证明"，装不下环境依赖、状态更新和失败。你当然还可以坚持"就用普通函数"，把这些都显式塞进参数和返回值，签名会长成这样（这正是上一章那个 `Env → State → 结果` 摊平后的样子）：

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

## pure、bind，兑现你上一章造的那两个操作

%%%
tag := "pure-bind-state-passing"
%%%

上一章你从 `then`、`allGoals` 里那段抄烂的样板中，逼出了 `pure` 和 `bind`。这一节把它们对到 Lean 的真实签名，并用一个能跑的例子，逐行看 `bind` 到底替你传了什么状态——那正是玩具里 `state → state1 → state2` 那条你不想再手接的链。

先统一口径：我这里说的"副作用"是*广义*的*计算效果（effect）*，就是上一章那四种——失败、读环境、读写状态、IO。它不特指"改全局变量"，也不是说代码"不纯净"。

Lean 里一个 monad 主要提供两个操作，跟你发明的一字不差：

\[示意\]
```leanBug
pure : α → M α
(>>=) : M α → (α → M β) → M β
```

`pure a` 把普通值 `a` 装进 `M` 计算里，不带额外的效果（就是你的“把值塞进机器”）。`ma >>= f` 先跑 `ma` 拿到 `a`，再把 `a` 喂给 `f` 跑下一步（就是你的“接起来”）。Lean 的 `do` 语法就是这条流水线的糖衣。

上一章我们把 monad laws 讲成了“重构安全的许可证”，这里给出它们在 Lean 里的精确写法：

- 左单位律：`pure a >>= f = f a`
- 右单位律：`m >>= pure = m`
- 结合律：`(m >>= f) >>= g = m >>= (fun a => f a >>= g)`

回忆上一章的翻译：`pure` 是接线里的空操作，一串 `bind` 怎么加括号都一样。所以你把几步 tactic 抽成辅助函数、或把大 `do` 拆小，行为不变——靠的就是这三条。

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

## Reader、State、Except：你发明的三种效果，各有一个 transformer
%%%
tag := "reader-state-except"
%%%

上一章你把效果分成了三种待遇：只读背景进得来改不了、可变状态读写接力、失败随时短路。Lean 给这三种待遇各配了一个 transformer——`ReaderT`、`StateT`、`ExceptT`。下面逐个对上。

### Reader：读一份固定的上下文（你的“只读背景 Env”）
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

这正是上一章埋的雷。玩具里 `orElse` 的回滚之所以“免费”，是因为状态是个到处复制的值，失败支弄脏的是副本，一扔就干净。现在 Lean 为了性能把状态换成了*原地修改的可变引用*——`t1` 的改动就地生效，`StateRefT` 的通用异常实例本身不会自动把引用恢复到旧值。Lean 因而另外提供可回溯状态的存档/恢复机制：`withoutModifyingState` 会在子计算结束后无条件丢弃其中的可回溯修改，适合“探查但不提交”；按成功与否决定提交的组合器则在失败时恢复存档；`TacticM` 自己的异常处理也会在尝试分支前保存状态、捕获失败后恢复。这里恢复的是被指定为*可回溯*的那部分状态，不是整个世界。回滚不是“只要用了 monad/StateRefT 就白送”，而是额外设计出来的事务策略——跟你上一章的推断一字不差。

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

一句话心智模型：*tactic 的运行环境 = 一堆效果能力的叠层，每加一层 `XxxT` 就多一种能力*。这就是上一章“每加一种能力就叠一层”那句话的现实版——只不过现实里的层是 `ReaderT`/`StateT`/`ExceptT` 这些有名有姓的东西。

不过要加个小括号——"每加一层就多一种能力"有个前提：相应的 lifting 和 typeclass 实例得存在。乱堆一通不保证外层能直接用 `read`、`get`、`throw` 这套统一接口，Lean 只是*在实例存在时*帮你打通。

## 为什么 Lean 用 monad 组织这些能力
%%%
tag := "why-lean-uses-monads"
%%%

不用 monad 也能显式传参数和状态——就像本节开头那个 20 参数的签名。Lean 用 monad 不是逻辑必然，是工程选择。理由是这几条：

1. *签名只暴露能力层*：`getMainGoal : TacticM MVarId` 告诉你它跑在 `TacticM` 里，不用展开几十个环境、状态、异常、IO 参数。
2. *状态按顺序传递*：`bind` 帮你把前一步的新状态交给后一步，`do` 管理这条管线。
3. *异常自动传播*：中间某步失败，后面的自动跳过，错误一路冒泡到调用者。
4. *局部控制可回溯状态*：`withoutModifyingState` 能跑一次探查，并且无论成功失败都丢掉其中的可回溯修改；“成功提交、失败恢复”则由相应的提交/异常组合器负责，`TacticM` 的尝试分支也采用先存档、失败后恢复的策略。`withLCtx` 能在临时局部上下文里跑一段 Meta 计算（对应你的“带作用域的局部换 Env”）。
5. *层之间可 lifting*：只要实例存在，外层 monad 直接调下层操作，你不用手写每一层的封装。

第 4 点有边界：*恢复可回溯状态不等于回滚全部内部缓存，更不等于回滚世界*。已经打印到终端的字符、写到文件的内容、走出去的网络请求，都不会因为你恢复了状态而消失。打印出去的话比元变量更难收回来——这就是上一章“状态可回滚，IO 不可回滚”那条，在真实 API 上的兑现。

还有一条上一章反复强调、这里必须落地的区分：*失败通道里塞的不都是一回事*。“没找到匹配假设”“目标不是等式”是*预期内*的失败，`orElse` 该据此换路；而“往环境里加了个类型不对的声明”“内核拒绝了一个证明项”是*真出错*，不该被 `orElse` 悄悄吞掉。关键在于：*异常通道本身并不可靠地区分这两类*——它就是一条统一的错误通道，同一个异常到底算“预期内换路”还是“严重错误”，取决于是谁、用哪个捕获/选择组合器去接它。所以捕获必须*小心圈定范围*：只在你确信“这里的失败就是搜索的一部分”时才用回溯组合器去兜，否则就会把真错误当成“换条路就好”而悄悄吞掉。区分它们、把捕获的作用域限制好，仍然是写 tactic 的人的责任。

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

现在回答上一章的第一个坑：那个 `Env → State → 结果` 的形状，Lean 到底叠了几层、为什么正好是那几层。答案是四层，每一层都是前一层外面再包一圈 `ReaderT`（加只读背景）和 `StateRefT`（加可变状态）——正是你发明的“叠层”。来看真实定义。先把三个可能拦路的语法讲一下：

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

`MetaM` 在 `CoreM` 外再叠一层 `Meta.Context` 和 `Meta.State`。这里正好回答上一章的第 2、3、4 个坑：局部假设住在哪、“同一个构造子的洞”是什么、那句危险的“命题相同”到底是什么。有两个特别容易混的数据，位置不一样：

- `LocalContext`：*在哪* 当前 Meta 计算从 `Meta.Context.lctx` 读它；*性质* Reader，单次计算里只读；*典型变化* 进 telescope 或局部绑定时，在扩展后的上下文里跑子计算。这就是玩具里 `Goal.hypotheses`——注意它是*只读背景*的一部分，跟你上一章把假设当只读原料库的直觉一致。但要小心一个常见误解：*并不是所有目标共用同一份 `LocalContext`*。
- `MetavarContext`：*在哪* `Meta.State`；*性质* State，可更新；*典型变化* 创建元变量、赋值元变量、定义等价检查求解约束时都会变。这就是玩具里那些“带洞证明的洞”——现实里它们是*元变量*，住在可写状态里，会被*赋值*。

上一章我用“同一个 `And.intro` 的两个洞”含糊兜住的东西，现实就是这里：`constructor` 开出的两个子目标各是一个元变量，它们通过共享的 `MetavarContext` 彼此牵连；解出一个洞，可能顺手把另一个洞也确定了。这里要接住上一章那个区分：玩具里的洞*一直有各自的身份*（元变量的 id 天生互不相同），被简化掉的*不是*身份，而是洞之间这种跨目标的*依赖与共享约束*——`MetavarContext` 才是这种约束的诚实承载者。

*`LocalContext` 其实活在两个相关的层次上*，这一点上一章的玩具没能表达，这里必须说清：

- 当前 Meta 计算读的是 `Meta.Context.lctx`——“此刻这段计算眼里的局部上下文”；
- 而*每个目标各自的* `MetavarDecl` 里，都记着*它自己*的 `lctx`（和局部实例）——因为不同目标（比如 `intro` 之后和 `intro` 之前的目标）手头能用的假设本来就不一样；
- 当你“进入”某个目标去干活（概念上就是 `MVarId.withContext`），它做的正是把*那个目标记录的 `lctx`* 装进 `Meta.Context`，让接下来这段 Meta 计算在这个目标的上下文里跑。

所以“局部假设是只读背景”没错，但要精确成：*每个目标带着自己的那份只读上下文，进入哪个目标，就把哪份上下文临时装上*——不是全局一份大家共享。`forallTelescope` 进 `∀ x, ...` 的 body 时，会在扩展后的局部上下文里跑你给的回调；回调跑完，外层看到的还是原来那份。这就是“进函数体临时借一份、出来还回去”的意思，也是上面“进入目标装上它的上下文”的同一个机制在更小尺度上的体现。

`MetavarContext` 记录元变量的声明和赋值。`mkFreshExprMVar` 会加新元变量；`isDefEq` *可能*给现有元变量赋值——所以它不是纯粹的判断，是有副作用的。不过它也不是“比较失败后照样留下一地赋值”：外层定义等价检查会设检查点，返回 `false` 或抛异常时恢复相关状态，成功时才提交求解出的赋值。这个事务边界，正是扫描多个候选时不互相污染的保障。

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

单独点名 `isDefEq`，因为它填的正是上一章那个坑。玩具里 `assumption` 有句含糊的“命题相同”，我当时就警告它将来要出事。现实里这个“相同”就是 `isDefEq e₁ e₂`——它判的不是逐字符相等，而是*定义等价*（`Nat` 和 `ℕ`、`n + 0` 和 `n` 会被判成相等）。更要命的是它*不纯*：一次成功的检查可能顺手给某个元变量赋值，改了 `MetavarContext`。所以 `isDefEq` 不是一个安静的谓词，是一次带检查点、可能提交状态变化的操作；失败检查会撤回自己的试探，成功检查则可能留下求解结果。上一章担心的“这里要出事”，出的就是这种事——你以为在做布尔比较，其实是在进行一次受事务保护的约束求解。

## TermElabM：由预期类型驱动的精译
%%%
tag := "termelabm-elaboration"
%%%

这一层回答上一章的第 4 个坑：“靠预期类型补全表面语法”在现实里怎么运作。parser 先把文本变成 `Syntax`；`TermElabM` 再结合环境、局部上下文、*预期类型*把 term syntax 精译成 `Expr`。这一层负责名字解析、重载消解、隐式参数插入、typeclass 综合、约束求解——一整套。这台机器玩具里根本没造：玩具直接拿现成的证明对象，从不处理“有省略、有重载的表面语法”。这是现实比玩具*多出来*的一整层。

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

最后回答上一章的第 5、6 个坑：目标列表管理是不是真如玩具那样设计、回滚在可变引用下怎么做。`TacticM` 在 `TermElabM` 外再加 tactic 自己的上下文和状态。核心状态就是*待处理目标列表*——正是玩具里 `State.goals`：

\[源码节选\]
```leanBug
-- Lean/Elab/Term/TermElabM.lean；省略 Tactic.State 的其他细节
structure Tactic.State where
  goals : List MVarId

-- Lean/Elab/Tactic/Basic.lean
abbrev Tactic := Syntax → TacticM Unit
```

注意 `goals : List MVarId`——是一列元变量标识，正是玩具里“目标列表是洞的工作索引”这句话的现实版本。这里要比玩具精确一步：raw `Tactic.State.goals` 是当前 tactic 的*工作队列*，可能暂时还含有已经被赋值的元变量；`pruneSolvedGoals`/`getUnsolvedGoals` 才会过滤出真正尚未解决的目标。也就是说，队列和“未填洞集合”通常同步，但不是每个瞬间都字面相等。

常用目标操作：

\[示意\]
```leanBug
getGoals : TacticM (List MVarId)
setGoals : List MVarId → TacticM Unit
getMainGoal : TacticM MVarId
getMainTarget : TacticM Expr
```

心智模型：*一个 tactic 读并更新目标工作队列，同时在共享的元变量状态里推进证明*。但要注意——*未解决目标数不保证变少*。`constructor` 会把一个合取目标拆成两个子目标，`skip` 保持不变，`swap` 只重排。tactic 成功返回也不代表它"关掉"了目标；整个 tactic block 结束时，经过清理后得到的*未解决目标*必须为空，证明才算完整。raw `goals` 队列在中间步骤里则可能尚未清走已赋值项。这跟你上一章亲手在 `intro`（不变）、`constructor`（变多）、`swap`（重排）、`skip`（不动）上验证过的结论完全一致——现实没有推翻它，只是把“队列”和“未解决集合”分得更细。

所以要把这句话钉死并当心一个常见的误导说法：“tactic 的本质是接收目标列表、返回更小的目标列表。” 这是错的，上一章四个例子已经从三个方向把它打死了。tactic 的本质是*在共享的元变量状态上，合法地推进那张带洞证明*；目标列表变长、变短、原地重排都可能发生。

回滚那一环（第 6 个坑）也在这里落地：`goals` 和 `MetavarContext` 都通过可变状态层被更新，`orElse`（在 Lean 里是 `<|>` 一类的组合器）不能指望 `StateRefT` 自动撤销。`TacticM` 的尝试/异常路径会先保存可回溯状态，分支失败时恢复；`withoutModifyingState` 则是另一种策略——连成功分支的可回溯修改也丢掉，专供只观察不提交的探查。两者都不是玩具里“扔副本”那种免费午餐。

# 现在你能读什么源码，还缺什么

%%%
tag := "what-you-can-read-now"
%%%

上一章的六个坑，这一章都填了：四层 monad 的形状、只读背景与可变状态的分工、元变量怎么把洞连起来、`isDefEq` 的副作用、目标列表“不保证变少”、可变引用下的显式回滚。玩具机器的每个零件，现在都对上了一个真实的类型或源码路径。

*现在你已经能读的源码*：一个最小 tactic 的骨架——`getMainGoal` 取出主目标那个 `MVarId`，`getType` 看它的待证命题，在 `MetaM` 里 `inferType`、`isDefEq` 做检查，最后更新状态。这“更新状态”里藏着一个上一章玩具没能分开、极容易搞混的区分，务必分清：

- `MVarId.assign` 是*真正把表达式写进证明洞*的低层步骤——它把赋值写入元变量上下文。这里不能把“写进去”和“已经合法”混为一谈：`assign` 本身不做类型检查、occurs check，也不检查该元变量是否早已赋值；对同一元变量再次调用甚至会覆盖旧值。规范的 tactic 必须由调用方先构造并检查类型正确、无循环且目标尚未赋值的证明表达式，再执行这个写操作，最终仍由后续类型检查与内核把关。玩具里“把洞补死”对应的是“检查后赋值”这一整套动作，不是裸调用一个写操作。
- `setGoals`（以及 `replaceMainGoal` 等）*只更新 tactic 的工作队列*——它改的是“接下来还要处理哪些目标”这份清单，*本身并不能证明任何东西*。你可以用 `setGoals []` 把队列清空，但只要没 `assign` 过对应的元变量，证明就是不完整的，最后会以“未解决的目标 / 元变量未赋值”被拒。
- `pruneSolvedGoals`/`getUnsolvedGoals` 能做的，是从*当前工作队列*里过滤掉已经被赋值的目标；它们不会遍历整张证明、也找不回曾被 `setGoals` 错误删掉但仍未赋值的洞。因此工作队列本身也必须维护正确：过滤操作负责清走“已经解决但还留在队列里的项”，不能修复“未解决项被提前丢出队列”的 bug。

一句话：*检查并赋值负责填证明洞，`setGoals` 只负责待办清单，别拿后者当前者*。你已经知道每一步跑在哪一层、能读什么、能改什么、失败会怎样冒泡。上一章那个 `my_assumption` 的伪代码，你现在有能力把它翻成真的 Lean。

*还缺的那块，正是下一章*：本章从头到尾把目标的“待证命题”当成一个不透明的 `Expr` 占位符——`getMainTarget` 给你一个 `Expr`，但我们从没打开看过它里面长什么样。这里要先纠正一个容易过度推广的印象：*不是每个 tactic 都要亲手拆 `Expr`*。`constructor`、`intro` 确实要看目标*最外层*的形状（是不是 `∧`、是不是 `→`），这需要检视 `Expr` 的外层结构；但 `assumption` *不用*拆解 `Expr`——它的正常做法是遍历局部上下文里的每条声明，拿它的类型和目标类型去调 `isDefEq`，让定义等价判定去比，自己一点都不碰 `Expr` 的内部构造。真正需要*显式检视和构造* `Expr` 的场合（判断外层构造子、拆出子项、拼出新的证明项），才是下一章要专门教的。

所以下一章的 Expr 章把这最后一块补上：`Expr` 有哪些构造子、怎么对它模式匹配、怎么构造新的 `Expr` 当证明项。学完那一章，你手里就齐了——既知道 tactic 跑在什么机器上（本章），又知道它操作的数据长什么样（下一章），可以动手写真正的 tactic 了。
