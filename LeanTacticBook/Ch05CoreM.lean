import VersoManual
import LeanTacticBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "examples"
set_option verso.exampleModule "Examples.Ch05CoreM"

#doc (Manual) "CoreM" =>
%%%
file := "Ch05CoreM"
tag := "ch05-corem"
%%%

> *本章目标*：从一个具体问题出发：自定义命令怎样读取当前文件中已经存在的声明，并把答案写进 Lean 的消息窗口？`CoreM` 承载这个过程所需的只读信息、可变状态与失败通道，本章逐项观察这些能力怎样参与命令执行。
>
> *版本基准*：Lean `leanprover/lean4:v4.32.2`，Mathlib revision `905b95818eb3`。源码路径和 API 签名均按这一版本说明。

# 概述：把上一章借来的现场逐层拆开
%%%
tag := "ch05-overview"
file := "ch05-overview"
%%%

Ch04 已经让 `my_poly_roots`、`my_assumption` 和 `my_apply` 跑了起来，但当时只给每个接口一份局部契约：`withMainContext` 为什么能装入局部现场，异常怎样中止计算，错误怎样取得位置，计算失败后状态怎样恢复，都还没有拆开。现在从最底层开始还债。

先看一个不依赖证明目标的问题。一个名字究竟指向哪个声明，要看当前 namespace、`open` 声明和前文已经加载的环境；一条诊断该标在哪里，也要知道源码位置；命令执行后产生的消息还要留给编辑器和构建日志读取。这些信息都不在命令的几个字符里。承载这份全局编译现场的计算层就是 `CoreM`。

从本章到 Ch08，我们把 Lean 扩展运行时的四层现场依次打开。它们不是四套互不相干的 API，而是一层层增加能力：

| 计算层 | 主要面对什么 | 在下层之上增加什么 |
|---|---|---|
| `CoreM` | 当前文件与编译过程 | 全局环境、选项、消息、源码引用、异常和核心状态 |
| `MetaM` | 已经译补的表达式与证明洞 | 局部上下文、元变量上下文、类型推断与证明构造 |
| `TermElabM` | 用户写下的项 Syntax | 预期类型、延期任务、合成元变量和恢复政策 |
| `TacticM` | `by` 块里的证明术 | 当前活动目标的有序队列 |

本章处理第一层。`CoreM α` 的操作含义是：

> 在 Lean 当前的核心工作现场中运行一项计算；成功后得到普通值 `α`。

这里的 `α` 可以是名称列表、一个声明、一个布尔值，也可以是 `Unit`。`CoreM α` 是一项会读取现场、更新状态或失败，并在成功后交出 `α` 的计算。`let xs ← action` 中的 `←` 运行 action，再把普通结果交给 `xs`。


假设文件前面已经声明了一个定理，后面的一条新命令想查询它。命令不能只看自己的那几个字符：它还要知道当前 namespace、已经 `open` 的名字、前文注册的声明，以及错误应当指向源码的哪一处。查询结束后，它还要把结果写进消息窗口。

# 第一个问题：命令如何查询一个声明
%%%
tag := "corem-finished-command"
%%%

Lean 已有一条适合观察的命令。它查询某个声明最终依赖哪些公理：

```anchor corem_builtin_print_axioms
#print axioms Classical.choice
#print axioms Nat.add_comm
```

把鼠标移到带波浪线的 `#print` 上，弹层应当显示这次执行产生的消息，而不是 `#print axioms` 的命令文档。这些消息来自示例模块的真实运行。

`Classical.choice` 依赖自身这条公理；`Nat.add_comm` 的依赖闭包没有抵达任何 axiom。后者仍会引用定义和定理，因而“没有公理依赖”绝非“没有依赖”。这里取传递闭包：若 `a` 引用 `b`，`b` 最终引用公理 `c`，`a` 的结果中便应出现 `c`。

公理锥审计的是最终声明，不会单独告诉你 tactic 的搜索算法是否可信。若搜索结果被重建成普通 proof Expr，搜索器算错通常只会导致失败或生成被内核拒绝的项；若系统通过新增 axiom 接入外部或原生计算，公理锥才会把那条桥显露出来。Ch09–Ch13 会反复同时检查“证明怎样构造”和“最终依赖哪些公理”。

输入只有一个标识符，内置命令却完成了三件输入文本本身无法完成的事：

1. 按当前 namespace 和 `open` 声明解释这个短名字；
2. 在当前已经加载的声明表中查询它；
3. 把结果记录成与该源码位置关联的消息。

这三项额外信息合起来，便是本章所谓的“工作现场”。为了逐项解释这些能力，本章稍后会实现教学版 `#book_print axioms`，并让它复现内置命令的查询过程。

先把名字解析、环境查询和消息记录排成执行骨架：

:::codeBox "pseudocode"
```
syntax "#book_print" "axioms" ident : command

@[command_elab bookPrintAxioms]
def elabBookPrintAxioms : CommandElab
  | `(#book_print axioms $id:ident) => withRef id do
      let names ← liftCoreM <| realizeGlobalConstWithInfos id
      for name in names do
        let axs ← collectAxioms name
        logInfo (...)
  | _ => throwUnsupportedSyntax
```
:::

这段轮廓把工作分到两个计算层：

:::codeBox "pseudocode"
```
命令句法与分派             CommandElabM
按 namespace/open 解析名字 CoreM
收集传递公理依赖           读取普通全局声明环境；本章稍后解释所在计算层
记录消息                   CommandElabM
把常量名显示成可点击文字   懒渲染阶段借用 MetaM
```
:::

现在从“为什么普通函数不够用”开始，逐步把这张表里的词解释出来。

# 朴素办法：把所有现场都写成参数
%%%
tag := "why-corem"
%%%

若坚持只写普通函数，名字解析器当然也能工作。它的接口大致会变成：

:::codeBox "pseudocode"
```
resolveName :
  FileName → FileMap → Options → SourceRef →
  Namespace → OpenDeclarations → Environment → InfoState →
  Syntax →
  Exception ⊕ (List Name × InfoState)
```
:::

此外还要加入递归深度、heartbeat、取消 token、trace、名字生成器和消息日志。问题不在“普通函数做不到”，而在每个辅助函数都要反复接收、传递和重组同一批参数；漏传一个更新，后一步看到的现场就会过期。

Lean 的做法是把“普通返回值”和“共同现场”分开。函数类型只写自己真正返回的值，共同现场由一种计算类型自动接续。这种在附加现场中运行的计算，才是下面 `CoreM α` 中 `CoreM` 的含义。

先用行为而不是实现写出这层计算：

:::codeBox "pseudocode"
```
CoreM α =
  读取一份 Context
  + 更新一份 State
  + 可能抛出 Exception
  + 成功时返回 α
```
:::

接下来分别观察 Context、State 和 Exception。读者见过三者各自的行为以后，再看它们在源码中怎样组合。

主线只有三步，其中并行流动着四类信息：

:::codeBox "pseudocode"
```
名字句法
  ──解析成功──→ 普通值：List Name
  ──隐式携带──→ Context：namespace / open declarations / source ref
  ──继续更新──→ State：info tree / messages / environment
  ──解析失败──→ Exception：停止后续 bind，交给调用者处理
```
:::

`←` 左边只接普通值；Context、State 和异常通道都由 `bind` 接续。辅助函数因而无须逐层搬运现场。

# action 与普通返回值
%%%
tag := "corem-computation"
%%%

回到成品中的一句：

:::codeBox "code"
```
let constNames ← liftCoreM <| realizeGlobalConstWithInfos id
```
:::

`realizeGlobalConstWithInfos id` 不会立刻给出名字列表。它返回 `CoreM (List Name)`，也就是一项 action（待运行的计算）。返回类型是列表而不是单个 `Name`，因为当前 namespace 与 `open` 声明可能让一个短名字产生多个合法解析；调用者必须逐项处理，不能擅自假定唯一：

:::codeBox "pseudocode"
```
Syntax → Option Expr → CoreM (List Name)
```
:::

这里省略的是 `(expectedType? := none)`；若调用者提供预期类型，Lean 会把它写进标识符的 info。`CoreM (List Name)` 的意思是：

> 把这段计算放进 Lean 的 Core 工作现场运行；若它成功，取回一个普通的 `List Name`。

计算所需的当前 namespace、`open` 声明、全局环境和源码位置，均由 `CoreM` 携带，无须调用者逐项传入。

因此，action 和 action 运行后的值不是同一种东西。`←` 正是两者的分界：

:::codeBox "code"
```
let constNames := action
```
:::

只是把计算 `action` 本身命名为 `constNames`，得到的仍是 `CoreM (List Name)`；

:::codeBox "code"
```
let constNames ← action
```
:::

才是在当前 monad 中运行 `action`，把普通结果 `List Name` 绑定给 `constNames`。

同一段代码里的三步分别返回三种普通结果：

:::codeBox "code"
```
realizeGlobalConstWithInfos id : CoreM (List Name)
collectAxioms constName        : CommandElabM (Array Name)
logInfo message                : CommandElabM Unit
```
:::

三步之间没有显式传递环境、消息和 info tree。连接这些 action 的规则稍后会命名为 `bind`；现在只要把 `←` 读成“运行右侧 action，并取出成功结果”。

# `Core.Context`：子计算只读的现场
%%%
tag := "core-context"
%%%

第一类现场只供读取。Lean 把它叫作 context（上下文）：一项子计算可以读取当前选项、名字空间和源码位置，却不会因“读取”而改变外层。`withRef`、`withOptions` 能在一个子计算期间临时换值；子计算结束后，外层仍看到原值。

主线用 `currNamespace` 和 `openDecls` 解析名字，用 `ref` 定位消息，用 `options` 读取设置；standalone runner 还须提供文件名和位置映射。先列这些字段：

:::table +header
* - 字段
  - 作用
  - 本章怎样遇到
* - `fileName`、`fileMap`
  - 当前文件及字节位置到行列位置的映射
  - 消息定位与 standalone runner
* - `options`
  - 当前选项
  - `checkExponent` 读取安全阈值
* - `ref`
  - 当前诊断所关联的句法节点
  - `withRef id` 让错误指向用户输入
* - `currNamespace`、`openDecls`
  - 当前名字解析背景
  - 把短名字解析成完整声明名
:::

下面的实验只读取表中已经列出的字段；递归深度、heartbeat、取消 token、quotation 与 trace 不参与这些实验。

## Context 的作用域替换与 State 是两回事
%%%
tag := "core-context-scope"
%%%

`withRef ref action` 只在 `action` 的动态范围内切换当前位置：

:::codeBox "pseudocode"
```
在 ref 作为当前源码位置的 Context 中运行 action
→ action 结束
→ 回到外层原来的 ref
```
:::

`withOptions f action` 通过 Reader 临时替换子计算的 options、diagnostics 缓存和最大递归深度。`action` 结束后，外层 Context 恢复原值。另有一项连带动作：diagnostics 开关若有变化，CoreM 为保持 kernel 设置一致，会经 `modifyEnv` 更新 `Core.State.env` 并清空 cache。

# `Core.State`：会留给下一步的变化
%%%
tag := "core-state"
%%%

第二类现场会随着计算前进而改变，并留给下一步。Lean 把它叫作 state（状态）。例如，前一步加入的新声明必须能被后一步查询；前一步记录的消息也必须留在最终消息列表中。本章只用以下四组：

:::table +header
* - 字段
  - 作用
  - 本章怎样遇到
* - `env`
  - 当前全局环境
  - 查询声明和公理依赖
* - `messages`
  - 消息日志与同类消息去重集合
  - `logInfo`、`logWarning`、`logMessageKind`
* - `nextMacroScope`
  - 下一个宏作用域编号
  - `mkFreshUserName` 与恢复实验
* - `infoState`
  - 编辑器消费的 info tree
  - 输入名字的 hover 与跳转
:::

`ngen` 为 `FVarId`、`MVarId` 和 `LMVarId` 生成唯一名字；`auxDeclNGen` 单独生成可持久化的辅助声明名；`traceState` 累积 trace 消息；`cache` 保存宇宙多态声明的实例化结果；`snapshotTasks` 保存异步子任务的 snapshot tree，供命令结束时汇总消息。它们也都属于 Core.State。

`Environment` 存在 `Core.State.env` 中。查询虽多，编译过程仍会改动它：添加声明、登记环境扩展、导入模块，都会产生供后续计算使用的新环境。

`modifyEnv` 在更新环境时还会清空与旧环境绑定的实例化缓存。绕过公开接口手改内部结构，容易让缓存继续引用旧环境。

# Options 与消息：同一个 Core message log 中为何只报一次
%%%
tag := "corem-options-messages"
%%%

Lean 用阈值拦截巨大指数。下面从真实保护函数中省略 warning 的完整文本和非主线细节：

:::codeBox "code"
```
def checkExponent (n : Nat) (warning := true) : CoreM Bool := do
  let threshold := exponentiation.threshold.get (← getOptions)
  if n > threshold then
    if (← pure warning <&&> logMessageKind `unsafe.exponentiation) then
      logWarning ...
    return false
  else
    return true
```
:::

参数 `warning` 的默认值是 `true`；下面两次调用都省略它，因此会进入 warning 分支。可运行包装连续检查两个超过默认阈值 `256` 的指数：

```anchor corem_options_messages
elab "#check_large_exponents" : command => do
  let (first, second) ← liftCoreM do
    let first ← checkExponent 300
    let second ← checkExponent 301
    return (first, second)
  logInfo m!"accepted? first={first}, second={second}"

#check_large_exponents
```

:::codeBox "code"
```
warning: exponent 300 exceeds the threshold 256, ...
accepted? first=false, second=false
```
:::

两个普通返回值都是 `false`。由于两次检查共用一个 Core message log，同类 warning 只记录一次。这里同时用到了 Reader 与 State：

:::codeBox "code"
```
getOptions                   读取 Core.Context.options
exponentiation.threshold.get 查询选项值
logMessageKind               读写 MessageLog.loggedKinds
logWarning                   写入 Core.State.messages
return false                 返回普通 Bool
```
:::

Command/Core 桥的运行边界还影响消息去重。两次独立的 `liftCoreM` 各自建立 Core 现场，去重记录分属两份 message state。本例把两次检查放进同一个 `liftCoreM do ...`，二者因而共享状态，只发出一条 warning。

# 失败会停下后续步骤，但不等于自动撤销
%%%
tag := "corem-exception-probe"
%%%

第三类现场是失败通道。`throwError` 抛出的异常会让后续 action 不再运行；若外层捕获异常，控制流可以继续。但“停止”不等于“撤销”：先前写入 state 的修改可能仍在。下面先生成一个 fresh name，再抛出并捕获预期异常：

```anchor corem_exception_probe
private def exceptionProbe : CoreM (Bool × Bool) := do
  let before := (← get).nextMacroScope
  let continued ←
    try
      let _ ← mkFreshUserName `insideFailure
      throwError "expected failure"
      pure true
    catch _ =>
      pure false
  let after := (← get).nextMacroScope
  return (continued, before != after)

elab "#check_corem_exception" : command => do
  let (continued, stateChanged) ← liftCoreM exceptionProbe
  logInfo m!"continued past throw? {continued}; state change survived? {stateChanged}"

#check_corem_exception
```

输出是：

:::codeBox "code"
```
continued past throw? false; state change survived? true
```
:::

第一个 `false` 表明 `throwError` 截断了后面的 `pure true`；第二个 `true` 表明 `nextMacroScope` 已经推进。需要失败回溯的算法，应在相应层级显式保存并恢复状态。


# Fresh names 与恢复边界
%%%
tag := "corem-fresh-restore"
%%%

编译器生成局部对象、元变量或辅助声明时必须避开重名。`mkFreshUserName` 给用户提供的名字加上新的宏作用域：

:::codeBox "code"
```
mkFreshUserName : Name → CoreM Name
```
:::

连续调用两次，擦掉宏作用域后看起来都像 `tmp`，内部 `Name` 却不同。

下面检验普通 `restore` 的恢复范围：

```anchor corem_fresh_restore
private def freshRestoreProbe : CoreM Bool := do
  let saved ← Core.saveState
  let first ← mkFreshUserName `tmp
  saved.restore
  let second ← mkFreshUserName `tmp
  return first != second

elab "#check_fresh_restore" : command => do
  let distinct ← liftCoreM freshRestoreProbe
  logInfo m!"fresh names remain distinct after ordinary restore: {distinct}"

#check_fresh_restore
```

:::codeBox "code"
```
fresh names remain distinct after ordinary restore: true
```
:::

程序依次保存状态、生成第一个 fresh name、恢复状态、生成第二个。结果为 `true`，说明普通的 `Core.SavedState.restore` 保留了已经推进的 `nextMacroScope`。本实验不涉及生成内部名字的 `ngen`。

生产源码明确列出了恢复的字段：

:::codeBox "code"
```
def SavedState.restore (saved : SavedState) : CoreM Unit :=
  modify fun current => { current with
    env           := saved.env
    messages      := saved.messages
    infoState     := saved.infoState
    snapshotTasks := saved.snapshotTasks
  }
```
:::

它选择性恢复：

- environment；
- messages；
- info tree；
- snapshot tasks。

它不恢复：

- `nextMacroScope`；
- `ngen`；
- `auxDeclNGen`；
- trace state；
- cache。

Lean 另有 `withRestoreOrSaveFull`，用于增量重用，可以恢复完整 `State` 并计算 heartbeat 消耗。普通 `restore` 与它服务于不同场景。

Core state restore 的范围也不包括以下外部动作：

- `IO.println`；
- 文件写入；
- 网络请求；
- 外部进程。

`do` 负责把计算排成顺序；恢复哪些东西，由具体 API 决定。

# 给刚才的连接规则命名：`pure`、`bind` 与 `do`
%%%
tag := "corem-pure-bind-do"
%%%

我们已经看到普通值、action、`←` 和顺序执行。现在才给它们的两条基本连接规则命名：

锁定版本将这三类现场组合成下面的类型。`ReaderT`、`StateRefT` 和 `EIO` 各给内层计算增加一种能力，对应前面已经观察到的只读现场、可变状态与失败通道：

:::codeBox "code"
```
abbrev CoreM :=
  ReaderT Core.Context <|
  StateRefT Core.State <|
  EIO Exception
```
:::

- `ReaderT Core.Context` 提供只读 Context；
- `StateRefT Core.State` 提供可更新 State；
- `EIO Exception` 提供失败通道和 IO 基础；
- `CoreM α` 中的 `α` 是成功时取回的普通值。

这四行把三个实验中的能力叠在同一计算类型上；`pure` 与 `bind` 再负责连接这些计算。

:::codeBox "code"
```
pure  : α → M α
(>>=) : M α → (α → M β) → M β
```
:::

`pure a` 把普通值 `a` 放进当前计算层，不额外读取或修改现场。`ma >>= f` 先运行 `ma`；若成功得到 `a`，再用 `f a` 继续，并让后一步看到前一步更新后的状态。`do` 记法把这条流水线写得像普通的逐行程序；在这里，`return a` 就是 `pure a` 的 `do` 记法。

下面直接用公理依赖计算检验三条定律：

```anchor corem_monad_laws
private def sortedAxioms (name : Name) : CoreM (Array Name) := do
  return (← collectAxioms name).qsort Name.lt

private def renderNames (names : Array Name) : CoreM String :=
  pure s!"{names.toList}"

private structure MonadLawObservation where
  leftViaPure : Array Name
  direct : Array Name
  rightViaBind : Array Name
  leftAssociated : String
  rightAssociated : String

private def observeMonadLaws (name : Name) : CoreM MonadLawObservation := do
  let leftViaPure ← (pure name >>= sortedAxioms)
  let direct ← sortedAxioms name
  let rightViaBind ← (sortedAxioms name >>= pure)
  let leftAssociated ←
    ((sortedAxioms name >>= fun names => pure names) >>= renderNames)
  let rightAssociated ←
    (sortedAxioms name >>= fun names => pure names >>= renderNames)
  return {
    leftViaPure, direct, rightViaBind, leftAssociated, rightAssociated
  }
```

命令包装只负责运行并比较三组结果：

```anchor corem_monad_laws_use
elab "#check_corem_laws " id:ident : command => do
  let names ← liftCoreM <| realizeGlobalConstWithInfos id
  for name in names do
    let obs ← liftCoreM <| observeMonadLaws name
    logInfo m!"left identity: {obs.leftViaPure.toList} = {obs.direct.toList}"
    logInfo m!"right identity: {obs.rightViaBind.toList} = {obs.direct.toList}"
    logInfo m!"associativity: {obs.leftAssociated} = {obs.rightAssociated}"

#check_corem_laws Classical.choice
```

:::codeBox "code"
```
left identity: [Classical.choice] = [Classical.choice]
right identity: [Classical.choice] = [Classical.choice]
associativity: [Classical.choice] = [Classical.choice]
```
:::

命令逐一打印三组等式的两边；本例六个值都是 `[Classical.choice]`。三组比较依次对应：

:::codeBox "code"
```
左单位律：pure a >>= f            = f a
右单位律：m >>= pure              = m
结合律  ：(m >>= f) >>= g          = m >>= fun x => f x >>= g
```
:::

这组输出只检验当前版本中的一个具体程序。每个 Monad 实例都应普遍满足三条 law：抽取辅助函数、插入无效果的 `pure`，或重新给一串 `bind` 加括号，都应保持计算含义。

三条 law 只约束 `pure` 与 `bind` 的连接方式，不规定失败时怎样回滚。状态能恢复到哪一步取决于具体的保存机制；已经发生的外部 IO 通常无法撤销。

# 公理依赖到底怎样算出来
%%%
tag := "collect-axioms"
%%%

`collectAxioms` 的公开签名只要求两项能力：

:::codeBox "code"
```
public def collectAxioms
    [Monad m] [MonadEnv m]
    (constName : Name) : m (Array Name)
```
:::

当前 monad 只须支持基本组合，并能读取 `Environment`。因此 `collectAxioms` 既可运行在 CoreM，也可直接运行在具有 `MonadEnv` 实例的 CommandElabM。

先立一张三节点依赖图：

:::codeBox "pseudocode"
```
dependencyA ──直接引用──→ dependencyB ──直接引用──→ dependencyC（axiom）
```
:::

A 直接引用 B，沿 B 再走一步才抵达公理 C。下面用同一组声明比较直接依赖与传递公理闭包：

```anchor corem_direct_dependencies
axiom dependencyC : Nat

noncomputable def dependencyB : Nat := dependencyC

noncomputable def dependencyA : Nat := dependencyB

private def directConstants (info : ConstantInfo) : Array Name := Id.run do
  let mut names : NameSet := {}
  for name in info.type.getUsedConstants do
    names := names.insert name
  if let some value := info.value? (allowOpaque := true) then
    for name in value.getUsedConstants do
      names := names.insert name
  return names.toArray.qsort Name.lt

elab "#direct_deps " id:ident : command => withRef id do
  let names ← liftCoreM <| realizeGlobalConstWithInfos id
  let env ← getEnv
  for name in names do
    let some info := env.find? name
      | throwError "unknown declaration '{name}'"
    logInfo m!"direct constants: {directConstants info}"

#direct_deps dependencyA
```

```anchor corem_axioms_builtin_use
#print axioms dependencyA
```

实测输出如下：

:::codeBox "code"
```
direct constants: [Nat, tacticbook_corem.dependencyB]
'tacticbook_corem.dependencyA' depends on axioms: [dependencyC]
```
:::

`Nat` 来自 `dependencyA` 的类型；`dependencyB` 来自定义体。`dependencyC` 不在 A 的直接常量中，却出现在传递公理闭包里。

这里第一次提到 `Expr`。本章暂时把它看作*已经译补好的表达式树*，只使用“从树中找出全局常量”这一项能力；表达式的构造、类型推断和定义等价留到 MetaM 章。

## 第一步：查看声明实际引用了什么
%%%
tag := "collect-used-constants"
%%%

常量的依赖写在类型和定义体中。`Expr.getUsedConstants` 收集一棵表达式树里出现的全局常量名。声明种类不同，待检查的字段也不同：

:::table +header
* - 声明种类
  - 需要继续遍历
* - axiom
  - 自身加入结果，并继续查看它的类型
* - definition、theorem、opaque
  - 类型和定义体
* - constructor、recursor
  - 类型
* - inductive
  - 类型和所有 constructor
* - quotient declaration
  - 不继续展开
:::

只看一层还不够。若 `a` 使用 `b`，`b` 使用 `c`，而 `c` 是公理，`a` 的结果必须包含 `c`。因此算法要递归计算传递闭包。

## 第二步：防止环和重复工作
%%%
tag := "collect-cache-sentinel"
%%%

内部工作 monad 是：

:::codeBox "code"
```
structure CollectAxioms.State where
  seen   : NameMap (Array Name) := {}
  axioms : NameSet := {}

abbrev CollectAxioms.M :=
  ReaderT Environment (StateM CollectAxioms.State)
```
:::

这里有两份不同的状态：

- 外围 Core/Command state 保存整个 Lean 编译现场；
- `CollectAxioms.State` 只服务于这一次图遍历，保存 cache 和当前累计结果。

算法第一次处理声明 `c` 时，先在 `seen` 中写入：

:::codeBox "code"
```
c ↦ []
```
:::

这个空数组是 sentinel。写入后再递归，便能截断 inductive 与 constructor 等声明之间的循环引用。

完成后，算法把排序后的依赖缓存为：

:::codeBox "code"
```
c ↦ [axiom₁, axiom₂, ...]
```
:::

以后再次遇到 `c`，直接合并缓存结果。

## 第三步：导入声明直接读取缓存
%%%
tag := "collect-persistent-extension"
%%%

模块导出前，Lean 通过 persistent environment extension 为每个导出声明预计算公理依赖。下游模块加载 `.olean` 后，按声明名读取结果，省去了跨模块遍历定义体的代价。

生产调用链是：

:::codeBox "pseudocode"
```
collectAxioms
→ getEnv
→ exportedAxiomsExt.getState
→ CollectAxioms.runM
→ collectAndGet
→ collect
→ imported extension / local cache / declaration body
```
:::

调用链在此分成两路：imported declaration 读取模块导出时保存的数据；当前模块尚未导出的声明则检查 body。

`Lean/Util/CollectAxioms.lean` 中的 `CollectAxioms.collectAndGet` 与 `CollectAxioms.collect` 实现这两条路径；调用端依赖的是这里列出的缓存、递归闭包与排序契约。

# 名字解析受当前环境约束
%%%
tag := "resolve-global-name"
%%%

用户写的是：

:::codeBox "code"
```
Classical.choice
```
:::

命令收到带源码信息的 `Syntax`，算法需要完整 `Name`。直接调用 `id.getId` 会漏掉当前 namespace 和 `open` 声明对短名字的影响。

生产入口是：

:::codeBox "code"
```
realizeGlobalConstWithInfos
  (id : Syntax)
  (expectedType? : Option Expr := none) :
  CoreM (List Name)
```
:::

它按以下步骤工作：

1. 根据 `currNamespace` 和 `openDecls` 解析候选；
2. 处理未知名和歧义名；
3. 返回所有合法解析；这里的 `List Name` 可能有一项，也可能有多项；
4. 在 info tree 开启时，为输入句法加入 constant info。

第四步把源码中的标识符与声明相连。Ch02 保存在 Syntax 中的 source info 由此参与诊断定位、hover 和跳转。

下面两个短名分别依靠当前 namespace 和 `open` 声明解析。`id.getId` 只给出原始短名，无法完成这两次查询：

```anchor corem_name_resolution
namespace ResolutionDemo
axiom localAxiom : Nat
#print axioms localAxiom
end ResolutionDemo

namespace OpenDemo
axiom openedAxiom : Nat
end OpenDemo

open OpenDemo
#print axioms openedAxiom
```

# 把 Core 计算接成一条命令
%%%
tag := "commandelabm-shell"
%%%

`#print axioms` 属于 command，入口类型为：

:::codeBox "code"
```
abbrev CommandElabM :=
  ReaderT Command.Context <|
  StateRefT Command.State <|
  EIO Exception

abbrev CommandElab := Syntax → CommandElabM Unit
```
:::

`CommandElabM` 与 `CoreM` 是两套平行栈：

:::codeBox "pseudocode"
```
CoreM        = ReaderT Core.Context    (StateRefT Core.State    (EIO Exception))
CommandElabM = ReaderT Command.Context (StateRefT Command.State (EIO Exception))
                         ↑ liftCoreM 负责适配与回写 ↑
```
:::

Command 层另有 scope stack、command position、macro stack、info state 和 snapshot tasks。它通过下面的官方桥调用 Core 功能：

:::codeBox "code"
```
Command.liftCoreM : CoreM α → CommandElabM α
```
:::

`liftCoreM` 从 command context/state 组装 `Core.Context` 和 `Core.State`，运行 Core action，再把 environment、messages、info trees、traces、名字生成器和 snapshots 合并回 command state。调用者无须手写这段转换。

## 教学命令逐行拆解
%%%
tag := "command-full-walkthrough"
%%%

下面把名字解析、`collectAxioms` 和消息输出接成完整命令：

```anchor corem_print_axioms
syntax (name := bookPrintAxioms) "#book_print" "axioms" ident : command

@[command_elab bookPrintAxioms]
def elabBookPrintAxioms : CommandElab
  | `(#book_print axioms $id:ident) => withRef id do
      let constNames ← liftCoreM <| realizeGlobalConstWithInfos id
      for constName in constNames do
        let axs ← collectAxioms constName
        let constMsg := MessageData.ofConstName constName
        if axs.isEmpty then
          logInfo m!"'{constMsg}' does not depend on any axioms"
        else
          let axiomMsgs := axs.qsort Name.lt
            |>.map MessageData.ofConstName
            |>.toList
          logInfo m!"'{constMsg}' depends on axioms: {axiomMsgs}"
  | _ => throwUnsupportedSyntax
```

定义完成后，用同一对声明检查输出：

```anchor corem_print_axioms_use
#book_print axioms Classical.choice
#book_print axioms Nat.add_comm
```

它与 `Lean/Elab/Print.lean` 中的内置实现功能等价。为便于教学，我们改了三处：

- 内置命令用 `withRef tk`，把位置放在 `#print` token；本章用 `withRef id`，让名字错误直接指向用户写的标识符；
- 内置实现把单个常量的输出抽成私有 `printAxiomsOf`；本章为了连续阅读而内联；
- 内置实现只显式地把非空公理列表中的名字包装成 `ofConstName`；本章也把被查询常量包装成富文本名字。

因此这里对齐*可观察功能和生产 API 路径*；实现细节经过教学化整理。

逐行读：

1. `syntax ... : command` 让 parser 识别新命令；上一章已经讲过这部分。
2. `@[command_elab bookPrintAxioms]` 把这个 syntax kind 注册给下面的 command elaborator。
3. `withRef id` 让后续消息和错误指向用户输入的标识符。
4. `liftCoreM <| realizeGlobalConstWithInfos id` 在 CommandElabM 里运行 Core 名字解析。
5. `collectAxioms constName` 不需要 lifting，因为 CommandElabM 自己有 `MonadEnv` 实例。
6. 跟随内置实现再次执行 `qsort Name.lt`。v4.32.2 的 `collectAxioms` 已返回有序结果；再次排序使输出顺序在调用处也一目了然。
7. `logInfo` 把结果写进 command message state。
8. 最后的 wildcard 分支用 `throwUnsupportedSyntax` 表示当前 elaborator 不接其他句法形状。

CommandElabM 只管接入命令。依赖算法在 `collectAxioms` 中，名字解析在 CoreM 中。

# 富文本名称在哪一步借用 MetaM
%%%
tag := "rich-message-metam"
%%%

若只求文字正确，可以输出：

:::codeBox "code"
```
MessageData.ofName constName
```
:::

它把名字格式化成普通 `MessageData`。内置 `#print axioms` 对*公理列表中的名字*使用：

:::codeBox "code"
```
MessageData.ofConstName constName
```
:::

本章也用 `ofConstName` 包装被查询常量，使两类名字都能在标准编辑器消息中 hover 和跳转。MetaM 出现在 lazy renderer 的一个条件分支里：

:::codeBox "pseudocode"
```
MessageData.ofConstName
├─ PPContext = none
│  └─ format constName                       （不进入 MetaM）
└─ PPContext = some ctx
   └─ Lean.ppConstNameWithInfos（PPExt 层入口）
      └─ ppExt / PPFns 分派
         └─ 标准 pretty-printer：ctx.runMetaM
            └─ PrettyPrinter.ppConstNameWithInfos
```
:::

构造 `MessageData` 时尚未进入 MetaM。渲染器取得 `PPContext` 并调用标准 pretty-printer 后，富文本分支才进入 MetaM。各阶段的边界如下：

- 解析输入名字：CoreM；
- 收集公理依赖：Environment 算法；
- 接入命令：CommandElabM；
- 把结果名字渲染成带语义信息的文字：标准富文本分支借用 MetaM；无 `PPContext` 时退回普通格式化。

本书采用生产源码中的 `ofConstName`，保留可点击输出；渲染阶段使用 MetaM，单独记在层次账目中。

renderer 为了准确显示常量名，会暂时进入带有 `Meta.Context` 与 `MetavarContext` 的 Meta 环境；这些对象将在 Ch06 展开。

# 在前端（frontend）外运行 CoreM
%%%
tag := "corem-to-io"
%%%

在普通 command 中，CommandElabM 已经备好运行现场。若要脱离前端单独运行 `CoreM`，则须亲自提供 Context 与 State：

```anchor corem_standalone
private def standaloneAudit : CoreM (Array Name × Bool) := do
  let axs ← collectAxioms ``Classical.choice
  let first ← mkFreshUserName `tmp
  let second ← mkFreshUserName `tmp
  return (axs, first != second)

unsafe def runStandaloneAudit : IO (Array Name × Bool) :=
  Lean.withImportModules #[{ module := `Init }] {} fun env => do
    let ctx : Core.Context := {
      fileName := "<corem-book>"
      fileMap := default
    }
    let state : Core.State := { env }
    let (result, _) ← standaloneAudit.toIO ctx state
    return result
```

调用：

```anchor corem_standalone_use
#eval runStandaloneAudit
```

得到：

:::codeBox "code"
```
(#[`Classical.choice], true)
```
:::

`withImportModules` 先构造含 `Init` 的 Environment；我们再提供最小 `Core.Context` 和 `Core.State`，最后用：

:::codeBox "code"
```
(action : CoreM α).toIO :
  Core.Context → Core.State → IO (α × Core.State)
```
:::

`toIO` 返回普通结果和最终 Core state。运行前，它用当前 IO heartbeat 计数覆盖传入 Context 的 `initHeartbeats`；运行中遇到普通或内部 Lean exception，则转换为 IO error。CommandElabM 已经为日常命令提供这套现场，`liftCoreM` 因而省去重复装配。

# 源码地图
%%%
tag := "corem-source-map"
%%%

本章查阅以下锁定版本的文件和声明。经过教学化简的签名均标作“示意”：

- `Lean/CoreM.lean`：`Core.Context`、`Core.State`、`CoreM`、saved state、`CoreM.toIO` 的 method notation；
- `Lean/Elab/Command.lean`：`CommandElabM`、`Command.liftCoreM`；
- `Lean/Elab/Print.lean`：内置 `#print axioms`；
- `Lean/Util/CollectAxioms.lean`：`collectAxioms`、局部 cache 与导出扩展；
- `Lean/Util/SafeExponentiation.lean`：`checkExponent`；
- `Lean/Message.lean`、`Lean/Util/PPExt.lean`、`Lean/PrettyPrinter.lean`：lazy message 分派和标准 Meta renderer。

# API 详表
%%%
tag := "corem-api-table"
%%%

下表省略与本章无关的隐式 universe 和 typeclass 参数。锁定版本中的完整签名以 `#check @name` 为准。

## 主线 API
%%%
tag := "corem-api-main"
%%%

:::table +header
* - API
  - 教学签名
  - 读写什么
  - 用途
* - `realizeGlobalConstWithInfos`
  - `Syntax → Option Expr → CoreM (List Name)`
  - 读 env/namespace/open/ref，写 info tree
  - 解析用户输入的全局常量
* - `collectAxioms`
  - `[MonadEnv m] → Name → m (Array Name)`
  - 读环境；内部维护局部 cache
  - 求传递公理依赖
* - `Expr.getUsedConstants`
  - `Expr → Array Name`
  - 只读 Expr
  - 求直接常量依赖
* - `getEnv`
  - `[MonadEnv m] → m Environment`
  - 读环境
  - 取得声明图
* - `Environment.find?`
  - `Environment → Name → Option ConstantInfo`
  - 纯查询
  - 查找声明
* - `logInfo`
  - `MessageData → m Unit`
  - 读 options/ref，写 message log
  - 记录普通信息
* - `MessageData.ofName`
  - `Name → MessageData`
  - 纯构造
  - 普通名字输出
* - `MessageData.ofConstName`
  - `Name → (fullNames : Bool := false) → MessageData`
  - 构造 lazy message；有 PPContext 的标准渲染分支读 PP/Meta context
  - 可 hover、可跳转的常量名
:::

## Context、State 与运行 API
%%%
tag := "corem-api-state"
%%%

:::table +header
* - API
  - 作用
  - 易错边界
* - `getOptions`
  - 读取 `Core.Context.options`
  - 读取当前 Core Context
* - `withOptions`
  - 主要临时修改子计算看到的 options
  - diagnostics 改变时会经 `modifyEnv` 同步 kernel 设置并清 cache
* - `getRef` / `withRef`
  - 读取或临时替换诊断位置
  - ref 表示源码位置；term 译补另有入口
* - `modifyEnv`
  - 更新 Environment
  - CoreM 实例会同时清相关 cache
* - `mkFreshUserName`
  - 生成带 fresh macro scope 的名字
  - 擦除 scope 后相同不表示内部 Name 相同
* - `Core.saveState`
  - 捕获 `Core.SavedState`
  - 保存本身不做恢复
* - `Core.SavedState.restore`
  - 恢复指定的 backtrackable 字段
  - 选择性恢复 `Core.State` 字段
* - `Core.withRestoreOrSaveFull`
  - 为增量重用保存或完整重放状态
  - 用于增量重用场景的完整状态协议
* - `(action : CoreM α).run`
  - 在给定 Context/State 上运行到 `EIO Exception (α × Core.State)`
  - 调用者负责提供完整现场
* - `(action : CoreM α).toIO`
  - 在 IO 中运行并转换 Lean exception
  - 覆写 `initHeartbeats`，并返回最终 Core state
* - `liftM` / `MonadLift IO CoreM`
  - 把 IO 动作提升到 CoreM；`do` 中通常可直接写 IO action
  - state restore 不撤销外部 IO
:::

## Command 薄外壳 API
%%%
tag := "corem-api-command"
%%%

:::table +header
* - API
  - 作用
  - 是否需要 MetaM
* - `CommandElabM`
  - command 阶段的 Reader/State/EIO 兄弟栈
  - 否
* - `CommandElab`
  - `Syntax → CommandElabM Unit`
  - 否
* - `syntax ... : command`
  - 注册命令句法
  - 否
* - `@[command_elab name]`
  - 注册 command elaborator
  - 否
* - `Command.liftCoreM`
  - 运行 Core action 并合并状态
  - 否
* - `throwUnsupportedSyntax`
  - 告诉 dispatcher 当前实现不处理此句法形状
  - 否
* - `MessageData.ofConstName` 的 renderer
  - 生成带语义信息的名字
  - 有 PPContext 且走标准 renderer 时是；fallback 否
:::

# 常见失败方式
%%%
tag := "corem-failures"
%%%

## 把短名字当成最终名字
%%%
tag := "corem-failure-name"
%%%

`id.getId` 只取出句法节点里的原始名字，不处理 namespace/open resolution。按用户语言语义解析时，应调用 `realizeGlobalConstWithInfos` 一类解析器。

## 把 Environment 说成 Reader
%%%
tag := "corem-failure-env-reader"
%%%

Environment 位于 `Core.State.env`。编译过程持续更新环境，后续命令由此看到新声明。

## 看见返回 `CoreM` 就断言全调用链只有 CoreM
%%%
tag := "corem-failure-hidden-meta"
%%%

`addDecl` 的签名是 `Declaration → CoreM Unit`，其必经的 `sorry` 警告检查却运行 MetaM；compiler 和 environment linter 也有类似的内部越层。因此，层次判断须沿实际调用链追查，单看最外层签名并不充分。

`MessageData.ofConstName` 把 MetaM 使用推迟到了显示阶段。有 `PPContext` 的标准 lazy renderer 经 `ppExt` 进入 MetaM；无 context 的分支直接格式化名称。

## 把 CommandElabM 画在 CoreM 上面
%%%
tag := "corem-failure-command-stack"
%%%

两者是平行栈，`liftCoreM` 负责显式适配与状态合并。继承链画法容不下这一步，后面的状态解释也随之失真。

## 以为异常等于事务
%%%
tag := "corem-failure-rollback"
%%%

异常截断后续步骤，已经写入 `StateRefT` 的修改仍可保留。搜索、替代方案和增量重用各有相应的 saved-state API；IO 则在这些状态之外。

# 练习
%%%
tag := "corem-exercises"
%%%

## 练习 5.0：先判断类型
%%%
tag := "corem-exercise-types"
%%%

不运行代码，分别判断下面两个 `names` 的类型：

:::codeBox "code"
```
let names := realizeGlobalConstWithInfos id
let names ← realizeGlobalConstWithInfos id
```
:::

基础答案：第一行得到 `CoreM (List Name)`，也就是一段尚未运行的计算；第二行在当前 `do` 中运行计算，得到普通值 `List Name`。

## 练习 5.1：声明种类
%%%
tag := "corem-exercise-kind"
%%%

写一条 `#decl_kind ident` 命令，解析名字后用 `Environment.find?` 判断它是 axiom、theorem、definition、inductive 还是 constructor。用 `Nat.add_comm` 测试时，预期输出包含 `Nat.add_comm: theorem`。

基础答案：

```anchor corem_decl_kind_solution
private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient declaration"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

elab "#decl_kind " id:ident : command => withRef id do
  let names ← liftCoreM <| realizeGlobalConstWithInfos id
  let env ← getEnv
  for name in names do
    let some info := env.find? name
      | throwError "unknown declaration '{name}'"
    logInfo m!"{MessageData.ofConstName name}: {declarationKind info}"

#decl_kind Nat.add_comm
```

## 练习 5.2：直接依赖与传递依赖
%%%
tag := "corem-exercise-direct-transitive"
%%%

对同一个声明分别输出：

- type/value 中直接出现的常量；
- `collectAxioms` 给出的传递公理依赖。

解释两个集合各自回答什么问题。正文“三节点图”中的 `directConstants` 就是基础答案；验收时，`dependencyA` 的直接结果应含 `dependencyB`，而传递公理结果应为 `[dependencyC]`。

## 练习 5.3：普通名字与富文本名字
%%%
tag := "corem-exercise-rich-name"
%%%

把 `#book_print axioms` 中的 `MessageData.ofConstName` 暂时换成 `MessageData.ofName`。比较纯文字、hover 和跳转，再分别注明构造阶段与渲染阶段所在的执行层。请在编辑器中验收；命令行只能显示纯文本。

基础答案：两种 `MessageData` 都在 CommandElabM 中构造。`ofName` 立即生成普通名字文本，没有常量语义信息；`ofConstName` 生成 lazy 常量名消息，带 `PPContext` 的渲染分支会进入 MetaM，因而能提供 hover 与跳转。命令行只能比较纯文字，hover 与跳转须在编辑器中验收。

```anchor corem_plain_print_solution
syntax (name := plainPrintAxioms) "#plain_print" "axioms" ident : command

@[command_elab plainPrintAxioms]
def elabPlainPrintAxioms : CommandElab
  | `(#plain_print axioms $id:ident) => withRef id do
      let names ← liftCoreM <| realizeGlobalConstWithInfos id
      for constName in names do
        let axs ← collectAxioms constName
        let constMsg := MessageData.ofName constName
        if axs.isEmpty then
          logInfo m!"'{constMsg}' does not depend on any axioms"
        else
          let axiomMsgs := axs.qsort Name.lt
            |>.map MessageData.ofName
            |>.toList
          logInfo m!"'{constMsg}' depends on axioms: {axiomMsgs}"
  | _ => throwUnsupportedSyntax

#plain_print axioms Classical.choice
```

## 练习 5.4：预测恢复结果
%%%
tag := "corem-exercise-restore"
%%%

在保存状态后依次：

1. 写一条消息；
2. 生成 fresh name，并用 `addDecl` 以该名字临时加入一个 axiom；
3. 确认环境中已有该声明，再恢复；
4. 检查消息和临时声明，并再次生成 fresh name。

先根据 `SavedState.restore` 源码写出预测，再运行验证。验收表至少包含 `messages`、`nextMacroScope`、`env` 三行；预期是消息与环境恢复，而 `nextMacroScope` 不恢复。不要用“回滚应该全撤销”代替逐字段判断。

基础答案：

```anchor corem_restore_solution
private structure CoreStateObservation where
  envRestored : Bool
  messagesRestored : Bool
  nextMacroScopeNotRestored : Bool
  freshNamesDistinct : Bool

private def observeCoreState : CoreM CoreStateObservation := do
  let before ← get
  let saved ← Core.saveState
  logInfo "state-observation message"
  let probeName ← mkFreshUserName `stateProbe
  addDecl <| Declaration.axiomDecl {
    name := probeName
    levelParams := []
    type := mkConst ``Nat
    isUnsafe := false
  }
  let envMutationObserved := (← getEnv).contains probeName
  saved.restore
  let afterRestore ← get
  let second ← mkFreshUserName `stateProbe
  return {
    envRestored := envMutationObserved && !afterRestore.env.contains probeName
    messagesRestored := before.messages.toList.length == afterRestore.messages.toList.length
    nextMacroScopeNotRestored := before.nextMacroScope < afterRestore.nextMacroScope
    freshNamesDistinct := probeName != second
  }

elab "#observe_core_state" : command => do
  let obs ← liftCoreM observeCoreState
  logInfo m!"env restored={obs.envRestored}; messages restored={obs.messagesRestored}; nextMacroScope not restored={obs.nextMacroScopeNotRestored}; fresh names distinct={obs.freshNamesDistinct}"

#observe_core_state
```

## 练习 5.5：声明来源模块
%%%
tag := "corem-exercise-module"
%%%

扩展命令，输出每个公理所属的模块。可从 `Environment.getModuleIdxFor?` 入手，并分别测试导入模块中的声明和当前文件中的声明。所得结果只是已发现依赖的来源；求“最小 imports”还须处理句法扩展、宏、证明术注册等 term 常量依赖图以外的关系。

基础答案：

```anchor corem_module_solution
axiom currentModuleAxiom : Nat
noncomputable def currentUsesAxiom : Nat := currentModuleAxiom

elab "#axiom_modules " id:ident : command => do
  let names ← liftCoreM <| realizeGlobalConstWithInfos id
  for name in names do
    let axs ← collectAxioms name
    for axiomName in axs do
      let env ← getEnv
      match env.getModuleIdxFor? axiomName with
      | none => logInfo m!"{axiomName}: {env.header.mainModule}"
      | some idx =>
        let moduleName := env.header.moduleNames[idx.toNat]!
        logInfo m!"{axiomName}: {moduleName}"

#axiom_modules Classical.choice
#axiom_modules currentUsesAxiom
```

# 下一层缺什么
%%%
tag := "corem-to-metam"
%%%

至此，我们能读取全局声明、解析名字、记录消息，并把这些操作接成一条 Lean 命令。上一章的 `my_step` 还要求查看*当前目标*和*局部上下文*；这些信息不在 `#book_print` 的全局 Environment 中，目标元变量也尚未出现。

下一章以改写为主案例。程序拿到一条等式证明后，要在当前目标中寻找匹配位置，处理定义等价，并构造新的证明项。完成这些工作，需要进入 `MetaM`。
