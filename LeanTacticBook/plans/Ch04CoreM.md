# Ch04 `CoreM` 章节架构与写作计划

> 状态：正文、配套 examples、聚合入口、R2 双审、整书构建与 HTML 渲染均已完成。
>
> 目标文件（实施时）：
>
> - 书稿：`LeanTacticBook/Ch04CoreM.lean`
> - 可运行示例：`examples/Examples/Ch04CoreM.lean`
> - 聚合入口：`LeanTacticBook.lean`、`examples/Examples.lean`
>
> 版本基准：Lean `leanprover/lean4:v4.32.2`；Mathlib revision `905b95818eb32af7874a58b427f50c1711a5e96c`。

## 一、这一章究竟要完成什么

读者在上一章已经会声明和展开宏，但宏只改写 `Syntax`。现在给出一个不能靠宏完成的任务：

```lean
#print axioms Classical.choice
#print axioms Nat.add_comm
```

第一条应报告：

```text
'Classical.choice' depends on axioms: [Classical.choice]
```

第二条应报告：

```text
'Nat.add_comm' does not depend on any axioms
```

为了实现这条命令，程序必须知道：

- 当前打开了哪些 namespace；
- 某个短名字究竟解析成哪个全局声明；
- 当前 `Environment` 里有哪些声明；
- 一个声明的 type/value 引用了哪些常量；
- 已经访问过哪些声明，避免递归环和重复工作；
- 消息应标在哪个源码位置；
- 最终结果如何进入 Lean 的消息系统和编辑器。

这一串需求自然逼出 `CoreM`。本章不从抽象的 `ReaderT`/`StateT` 名词开场，也不先写一个数字计数器。先把命令跑起来，再把其中暗中传递的 context、state、exception 和 IO 一件件摊开。

本章完成后，读者应能：

1. 把 `CoreM α` 读作“在 Lean 的核心编译现场中运行、成功时返回 `α` 的计算”；
2. 区分 `Core.Context` 与 `Core.State`；
3. 看懂 `pure`、`>>=`、`do`、`let x ← action` 在真实 CoreM 程序中的作用；
4. 使用 `Environment` 查询声明并运行 `collectAxioms`；
5. 解释为什么 `Environment` 是 state 而不是 reader；
6. 使用 options、messages、source ref、info tree 和 fresh names；
7. 解释普通顺序执行与显式状态恢复的区别；
8. 写出一个真正注册到 Lean 中、能在源码里调用的 `#print axioms` 同类命令；
9. 分清 CoreM 语义内核、CommandElabM 外壳和 MetaM 富文本渲染三条责任边界。

## 二、章名与一句话主线

章名已经确定为：

> **CoreM**

一句话主线：

> 我们从零复刻 `#print axioms`：先查全局声明的公理依赖，再把它接到 Lean 的命令和消息系统里；CoreM 的每个主要部件都由这项工作逼出来。

不建议把章名写成“Monad 与 CoreM”。“Monad”是本章解释真实程序时得到的抽象，不是读者进门前必须吞下的一颗药丸。

## 三、整章叙事结构

### 4.1 先看完成品：一个能在 Lean 文件里运行的命令

开篇直接放两个真实调用：

```lean
#book_print axioms Classical.choice
#book_print axioms Nat.add_comm
```

命令名暂用 `#book_print axioms`，避免和 builtin `#print axioms` 冲突。正文同时展示 builtin 输出，让读者知道我们不是发明一个无关工具。

本节只给最终效果和十几行实现，不立刻解释所有名字。读者先知道本章会做成什么。

第一处醒目标账：

```text
Syntax/command dispatcher：CommandElabM
名字解析和 info：CoreM
公理依赖闭包：MonadEnv，可在 CoreM/CommandElabM 中运行
消息：CommandElabM
富文本常量名：显示时借一次 MetaM
```

这样从第一页起就不假装完整命令“纯属 CoreM”。

### 4.2 `CoreM α` 不是一个 `α`

沿最终代码中的三行解释：

```lean
let names ← liftCoreM <| realizeGlobalConstWithInfos id
let axs   ← collectAxioms constName
logInfo ...
```

重点不是先背 monad 定义，而是说明：

- `realizeGlobalConstWithInfos id` 不是 `List Name`，是一个将来在 Core 现场运行后才得到 `List Name` 的计算；
- `collectAxioms constName` 不是 `Array Name`，它需要当前环境；
- `logInfo` 的普通返回值是 `Unit`，但它会更新消息状态；
- `←` 运行右侧计算并取出普通结果；
- `:=` 只给表达式起名，不会把 `M α` 变成 `α`。

随后给出教学数据流：

```text
读取当前 context/state
→ 运行第一步
→ 若失败则停止
→ 取得普通结果
→ 把更新后的 state 交给下一步
```

明确注明这不是 `StateRefT` 的定义展开，只是读 `do` 代码的工作模型。

### 4.3 为什么普通函数签名会越来越长

把命令内核先摊平成普通函数接口：

```text
file/ref/options/namespace/open declarations
→ environment/message/info/name state
→ Either Exception (Array Name × new state)
```

然后给真实定义：

```lean
CoreM :=
  ReaderT Core.Context <|
  StateRefT Core.State <|
  EIO Exception
```

逐层只解释本章已经遇到的需求：

- `ReaderT`：当前文件、源码位置、选项、namespace/open declarations；
- `StateRefT`：环境、消息、info tree、名字生成器和缓存；
- `EIO Exception`：异常和 IO；
- `α`：这次计算真正要返回的普通结果。

`pure`、`bind` 和 `do` 在这里讲完整：

- `pure` 把普通值放进当前计算层；
- `ma >>= f` 先运行 `ma`，再把结果与更新后的现场交给 `f`；
- `return a` 在尾位置是当前 monad 的 `pure a`；
- monad laws 简洁列出，用“重排 do 块为什么可以不改变含义”解释用途；
- 回滚不是第四条 monad law，后文单讲。

### 4.4 `Core.Context`：这次编译从哪里看世界

不把所有字段平铺成字典。先围绕名字解析解释四项：

- `currNamespace`；
- `openDecls`；
- `ref`；
- `options`。

再用一张完整字段表收束：文件与位置、资源限制、quotation/macro scope、diagnostics、cancellation 等字段各自解决什么问题。

核心例子：在不同 namespace/open 环境下解析同一个短名字，观察 `realizeGlobalConstWithInfos` 的结果；再说明 `withRef` 是对子计算临时换 context，不是永久修改 state。

### 4.5 `Core.State`：这次编译已经知道和做过什么

围绕主线依次介绍：

- `env`：查询声明；
- `messages`：记录输出和警告；
- `infoState`：使输入标识符可 hover/跳转；
- `ngen` / `auxDeclNGen` / `nextMacroScope`：生成不会冲突的名字；
- `cache`：缓存层级实例化；
- `traceState` / `snapshotTasks`：诊断与增量处理。

必须明确：`Environment` 位于 `Core.State`，不是 `Core.Context`。它虽然经常只读，但声明安装和环境扩展会产生新环境，后续计算必须看到更新。

### 4.6 公理依赖到底怎样算出来

先做一个只看直接依赖的小函数，让读者看见：

```lean
ConstantInfo
Expr.getUsedConstants
```

然后读 production `collectAxioms`：

```text
collectAxioms
→ getEnv
→ imported persistent extension lookup
→ CollectAxioms.runM
→ collectAndGet
→ collect
→ Environment.checked.get.find?
→ Expr.getUsedConstants
→ 递归闭包
```

需要详细解释：

1. `ConstantInfo` 不同构造子的 type/value/constructor 该怎样遍历；
2. 递归依赖图可能有环，因此先放 sentinel；
3. `seen` 同时承担 visited 和 cache；
4. 内部 `ReaderT Environment (StateM State)` 是算法自己的局部状态，不等于外围 `Core.State`；
5. imported declarations 使用 persistent environment extension 的预计算结果，避免跨模块反复展开 body；
6. 公理依赖为空不等于“声明没有任何依赖”，只表示传递闭包里没有 axiom。

这里是全章技术最深的一节，但要以一张三节点依赖图贯穿，避免直接把 150 行源码倾倒给读者。

### 4.7 名字解析不是查一张 `String → Declaration` 表

解剖：

```lean
realizeGlobalConstWithInfos :
  Syntax → Option Expr → CoreM (List Name)
```

讲清：

- 输入是带 source info 的 `Syntax`，不是裸 `String`；
- namespace 和 open declarations 影响候选；
- 一个表面名字可能有多个解析结果；
- 未知名和歧义名通过异常报告；
- 成功后写 info tree，所以编辑器知道输入标识符指向哪个声明。

这里承接 Ch02 Syntax：Syntax 保留源码位置的价值终于变得可见。

### 4.8 把 Core 内核接成一条真正的命令

到这里再正式介绍：

```lean
CommandElabM :=
  ReaderT Command.Context <|
  StateRefT Command.State <|
  EIO Exception
```

必须画成“兄弟栈”，而不是误画成 CoreM 的上层：

```text
                         CoreM
EIO Exception ← StateRefT ← ReaderT
                         CommandElabM
```

解释官方桥 `Command.liftCoreM`：从 command context/state 组装 Core context/state，运行 Core 计算，再把 env、messages、info、trace、name generators 和 snapshots 合并回来。

随后逐行实现 `#book_print axioms`：

```lean
syntax (name := bookPrintAxioms)
  "#book_print" "axioms" ident : command

@[command_elab bookPrintAxioms]
def elabBookPrintAxioms : CommandElab
  | `(#book_print axioms $id:ident) => withRef id do
      let constNames ← liftCoreM <| realizeGlobalConstWithInfos id
      for constName in constNames do
        let axs ← collectAxioms constName
        ...
  | _ => throwUnsupportedSyntax
```

正文不要把 CommandElabM 展开成第二章。只解释这次确实用到的四件事：

- command syntax；
- `CommandElab` 注册；
- `withRef`；
- `liftCoreM`。

### 4.9 为了真实，借一次 MetaM：可点击的输出名字

先用：

```lean
MessageData.ofName
```

得到语义完整但不可点击的结果。然后换成 production 使用的：

```lean
MessageData.ofConstName
```

追踪真实懒渲染边界：

```text
MessageData.ofConstName
→ lazy renderer
→ ppConstNameWithInfos
→ PPContext.runMetaM
```

本节只需要交代：

- 公理分析仍然是 Core/Environment 工作；
- MetaM 只负责在显示阶段根据环境和 pretty-printing context 生成带 hover/go-to-definition 的名字；
- 这不是“全章突然变成 MetaM”，也不需要提前解释局部上下文、元变量或定义等价；
- 完整 production behavior 比人为维持纯层次更重要，因此最终版本采用 `ofConstName`。

这正好给 Ch05 留下一个问题：`runMetaM` 中的 Meta context/state 究竟是什么？

### 4.10 Options 和消息状态：为什么同类警告只出现一次

使用真实：

```lean
checkExponent : Nat → Bool → CoreM Bool
```

数据流：

```text
getOptions
→ exponentiation.threshold.get
→ logMessageKind `unsafe.exponentiation`
→ 首次超限时 logWarning
→ 后续同类警告去重
```

可运行例应连续检查两个超阈值指数，再读取最终 message log，确认 warning 只有一个。

这节用来说明：

- options 是只读 context；
- message log 是可写 state；
- 同一个函数可以同时读取 context 和更新 state；
- 普通返回值 `Bool` 与状态变化是两条不同的信息通道。

### 4.11 Fresh names、save/restore 与“Monad 不自动回滚”

依次演示：

```lean
mkFreshUserName
Core.saveState
Core.SavedState.restore
Core.withRestoreOrSaveFull
```

必须准确写明：

- 连续调用 `mkFreshUserName` 得到不同 macro scopes；
- `Core.saveState` 保存 `SavedState`；
- 普通 `SavedState.restore` 只恢复 env、messages、infoState、snapshotTasks；
- 它不恢复所有 fresh-name counters；
- `withRestoreOrSaveFull` 的用途是完整增量状态重放；
- 外部 IO 不在这些恢复承诺之内；
- `do` 和 `bind` 只负责顺序组合，不自动撤销前一步。

这一节不写虚假的“失败后什么都会恢复”示意。

### 4.12 在 frontend 外运行 CoreM

作为选读节展示：

```lean
CoreM.run
CoreM.toIO
```

解释手工提供 `Core.Context` 和 `Core.State` 的成本，以及为什么正常扩展 Lean 命令时更适合让 CommandElabM 帮我们搭好现场。

可运行 probe 只需输出：

```text
axioms=[Classical.choice]
fresh-distinct=true
warnings=1
```

这节的目的不是鼓励所有人手造 context/state，而是让 `CoreM α` 的运行语义彻底落地。

### 4.13 常见失败与调试

至少覆盖：

1. 把短名字当裸 `Name`，绕过 namespace/open resolution；
2. 把 `Environment` 误说成 Reader context；
3. 用 `MessageData.ofConstName` 后仍声称整条路径绝不运行 MetaM；
4. 误以为 `SavedState.restore` 恢复所有 Core state；
5. 误以为恢复 monad state 会撤销 `IO.println` 或文件写入；
6. 把 command elaborator 当成 `CoreM` 的 transformer 上层；
7. 使用 lazy `MessageData` 时只检查构造点、不检查最终 renderer；
8. 递归依赖遍历不做 visited/cache，遇到 inductive/constructor 环路。

### 4.14 练习梯度

1. **热身**：给一个全局名字，打印 declaration kind。
2. **基础**：打印直接使用的常量集合，不求传递闭包。
3. **进阶**：实现 `#book_print axioms` 的 `ofName` 版本。
4. **进阶**：改成 `ofConstName`，比较输出是否可 hover/跳转，并说明新增的执行层。
5. **挑战**：实现 `#book_print modules`，把公理依赖映射到声明来源模块；明确它不是“最小 import”的完整求解器。
6. **调试题**：给一个错误的 save/restore 推断，让读者预测哪些字段会恢复。

不建议要求读者从头复刻 persistent environment extension。正文读懂 production 机制即可，练习重点放在消费现有 API 和边界判断。

## 四、API 详表

以下签名为教学签名：省略不影响本章理解的隐式宇宙和 typeclass 参数；正文第一次出现时用 `#check @name` 给出锁定版本的完整签名。

### 4.1 主线 API

| API | 教学签名 | 最高执行层 | 读取 | 写入 | 正文用途 | 来源 |
|---|---|---|---|---|---|---|
| `realizeGlobalConstWithInfos` | `Syntax → Option Expr → CoreM (List Name)` | CoreM | env、namespace、open declarations、ref | info tree | 把用户写的标识符解析成全名，并给输入加编辑器信息 | `Lean.Elab.InfoTree.Main` |
| `collectAxioms` | `[MonadEnv m] → Name → m (Array Name)` | `MonadEnv`，主线在 Core/Command 中运行 | env、persistent extension | 内部局部 cache | 求声明的传递公理依赖 | `Lean.Util.CollectAxioms` |
| `Expr.getUsedConstants` | `Expr → Array Name` | 纯函数 | Expr | 无 | 取得直接常量依赖 | `Lean.Expr` |
| `getEnv` | `[MonadEnv m] → m Environment` | 多态 | 当前环境 | 无 | 查询声明图 | `Lean.MonadEnv` |
| `Environment.find?` | `Environment → Name → Option ConstantInfo` | 纯函数 | environment | 无 | 查声明 | `Lean.Environment` |
| `logInfo` | `MessageData → m Unit` | 多态；本章在 Core/Command | options、ref | message log | 把结果送入 Lean 消息系统 | `Lean.Log` |
| `MessageData.ofName` | `Name → MessageData` | 纯构造 | Name | 无 | 无 MetaM 的普通名字输出 | `Lean.Message` |
| `MessageData.ofConstName` | `Name → Bool → MessageData` | 构造时纯；懒渲染时 MetaM | PP context、env、options | rich info | production 式可点击常量名 | `Lean.Message` |

### 4.2 Monad 与 context/state API

| API | 教学签名 | 读/写 | 应在何处讲 | 易错点 |
|---|---|---|---|---|
| `pure` | `α → M α` | 无新增效果 | 4.2–4.3 | 不是“执行并返回”，而是把普通值放入当前计算层 |
| `(>>=)` | `M α → (α → M β) → M β` | 顺序传递当前层效果 | 4.2–4.3 | 不自动提供 rollback |
| `read` | `ReaderT ρ m ρ` 的通用读取 | 读 context | 4.4 | 不应拿它直接猜当前是哪一层 Context |
| `get` / `set` / `modify` | state 接口 | 读写 state | 4.5 | `Core.State` 较大，别为一字段更新手拼整个结构 |
| `getOptions` | `m Options` | 读 context | 4.4、4.10 | options 不在 `Core.State` |
| `withOptions` | `(Options → Options) → m α → m α` | 临时改子计算 context | 4.4 | 子计算结束后恢复，不是永久 state mutation |
| `getRef` | `m Syntax` | 读 context | 4.4、4.8 | ref 是诊断位置，不是待处理 term 本身 |
| `withRef` | `Syntax → m α → m α` | 临时改 ref | 4.4、4.8 | scoped context change，不是 message state mutation |
| `modifyEnv` | `(Environment → Environment) → m Unit` | 写 environment state | 4.5 边界说明 | 更新 env 时 CoreM 还会清相关 cache |
| `liftM` / `MonadLift IO CoreM` | `IO α → CoreM α` | 外部 IO | 4.3、4.12 | monad state restore 不撤销 IO |

### 4.3 名字、消息与诊断 API

| API | 教学签名 | 作用 | 本章地位 |
|---|---|---|---|
| `mkFreshUserName` | `Name → CoreM Name` | 追加 fresh macro scope，生成不可冲突名字 | 状态 micro-case |
| `mkAuxDeclName` | `Name → m Name` | 生成持久 auxiliary declaration 名 | API 表和旁注，不展开主线 |
| `logWarning` | `MessageData → m Unit` | 在当前 ref 记录 warning | `checkExponent` 短例 |
| `logMessageKind` | `Name → CoreM Bool` | 记录消息种类并返回是否首次出现 | 警告去重关键点 |
| `checkExponent` | `Nat → Bool → CoreM Bool` | 读取阈值，必要时写一次 warning | Options/messages 主例 |
| `throwError` | message syntax/API | 构造带当前 ref 的 Lean 异常 | 名字解析失败与 command 错误 |
| `trace` / `MonadTrace` | 按 trace class 写 trace state | 可选诊断 | 只列 API；不扩成 trace 专题 |
| `getInfoState` / `modifyInfoState` | info-tree state access | 读写编辑器语义信息 | 名字解析节 |

### 4.4 状态保存与运行 API

| API | 教学签名 | 语义 | 本章必须强调 |
|---|---|---|---|
| `Core.saveState` | `CoreM Core.SavedState` | 捕获当前 Core saved state | 保存不等于已经恢复 |
| `Core.SavedState.restore` | `SavedState → CoreM Unit` | 选择性恢复 env/messages/info/snapshots | 不恢复所有 name counters/cache/trace 字段 |
| `Core.withRestoreOrSaveFull` | `Option (α × SavedState) → CoreM α → CoreM (α × SavedState)` | 为增量重用保存或完整重放状态 | 与普通 rollback 目的不同 |
| `(action : CoreM α).run` | `Context → State → EIO Exception (α × State)` | 显式运行 transformer stack | 把抽象类型落地 |
| `(action : CoreM α).toIO` | `Context → State → IO (α × State)` | 在 IO 中运行并转换 Lean exception | 选读 standalone probe |

### 4.5 CommandElabM 薄外壳 API

| API | 教学签名 | 作用 | 是否进入 MetaM |
|---|---|---|---|
| `CommandElabM` | `ReaderT Command.Context (StateRefT Command.State (EIO Exception))` | command 阶段的兄弟 monad stack | 否 |
| `CommandElab` | `Syntax → CommandElabM Unit` | command elaborator 的函数类型 | 否 |
| `syntax ... : command` | 句法注册 | 让 parser 识别新命令 | 否 |
| `@[command_elab name]` | elaborator 注册属性 | 把 syntax kind 接到实现 | 否 |
| `Command.liftCoreM` | `CoreM α → CommandElabM α` | 组装 Core context/state，运行后合并状态 | 否 |
| `throwUnsupportedSyntax` | command fallback signal | 当前 elaborator 不接此形状 | 否 |
| `MessageData.ofConstName` 的 renderer | `PPContext → Name → IO ...`，内部 `runMetaM` | 可点击常量名 | **是，但只在懒渲染阶段** |

## 五、`Core.Context` 字段详表

| 字段 | 含义 | 主线是否直接使用 | 教学处理 |
|---|---|---:|---|
| `fileName` | 当前文件名 | 间接 | 字段表解释 |
| `fileMap` | 字节位置到行列位置的映射 | 间接 | 诊断位置说明 |
| `options` | 当前 Lean 选项 | 是 | `checkExponent` 主讲 |
| `currRecDepth` / `maxRecDepth` | 当前/最大递归深度 | 否 | 资源限制旁注 |
| `ref` | 当前诊断关联的 Syntax | 是 | `withRef` 主讲 |
| `currNamespace` | 当前 namespace | 是 | 名字解析主讲 |
| `openDecls` | 当前 open declarations | 是 | 名字解析主讲 |
| `initHeartbeats` / `maxHeartbeats` | heartbeat 基准与上限 | 否 | 与取消一起短讲 |
| `quotContext` | quotation 的命名上下文 | 间接 | 承接宏章 |
| `currMacroScope` | 当前宏作用域 | 是 | fresh name 短例 |
| `diag` | diagnostics 开关缓存 | 否 | 字段表 |
| `cancelTk?` | 外部取消 token | 否 | 解释长任务为何可中断 |
| `suppressElabErrors` | 解析失败时抑制部分译补错误 | 否 | frontend 边界旁注 |
| `inheritedTraceOptions` | 继承的 trace 选项缓存 | 否 | trace 旁注 |

## 六、`Core.State` 字段详表

| 字段 | 含义 | 主线是否直接使用 | 恢复边界 |
|---|---|---:|---|
| `env` | 当前全局环境 | 是 | 普通 `SavedState.restore` 恢复 |
| `nextMacroScope` | 下一个宏作用域编号 | fresh 短例 | 普通 restore 不恢复 |
| `ngen` | fvar/mvar/lmvar 唯一名字生成器 | 短讲 | 普通 restore 不恢复 |
| `auxDeclNGen` | 持久辅助声明名字生成器 | 旁注 | 普通 restore 不恢复 |
| `traceState` | trace 信息 | 旁注 | 普通 restore 不恢复 |
| `cache` | universe level 实例化缓存 | 旁注 | env 修改时清空；普通 restore 不恢复 |
| `messages` | 消息日志 | 是 | 普通 restore 恢复 |
| `infoState` | 编辑器 info tree | 是 | 普通 restore 恢复 |
| `snapshotTasks` | 异步子任务快照 | 旁注 | 普通 restore 恢复 |

这里必须写一句防止读者形成错误规律：

> Context 不等于“永远不会变”，State 也不等于“异常时必然回滚”。Context 可以在子计算中临时替换；State 的恢复范围由具体保存/恢复 API 决定。

## 七、代码块与验证设计

### 7.1 代码块分类

所有代码块沿用项目现有 `:::codeBox`：

- `可运行`：进入 `examples/Examples/Ch04CoreM.lean`；
- `源码节选`：注明 Lean 4.32.2 路径和行号；
- `示意`：省略构造 context/state 或隐式参数；
- `伪代码`：只解释数据流；
- `练习·故意错误` / `练习模板`：按项目 Helper 现有标签。

若数个可运行块依赖前文定义，在第一块前明确说明它们位于同一文件，避免读者分别复制后得到 `unknown identifier`。

### 7.2 计划中的可运行观测点

| 编号 | 观测点 | 预期结果 |
|---|---|---|
| P1 | builtin `#print axioms Classical.choice` | 包含 `Classical.choice` |
| P2 | builtin `#print axioms Nat.add_comm` | 无公理依赖 |
| P3 | 自制 `#book_print axioms` | 与 builtin 语义结果一致 |
| P4 | namespace/open resolution | 短名解析为当前可见的完整声明名 |
| P5 | `MessageData.ofName` | 正确文字，无富 hover |
| P6 | `MessageData.ofConstName` | 正确文字，输出名可 hover/跳转 |
| P7 | 两次超阈值 `checkExponent` | 返回两次 `false`，同类 warning 仅一条 |
| P8 | 两次 `mkFreshUserName` | 擦除 scope 后同名，但内部 Name 不同 |
| P9 | save/restore probe | env/messages/info/snapshot 恢复；fresh counter 不按读者直觉回退 |
| P10 | standalone `(action : CoreM α).toIO` | 输出公理列表和 fresh-name 差异 |

### 7.3 验证门

实施后依次执行：

1. `lake build Examples.Ch04CoreM`；
2. `lake build LeanTacticBook.Ch04CoreM`；
3. 聚合模块构建；
4. `git diff --check`；
5. 检查每个 `源码节选` 的路径和行号仍对应 pinned source；
6. 运行 standalone probe；
7. 渲染 Ch04 HTML，检查 codeBox 类型、锚点和链接；
8. 对章节做技术审读与教学审读，分别处理；
9. 最终核对 API 表中的“最高执行层”与真实 reachable call path。

## 八、写作语气与现有章节的衔接

从现有 Ch02/Ch03 保留以下风格：

- 直接使用“你”“我们”，不写行政文档式被动句；
- 先给真实调用，再逐词、逐行解释；
- 真实 Lean/Mathlib 源码和自写代码并列；
- 遇到易错处明确说“为什么错”，不只给正确答案；
- 保留少量有技术功能的幽默，例如“`CoreM α` 不是一种神秘的 `α`，它只是还没跑”；
- 需要横向比较时才用表格。

同时修正现有早期章节中的若干表达习惯，不继续复制：

- 不写“让我们来看”“值得注意的是”“总而言之”；
- 不把每节末尾做成机械总结；
- 不把 parser、macro、elaborator 混称为“编译器一步做完”；
- 不用“美化的正则表达式”一类会造成错误心智模型的类比；
- 不把 API 清单放在动机之前；
- 不用未经编译的代码块冒充可运行例。

正文的解释密度以 Ch02 的逐词拆解和 Ch03 的真实源码分类为基线，但段落要比 Ch03 当前后半部更紧，避免同一判断在正文、表格和总结中重复三遍。

## 九、内容预算

建议正文规模：

- 约 9,000–13,000 个中文字符；
- 10–14 个一级节；
- 12–18 个可运行代码块；
- 5–8 个源码节选；
- 2 张架构图；
- 4–6 道练习。

不是硬上限。若完整解释 `collectAxioms` 的 persistent extension 需要更多篇幅，宁可增加一节，也不压成几句术语堆砌。

## 十、作者已拍板的写作取舍

### D1：章名

章名只用 `CoreM`，不加副标题。

### D2：开篇展示方式

先展示完整命令、输出和折叠后的实现骨架；随后逐节重建，到 4.8 再给完整代码。

### D3（已拍板）：最终版本采用 `MessageData.ofConstName`

采用 production 的可点击输出。正文用一小节如实标注 lazy renderer 借用了 MetaM，但不为了维持人为的“纯 CoreM”边界而降级成 `ofName`。`ofName` 只作为前一阶段的对照版本，让读者亲眼看到语义结果与 IDE 富信息是两层功能。

### D4：`collectAxioms` 内部讲到多深

完整讲递归、sentinel、cache、`ConstantInfo` 分支和 imported persistent extension，但不要求读者从头复刻 extension。

### D5：Monad laws 的篇幅

列出三条 law，解释它们为何允许重组 `do` 管线，并增加一个可运行的等价程序实验。实验应直接改写本章已有的小段计算，不另造与主线无关的抽象玩具。

### D6：是否保留 standalone `CoreM.toIO`

作为选读节保留。它回答“这个 monad 最后究竟怎样跑”；手造 context/state 的样板代码完整提供，但不要求初读者记忆。

### D7：章节中的第一人称密度

保留现有作者风格：关键取舍处使用“我这里选择……”，普通技术说明以“你”称读者；不在每节重复“我们”。

### D8：练习是否给完整答案

热身和基础练习在章末给答案；进阶和挑战题只给测试与提示，答案放 examples 中但正文不立即展开。

### D9：`elaboration` 的中文译名

统一使用“译补”，并把它作为本书今后的标准译名。首次出现写“译补（elaboration）”，API 名中的 `Elab` / `elab` 保持原样。

## 十一、实施任务顺序

- [x] `core-1` 冻结 D1–D9 风格取舍。
- [x] `core-2` 建立 `examples/Examples/Ch04CoreM.lean`，先让 P1–P10 全部可重复运行。
- [x] `core-3` 写 4.1–4.3：完成品、`CoreM α`、Monad 基础。
- [x] `core-4` 写 4.4–4.7：Context、State、`collectAxioms`、名字解析。
- [x] `core-5` 写 4.8–4.9：CommandElabM 薄外壳和 MetaM 富文本边界。
- [x] `core-6` 写 4.10–4.12：options/messages、fresh/restore、standalone runner。
- [x] `core-7` 写失败模式、练习和 API 表，并检查正文首次出现顺序。
- [x] `core-8` 局部构建、完整构建、源码引用核验。
- [x] `core-9` 技术 R1 修订及 R2 复审：ACCEPT。
- [x] `core-10` 教学 R1 重排及 R2 复审：ACCEPT。
- [x] `core-11` 渲染与 HTML 检查。

## 十二、完成标准

这一章完成不能只以“构建绿了”为准。必须同时满足：

- 读者能在普通 `.lean` 文件中运行自制命令；
- 自制命令与 builtin `#print axioms` 在选定测试声明上给出相同语义结果；
- 输入短名遵守 namespace/open declarations；
- 最终版输出名称使用 `MessageData.ofConstName`，具备 rich hover；
- `collectAxioms` 的 imported-extension 路线没有被误写成每次跨模块展开 body；
- CommandElabM 被画成 CoreM 的兄弟栈，而不是 transformer 上层；
- `MessageData.ofConstName` 的 deferred MetaM 边界已记账；
- `SavedState.restore` 的选择性恢复和 IO 非回滚边界写清；
- 所有可运行块进入 examples 模块并实际编译；
- API 表、正文和 pinned source 三者签名一致；
- 技术审读与教学审读均无 blocker。
