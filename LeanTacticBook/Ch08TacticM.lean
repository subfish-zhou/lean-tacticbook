import VersoManual
import LeanTacticBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "examples"
set_option verso.exampleModule "Examples.Ch08TacticM"

#doc (Manual) "TacticM：把证明洞排成工作队列" =>
%%%
file := "Ch08TacticM"
tag := "ch08-tacticm"
%%%

> *本章目标*：回答一个界面问题：`constructor` 把一个目标拆成两个以后，下一条证明术为什么先处理左边？我们先观察目标列表，再区分“洞有没有被填”和“哪些洞正排队等待”，最后由此理解 `apply`、`<;>` 与 `first`。
>
> *版本基准*：Lean `leanprover/lean4:v4.32.2`，Mathlib revision `905b95818eb3`。

# 概述：证明术在管理什么
%%%
tag := "ch08-overview"
file := "ch08-overview"
%%%

走到本章时，前面三层已经各自解决了一类问题。CoreM 保存文件级现场，MetaM 认识局部表达式和证明洞，TermElabM 把用户写下的项 Syntax 译补成 Expr。`by` 块还需要一层界面逻辑：上一条证明术可能产生零个、一个或多个新洞，下一条证明术应当从哪个洞继续，分支记号又该把哪段脚本交给哪组洞。

证明术的基本接口可以先读成：

:::codeBox "pseudocode"
```
一段 tactic Syntax
  + 当前活动目标的有序列表
        ↓ TacticM
修改证明洞的赋值
  + 更新下一步要处理的活动目标列表
```
:::

这里有两个容易混淆的状态。MetaM 的 metavariable context 记录一个洞是什么、有没有被赋值；TacticM 的 goal queue 记录当前脚本准备按什么顺序处理哪些洞。内核最终只检查各个洞组成的证明项，不关心用户当时先处理左边还是右边。目标队列属于证明术界面的调度状态，不是命题的组成部分。

本章会先观察队列，而不是立刻实现 `apply`。我们先确认 `constructor` 前后活动目标如何变化，再分别检查洞的赋值和队列的删改；随后学习 `getGoals`、`setGoals` 与 pruning。到这时，缩小版 `apply` 才有足够背景：MetaM 负责填旧洞并产生新洞，TacticM 负责把新洞排回队列。最后再讨论 `<;>`、`first`、focus 和失败回滚怎样组合这套调度。


先看一段普通证明：目标是 `P ∧ Q` 时，`constructor` 产生 `P` 和 `Q` 两个新目标。它们都是待填的证明洞，但用户随后总要按某种顺序处理。这个顺序既不是命题本身的一部分，也不参与内核检查；它是证明术界面的工作安排。

Lean 用一个有序列表保存“现在准备继续处理哪些洞”。本章把它叫作 active goal queue（活动目标队列）。列表元素是 `MVarId`，也就是 Ch06 中证明洞的内部编号。

# 第一个实验：`constructor` 前后有几个活动目标
%%%
tag := "ch08-s06"
%%%

观察用证明术 `queue_xray` 只做两件事：读取活动目标列表，并按次序打印每个洞的目标类型。第一遍无需关心循环写法。

```anchor tacticm_queue_xray
elab "queue_xray" : tactic => do
  let goals ← getGoals
  logInfo m!"active goals: {goals.length}"
  for h : i in [0:goals.length] do
    let g := goals[i]
    g.withContext do
      logInfo m!"goal {i + 1}:{indentExpr (← g.getType)}"
```

在 `constructor` 前后调用：

```anchor tacticm_queue_xray_use
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  queue_xray
  constructor
  queue_xray
  · exact hP
  · exact hQ
```

日志先显示一个目标 `P ∧ Q`，随后按顺序显示 `P`、`Q`。这个现象把问题拆成两半：旧洞怎样由两个新洞组成，以及两个新洞怎样进入活动队列。

# 洞的赋值与洞的排队是两件事
%%%
tag := "ch08-s03"
%%%

交互界面常把所有信息统称为 proof state（证明状态）。写元程序时必须把其中两层分开。Ch06 的 mctx 回答“每个洞是什么、有没有被填”；本章的 goal queue 回答“接下来按什么顺序处理哪些洞”。

## Meta.State.mctx
%%%
tag := "ch08-s04"
%%%

保存：

- 每个 MVarId 的类型；
- 创建时 local context；
- assignment；
- delayed assignments 等 Meta 信息。

## Tactic.State.goals
%%%
tag := "ch08-s05"
%%%

保存：

- 当前活动目标的有序列表；
- 下一条普通证明术默认处理队首；
- focus/combinator 怎样临时重排或分组。

因此，一个 MVarId 可以仍在 goals 中，却已经被赋值；也可以存在于 mctx，却不在当前活动队列中。前一种情况像“任务已经完成，但还没从待办列表划掉”；后一种情况表示系统知道这个洞，却没有把它交给当前 tactic 脚本处理。

# `TacticM` 只为这层调度增加很薄的现场
%%%
tag := "ch08-s02"
%%%

锁定版本中的定义为：

:::codeBox "code"
```
structure Tactic.Context where
  elaborator : Name
  recover    : Bool := true

structure Tactic.State where
  goals : List MVarId

abbrev TacticM :=
  ReaderT Tactic.Context <|
  StateRefT Tactic.State <|
  TermElabM

abbrev Tactic := Syntax → TacticM Unit
```
:::

`Tactic.State.goals` 正是刚才观察到的活动目标列表。`Tactic.Context` 另存当前证明术实现的名字和恢复策略；这些概念到 dispatcher 与失败分支处再解释。Environment、local context、mctx、synthetic metavariables、messages 和 exceptions 都由下层计算层继续承载。

# `getGoals`、`setGoals` 与 pruning
%%%
tag := "ch08-s07"
%%%

这里用到四个基础接口：

:::codeBox "code"
```
def getGoals : TacticM (List MVarId)
def setGoals : List MVarId → TacticM Unit
def pruneSolvedGoals : TacticM Unit
def getUnsolvedGoals : TacticM (List MVarId)
```
:::

`getGoals` 原样读取队列，可能包含已赋值目标。`getUnsolvedGoals` 会先调用 `pruneSolvedGoals`，滤掉 `MVarId.isAssigned` 返回 true 的目标。

本章故意写了一个只给目标赋值、不主动修改队列的证明术：

```anchor tacticm_prune_solved
elab "assign_without_pruning " t:term : tactic => withMainContext do
  let g ← getMainGoal
  let proof ← elabTermEnsuringType t (some (← g.getType))
  g.assign proof
  logInfo m!"goal queue length immediately after assignment: {(← getGoals).length}"

example (P : Prop) (h : P) : P := by
  assign_without_pruning h
-- Tactic framework prunes solved goals when the block finishes.
```

赋值后立即读取 `getGoals`，长度仍为一。证明术块收尾时，框架才会 prune solved goals：

:::codeBox "pseudocode"
```
给 mvar 赋值
≠
从 Tactic.State.goals 中立即删除它
```
:::

Lean 自带的证明术通常同时维护 mctx 和目标队列，免得后续代码继续处理已经解决的目标。

# 把两层变化合起来：缩小版 `apply`
%%%
tag := "ch08-s01"
%%%

现在才实现 `book_apply`。它必须同时完成两件事：在 mctx 中用一个 theorem application 填旧洞，并把 theorem 尚缺的参数洞放进活动目标队列。

```anchor tacticm_book_apply
elab "book_apply " t:term : tactic => withMainContext do
  let mut theoremExpr ← instantiateMVars (← elabTermForApply t)
  if theoremExpr.isMVar then
    Term.synthesizeSyntheticMVarsNoPostponing
    theoremExpr ← instantiateMVars theoremExpr
  let newGoals ← (← getMainGoal).apply theoremExpr
  Term.synthesizeSyntheticMVarsNoPostponing
  replaceMainGoal newGoals
```

```anchor tacticm_book_apply_use
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  book_apply And.intro
  case left => exact hP
  case right => exact hQ

example (P Q : Prop) (hP : P) : P ∨ Q := by
  book_apply Or.inl
  exact hP
```

调用 `And.intro` 后，旧目标获得形如 `And.intro ?left ?right` 的赋值；两个问号对应的新洞则按 `[left, right]` 进入活动队列。旧洞的证明结构与新洞的工作顺序由此同时更新。

把代码按刚才的两层分组：

:::codeBox "pseudocode"
```
准备 theorem：Syntax → theorem Expr
→ Meta 层：填旧洞，并返回尚未填的参数洞
→ Tactic 层：用这些参数洞替换队首目标
→ 后续证明术按新队列继续
```
:::

# `elabTermForApply` 为何不同
%%%
tag := "ch08-s08"
%%%

普通 term 译补会积极插入隐式参数。`apply` 希望 Meta apply 自己创建这些参数洞，再根据目标结论统一。当输入只是标识符 `f` 时，`elabTermForApply` 尽量返回接近 `@f` 的 Expr，而不提前插入所有隐式参数。

某些参数只能从 apply 的目标中确定。若 term elaborator 过早创建并锁定参数结构，Meta apply 就无法再用目标约束这些参数。

`elabTermForApply` 的数据流：

:::codeBox "pseudocode"
```
若 Syntax 是 identifier
  → resolveId?，直接取得 declaration Expr
否则
  → elabTerm stx none
```
:::

这里故意不给预期类型。结论与目标的统一发生在下一步。

# Postponed term 的强制处理
%%%
tag := "ch08-s09"
%%%

某些 notation 需要预期类型，例如用户写下 `.inl`。apply 风格的译补没有直接提供预期类型，可能暂时返回 metavariable。Lean 自带的 `evalApplyLikeTactic` 会检查：

:::codeBox "pseudocode"
```
若 val 仍是 metavariable
→ synthesizeSyntheticMVarsNoPostponing
→ instantiateMVars val
```
:::

这一步要求所有延期任务立即处理，因而要么得到完整的 theorem Expr，要么给出更准确的错误。Meta apply 后再次调用 synthesis，处理应用过程中出现的 instance 与 synthetic constraints。

# `MVarId.apply` 修改了什么
%%%
tag := "ch08-s10"
%%%

设目标为 `P ∧ Q`，theorem Expr 为 `And.intro`。它的类型可读成：

:::codeBox "code"
```
∀ {a b : Prop}, a → b → a ∧ b
```
:::

Meta apply：

1. 为隐式命题参数和证明参数创建 metavariables；
2. 将结论 `?a ∧ ?b` 与目标 `P ∧ Q` 统一；
3. 得到 `?a := P`、`?b := Q`；
4. 给旧目标赋值 `And.intro ?hP ?hQ`；
5. 返回尚未赋值的 `?hP : P` 与 `?hQ : Q`。

mctx 的变化是：

:::codeBox "pseudocode"
```
?old : P ∧ Q
?old := And.intro ?left ?right
?left  : P
?right : Q
```
:::

返回的 `List MVarId` 是下一批待处理目标，但此时还没有写入 Tactic.State。

# `replaceMainGoal` 的队列政策
%%%
tag := "ch08-s11"
%%%

Lean 自带的 `apply` 最后执行：

:::codeBox "code"
```
replaceMainGoal newGoals
```
:::

若当前队列为：

:::codeBox "pseudocode"
```
[old, rest₁, rest₂]
```
:::

替换后成为：

:::codeBox "pseudocode"
```
[new₁, new₂, rest₁, rest₂]
```
:::

Meta apply 只产生新洞；Tactic 前端决定如何把它们装入队列。证明术可以把新目标逆序放入队列、延后某类 side goal，也可以只聚焦其中一项。这些选择会直接改变用户随后看到的目标顺序。

# `<;>` 为什么会在每个新目标上各运行一次
%%%
tag := "ch08-s12"
%%%

`<;>` 是 tactic combinator（证明术组合符）：它把左、右两段证明术组合成一种调度方式。下面在右侧调用 `queue_xray`：

```anchor tacticm_focus_sequence
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor <;> queue_xray
  · exact hP
  · exact hQ
```

虽然 `constructor` 产生两个目标，每次日志只看到一个。`<;>` 的行为可以概括为：

:::codeBox "pseudocode"
```
运行左侧 tactic，得到 [g₁, g₂]
→ focus g₁，在 singleton queue [g₁] 上运行右侧
→ 收集 g₁ 产生的剩余目标
→ focus g₂，在 singleton queue [g₂] 上运行右侧
→ 按次序拼接各分支剩余目标
```
:::

所以 `<;>` 不是简单地先运行 `tac1`、再运行一次 `tac2`。它会在左侧产生的每个新目标上分别运行右侧证明术，而右侧每次只看到当前聚焦的 singleton queue。

在 Lean 4.32.2 中，`<;>` 是 macro，真实展开还保留 tactic-state annotation：

:::codeBox "code"
```
focus
  lhs
  with_annotate_state token skip
  all_goals rhs
```
:::

`all_goals` 逐个建立 singleton queue，并按原目标顺序拼接各次运行留下的 residual goals。上图只概括这套执行顺序；`<;>` 并不是由某个独立的 `seqFocus` elaborator 实现的。

# 同一种 tactic Syntax 可能有多个处理者
%%%
tag := "ch08-s13"
%%%

parser 为 tactic Syntax 标出 kind，多个 tactic elaborator 可以注册到同一个 kind。`evalTactic` 是选择处理者并运行它的 dispatcher（分派器）。它会：

1. 检查 syntax node kind；
2. 查询该 kind 注册的 macros 与 tactic elaborators；
3. 保存 Tactic saved state；
4. 依次尝试 macro expansion 与 elaborators；
5. 记录 before/after tactic info；
6. 处理 unsupported、普通错误和 recovery；
7. 递归执行 macro 展开的 nested tactic Syntax。

下面为同一个 syntax kind 注册两个 elaborator。在本书锁定的版本中，dispatcher 按注册顺序从后向前尝试。因此先注册 accepting 实现，再注册 declining 实现。后注册的 declining 实现先抛出 unsupported；dispatcher 恢复 saved state 后，再由 accepting 实现接管。

```anchor tacticm_dispatch_fallback
syntax (name := bookFallback) "book_fallback" : tactic

@[tactic bookFallback]
def acceptingBookFallback : Tactic := fun _ => do
  unless (← getGoals).length = 1 do
    throwError "dispatcher did not restore the goal queue"
  if ← (← getMainGoal).isAssigned then
    throwError "dispatcher did not restore the metavariable assignment"
  logInfo "the accepting elaborator ran after fallback"
  evalTactic (← `(tactic| trivial))

@[tactic bookFallback]
def decliningBookFallback : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  g.assign (← mkLabeledSorry (← g.getType) (synthetic := true) (unique := true))
  setGoals []
  throwUnsupportedSyntax

example : True := by
  book_fallback
```

unsupported 表示“这个实现不处理该语法”，dispatcher 恢复状态并尝试下一项。普通错误表示该实现已经接管，但执行失败；是否继续尝试受 fallback 属性和控制路径影响。

# Tactic.Context.elaborator
%%%
tag := "ch08-s14"
%%%

`evalTactic` 进入某个实现时，把该 tactic elaborator 的声明名写入 `Tactic.Context.elaborator`。info tree 因而可以记下修改目标的是哪个 elaborator，错误消息、trace 和编辑器也能借这个名称定位执行者。

这个字段属于 Reader context：嵌套动作可以临时替换它，退出嵌套范围后便恢复。它与 theorem 所在环境中的声明状态无关。

# 出错后是失败，还是用占位项继续
%%%
tag := "ch08-s15"
%%%

交互编辑时，Lean 有时会在错误后放入占位证明，继续处理后面的代码，以便一次显示更多诊断。这项选择叫 recovery policy（恢复策略），由 `Tactic.Context.recover` 控制。它服务于错误恢复，不表示证明已经成功。

`withoutRecover tac` 临时关闭这种策略。搜索 combinator 需要候选真正失败，不能让候选用 sorry 恢复后被误判为成功。Lean 自带的 `first` 用 `<|>` 逐个尝试候选，并在这条路径上关闭 recovery。

`evalApplyLikeTactic` 不会自行关闭 recovery；它通过 `runTermElab`，沿用外层 `Tactic.Context.recover` 的设置。

判断一条证明术是否成功，不能只看它有没有抛异常。还要分别检查：

- 目标 mvar 是否获得普通 proof assignment；
- 是否出现 synthetic sorry；
- 队列是否为空；
- 消息系统中是否仍有 error。

# `first` 为什么必须撤销失败候选留下的两层变化
%%%
tag := "ch08-s16"
%%%

`first | t₁ | t₂` 的意思是依次尝试候选，采用第一个成功者。若 `t₁` 先填了洞、改了队列，随后才失败，`t₂` 就必须从尝试前的现场开始。下面故意让第一分支污染两层状态：它先给主目标赋 synthetic sorry，再清空活动队列，最后抛异常。

```anchor tacticm_dirty_failure
elab "assign_then_fail" : tactic => withMainContext do
  let g ← getMainGoal
  let target ← g.getType
  g.assign (← mkLabeledSorry target (synthetic := true) (unique := true))
  setGoals []
  logInfo "the failing branch changed mctx and emptied the goal queue"
  throwError "intentional failure after changing both states"

elab "assert_main_unassigned" : tactic => do
  unless (← getGoals).length = 1 do
    throwError "the activity queue was not restored"
  let assigned ← (← getMainGoal).isAssigned
  if assigned then
    throwError "the main goal is still assigned"
  logInfo "the restored main goal is unassigned"
```

随后交给 `first`：

```anchor tacticm_first_restore
example (P : Prop) (h : P) : P := by
  first
  | assign_then_fail
  | assert_main_unassigned
    exact h
```

第二分支先核对队列长度，再打印“restored main goal is unassigned”。这说明原来的活动目标队列和 mctx 中的赋值状态都已恢复。若只恢复 `Tactic.State.goals`，队列中的旧 MVarId 仍会指向已赋值目标；若只恢复 mctx，队列仍为空。

因此，`Tactic.SavedState` 至少由两部分组成：

:::codeBox "code"
```
structure Tactic.SavedState where
  term   : Term.SavedState
  tactic : Tactic.State
```
:::

其中，Term saved state 保存 Meta state、synthetic tasks 以及 TermElabM 下层的状态。`SavedState.restore` 先恢复 term 部分，再恢复 goal queue。

# 两种 `try/catch` 的回滚差异
%%%
tag := "ch08-s17"
%%%

在 Lean 4.32.2 的 TacticM 中，普通 `try ... catch ...` 使用可回溯的 `MonadExcept` 实例。分支抛出异常时，它会恢复 `Tactic.SavedState`；Term/Meta 状态和活动目标队列都在恢复范围内。

`first` 用 `<|>` 串接候选，也沿用这套可回溯的异常与 Alternative 语义。因此，`evalFirst` 不必另写保存恢复循环。

Tactic 命名空间里还有一个同名易混的 `Tactic.tryCatch`。这个函数不回溯，失败分支对 mctx 和目标队列的修改可以保留下来。读源码时要看清：调用的是普通 `try/catch` 语法，还是 `Tactic.tryCatch` 函数。

后面的自动化实现会反复遇到同一区别：

- Library Search 的候选边界保存 Meta state，用于撤销“统一成功、后续失败”的赋值；
- Grind 的 split branch 使用自己的分支状态协议；
- term elaborator fallback 恢复可回溯的 Term/Meta state，同时按 API 规定保留部分 trace/info。

# Goal tags
%%%
tag := "ch08-s18"
%%%

新目标可以带 tag，帮助用户识别分支。`constructor` 创建的合取目标通常标作 `left` 和 `right`：

```anchor tacticm_goal_tags
elab "show_goal_tags" : tactic => do
  for g in (← getGoals) do
    logInfo m!"goal tag: {← g.getTag}"

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  show_goal_tags
  · exact hP
  · exact hQ
```

tag 不参与 kernel 判断，却影响 case syntax、错误显示和交互脚本。Meta 变换创建子目标时要继承或追加 parent tag，避免复杂证明中的分支名称丢失。

# Tactic info 与增量编辑
%%%
tag := "ch08-s19"
%%%

`mkTacticInfo` 记录：

- elaborator；
- mctx before/after；
- goals before/after；
- 原 tactic Syntax。

编辑器据此显示 tactic state、跳转和增量结果。info tree 不参与证明正确性，它记录每段 Syntax 执行前后的界面信息。恢复 proof state 时是否恢复 info，要由调用者另行选择。

# 生产 `apply` 对照
%%%
tag := "ch08-s20"
%%%

Lean 自带的实现可以写成下面这段骨架：

:::codeBox "code"
```
def evalApplyLikeTactic
    (tac : MVarId → Expr → MetaM (List MVarId))
    (e : Syntax) : TacticM Unit := do
  withMainContext do
    let mut val ← instantiateMVars (← elabTermForApply e)
    if val.isMVar then
      Term.synthesizeSyntheticMVarsNoPostponing
      val ← instantiateMVars val
    let newGoals ← tac (← getMainGoal) val
    Term.synthesizeSyntheticMVarsNoPostponing
    replaceMainGoal newGoals
```
:::

`book_apply` 保留了这条骨架。Lean 自带的 `evalApply` 还会把用户 term 作为 message data 传给 Meta apply，用来生成更具体的 diagnostics。

# 源码地图
%%%
tag := "ch08-s21"
%%%

建议先按下面的顺序阅读源码：

:::codeBox "pseudocode"
```
Lean/Elab/Term/TermElabM.lean
  Tactic.State / Tactic.SavedState
→ Lean/Elab/Tactic/Basic.lean
  Context / TacticM
  getGoals / setGoals / pruneSolvedGoals
  saveState / restore
  evalTactic
→ Lean/Elab/Tactic/ElabTerm.lean
  elabTermForApply
  evalApplyLikeTactic
  evalApply / evalConstructor
→ Lean/Meta/Tactic/Apply.lean
  MVarId.apply
→ tactic combinator 源码
  first / focus / all_goals / <;>
→ InfoTree 与 TacticInfo
```
:::

第一遍沿 `apply And.intro` 追到底。第二遍再读 dispatcher fallback 和 `first` 的 saved-state 控制。

# API 回查表
%%%
tag := "ch08-s22"
%%%

| 任务 | 入口 |
|---|---|
| 取得活动目标 | `getGoals` |
| 取得队首目标 | `getMainGoal` |
| 替换完整队列 | `setGoals` |
| 替换队首 | `replaceMainGoal` |
| 过滤已赋值目标 | `pruneSolvedGoals` |
| 在主目标上下文运行 | `withMainContext` |
| apply 风格译补 | `elabTermForApply` |
| Meta 应用 theorem | `MVarId.apply` |
| 强制处理 synthetics | `Term.synthesizeSyntheticMVarsNoPostponing` |
| 执行 nested tactic | `evalTactic` |
| 保存完整 tactic state | `Tactic.saveState` |
| 恢复 state | `Tactic.SavedState.restore` |
| 暂停 recovery | `withoutRecover` |
| 读取 goal tag | `MVarId.getTag` |

# 练习
%%%
tag := "ch08-s23"
%%%

## 基础一：两个状态
%%%
tag := "ch08-s24"
%%%

`MVarId.apply` 成功返回 `[g₁, g₂]` 后，若调用者没有 `replaceMainGoal`，发生了什么？

*答案*：旧目标已在 mctx 中赋值，新 metavariables 也已创建；Tactic goal queue 仍保留原列表。后续框架若 prune，会移除已赋值旧目标，但新洞未必进入活动队列。

## 基础二：为何 `getGoals` 可能含 solved goal
%%%
tag := "ch08-s25"
%%%

为什么 `getGoals` 可能返回已经赋值的目标？

*答案*：给 mvar 赋值只修改 mctx。过滤属于 `pruneSolvedGoals`，不会在每次 assignment 后自动运行。

## 基础三：`<;>` 右侧看见几个目标
%%%
tag := "ch08-s26"
%%%

`constructor <;> queue_xray` 中，每次 `queue_xray` 会看见几个目标？

*答案*：每次看见一个聚焦目标。combinator 对左侧产生的每个目标分别建立 singleton queue，运行右侧后再拼接结果。

## 进阶一：逆序 apply
%%%
tag := "ch08-s27"
%%%

实现 `book_apply_reverse`，把 `MVarId.apply` 返回的新目标按逆序放入队列。

*测试*：`And.intro` 后先显示 `Q`，再显示 `P`；旧目标 proof assignment 仍是同一结构。

## 进阶二：保留其他目标
%%%
tag := "ch08-s28"
%%%

在已有三个活动目标的状态下，只对队首运行 Meta 变换，证明 `replaceMainGoal` 保留尾部目标次序。

*提示*：用 `constructor` 与 `all_goals` 构造受控队列，并在每一步打印类型。

## 进阶三：错误的回滚器
%%%
tag := "ch08-s29"
%%%

写一个只保存/恢复 `Tactic.State.goals` 的候选 combinator，再运行 `assign_then_fail`。捕获异常时显式调用非回溯的 `Tactic.tryCatch`；若写普通 `try/catch`，TacticM 的 backtracking 实例已经替你恢复完整 saved state，实验便失去对照。

*测试*：恢复后的队列看似相同，但队首 MVarId 已在 mctx 中赋值。随后比较完整 `Tactic.saveState` 的结果。

## 进阶四：dispatcher fallback
%%%
tag := "ch08-s30"
%%%

为同一 syntax kind 注册三个 elaborator：第一个 unsupported，第二个先改状态再失败，第三个成功。检查第三个开始时两层状态都已恢复。

## 挑战：实现 `book_all_goals`
%%%
tag := "ch08-s31"
%%%

`<;>` 的右半段依赖 `all_goals`。下面的教学实现保存原队列，逐个建立 singleton queue，运行参数 tactic，再按原顺序拼接 residual goals。循环使用非回溯的 `Tactic.tryCatch`；分支失败时，代码显式恢复 `Tactic.SavedState`，然后重新抛出异常。

```anchor tacticm_book_all_goals
syntax "book_all_goals " tacticSeq : tactic

elab_rules : tactic
  | `(tactic| book_all_goals $seq:tacticSeq) => do
      let saved ← saveState
      Tactic.tryCatch
        (do
          let original ← getGoals
          let mut residual := []
          for g in original do
            setGoals [g]
            evalTactic seq
            residual := residual ++ (← getGoals)
          setGoals residual)
        (fun e => do
          saved.restore
          throw e)

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  book_all_goals assumption
```

完整 `<;>` 还需先执行左 tactic，并保留 `with_annotate_state` 的增量编辑信息。进阶实现可在此版本外再加左参数和 goal-tag 回归测试。

# 四层工作现场总图
%%%
tag := "ch08-s32"
%%%

四层现场可以合在一张图里：

:::codeBox "pseudocode"
```
CoreM
  Environment / Options / messages / source refs / exceptions

MetaM
  + LocalContext / MetavarContext / defeq / proof construction

TermElabM
  + expected type / synthetics / postponement / term recovery

TacticM
  + current elaborator / recovery policy / ordered active goals
```
:::

`apply` 会经过这四层。tactic dispatcher 先接收 Syntax；TermElabM 把 theorem term 译补成 Expr；MetaM 负责目标统一和 proof assignment；TacticM 再更新活动目标队列。Environment、messages 和 exceptions 则一直由底层 CoreM 承载。

# 本章边界
%%%
tag := "ch08-s33"
%%%

现在可以分别定位 proof Expr、metavariable assignment、synthetic recovery 和 active goal queue。下一组章节进入成熟自动化：先从 `exact?` 看全库候选索引与搜索，再依次研究规范化、证书、饱和推理和外部求解器的信任链。
