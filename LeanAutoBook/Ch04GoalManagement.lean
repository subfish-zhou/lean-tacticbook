import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch04GoalManagement"

#doc (Manual) "目标管理" =>
%%%
file := "Ch04GoalManagement"
tag := "ch04-goal-management"
%%%

*本章目标*：掌握多目标操作、目标聚焦、保存/恢复状态、`try`/`catch` 回溯，以及常见的失败模式与调试手段。

# 回顾与导引
%%%
tag := "recap-and-intro"
%%%

在第三章中，你学会了 tactic 的基本写法：如何用 `elab` 声明一个 tactic，如何通过 `getMainGoal` 获取当前目标，如何用 `Expr` 构造证明项，最终通过 `MVarId.assign` 把证明项赋给目标元变量。那些例子都有一个共同特征——*自始至终只有一个目标*。

但现实中，很多 tactic 会把一个目标拆成多个子目标。比如 `constructor` 会把 `⊢ A ∧ B` 拆成 `⊢ A` 和 `⊢ B` 两个子目标；`induction` 会为每个构造子生成一个子目标。一旦出现多个目标，你的 tactic 就必须回答以下问题：

- 哪个目标是"主目标"？其余目标怎么办？
- 处理完主目标后，新产生的子目标放在列表的什么位置？
- 如果想对某个子目标单独操作、其余目标暂时隐藏，该怎么做？
- 如果一次尝试失败了，怎么把状态回退到尝试之前？

本章就来回答这些问题。你将看到 Lean 4 的 tactic 框架把目标管理的复杂性压缩到了一组简洁的 API 里——但"简洁"不等于"不会出错"。理解这些 API 的语义细节，是写出健壮 tactic 的关键。

# 4.1 多目标的心智模型
%%%
tag := "multi-goal-mental-model"
%%%

`TacticM` 的核心状态之一是 `goals : List MVarId`——一个有序的元变量 ID 列表。你可以把它理解为 tactic 的"待办事项清单"。每个 `MVarId` 代表一个尚未填入证明项的"洞"，而列表的顺序决定了 tactic 的行为。

几个关键规则：

*顺序有意义。* 列表的第一个元素是"主目标"（main goal），也就是 `getMainGoal` 返回的那个。当用户在 Lean InfoView 中看到的"当前目标"，就是这个主目标。顺序不仅影响显示，还影响 tactic 的执行——大多数 tactic 默认只操作主目标。

*tactic 默认只操作主目标。* 当你调用 `assumption`、`exact`、`apply` 等内置 tactic 时，它们会取出主目标进行处理。如果主目标被解决了，它从列表中移除，下一个目标自然成为新的主目标。如果 `apply` 产生了新的子目标，这些子目标会被放到列表的前面，这样用户接下来就会先看到并处理这些新产生的子目标。

*`<;>` 对所有子目标执行。* 比如 `constructor <;> simp` 的语义是：先执行 `constructor`（可能产生多个子目标），然后对 `constructor` 产生的 *每一个* 子目标都执行 `simp`。这是一个广播操作符，在组合 tactic 时非常方便。

*目标列表可能包含已解决的目标。* 当某个 `MVarId` 已经被赋值（`isAssigned` 返回 `true`），它实际上已经解决了，但它可能还留在 `goals` 列表里。这就是为什么你经常需要调用 `getUnsolvedGoals` 而不是 `getGoals`——前者会帮你过滤掉已经赋值的元变量。

# 4.2 目标列表操作
%%%
tag := "goal-list-operations"
%%%

## 基本 API
%%%
tag := "basic-api"
%%%

```
-- [示意]
getGoals : TacticM (List MVarId)            -- 获取全部目标（含可能已解决的）
setGoals (gs : List MVarId) : TacticM Unit  -- 设置全部目标
getMainGoal : TacticM MVarId                -- 获取第一个目标（主目标）
getUnsolvedGoals : TacticM (List MVarId)    -- 过滤掉已赋值的目标
```

`getGoals` 和 `setGoals` 是最底层的操作——它们直接读写 tactic state 中的目标列表，不做任何过滤或检查。`getMainGoal` 则是 `getGoals` 的便利包装：它取出列表的第一个元素，如果列表为空就抛出 "no goals" 错误。

`getUnsolvedGoals` 值得特别关注。它不仅获取目标列表，还会对每个目标调用 `MVarId.isAssigned`，只保留尚未赋值的目标。这在你处理完一批目标后特别有用——你不需要手动追踪哪些目标已经被解决，只需在最后调用 `getUnsolvedGoals` 就能得到干净的列表。

## 常见模式
%%%
tag := "common-patterns"
%%%

```
-- [示意]
-- 模式 1（推荐）：用 replaceMainGoal 替换主目标
elab "my_tactic" : tactic => do
  let goal ← getMainGoal
  -- ... 处理 goal，产生 newGoals ...
  replaceMainGoal newGoals
```

模式 1 是最常见的 tactic 结构。`replaceMainGoal newGoals` 会把主目标从列表中移除，并把 `newGoals` 插到列表前面、其余目标保留在后面。这遵循了 Lean 的惯例：*新子目标总是排在前面*，这样用户会按"深度优先"的顺序处理它们。

*为什么推荐 `replaceMainGoal`？* 它在内部完成了"取出其余目标、拼接新目标"的逻辑，等价于：

```
-- [示意]
-- replaceMainGoal 的等价手写版（不推荐，仅供理解）
let rest := (← getGoals).erase goal
setGoals (newGoals ++ rest)
```

直接用 `replaceMainGoal` 更简洁、不容易出错，应作为模式 1 的首选写法。

```
-- [示意]
-- 模式 2：处理所有目标
elab "my_tactic_all" : tactic => do
  let goals ← getGoals
  let mut remaining := []
  for g in goals do
    -- ... 尝试处理 g ...
    if !(← g.isAssigned) then
      remaining := remaining ++ [g]
  setGoals remaining
```

模式 2 遍历所有目标并逐一处理。在循环结束后，用 `isAssigned` 过滤掉已解决的目标。这里有一个微妙之处：处理某个目标时可能会*间接影响其他目标*，比如 unification 可能会把两个目标中共享的元变量统一起来。所以即使你没有显式处理某个目标，它也可能在循环中途变成"已解决"的。

```
-- [示意]
-- 模式 3：交换目标顺序
elab "swap" : tactic => do
  let goals ← getGoals
  match goals with
- g1 :: g2 :: rest => setGoals (g2 :: g1 :: rest)：_ => throwError "swap requires at least 2 goals"
```

模式 3 展示了目标列表操作的灵活性：你可以任意重新排列目标的顺序。实际上 Lean 内置的 `rotate_left`、`rotate_right`、`swap` 等 tactic 就是这样实现的——纯粹的列表操作，不涉及任何证明项的构造。

# 4.3 聚焦（Focus）
%%%
tag := "focus"
%%%

当你的 tactic 只关心主目标、不想被其他目标干扰时，`focus` 是标准工具。它的语义可以用下面的简化实现来理解：

> *注意*：以下伪代码*仅用于帮助理解 `focus` 的语义*，不是推荐的实现模板。在实际代码中直接调用 `Lean.Elab.Tactic.focus` 即可，不需要手写这段逻辑。

```
-- [伪代码]
-- 简化示意，帮助理解 focus 的语义（不是推荐模板）
def focus (tac : TacticM Unit) : TacticM Unit := do
  let goals ← getGoals
  match goals with
- [] => throwError "no goals"：main :: rest =>
    setGoals [main]        -- 暂时隐藏其余目标
    tac                     -- 执行 tactic，它只能看到 main
    let newGoals ← getGoals -- tac 可能解决了 main，也可能产生了新子目标
    setGoals (newGoals ++ rest)  -- 把其余目标拼回来
```

这个伪代码揭示了 `focus` 的本质：它在执行 `tac` 之前，把 `rest` 从目标列表中"摘走"，执行完再"拼回来"。这意味着 `tac` 内部调用 `getGoals` 只会看到与 `main` 相关的目标（`main` 本身，以及 `tac` 新产生的子目标）。

这为什么有用？考虑一个场景：你正在写一个 tactic，它先调用 `cases`，然后对产生的每个子目标做一些处理。如果没有 `focus`，`cases` 产生的子目标会和原来就有的其他目标混在一起，你很难区分哪些是 `cases` 新产生的、哪些是之前就存在的。用 `focus` 包一下，`cases` 产生的子目标就是 `getGoals` 返回的全部——干净利落。

在你自己的 tactic 中使用 `focus`：

```
-- [示意]
elab "my_focused_tactic" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    Lean.Elab.Tactic.focus do
      -- 这里只能看到一个目标（主目标）
      let target ← (← getMainGoal).getType
      -- ... 对 target 做分析和处理 ...
```

注意 `focus` 和 `withContext` 经常一起出现：`focus` 确保目标列表的隔离，`withContext` 确保局部上下文的正确性。两者解决的是不同维度的问题，不能互相替代。

# 4.4 保存与恢复状态
%%%
tag := "save-restore-state"
%%%

有时你想"先试一个策略，如果失败就回退到试之前的状态，换一个策略再试"。这种试探性执行（speculative execution）是很多自动化 tactic 的核心模式。Lean 提供了 `saveState` 和 `restoreState` 来支持这种模式。

## 基本用法
%%%
tag := "save-restore-basic-usage"
%%%

```
-- [示意]
elab "try_or_skip" : tactic => do
  let state ← saveState
  try
    evalTactic (← `(tactic| assumption))
  catch _ =>
    restoreState state
    -- assumption 失败了，恢复状态，什么都不做
```

这里的流程是：先把当前完整状态保存到 `state`，然后尝试执行 `assumption`。如果 `assumption` 成功，皆大欢喜，`state` 就被丢弃了。如果 `assumption` 抛出异常（说明它无法解决当前目标），`catch` 会捕获异常，调用 `restoreState state` 回退到尝试之前的状态。

## `saveState` 保存了什么？
%%%
tag := "what-savestate-saves"
%%%

`saveState` 保存的是*完整的 `Meta.State` 和 `Core.State`*，其中最重要的部分是 `MetavarContext`——它记录了所有元变量的赋值情况以及 universe 约束。这意味着 `restoreState` 不仅会回退目标列表，还会撤销所有 unification 产生的副作用。

为什么这很重要？因为 tactic 执行过程中，`apply` 或 `unify` 可能会给一些元变量赋值，而这些元变量可能不仅仅属于当前目标——它们可能是多个目标共享的。如果你只回退目标列表而不回退 `MetavarContext`，那些共享的元变量就会残留着"试探性赋值"，导致后续的 tactic 行为异常。`restoreState` 通过一次性回退整个状态来避免这个问题。

## 更高层的封装：`tryTactic?`
%%%
tag := "try-tactic-wrapper"
%%%

```
-- [示意]
-- 尝试执行 tac，失败则恢复状态并返回 none
def tryTactic? (tac : TacticM α) : TacticM (Option α) := do
  let s ← saveState
  try
    let r ← tac
    return some r
  catch _ =>
    restoreState s
    return none
```

`tryTactic?` 把"试一试"的模式封装成了返回 `Option` 的函数。如果 `tac` 成功，返回 `some r`；如果失败，恢复状态并返回 `none`。调用者可以用 `match` 或 `if let` 来分支处理，而不需要手动写 `try`/`catch`/`restoreState`。

这个模式在编写"先试策略 A，不行试策略 B"的 tactic 时特别有用：

```
-- [示意]
elab "try_simp_then_omega" : tactic => do
  if let some _ ← tryTactic? (evalTactic (← `(tactic| simp))) then
    return  -- simp 成功，结束
  if let some _ ← tryTactic? (evalTactic (← `(tactic| omega))) then
    return  -- omega 成功，结束
  throwError "neither simp nor omega worked"
```

# 4.5 调用其他 tactic
%%%
tag := "calling-other-tactics"
%%%

在你的 tactic 中复用已有 tactic 是常见需求。Lean 提供了两种主要方式。

## 方式 1：用 `evalTactic` 执行语法
%%%
tag := "evaltactic-syntax"
%%%

```
-- [示意]
elab "my_combo" : tactic => do
  evalTactic (← `(tactic| simp))
  evalTactic (← `(tactic| ring))
```

`evalTactic` 接受一个 `Syntax` 参数（通过 `` `(tactic| ...) `` 引用构造），然后像用户在交互模式中输入这个 tactic 一样执行它。这是最通用的方式——任何用户能在 `by` 块中写的 tactic，你都能通过 `evalTactic` 调用。

它的缺点是*间接性*：每次调用都要经过语法解析和 tactic 分发（elaborate），比直接调用底层 API 函数慢一些。但在大多数场景下，这点开销可以忽略不计。

## 方式 2：直接调用实现函数
%%%
tag := "direct-impl-call"
%%%

```
-- [示意]
import Lean.Elab.Tactic.Simp

elab "simp_then_check" : tactic => do
  evalTactic (← `(tactic| simp))
  let goals ← getUnsolvedGoals
  if goals.isEmpty then
    logInfo "simp closed everything!"
  else
    logInfo m!"simp left {goals.length} goals"
```

虽然这个例子仍然用了 `evalTactic`，但你也可以直接调用 simp 的底层 API（如 `Lean.Meta.Simp.simp`）来获得更细粒度的控制——比如指定 simp lemma 集合、控制展开深度等。直接调用底层函数的好处是性能更好、控制更精细；缺点是你需要了解该 tactic 的内部 API，而这些 API 不一定有稳定的接口保证。

*选择建议*：如果你只是想"在我的 tactic 中途调用一下 simp"，用 `evalTactic` 就够了。如果你需要精细控制或者性能敏感，再考虑直接调用底层 API。

# 4.6 `withMainContext` 模式
%%%
tag := "with-main-context"
%%%

## 问题背景
%%%
tag := "context-mismatch-problem"
%%%

在 tactic 编程中，有一个容易踩的坑：*局部上下文不匹配*。每个目标（`MVarId`）都有自己的局部上下文（local context），包含了该目标可见的局部变量和假设。当你调用 `getLCtx` 获取局部上下文时，拿到的是*当前活跃的上下文*，而这个上下文不一定是你正在操作的那个目标的上下文。

举个例子：你用 `getMainGoal` 拿到了目标 `g`，然后直接调用 `getLCtx`。如果之前有别的操作切换过上下文，`getLCtx` 返回的可能不是 `g` 的上下文，而是之前某个操作遗留下来的上下文。这会导致你在错误的上下文中查找假设，产生难以排查的 bug。

## 解决方案
%%%
tag := "context-solution"
%%%

```
-- [示意]
elab "safe_tactic" : tactic => do
  withMainContext do        -- 自动切换到主目标的上下文
    let target ← getMainTarget
    -- 这里的 getLCtx 保证是主目标的局部上下文
    let lctx ← getLCtx
    -- ... 在正确的上下文中操作 ...
```

`withMainContext` 的实现等价于 `getMainGoal >>= fun g => g.withContext`。它做了两件事：取出主目标，然后在该目标的局部上下文中执行后续代码。这样你在 `do` 块中调用 `getLCtx`、`getLocalDecl` 等 API 时，总是能拿到正确的上下文。

## `withMainContext` vs `withContext` 的区别
%%%
tag := "withmaincontext-vs-withcontext"
%%%

`withContext` 是更底层的 API：`g.withContext do ...` 在目标 `g` 的上下文中执行代码。你需要自己指定是哪个目标。

`withMainContext` 是语法糖：它自动选择主目标。在大多数 tactic 中，你操作的就是主目标，所以用 `withMainContext` 更简洁。

但如果你在遍历多个目标（比如模式 2 中的循环），你应该用 `g.withContext` 而不是 `withMainContext`——因为循环中的 `g` 不一定是主目标：

```
-- [示意]
elab "inspect_all" : tactic => do
  for g in (← getGoals) do
    g.withContext do           -- 用 g 的上下文，而非主目标的
      let target ← g.getType
      let lctx ← getLCtx
      logInfo m!"Goal {g.name} has {lctx.size} local decls, target: {target}"
```

如果在这个循环里用 `withMainContext`，每次迭代都会切换到主目标的上下文，而不是当前循环变量 `g` 的上下文——这几乎肯定不是你想要的。

# 4.7 常见失败模式与调试
%%%
tag := "common-failures-debugging"
%%%

写 tactic 时，目标管理相关的 bug 往往表现为"运行时没报错，但结果不对"或"莫名其妙的 internal error"。以下是最常见的几类问题。

## 4.7.1 忘了更新 goals 列表
%%%
tag := "failure-forgetting-goals-update"
%%%

*症状*：你的 tactic 把主目标解决了（给它 `assign` 了一个证明项），但后续 tactic 仍然试图操作已解决的目标，或者 Lean InfoView 显示的目标没有变化。

*原因*：你 `assign` 了目标，但没有调用 `setGoals` 把已解决的目标从列表中移除。

```
-- [示意]
-- ❌ 错误写法
elab "bad_exact" : tactic => do
  let goal ← getMainGoal
  goal.assign someProofTerm
  -- 忘了 setGoals！goal 仍在列表中

-- ✅ 正确写法
elab "good_exact" : tactic => do
  let goal ← getMainGoal
  goal.assign someProofTerm
  let remaining ← getUnsolvedGoals  -- 自动过滤已赋值的目标
  setGoals remaining
```

*建议*：如果你的 tactic 可能通过 `assign` 解决目标却没有同步更新列表，可以在最后调用 `setGoals (← getUnsolvedGoals)` 来清理残留的已解决目标。但这只是一个*防御性清理手段*，不应作为通用模板——在大多数场景下，优先使用 `replaceMainGoal` 来精确管理目标列表，而不是依赖最后的"大扫除"。

## 4.7.2 `saveState` 和 `restoreState` 的正确用法
%%%
tag := "failure-savestate-restorestate"
%%%

*症状*：你用了 `try`/`catch` 来回退失败的尝试，但回退后状态仍然不干净——有些元变量残留了赋值。

*原因*：你在 `catch` 中忘了 `restoreState`，或者在 `try` 块外面保存了状态但在 `try` 块里面又进行了会影响状态的操作。

```
-- [示意]
-- ❌ 常见错误：忘了 restoreState
elab "bad_try" : tactic => do
  try
    evalTactic (← `(tactic| apply And.intro))
  catch _ =>
    pure ()  -- 没有 restoreState！
    -- apply 可能已经创建了新的元变量或做了 unification
    -- 这些副作用会残留

-- ✅ 正确写法
elab "good_try" : tactic => do
  let s ← saveState
  try
    evalTactic (← `(tactic| apply And.intro))
  catch _ =>
    restoreState s  -- 完全回退
```

另一个常见错误是*在错误的位置保存状态*。如果你在循环中多次保存/恢复，确保每次保存的是当次迭代开始时的状态，而不是循环开始前的总状态——否则每次恢复都会回退到循环起点，丢失前面迭代的成果。

## 4.7.3 `focus` 的副作用
%%%
tag := "failure-focus-side-effects"
%%%

*症状*：在 `focus` 块结束后，你发现某些目标"消失了"，或者目标的顺序与预期不同。

*原因*：`focus` 在结束时会把 `tac` 执行后的目标列表和之前"摘走"的 `rest` 拼接在一起。如果 `tac` 内部调用了 `setGoals` 并且不小心把 `rest` 中的目标也加进去（例如通过某个间接调用），`focus` 结束后这些目标就会出现两次。

```
-- [示意]
-- ❌ 可能出问题的用法
elab "focus_danger" : tactic => do
  Lean.Elab.Tactic.focus do
    let allGoals ← getGoals  -- focus 内部，只能看到主目标
    -- 但如果你在这里通过 MetavarContext 获取了其他目标并加到列表中...
    -- focus 结束时会把它们和 rest 拼起来，可能导致重复
```

*建议*：在 `focus` 块内部，不要往目标列表中添加不属于当前 `focus` 范围的目标。`focus` 的契约是"进去时只看到主目标，出来时只有新产生的子目标"。遵守这个契约就不会出问题。

## 4.7.4 `withMainContext` vs `withContext` 的误用
%%%
tag := "failure-context-misuse"
%%%

*症状*：你在遍历多个目标时，每个目标拿到的局部上下文都一样——都是主目标的上下文。

*原因*：在循环中用了 `withMainContext` 而不是 `g.withContext`。详见 4.6 节的讨论。

*调试技巧*：在循环中加一行 `logInfo m!"Processing goal {g.name} in context with {(← getLCtx).size} decls"`，如果每次打印的 `size` 都一样（且不符合预期），说明上下文切换有问题。

## 4.7.5 通用调试手段
%%%
tag := "general-debugging-tips"
%%%

当 tactic 的行为不符合预期时，以下手段可以帮助你定位问题：

1. *`logInfo` 打印状态*：在关键位置打印目标列表的长度和内容。`logInfo m!"goals: {← getGoals}"` 会显示当前所有目标的 `MVarId`。
2. *`isAssigned` 检查*：在 `setGoals` 之前，检查每个目标的赋值状态。`for g in goals do logInfo m!"{g.name}: assigned={← g.isAssigned}"` 可以帮你确认哪些目标已经被解决了。
3. *最小化复现*：把 tactic 拆成更小的步骤，在每步之后检查目标状态。这比在整个 tactic 上猜测问题原因要高效得多。
4. *`trace` 系统*：Lean 提供了 `trace[Meta.Tactic]` 等 trace 选项，可以打印 tactic 框架内部的执行细节。通过 `set_option trace.Meta.Tactic true` 开启。

# 4.8 练习
%%%
tag := "exercises"
%%%

## 热身练习
%%%
tag := "warmup-exercises"
%%%

*练习 4.1：`rotate_goals`*

实现一个 tactic `rotate_goals`，它把目标列表"旋转"一个位置：主目标移到列表末尾，第二个目标变成新的主目标。如果只有一个或零个目标，什么都不做。

```anchor rotateGoals
elab "rotate_goals" : tactic => do
  sorry -- 你的实现
```

提示：你只需要用 `getGoals` 和 `setGoals`，加上列表操作。

*练习 4.2：`count_goals`*

实现一个 tactic `count_goals`，它不改变任何状态，只在 InfoView 中打印当前未解决的目标数量。

```anchor countGoals
elab "count_goals" : tactic => do
  sorry -- 你的实现
```

提示：使用 `getUnsolvedGoals` 和 `logInfo`。

## Debug 练习
%%%
tag := "debug-exercises"
%%%

*练习 4.3：找出 bug*

下面的 tactic 试图对每个目标尝试 `assumption`，解决能解决的，保留不能解决的。但它有一个 bug——找出来并修复它。

```anchor tryAssumptionAll
elab "try_assumption_all" : tactic => do
  let goals ← getGoals
  for g in goals do
    try
      evalTactic (← `(tactic| assumption))
    catch _ =>
      pure ()
  -- Bug 在哪里？
```

提示：考虑两个问题——（1）`evalTactic` 默认作用于*主目标*（即目标列表的第一个元素），而不是循环变量 `g`——所以循环中每次 `assumption` 操作的未必是你期望的目标；（2）失败时状态有没有被正确恢复？

## 综合练习
%%%
tag := "comprehensive-exercises"
%%%

*练习 4.4：`first_success`*

实现一个 tactic `first_success`，它接受一个 tactic 列表，对主目标依次尝试每个 tactic，使用第一个成功的。如果全部失败，抛出错误信息列出所有尝试过的 tactic 和它们的错误。

```
-- [伪代码]
-- 目标行为：
-- first_success [simp, omega, assumption]
-- 等价于：先试 simp，不行试 omega，不行试 assumption，全不行则报错

elab "first_success" : tactic => do
  sorry -- 你的实现
```

提示：使用 `saveState`/`restoreState` 进行回溯。把每次失败的错误信息收集起来，如果全部失败，用 `throwError` 一次性报告。

# 4.9 小结
%%%
tag := "summary"
%%%

- `获取/设置目标列表`：`getGoals` / `setGoals`
- `获取未解决的目标`：`getUnsolvedGoals`
- `只看主目标`：`getMainGoal` / `getMainTarget`
- `聚焦`：`focus tac`
- `保存/恢复`：`saveState` / `restoreState`
- `试探性执行`：`tryTactic?`
- 调用其他 tactic：evalTactic
- `安全上下文切换`：`withMainContext do` / `g.withContext do`

*核心原则*：

- 永远用 `withContext` 或 `withMainContext` 确保局部上下文正确——在遍历多个目标时，用 `g.withContext` 而不是 `withMainContext`。
- 回溯时用 `saveState` / `restoreState`，不要手动管理 `MetavarContext`——手动管理几乎必然遗漏。
- 新子目标放在列表前面，遵循用户期望的深度优先顺序。优先使用 `replaceMainGoal` 而非手写 `getGoals`/`erase`/`setGoals`。
- 需要清理残留的已解决目标时，可以用 `setGoals (← getUnsolvedGoals)` 作为防御性手段，但不应作为目标管理的通用模板。
- 出了问题时，用 `logInfo` 打印目标列表和赋值状态进行调试。

# 下一章预告
%%%
tag := "next-chapter-preview"
%%%

下一章将进入 *Type Class Synthesis*——Lean 的类型类推断系统。你将了解 Lean 如何自动搜索类型类实例，`instance` 的优先级如何影响搜索顺序，以及在 tactic 编程中如何手动触发和控制 instance synthesis。这是理解 `simp`、`norm_num` 等高级 tactic 内部机制的基础。
