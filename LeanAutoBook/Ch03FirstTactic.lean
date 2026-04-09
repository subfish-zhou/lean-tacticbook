import VersoManual

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch03FirstTactic"

#doc (Manual) "第三章 编写你的第一个 Tactic" =>
%%%
file := "Ch03FirstTactic"
tag := "ch03-first-tactic"
%%%

*本章目标*：从零实现几个有实际用途的 tactic，掌握 `TacticM` 的核心模式。

# 回顾：从 Expr 到 Tactic
%%%
tag := "recap-expr-to-tactic"
%%%

第二章中，你学习了 Lean 4 内部表示表达式的核心数据类型 `Expr`。你已经知道 `Expr.app`、`Expr.const`、`Expr.mvar` 等构造子分别代表什么，也知道如何用 {moduleTerm}`mkApp`、{moduleTerm}`mkConst` 等辅助函数构造表达式。本章要做的事情是：*把 Expr 的知识用起来*。

Tactic 的本质是什么？它是一个接收当前证明状态、返回新证明状态的函数。而"证明状态"的核心就是一组尚未填充的元变量（metavariable），每个元变量对应一个待证目标。Tactic 的工作就是读取这些元变量的类型（即目标命题），构造出合适的 `Expr` 来填充它们，或者把一个目标拆分成更小的子目标。

换句话说，第二章教你认识了积木的形状，本章教你用这些积木搭建证明。

# Tactic 的生命周期
%%%
tag := "tactic-lifecycle"
%%%

回顾第一章：tactic 是一个 `Syntax → TacticM Unit` 函数。当 Lean 在证明模式中遇到你注册的 tactic 关键字时，就会调用这个函数。它的完整生命周期分为五步：

1. *接收语法*：Lean 解析器根据你用 `syntax` 或 `elab` 注册的语法规则进行匹配，把解析出的 `Syntax` 节点传给你的函数。如果你的 tactic 接受参数（比如一个假设名），参数也在这个 `Syntax` 里。

2. *读取状态*：从 `TacticM` monad 中获取当前目标列表。最常用的是 {moduleTerm}`getMainGoal`（取第一个目标）和 {moduleTerm}`getGoals`（取全部目标）。每个目标是一个 `MVarId`——元变量的唯一标识符。

3. *分析目标*：通过 `goal.getType` 拿到目标的类型（一个 `Expr`），然后用第二章学到的模式匹配技术分析它的结构。比如判断它是否形如 `P ∧ Q`，或者是否是一个等式 `a = b`。

4. *构造证明项并更新状态*：这是最关键的一步。你需要构造一个 `Expr` 来"回答"当前目标。如果证明项中还有未填充的部分（hole），那些 hole 就变成新的子目标。最后调用 `goal.assign proof` 关闭当前目标，调用 {moduleTerm}`setGoals` 设置新的目标列表。

5. *返回*：`TacticM Unit` 不需要显式返回值。剩余的目标留在目标列表中，由后续 tactic 继续处理。如果所有目标都被关闭了，证明就完成了。

最简单的 tactic 只做第 2 和第 4 步——读取目标，然后直接用一个现成的表达式关闭它。复杂的 tactic 会在第 3 步做大量分析，甚至递归地调用自己或其他 tactic。

# assumption：在假设中搜索
%%%
tag := "assumption-search"
%%%

`assumption` 是最经典的入门 tactic：在局部上下文中找一个类型匹配目标的假设，然后用它关闭目标。这个 tactic 虽然简单，但展示了 tactic 编写的基本骨架。

```anchor my_assumption
elab "my_assumption" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.getType
    let lctx ← getLCtx
    for decl in lctx do
      if decl.isImplementationDetail then continue
      if ← isDefEq decl.type target then
        goal.assign decl.toExpr
        return
    throwTacticEx `my_assumption goal "no matching hypothesis found"
```

逐行解释这段代码：

*`let goal ← getMainGoal`*：从当前证明状态中取出第一个未解决的目标。{moduleTerm}`getMainGoal` 返回 `MVarId`，它是元变量的标识符。为什么叫"main goal"？因为 Lean 的目标列表是有序的，第一个目标就是用户在 Infoview 中看到的那个。

*`goal.withContext do`*：这一步至关重要。每个目标都有自己的局部上下文（local context），包含该目标可见的所有局部变量和假设。不同目标的上下文可能不同——比如 `cases` 拆分出的两个子目标，各自有不同的假设。`withContext` 把 monad 的环境切换到该目标的上下文，这样后续的 {moduleTerm}`getLCtx` 才能拿到正确的假设列表。*忘记 `withContext` 是新手最常犯的错误之一*，后面 3.8 节会专门讨论。

*`let target ← goal.getType`*：获取目标的类型，即待证命题。返回值是一个 `Expr`。

*`let lctx ← getLCtx`*：获取当前局部上下文，它是一个 `LocalContext`，包含所有局部声明（local declaration）。

*`for decl in lctx do`*：遍历所有局部声明。每个 `decl` 是一个 `LocalDecl`，包含 `.userName`（用户可见的名字）、`.type`（类型）、`.toExpr`（对应的自由变量表达式，即 `Expr.fvar`）等字段。

*`if decl.isImplementationDetail then continue`*：跳过编译器内部生成的辅助变量。这些变量对用户不可见，不应该被 tactic 使用。

*`if ← isDefEq decl.type target then`*：这是核心判断。{moduleTerm}`isDefEq` 检查两个表达式是否 definitionally equal——不只是语法层面的相等，而是考虑 beta 规约（`(fun x => x) a ≡ a`）、delta 规约（展开定义）、iota 规约（结构体投影和匹配）等所有计算规则之后的相等性。如果假设的类型和目标匹配，我们就找到了证明。

*`goal.assign decl.toExpr`*：用这个假设（一个 `Expr.fvar`）填充目标元变量。这相当于说"这个目标的证明就是这个假设"。赋值后，目标就被关闭了。

*`throwTacticEx`*：如果遍历完所有假设都没找到匹配的，抛出一个带目标上下文的错误。用户会看到错误信息和当前目标的完整状态，便于 debug。

# `split_and`：拆分合取目标
%%%
tag := "split-and"
%%%

如果目标是 `P ∧ Q`，我们希望把它拆成两个子目标 `P` 和 `Q`。这个 tactic 展示了一个比 `assumption` 更复杂的模式：不是直接关闭目标，而是把目标"拆开"。

```anchor split_and
elab "split_and" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.getType
    let_expr And P Q := target | throwTacticEx `split_and goal "goal is not a conjunction"
    let mvarP ← mkFreshExprMVar P
    let mvarQ ← mkFreshExprMVar Q
    let proof := mkApp4 (mkConst ``And.intro) P Q mvarP mvarQ
    goal.assign proof
    let newGoals := [mvarP.mvarId!, mvarQ.mvarId!]
    let others := (← getGoals).erase goal
    setGoals (newGoals ++ others)
```

这段代码的思路是什么？要证明 `P ∧ Q`，需要构造 `And.intro hP hQ`，其中 `hP : P`、`hQ : Q`。但我们现在手上还没有 `hP` 和 `hQ`，所以先创建两个"占位符"（元变量），拼成证明项赋值给原目标，然后把这两个占位符作为新的子目标留给用户。

逐行拆解：

*`let_expr And P Q := target | ...`*：这是 Lean 提供的宏，专门用于对 `Expr` 做模式匹配。它会检查 `target` 是否形如 `@And P Q`（即 `Expr.app (Expr.app (Expr.const And _) P) Q`），如果是则绑定 `P` 和 `Q`，否则执行 `|` 后面的分支。这比手写 `match` 简洁很多。

*`let mvarP ← mkFreshExprMVar P`*：创建一个类型为 `P` 的新元变量。{moduleTerm}`mkFreshExprMVar` 返回 `Expr`（具体来说是一个 `Expr.mvar`），这个表达式代表一个尚未填充的 hole。`.mvarId!` 可以取出它的 `MVarId`。

*`let proof := mkApp4 (mkConst And.intro) P Q mvarP mvarQ`*：构造表达式 `@And.intro P Q ?mvarP ?mvarQ`。{moduleTerm}`mkApp4` 是 {moduleTerm}`mkApp` 的四参数版本。注意 `And.intro` 的完整签名是 `And.intro : {a b : Prop} → a → b → a ∧ b`，这里四个参数分别是 `a := P`、`b := Q`、以及两个证明。

*`goal.assign proof`*：把原目标赋值为这个带 hole 的证明项。Lean 的元变量系统会自动追踪哪些 hole 尚未填充。

*`let others := (← getGoals).erase goal`*：从目标列表中移除当前目标。用 `List.erase` 而不是 `tail!`，是因为当前目标不一定在列表首位——在多目标场景中，目标的顺序可能已被其他 tactic 调整过。

*`setGoals (newGoals ++ others)`*：把两个新子目标放在前面，其余未处理的目标跟在后面。*这一步不能遗漏*——如果你不调用 {moduleTerm}`setGoals`，新创建的元变量不会出现在目标列表中，用户在 Infoview 里看不到它们，也无法用后续 tactic 处理它们。

这个例子展示了 tactic 最核心的模式：*分析目标结构 → 构造部分证明项（带 hole）→ 把 hole 变成新的子目标*。几乎所有非平凡的 tactic 都遵循这个模式。

> *{moduleTerm}`replaceMainGoal` vs {moduleTerm}`setGoals` 的选择*
>
> - *只替换当前主目标*时，用 `replaceMainGoal newGoals`——它自动把主目标替换为 `newGoals`，并保留其余目标，不需要手动做 `erase`。
> - *需要完全控制整个目标列表*时（比如重新排序、批量过滤），才用 {moduleTerm}`setGoals`。
>
> 经验法则：如果你的 tactic 只处理一个目标并产出若干子目标，{moduleTerm}`replaceMainGoal` 更简洁也更安全。

# 调用已有 tactic：组合式证明
%%%
tag := "combining-tactics"
%%%

手动构造 `Expr` 虽然灵活，但很多时候你不需要从头来——Lean 标准库已经提供了大量 tactic，你可以在自己的 tactic 中直接调用它们。这就是"组合式"tactic 的思路：把已有的自动化当作积木块来组合。

```anchor my_smart_close
elab "my_smart_close" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.getType
    let lctx ← getLCtx
    for decl in lctx do
      if decl.isImplementationDetail then continue
      if ← isDefEq decl.type target then
        goal.assign decl.toExpr
        return
    try
      evalTactic (← `(tactic| rfl))
      return
    catch _ => pure ()
    throwTacticEx `my_smart_close goal "no hypothesis matches and rfl failed"
```

核心 API 是 *{moduleTerm}`evalTactic`*：它接收一个 `Syntax` 节点，执行对应的 tactic。`` ← `(tactic| ...) `` 是 Lean 的 quotation 语法，用于在代码中构造 `Syntax`。

这段代码的策略是*搜索 + 回退*：先试最简单的方法（直接在假设中找精确匹配），失败了再试 `rfl`（关闭 `a = a` 形式的等式目标）。`try ... catch _ => pure ()` 确保第二个策略失败时不会中断整个 tactic，而是回退到最后的 `throwTacticEx`。

你也可以用 {moduleTerm}`evalTactic` 一次性表达同样的逻辑：

```anchor my_smart_close_short
elab "my_smart_close₂" : tactic => do
  evalTactic (← `(tactic| first | assumption | rfl))
```

`first` 会依次尝试列出的 tactic，直到有一个成功。这种写法更简洁，但手动写搜索循环给你更多控制权——比如你可以过滤掉特定类型的假设，或者按照特定顺序搜索。直接操作 `Expr` 也比通过 {moduleTerm}`evalTactic` 调用更高效，因为省去了语法解析和 tactic 调度的开销。在性能敏感的场景（比如要在大量目标上运行的自动化），这种混合风格很常见。

# 对所有目标执行同一操作
%%%
tag := "operate-all-goals"
%%%

前面的 tactic 都只处理第一个目标（{moduleTerm}`getMainGoal`）。但有时你希望对所有未解决的目标执行同一操作——比如"把所有能用 `assumption` 关掉的目标都关掉"。

```anchor assumption_on_all
elab "assumption_on_all" : tactic => do
  let goals ← getGoals
  let mut remaining : List MVarId := []
  for g in goals do
    if ← g.isAssigned then continue
    let closed ← g.withContext do
      let target ← g.getType
      let lctx ← getLCtx
      for decl in lctx do
        if decl.isImplementationDetail then continue
        if ← isDefEq decl.type target then
          g.assign decl.toExpr
          return true
      return false
    if !closed then
      remaining := remaining ++ [g]
  setGoals remaining
```

注意几个关键点：

*`let goals ← getGoals`*：获取所有目标，而不是只取第一个。

*`if ← g.isAssigned then continue`*：检查目标是否已经被赋值。为什么需要这个检查？因为 {moduleTerm}`isDefEq` 有副作用——它在判断等价性的过程中可能会实例化（instantiate）某些元变量。这意味着在处理目标 A 时调用 {moduleTerm}`isDefEq`，可能会"顺带"解决了目标 B。所以在处理每个目标之前，先检查它是否已经被解决了。

*`g.withContext do`*：注意这里每个目标都需要单独调用 `withContext`，因为不同目标的局部上下文可能不同。

*`remaining := remaining ++ [g]`*：如果某个目标没能被关闭，把它加入 remaining 列表。

*`setGoals remaining`*：最后用 remaining 更新目标列表。被关闭的目标不在列表中，用户看到的就只剩没解决的。

# 错误处理与 diagnostics
%%%
tag := "error-handling"
%%%

好的 tactic 不仅要能成功，还要在失败时给出有用的信息。Lean 提供了多个层次的诊断工具：

```anchor diagnostics
-- throwTacticEx 会显示目标上下文
-- throwTacticEx `my_tactic goal "expected an equality goal"

-- throwError 是通用错误
-- throwError "my_tactic: internal error"

-- logWarning 不中断执行
-- logWarning "this goal might not be provable by my_tactic"

-- trace 用于调试
-- trace[my_tactic] "trying hypothesis {decl.userName}"
```

*`throwTacticEx` vs `throwError`*：`throwTacticEx` 接受一个 `MVarId` 参数，抛出的错误信息会包含该目标的完整上下文（包括所有假设和目标类型）。这对用户来说非常有价值——他们不需要自己去翻 Infoview 就能看到出错时的状态。`throwError` 则是通用的错误抛出函数，不附带目标上下文，适合用于和特定目标无关的错误（比如参数解析失败）。

*{moduleTerm}`logWarning`*：发出警告但不中断执行。适合用于"这个情况可能有问题但不确定"的场景。

*`trace`*：调试专用。只有在用户设置了 `set_option trace.my_tactic true` 时才会输出。适合在开发过程中打印中间状态。

注册 trace option：

```anchor register_trace
initialize registerTraceClass `my_tactic
```

你需要在文件顶部调用 `registerTraceClass` 来注册 trace 类别。之后就可以在代码中使用 `trace[my_tactic]` 来输出调试信息。Lean 的 trace 系统支持层级结构——你可以注册 `my_tactic.search` 和 `my_tactic.unify` 来分别控制搜索和 unification 阶段的调试输出。

# 常见失败模式与 debug
%%%
tag := "ch03-common-failures"
%%%

编写 tactic 时，有几类错误特别常见。本节列出最典型的失败模式，帮助你快速定位问题。

## 忘记 withContext
%%%
tag := "failure-missing-withcontext"
%%%

这是新手最容易犯的错误。看下面的代码：

```
-- [示意]
-- 错误示范：忘记 withContext
elab "bad_assumption" : tactic => do
  let goal ← getMainGoal
  -- 没有调用 goal.withContext！
  let target ← goal.getType
  let lctx ← getLCtx    -- 拿到的可能是错误的上下文
  for decl in lctx do
    if ← isDefEq decl.type target then
      goal.assign decl.toExpr
      return
  throwError "not found"
```

如果你在证明过程中只有一个目标、且没有经过 `intro` 或 `cases` 之类改变上下文的操作，这段代码可能"碰巧"能工作。但一旦有多个目标或上下文被修改过，{moduleTerm}`getLCtx` 拿到的就不是当前目标的上下文，而是"默认"上下文（通常是最外层的），导致找不到该有的假设，或者更糟——找到错误的假设。

*规则*：只要你要读取目标的局部上下文，就用 `goal.withContext do` 包裹。没有例外。

## isDefEq 的 unification 副作用
%%%
tag := "failure-isdefeq-unification"
%%%

{moduleTerm}`isDefEq` 不是一个纯函数——它会修改元变量的状态。当你调用 `isDefEq a b`，如果 `a` 或 `b` 中包含未实例化的元变量，{moduleTerm}`isDefEq` 可能会把它们实例化来使等式成立。

```
-- [伪代码]
-- 危险场景：isDefEq 的副作用
let mvar ← mkFreshExprMVar (mkConst ``Nat)
-- 此时 mvar 尚未赋值
let _ ← isDefEq mvar (mkNatLit 42)
-- 现在 mvar 被赋值为 42 了！
```

这有两个实际后果：

1. *不要把 {moduleTerm}`isDefEq` 当作"无害的检查"来用*。如果你只是想"试试看两个类型是否相同"但不想产生任何副作用，你需要用 `withoutModifyingState` 包裹：`withoutModifyingState (isDefEq a b)`。

2. *遍历假设时注意顺序*。如果你先用 {moduleTerm}`isDefEq` 匹配了假设 A，虽然最终没用它（比如后来发现假设 B 更好），但 A 的匹配过程可能已经实例化了某些元变量，影响后续的匹配。这是 3.5 节中需要 `g.isAssigned` 检查的根本原因。

## setGoals 遗漏目标
%%%
tag := "failure-setgoals-missing"
%%%

```
-- [伪代码]
-- 错误示范：忘记保留其他目标
elab "bad_split" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    -- ...构造子目标 mvarP 和 mvarQ...
    goal.assign proof
    setGoals [mvarP.mvarId!, mvarQ.mvarId!]  -- 只设置了新目标！
```

问题在哪？如果调用 `bad_split` 时目标列表是 `[goal, g2, g3]`，{moduleTerm}`setGoals` 只设置了 `[mvarP, mvarQ]`，那 `g2` 和 `g3` 就从目标列表中消失了。用户看不到它们，也无法用后续 tactic 处理它们——但它们还在那里，未被证明，最终会导致"unsolved goals"错误。

正确的做法是保留原目标列表中除了当前目标以外的所有目标：

```
-- [伪代码]
let others := (← getGoals).erase goal
setGoals (newGoals ++ others)
```

用 `List.erase` 而不是 `tail!`，是因为当前目标不一定在列表首位——在多目标场景中顺序可能已被调整。

## throwTacticEx vs throwError 的选择
%%%
tag := "throw-tactic-ex-vs-error"
%%%

```
-- [伪代码]
-- 当你有 MVarId 时，优先用 throwTacticEx
throwTacticEx `my_tactic goal "expected a conjunction"
-- 输出会包含完整的目标上下文，类似：
-- my_tactic: expected a conjunction
-- h : P
-- ⊢ P → Q

-- 当你没有特定目标、或者错误与目标无关时，用 throwError
throwError "my_tactic: unexpected number of arguments"
```

经验法则：如果你的错误信息中包含"目标应该是 XXX 形式"之类的内容，用 `throwTacticEx`，因为用户需要看到目标上下文才能理解为什么不匹配。如果是语法错误、参数错误等和目标无关的情况，用 `throwError`。

# 练习
%%%
tag := "ch03-exercises"
%%%

## 练习 1（热身）：`my_exact`
%%%
tag := "exercise-3-1"
%%%

编写一个 tactic `my_exact`，接受一个标识符参数，在局部上下文中查找该名字的假设并用它关闭目标。

提示：
- 用 `elab "my_exact" ident:ident : tactic => do` 接收参数
- 用 `ident.getId` 获取名字
- 在 `lctx` 中用 `lctx.findFromUserName?` 查找

测试用例：

```
-- [示意]
example (h : 1 + 1 = 2) : 1 + 1 = 2 := by
  my_exact h  -- 应该成功
```

## 练习 2（热身）：`my_intro`
%%%
tag := "exercise-3-2"
%%%

编写一个 tactic `my_intro`，当目标是 `P → Q` 时引入假设。

提示：
- 目标 `P → Q` 在 `Expr` 层面是 `Expr.forallE name P Q info`
- 用 `goal.intro name` 来引入——它会自动创建新的局部假设并返回新目标
- `goal.intro` 返回的是新目标的 `MVarId`，你需要 `replaceMainGoal [newGoal]` 来更新

## 练习 3（debug）：找出 bug
%%%
tag := "exercise-3-3"
%%%

下面的 tactic 试图对所有目标执行 `rfl`，但有两个 bug。找出并修复它们。

```
-- [示意]
elab "rfl_all" : tactic => do
  let goals ← getGoals
  for g in goals do
    g.withContext do
      try
        let target ← g.getType
        let_expr Eq _ lhs _ := target | throwError "not eq"
        g.assign (← mkEqRefl lhs)
      catch _ => pure ()
  setGoals []  -- bug 在这里附近
```

提示：bug 1 与 {moduleTerm}`setGoals` 有关（参考 3.7 节），bug 2 与 `Eq` 的参数个数有关（`@Eq α a b` 有三个参数，不是两个）。

## 练习 4（综合）：`split_iff`
%%%
tag := "exercise-3-4"
%%%

编写一个 tactic `split_iff`，当目标是 `P ↔ Q` 时拆成两个子目标 `P → Q` 和 `Q → P`。

提示：
- `Iff.intro` 的签名是 `{a b : Prop} → (a → b) → (b → a) → (a ↔ b)`
- 模仿 3.3 节的 `split_and`，但换成 `Iff` 和 `Iff.intro`
- 两个子目标的类型分别是 `P → Q` 和 `Q → P`——你需要用 `mkArrow` 来构造箭头类型
- 不要忘记用 `(← getGoals).erase goal` 保留其他目标，或者用 {moduleTerm}`replaceMainGoal`

# 小结
%%%
tag := "ch03-summary"
%%%

- {moduleTerm}`getMainGoal` + `goal.withContext`：获取目标并切换上下文
- `goal.getType`：读取目标命题
- `goal.assign proof`：用证明项关闭目标
- `mkFreshExprMVar T`：创建类型 T 的新 hole（子目标）
- {moduleTerm}`setGoals`：更新目标列表
- `isDefEq a b`：判断定义等价（核心匹配操作）
- `throwTacticEx`：带目标上下文的错误信息
- {moduleTerm}`evalTactic`：在 tactic 中调用其他 tactic
- `withoutModifyingState`：不产生副作用地执行操作

*核心原则*：tactic = 读目标 + 分析结构 + 构造证明项 + 更新目标列表。

本章你学到了编写 tactic 的完整流程：从最简单的 `assumption` 到拆分目标的 `split_and`，从组合已有 tactic 到对多目标批量操作，再到错误处理和常见陷阱。每个 tactic 都遵循同一个模式——读取目标、分析 `Expr` 结构、构造证明项、更新目标列表。

下一章将深入目标管理的进阶技巧：如何用 `focus` 聚焦单个目标、如何用 `withMainContext` 简化上下文切换、如何实现回溯搜索（backtracking），以及 `MonadBacktrack` 的工作原理。
