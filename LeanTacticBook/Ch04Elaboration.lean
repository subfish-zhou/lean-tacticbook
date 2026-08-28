import VersoManual
import LeanTacticBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "examples"
set_option verso.exampleModule "Examples.Ch04Elaboration"

#doc (Manual) "译补" =>
%%%
file := "Ch04Elaboration"
tag := "ch04-elaboration"
%%%

> *本章目标。* 现在就写出实用的目标驱动证明术：读取当前目标和局部上下文，译补调用者给出的项，关闭或替换目标，创建子目标，调用已有证明术，并把错误报在引发错误的那段句法上。
>
> *版本基线。* Lean 4.32.2 与 Mathlib 修订版 `905b95818eb3`。

# 4.0 先借来机器，再拆开它
%%%
tag := "ch04-borrow-machine"
file := "ch04-borrow-machine"
number := false
%%%

上一版 `poly_roots` 要求调用者重复三份信息：

```module (module := Examples.Ch03Macros) (anchor := elaboration_old_poly_roots_call)
  poly_roots x^2 - 5*x + 6 with [2, 3] in x
```

多项式、根和变量都已出现在目标里，但宏只拿到调用处的 `Syntax`；目标怎么变，都不会给这棵句法树多添一个参数。译补器则能读取当前目标。先用一个最小例确认这件事，再让调用者只保留多项式，把根和变量从目标右边读出来。

一个证明术译补器下面垫着四层计算。若等到四层全部拆完才动手，第一个能读取目标的实用证明术就离得太远了。这里先借用需要的操作；第 5 至第 8 章再逐层拆开它们。

# 4.1 同一句调用，读到不同目标
%%%
tag := "ch04-show-target"
file := "ch04-show-target"
number := false
%%%

先写最小的证明术译补器。它不关闭目标，不生成新目标，只把当前目标记进 Lean 的诊断消息：

```anchor elaboration_show_target
syntax "my_show_target" : tactic

elab_rules : tactic
  | `(tactic| my_show_target) => withMainContext do
      logInfo m!"{← getMainTarget}"

set_option linter.unusedTactic false in
example (P : Prop) : P → P := by
  my_show_target
  intro h
  my_show_target
  exact h
```

两次调用的文本完全相同。第一次位于 `intro` 之前，消息里的目标是 `P → P`；第二次位于 `intro h` 之后，消息变成 `P`。解析器两次都只生成 `my_show_target` 那棵 `Syntax`，变化来自证明现场。

`macro_rules` 的分支会把输入句法换成另一棵句法；这里的 `elab_rules : tactic` 分支则运行一项 `TacticM` 计算。`withMainContext` 把主目标携带的局部声明装入当前 Meta 现场，`getMainTarget` 取得目标 `Expr`，`m!` 将它插入结构化消息，`logInfo` 再通过诊断系统报告这条消息。函数体没有给证明洞赋值，也没有替换活动目标，所以两次观察之后仍要由 `intro` 和 `exact` 完成证明。

这就是本章所需的译补最小粒子：*调用句法不变，运行结果可以依赖当前目标。* 下面沿这条边界再走一步：先把目标右侧的 `Expr` 拆成变量与根，4.3 节再用它运行证明步骤。

# 4.2 从目标读出变量和根
%%%
tag := "ch04-read-roots"
file := "ch04-read-roots"
number := false
%%%

我们要把上一章的调用缩成：

```anchor elaboration_poly_roots_first_example
example (x : ℚ) : x^2 - 5*x + 6 = 0 ↔ x = 2 ∨ x = 3 := by
  my_poly_roots x^2 - 5*x + 6
```

它少了根列表和变量。多项式参数有意保留：无参版本当然可以再读双条件左边，但这会让刚刚得到的单一动作与另一条读取路径缠在一起。这里固定调用者给出多项式，只从目标右边读取变量和候选根。

这个公开接口只接受双条件目标。右边可以是一条等式，也可以是若干等式组成的析取；所有等式必须具有同一个左端。上例因此给出共同左端 `x` 与根数组 `#[2, 3]`。一个递归函数就能完成这项读取：

```anchor elaboration_roots_and_variable
private partial def rootsAndVariable? (e : Expr) : Option (Expr × Array Expr) := do
  let e := e.consumeMData
  if e.isAppOfArity ``Or 2 then
    let args := e.getAppArgs
    let (x, roots₁) ← rootsAndVariable? args[0]!
    let (x', roots₂) ← rootsAndVariable? args[1]!
    guard (x == x')
    return (x, roots₁ ++ roots₂)
  else
    guard (e.isAppOfArity ``Eq 3)
    let args := e.getAppArgs
    return (args[1]!, #[args[2]!])
```

从最下面的分支开始读。一条等式是以 `Eq` 为头、带三个参数的应用：等式两边共同的类型、左边和右边。`isAppOfArity` 已经检查头部与参数数目，所以这里的 `args[1]!` 和 `args[2]!` 不会越界；`!` 仍是越界时报错的索引形式，并没有接收一份静态边界证明。读取器把左边当作变量表达式，把右边装进只有一个元素的根数组。

遇到 `Or`，函数分别递归读取左右两边。两次读取必须返回同一棵左端表达式树；`guard (x == x')` 失败时，当前 `Option` 计算立即得到 `none`。递归调用后的模式绑定也遵守同一规则：任一子树返回 `none`，后面的拼接便不再运行。成功时，两个根数组直接拼在一起。

于是下面两种结合方式都会得到 `x` 与 `#[1, 2, 3]`：

:::codeBox "pseudocode"
```
x = 1 ∨ x = 2 ∨ x = 3
(x = 1 ∨ x = 2) ∨ x = 3
```
:::

每轮检查前，`consumeMData` 先剥掉最外层元数据包装，免得源码信息挡住 `Or` 或 `Eq`。定义写成 `partial`，因为终止检查器无法从 `getAppArgs` 的结果看出递归调用确实走进了原表达式的子树；运行时仍由有限的 `Expr` 树限制递归深度。`private` 则把这个教学辅助函数留在当前模块内。

这只是结构读取。它用 `==` 比较表达式树，不识别所有定义相等的写法；它也不检查共同左端是否真是自由变量，只把每条等式的左边交给内部宏充当 `x`。因此，若所有分支都写成 `r = x` 且共同左端恰好相同，读取器仍会接收；把 `x = 2` 与 `3 = x` 混在同一个析取里，则会因左端不同而返回 `none`。读取器没有求根，也不检查调用者给出的多项式。

# 4.3 译补器只负责接线
%%%
tag := "ch04-wire-elaborator"
file := "ch04-wire-elaborator"
number := false
%%%

根和变量一旦转成可重新译补的句法，上一章的证明办法就够用了。内部宏把多项式改写为因式乘积，再把乘积等于零化成根的析取：

```anchor elaboration_my_poly_roots_target
syntax "my_poly_roots_target " term " with " term " in " term : tactic

macro_rules
  | `(tactic| my_poly_roots_target $poly:term with $roots:term in $x:term) =>
      `(tactic|
        rw [show $poly = (($roots).map (fun r => $x - r)).prod by simp <;> ring] <;>
        simp [mul_eq_zero, sub_eq_zero, or_assoc])
```

第一处 `simp` 展开具体列表的 `map` 与 `prod`，`ring` 证明因式恒等式；`rw` 把这条恒等式用于原目标，最后的 `simp` 再把零乘积化成等式析取并整理结合方式。读取器只提供候选数据，数学正确性仍由这些证明步骤检查。

公开译补器在外面接一层：

```anchor elaboration_poly_roots_definition
syntax "my_poly_roots " term : tactic

elab_rules : tactic
  | `(tactic| my_poly_roots $poly:term) => withMainContext do
      let target := (← getMainTarget).consumeMData
      unless target.isAppOfArity ``Iff 2 do
        throwError "my_poly_roots: expected an iff target"
      let some (x, roots) := rootsAndVariable? target.getAppArgs[1]!
        | throwError "my_poly_roots: expected the right side to contain equalities with one shared left-hand side"
      let x ← Term.exprToSyntax x
      let roots ← roots.mapM fun root => Term.exprToSyntax root
      let roots : TSyntaxArray `term := roots
      evalTactic (← `(tactic| my_poly_roots_target $poly with [$roots,*] in $x))
```

沿用 4.1 节的 `withMainContext` 后，函数体先取得目标、剥掉外层元数据，再明确检查它是双条件。检查保证 `getAppArgs[1]!` 存在；这个参数就是右边，交给上一节的递归读取器。

读取结果是 `Expr`，内部宏却接收项句法。`Term.exprToSyntax` 为这个例子读出的局部变量与根表达式生成可重新译补的句法；它不会恢复用户原文，这里也不主张任意 `Expr` 都能无损往返。`roots.mapM` 逐个运行这项可能失败的转换，任一步失败就让整次数组转换失败。随后，类型标注把 `roots` 固定为 `term` 句法数组，使准引用中的 `$roots,*` 能逐项展开进列表。

`evalTactic` 最后在当前证明状态中运行生成的 `my_poly_roots_target` 调用；内部宏造成的目标变化会直接留在这次证明中。

再试单根和左结合析取：

```anchor elaboration_poly_roots_variants
example (x : ℚ) : x - 2 = 0 ↔ x = 2 := by
  my_poly_roots x - 2

example (x : ℚ) :
    x^3 - 6*x^2 + 11*x - 6 = 0 ↔ (x = 1 ∨ x = 2) ∨ x = 3 := by
  my_poly_roots x^3 - 6*x^2 + 11*x - 6
```

递归读取器没有为这两种形状增加分支。非双条件目标与右边结构不合分别由公开译补器报错。若参数里的多项式没有出现在目标中，`rw` 找不到改写位置；若它确实位于目标左边、却不能分解成右边给出的根，因式恒等式证明无法关闭。结构错误和数学错误停在不同层。

固定的调用句法现在能够读取变化的证明目标，再选择要运行的证明术。下一节把相同能力用于普通证明任务：从局部上下文中找到一个已经证明当前目标的假设。

# 4.4 找到已经证明目标的假设
%%%
tag := "ch04-my-assumption"
file := "ch04-my-assumption"
number := false
%%%

假设局部上下文含有 `h : P`，目标也是 `P`。我们想要的证明术没有项参数，也无需生成证明术句法再委托执行；它应该搜索局部声明，直接把匹配的自由变量放进当前证明洞。

这个教学版重构叫作 `my_assumption`。前缀不能省：该定义露出了主干路线，但 Lean 的生产级 `assumption` 还覆盖了这一版略去的工程情形。

```anchor elaboration_my_assumption_definition
private def myFindLocalDeclWithType? (type : Expr) : MetaM (Option FVarId) := do
  (← getLCtx).findDeclRevM? fun localDecl => do
    if localDecl.isImplementationDetail then
      return none
    else if ← isDefEq type localDecl.type then
      return some localDecl.fvarId
    else
      return none

syntax "my_assumption" : tactic

elab_rules : tactic
  | `(tactic| my_assumption) =>
      liftMetaTactic fun goal => do
        goal.checkNotAssigned `my_assumption
        let target ← goal.getType
        let some fvarId ← myFindLocalDeclWithType? target
          | throwError "my_assumption failed, target{indentExpr target}"
        goal.assign (mkFVar fvarId)
        return []
```

`liftMetaTactic` 先用 `withMainContext` 进入活动主目标的局部上下文，再把它的 `MVarId` 交给 MetaM 函数，接过函数返回的替代目标并负责接好队列；它定义在 `Lean/Elab/Tactic/Basic.lean` 的目标队列操作旁边。因此回调里可以直接搜索局部声明。这里搜索从较新的声明走向较旧的声明，忽略实现细节，并用 `isDefEq` 比较每个声明的类型与目标类型。

结构相等会拒绝无关紧要的表面写法差异。`isDefEq` 问的是：借助当前元变量上下文中可用的定义规约和合一，Lean 能否让两个表达式变成相同。若比较成功，匹配声明带有一个 `FVarId`，`mkFVar` 便构造引用它的表达式。把这个表达式赋给目标元变量，就填上了证明洞。返回 `[]` 则告诉 `liftMetaTactic`：刚关闭的目标不需要任何活动目标来接替。

`isDefEq` 不能当成无状态的布尔测试。在 Lean 4.32.2 中，比较失败会恢复其间产生的临时赋值，抛出异常也会恢复；比较成功却可能提交约束。如果一个更大的候选流程在合一成功后还要继续检查，而后续检查失败，整个候选仍需要外层快照。第 6 章会建立这种候选级纪律，否则后面的候选可能继承本候选留下的约束。

这个小证明术可以工作：

```anchor elaboration_my_assumption_example
example (P : Prop) (h : P) : P := by
  my_assumption
```

Lean 在 `Lean/Meta/Tactic/Assumption.lean` 中的 Meta 层实现几乎就是同一段代码。主干先把搜索抽成可复用函数：

:::codeBox "code"
```
def findLocalDeclWithType? (type : Expr) : MetaM (Option FVarId) := do
  (← getLCtx).findDeclRevM? fun localDecl => do
    if localDecl.isImplementationDetail then
      return none
    else if (← isDefEq type localDecl.type) then
      return some localDecl.fvarId
    else
      return none

def MVarId.assumptionCore (mvarId : MVarId) : MetaM Bool :=
  mvarId.withContext do
    mvarId.checkNotAssigned `assumption
    match (← findLocalDeclWithType? (← mvarId.getType)) with
    | none => return false
    | some fvarId => mvarId.assign (mkFVar fvarId); return true

def MVarId.assumption (mvarId : MVarId) : MetaM Unit :=
  unless (← mvarId.assumptionCore) do
    throwTacticEx `assumption mvarId
```
:::

`assumptionCore` 返回 `false`，别的流程便能尝试另一条路线，而不必先捕获证明术错误。`assumption` 再把这个结果包装成公开操作应有的标准失败。随后，内置译补器把它接到证明术队列上：

:::codeBox "code"
```
@[builtin_tactic Lean.Parser.Tactic.assumption] def evalAssumption : Tactic := fun _ =>
  liftMetaTactic fun mvarId =>
    withAssignableSyntheticOpaque do
      mvarId.assumption
      pure []
```
:::

这个内置译补器位于 `Lean/Elab/Tactic/BuiltinTactic.lean`；生产源码把最后的函数体排在一行里，此处只改换行，操作没有变化。定义于 `Lean/Meta/Basic.lean` 的 `withAssignableSyntheticOpaque` 允许 `isDefEq` 给 synthetic opaque 元变量赋值，因此 `assumption` 能接在 `refine` 后面使用；我们的教学版不承诺这种兼容性。

# 4.5 把调用者的项当作证明
%%%
tag := "ch04-my-exact"
file := "ch04-my-exact"
number := false
%%%

`my_assumption` 自己选择证明表达式。对 `my_exact term` 来说，调用者给出句法，当前目标则告诉 Lean 应该怎样理解它。

以 `And.intro hP hQ` 为例。译补之前，它只是句法：一个标识符、两个参数节点以及各自的源码位置。解析 `And.intro`，推断隐式命题参数，检查 `hP` 和 `hQ` 的类型，再构造最终证明表达式，全都依赖局部上下文和预期类型 `P ∧ Q`。因此，exact 一类的证明术还必须在当前上下文和目标下译补参数。

```anchor elaboration_my_exact
syntax "my_exact " term : tactic

elab_rules : tactic
  | `(tactic| my_exact $proof:term) => withMainContext do
      let goal ← getMainGoal
      let target ← instantiateMVars (← goal.getType)
      let proof ← Lean.Elab.Tactic.elabTermEnsuringType proof (some target)
      goal.assign proof
      replaceMainGoal []

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  my_exact And.intro hP hQ

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example (P Q : Prop) (hQ : Q) : P := by
  my_exact hQ
```

目标作为预期类型传给 `elabTermEnsuringType`。这个预期类型既引导译补，也会被强制检查：若结果表达式的类型无法在定义上与目标相等，辅助函数就报告类型不匹配。这个高层辅助函数会在捕获的 `proof` 句法引用下运行项译补，因此失败的例子会把位置指向调用者能够修正的那个项 `hQ`。

译补成功后，`goal.assign proof` 填上元变量。`replaceMainGoal []` 做的是另一件事：从 TacticM 的有序活动目标列表中移除旧队首。填证明洞与编辑活动目标队列相邻发生，却是两次状态更新。`my_apply` 会把两者拆开给我们看。

`Lean/Elab/Tactic/ElabTerm.lean` 中的生产级 `exact` 还会做带检查的关闭。若显式的 catch 捕获到异常，它会把弹出的目标放回队列；这不等于通用的元变量状态快照。这里只依赖两件事：成功译补会返回一个在所要求类型上可接受的证明表达式，失败仍附着在用户给出的项上。

# 4.6 应用定理，留下前提
%%%
tag := "ch04-my-apply"
file := "ch04-my-apply"
number := false
%%%

Exact 吃掉的是整个目标的证明。Apply 则从结论能够匹配目标的定理开始：它用该定理的一次应用填入旧目标，并把尚未解决的前提留下来作为新证明洞。

先只动三行：

```anchor elaboration_my_apply
syntax "my_apply " term : tactic

elab_rules : tactic
  | `(tactic| my_apply $rule:term) => withMainContext do
      let rule ← Lean.Elab.Tactic.elabTermForApply rule
      let newGoals ← (← getMainGoal).apply rule
      replaceMainGoal newGoals

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  my_apply And.intro
  · exact hP
  · exact hQ
```

`elabTermForApply` 译补规则时，不把目标用作预期类型。尤其是标识符，它会先以一种不急着插入隐式参数的形式解析；这些元变量应该由 Meta 层的 apply 操作创建和控制。随后 `MVarId.apply` 把规则结论与当前目标匹配，将旧目标赋值为一个含有新元变量的定理应用，并按目标顺序返回未解元变量。`replaceMainGoal` 再把这个返回列表装到旧队列尾部之前。

值得把状态变化写成两行：

:::codeBox "pseudocode"
```
metavariable context:  ?old := And.intro ?left ?right
active goal queue:     [?old, ...tail]  ->  [?left, ?right, ...tail]
```
:::

Meta 操作已经创建了 `?left` 与 `?right`，也给 `?old` 赋了值。但在 `replaceMainGoal` 运行之前，TacticM 呈现的仍是旧队列。反过来，从队列中移除一个标识符也不等于证明了它。MetaM 管理证明元变量的声明与赋值；TacticM 在这之上再加一张有序工作清单。

`Lean/Elab/Tactic/ElabTerm.lean` 中的生产级译补包装器已经短到可以直接读了：

:::codeBox "code"
```
def elabTermForApply (stx : Syntax) (mayPostpone := true) : TacticM Expr := do
  if stx.isIdent then
    match (← Term.resolveId? stx (withInfo := true)) with
    | some e => return e
    | _      => pure ()
  elabTerm stx none mayPostpone

def evalApplyLikeTactic
    (tac : MVarId → Expr → MetaM (List MVarId))
    (e : Syntax) : TacticM Unit := do
  withMainContext do
    let mut val ← instantiateMVars (← elabTermForApply e)
    if val.isMVar then
      Term.synthesizeSyntheticMVarsNoPostponing
      val ← instantiateMVars val
    let mvarIds' ← tac (← getMainGoal) val
    Term.synthesizeSyntheticMVarsNoPostponing
    replaceMainGoal mvarIds'

@[builtin_tactic Lean.Parser.Tactic.apply] def evalApply : Tactic := fun stx =>
  match stx with
  | `(tactic| apply $t) =>
      evalApplyLikeTactic
        (fun g e => g.apply e (term? := some m!"`{e}`")) t
  | _ => throwUnsupportedSyntax
```
:::

上面的源码只调整了换行，分支与操作均未删改。生产包装器先译补这个项，再实例化其中的元变量。若结果仍是元变量，它会强制执行推迟的工作，再实例化一次；于是 `.inl` 这类依赖类型信息的句法还能继续解析，并在自身位置报错。传入的 Meta 操作运行完后，包装器强制求解剩余 synthetic 元变量，最后才替换目标队列。`evalApply` 自己只负责识别 `apply $t`，再把 `MVarId.apply` 交给这个通用包装器。

`MVarId.apply` 背后的 Meta 引擎仍未拆开。刚才读的是 `MVarId.apply` 的外围；第 6 章再进入它的 Meta 核心。

# 4.7 根据目标形状选择下一步
%%%
tag := "ch04-my-step"
file := "ch04-my-step"
number := false
%%%

现在，我们已经能够组合目标检查、局部上下文搜索、最外层形状识别、直接 Meta 操作与委托。我想要一个小证明术，每次只做下面一项明示动作：

- 若有匹配的局部假设，就使用它；
- 关闭 `True`；
- 拆开 `And` 或 `Iff`；
- 若目标是函数或 `forall`，引入一个绑定项；
- 否则停下，并在错误里带上目标。

```anchor elaboration_my_step_definition
syntax "my_step" : tactic

elab_rules : tactic
  | `(tactic| my_step) => withMainContext do
      let goal ← getMainGoal
      if ← goal.assumptionCore then
        replaceMainGoal []
      else
        let target ← whnf (← instantiateMVars (← goal.getType))
        if target.isConstOf ``True then
          evalTactic (← `(tactic| trivial))
        else if target.isAppOfArity ``And 2 || target.isAppOfArity ``Iff 2 then
          evalTactic (← `(tactic| constructor))
        else
          match target with
          | .forallE .. => evalTactic (← `(tactic| intro))
          | _ => throwError "my_step does not know how to continue from target{indentExpr target}"
```

假设分支放在最前，因为它无需拆解目标便可能关闭任何形状。若搜索返回 `false`，`whnf` 会把目标规约到刚好露出弱头形的程度。因此，一个函数体以 `And` 开头的定义也能走进构造器分支；只匹配表面表达式就会漏掉它。我们不规范化整个命题，因为这棵决策树只需要最外层构造子。

其余分支委托给已有证明术。引用构造证明术句法，`evalTactic` 带着当前目标和错误行为运行它。复用 `trivial`、`constructor` 和 `intro`，便能保留它们对新目标与诊断的生产级处理，而不必在一个入门例子里再造三台 Meta 引擎。

```anchor elaboration_my_step_examples
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  my_step
  · my_step
  · my_step

example (P : Prop) : P → P := by
  my_step
  my_step
```

第一个证明里，初次调用看到 `And`，委托 `constructor`，于是得到两个活动目标。余下两次调用分别找到匹配假设。第二个证明里，弱头形露出函数目标，`intro` 创建局部假设和新目标，最后一次调用再用假设关闭它。

固定版本并没有内置的 `step` 可供逐行简化；`my_step` 是本书自己的组合。它的分支通往真实的生产机制——`assumptionCore`、`trivial`、`constructor` 和 `intro`——组合规则则由本书给出。这棵树故意有限：认不出的目标直接报错，不冒充通用自动化。

错误里包含规约后的目标，因为调度器实际检查的正是这个形状。`indentExpr` 让 Lean 把表达式作为消息数据渲染，而不是压成一条丢失结构的字符串。

# 4.8 三条已经配得上名字的路线
%%%
tag := "ch04-three-routes"
file := "ch04-three-routes"
number := false
%%%

前面的例子先用了三条实现路线，到现在才给它们命名。

操作若必须读取或编辑活动目标队列，把项译补与 Meta 操作混在一起，或协调多个阶段，就*直接在 `TacticM` 中写函数体*。`my_exact`、`my_apply` 与 `my_step` 都如此；控制权最大，也就必须自己维持元变量赋值、活动目标与错误的一致。

“接收一个 `MVarId`，返回取代它的一组 `MVarId`”正是 *`liftMetaTactic`* 接受的形状。`my_assumption` 关闭传入的主目标，交回空列表；apply 一类的 Meta 辅助函数若已按所需顺序返回目标，也可以直接接上。`liftMetaTactic` 先进入活动主目标的局部上下文，再取出主目标交给函数，最后用函数返回的目标列表替换队首。它不会替任意 Meta 计算补上生产级事务语义。

已有成熟证明术能完成操作时，译补器只需检查状态，选择或构造调用，再交给 *`evalTactic`* 运行。`my_poly_roots` 和 `my_step` 都走这里。被委托的证明术成功时，创建或关闭目标等更新直接作用于当前证明状态。普通可回退候选失败时，证明术分派器先保存失败现场，再恢复这次分派开始前的状态并尝试下一候选；若最终没有候选成功，它会恢复选中的失败现场再抛出错误。标记 `no_fallback` 的错误和意外内部异常则可以直接外抛。

三条路线没有普遍的优先次序。若用底层表达式构造器重写 `constructor`，只会暴露与 `my_step` 无关的机器；若给 `my_assumption` 中直接赋入自由变量的操作生成证明术引用，又会遮住我们想学的机制。先看操作接收什么、返回什么，再选 API。

# 4.9 追踪一次漏掉的队列更新
%%%
tag := "ch04-queue-failure"
file := "ch04-queue-failure"
number := false
%%%

从 `my_apply` 中删掉 `replaceMainGoal newGoals`，再运行同一个双前提例子：

```anchor elaboration_my_apply_without_queue
syntax "my_apply_without_queue " term : tactic

elab_rules : tactic
  | `(tactic| my_apply_without_queue $rule:term) => withMainContext do
      let rule ← Lean.Elab.Tactic.elabTermForApply rule
      let _newGoals ← (← getMainGoal).apply rule

/-- error: No goals to be solved -/
#guard_msgs (substring := true) in
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  my_apply_without_queue And.intro
  · exact hP
  · exact hQ
```

`MVarId.apply` 仍把旧元变量赋成 `And.intro ?left ?right`，可是证明术队列里仍然只有那个已经赋值、如今陈旧的队首。下一个圆点先进入自己的聚焦与收尾包装器；包装器调用 `getUnsolvedGoals`，清掉已经赋值的陈旧队首后发现活动队列为空，于是尚未执行圆点正文就报告 `No goals to be solved`。未解的 `?left` 和 `?right` 确实存在于元变量上下文中，但 TacticM 不会自动发现并把它们当成活动目标。

把那一行放回来。返回列表替换旧队首，两个圆点便依次拿到 `?left` 和 `?right`。这样一次破坏再修复，比罗列可能故障更清楚地分开了两种状态：先检查元变量赋值，再检查那张告诉下一个证明术去哪里工作的活动队列。

# 4.10 回查本章用过的 API
%%%
tag := "ch04-api-reference"
file := "ch04-api-reference"
number := false
%%%

常用动作已经具体到足以放进查阅表了。这张表只供写证明术时回查，不再复述本章。

```table
| 当前愿望 | 常用入口 | 理论归属 |
|---|---|---|
| 读取活动目标 | `getMainGoal`, `getMainTarget` | TacticM / MetaM |
| 进入它的局部现场 | `withMainContext`, `MVarId.withContext`, `getLCtx` | MetaM |
| 露出表达式可用的形状 | `instantiateMVars`, `whnf` | MetaM |
| 比较类型 | `isDefEq` | MetaM |
| 译补用户项 | `Term.elabTerm...`, `Lean.Elab.Tactic.elabTerm...` | TermElabM |
| 填充或变换证明洞 | `MVarId.assign`, Meta 证明术操作 | MetaM |
| 替换目标队列的活动队首 | `replaceMainGoal` | TacticM |
| 运行已有证明术 | `evalTactic` | TacticM |
| 接上一段单目标 Meta 程序 | `liftMetaTactic` | TacticM |
| 报告错误或消息 | `throwError`, `logInfo`, 消息数据操作 | CoreM / 译补层 |
```

表中省略了许多变体，因为本章还没让它们获得出场理由。若开始关心恢复、synthetic 元变量、目标标签或推迟译补，就回读生产级包装器，别只凭 API 名选择。

# 4.11 每次只推进一条边界
%%%
tag := "ch04-exercises"
file := "ch04-exercises"
number := false
%%%

下面的练习分别延伸不同路线。教学证明术请保留 `my_` 前缀，同时编译成功例子和刻意失败的例子，并在每个定义旁写明它支持的目标形状。

1. *给“变量”补上身份检查。* 当前读取器接受任意共同左端，只是把它叫作 `x`。先要求该表达式满足 `isFVar`，确认 `2 = x` 这样的目标会被拒绝。再扩展等式分支：若两边恰有一边是自由变量，就把自由变量作为共同项、另一边作为根，使 `x = 2 ∨ 3 = x` 也能得到 `x` 与 `#[2, 3]`；两边都是自由变量或都不是时明确拒绝。这个扩展只规范等式方向，不做代数求根。

2. *支持首项系数。* 为 `2*x^2 - 10*x + 12` 这样的非首一多项式设计接口。决定系数是从命题读取，还是由调用者提供，再生成形如 `a * ∏ (x - r)` 的因式分解。认证工作仍交给 `ring`。说明你的读取器接受哪些来源形状。

3. *按名字筛选 `my_assumption`。* 添加一个可选标识符。模式捕获值的 `getId` 给出用户写下的 `Name`；可用 `LocalContext.findFromUserName? (← getLCtx) name.getId` 查找对应的 `LocalDecl`，也可在遍历时比较 `decl.userName`。找到声明后再比较类型。名字不存在与名字存在但类型错误，应该产生不同错误。接着，比较这个直接 `TacticM` 接口与核心仍为 `MVarId → MetaM (List MVarId)` 程序的版本。

4. *按预期类型筛选。* 让调用者写一个表示所需假设类型的项，在当前上下文中译补它，再用 `isDefEq` 搜索。若成功比较之后还要做更多检查，请记录外层候选快照会从哪里开始成为必需。

5. *控制 `my_apply` 的目标顺序。* 把 `MVarId.apply` 返回的列表反转后再交给 `replaceMainGoal`，观察第一个圆点会拿到哪个前提。然后恢复原顺序，并解释为何目标顺序应以 Meta 操作的返回列表为准，不能从定理文本猜测元变量创建顺序。

6. *让 `my_step` 支持 `Exists`。* 先决定“一步”到底能诚实地做什么。只有能够形成预期的构造器应用时，`constructor` 才能露出见证与证明义务；选择见证则是另一件事。在存在量词目标上要求写 `my_step witness`，或许比凭空造一个元变量再不加解释更诚实。

7. *看穿一层命题定义。* 定义一个弱头形为 `And` 的命题，再确认 `whnf` 能走到现有分支。然后在旁边加入一道 opaque 或不可规约的边界；只报告不支持的规约后目标，不继续做无界规范化。

8. *写一个轻薄的委托型译补器。* 接收一个标志或一小段句法，检查目标，构造两种成熟证明术调用之一，再用 `evalTactic` 运行。至少加入一种“委托证明术成功却仍留下目标”的情况，从而迫使接口明确说明它是否承诺完成证明。

9. *选择扩展层。* 对下面每项需求，在宏、项译补器、证明术译补器或可复用 Meta 辅助函数中选择一种，并根据它必须读取的信息与必须返回的值说明理由：
   - 接受两种表层写法，并把它们展开成同一次证明术调用；
   - 在译补一个项时，根据预期类型推断证明项；
   - 搜索局部上下文，并给传入的目标赋值；
   - 检查活动目标队列，再重新排列目标；
   - 给 `constructor <;> assumption` 加一个不检查状态的便捷包装。

完整解答不必使用最底层路线。选择哪一层，只看它必须读取什么状态、交回什么结果。

# 4.12 归还每一项借来的能力
%%%
tag := "ch04-next-layers"
file := "ch04-next-layers"
number := false
%%%

这些例子已经把目标、局部假设、用户项和活动目标队列接到一起。借用四层操作留下的问题，下面四章各接走一类。

本章打印目标并报错时，已经借用了环境、选项、源码引用、消息、异常与核心可变状态。它们从哪里来？为什么 4.1 节的 `logInfo` 能记录结构化消息数据，`throwError` 又怎样取得有用的位置？这些都属于后续各层下方的全局编译现场，*第 5 章 CoreM* 从这里拆起。

`isDefEq` 成功后可能留下约束；*第 6 章 MetaM* 要解释一次合一成功后，为什么更大的候选若随后失败，仍可能需要外层快照。`MVarId.apply` 尚未打开的证明构造也在这一层处理。

`.inl` 有时必须等类型信息到齐才能继续；*第 7 章 TermElabM* 就从这次推迟出发，解释用户 `Syntax` 怎样在预期类型下变成 `Expr`，以及生产包装器为何要在特定位置求解或拒绝遗留义务。

漏掉一次 `replaceMainGoal`，`?left` 和 `?right` 明明存在，下一个圆点却无事可做。*第 8 章 TacticM* 就从这道接缝进入有序活动目标队列和证明术执行的保存与恢复规则。为什么给 `?old` 赋值不会把它移出队列？`replaceMainGoal`、`liftMetaTactic`、`evalTactic`、`first` 和普通证明术异常，如何保存并恢复队列与继承来的元变量上下文？`my_apply` 暴露的两种状态会在这里成为主角。

这四笔债都来自已经运行过的代码。下一章先从它们共同依赖的全局编译现场开始。
