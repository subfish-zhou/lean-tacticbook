import VersoManual
import LeanTacticBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "examples"
set_option verso.exampleModule "Examples.Ch04Elaboration"

#doc (Manual) "先写出能看见目标的证明术" =>
%%%
file := "Ch04Elaboration"
tag := "ch04-elaboration"
%%%

> *本章目标*：先不拆开 CoreM、MetaM、TermElabM 和 TacticM 的全部内部结构，直接写出能够读取目标、读取局部上下文、译补用户输入、关闭目标、产生新目标并调用现有 tactic 的简单证明术译补器。

Ch03 最后留下的不是一道抽象思考题，而是一个很实际的麻烦。命题里明明已经写着变量和候选根，`poly_roots` 的调用者却还要再抄一遍：

:::codeBox "code"
```
poly_roots₂ x^2 - 5*x + 6 with 2 3 in x
```
:::

普通宏只收到这一行的 Syntax，看不到待证目标，所以它确实没法自己删掉 `in x` 和 `with 2 3`。我们当然可以先讲完 CoreM、MetaM、TermElabM 和 TacticM，再回来补这个窟窿；但你很可能等不到那时，就已经去自己的研究项目里手写 tactic 了。

这一章先走另一条路。后面四章的常用接口，我们按眼前任务借一点，用一点。关键借用都会说明它此刻能保证什么，不能保证什么；内部结构等读者亲手遇到问题以后再偿还。这样不是省略理论，而是先让理论有债主。

# 先偷看一眼目标
%%%
tag := "elaboration-show-target"
%%%

宏和证明术译补器的调用都从 Syntax 开始，但后者运行时已经进入证明现场。先写一个只打印目标的版本：

```anchor elaboration_show_target
syntax "my_show_target" : tactic

elab_rules : tactic
  | `(tactic| my_show_target) => withMainContext do
      logInfo m!"{← getMainTarget}"

set_option linter.unusedTactic false in
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  my_show_target
  constructor
  · exact hP
  · exact hQ
```

`syntax` 仍然只声明表面写法。变化发生在 `elab_rules : tactic`：匹配成功后，右边运行的是 `TacticM Unit`，不再是返回新 Syntax 的 `MacroM Syntax`。

`withMainContext` 把当前主目标对应的局部上下文装进 Meta 层；`getMainTarget` 随后取出目标的 `Expr`。同一个 `my_show_target` 放在不同 theorem 里，调用 Syntax 一字不变，读到的目标却会变化。这就是上一章普通宏缺少的那份信息。

这里只借用了 `Expr` 这个名字，还没有解释它的构造子。眼前只需知道：Syntax 保存用户写下的表面结构；Expr 已经经过名字解析、隐式参数补全和类型检查，里面的常量与变量都有确定身份。Ch06 会系统拆开它。

# 先省掉 `in x`
%%%
tag := "elaboration-poly-roots-infer-variable"
%%%

回到 `poly_roots`。目标的右侧析取已经写着：

:::codeBox "code"
```
x = 2 ∨ x = 3
```
:::

如果证明术能读取目标，就能递归拆开析取，检查这些等式的左边是否是同一个 Expr；在当前例子中，那一项正好是变量 `x`。真正负责读取的 helper 不长，先把它完整摊开：

```anchor elaboration_poly_roots_readers
private def eqSides? (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``Eq 3 then
    let args := e.getAppArgs
    some (args[1]!, args[2]!)
  else
    none

private partial def rootEqualities? (e : Expr) : Option (Array (Expr × Expr)) :=
  let e := e.consumeMData
  if e.isAppOfArity ``Or 2 then
    let args := e.getAppArgs
    return (← rootEqualities? args[0]!) ++ (← rootEqualities? args[1]!)
  else
    return #[← eqSides? e]

private def rootsAndVariable? (e : Expr) : Option (Expr × Array Expr) := do
  let equalities ← rootEqualities? e
  let (x, firstRoot) ← equalities[0]?
  let mut roots := #[firstRoot]
  for (x', root) in equalities[1...*] do
    if x' != x then failure
    roots := roots.push root
  return (x, roots)

private def rootConclusion (target : Expr) : Expr :=
  let target := target.consumeMData
  if target.isAppOfArity ``Iff 2 then target.getAppArgs[1]! else target

private def sourcePolynomial? (target : Expr) (x : Expr) (lctx : LocalContext) : Option Expr := do
  let target := target.consumeMData
  if target.isAppOfArity ``Iff 2 then
    return (← eqSides? target.getAppArgs[0]!).1
  for decl in lctx do
    if !decl.isImplementationDetail then
      if let some (poly, _) := eqSides? decl.type then
        if x.isFVar && poly.containsFVar x.fvarId! then return poly
  failure
```

`rootConclusion` 决定从双条件右侧还是整个目标开始；`rootEqualities?` 把 Or 树压成等式数组；`rootsAndVariable?` 从数组中取公共左式和所有右式；`sourcePolynomial?` 才在目标或局部上下文中找来源式。调用者现在可以只保留多项式和候选根：

```anchor macro_poly_roots_infer_variable
syntax "poly_roots₂ " term " with " term:max+ : tactic

elab_rules : tactic
  | `(tactic| poly_roots₂ $poly:term with $suppliedRoots:term*) => withMainContext do
      let target ← instantiateMVars (← getMainTarget)
      let some (x, roots) := rootsAndVariable? (rootConclusion target)
        | throwError "poly_roots₂: expected a disjunction of equations with one common variable"
      if roots.size != suppliedRoots.size then
        throwError "poly_roots₂: the number of supplied roots does not match the target"
      let x ← Term.exprToSyntax x
      let roots : TSyntaxArray `term := suppliedRoots
      let rootList ← `(term| [$roots,*])
      evalTactic (← `(tactic| poly_roots_core $poly with $rootList in $x))

example (x : ℚ) (h : x^2 - 5*x + 6 = 0) : x = 2 ∨ x = 3 := by
  poly_roots₂ x^2 - 5*x + 6 with 2 3
```

这里从上往下只做了六件事。

1. `getMainTarget` 读取目标，`instantiateMVars` 把已经确定的元变量替换进去。
2. `rootConclusion` 在双条件命题中取右边，否则直接使用整个目标。
3. `rootsAndVariable?` 递归展平整棵 `Or`，再检查叶子是不是等式。
4. 所有等式左边必须是结构相同的 Expr；这个 helper 的名字里虽有 Variable，却没有额外检查公共左式一定是自由变量。根的数量还要与调用者给出的数量一致。
5. `Term.exprToSyntax` 把公共左式转回 Syntax，因为我们准备调用上一章已经写好的宏核心。
6. `evalTactic` 运行生成的 `poly_roots_core ... in x`。

这个译补器没有重新证明多项式定理。它只读取证明现场，再把缺失参数补回旧接口。它甚至只比较了根的数量，没有在这里比较调用者写的根与目标中的根；把顺序写反会越过这道局部检查，然后在真正的证明步骤中失败：

```anchor elaboration_poly_roots_wrong_order
/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example (x : ℚ) (h : x^2 - 5*x + 6 = 0) : x = 2 ∨ x = 3 := by
  poly_roots₂ x^2 - 5*x + 6 with 3 2
```

真正的因式分解仍由 `ring` 验证，根析取仍由 `mul_eq_zero` 与 `sub_eq_zero` 产生。

# 再省掉 `with`
%%%
tag := "elaboration-poly-roots-infer-all"
%%%

目标已经列出了候选根，`with 2 3` 也可以省掉。双条件命题左边可以直接充当来源式；若目标只有根析取，当前 helper 就在局部上下文中寻找一个等式，其左边含有刚才读到的自由变量：

```anchor macro_poly_roots_infer_all
syntax "poly_roots" : tactic

elab_rules : tactic
  | `(tactic| poly_roots) => withMainContext do
      let target ← instantiateMVars (← getMainTarget)
      let some (x, roots) := rootsAndVariable? (rootConclusion target)
        | throwError "poly_roots: expected a disjunction of equations with one common variable"
      let some poly := sourcePolynomial? target x (← getLCtx)
        | throwError "poly_roots: expected a polynomial equation in the target or local context"
      let poly ← Term.exprToSyntax poly
      let x ← Term.exprToSyntax x
      let rootList ← mkRootListSyntax roots
      evalTactic (← `(tactic| poly_roots_core $poly with $rootList in $x))

example (x : ℚ) (h : x^2 - 5*x + 6 = 0) : x = 2 ∨ x = 3 := by
  poly_roots
```

三次和四次调用也只剩名字：

```anchor macro_poly_roots_cubic
example (x : ℚ) :
    x^3 - 6*x^2 + 11*x - 6 = 0 ↔
      x = 1 ∨ x = 2 ∨ x = 3 := by
  poly_roots
```

```anchor macro_poly_roots_quartic
example (x : ℚ) :
    x^4 - 10*x^3 + 35*x^2 - 50*x + 24 = 0 ↔
      x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by
  poly_roots
```

这里必须把“省略根参数”和“自动求根”分开。这个程序没有从系数算出 `2` 和 `3`；它从待证命题中读出候选根，再让后面的证明步骤验证。目标里若把 `3` 写成 `4`，程序仍会生成同样形状的脚本，随后由 `ring` 失败。要从系数真正计算根，需要识别一元多项式、提取系数、选择求根算法并处理定义域，那已经是另一个符号求解器。

`rootEqualities?` 接受单个等式，也会把左右两边的 Or 递归压平；公开入口就应兑现这两个承诺。宏核心中的化简因此显式使用 `or_assoc` 统一析取结合方式，并用 `<;>` 让 `simp` 已经关闭目标时不再强行执行一个多余的 `ring`。下面四个回归例分别钉住单根、已因式分解输入、左结合析取和局部单根来源：

```anchor elaboration_poly_roots_contract_regression
example (x : ℚ) : x - 2 = 0 ↔ x = 2 := by
  poly_roots

example (x : ℚ) : (x - 2) * (x - 3) = 0 ↔ x = 2 ∨ x = 3 := by
  poly_roots

example (x : ℚ) :
    x^3 - 6*x^2 + 11*x - 6 = 0 ↔ (x = 1 ∨ x = 2) ∨ x = 3 := by
  poly_roots

example (x : ℚ) (h : x - 2 = 0) : x = 2 := by
  poly_roots
```

修完这两处实现缺口以后，helper 的剩余契约仍然比名称窄。它要求所有根等式的左边在 Expr 结构上相同，却不把公共左式验证成自由变量；处理双条件时，它直接拿左边等式的左侧当来源式，没有核对等式右侧一定是零。处理局部上下文时，它只接受公共左式恰为自由变量的情况，遇到多个候选会静默取先碰到的一个。最后，宏核心只验证候选根给出的首一因式乘积；非首一情形还要另外处理首项系数并证明它非零。若继续扩展这个 tactic，首先要把这些条件变成显式检查或公开参数，而不是把它们藏在 helper 名称后面。

# 从局部上下文里拿一个现成证明
%%%
tag := "elaboration-my-assumption"
%%%

`poly_roots` 很专用。换一个每个人都会遇到的问题：目标已经作为某个局部假设摆在眼前，证明术应当直接使用它。

教学实现统一用 `my_` 前缀。`my_assumption` 先自己走一遍最短路径：

```anchor elaboration_my_assumption
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
      liftMetaTactic fun goal => goal.withContext do
        goal.checkNotAssigned `my_assumption
        let some fvarId ← myFindLocalDeclWithType? (← goal.getType)
          | throwError "my_assumption failed"
        goal.assign (mkFVar fvarId)
        return []

example (P : Prop) (h : P) : P := by
  my_assumption
```

`goal` 是当前目标的 `MVarId`。`goal.withContext` 进入它自己的局部上下文；helper 逆序寻找一个类型与目标定义等价的局部声明，找到后返回 `FVarId`。`mkFVar fvarId` 构造对该假设的引用，`goal.assign` 用这个证明给目标赋值。最后返回空列表，因为旧目标已经解决，不需要加入任何新目标。

## 真实的 `assumption`

Lean 4.32.2 的生产实现没有躲在一座巨大的框架后面。下面摘自 `Lean/Meta/Tactic/Assumption.lean`，只删掉了文档注释：

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

def _root_.Lean.MVarId.assumptionCore (mvarId : MVarId) : MetaM Bool :=
  mvarId.withContext do
    mvarId.checkNotAssigned `assumption
    match (← findLocalDeclWithType? (← mvarId.getType)) with
    | none => return false
    | some fvarId => mvarId.assign (mkFVar fvarId); return true

def _root_.Lean.MVarId.assumption (mvarId : MVarId) : MetaM Unit :=
  unless (← mvarId.assumptionCore) do
    throwTacticEx `assumption mvarId
```
:::

它比 `my_assumption` 多保留了一个“不抛错，只报告成功与否”的 `assumptionCore`，方便其他 tactic 把它当候选。`Lean/Elab/Tactic/BuiltinTactic.lean` 中注册到 tactic 层的外壳更短：

:::codeBox "code"
```
@[builtin_tactic Lean.Parser.Tactic.assumption] def evalAssumption : Tactic := fun _ =>
  liftMetaTactic fun mvarId => withAssignableSyntheticOpaque do mvarId.assumption; pure []
```
:::

`withAssignableSyntheticOpaque` 让它也能处理 `refine` 留下的某些 synthetic opaque 目标。现在知道它补了一条生产边界就够了；synthetic metavariable 为什么分 opaque 与普通形式，Ch07 再讲。重要的是，读者刚刚发明的 `my_assumption` 与真实源码只有这点工程距离。

# 把用户写的 term 当成证明
%%%
tag := "elaboration-my-exact"
%%%

`my_assumption` 自己从局部上下文挑证明。若调用者已经写出一个 term，我们还要把 Syntax 译补成 Expr，再交给目标：

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
```

这里的 `proof` 先后指两种对象：pattern 捕获的是 Syntax，`elabTermEnsuringType` 返回的是 Expr。`some target` 把当前目标作为预期类型传给项译补器，所以 `And.intro hP hQ` 中省略的隐式命题参数可以从目标与实参类型中补出。若译补得到的项不是目标要求的类型，错误在赋值前就会报告。

完整的项译补不是 `Syntax → Expr` 这么简单：预期类型会向内传播，有些约束要延期，有些洞会变成 synthetic metavariable。眼前只借用一个高层契约：给定 Syntax 与预期类型，这个接口要么产生满足该类型的 Expr，要么在用户输入位置失败。

内置 `exact` 还会用 `closeMainGoalUsing` 包住这段过程：候选失败时恢复证明状态，并检查本次译补新建的元变量是否都已解决。`my_exact` 故意没复制这层事务性外壳，所以它只适合当前受控例子，不能冒充生产 `exact`。

# 应用定理以后，目标为什么变多
%%%
tag := "elaboration-my-apply"
%%%

`exact` 成功后没有目标，`apply` 成功后通常会留下前提。先写一个受控的教学版：

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

`MVarId.apply` 给旧目标赋值，同时为尚未解决的参数建立新元变量，并把需要交还给用户的那些洞返回为 `List MVarId`。但“内存里出现了新洞”和“这些洞出现在 tactic 的活动目标队列里”是两件事，所以最后还要 `replaceMainGoal newGoals`。

## 真实 `apply` 的译补外壳

生产版的 Meta 核心很复杂，外壳却适合现在阅读。下面摘自 `Lean/Elab/Tactic/ElabTerm.lean`；关于 `.inl` 的长注释暂时删去，代码保持原样：

:::codeBox "code"
```
def evalApplyLikeTactic (tac : MVarId → Expr → MetaM (List MVarId)) (e : Syntax) : TacticM Unit := do
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
  | `(tactic| apply $t) => evalApplyLikeTactic (fun g e => g.apply e (term? := some m!"`{e}`")) t
  | _ => throwUnsupportedSyntax
```
:::

真实实现为什么不直接把目标当成普通 expected type？例如 `apply .inl` 需要根据上下文解析点记法，却又不能像 `exact` 那样要求整个项已经具有目标类型。延期项何时强制处理、隐式参数怎样生成、`MVarId.apply` 怎样统一结论与目标，这些问题已经露出来了，Ch06 和 Ch07 会分别拆开。

# 把几种现场信息接成一步
%%%
tag := "elaboration-my-step"
%%%

最后写一个教学 decision tree。固定工具链中没有名为 `step` 的内置 tactic，所以它叫 `my_step`，不能冒充生产源码的缩小版：

```anchor elaboration_my_step
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

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  my_step
  · my_step
  · my_step

example (P : Prop) : P → P := by
  my_step
  my_step
```

它先尝试真实的 `assumptionCore`。失败后，`whnf` 只把目标最外层规约到可辨认形态；`True` 交给 `trivial`，合取与双条件交给 `constructor`，函数或 forall 目标执行一次 `intro`。这里没有重新实现这些 tactic，而是根据目标外形把任务交给已经成熟的入口。

`my_step` 的用途是把本章能力接到一起：读目标、进入局部上下文、尝试 Meta 操作、观察 Expr 外形、生成 tactic Syntax、运行已有 tactic、在无路可走时带着目标报错。它不是生产级自动化；真实的搜索还要处理透明度、候选回滚、进展检查、目标排序和循环。

# 三条最常用的接线方式
%%%
tag := "elaboration-three-routes"
%%%

现在再回头看，前面的程序用了三种接法。

`my_show_target`、`my_exact`、`my_apply` 和 `my_step` 直接运行 `TacticM`，适合既读取证明现场又控制活动目标的程序。`my_assumption` 的核心更简单：给它一个目标，它在 `MetaM` 中解决目标并返回替代目标列表，所以用 `liftMetaTactic` 接入队列。`poly_roots` 与 `my_step` 还使用 `evalTactic`，把生成的 tactic Syntax 交给现有译补器执行。

没有一条路线普遍更好。若已有 tactic 已经做对了困难部分，`evalTactic` 可以避免复制语义；若核心天然是 `MVarId → MetaM (List MVarId)`，`liftMetaTactic` 最薄；若程序需要自己安排多个目标和不同阶段的 API，直接写 `TacticM` 更清楚。

# 急用 API 回查表
%%%
tag := "elaboration-api-table"
%%%

```table
|| 现在想做什么 || 常用入口 || 后面正式解释
| 取得当前目标 | `getMainGoal`、`getMainTarget` | Ch06 MetaM、Ch08 TacticM
| 进入目标的局部现场 | `withMainContext`、`getLCtx` | Ch06 MetaM
| 替换已确定的元变量 | `instantiateMVars` | Ch06 MetaM
| 暴露目标最外层 | `whnf` | Ch06 MetaM
| 比较类型 | `isDefEq` | Ch06 MetaM
| 把用户 term 译补成 Expr | `elabTerm...` | Ch07 TermElabM
| 给目标赋值 | `MVarId.assign` | Ch06 MetaM
| 用定理产生新目标 | `MVarId.apply` | Ch06 MetaM
| 替换活动目标 | `replaceMainGoal` | Ch08 TacticM
| 运行已有 tactic | `evalTactic` | Ch08 TacticM
| 接入单目标 Meta 程序 | `liftMetaTactic` | Ch08 TacticM
| 报错与输出消息 | `throwError`、message API | Ch05 CoreM
```

这张表是急用工具，不是十二项同等重要的新知识。前面的例子已经给它们安排了位置，读者现在可以按自己的研究需求回查。

# 失败时先看哪一层
%%%
tag := "elaboration-failures"
%%%

证明术译补器出错以后，先判断状态走到了哪里。

若 pattern 没匹配，当前译补器根本没有接管输入；若 term 译补失败，用户 Syntax 还没有变成可用 Expr；若 `isDefEq` 或 `apply` 在候选中修改了元变量，失败后的恢复策略会决定下一个候选看见什么；若 Meta 操作已经产生新洞却没有更新 goals，证明状态里有元变量，编辑器却不会把它们都交给用户；若 `evalTactic` 成功返回但仍有目标，这可能正是被调用 tactic 的正常行为。

本章只要求你在代码中把这些层分开，不要求现在实现完整回滚器。Ch06 会讲 Meta state 的保存与恢复，Ch08 再讲 tactic 候选为什么还要恢复活动目标队列。

# 本章练习

1. 给 `my_assumption` 增加一个可选 ident，只允许使用指定名字的局部假设；比较这与内置 `assumption` 的用途。
2. 让 `my_exact` 在失败时把当前目标和用户项同时放进错误信息，检查错误位置是否仍落在用户输入上。
3. 给 `my_apply` 设计一个会产生三个新目标的例子，预测并验证目标顺序。
4. 给 `my_step` 增加 `Exists` 分支。调用者还需要提供什么信息，才能构造 witness？若没有这份信息，不要偷偷猜。
5. 写一个只用 `evalTactic` 编排现有 tactic 的译补器，再写一个 `liftMetaTactic` 版本；比较两者分别复制了多少语义。
6. 判断下列需求应该写宏还是证明术译补器：调用形式固定，但要根据目标 head symbol、局部假设类型或定义等价选择行为。逐项说明所需信息来自 Syntax 还是证明现场。

# 接下来为什么还要讲四个 Monad
%%%
tag := "elaboration-debt-map"
%%%

我们已经借来了足够多的接口，可以在研究项目里写一个简单的目标驱动 tactic。借来的东西也留下了四组具体问题。

Ch05 讲 CoreM：环境、options、消息和异常从哪里来，失败为什么会停下后续计算。Ch06 讲 MetaM：Expr、局部上下文、元变量、定义等价和候选恢复怎样工作。Ch07 讲 TermElabM：Syntax 怎样在 expected type 下变成 Expr，为什么有些信息必须延期。Ch08 讲 TacticM：已经赋值的目标与活动 goals 队列为什么分开，多个 tactic 候选怎样恢复现场。

这四章不是回头补一套与实践无关的基础理论。`my_assumption`、`my_exact`、`my_apply` 和 `my_step` 已经把问题摆在桌上；后面只是逐层把答案打开。
