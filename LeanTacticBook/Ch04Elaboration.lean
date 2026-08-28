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

多项式已经在命题左边，根已经在右边，`x` 则两边都有。若调用处只写一个普通的 `poly_roots`，宏无法恢复这些信息，因为它拿到的输入只是这次调用的 `Syntax`；目标变了，交给宏的句法树并不会跟着变。我们之所以走到译补这一层，只是因为想少写一个参数。

一个证明术译补器下面垫着四层计算，但若等到四层全部拆完才动手，第一个真正能读取目标的实用证明术就离得太远了。每个例子用到哪些操作，我们便先借来哪些并立刻用起来；内部机制留给第 5 至第 8 章逐层拆开。

# 4.1 问问目标自己是什么
%%%
tag := "ch04-show-target"
file := "ch04-show-target"
number := false
%%%

先从宏做不到的最小观察开始。我想要一个调用形式永远不变、消息却跟随当前目标变化的证明术。伴随示例模块已经导入本书示例环境并打开 `Lean Meta Elab Tactic`；本章片段按出现顺序累积在同一个命名空间中。

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

调用前，活动目标队列以当前证明洞 `?g` 开头，`?g` 的类型是 `P ∧ Q`。`getMainTarget` 只读取这个类型；它既不赋值 `?g`，也不替换队列。因此 `my_show_target` 返回后，活动队列仍以同一个 `?g` 开头。

在调用处，解析器仍然只为 `my_show_target` 生成一棵句法树。`macro_rules` 会返回更多 `Syntax`；`elab_rules : tactic` 则注册一段在当前证明状态中运行的 `TacticM` 计算。紧凑写法 `elab "..." : tactic => ...` 会把句法及其译补器一起注册。这里单列 `syntax`，先把句法与处理函数的分界露出来。

顺着函数体走一遍。`withMainContext` 暂时把第一个活动目标携带的局部声明设为接下来 Meta 查询的当前现场；这里先把它当作读取和显示主目标的标准护栏，4.4 再让这些声明真正参与搜索。随后 `getMainTarget` 读取目标类型。`←` 先运行这项读取，`m!` 把得到的 `Expr` 作为结构化消息数据插入消息，`logInfo` 再连同当前源码上下文把它记下；消息系统的细节留到第 5 章。函数体没有赋值目标或替换队列，所以 `constructor` 会从刚才打印的目标原样继续。

把同一个调用移到 `constructor` 的任一分支下面，它会分别打印 `P` 或 `Q`。送入译补器的句法仍然是 `my_show_target`，所以不断变化的消息直接证明：译补器已经越过了先前挡住宏的那条边界。

我们有意还没拆开 `Expr`。目前，`Expr` 就是 Lean 译补项或类型后得到的表示：名字已经解析，隐式结构可能已经补入，局部变量也已经连到局部上下文里的声明。能打印表达式，就足以说明它已经在手里。更难的问题是怎样利用它的形状。

# 4.2 去掉 `in x`
%%%
tag := "ch04-infer-variable"
file := "ch04-infer-variable"
number := false
%%%

下一个接口保留多项式和根，却删掉变量：

```anchor elaboration_poly_roots2_call
  poly_roots₂ x^2 - 5*x + 6 with 2 3
```

目标已经写着 `x = 2 ∨ x = 3`。只要能把这个结论逐层剥成等式，并确认每条等式左边都是同一个表达式，缺失的参数就已经到手了。

我们需要几个小型读取器。它们只认眼前这几种形状，不打算做通用的逻辑表达式库。

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
```

每次测试最外层形状之前，`consumeMData` 都先剥掉元数据包装。接着，`eqSides?` 接受带三个参数的 `Eq` 应用——类型与等式两边——只返回我们需要的左右两边。`rootEqualities?` 则递归打开每一个 `Or` 节点。这里的递归比只匹配一次 `A ∨ B` 更重要：`A ∨ B ∨ C` 和 `(A ∨ B) ∨ C` 都会变成同一个扁平数组；若结论只有一条等式，也会得到长度为一的数组。

最后一个读取器选取第一条等式的左边；后面若出现结构上不同的 `Expr`，就拒绝整个结论。这一版只认结构相同：两种写法即使在定义上相等，它也认不出来；选出的表达式也尚不必是自由变量。

译补器委托执行的证明脚本也必须接受同样范围的析取形状，因此最后一次化简要包含 `or_assoc`：

```anchor elaboration_poly_roots_target_core
syntax "poly_roots_target_core " term " with " term " in " term : tactic

macro_rules
  | `(tactic| poly_roots_target_core $poly:term with $roots:term in $x:term) =>
      `(tactic|
        rw [show $poly = (($roots).map (fun r => $x - r)).prod by
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] <;>
          ring] <;>
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
          mul_eq_zero, sub_eq_zero, or_assoc])
```

现在，译补器可以把两半接起来：

```anchor elaboration_poly_roots2_definition
syntax "poly_roots₂ " term " with " term:max+ : tactic

elab_rules : tactic
  | `(tactic| poly_roots₂ $poly:term with $suppliedRoots:term*) => withMainContext do
      let target ← getMainTarget
      let some (x, roots) := rootsAndVariable? (rootConclusion target)
        | throwError "poly_roots₂: expected one or more equations with structurally identical left-hand sides"
      if roots.size != suppliedRoots.size then
        throwError "poly_roots₂: the number of supplied roots does not match the target"
      let x ← Term.exprToSyntax x
      let roots : TSyntaxArray `term := suppliedRoots
      let rootList ← `(term| [$roots,*])
      evalTactic (← `(tactic| poly_roots_target_core $poly with $rootList in $x))
```

沿数据流读这段函数体。`getMainTarget` 取得目标，并且已经把 Lean 求解的元变量代进去，免得一个已有赋值的占位符把最外层的 `Iff`、`Or` 或 `Eq` 遮住。`rootConclusion` 遇到 `Iff` 就选右边。几个读取器将其展平，并返回反复出现的左边。已经测试过的核心接收的是句法参数，所以 `Term.exprToSyntax` 又把译补后的表达式转成可重新交给该核心的句法；这一步不保留原始源码，也不承诺 `Expr → Syntax → Expr` 是恒等往返。最后，一段引用把调用者给出的重复根句法装进列表，`evalTactic` 再在当前证明状态中运行生成的 `poly_roots_target_core` 调用。

`roots` 来自目标，只告诉我们识别出了多少条等式；`suppliedRoots` 来自调用处，仍是证明实际使用的列表。这一版只比较长度，不比较内容。把 `2 3` 换成 `3 2` 可以通过长度检查，但生成的因式分解顺序与命题结论不合，委托出去的证明便会失败。我们正想要这个失败。若用 `try` 包住调用，只会留下未解目标，让坏候选看起来像成功。

把这项失败固定成可运行的边界反例：

```anchor elaboration_poly_roots_wrong_order
/-- error: unsolved goals -/
#guard_msgs (substring := true) in
example (x : ℚ) : x^2 - 5*x + 6 = 0 ↔ x = 2 ∨ x = 3 := by
  poly_roots₂ x^2 - 5*x + 6 with 3 2
```

单根和不同结合方式的情形同样来自这套递归，而非两个补丁：

```anchor elaboration_poly_roots2_shapes
example (x : ℚ) : x - 2 = 0 ↔ x = 2 := by
  poly_roots₂ x - 2 with 2

example (x : ℚ) :
    x^3 - 6*x^2 + 11*x - 6 = 0 ↔ (x = 1 ∨ x = 2) ∨ x = 3 := by
  poly_roots₂ x^3 - 6*x^2 + 11*x - 6 with 1 2 3
```

还剩一个重复参数。

# 4.3 去掉 `with`
%%%
tag := "ch04-infer-roots"
file := "ch04-infer-roots"
number := false
%%%

面对这样的命题：

:::codeBox "pseudocode"
```
x^3 - 6*x^2 + 11*x - 6 = 0 ↔ x = 1 ∨ x = 2 ∨ x = 3
```
:::

右边已经给出了 `1`、`2` 和 `3`。译补器不必解三次方程，只需读出调用者已经写进目标的候选值；候选因式分解交给 `ring` 验证，表达式读取器和译补器都不实现二次或三次求根公式。

多项式来源可能出现在 `Iff` 左边，也可能是一条用于证明裸析取结论的局部等式。下面的读取器检查这两个地方：

```anchor elaboration_source_polynomial
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

遇到 `Iff`，它要求左边是一条等式，再取这条等式的左边。遇到裸结论，它会按声明进入局部上下文的顺序，从较旧的声明走向较新的声明，跳过实现细节，取沿这个方向遇到的第一条左边含有所推断自由变量的等式。这里两条来源路径的范围并不相同：`Iff` 路径可以继续携带复合的共同左端；局部上下文路径受 `x.isFVar` 限制，只支持共同左端本身就是自由变量。当前辅助函数不反转等式，不检查另一边是否为零，不比较多个候选，也不展开定义。

证明还需要另一条路线来处理裸结论：

```anchor elaboration_poly_roots_core_tactic
syntax "poly_roots_core " term " with " term " in " term : tactic

macro_rules
  | `(tactic| poly_roots_core $poly:term with $roots:term in $x:term) =>
      `(tactic|
        first
        | poly_roots_target_core $poly with $roots in $x
        | have hpoly : $poly = 0 := by assumption
          rw [show $poly = (($roots).map (fun r => $x - r)).prod by
            simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] <;>
            ring] at hpoly
          simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
            mul_eq_zero, sub_eq_zero, or_assoc] using hpoly)
```

第一条分支尝试直接证明 `Iff`。只要它失败，`first` 都会恢复状态并尝试第二条，并不先判断失败是否来自目标形状。第二条分支为裸析取结论准备：它用 `assumption` 重新搜索任意类型可与 `$poly = 0` 定义相等的局部证明，把找到的证明重写成乘积等式，再用结果证明结论。局部上下文读取器只挑出放进调用的多项式表达式；它没有把原声明的身份传给宏核心。若多个局部等式含有同一个多项式，读取器选出的多项式表达式与核心最终采用的证明可能来自不同声明。

我们还需要根列表的句法。现在这些根是表达式，不再是调用者的原始句法，因此也不能继续使用先前的重复反引用。

```anchor elaboration_mk_root_list_syntax
private def mkRootListSyntax (roots : Array Expr) : TacticM (TSyntax `term) := do
  let some firstRoot := roots[0]?
    | throwError "poly_roots: expected at least one root"
  let rootType ← inferType firstRoot
  Term.exprToSyntax (← mkListLit rootType roots.toList)
```

第一个根给出元素类型，`mkListLit` 构造译补后的列表表达式，`exprToSyntax` 再把结果变成宏核心能够接收的项。上游虽已拒绝空结论，这里仍显式报错，保证这个辅助函数单独调用时也会拒绝空列表。

公开接口终于缩成了一个词：

```anchor elaboration_poly_roots_public
syntax "poly_roots" : tactic

elab_rules : tactic
  | `(tactic| poly_roots) => withMainContext do
      let target ← getMainTarget
      let some (x, roots) := rootsAndVariable? (rootConclusion target)
        | throwError "poly_roots: expected one or more equations with structurally identical left-hand sides"
      let some poly := sourcePolynomial? target x (← getLCtx)
        | throwError "poly_roots: expected an equation source in the target or local context"
      let poly ← Term.exprToSyntax poly
      let x ← Term.exprToSyntax x
      let rootList ← mkRootListSyntax roots
      evalTactic (← `(tactic| poly_roots_core $poly with $rootList in $x))
```

`getLCtx` 返回主目标处活动的局部声明。译补器从目标读取候选根，在目标或局部上下文中寻找多项式来源，然后重新拼出我们已有核心会证明的显式调用。

现在两种形式都可以用了：

```anchor macro_poly_roots_cubic
example (x : ℚ) :
    x^3 - 6*x^2 + 11*x - 6 = 0 ↔
      x = 1 ∨ x = 2 ∨ x = 3 := by
  poly_roots
```

```anchor elaboration_poly_roots_local_example
example (x : ℚ) (h : x^2 - 5*x + 6 = 0) : x = 2 ∨ x = 3 := by
  poly_roots
```

再用两个紧邻契约的调用钉住现有范围：目标可以直接写成已经因式分解的双条件；局部来源也可以只推出一个根。

```anchor elaboration_poly_roots_contract_regression
example (x : ℚ) : (x - 2) * (x - 3) = 0 ↔ x = 2 ∨ x = 3 := by
  poly_roots

example (x : ℚ) (h : x - 2 = 0) : x = 2 := by
  poly_roots
```

换成四次多项式，译补器和接口都不必改变。根已经写在命题里；列表变长交给下层的成熟证明术处理。

这个教学证明术支持由 `∏ (x - r)` 生成的首一因式分解。`2*x^2 - 10*x + 12` 这样的多项式，要么需要在生成的乘积里加入首项系数，要么先做规范化，当前核心才能验证它。候选错了，委托出去的证明仍应直接报错。

重复参数已经消失。接着把同样的译补操作用到普通证明目标上。

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

已有成熟证明术能完成操作时，译补器只需检查状态，选择或构造调用，再交给 *`evalTactic`* 运行。`poly_roots` 和 `my_step` 都走这里。被委托的证明术成功时，创建或关闭目标等更新直接作用于当前证明状态。普通可回退候选失败时，证明术分派器先保存失败现场，再恢复这次分派开始前的状态并尝试下一候选；若最终没有候选成功，它会恢复选中的失败现场再抛出错误。标记 `no_fallback` 的错误和意外内部异常则可以直接外抛。

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

1. *改进 `poly_roots` 的诊断。* 修改 `sourcePolynomial?`：对每个候选等式的右边使用 `rhs.nat? == some 0`，只接受这种结构上的数值字面量零；这项检查不承诺识别所有定义等于零的表达式。若没有候选通过，公开译补器就在整个调用处报告来源错误。把 `hBad : x + 1 = 1` 放在 `hGood : x^2 - 5*x + 6 = 0` 之前，并以 `x = 2 ∨ x = 3` 为目标：由于循环从较旧的声明走向较新的声明，未检查右边的实现会先误选 `x + 1` 并在委托证明中失败，正确实现才会跳过它并接受 `hGood`。再加入只有非零右边的反例，确认执行不会走到 `ring`。这改变的是识别，不是数学，也不要求核心记住某个声明身份。

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

本章打印目标和报错时，已经借用了环境、选项、源码引用、消息、异常与核心可变状态。它们从哪里来？为什么 `logInfo` 能记录结构化消息数据，`throwError` 又怎样取得有用的位置？这些都属于后续各层下方的全局编译现场，*第 5 章 CoreM* 从这里拆起。

`isDefEq` 成功后可能留下约束；*第 6 章 MetaM* 要解释一次合一成功后，为什么更大的候选若随后失败，仍可能需要外层快照。`MVarId.apply` 尚未打开的证明构造也在这一层处理。

`.inl` 有时必须等类型信息到齐才能继续；*第 7 章 TermElabM* 就从这次推迟出发，解释用户 `Syntax` 怎样在预期类型下变成 `Expr`，以及生产包装器为何要在特定位置求解或拒绝遗留义务。

漏掉一次 `replaceMainGoal`，`?left` 和 `?right` 明明存在，下一个圆点却无事可做。*第 8 章 TacticM* 就从这道接缝进入有序活动目标队列和证明术执行的保存与恢复规则。为什么给 `?old` 赋值不会把它移出队列？`replaceMainGoal`、`liftMetaTactic`、`evalTactic`、`first` 和普通证明术异常，如何保存并恢复队列与继承来的元变量上下文？`my_apply` 暴露的两种状态会在这里成为主角。

宏之后引入的计算栈，现在每一层都有了实际工作：

:::codeBox "pseudocode"
```
CoreM     : global compilation context, messages, exceptions, core state
MetaM     : expressions, local context, metavariables, proof construction
TermElabM : user terms, expected types, postponement, synthetic obligations
TacticM   : ordered active goals and tactic recovery policy
```
:::

四层沿同一条计算栈叠起来，并非四套互不相干的编程语言。每往外一层，计算都会加入自己的当前上下文或状态，同时保留下层能力。我们先用组装好的整台机器，让 `poly_roots` 只说调用者真正想说的话。现在再逐层拆开，每一层的问题都已有来处。
