import VersoManual
import LeanTacticBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "examples"
set_option verso.exampleModule "Examples.Ch06MetaM"

#doc (Manual) "MetaM：在局部上下文中改写表达式" =>
%%%
file := "Ch06MetaM"
tag := "ch06-metam"
%%%

> *本章目标*：解释 `rw [h]` 为什么不是文字替换。我们先把目标看成一个待填的证明洞，再逐步引入局部变量、表达式树和洞的赋值，最后亲眼看到改写器构造“旧目标等于新目标”的证明。
>
> *版本基准*：Lean `leanprover/lean4:v4.32.2`，Mathlib revision `905b95818eb3`。源码签名和调用链按这一版本说明。

# 概述：从文件现场进入证明现场
%%%
tag := "ch06-overview"
file := "ch06-overview"
%%%

CoreM 知道当前文件已经声明了什么，却还不足以解释一条具体证明里的 `x`、`h` 和待证目标。定理参数只在自己的局部作用域内存在；证明进行到一半时，还会出现暂时没有答案的洞。它们不是 Environment 中的全局常量，也不能靠打印名称来辨认。

MetaM 在 CoreM 之上增加了一间“证明工作室”。这间工作室里最重要的对象有四种：

| 对象 | 第一遍应当怎样理解 |
|---|---|
| `Expr` | 已经译补的表达式树，常量与变量身份已经确定 |
| local context | 当前证明位置可以使用的局部声明，如 `x : Nat`、`h : x = 3` |
| metavariable | 尚待填入表达式或证明的洞，内部由 `MVarId` 标识 |
| metavariable context | 记录每个洞的类型、创建现场和当前赋值的状态 |

因此，Meta 程序通常不是把一串文字改成另一串文字。它读取局部上下文和 Expr，创建或检查证明洞，调用类型推断与定义等价判断，最后构造能交给内核检查的 Expr。界面上看见“目标变了”，只说明显示内容发生了变化；要让旧目标真正成立，还必须提供一份连接旧目标和新目标的证明。

本章会用改写作为贯穿案例，但不会一上来要求读者理解实现。先观察改写器应当交出什么，再补齐 `Expr`、局部变量和 metavariable 的词汇；随后学习如何进入某个洞的局部上下文、怎样给洞赋值；这些准备完成后，才把 `MVarId.rewrite` 与 `replaceTargetEq` 接成完整的数据流。Ch08 才负责多个活动目标的排列，本章只关心每个洞本身的语义和赋值。


给定 `h : x = y` 和目标 `x + 1 = y + 1`，把字符 `x` 换成 `y` 看似足够。这个办法很快会出错：同名变量可能来自不同的局部作用域，替换也可能穿过依赖类型和 binder。Lean 不能凭打印出来的文字判断变量身份。

还有第二个问题。界面把目标显示成新文字，并不等于旧目标已经获得证明。内核最终要检查一个普通证明项。因此，可靠的改写至少要交出两样东西：替换后的新命题，以及一份说明旧命题与新命题相等的证明。

# 先观察改写器交出的三样东西
%%%
tag := "ch06-s01"
%%%

本章实现一条观察用证明术 `rw_xray`。第一遍不读实现，只看它打印什么：改写前的目标、改写后的目标，以及连接两者的等式证明。它省略位置选择和局部假设改写等完整前端功能。

```anchor metam_rw_xray_use
example (x y : Nat) (h : x = y) : x + 1 = y + 1 := by
  rw_xray h
  rfl
```

这段证明中，`rw_xray h` 把目标改成自反等式，下一行 `rfl` 才关闭新目标。构建日志还会显示负责运输目标的证明类型。

下面给出完整教学实现。代码里的 `MVarId` 是“证明洞的内部编号”，`Expr` 是“已经译补并带有变量身份的表达式树”，side goal 是改写定理额外留下的待证条件。三者都会在使用处展开；此刻只沿日志读数据流：

```anchor metam_rw_xray
elab "rw_xray " t:term : tactic => do
  let g ← getMainGoal
  let target ← g.getType
  let heq ← elabTerm t none
  let heqType ← inferType heq
  logInfo m!"rewrite theorem type:{indentExpr heqType}"
  logInfo m!"target before:{indentExpr target}"
  let r ← g.rewrite target heq
  logInfo m!"target after:{indentExpr r.eNew}"
  logInfo m!"equality proof type:{indentExpr (← inferType r.eqProof)}"
  logInfo m!"side goals: {r.mvarIds.length}"
  let g' ← g.replaceTargetEq r.eNew r.eqProof
  replaceMainGoal (g' :: r.mvarIds)
```

先把调用链压成三段：

:::codeBox "pseudocode"
```
读取：取得当前证明洞及其目标表达式
→ 计算：用 h 得到新目标、运输证明和附加条件
→ 提交：用新证明洞承接新目标，并把待证条件排进队列
```
:::

中间的“计算”是本章主角。它需要知道局部变量的类型，也需要创建和赋值证明洞。Lean 把承载这些操作的计算层叫作 `MetaM`。最后的“提交”还涉及活动目标的排列，属于 Ch08 才讲的 `TacticM`；本章只把它当作两行外壳。

`rw_xray` 没有复刻 Lean 自带的完整前端。

`rewriteTarget` 还使用 `Term.withSynthesize`。`elabRewrite` 处理 occurs check，过滤旧 metavariable，并译补改写 theorem。

`finishElabRewrite` 过滤已解决的 side goals，再把 proposition goals 调整为 synthetic opaque。遇到裸 definition 名时，前端还可能退回对应的 equation theorem。

`rw_xray` 只保留 theorem Expr 进入 `MVarId.rewrite`，再由 `replaceTargetEq` 提交结果的主干步骤。

# 为什么全局环境还不够
%%%
tag := "ch06-s02"
%%%

CoreM 能查询全局声明，但目标中的 `x` 和假设 `h` 不是全局声明。它们只在当前证明的局部作用域内有效；证明洞的类型和赋值也会随着算法推进而改变。MetaM 因此在 CoreM 上再加两份现场。

锁定版本中的定义形状如下：

:::codeBox "code"
```
abbrev MetaM :=
  ReaderT Meta.Context <|
  StateRefT Meta.State <|
  CoreM
```
:::

CoreM 的 Environment、Options、MessageLog 和异常通道仍在下层。MetaM 新增：

- `Meta.Context`：保存当前局部声明等只读信息。局部声明组成 local context（局部上下文）；
- `Meta.State`：保存证明洞及其赋值等会变化的信息。记录这些洞的表叫作 metavariable context（元变量上下文，简称 mctx）。

本章最常用的两份数据是：

:::codeBox "pseudocode"
```
Meta.Context.lctx    当前局部声明
Meta.State.mctx      元变量声明和赋值
```
:::

局部上下文保存 `x : Nat`、`h : x = 3` 这类声明。mctx 可以先记录 `?m : Nat`，表示“这里还缺一个 `Nat`”；找到答案后再记录 `?m := 3`。问号不是字符串命名习惯，而是在提醒读者：这个位置仍待赋值。

# `Expr`：带变量身份的表达式树
%%%
tag := "ch06-s03"
%%%

Syntax 保存用户写下的结构。经过译补后，Lean 得到 `Expr`：一棵已经解析了常量、局部变量和绑定关系的表达式树。`Expr` 不是目标的打印字符串。改写器在树上识别同一个局部变量，因此不会把另一个作用域中碰巧也叫 `x` 的变量换掉。

第一遍只需要两种观察：一个函数应用怎样储存在树中，变量节点怎样指向自己的声明。其余构造等用到时再引入。

## 多参数应用为什么形成一条 spine
%%%
tag := "ch06-s04"
%%%

Lean 的底层应用节点一次只接一个参数，所以 `f x y` 实际是 `(f x) y`。从最外层应用一路向左走到 `f`，再把沿途参数收集起来，这条链叫 application spine（应用脊柱）。目标 `x + y = y + x` 展开后可读成 `@Eq Nat (Nat.add x y) (Nat.add y x)`：

```anchor metam_expr_spine
elab "inspect_main_target" : tactic => withMainContext do
  let target ← (← getMainGoal).getType
  let fn := target.getAppFn
  let args := target.getAppArgs
  logInfo m!"target:{indentExpr target}"
  logInfo m!"application head: {fn}"
  logInfo m!"number of arguments: {args.size}"

example (x y : Nat) : x + y = y + x := by
  inspect_main_target
  exact Nat.add_comm x y
```

日志显示应用头是 `@Eq`，参数是类型、左端和右端。Meta 算法常先拆开 spine，再根据头常量决定接下来的处理方式。只匹配最外层 `.app` 会丢失多参数应用的整体结构。

## 三种变量各自指向哪里
%%%
tag := "ch06-s05"
%%%

| 构造 | 含义 | 引用位置 |
|---|---|---|
| `Expr.fvar id` | 局部上下文中的声明 | `FVarId` 指向 local declaration |
| `Expr.bvar i` | binder 中的 de Bruijn index | 只在包含它的 binder 内有意义 |
| `Expr.mvar id` | 尚待赋值的表达式洞 | `MVarId` 指向 mctx declaration |

free variable（自由变量）指向局部上下文中的声明；bound variable（绑定变量）指向包住它的 binder；metavariable（元变量）指向 mctx 中的待填洞。不要从打印名称判断身份。pretty-printer 可以显示相同的用户名字，内部引用才决定“它是哪一个变量”。

## binder 内部怎样指向被绑定变量
%%%
tag := "ch06-s06"
%%%

目标 `∀ n : Nat, n = n` 的最外层是 `.forallE`：

```anchor metam_binder_probe
elab "inspect_forall_target" : tactic => withMainContext do
  let target ← (← getMainGoal).getType
  match target with
  | .forallE name domain body binderInfo =>
      logInfo m!"binder={name}; info={repr binderInfo}; domain={domain}; body={body}"
  | _ => throwError "expected a forall target"

example : ∀ n : Nat, n = n := by
  inspect_forall_target
  intro n
  rfl
```

在 `∀ n : Nat, n = n` 中，`∀ n : Nat, ...` 是一个 binder（绑定构造），它把正文里的两个 `n` 都绑到自己。底层正文用 `#0` 表示“离我最近的 binder”；这套按距离编号的方法叫 de Bruijn index。再进入一层 binder 时，距离会改变，所以 Lean 提供 abstract/instantiate 操作，避免程序员手算编号位移。

改写器使用同一纪律：先把匹配到的左端从目标中抽象出来，得到 motive；再把右端实例化进去。

# 类型推断依赖局部上下文
%%%
tag := "ch06-s07"
%%%

`inferType` 的接口很短：

:::codeBox "code"
```
inferType : Expr → MetaM Expr
```
:::

`inferType` 还要读取当前现场。若输入是 `Expr.fvar xId`，它的类型保存在 local context 中；若输入含有 metavariable，`inferType` 还要读取 mctx。处理隐式参数和 universe 约束时，它也可能更新状态。

在 `rw_xray` 中，`inferType heq` 得到 `x = y`。源码中的 `rewrite` 会再次推断并实例化 theorem 的类型，因为调用者传入的 Expr 可能仍含刚被其他步骤赋值的 metavariables。

# 定义等价是带状态的判断
%%%
tag := "ch06-s08"
%%%

两个 Expr 可以句法不同而定义等价，例如 `(fun x => x) 3` 与 `3`。`isDefEq` 在归约、透明度和统一约束下判断定义等价：

:::codeBox "code"
```
isDefEq : Expr → Expr → MetaM Bool
```
:::

只看返回值 `Bool`，很容易忽略它还会修改状态。下面的实验创建一个类型为 `Nat` 的 fresh metavariable，再把它与 `3` 比较：

```anchor metam_defeq_assignment
elab "observe_defeq_assignment" : tactic => do
  let hole ← mkFreshExprMVar (mkConst ``Nat)
  let holeId := hole.mvarId!
  let before ← holeId.isAssigned
  let ok ← isDefEq hole (mkNatLit 3)
  let after ← holeId.isAssigned
  let value ← instantiateMVars hole
  logInfo m!"before={before}, isDefEq={ok}, after={after}, value={value}"

example : True := by
  observe_defeq_assignment
  trivial
```

比较前未赋值；成功后得到 `?m := 3`。`instantiateMVars hole` 随后读取这项赋值。

Lean 4.32.2 的 `isDefEq` 自带 defeq checkpoint。比较返回 `false` 或抛出异常时，它会撤销比较过程中产生的临时赋值；比较成功时，约束和 metavariable assignment 才提交到当前 mctx。

候选搜索仍要在外层保存快照。一个候选可能通过 `isDefEq`，却在后续的 side-goal 检查或证明构造中失败；这时还要撤销成功统一留下的赋值。

# 保存和恢复元变量上下文
%%%
tag := "ch06-s09"
%%%

下面用一个只保存 mctx 的最小实验观察回滚：

```anchor metam_mctx_restore
elab "observe_mctx_restore" : tactic => do
  let hole ← mkFreshExprMVar (mkConst ``Nat)
  let holeId := hole.mvarId!
  let saved ← getMCtx
  discard <| isDefEq hole (mkNatLit 7)
  let assignedDuring ← holeId.isAssigned
  setMCtx saved
  let assignedAfterRestore ← holeId.isAssigned
  logInfo m!"assigned during branch={assignedDuring}; after restore={assignedAfterRestore}"

example : True := by
  observe_mctx_restore
  trivial
```

日志显示分支中已经赋值，恢复后重新变为未赋值。源码中的搜索过程通常会保存更完整的 Term/Tactic state，因为尝试一个候选还可能更新 synthetic metavariables、messages、info tree 和活动目标队列。

Meta action 抛出异常时，不能假定此前的所有写入都会自动撤销。是否回滚，要看 API 内部是否设置了 checkpoint，或者调用者是否在外层保存并恢复状态。`isDefEq` 会自行撤销失败比较留下的修改；如果统一已经成功、候选却在后续步骤失败，就必须由调用者恢复外层状态。

# `MVarId.rewrite` 的契约
%%%
tag := "ch06-s10"
%%%

源码入口是 `Lean/Meta/Tactic/Rewrite.lean`。核心类型如下：

:::codeBox "code"
```
structure RewriteResult where
  eNew     : Expr
  eqProof  : Expr
  mvarIds  : List MVarId

MVarId.rewrite
  (mvarId : MVarId)
  (e heq : Expr)
  (symm : Bool := false)
  (config := {}) : MetaM RewriteResult
```
:::

第二个显式参数 `e` 是要改写的表达式。改写目标还是局部假设，由调用者传入的 Expr 决定。本章传入 `g.getType`。

结果字段的含义是：

- `eNew`：替换后的表达式；
- `eqProof`：原表达式等于新表达式的证明；
- `mvarIds`：实例化改写 theorem 时留下的 side goals。

`rewrite` 不给原目标赋值。它返回足够的信息，让调用者决定如何提交。

# 打开 theorem 参数
%%%
tag := "ch06-s11"
%%%

改写 theorem 可能是 `∀ n, f n = n + 1`。源码依次执行：

:::codeBox "pseudocode"
```
inferType heq
→ instantiateMVars
→ forallMetaTelescopeReducing
→ mkAppN heq newMVars
```
:::

`forallMetaTelescopeReducing` 为参数创建 fresh metavariables，并返回打开后的结论。匹配目标中的 `f x` 时，统一把参数洞赋为 `x`。

```anchor metam_rewrite_side_goal
example (f : Nat → Nat) (x : Nat)
    (h : ∀ n, n > 0 → f n = n + 1) (hx : x > 0) : f x = x + 1 := by
  rw_xray h
  · rfl
  · exact hx
```

左端模式可以把参数 `n` 推断为 `x`，但匹配本身无法证明条件 `x > 0`，所以这个条件进入 `RewriteResult.mvarIds`。日志会显示一个 side goal。Lean 前端把改写后的新主目标排在它前面，因此示例先用 `rfl` 关闭新目标，再用 `hx` 证明条件。

# 等式、Iff 与方向
%%%
tag := "ch06-s12"
%%%

打开参数后，`matchEq?` 检查结论是否形如 `lhs = rhs`。命题改写还接受 `lhs ↔ rhs`；处理 Iff 时，改写器先通过 `propext` 得到命题等式，再按 Eq 的方式继续改写。

`symm := true` 时，改写器先构造对称等式并交换左右端。theorem 无效、左端仍是 metavariable，或目标中找不到匹配项时，改写都会在匹配阶段失败。

# `kabstract` 与 motive
%%%
tag := "ch06-s13"
%%%

设目标为 `x + 1 = y + 1`，改写定理的左端是 `x`。`kabstract` 把匹配 occurrence 抽象成 bound variable，得到可读成 `_a + 1 = y + 1` 的 body。随后构造：

:::codeBox "pseudocode"
```
fun _a => _a + 1 = y + 1
```
:::

这就是 motive。此时 `rhs` 是 `y`；用它实例化抽象出的 bound variable，就得到新表达式 `y + 1 = y + 1`。数据流是：

:::codeBox "pseudocode"
```
e
→ kabstract e lhs
→ eAbst
→ eAbst.instantiate1 rhs
→ eNew
```
:::

Lean 还会检查 motive 是否类型正确。若目标类型依赖被替换值，普通 rewrite 可能无法构造合法运输；出错时打印的 motive 会直接显示哪一处依赖结构使运输无法成立。

# 等式证明怎样产生
%%%
tag := "ch06-s14"
%%%

若 `heq : lhs = rhs`，motive 的类型为 `α → β`，则：

:::codeBox "pseudocode"
```
congrArg motive heq : motive lhs = motive rhs
```
:::

`motive lhs` 定义等价于原表达式，`motive rhs` 定义等价于 `eNew`。源码使用 `mkApp6` 构造这个 `congrArg` 表达式。

本章日志打印的 proof type 是 `(x + 1 = y + 1) = (y + 1 = y + 1)`。内核只检查最终的 proof Expr，不把改写器的匹配算法列入信任边界。

# 提交目标变化
%%%
tag := "ch06-s15"
%%%

`RewriteResult` 返回后，外壳调用：

:::codeBox "code"
```
let g' ← g.replaceTargetEq r.eNew r.eqProof
replaceMainGoal (g' :: r.mvarIds)
```
:::

`replaceTargetEq` 创建一个类型为 `eNew` 的新 metavariable，再借助 `eqProof` 用它给旧目标赋值。随后 TacticM 把 side goals 与新目标装入活动队列。

此时有两层状态：

:::codeBox "pseudocode"
```
Meta.State.mctx
  旧目标 := 由 eqProof 与新目标组成的 proof

Tactic.State.goals
  [旧目标] → [新目标, side goals...]
```
:::

Ch08 将完整展开第二层。

# 失败发生在哪一步
%%%
tag := "ch06-s16"
%%%

下面固定一条失败路径：

```anchor metam_rewrite_failure
example (x y : Nat) (_h : x = y) : 0 = 0 := by
  fail_if_success rw_xray _h
  rfl
```

`h : x = y` 的左端没有出现在 `0 = 0` 中。失败发生在 occurrence 检查，没有可抽象的位置，因而无法构造 motive。

| 阶段 | 典型错误 |
|---|---|
| 推断 theorem 类型 | theorem Expr 在当前上下文中无类型 |
| 打开参数 | universe 或参数约束不合法 |
| `matchEq?` | theorem 结论不是 Eq/Iff |
| pattern 检查 | lhs 仍是 metavariable |
| `kabstract` | 目标中没有 occurrence |
| motive 检查 | 替换造成依赖类型非法 |
| 实例合成 | theorem 参数留下未解 instance |
| 目标提交 | proof type 与运输目标不一致 |

# `apply` 的 Meta 尾段
%%%
tag := "ch06-s17"
%%%

Ch08 将讲到的 Lean 自带 `apply` 也建立在一段很小的 Meta 核心之上：

```anchor metam_apply_core
elab "apply_core " t:term : tactic => withMainContext do
  let theoremExpr ← elabTermForApply t
  let newGoals ← (← getMainGoal).apply theoremExpr
  Term.synthesizeSyntheticMVarsNoPostponing
  replaceMainGoal newGoals
```

```anchor metam_apply_core_use
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  apply_core And.intro
  · exact hP
  · exact hQ
```

`MVarId.apply` 创建 theorem 参数洞，统一 theorem 结论与目标，给旧目标赋值，再返回未赋值的参数洞。它不管理活动目标顺序；`replaceMainGoal` 属于 TacticM 外壳。

# `substCore` 提示的依赖边界
%%%
tag := "ch06-s18"
%%%

变量消去还要处理局部声明之间的依赖：其他声明的类型可能引用被消去变量。源码中的 `substCore` 中的 `depElim` 检查 reverted 目标是否依赖等式证明 `h`，据此选择 `mkEqRec` 或 `mkEqNDRec`；它检查的并非“目标是否依赖被消去变量 `x`”。局部上下文是一串按依赖排序的声明，不是无序字典。

本章不复刻完整 `substCore`。它留作源码导读和挑战练习，用来检验读者是否理解 local context、motive 与 `Eq.rec` transport。

# 源码地图
%%%
tag := "ch06-s19"
%%%

建议按下面的顺序阅读源码：

:::codeBox "pseudocode"
```
Lean/Meta/Tactic/Rewrite.lean
  RewriteResult / MVarId.rewrite
→ Lean/Meta/KAbstract.lean
  kabstract
→ Meta matcher 与 matchEq?
→ Lean/Meta/MVarContext.lean
  declarations / assignments
→ Lean/Meta/Tactic/Apply.lean
  MVarId.apply
→ Lean/Meta/Tactic/Subst.lean
  dependent substitution
```
:::

第一遍只跟 `symm := false` 的 Eq 分支。第二遍再看 Iff、occurrence 配置、binder-name 后处理和 dependent error。

# API 回查表
%%%
tag := "ch06-s20"
%%%

| 任务 | 入口 |
|---|---|
| 取得目标类型 | `MVarId.getType` |
| 在目标上下文运行 | `MVarId.withContext` |
| 推断 Expr 类型 | `inferType` |
| 弱头归约 | `whnf` |
| 判断定义等价 | `isDefEq` |
| 实例化元变量 | `instantiateMVars` |
| 创建表达式洞 | `mkFreshExprMVar` |
| 查询是否赋值 | `MVarId.isAssigned` |
| 读取/替换 mctx | `getMCtx` / `setMCtx` |
| 打开 forall 参数 | `forallMetaTelescopeReducing` |
| 抽象 occurrence | `kabstract` |
| 改写 Expr | `MVarId.rewrite` |
| 提交目标运输 | `MVarId.replaceTargetEq` |
| 应用 theorem | `MVarId.apply` |

# 练习
%%%
tag := "ch06-s21"
%%%

## 基础一：读 application spine
%%%
tag := "ch06-s22"
%%%

预测 `inspect_main_target` 对 `f x y = z` 打印的应用头和参数数目。

*答案*：最外层应用头仍是 `@Eq`，参数是等式所在类型、`f x y` 与 `z`。要观察 `f` 的 spine，应继续拆等式左端。

## 基础二：定义等价修改了什么
%%%
tag := "ch06-s23"
%%%

解释 `observe_defeq_assignment` 中 `hole` 为何在比较后变成 `3`。

*答案*：比较把 `?m` 与具体项统一，赋值记录在 `Meta.State.mctx`；`instantiateMVars` 读取该赋值。

## 基础三：`rewrite` 返回后旧目标是否已经赋值
%%%
tag := "ch06-s24"
%%%

`MVarId.rewrite` 返回 `RewriteResult` 时，旧目标是否已经获得赋值？

*答案*：尚未赋值。`MVarId.rewrite` 只返回 `RewriteResult`；`replaceTargetEq` 才创建承接目标并安排运输证明。

## 进阶一：打印 motive
%%%
tag := "ch06-s25"
%%%

复制 `rw_xray`，根据 lhs 与 target 调用 `kabstract`，打印抽象结果和 `mkLambda` 得到的 motive。

*测试*：motive 实例化 lhs 后定义等价于原目标，实例化 rhs 后定义等价于新目标。

## 进阶二：制造 side goal
%%%
tag := "ch06-s26"
%%%

构造带额外前提的改写 theorem，使某个参数无法从 lhs 推断。观察 `RewriteResult.mvarIds`。

*提示*：增加一个不出现在 lhs、却参与 theorem proof 的 proposition 参数。

## 进阶三：候选回滚
%%%
tag := "ch06-s27"
%%%

第一候选先用 `isDefEq` 给 fresh metavariable 赋值，再故意失败；恢复 mctx 后运行第二候选。

*测试*：第二候选开始时该 metavariable 未赋值。

## 挑战：局部假设改写
%%%
tag := "ch06-s28"
%%%

这个可运行外壳先把 hypothesis 名解析成 `FVarId`，再调用源码中的 `rewriteLocalDecl`。后者负责译补 theorem、替换局部声明、维护依赖它的上下文，并更新活动目标队列。最后，代码从新的局部上下文中找到同名声明，打印它的新类型。

```anchor metam_local_rewrite
elab "rw_hyp_xray " t:term " at " h:ident : tactic => do
  let fvarId ← getFVarId h
  Lean.Elab.Tactic.rewriteLocalDecl t false fvarId
  withMainContext do
    let lctx ← getLCtx
    let some decl := lctx.findFromUserName? h.getId
      | throwError "rewritten hypothesis is missing"
    logInfo m!"rewritten hypothesis type: {decl.type}"

example (x y : Nat) (hxy : x = y) (h : x + 1 = 2) : y + 1 = 2 := by
  rw_hyp_xray hxy at h
  exact h
```

进阶任务是不再直接调用 `rewriteLocalDecl`，而是用 `MVarId.rewrite` 和 `replaceLocalDecl` 展开它的核心步骤，并逐项记录 `AssertAfterResult.fvarId`、`mvarId` 和 `subst`。测试中还应加入一个后续声明依赖旧 hypothesis 的例子。

# 本章边界
%%%
tag := "ch06-s29"
%%%

`rw_xray` 已经展示了 Expr、local context、定义等价、metavariable assignment、motive、proof Expr 和目标运输之间的关系。外壳中的 `elabTerm` 仍替我们处理 Syntax 和类型。下一章进入 TermElabM，说明预期类型、延期任务、synthetic metavariables 与译补恢复怎样协同工作。
