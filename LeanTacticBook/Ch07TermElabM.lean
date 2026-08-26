import VersoManual
import LeanTacticBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "examples"
set_option verso.exampleModule "Examples.Ch07TermElabM"

#doc (Manual) "TermElabM：让句法获得类型" =>
%%%
file := "Ch07TermElabM"
tag := "ch07-termelabm"
%%%

> *本章目标*：解释同一个 `0` 为什么能在不同位置获得不同类型。我们先观察外层类型怎样帮助内层译补，再处理“信息暂时不够”的情况；最后用 `exact?%` 把这些机制接到自动证明搜索。
>
> *版本基准*：Lean `leanprover/lean4:v4.32.2`，Mathlib revision `905b95818eb3`。

# 概述：用户写的是 Syntax，MetaM 处理的是 Expr

Ch06 假定 Expr 已经存在，然后研究怎样推断它的类型、检查定义等价、创建证明洞和构造证明。用户输入却不是 Expr。用户写下的是 Syntax，其中的 `0`、`_`、省略的隐式参数和重载名称都可能有多种解释。把 Syntax 变成带有确定变量身份和类型约束的 Expr，这一步叫作项译补。

可以先把这一层放进整条数据流：

:::codeBox "pseudocode"
```
用户输入的 term Syntax
  + 当前局部上下文
  + 外层提供的可选预期类型
        ↓ TermElabM
已经译补的 Expr
  + 尚待 MetaM 求解的约束或证明洞
```
:::

TermElabM 不取代 MetaM。它仍然调用 MetaM 做类型推断、统一和证明构造，但它还要决定用户句法应当怎样解释。外层类型可以帮助内层消除歧义，内层产生的类型也能反过来约束外层；信息暂时不足时，译补器可以延期，而不是立即猜一个答案。类型类参数、coercion 和记号产生的辅助洞还需要专门登记，等更多信息出现后统一收尾。

本章会依次建立四个概念。先看预期类型怎样参与双向传播，再区分“类型检查”与“只比较打印结果”；接着解释 postponement 为什么要保存原现场；最后区分普通 metavariable、synthetic metavariable 和恢复用的 synthetic sorry。读完这些准备后，`TermElab := Syntax → Option Expr → TermElabM Expr` 才不再是一串陌生名字，而是前面每项需求的汇总。


Ch06 从已经译补好的 `Expr` 开始。本章向前退一步，面对用户刚写下的 `Syntax`。考虑两个声明：`def n : Nat := 0` 与 `def z : Int := 0`。两处源码都是字符 `0`，结果却不是同一个表达式。区别来自等号左边已经规定的类型。

外层希望内层得到的类型，叫作 expected type（预期类型）。term elaboration（项译补）不是脱离上下文地把 Syntax 翻成 Expr；它让外层预期类型和内层表达式相互传递约束。

# 译补为何不能写成 `Syntax → Expr`
%%%
tag := "ch07-s03"
%%%

同一个数字 `3` 可以成为 `Nat`、`Int`、`Rat` 或 `Real`。相同的 `_` 在不同位置也可能需要不同类型。仅有 Syntax，信息还不够。最小的数据流是：

:::codeBox "pseudocode"
```
Syntax + 可选的预期类型 + 当前局部含义
→ Expr + 尚待解决的类型约束
```
:::

预期类型沿外到内的方向传播。例如 `Nat` 告诉数字记号应产生哪一种零。译补出的 Expr 也会沿内到外的方向补充信息。例如，一个已经确定为 `Nat` 的参数可以反过来确定函数的隐式类型参数。这就是“双向”的含义。

# `show T from e`：显式类型怎样参与双向传播
%%%
tag := "ch07-s10"
%%%

最直接的观察工具是 `show T from e`：它明确要求先把 `e` 当作类型 `T` 的项来译补。在 `show Nat from 3` 中，`Nat` 先成为数字 `3` 的预期类型。

`book_show` 是一份刻意缩小的对照实现：先译补类型，再用该类型译补值，最后检查整个结果是否符合更外层的类型。它省略了 Lean 自带 `show` 所保留的局部 `have` 结构。

```anchor termelab_book_show
syntax (name := bookShow) "book_show " term " from " term : term

@[term_elab bookShow]
def elabBookShow : TermElab := fun stx expectedType? => do
  let `(book_show $typeStx from $valueStx) := stx
    | throwUnsupportedSyntax
  let type ← elabType typeStx
  logInfo m!"type written after show:{indentExpr type}"
  let value ← elabTermEnsuringType valueStx (some type)
  ensureHasType expectedType? value
```

```anchor termelab_book_show_use
example : Nat := book_show Nat from 3
example : True := book_show True from True.intro
example : Int := book_show Nat from 0
```

Lean 自带的 `show` 会生成局部 `have` 结构，把显式写出的类型 `T` 保留下来，再根据外层预期类型继续译补整个结构。因此，`from` 后的项必须先具有类型 `T`，而外层仍可在需要时插入 coercion。下面两项使用 Lean 自带的记号：

```anchor termelab_real_show
example : Int := show Nat from 0
example (x y : Nat) : (x + 0) + y = x + y := by
  rw [show x + 0 = x from rfl]
```

数据流是：

:::codeBox "pseudocode"
```
type Syntax
→ elabType
→ T : Expr

value Syntax + expected T
→ elabTermEnsuringType
→ e : Expr

outer expected type + e
→ ensureHasType
→ 返回 e，或返回插入 coercion 后的新 Expr
```
:::

在 `book_show Nat from 3` 中，数字 `3` 从一开始就在 `Nat` 预期类型下译补。随后，`ensureHasType expectedType? value` 检查所得 Expr 是否符合外层预期类型，并在需要时插入 coercion。因此，`book_show Nat from 0` 也可用于预期类型为 `Int` 的位置。

Lean 自带的 `show` 还会保留 `have this : T := e; this` 这层结构：`e` 必须先精确具有显式类型 `T`，整个 `have` 表达式再接受外层 coercion。

# `ensureHasType` 与定义等价
%%%
tag := "ch07-s11"
%%%

`ensureHasType` 的任务是把已经得到的 Expr 交给更外层。它不会只比较两段打印文字，而会推断 Expr 的类型，再检查它与外层预期类型是否定义等价。若存在合法的 coercion（强制转换），它还可以插入转换；否则报告类型不匹配。

Term 层决定何时调用这些 Meta 操作，并把错误定位到对应的 Syntax。MetaM 提供语义判断；TermElabM 提供用户输入、预期类型、延期与诊断政策。

# Postponement：信息尚未到齐
%%%
tag := "ch07-s12"
%%%

有时外层预期类型本身还是一个未赋值的洞。此时任选 `Nat` 或 `Bool` 都是不可靠的猜测。Term elaborator 可以选择 postponement（延期）：先记下“这段 Syntax 等类型更明确后再处理”，继续译补别处。别处增加约束后，系统重试这项工作。

一项延期工作至少要能找回原 Syntax、当时的局部上下文和重试动作。锁定实现用 `SavedContext` 保存所需现场，并让一个 placeholder metavariable 标记结果仍未完成。三个位置不要混写：

- `syntheticMVars` 是以元变量编号为键的表；若该项被延期，对应 `SyntheticMVarDecl.kind` 是 `postponed savedContext`，真正的延期 payload 在这里；
- `pendingMVars` 只是“仍要再次处理哪些元变量”的有序编号队列；它不保存 Syntax 和 `SavedContext`；
- Meta 层的 metavariable declaration 保存 placeholder 自身的类型和局部上下文。

因此，“向 `pendingMVars` 放一个编号”和“保存延期任务内容”不是同一动作。第一遍不需要记字段，只需理解：延期是带着原现场登记任务，队列只负责以后轮到谁。

延期表示当前信息不足。相关 metavariable 获得更多约束后，任务会再次尝试；若所有任务收尾时仍无法推进，synthesis 才报告 stuck metavariables 或启用恢复策略。

下面的 elaborator 要求预期类型中不再含 metavariable。`same` 的第二个参数先约束 `α := Nat`，随后延期任务恢复并成功：

```anchor termelab_postpone_resume
syntax (name := needsExpected) "needs_expected% " term : term

@[term_elab needsExpected]
def elabNeedsExpected : TermElab := fun stx expectedType? => do
  let `(needs_expected% $t) := stx | throwUnsupportedSyntax
  let expectedType ← tryPostponeIfHasMVars expectedType?
    "needs_expected% requires a fully known expected type"
  logInfo m!"needs_expected% resumed with: {expectedType}"
  elabTerm t (some expectedType)

def same {α : Type} (x _y : α) : α := x

set_option trace.Elab.postpone true in
#check same (needs_expected% 7) (8 : Nat)
```

若没有第二个参数提供约束，任务会反复等待，并在收尾时报告预期类型仍含 metavariable。请在单独的 probe 文件中运行这个预期失败；recovery 生成的占位项不能算作成功结果。

# TermElabM 增加的现场
%%%
tag := "ch07-s02"
%%%

前面的双向传播和延期都需要保存额外现场。Lean 把承载项译补的计算层叫作 `TermElabM`。锁定版本的结构形状如下：

:::codeBox "code"
```
abbrev TermElabM :=
  ReaderT Term.Context <|
  StateRefT Term.State <|
  MetaM

abbrev TermElab :=
  Syntax → Option Expr → TermElabM Expr
```
:::

`TermElab` 接收两个显式输入：

- 用户写下的 Syntax；
- 可选的预期类型 `Option Expr`。

预期类型是每次调用 `TermElab` 时显式传入的参数，不是 `Term.Context` 的一个字段。`Term.Context` 保存声明、binder、recovery 等较长期政策；不要把“这一项此刻希望得到什么类型”误塞进 Context。

它在 TermElabM 中返回 Expr。底层仍是 MetaM，所以局部上下文、mctx、定义等价检查和证明构造都可以继续使用。Term 层主要多记两类进行中的工作：等待重试的译补任务，以及稍后统一处理的辅助洞。完整字段到本章后半再回查。

# Synthetic metavariables
%%%
tag := "ch07-s13"
%%%

考虑表达式 `(default : Nat)`。常量 `default` 需要一份 `[Inhabited Nat]` 实例，用户却没有手写这份参数。译补器先创建一个辅助洞，登记“稍后用类型类搜索填它”，再继续构造外层 Expr。这类由译补器登记、需要专门收尾程序处理的辅助洞，叫 synthetic metavariable（合成元变量）。

它不同于用户正在证明的主目标，也不同于失败恢复时插入的 synthetic sorry。`Term.State.syntheticMVars` 保存的是待处理任务。下面的教学 elaborator 显式登记一个类型类任务：

下面的纯 term elaborator 显式创建 `Inhabited expectedType` 实例洞，把它登记成 `.typeClass` synthetic task，再构造 `default`：

```anchor termelab_synthetic_default
syntax (name := syntheticDefault) "synthetic_default%" : term

@[term_elab syntheticDefault]
def elabSyntheticDefault : TermElab := fun stx expectedType? => do
  let expectedType ← withExpectedType expectedType? pure
  let u ← getLevel expectedType
  let classType := mkApp (mkConst ``Inhabited [u]) expectedType
  let inst ← mkFreshExprMVar classType MetavarKind.synthetic
  registerSyntheticMVar stx inst.mvarId! (.typeClass none)
  let kinds ← (← get).pendingMVars.mapM fun mvarId => do
    return (← getSyntheticMVarDecl? mvarId).map (toString ·.kind) |>.getD "unknown"
  logInfo m!"registered synthetic kinds: {kinds}"
  return mkApp2 (mkConst ``default [u]) expectedType inst

#eval (synthetic_default% : Nat)
```

日志在 synthesis 前记录 `[typeclass]`，随后框架求出 `Inhabited Nat`，`#eval` 得到 `0`。elaborator 必须在相应位置明确选择处理方式：

- 允许延期；
- 禁止继续延期；
- 报错；
- recovery 中插入 synthetic sorry。

Ch08 的 Lean 自带 `apply` 会在 Meta apply 前后各处理一次 synthetic metavariables。

# 同一 syntax kind 可以有多个 elaborator
%%%
tag := "ch07-s14"
%%%

parser 会给 Syntax 节点标上 kind（种类），例如“这是 `book_default` 这种句法”。一个 kind 可以注册多个 term elaborator。负责按顺序尝试这些实现的程序叫 dispatcher（分派器）。当前实现发现“这不是我负责的预期类型”时，应抛 `throwUnsupportedSyntax`，让分派器尝试下一项。

本章用 `book_default` 建了两个实现，一个只接受 Nat 预期类型，一个只接受 Bool：

```anchor termelab_same_syntax_kind
syntax (name := bookDefault) "book_default" : term

@[term_elab bookDefault]
def elabBookDefaultNat : TermElab := fun stx expectedType? => do
  let `(book_default) := stx | throwUnsupportedSyntax
  let some expectedType := expectedType? | throwUnsupportedSyntax
  unless expectedType.isConstOf ``Nat do throwUnsupportedSyntax
  logInfo "Nat elaborator accepted book_default"
  return mkNatLit 0

@[term_elab bookDefault]
def elabBookDefaultBool : TermElab := fun stx expectedType? => do
  let `(book_default) := stx | throwUnsupportedSyntax
  let some expectedType := expectedType? | throwUnsupportedSyntax
  unless expectedType.isConstOf ``Bool do throwUnsupportedSyntax
  logInfo "Bool elaborator accepted book_default"
  return mkConst ``Bool.false

example : Nat := book_default
example : Bool := book_default
```

两个例子使用相同 Syntax；预期类型决定哪一个 elaborator 接受。`throwUnsupportedSyntax` 表示“该实现不负责此输入”，用户错误则应使用 `throwError`。混淆两者会阻止合法 fallback，或把真正错误静默交给其他实现。

# Mathlib set-builder 的实际启示
%%%
tag := "ch07-s15"
%%%

Mathlib 中，Set 和 Finset 的集合构造记号可以使用相近的 Syntax。多个 elaborator 会检查预期类型，据此判断自己是否应当接管。某些实现还要限制 postponement：如果高优先级实现一直延期，排在后面的实现就没有机会处理本来属于自己的输入。

```anchor termelab_setbuilder_fallback
def smallEvens : Finset (Fin 6) := {x | x.val % 2 = 0}
def oddsFromFinset (s : Finset Nat) : Finset Nat := {x ∈ s | x % 2 = 1}
def oddsFromSet (s : Set Nat) : Set Nat := {x ∈ s | x % 2 = 1}
def noExpectedSet := {x : Nat | x % 2 = 0}
```

前三项由预期类型或左侧容器决定哪个 elaborator 接管。最后一项没有外层预期类型，仍由 Set 的默认实现处理。

锁定版本的 Finset elaborator 遇到 Set 预期类型时抛 unsupported，并且在预期类型未知时不会一味 postpone，以免挡住 Set fallback。

本章不复刻完整 set-builder。源码导读只追三件事：

1. 相同 syntax kind 的多个注册项；
2. 预期类型如何决定接管者；
3. unsupported、postpone 与 user error 怎样分流。

你可以先通过 `book_default` 直接观察分派结果，再去读源码。

# 综合案例：`exact?%` 把预期类型变成搜索目标
%%%
tag := "ch07-s01"
%%%

名称末尾的 `%` 用来区分两个前端：`exact?%` 出现在 term 位置，`exact?` 出现在 `by` 后的 tactic 位置。下面先实测拼写，再实现 term 版本。

```anchor termelab_exact_spellings
example : True := exact?%
example : True := by
  exact?
```

教学版本叫 `book_exact?%`：

```anchor termelab_book_exact_use
example : True := book_exact?%
example (P : Prop) (h : P) : P := book_exact?%
example (P Q : Prop) : P → Q → P ∧ Q := book_exact?%
```

它在三种目标下分别找到 `True`、局部假设和合取构造器。实现如下：

```anchor termelab_book_exact
syntax (name := bookExactTerm) "book_exact?%" : term

@[term_elab bookExactTerm]
def elabBookExactTerm : TermElab := fun stx expectedType? => do
  let `(book_exact?%) := stx | throwUnsupportedSyntax
  withExpectedType expectedType? fun expectedType => do
    logInfo m!"expected type:{indentExpr expectedType}"
    let goal ← mkFreshExprMVar expectedType
    let (_, introdGoal) ← goal.mvarId!.intros
    introdGoal.withContext do
      if let some suggestions ← librarySearch introdGoal then
        if suggestions.isEmpty then
          logError "book_exact?% did not find a relevant declaration"
        else
          logError "book_exact?% found only partial suggestions"
        mkLabeledSorry expectedType (synthetic := true) (unique := true)
      else
        let proof ← instantiateMVars goal
        logInfo m!"proof type:{indentExpr (← inferType proof)}"
        addTermSuggestion stx proof.headBeta
        return proof
```

此前的概念现在串成一条调用链：

:::codeBox "pseudocode"
```
term Syntax
→ 取得预期类型
→ 创建该类型的 proof metavariable
→ intros 打开函数目标
→ 在引入后的 local context 中运行 Library Search
→ 成功：实例化 proof hole，返回 Expr
→ 失败：记录 error，返回 typed synthetic sorry
```
:::

Ch06 的 `rw_xray` 从现成的目标 Expr 开始。本章再向前追一步：目标 Expr 从哪里来，搜索返回的 Expr 又怎样与外层类型对齐。

# `withExpectedType`
%%%
tag := "ch07-s04"
%%%

`book_exact?%` 先执行：

:::codeBox "pseudocode"
```
withExpectedType expectedType? fun expectedType => ...
```
:::

`withExpectedType` 会尝试延期 `none`，也会延期头部仍是 metavariable 的预期类型。若调度器已不允许继续延期，`some ?m` 仍会交给回调，后端可以反过来约束这个 metavariable。只有参数最终仍是 `none` 时，它才报告“expected type must be known”。

因此，这个函数只保证回调能取得 `some expectedType`。它不保证 `expectedType` 中没有 metavariable，也不会在这里创建 fresh type metavariable。算法若要求类型完全确定，应改用 `tryPostponeIfHasMVars`。

下面三个例子分属两种情况：前两个由外层目标把类型定为 `True`，第三个让搜索反向约束未知类型。

```anchor termelab_expected_type_flow
example : True := id book_exact?%
example : True := (book_exact?% : True)
#check id book_exact?%
```

最后一行没有外层预期类型。停止延期后，`book_exact?%` 收到 `some ?m`；Library Search 找到 term，并由该 term 的类型反向约束 `?m`。具体结果取决于锁定环境中的候选排序。这个例子只证明 metavariable 可以流入回调，不建议用搜索器猜顶层类型。

# 从预期类型创建证明目标
%%%
tag := "ch07-s05"
%%%

取得 `expectedType` 后，主例调用：

:::codeBox "code"
```
let goal ← mkFreshExprMVar expectedType
```
:::

若预期类型是命题，`goal` 是一个证明洞；term elaborator 也可以为非命题类型创建数据洞。它的 mvar declaration 保存：

- 类型；
- 创建时的 local context；
- kind 与 synthetic 信息；
- 是否已经赋值。

此处创建的是普通 Expr metavariable，Library Search 成功后会给它赋值。

# 为什么先 `intros`
%%%
tag := "ch07-s06"
%%%

若目标是：

:::codeBox "code"
```
P → Q → P ∧ Q
```
:::

Library Search 直接面对整个箭头类型时，局部上下文中还没有 `P` 和 `Q` 的证明。Lean 自带的 `exact?%` 调用：

:::codeBox "code"
```
let (_, introdGoal) ← goal.mvarId!.intros
```
:::

`intros` 为开头的 binder 创建 free variables，把原 proof hole 赋值为 lambda，并把 lambda 的 body 留作新目标。Library Search 随后在 `introdGoal.withContext` 中运行，可以使用这些新引入的局部假设。

此时，mctx 保存原目标到 lambda 的赋值，local context 则保存新引入的 free variables。

# Library Search 在这里是 Meta 后端
%%%
tag := "ch07-s07"
%%%

Ch09 会完整讲解 Library Search。本章只使用它的契约：

:::codeBox "code"
```
librarySearch : MVarId → MetaM (Option Suggestions)
```
:::

返回 `none` 表示 Library Search 已找到完整证明并给目标赋值。返回 `some suggestions` 表示它没有找到并提交完整证明；数组中可能包含 partial candidates。

`exact?%` 默认以 `try? = false` 调用 `librarySearch`。这条路径从 TermElabM 进入 MetaM，不经过 TacticM。

Library Search 还提供可选的 Grind discharger；只有显式开启 `try?` 时，它才可能通过 `Tactic.run` 执行 tactic。这是搜索后端的可选分支，不能据此把 `exact?%` 的前端归到 TacticM。

主例成功后执行：

:::codeBox "code"
```
instantiateMVars goal
```
:::

`intros` 和搜索结果已经共同完成原 proof hole 的赋值。对 `goal` 执行 `instantiateMVars` 后即可得到完整的 proof Expr，Term elaborator 再把它返回给外层。

# term suggestion 与 proof Expr
%%%
tag := "ch07-s08"
%%%

教学版本调用 `addTermSuggestion`，因此构建日志显示 `Try this`。这条建议来自已经构造出的 proof Expr，经 pretty-printer 转成用户可复制的 term。

要区分：

- 返回 Expr：本次译补结果；
- suggestion：编辑器诊断；
- suggestion 重放：检查显示出的源码能否在保存状态中再次译补；
- kernel check：最终 declaration 接受 proof Expr。

Ch09 再检查建议重放时保存了哪些状态，以及显示出的源码能否独立通过译补。

# 失败与 synthetic sorry
%%%
tag := "ch07-s09"
%%%

Lean 自带的 `exact?%` 失败时先记录错误，再构造一个占位项：

:::codeBox "code"
```
mkLabeledSorry expectedType
  (synthetic := true)
  (unique := true)
```
:::

这棵 Expr 有正确的预期类型，使外层译补得以继续，IDE 可以显示后续错误和信息。它仍然是 sorry；若错误被忽略或恢复模式将其提交，公理锥会反映这一事实。

因此需要分清：

| 事件 | 含义 |
|---|---|
| `logError` | 在消息系统记录失败 |
| 返回 synthetic sorry | 为恢复提供类型正确占位项 |
| declaration 最终接受 | 取决于命令层如何处理错误 |
| 无公理证明 | 必须另做 sorry census 与公理检查 |

这个恢复项只让后续译补和 IDE 诊断继续进行，不能据此把本次搜索视为成功。

# Term.Context 与 Term.State
%%%
tag := "ch07-s16"
%%%

本章不列全字段，只按行为分组。

## Context 中的政策
%%%
tag := "ch07-s17"
%%%

- 当前 declaration 与 section 信息；
- macro expansion stack；
- binder 与 implicit-lambda 政策；
- auto-bound implicits；
- recovery、incrementality 与 source context。

## State 中的进行中工作
%%%
tag := "ch07-s18"
%%%

- synthetic metavariables；
- pending metavariables；
- universe level 名称及相关错误定位信息；
- metavariable 参数名与错误定位信息；
- 待提升的 `let rec` 记录。

普通 metavariable declaration 和 assignment 仍由 Meta.State.mctx 保存。Term.State 记录的是这些 Meta 洞在 term 译补流程中还要怎样处理。

# Saved state 与 recovery
%%%
tag := "ch07-s19"
%%%

候选 term elaborator 可能：

- 创建 ordinary metavariables；
- 添加 synthetic tasks；
- 写 messages；
- 写 info tree；
- 展开 macro；
- 最后抛 unsupported 或 error。

dispatcher 尝试下一个实现前，必须恢复当前候选改动过的 Term 和 Meta 状态；只恢复 mctx 不够。`Term.SavedState` 同时包含 `Meta.SavedState` 与 `Term.State`。

默认的 `restore` 会保留当前 trace state；当 `restoreInfo = false` 时，它还会保留 info state。因此，这里的“恢复”并不表示删除所有诊断记录。

Ch06 的 `getMCtx/setMCtx` 实验只处理 mctx，而 Term fallback 需要恢复范围更完整的 saved state。

# 源码调用链
%%%
tag := "ch07-s20"
%%%

按下面这条调用链阅读源码：

:::codeBox "pseudocode"
```
Lean/Elab/Tactic/LibrarySearch.lean
  elabExact?Term
→ Lean/Elab/Term.lean
  TermElabM / TermElab / withExpectedType
→ Lean/Elab/TermElabM.lean 等
  Context / State / saved state
→ Lean/Elab/SyntheticMVars.lean
  synthetic metavariables 与 synthesis
→ Lean/Elab/Term dispatcher
  elaborator registration / fallback
→ Mathlib set-builder elaborators
  预期类型驱动的多实现分派
```
:::

第一遍只追 `exact?%` 的成功分支。第二遍再读 failure recovery 与 postponed tasks。

# API 回查表
%%%
tag := "ch07-s21"
%%%

| 任务 | 入口 |
|---|---|
| 定义 term elaborator | `TermElab` |
| 注册 elaborator | `@[term_elab ...]` |
| 取得一项 `some` 预期类型（内部仍可含 mvar） | `withExpectedType` |
| 译补普通 term | `elabTerm` |
| 译补类型 | `elabType` |
| 在给定类型下译补 | `elabTermEnsuringType` |
| 检查外层类型 | `ensureHasType` |
| 创建 proof hole | `mkFreshExprMVar` |
| 收尾实例化 | `instantiateMVars` |
| 处理 synthetics | `synthesizeSyntheticMVars...` |
| 表示不负责此 Syntax | `throwUnsupportedSyntax` |
| 恢复占位项 | `mkLabeledSorry` |
| 添加 term suggestion | `addTermSuggestion` |

# 练习
%%%
tag := "ch07-s22"
%%%

## 基础一：预期类型来自哪里
%%%
tag := "ch07-s23"
%%%

解释 `example : True := id book_exact?%` 中 `True` 如何抵达内层 elaborator。

*答案*：外层目标约束 `id` 的结果类型，`id` 的参数与结果共享同一隐式类型参数，该约束传到参数位置，`withExpectedType` 最终取得 `True`。

## 基础二：为何先 `intros`
%%%
tag := "ch07-s24"
%%%

给定目标 `P → Q → P ∧ Q`，若跳过 `intros` 就直接让 Library Search 处理最外层 proof hole，它看不到哪些局部证据？

*答案*：函数目标的 binder 尚未成为 local hypotheses。`intros` 创建 free variables，并把原 proof hole 赋为 lambda，使 Library Search 能在 body 目标的 local context 中使用这些假设。

## 基础三：unsupported 与 error
%%%
tag := "ch07-s25"
%%%

同一 syntax kind 注册多个 elaborator 时，何时应抛 `throwUnsupportedSyntax`，何时应抛普通 user error？

*答案*：unsupported 表示当前注册实现不接管输入，dispatcher 可尝试其他实现；error 表示该实现已经接管并发现用户输入不合法。

## 进阶一：增加第三个 `book_default`
%%%
tag := "ch07-s26"
%%%

为 String 预期类型返回空串。要求 Nat、Bool、String 三例都由对应 elaborator 接管。

*测试*：未知预期类型下不得擅自选择任一分支。

## 进阶二：观察 synthetic mvar
%%%
tag := "ch07-s27"
%%%

设计一个需要类型类实例的 term elaborator，在 synthesis 前后打印 pending tasks。

*提示*：选择带 `[OfNat α 0]` 或 coercion 约束的目标；不要手工制造永远无法解决的全局实例。

## 进阶三：受控延期
%%%
tag := "ch07-s28"
%%%

写一个 elaborator：预期类型为未赋值 metavariable 时延期；确定为 Nat 时返回 `0`；确定为 Bool 时返回 `false`。

*测试*：放在外层类型可稍后确定的应用中成功；放在完全无约束位置时报告无法推断，而非任选分支。

## 挑战：set-builder fallback 审计
%%%
tag := "ch07-s29"
%%%

在锁定版本的 Mathlib 中选择一条 Set/Finset 共用同形 Syntax 的分派过程。逐个记录 elaborator 在什么条件下接管、postpone、抛 unsupported 或报告 user error。正文只画调用图，完整 probe 放入 examples。

# 本章边界
%%%
tag := "ch07-s30"
%%%

到这里，Syntax 已经能在预期类型、synthetic metavariable、postponement 与 recovery 的配合下变成 Expr。Term elaborator 每次仍只返回一个 Expr；多个证明洞接下来按什么顺序工作，要看 TacticM 的活动目标队列。下一章用 Lean 自带的 `apply` 说明活动目标队列如何调度这些证明洞。
