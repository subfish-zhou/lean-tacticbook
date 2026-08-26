import VersoManual
import LeanTacticBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "examples"
set_option verso.exampleModule "Examples.Ch08Exact"

#doc (Manual) "exact?：从结论索引到可重放建议" =>
%%%
file := "Ch08Exact"
tag := "ch08-exact"
%%%

> *本章目标*：从“我知道这个目标应该有现成证明，但忘了定理名”开始。先在一张很小的候选表中逐项尝试，分清候选可用、完整证明和可复制建议；候选多到不能线性扫描时，再引入结论索引。
>
> *版本基准*：Lean `leanprover/lean4:v4.32.2`，commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`；Mathlib revision `905b95818eb32af7874a58b427f50c1711a5e96c`。

若目标是 `P`，局部上下文里正好有 `h : P`，手写 `exact h` 即可。困难常常不是不会证明，而是不记得库中哪条声明能产生当前目标。`exact?` 试着替你找这样的声明，并把找到的证明显示成可以放回源码的建议。

这里有三个容易混淆的问题：某个候选的结论能否套到目标上？它留下的前提能否全部证明？内部证明怎样变成一段可复制的源码？本章按这个顺序处理。结论索引只是减少候选数的工程结构，不应抢在这三个问题之前出现。

# 先看一次搜索成功
%%%
tag := "ch08-s01"
%%%

下面的目标需要把 `P → Q` 和 `Q → R` 接起来。`exact?` 给出的文字未必和你手写的证明相同，但替换回去后必须得到类型为 `R` 的普通证明项。

```anchor exact_success
example (P Q R : Prop) (hP : P) (hPQ : P → Q) (hQR : Q → R) : R := by
  exact?
```

锁定版本中的输出为：

:::codeBox "code"
```
Try this:
  exact (hQR ∘ hPQ) hP
```
:::

term 位置使用的名字多一个 `%`：

```anchor exact_term_success
example (P Q R : Prop) (hP : P) (hPQ : P → Q) (hQR : Q → R) : R :=
  exact?%
```

这里的输出少了 tactic 位置常见的 `exact` 包装，因为 `exact?%` 本身就要返回一个 term。两个前端共享 Library Search，却不共享最后一段建议生成路径。

# 先在显式候选表中学习搜索
%%%
tag := "ch08-s18"
%%%

先不碰全库索引。下面的 `book_exact` 让用户直接给出一张候选表。对每个候选，它做三件事：尝试把候选用于目标；用现有局部假设填剩余的参数洞；若仍有洞或发生错误，恢复到尝试前再看下一项。

```anchor exact_toy_search
syntax "book_exact " term,* : tactic

elab_rules : tactic
  | `(tactic| book_exact $[$candidates],*) => do
      let initial ← saveState
      for candidate in candidates do
        initial.restore
        try
          withMainContext do
            let theoremExpr ← elabTermForApply candidate
            let newGoals ← (← getMainGoal).apply theoremExpr
            replaceMainGoal newGoals
          evalTactic (← `(tactic| all_goals assumption))
          if (← getGoals).isEmpty then
            return
        catch _ =>
          pure ()
      initial.restore
      throwError "book_exact exhausted its explicit candidate list"
```

第一个候选要求不存在的 `Q`，第二个候选要求已有的 `P`。只有完整关闭活动目标队列才算成功。

```anchor exact_toy_search_use
example (P Q R : Prop) (hP : P) (hR : R) : R := by
  book_exact (fun (_ : Q) => hR), (fun (_ : P) => hR)
```

这个缩小版故意没有做三件生产实现才需要做的事：

- 没有按结论形状建索引；
- 没有保存 partial mctx；
- 没有生成和重放建议。

它仍准确保留了核心状态契约：候选可 apply 不等于成功；失败候选不得污染下一项；完整解可以提交。

# 生产搜索依次回答四个问题
%%%
tag := "ch08-s02"
%%%

:::codeBox "pseudocode"
```
当前目标
→ 从候选来源取出“也许能用”的声明
→ apply 检验声明结论能否与目标统一
→ 局部搜索尝试关闭新参数洞
→ 把完整 proof Expr 显示成建议，并在原位置重放
```
:::

缩小版的候选来源是用户写的列表；生产版稍后会换成按结论结构查询的索引。这四步不能揉成一句“从库里找定理”。

1. *取候选*允许拿到最终不可用的声明；这一阶段只要求“值得尝试”。
2. *apply* 才创建 fresh parameter metavariables，并对结论与目标调用统一机制。
3. *关闭参数洞*是另一段 DFS；主引理能 apply 不等于完整证明已经找到。
4. *显示建议*还要把内部 Expr 变回人能写的源码、定位替换范围，并在初始证明状态上验证脚本。

只要记住这四道门，后面的源码不会变成一团互相调用的函数名。

# 搜索前先把箭头变成局部事实
%%%
tag := "ch08-s03"
%%%

前端先保存初始状态，再对主目标调用 `intros`。例如目标

:::codeBox "pseudocode"
```
P → Q → P ∧ Q
```
:::

会变成局部上下文中的 `hP : P`、`hQ : Q` 和目标 `P ∧ Q`。搜索器因此既能索引较小的结论，也能让后续的“小型局部求解程序”使用刚引入的局部事实；到实际调用处再给这个程序写出 API 名。最后生成的 proof Expr 再包回 lambda。

这一步已经在 Ch06 的 `exact?%` 里出现过。它不是 tactic 层的 `intro` 调度，而是 `MVarId.intros` 对 Meta goal 的变换。

# apply 之后是 solveByElim
%%%
tag := "ch08-s10"
%%%

候选声明变成 Expr 后，生产代码调用：

:::codeBox "code"
```
let newGoals ← goal.apply lemma applyConfig
try
  solveByElim ... newGoals
catch _ =>
  -- 按 allowFailure 决定是否保留 partial result
```
:::

Library Search 给 `solveByElim` 的默认配置包括：

- `maxDepth := 6`；
- `exfalso := false`；
- 开启对称规则；
- 各独立目标成功时可以提交；
- 明确关闭 constructor，因为它在大型库搜索中会显著拖慢；
- 可按配置附加两种不同 discharger：`+grind` 直接调用 `Grind.main`，`+try?` 则通过 `Tactic.run` / `evalTactic` 执行给定 tactic syntax。

因此 `exact?` 不是“挑一个结论完全相同的定理”。主引理可以留下参数洞，只要局部事实和小型默认规则能在深度界限内把它们关完。

# `using` 是约束，不是候选表
%%%
tag := "ch08-s11"
%%%

```anchor exact_required
example (P Q R : Prop) (hP : P) (hPQ : P → Q) (hQR : Q → R) : R := by
  exact? using hPQ, hQR
```

`exact? using hPQ, hQR` 要求局部搜索的最终证明使用列出的 free variables。语法写成 `term`，前端语义却会把每项译补后检查为 free variable，再交给 `requireUsingAll`。所以它不是“只搜索这两条定理”，也不是向主索引临时插入两个候选。

这类 parser 比语义宽的接口不能只看 grammar 解释；要沿 frontend 把 Syntax 追到实际检查。

# 候选之间怎样回滚
%%%
tag := "ch08-s12"
%%%

`tryOnEach` 在循环前保存 Meta state。每个候选可能：

- 给原目标赋值；
- 创建参数 metavariables；
- 让 `solveByElim` 赋值其中一部分；
- 触发 typeclass synthesis；
- 产生一个 partial MetavarContext。

生产循环的状态纪律可缩成：

:::codeBox "pseudocode"
```
saved ← saveState
for candidate in candidates:
  run candidate
  if complete and not collectAll:
    commit current mctx and return
  if partial or collectAll result:
    copy current mctx into result
  restoreState saved
```
:::

普通首个完整解是唯一不恢复的分支。partial result 必须把自己的 mctx 一起保存；仅保存 residual MVarId 没用，因为这些 id 的声明与 assignment 就住在那个 mctx 里。

达到 heartbeat 阈值时，内部异常只表示停止继续推测并返回已有结果；它不证明剩余候选都失败，更不证明目标不可证。

# 直接观察 partial result
%%%
tag := "ch08-s13"
%%%

下面的探针另建一个类型为 `P ∧ Q` 的临时目标。当前上下文没有 `P` 或 `Q` 的证明，因此搜索只能找到若干可 apply 的候选，不能完整关闭。探针最后恢复创建临时目标之前的状态，再打印结果。

```anchor exact_partial_probe
elab "partial_search_xray " typeStx:term : tactic => withMainContext do
  let saved ← saveState
  let type ← elabTerm typeStx (some (mkSort .zero))
  let probe ← mkFreshExprMVar type
  let result ← probe.mvarId!.withContext do
    librarySearch probe.mvarId!
  let assigned ← probe.mvarId!.isAssigned
  let summary ← match result with
    | none => pure "complete solution"
    | some suggestions =>
      let sample := (suggestions.extract 0 (min suggestions.size 5)).map (·.1.length)
      pure s!"{suggestions.size} partial suggestion(s), first returned subsidiary-list lengths {sample.toList}"
  saved.restore
  logInfo m!"search result: {summary}; probe assigned after return: {assigned}"

example (P Q : Prop) : True := by
  partial_search_xray (P ∧ Q)
  trivial
```

锁定环境中的输出末尾为：

:::codeBox "code"
```
search result: 68 partial suggestion(s),
first returned subsidiary-list lengths [2, 2, 1, 1, 1];
probe assigned after return: false
```
:::

候选数量不是 API 契约；版本、imports 和当前模块都会改变它。稳定的观察是：返回 `some suggestions`，每项带 `goal.apply` 最初产生的 subsidiary-goal list 与对应 mctx，当前 Meta state 已恢复，临时目标未被提交。若 `solveByElim` 已关闭其中一部分，当前 API 并不追踪并缩短这张列表；因此上面的长度不能解释成“仍未赋值的 residual 数”。

# 四种前端不能混写
%%%
tag := "ch08-s14"
%%%

```table
- 前端
- 完整候选
- partial / failure
- 最终状态
---
- `exact?`
- 提交第一个完整 proof，显示经重放的 `exact`
- 无完整解时报错
- 成功时目标关闭
---
- `apply?`
- 完整解走与 `exact?` 相同的提交分支
- 显示 `refine` 与剩余目标，随后 admit 供恢复
- partial 声明带 sorry；零候选还会记录 error
---
- `exact? +all`
- 收集并显示全部完整解，不提交第一个
- 没有完整解时直接报错，不进入 admit tail
- 有完整解时恢复候选状态，最后 admit
---
- `apply? +all`
- 收集全部完整解
- 同时显示允许的 partial
- 恢复候选状态，最后 admit
---
- `exact?%`
- 返回成功 proof term
- 记录错误并造 synthetic labeled sorry
- 不经过普通 TacticM 前端
```

表中最容易被压错的是 `apply?`。把控制流写成判定顺序更稳：

:::codeBox "pseudocode"
if 普通 exact? 或普通 apply? 找到完整解:
  提交普通 proof；关闭目标；不 admit
else if 普通 apply? 只找到 partial 解:
  显示 refine 建议；用 admit 恢复命令现场
else if 使用 +all:
  收集可显示的建议；最后恢复现场并 admit
else:
  报告没有结果
:::

所以 `apply?` 不是“总会返回 partial 并 admit”；完整成功分支与普通 `exact?` 一样。相反，`+all` 即使已经找到完整解也会继续收集，所以不能保留某个候选的 mctx 作为最终状态。`exact? +all` 只接受至少一个完整解；`apply? +all` 才会显示 incomplete suggestions。

下面用公理锥把两个容易误判的分支固定下来：partial `apply?` 与已有完整解的 `exact? +all` 都以恢复用 admit 收尾，所以所得 theorem 都含 `sorryAx`。

```anchor exact_frontend_axiom_probe
theorem applyPartialUsesSorry (P Q : Prop) (hP : P) : NeedBoth P Q := by
  apply?

#print axioms applyPartialUsesSorry

set_option linter.unusedVariables false in
theorem exactAllUsesSorry (P : Prop) (hP : P) : P := by
  exact? +all

#print axioms exactAllUsesSorry
```

# collect-all 必须恢复完整解
%%%
tag := "ch08-s15"
%%%

```anchor exact_collect_all_probe
elab "collect_all_xray " typeStx:term : tactic => withMainContext do
  let saved ← saveState
  let type ← elabTerm typeStx (some (mkSort .zero))
  let probe ← mkFreshExprMVar type
  let result ← probe.mvarId!.withContext do
    librarySearch probe.mvarId! (collectAll := true)
  let assigned ← probe.mvarId!.isAssigned
  let summary ← match result with
    | none => pure "unexpected committed solution"
    | some suggestions =>
      let complete := suggestions.countP (·.1.isEmpty)
      pure s!"{suggestions.size} collected suggestion(s), {complete} complete"
  saved.restore
  logInfo m!"collect-all result: {summary}; probe assigned after return: {assigned}"

example : True := by
  collect_all_xray True
  trivial
```

锁定环境中，临时 `True` 目标收集到多条建议，其中若干是完整解，但探针目标在返回后仍未赋值。`collectAll := true` 的函数返回值保存了每项自己的 mctx；调用者负责在相应 mctx 中提取 proof Expr。

这个实验解释了为什么 `exact? +all` 能显示多个完整建议，却不能顺手把第一个解留在目标中。

# 候选太多以后，才需要结论索引
%%%
tag := "ch08-s04"
%%%

小候选表可以逐项尝试，完整库却有大量声明。每次都从头扫描会把大部分时间浪费在结论形状明显不符的项上。生产实现因此预先按“声明最终能得到什么结论”建立索引。查询目标时，索引只召回轮廓相近的声明；真正可用与否仍由后面的 `apply` 决定。

声明类型开头可能有一串 `∀` 参数。把这些参数暂时打开、露出末端结论的操作常叫打开 telescope（望远镜）。例如 `∀ {P Q}, P → Q → P ∧ Q` 的末端结论是 `P ∧ Q`。`addImport` 对每个公开声明做三件事：

1. 排除 deprecated 声明和元编程命名空间中的声明；
2. 打开声明类型最外层的 `∀` telescope；
3. 用最终结论创建 discrimination-tree entry。

生产代码的骨架是：

:::codeBox "code"
```
forallTelescope constInfo.type fun _ type => do
  let entry ← InitEntry.fromExpr type (name, DeclMod.none)
  if entry.key == .const ``Iff 2 then
    -- 额外加入 Iff.mp 与 Iff.mpr 两个方向
    ...
  else
    ...
```
:::

索引记录的是声明名和一个方向修饰，不提前制造完整 proof Expr。实际尝试候选时，`mkLibrarySearchLemma` 才用 fresh universe metavariables 建常量；若修饰是 `mp` 或 `mpr`，再把 `Iff.mp` 或 `Iff.mpr` 映射到 telescope 末端。

## 过滤不只发生在这一层
%%%
tag := "ch08-s05"
%%%

不能把上面两条过滤说成“完整过滤规则”。LazyDiscrTree 建树时还会排除 unsafe、completion 不适用、不可访问内部声明、`sorryAx` 和若干生成名。教学上应把它们分成两层：Library Search 的候选政策，以及通用惰性索引的插入政策。

# 判别树：按外形缩小候选范围
%%%
tag := "ch08-s06"
%%%

这类索引叫 discrimination tree（判别树）。可以把它想成按表达式外层结构分叉的目录：等式目标先走“`Eq`”分支，箭头目标先走“arrow”分支，数值字面量走“literal”分支。每一步用于选分支的结构摘要叫 key（键）。生产 key 包括：

:::codeBox "code"
```
const name arity
fvar id arity
literal
star
other
arrow
projection structure field arity
```
:::

对 `List α`、`x = y`、`P → Q`、投影应用和数值字面量，树可以沿不同路径检索。某些位置暂时不能稳定区分，例如应由统一器决定的隐式参数；这些位置压成 `star`，意思是“这里先接受任意结构”。这样会多召回一些假阳性，却不容易过早漏掉候选。

“discrimination tree 做统一”是本章最需要删掉的误解。树回答的是“哪些声明值得试”；`MVarId.apply` 才回答“这个声明在当前 mctx 中能不能用”。

## 为什么还要“惰性”
%%%
tag := "ch08-s07"
%%%

导入模块中可能有数万条声明。若每次载入环境都立即展开整棵索引，许多从未查询的分支也会付出成本。lazy（惰性）表示先把待加入项留在 pending 区，查询真正走到相关 trie（前缀树）节点时再处理。environment extension（环境扩展）则让这份索引数据随 Lean 环境和模块导入一起维护。

第一遍不需要学习环境扩展的序列化接口。此处只记住可观察政策：查询先追加当前模块的 matches，再追加 imported matches，所以当前模块候选整体排在导入候选之前。

这是本书第一次完整使用 environment extension。Ch04 只需要查询 Environment，没有提前讲扩展缓存；这里第一次遇到真实需求，再介绍并不晚。

# 结构更具体，不等于数学上更自然
%%%
tag := "ch08-s08"
%%%

判别树用非 `star` 匹配数衡量 specificity（结构具体度）：目标中能对上越多明确结构，分数越高。它只衡量外形，不理解哪条证明对人最自然。候选大体按下列顺序进入尝试队列：

1. 当前模块候选整体在 imported 候选之前；
2. 每组内按结构具体度排序；
3. 同分沿稳定的内部遍历次序；
4. 原目标与对称目标的候选交错；
5. 主搜索没有合适结果时，才按配置考虑被丢到 star fallback 的宽泛声明。

这不是按名称、声明时间、用户心中的“最自然证明”或数学相关度排序。下面的对称等式就展示了这一点：搜索结果是合法的，却可能绕远。

下面的探针为同一个自定义目标分别声明当前模块与 imported theorem，再直接查看索引顺序：

```anchor exact_module_order_probe
elab "module_order_xray" : tactic => withMainContext do
  let target := mkConst ``tacticbook_exact_imported.SearchToken
  let candidates ← libSearchFindDecls target
  let relevant := candidates.filter fun (name, _) =>
    name == ``currentToken || name == ``tacticbook_exact_imported.importedToken
  logInfo m!"current/imported order: {relevant.map (·.1) |>.toList}"

example : True := by
  module_order_xray
  trivial
```

锁定输出为：

:::codeBox "code"
```
current/imported order:
[tacticbook_exact.currentToken,
 tacticbook_exact_imported.importedToken]
```
:::


```anchor exact_iff_and_symm
example (P Q : Prop) (hPQ : P ↔ Q) (hP : P) : Q := by
  exact?

example (a b : Nat) (h : a = b) : b = a := by
  exact?
```

在锁定环境中，第二个例子没有简单地建议 `h.symm`，而是找到了一条更长的 `Nat.add_right_cancel` 路线。搜索器没读过你的审美标准。

# Iff 与对称目标
%%%
tag := "ch08-s09"
%%%

`Iff` 声明会额外按两个方向入树；等式目标则由 `librarySearchSymm` 尝试 `applySymm`，在原目标和对称目标上分别召回候选，再交错排列。每个对称候选都携带自己的 goal 和 MetavarContext。切换候选时必须同时切换两者，否则会把只存在于对称分支的元变量拿到原分支里使用。

Iff 方向来自索引 entry 的 modifier；等式对称来自临时改造目标。两者都表现为“反方向也能搜”，内部位置并不相同。

# 看见候选不等于候选能用
%%%
tag := "ch08-s17"
%%%

```anchor exact_candidate_xray
elab "candidate_xray" : tactic => withMainContext do
  let target ← (← getMainGoal).getType
  let candidates ← libSearchFindDecls target
  logInfo m!"indexed candidates for{indentExpr target}"
  logInfo m!"candidate count: {candidates.size}"
  for (name, modifier) in candidates[:min candidates.size 5] do
    let modifierName := match modifier with
      | .none => "plain"
      | .mp => "Iff.mp"
      | .mpr => "Iff.mpr"
    logInfo m!"  {name} ({modifierName})"

example (a b : Nat) : a = b → b = a := by
  intro h
  candidate_xray
  exact h.symm
```

这个探针只调用 `libSearchFindDecls`。目标 `b = a` 在当前库中召回许多声明，前五项甚至未必包含最终采用的证明。它们只是树认为结构上值得尝试的名字。若要判断某项可否成为证明，还得创建 constant Expr、处理 Iff modifier、调用 `apply`，再处理全部子目标。

不要用候选列表解释最终排序的全部语义；对称目标交错、当前模块候选、star fallback 和 heartbeat 都可能在后续改变尝试队列。

# 建议不是把 Expr 打印出来就完事
%%%
tag := "ch08-s16"
%%%

普通 tactic 成功后，`addExactSuggestion` 从已赋值目标提取 proof Expr，去掉头部 beta redex，雅印成 `exact ...` 或 `refine ...`。它还拿着搜索前保存的 `Tactic.SavedState`，在原始现场重放候选脚本。

若名字不可直接引用，建议器会再试 `expose_names`。partial suggestion 会附上 residual goals；重放失败可降成信息并解释需要类型标注或显式参数。

TryThis 最终把建议写入 info tree，包含 source range 和 replacement text，编辑器据此生成 code action。以下三件事仍然不同：

1. 内部已经构造出类型正确的 proof Expr；
2. 雅印得到一段人能读的 Syntax；
3. 在原位置替换后，这段脚本独立重编译通过。

term 前端的 `addTermSuggestion` 直接雅印已成功的 proof term，不走 tactic 建议的 saved-state 重放路径。

# `LibrarySuggestions` 是另一项服务
%%%
tag := "ch08-s16-library-suggestions"
%%%

名字相近不代表同一条管线：

```table
- 名称
- 职责
---
- `Lean.Meta.LibrarySearch`
- 用 LazyDiscrTree 召回结论，再 `apply` 和 `solveByElim`
---
- `Lean.LibrarySuggestions`
- premise selector API，返回声明、分数与标记
---
- `suggestions` tactic
- 打印当前 selector 的结果，不证明目标
```

`exact?` 主路径不调用 `LibrarySuggestions.select`。Lean core 也不自行注册 selector；在本书 `import Mathlib` 的锁定环境中，传递导入的默认 selector 才把 Sine Qua Non 结果与当前文件 theorem 交错。Ch11 的 `grind +suggestions` 使用的是这一额外服务，不是 Ch08 的候选树。

# 可信性账本
%%%
tag := "ch08-s19"
%%%

```table
- 环节
- 出错后果
- 是否直接提供定理
---
- LazyDiscrTree 插入、召回、排序
- 漏解、慢、建议变差
- 否
---
- `MVarId.apply` 与 `solveByElim`
- 候选失败或构造错误 proof Expr
- 构造候选 proof
---
- Meta snapshot / restore
- 分支污染、错误接受或崩溃
- 否
---
- 雅印与 TryThis replacement
- 建议难读、位置错、不能重放
- 否
---
- kernel type checking
- 拒绝错误 proof Expr
- 是最终检查者
```

Library Search 没有引入“相信搜索器说目标为真”的公理。索引、排序和 DFS 都可视为不可信搜索计算；成功必须落实为普通 proof Expr 并通过内核检查。搜索器 bug 仍可能造成严重工程问题，但“漏掉证明”和“接受假证明”不是一类故障。

# 失败应怎样分类
%%%
tag := "ch08-s20"
%%%

```table
- 现象
- 最先检查
---
- `exact?` 完全找不到相关引理
- 目标头是否过宽、声明是否被过滤、是否需要 `star := true`
---
- `apply?` 有 partial，`exact?` 失败
- residual goals、局部事实、深度 6、constructor 已关闭
---
- 建议很长或反直觉
- 候选排序、对称交错、同分稳定次序；不等于证明错误
---
- `using` 看似被忽略
- 项是否真是 fvar；required 约束的是局部关闭阶段
---
- `+all` 后声明含 sorry
- collect-all 设计上恢复所有候选并走 admit tail

搜索失败最多只能推出：在已导入模块、候选过滤、当前局部事实和本次资源限制下，程序没有找到“一个主候选先 `apply`，再由深度受限局部搜索关闭全部参数洞”的证明。这里不是“一步定理直接闭合”，也绝不能推出该命题在数学上不可证。
---
- TryThis 文本不能替换
- suggestion replay、名字暴露、source range、类型标注
---
- 搜索提前停止
- heartbeat reserve；不能据此断言不可证
```

# 生产源码纵切
%%%
tag := "ch08-s21"
%%%

按数据流阅读，不要按目录字母序：

:::codeBox "pseudocode"
```
Lean/Elab/Tactic/LibrarySearch.lean
  exact? / apply? / exact?% 的提交与 recovery

Lean/Meta/Tactic/LibrarySearch.lean
  addImport → libSearchFindDecls → librarySearchSymm
  → librarySearchLemma → tryOnEach → librarySearch

Lean/Meta/LazyDiscrTree.lean
  key path、惰性初始化、specificity、current/imported 次序

Lean/Meta/Tactic/SolveByElim.lean
  assumption set、DFS、required terms、深度与回溯

Lean/Meta/Tactic/TryThis.lean
  proof Expr → syntax → replay → info tree / code action
```
:::

第一遍只追普通 `exact?` 完整成功。第二遍分别追 `apply?` partial、`+all` 和 `exact?%` failure。四条分支一次混读，最容易把 admit 和提交关系写反。

# 练习
%%%
tag := "ch08-s22"
%%%

## 基础一：标四道门
%%%
tag := "ch08-s23"
%%%

对一个成功建议逐项标出：何时只是索引召回，何时完成统一，何时 residual goals 归零，何时 suggestion replay。

*答案*：召回发生在 `libSearchFindDecls`；统一在 `goal.apply`；关闭发生在 `solveByElim` 返回空目标列表；建议重放在 `addExactSuggestion` 使用初始 saved state 时。

## 基础二：为什么 `constructor` 没有参与
%%%
tag := "ch08-s24"
%%%

解释目标 `P ∧ Q` 有局部 `hP : P`、`hQ : Q` 时，Library Search 为什么仍可能成功，但成功不能归因于默认 `solveByElim` 的 constructor 规则。

*答案*：主索引可以召回 `And.intro` 或等价主引理；`apply` 产生两个参数洞，局部搜索再用 assumptions 关闭。Library Search 配置明确把 `constructor := false`。

## 进阶一：损坏回滚
%%%
tag := "ch08-s25"
%%%

修改 `book_exact`，只恢复 `Tactic.State.goals`，不恢复 Meta mctx。让第一个候选先给主目标或参数洞赋值后失败，观察第二个候选的异常状态。

*测试*：恢复后队列看似相同，但 `isAssigned` 或参数 metavariable 声明已经改变。再与完整 `saveState` 对照。

## 进阶二：保留 partial mctx
%%%
tag := "ch08-s26"
%%%

把缩小版返回类型改为 `Array (List MVarId × MetavarContext)`。每项失败前复制其 mctx，恢复初始状态后，再逐项 `withMCtx` 打印 residual goal 类型。

## 进阶三：候选排序实验
%%%
tag := "ch08-s27"
%%%

在一个辅助 imported module 和当前 module 中各声明一条能关闭同一自定义目标的 theorem，记录建议变化。交换 import 与当前声明的角色，区分当前模块政策和同组稳定次序。

## 挑战：最小 TryThis
%%%
tag := "ch08-s28"
%%%

给 `book_exact` 增加建议输出：从已赋值主目标取 proof Expr，生成 `exact` syntax，并在搜索前 saved state 上重放。先只支持单行 source range；再解释多行缩进、名字暴露和 partial subgoal 注释为什么会把实现复杂度推高。

# 本章边界
%%%
tag := "ch08-s29"
%%%

现在可以把 Library Search 看成“结构索引 + 定义等价统一 + 小型局部搜索 + 可重放输出”。下一章换一种完全不同的自动化：`ring` 不在定理库中猜主引理，而是把两边重化到规范形，并让每一步计算携带等式证明。
