# Ch04–Ch07 四层 Monad 章节路线图

> 状态：Ch04–Ch07 已按本路线实施；后续自动化章节见 `AutomationChapters.md`。
>
> 版本基准：Lean `leanprover/lean4:v4.32.2`；Mathlib revision `905b95818eb32af7874a58b427f50c1711a5e96c`。

## 一、为什么拆成四章

`CoreM`、`MetaM`、`TermElabM`、`TacticM` 不是四个同义名字。它们依次增加不同的计算现场：

```text
CoreM
  + 局部上下文、元变量上下文、定义等价等 Meta 状态
= MetaM
  + expected type、postponement、synthetic mvar 等项译补状态
= TermElabM
  + 当前证明术、recovery policy、有序活动目标队列
= TacticM
```

四章不各讲一遍 Monad。Monad、`pure`、`bind`、`do`、Reader、State、exception 的共同基础在 Ch04 借真实 CoreM 程序讲清；后三章只回答五个固定问题：

1. 上一层缺什么能力？
2. 这一层新增什么只读 `Context`？
3. 这一层新增什么可写 `State`？
4. 哪段真实生产代码非要这些能力不可？
5. 失败时保存、恢复和保留的分别是什么？

每章都以“任务先行”为原则：先让读者看到一个真实功能及其输出，再解释 API 和 monad 层。API 表用来回查，不承担叙事主线。

## 二、四章总表

| 章节 | 暂定标题 | 生产主线 | 两个补充案例 | 本章结束时读者应能说清 |
|---|---|---|---|---|
| Ch04 | `CoreM` | 完整拆解并复刻 `#print axioms` | `checkExponent`；fresh name 与状态恢复 | 全局环境、选项、源码位置、消息、info tree 和异常为什么组成一个可顺序组合的计算 |
| Ch05 | `MetaM：在局部上下文中改写表达式` | `MVarId.rewrite` 的 equality 路线 | `MVarId.apply` 尾段；`substCore` 的 dependent 分支 | `Expr`、局部上下文和元变量状态如何共同支持类型推断、定义等价、回滚和证明项构造 |
| Ch06 | `TermElabM：让句法获得类型` | `exact?%` term elaborator | `show T from e`；Mathlib Finset set-builder | 为什么译补不是纯 `Syntax → Expr`，expected type、延期任务、synthetic mvar 和 recovery 分别做什么 |
| Ch07 | `TacticM：把证明洞排成工作队列` | production `apply` frontend | `first`；`constructor <;> ...` | Meta 元变量与 tactic 活动目标列表不是一回事，证明术分派、目标调度和失败回滚如何配合 |

术语统一使用：

- `tactic`：正文称“证明术”，API 名和源码标识保持英文；
- `elaboration`：统一采用新的标准译名“译补”，首次出现保留英文；
- `expected type`：称“预期类型”，必要时括注英文；
- `metavariable`：称“元变量”；
- `goal queue`：称“活动目标队列”，避免把它与 `MetavarContext` 混成一个“证明状态”。

## 三、Ch05 MetaM 初步计划

### 3.1 读者入口

Ch04 的工具能查询全局声明，却回答不了以下问题：

- 这个 `Expr` 在当前局部假设下是什么类型？
- 两个表达式经过归约后是否定义等价？
- 搜索过程中创建的元变量应当提交还是撤销？
- 怎样构造一个经过内核检查的等式运输证明？

用这一组缺口引出：

```lean
MetaM := ReaderT Meta.Context (StateRefT Meta.State CoreM)
```

### 3.2 主线：`MVarId.rewrite`

只讲 `rw` 的 Meta 核心，不把用户写下的 `rw [h]` 整体误称为 MetaM 程序。主调用链：

```text
MVarId.rewrite
→ inferType rewrite theorem
→ forallMetaTelescopeReducing
→ mkAppN
→ matchEq?
→ kabstract
→ instantiate1
→ mkLambda motive
→ 构造 congrArg / Eq.mpr 一类证明项
→ 返回 RewriteResult
→ replaceTargetEq / replaceLocalDecl 提交目标变化
```

这条线承担本章的 `Expr` 教学，不另写一份构造子目录式章节。读者因实际改写需要，依次遇到：

- `app` spine、`const`、`fvar`、`mvar`；
- `lam`、`forallE`、`bvar` 与 de Bruijn index；
- abstract/instantiate；
- `inferType`、`whnf`、`isDefEq`；
- fresh metavariables 与状态回滚；
- motive 和 proof term；
- 局部声明与目标替换。

### 3.3 补充案例

1. `MVarId.apply` 尾段：只讲“创建参数洞—统一结论—给旧目标赋值—返回未赋值元变量”。不在本章引入 TacticM 的 goal queue。
2. `substCore` 的 dependent/nondependent 分叉：作为进阶节补局部依赖关系与 `Eq.rec` transport；若正文过长，可降为源码导读和挑战练习。

### 3.4 明确不讲

- `rw` 的 syntax/macro 和 `rewrite` tactic elaborator：留给 Ch07 或后续改写章节回看。
- 完整 `simp`：索引、缓存、congruence、simproc、discharger 会吞没 MetaM 入门主线。
- 把 syntactic equality 当 definitional equality。
- 把 `isDefEq : MetaM Bool` 描述成无状态谓词。

### 3.5 预期产物

- 一条可运行的 `rw_xray`，打印 theorem type、lhs、abstracted target、motive、新目标和 equality proof type；
- 一个明确观察 mvar 在 `isDefEq` 前后是否被赋值的 probe；
- binder 下匹配成功与失败各一例；
- production 实现、教材 x-ray、省略机制三列表；
- API 表按“观察 Expr / 构造 Expr / local context / mvar / defeq / 提交目标”分组。

## 四、Ch06 TermElabM 初步计划

### 4.1 读者入口

Ch05 中的 Meta API 接收已经存在的 `Expr`。用户实际输入的却是带省略、重载和记号的 `Syntax`。同一个 `3` 可以被译补成 `Nat`、`Int` 或 `Real`；这不是只看句法树便能决定的。

由此引出：

```lean
TermElabM := ReaderT Term.Context (StateRefT Term.State MetaM)
TermElab  := Syntax → Option Expr → TermElabM Expr
```

### 4.2 主线：`exact?%`

默认生产路径：

```text
term Syntax
→ withExpectedType
→ mkFreshExprMVar expectedType
→ intros
→ 在目标 local context 中运行 MetaM librarySearch
→ 成功：回收完整 proof Expr 并添加建议
→ 失败：logError + typed synthetic sorry
```

选它的原因：前端短，能在一章内闭合；expected type、postponement、元变量、局部上下文、状态提交/回滚、诊断和 recovery 都有真实落点；默认路径不进入 `TacticM`。

### 4.3 补充案例

1. `show T from e`：补 expected type 的双向传播、`isDefEq`、coercion，以及“生成新 Syntax 后递归调用 `elabTerm`”。
2. Mathlib Finset set-builder：同一 syntax kind 注册多个 elaborator；expected type 决定谁接管；`throwUnsupportedSyntax` 表示回退而不是用户错误；某些高优先级 elaborator 故意不 postpone，避免挡住低优先级候选。

### 4.4 明确不讲

- 不把完整 function application elaborator 当主线：机制最全，但源码规模过大。
- 不把匿名构造器 `⟨...⟩` 当“严格不进入 TacticM”的主例：带 `autoParam` 的完整路径可能登记 tactic synthetic mvar，收尾时运行 `TacticM`。
- 不把 tactic `exact?` 与 term `exact?%` 混在一起。
- 不在本章展开 Library Search 候选索引；只把它当 `MVarId → MetaM ...` 的真实后端。

### 4.5 预期产物

- 受控版 `exact?%` term elaborator；
- expected type 已知、未知而延期、最终无法取得三种路径；
- `show Int from (0 : Nat)` coercion probe；
- Set/Finset 同形 syntax 的 elaborator fallback probe；
- synthetic mvar 与 tactic goal queue 的对照图；
- API 表按“入口 / expected type / 递归译补 / postponement / synthesis / recovery / registration”分组。

## 五、Ch07 TacticM 初步计划

### 5.1 读者入口

TermElabM 已能把用户写的项译补成 proof `Expr`，MetaM 已能创建和赋值元变量，但还没有回答：

- 现在有几个活动目标？
- 下一条证明术处理哪一个？
- 一个目标拆成三个以后按什么顺序继续？
- 一个候选失败后，目标队列和 Meta 赋值是否一起恢复？

由此引出：

```lean
TacticM := ReaderT Tactic.Context (StateRefT Tactic.State TermElabM)
```

这一层新增的状态很薄：核心是 `goals : List MVarId`。元变量声明和赋值仍住在继承的 `Meta.State.mctx` 中。

### 5.2 主线：production `apply`

```text
apply syntax
→ evalTactic 分派并记录当前 elaborator
→ elabTermForApply 译补 theorem term
→ MVarId.apply 创建参数元变量、统一结论、赋值旧目标
→ 返回未解决元变量
→ synthesizeSyntheticMVarsNoPostponing
→ replaceMainGoal 安装有序子目标
```

`apply` 能把四层串起来，同时让各层职责仍然可分：

- 参数 Syntax→Expr：TermElabM；
- 元变量、统一、旧目标赋值：MetaM；
- 子目标列表替换：TacticM；
- 环境、消息和异常：CoreM。

### 5.3 补充案例

1. `first | ... | ...`：第一支先给目标赋值再故意失败，第二支仍能看到原目标；据此证明回滚来自显式 saved-state/control operator，不是 `do` 或 Monad 自动提供。
2. `constructor <;> exact h`：`constructor` 通过 Meta `apply` 产生两个目标；`<;>` 展开为 `focus` 与 `all_goals`，逐个 singleton 化目标队列并重新拼接。

### 5.4 必讲底座

`evalTactic` 不宜单独充当“目标变换”主例，但必须解释：

- syntax kind 与 elaborator 注册表；
- `Tactic.Context.elaborator`；
- macro/elaborator fallback；
- before/after tactic info；
- recovery 模式；
- nested tactic 如何再次调用 dispatcher。

### 5.5 明确不讲

- 不用 `cases` 作入门主线：alternatives、eliminator、tags、recovery 和 incremental snapshots 同时出现，负担太重。
- 不用 `exact` 单独撑整章：它只展示“译补一项并关闭队首”，新增的 queue 语义不足。
- 不把“从 goals 列表移除”说成“目标已经证明”；是否证明取决于对应 mvar 是否已赋值。

### 5.6 预期产物

- 缩小版 production `apply`；
- `mctx` 与 `goals` 双层状态图；
- `first` 完整回滚 probe；
- `<;>` 展开与 goal queue 逐步快照；
- goal tag 继承/追加例；
- API 表按“取得目标 / 运行于目标上下文 / Meta 变换 / 替换队列 / dispatcher / backtracking”分组。

## 六、跨章防重复约定

| 主题 | 首次完整讲解 | 其他章节只允许怎样引用 |
|---|---|---|
| `pure`、`bind`、`do`、Reader/State/exception | Ch04 | 用一句话指出新增层，不重复玩具教程 |
| `Expr` 构造与 binder | Ch05 | Ch06/Ch07 只解释本例实际产生或消费的 Expr |
| `isDefEq` 的赋值与回滚 | Ch05 | 后章引用其契约，不重新证明 |
| expected type、coercion、postponement | Ch06 | Ch07 只说明 `apply` 如何调用 term elaboration |
| goal queue、`replaceMainGoal`、combinator rollback | Ch07 | Ch05 不把 `List MVarId` 当 MetaM 状态 |
| CommandElabM | Ch04 的真实命令外壳 | 后章仅在需要注册 command 时交叉引用 |

## 七、共同写作模板

每章正文按同一节奏推进：

```text
先运行真实功能
→ 遇到上一层无法解释的现象
→ 查看这一层 Context/State
→ 沿生产调用链拆开
→ 写一个受控缩小版
→ 制造失败并观察状态
→ 回到生产版本核对省略项
→ API 详表与练习
```

行文沿用现有 Ch02/Ch03 的特点：直接称“你”，代码后逐行解释，真实源码与自写实现并列，允许少量针对真实坑点的吐槽。不使用“让我们来看看”“值得注意的是”一类开场填充，也不在每节末尾重复总结。

## 八、后三章目前冻结到什么程度

已经冻结：

- 每章最高能力层；
- 主例与两个补充案例；
- 关键源码调用链；
- 与相邻章节的内容边界；
- 最低可运行产物。

暂不冻结：

- 具体节数和编号；
- 每章代码块数量；
- `substCore` 是否进入 Ch05 正文还是挑战阅读；
- Ch06 Finset set-builder 是否要求读者亲自实现；
- Ch07 是否另开 goal tags 小节。

这些在 Ch04 定稿后，根据实际篇幅和读者反馈再决定，避免四章同时写死后一起返工。
