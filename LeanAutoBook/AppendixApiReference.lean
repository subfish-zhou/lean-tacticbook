import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

#doc (Manual) "附录 A：Metaprogramming API 速查表" =>
%%%
file := "AppendixApiReference"
tag := "appendix-api-reference"
%%%

本附录按 monad 层分类，列出本书各章提到的所有常用元编程 API。每个条目给出签名、所在层、用途、简短示例和注意事项。API 按使用频率排序（常用在前）。

**图标说明**：条目标题后的图标表示使用层级——

- 没有图标 = 核心常用 API，日常 tactic 开发的基本工具
- 🔧 = 高级或版本敏感 API，仅在特殊场景下需要

# 最小 tactic 工作流模板
%%%
tag := "appendix-api-minimal-template"
%%%

第一次写自定义 tactic？从这个 10 行模板开始：

```
import Lean
open Lean Elab Tactic Meta

elab "my_first_tactic" : tactic => do
  let goal ← getMainGoal        -- 拿到当前目标（MVarId）
  let target ← goal.getType     -- 目标类型（Expr，即"要证什么"）
  let target ← whnf target      -- 规约到弱头范式，露出顶层结构
  logInfo m!"goal type: {target}" -- 在 InfoView 里显示
  -- 在这里添加你的证明逻辑
```

**建议阅读顺序**：先通读 Ch01，掌握 `getMainGoal` / `goal.getType` / `whnf` / `goal.assign` 四件套，再按需查阅本附录。

# A.1 CoreM 层
%%%
tag := "appendix-api-corem"
%%%

`CoreM` 是整个元编程栈的基础层（最底层的 monad，所有上层 monad 都继承它的能力），提供环境访问、名字生成和选项读取。

## `getEnv`
%%%
tag := "appendix-api-getenv"
%%%

- **签名**: `CoreM Environment`
- **用途**: 获取当前环境（environment，即所有已声明的定义、定理、公理的集合）的只读快照
- **示例**: `let env ← getEnv; if env.contains Nat.add then ...`
- **注意**: 返回的是快照，后续修改环境不会反映到已获取的值
- **推荐掌握时机**: Ch01 后

## `getOptions`
%%%
tag := "appendix-api-getoptions"
%%%

- **签名**: `CoreM Options`
- **用途**: 读取当前用户选项（`set_option` 设置的值）
- **推荐掌握时机**: Ch05 后

## `mkFreshId`
%%%
tag := "appendix-api-mkfreshid"
%%%

- **签名**: `CoreM Name`
- **用途**: 生成一个全局唯一的名字
- **推荐掌握时机**: Ch03 后

# A.2 MetaM 层
%%%
tag := "appendix-api-metam"
%%%

`MetaM` 是元编程的核心层（在 `CoreM` 之上，增加了元变量管理和统一化），提供类型检查、元变量（metavariable，即待填充的"洞"）管理、表达式规约（reduction，把表达式化简到更基本的形式）和 unification（统一化，判断两个表达式是否"本质相同"并尝试让它们匹配）。

## `inferType`
%%%
tag := "appendix-api-infertype"
%%%

- **签名**: `Expr → MetaM Expr`
- **用途**: 推断表达式的类型
- **示例**: `let ty ← inferType (mkConst Nat.zero)  -- 得到 Nat`
- **注意**: 对含自由变量（free variable，局部上下文中的变量）的表达式，需在正确的 `LocalContext` 中调用
- **推荐掌握时机**: Ch01 后
- **出现章节**: Ch01, Ch02, Ch05

## `isDefEq`
%%%
tag := "appendix-api-isdefeq"
%%%

- **签名**: `Expr → Expr → MetaM Bool`
- **所在层**: MetaM
- **用途**: 判断两个表达式是否定义等价（definitional equality，经过规约后完全一致）；会触发 unification 副作用

**示例**：

```
if ← isDefEq declType target then
  goal.assign decl.toExpr
```

- **注意**: **有副作用**——可能会赋值元变量。如果只想检查而不想影响状态，用 `withoutModifyingState`
- **推荐掌握时机**: Ch01 后
- **出现章节**: Ch01, Ch03, Ch06, Ch19

## `whnf`
%%%
tag := "appendix-api-whnf"
%%%

- **签名**: `Expr → MetaM Expr`
- **用途**: 将表达式规约到弱头范式（Weak Head Normal Form，只展开最外层，露出顶层构造子）
- **示例**: `let e ← whnf target`
- **注意**: 只规约"头部"，不深入子项；需要完全规约用 `reduce`
- **推荐掌握时机**: Ch01 后
- **出现章节**: Ch02

## `reduce`
%%%
tag := "appendix-api-reduce"
%%%

- **签名**: `Expr → MetaM Expr`
- **用途**: 尽可能完全规约表达式（比 `whnf` 更彻底但更慢）
- **推荐掌握时机**: Ch02 后

## `mkFreshExprMVar`
%%%
tag := "appendix-api-mkfreshexprmvar"
%%%

- **签名**: `Option Expr → MetaM Expr`
- **用途**: 创建一个新的元变量（hole，即待填充的占位符）；参数是可选的期望类型
- **示例**: `let mvar ← mkFreshExprMVar (some targetType)`
- **注意**: 新元变量未赋值——它会成为需要后续处理的子目标
- **推荐掌握时机**: Ch01 后
- **出现章节**: Ch01, Ch03

## `instantiateMVars`
%%%
tag := "appendix-api-instantiatemvars"
%%%

- **签名**: `Expr → MetaM Expr`
- **用途**: 将表达式中已赋值的元变量替换为其赋值
- **注意**: 在检查证明项完整性前应当调用
- **推荐掌握时机**: Ch19 后
- **出现章节**: Ch19

## `forallTelescope`
%%%
tag := "appendix-api-foralltelescope"
%%%

- **签名**: `Expr → (Array Expr → Expr → MetaM α) → MetaM α`
- **用途**: 展开 `∀` 类型，将绑定变量（bound variable）转为 fvar（free variable），进入 body

**示例**：

```
forallTelescope goalType fun fvars body => do
  -- fvars: 量化变量（fvar）; body: bvar 已替换为 fvar
```

- **注意**: fvar 只在回调内有效，**不要泄漏到回调外部**
- **配对记忆**: `forallE ↔ forallTelescope`（构造子 vs 展开器），逆操作是 `mkForallFVars`
- **推荐掌握时机**: Ch01 后
- **出现章节**: Ch01, Ch02

## `lambdaTelescope`
%%%
tag := "appendix-api-lambdatelescope"
%%%

- **签名**: `Expr → (Array Expr → Expr → MetaM α) → MetaM α`
- **用途**: 展开 `λ` 表达式，将绑定变量转为 fvar，进入 body
- **注意**: 与 `forallTelescope` 对称；同样不要泄漏 fvar
- **配对记忆**: `lam ↔ lambdaTelescope`，逆操作是 `mkLambdaFVars`
- **推荐掌握时机**: Ch02 后
- **出现章节**: Ch02

## `withLocalDecl`
%%%
tag := "appendix-api-withlocaldecl"
%%%

- **签名**: `Name → BinderInfo → Expr → (Expr → MetaM α) → MetaM α`
- **用途**: 临时向局部上下文添加一个变量，回调结束后自动移除
- **推荐掌握时机**: Ch02 后

**示例**：

```
withLocalDecl `x .default (mkConst ``Nat) fun x => do ...
```

## `mkForallFVars` / `mkLambdaFVars`
%%%
tag := "appendix-api-mkforallfvars"
%%%

- **签名**: `Array Expr → Expr → MetaM Expr`
- **用途**: 将 body 中的 fvar 抽象为 `∀`/`λ` 绑定（与 telescope 系列互逆）
- **示例**: `let ty ← mkForallFVars fvars body`
- **配对记忆**: `forallTelescope` 展开 → `mkForallFVars` 重建；`lambdaTelescope` 展开 → `mkLambdaFVars` 重建
- **推荐掌握时机**: Ch01 后
- **出现章节**: Ch01

## `kabstract`
%%%
tag := "appendix-api-kabstract"
%%%

- **签名**: `Expr → Expr → MetaM Expr`
- **用途**: 将表达式中匹配指定子项的部分抽象为 `bvar`（bound variable，de Bruijn 索引表示的绑定变量）
- **注意**: 支持 `occurrences` 参数控制替换哪些出现
- **推荐掌握时机**: Ch02 后
- **出现章节**: Ch02

## `isProof` / `isProp`
%%%
tag := "appendix-api-isproof-isprop"
%%%

- **签名**: `Expr → MetaM Bool`
- **用途**: `isProof` 判断表达式是否为证明项（proof term）；`isProp` 判断其类型是否为 `Prop`（命题宇宙）
- **推荐掌握时机**: Ch02 后
- **出现章节**: Ch02

## `synthInstance?` / `synthInstance`
%%%
tag := "appendix-api-synthinstance"
%%%

- **签名**: `Expr → MetaM (Option Expr)` / `Expr → MetaM Expr`
- **用途**: 搜索 type class（类型类，Lean 的自动实例推断机制）实例；`synthInstance?` 失败时返回 `none`，`synthInstance` 失败时直接报错

**示例**：

```
-- 推荐：先用 synthInstance?，可以优雅地处理搜索失败
match ← synthInstance? (← mkAppM ``Inhabited #[α]) with
| some inst => logInfo m!"found: {inst}"
| none      => throwError "no Inhabited instance for {α}"

-- 也可以查找 OfNat 实例
let inst ← synthInstance (← mkAppM ``OfNat #[mkConst ``Nat, mkNatLit 0])
```

- **注意**: 推荐优先使用 `synthInstance?`，它让你能在搜索失败时给出更好的错误信息，而不是直接抛出内部错误
- **推荐掌握时机**: Ch05 后
- **出现章节**: Ch05

## `isInstance`
%%%
tag := "appendix-api-isinstance"
%%%

- **签名**: `Name → MetaM Bool`
- **用途**: 检查某个声明是否被标记为 type class instance
- **推荐掌握时机**: Ch05 后
- **出现章节**: Ch05

## `mkAppM`
%%%
tag := "appendix-api-mkappm"
%%%

- **签名**: `Name → Array Expr → MetaM Expr`
- **用途**: 创建函数应用并自动填充隐式参数（implicit argument，由编译器推断的参数）和 universe level

**示例**：

```
-- mkAppM 自动推断隐式参数和 universe level
let eqRefl ← mkAppM ``Eq.refl #[a]

-- 对比：手动用 mkConst + mkAppN 需要自己提供所有参数
let eqRefl := mkApp2 (mkConst ``Eq.refl [levelOne]) ty a
-- 注意手动版本需要知道 Eq.refl 的 universe level 和类型参数
```

- **注意**: 比手动 `mkApp` + `mkConst` 方便得多，自动处理 universe polymorphism。如果 `mkAppM` 报错"failed to synthesize"或"type mismatch"，通常意味着提供的显式参数不足以推断出所有隐式参数——此时可以用 `mkAppOptM` 手动指定部分隐式参数，或检查参数类型是否正确
- **推荐掌握时机**: Ch05 后
- **出现章节**: Ch05, Ch14, Ch19

## `mkConstWithFreshMVarLevels`
%%%
tag := "appendix-api-mkconstwithfreshmvarlevels"
%%%

- **签名**: `Name → MetaM Expr`
- **用途**: 创建常量引用并为 universe 参数生成新的元 level
- **推荐掌握时机**: Ch05 后

## `mkEqRefl`
%%%
tag := "appendix-api-mkeqrefl"
%%%

- **签名**: `Expr → MetaM Expr`
- **用途**: 构造 `@Eq.refl α a` 证明项
- **推荐掌握时机**: Ch01 后
- **出现章节**: Ch01

## `withoutModifyingState`
%%%
tag := "appendix-api-withoutmodifyingstate"
%%%

- **签名**: `MetaM α → MetaM α`
- **用途**: 执行操作但不保留对状态的修改（用于探测性检查）
- **示例**: `let canUnify ← withoutModifyingState (isDefEq a b)`
- **注意**: 常用于"试探" `isDefEq` 而不想留下副作用
- **推荐掌握时机**: Ch01 后
- **出现章节**: Ch01, Ch03

## `withOptions`
%%%
tag := "appendix-api-withoptions"
%%%

- **签名**: `(Options → Options) → MetaM α → MetaM α`
- **用途**: 临时修改选项后执行操作
- **推荐掌握时机**: Ch05 后
- **出现章节**: Ch05

## `withNewLocalInstance`
%%%
tag := "appendix-api-withnewlocalinstance"
%%%

- **签名**: `Name → Expr → MetaM α → MetaM α`
- **用途**: 临时向 type class 搜索添加一个局部实例
- **推荐掌握时机**: Ch05 后
- **出现章节**: Ch05

# A.3 TermElabM 层
%%%
tag := "appendix-api-termelabm"
%%%

`TermElabM` 处理从语法（`Syntax`，Lean 的抽象语法树表示）到表达式（`Expr`，Lean 的内核项表示）的精化（elaboration，把用户写的语法转换为类型正确的内核表达式）过程。

## `elabTerm`
%%%
tag := "appendix-api-elabterm"
%%%

- **签名**: `Syntax → Option Expr → TermElabM Expr`
- **用途**: 将语法精化为表达式；第二个参数是可选的期望类型
- **示例**: `` let e ← elabTerm (← `(Nat.add 2 3)) none ``
- **注意**: 有 elaboration 开销；性能敏感时优先用 `mkApp` 系列手动构造
- **推荐掌握时机**: Ch02 后
- **出现章节**: Ch02, Ch05

## `elabType`
%%%
tag := "appendix-api-elabtype"
%%%

- **签名**: `Syntax → TermElabM Expr`
- **用途**: 将语法精化为类型（期望结果是 `Sort _`）
- **推荐掌握时机**: Ch02 后

# A.4 TacticM 层
%%%
tag := "appendix-api-tacticm"
%%%

`TacticM` 是 tactic 的直接运行环境（最上层 monad），管理目标列表（goal list，每个目标对应一个待证明的元变量）。

## `getMainGoal`
%%%
tag := "appendix-api-getmaingoal"
%%%

- **签名**: `TacticM MVarId`
- **用途**: 获取当前目标列表的第一个目标（主目标）；列表为空时抛出 "no goals"
- **推荐掌握时机**: Ch01 后
- **出现章节**: Ch01, Ch03, Ch04, Ch05, Ch07, Ch14, Ch19

## `getMainTarget`
%%%
tag := "appendix-api-getmaintarget"
%%%

- **签名**: `TacticM Expr`
- **用途**: 获取主目标的类型（即需要证明的命题）
- **推荐掌握时机**: Ch01 后
- **出现章节**: Ch01, Ch04, Ch05

## `getGoals` / `setGoals`
%%%
tag := "appendix-api-getgoals-setgoals"
%%%

- **签名**: `TacticM (List MVarId)` / `List MVarId → TacticM Unit`
- **用途**: 直接读写目标列表（不做过滤）
- **注意**: `setGoals` 不过滤已解决目标——可能需要配合 `getUnsolvedGoals`
- **推荐掌握时机**: Ch03 后
- **出现章节**: Ch03, Ch04, Ch19

## `getUnsolvedGoals`
%%%
tag := "appendix-api-getunsolvedgoals"
%%%

- **签名**: `TacticM (List MVarId)`
- **用途**: 获取目标列表并过滤掉已赋值的元变量
- **推荐掌握时机**: Ch04 后
- **出现章节**: Ch04

## `replaceMainGoal`
%%%
tag := "appendix-api-replacemaingoal"
%%%

- **签名**: `List MVarId → TacticM Unit`
- **用途**: 用新的子目标列表替换主目标（新目标在前，旧的其余目标在后）
- **推荐掌握时机**: Ch04 后
- **出现章节**: Ch04

## `closeMainGoal` 🔧
%%%
tag := "appendix-api-closemaingoal"
%%%

- **签名**: `Expr → TacticM Unit`
- **用途**: 用给定证明项关闭主目标（assign + 移除）
- **注意**: 此 API 名称在不同 Lean 4 版本间可能有变化，建议以当前 toolchain 的 API 文档为准。等价的手动写法：`goal.assign proof; replaceMainGoal \[\]`
- **推荐掌握时机**: Ch19 后
- **出现章节**: Ch19

## `MVarId.assign`
%%%
tag := "appendix-api-mvarid-assign"
%%%

- **签名**: `MVarId → Expr → MetaM Unit`
- **用途**: 将证明项赋值给元变量，关闭对应目标
- **示例**: `goal.assign proofExpr`
- **注意**: 赋值后 `MVarId` 标记为已解决，但仍可能留在目标列表中
- **推荐掌握时机**: Ch01 后
- **出现章节**: Ch01, Ch03, Ch04

## `MVarId.getType` / `MVarId.isAssigned`
%%%
tag := "appendix-api-mvarid-gettype"
%%%

- **签名**: `MVarId → MetaM Expr` / `MVarId → MetaM Bool`
- **用途**: 获取目标类型 / 检查是否已赋值
- **推荐掌握时机**: Ch03 后
- **出现章节**: Ch03, Ch04

## `MVarId.intro`
%%%
tag := "appendix-api-mvarid-intro"
%%%

- **签名**: `MVarId → Name → MetaM (FVarId × MVarId)`
- **用途**: 对目标执行 `intro`，返回引入的变量和新目标
- **示例**: `` let (fvar, newGoal) ← goal.intro `h ``
- **推荐掌握时机**: Ch03 后
- **出现章节**: Ch03, Ch04

## `MVarId.withContext` / `withMainContext`
%%%
tag := "appendix-api-mvarid-withcontext"
%%%

- **签名**: `MVarId → MetaM α → MetaM α` / `TacticM α → TacticM α`
- **用途**: 在目标的局部上下文中执行操作

**示例**：

```
withMainContext do
  let lctx ← getLCtx
  for decl in lctx do ...
```

- **注意**: 访问目标的局部假设前**必须**先进入其上下文
- **推荐掌握时机**: Ch03 后
- **出现章节**: Ch03, Ch04, Ch05, Ch07, Ch19

## `getLCtx`
%%%
tag := "appendix-api-getlctx"
%%%

- **签名**: `MetaM LocalContext`
- **用途**: 获取当前局部上下文（所有局部变量和假设）
- **注意**: `LocalDecl` 有 `.userName`、`.type`、`.toExpr` 等字段；用 `.isImplementationDetail` 过滤内部变量
- **推荐掌握时机**: Ch03 后
- **出现章节**: Ch03, Ch04, Ch05

## `focus`
%%%
tag := "appendix-api-focus"
%%%

- **签名**: `TacticM α → TacticM α`
- **用途**: 隔离主目标——回调中只能看到主目标，结束后子目标自动合并回
- **推荐掌握时机**: Ch04 后
- **出现章节**: Ch04

## `saveState` / `restoreState`
%%%
tag := "appendix-api-savestate"
%%%

- **签名**: `TacticM SavedState` / `SavedState → TacticM Unit`
- **用途**: 保存/恢复 tactic 状态，用于回溯（backtracking，尝试一种策略失败后恢复到之前的状态）
- **示例**: `let saved ← saveState; try ... catch _ => restoreState saved; ...`
- **推荐掌握时机**: Ch04 后
- **出现章节**: Ch04

## `tryTactic?` 🔧
%%%
tag := "appendix-api-trytactic"
%%%

- **签名**: `TacticM Unit → TacticM (Option Unit)`
- **所在层**: TacticM
- **用途**: 尝试执行 tactic，失败时返回 `none` 并回滚状态
- **注意**: 此 API 名称在不同 Lean 4 版本间可能有变化。如果编译报错，可用 `saveState`/`restoreState` 手动实现等价逻辑
- **推荐掌握时机**: Ch04 后
- **出现章节**: Ch04

## `evalTactic`
%%%
tag := "appendix-api-evaltactic"
%%%

- **签名**: `Syntax → TacticM Unit`
- **所在层**: TacticM
- **用途**: 执行由 `Syntax` 表示的 tactic（在元编程中调用其他 tactic）
- **示例**: `` evalTactic (← `(tactic| simp [Nat.add_comm])) ``
- **注意**: 常与 syntax quotation 配合使用；是 tactic 组合的主要手段
- **推荐掌握时机**: Ch03 后
- **出现章节**: Ch03, Ch04, Ch06, Ch07, Ch08

## `liftMetaTactic`
%%%
tag := "appendix-api-liftmetatactic"
%%%

- **签名**: `(MVarId → MetaM (List MVarId)) → TacticM Unit`
- **用途**: 将 `MetaM` 层的目标操作提升到 `TacticM`
- **推荐掌握时机**: Ch04 后

# A.5 错误处理与日志
%%%
tag := "appendix-api-error-logging"
%%%

## `throwError`
%%%
tag := "appendix-api-throwerror"
%%%

- **签名**: `MessageData → MetaM α`（各层均可用）
- **用途**: 抛出带格式化消息的错误
- **示例**: `throwError "expected equality, got {← ppExpr target}"`
- **推荐掌握时机**: Ch01 后
- **出现章节**: Ch02, Ch03, Ch04, Ch05, Ch19

## `throwTacticEx`
%%%
tag := "appendix-api-throwtacticex"
%%%

- **签名**: `Name → MVarId → MessageData → TacticM α`
- **用途**: 抛出 tactic 错误，自动包含目标上下文信息
- **推荐掌握时机**: Ch01 后
- **出现章节**: Ch01, Ch03

## `logInfo` / `logWarning`
%%%
tag := "appendix-api-loginfo"
%%%

- **签名**: `MessageData → CoreM Unit`（各层均可用）
- **用途**: 输出信息/警告消息（在 InfoView 中显示）
- **示例**: `logInfo m!"Found {matches.size} matching lemmas"`
- **推荐掌握时机**: Ch01 后
- **出现章节**: Ch03, Ch04, Ch07

## `ppExpr`
%%%
tag := "appendix-api-ppexpr"
%%%

- **签名**: `Expr → MetaM Format`
- **用途**: 将 `Expr` 转为人类可读格式
- **注意**: 在 `m!"..."` 插值中 `Expr` 会自动调用 `ppExpr`
- **推荐掌握时机**: Ch01 后
- **出现章节**: Ch01

# A.6 Expr 构造函数
%%%
tag := "appendix-api-expr-constructors"
%%%

## `mkConst`
%%%
tag := "appendix-api-mkconst"
%%%

- **签名**: `Name → List Level → Expr`（纯函数）
- **用途**: 创建对已声明常量的引用
- **示例**: `let natAdd := mkConst Nat.add`
- **注意**: universe level 默认 `[]`；多态定义需提供正确 level
- **配对记忆**: 构造用 `mkConst`，匹配/提取用 `Expr.constName?`
- **推荐掌握时机**: Ch01 后
- **出现章节**: Ch01, Ch02, Ch03, Ch05

## `mkApp` / `mkApp2` / `mkApp3` / `mkApp4` / `mkAppN`
%%%
tag := "appendix-api-mkapp"
%%%

- **签名**: `Expr → Expr → Expr`（mkApp）/ `Expr → Array Expr → Expr`（mkAppN）
- **用途**: 构造函数应用（单参数/多参数/数组参数）
- **示例**: `let eq := mkApp3 (mkConst Eq) (mkConst Nat) a b`
- **配对记忆**: 构造用 `mkApp`，分析用 `Expr.getAppFn` + `Expr.getAppArgs`
- **推荐掌握时机**: Ch02 后
- **出现章节**: Ch02, Ch03

## `mkLambda` / `mkForall`
%%%
tag := "appendix-api-mklambda-mkforall"
%%%

- **签名**: `Name → BinderInfo → Expr → Expr → Expr`（纯函数）
- **用途**: 构造 `λ` / `∀`/`→` 表达式（使用 de Bruijn 索引，一种用数字代替变量名的表示方式）
- **示例**: ``mkLambda `n .default (mkConst Nat) (.bvar 0)``  -- `fun n : Nat => n`
- **配对记忆**: `mkLambda ↔ lambdaTelescope`，`mkForall ↔ forallTelescope`
- **推荐掌握时机**: Ch02 后

## `mkNatLit`
%%%
tag := "appendix-api-mknatlit"
%%%

- **签名**: `Nat → Expr`（纯函数）
- **用途**: 创建自然数字面量
- **推荐掌握时机**: Ch01 后

# A.7 Expr 匹配与分析
%%%
tag := "appendix-api-expr-matching"
%%%

## `match\_expr` / `let\_expr` 语法
%%%
tag := "appendix-api-match-expr"
%%%

- **用途**: 按 head constant 匹配表达式，自动解开嵌套的 `app`。示例：`match_expr target with | Eq α lhs rhs => ... | And p q => ...`
- **注意**: 只按 head constant 匹配；对 `forallE` 等 binder 构造子无效，需用普通 `match`
- **推荐掌握时机**: Ch02 后
- **出现章节**: Ch02, Ch03, Ch19

## `Expr.getAppFn` / `Expr.getAppArgs`
%%%
tag := "appendix-api-expr-getappfn"
%%%

- **签名**: `Expr → Expr` / `Expr → Array Expr`（纯函数）
- **用途**: 获取应用头函数 / 所有参数
- **示例**: `target.getAppFn` 对 `f a b c` 返回 `f`；`target.getAppArgs` 返回 `#\[a, b, c\]`
- **配对记忆**: 与 `mkApp` / `mkAppN` 互逆——`mkApp` 组装，`getAppFn`/`getAppArgs` 拆解
- **推荐掌握时机**: Ch02 后
- **出现章节**: Ch02

## `Expr.isApp` / `Expr.isConst` / `Expr.isForall`
%%%
tag := "appendix-api-expr-isapp"
%%%

- **签名**: `Expr → Bool`（纯函数）
- **用途**: 判断表达式是否为特定构造子
- **推荐掌握时机**: Ch02 后
- **出现章节**: Ch02

## Expr constName / constName?
%%%
tag := "appendix-api-expr-constname"
%%%

- **签名**: `Expr → Name` / `Expr → Option Name`（纯函数）
- **用途**: 提取 `const` 构造子中的名字
- **注意**: `constName` 在非 const 时会 panic；安全版用 `constName?`
- **推荐掌握时机**: Ch02 后
- **出现章节**: Ch02

# A.8 Name / Level / Syntax 操作
%%%
tag := "appendix-api-name-level-syntax"
%%%

## Name
%%%
tag := "appendix-api-name"
%%%

```
-- 构造（推荐：反引号语法）
`Nat.add                          -- 单反引号：当前命名空间解析
``Nat.add                         -- 双反引号：完全限定名（推荐日常使用）

-- 编程方式构造（仅在需要动态拼接名字时使用）
Name.mkStr2 "Lean" "Meta"        -- 等价于 `Lean.Meta，但用于运行时构造
Name.anonymous                    -- 空名字

-- 操作
Name.append : Name → Name → Name  -- 连接两个名字
Name.str : Name → String → Name   -- 追加字符串组件
Name.num : Name → Nat → Name      -- 追加数字组件（如 `_uniq.123`）
Name.isPrefixOf : Name → Name → Bool  -- 前缀检查
```

**注意**: 在元程序中引用已有声明**首选双反引号**（如 `Nat.add`），它在编译时检查名字是否存在。`Name.mkStr2` 等编程构造方式只在需要运行时动态拼接名字时使用（如根据用户输入生成名字）。

## Level
%%%
tag := "appendix-api-level"
%%%

```
-- 构造
Level.zero                        -- universe 0
Level.succ : Level → Level        -- u + 1
Level.max : Level → Level → Level -- max u v
Level.param : Name → Level        -- 参数 level（如 `u`）

-- 常用
levelOne := Level.succ Level.zero  -- universe 1
```

## Syntax 与引号
%%%
tag := "appendix-api-syntax"
%%%

```
-- Tactic 语法引号
`(tactic| simp [h1, h2])          -- 构造 tactic 语法
`(tactic| ring)                    -- 简单 tactic

-- Term 语法引号
`(Nat.add 2 3)                    -- 构造 term 语法
`($e + $f)                        -- 带反引号插值

-- 标识符
mkIdent : Name → Syntax           -- 从 Name 创建标识符语法
```

# A.9 Tactic 声明方式
%%%
tag := "appendix-api-tactic-decl"
%%%

## `elab` / `elab\_rules`
%%%
tag := "appendix-api-elab"
%%%

- **用途**: 声明带完整语义实现的 tactic
- **示例**: `elab "my_tactic" : tactic => do let goal ← getMainGoal; ...`
- **推荐掌握时机**: Ch01 后
- **出现章节**: Ch01, Ch03, Ch04, Ch05, Ch07, Ch08, Ch14, Ch19

## `macro`
%%%
tag := "appendix-api-macro"
%%%

- **用途**: 声明纯语法展开的 tactic（不进入 `TacticM`）
- **示例**: `` macro "my_rfl" : tactic => `(tactic| rfl) ``
- **注意**: 适合简单 tactic 组合；复杂逻辑需用 `elab`
- **推荐掌握时机**: Ch01 后
- **出现章节**: Ch01, Ch08

# A.10 常用属性（Attribute）
%%%
tag := "appendix-api-attributes"
%%%

属性（attribute）用于将声明注册到特定 tactic 的规则库中。

**注意**：虽然下面的属性写法看起来相似（都是 `@[xxx]`），但它们背后的注册机制并不相同。例如 `@[simp]` 将引理加入 `simp` 的 discrimination tree 索引，`@[aesop]` 将规则加入 `aesop` 的搜索树，而 `@[instance]` 是将声明注册到 type class 系统。它们只是共享了 `@[...]` 这一语法外壳，底层的存储和查询方式各不相同。

| 属性 | 用途 | 出现章节 |
|------|------|----------|
| `@[simp]` | 注册为 `simp` 化简规则 | Ch06 |
| `@[aesop]` | 注册为 `aesop` 搜索规则（支持 `safe`/`unsafe`/`norm`） | Ch11, Ch19 |
| `@[norm_num]` | 注册为 `norm_num` 计算插件 | Ch10 |
| `@[positivity]` | 注册为 `positivity` 传播规则 | Ch14, Ch19 |
| `@[grind]` | 注册为 `grind` E-matching 触发规则 | Ch12 |
| `@[field_simp]` | 注册为 `field_simp` 分母消除规则 | Ch17 |
| `@[gcongr]` | 注册为 `gcongr` 不等式 congruence 规则 | Ch16 |
| `@[fun_prop]` | 注册为 `fun_prop` 函数性质传播规则 | Ch15 |
| `@[ext]` | 注册为扩展性引理 | — |
| `@[instance]` | 注册为 type class 实例 | Ch05 |

# A.11 Monad 层级提升
%%%
tag := "appendix-api-monad-lifting"
%%%

```
CoreM ← MetaM ← TermElabM ← TacticM
```

每一层自动 lift（提升，即自动继承下层能力）下层 API。例如在 `TacticM` 中可直接调用 `inferType`（MetaM 层）。需要将 `MVarId → MetaM (List MVarId)` 提升到 `TacticM` 时用 `liftMetaTactic`。

# A.12 Expr 构造子速览
%%%
tag := "appendix-api-expr-overview"
%%%

| 构造子 | 含义 | 日常使用频率 | 配对 API |
|--------|------|------------|----------|
| `Expr.app fn arg` | 函数应用（多参数 = 嵌套 app） | ★★★★★ | 构造: `mkApp`; 分析: `getAppFn`/`getAppArgs` |
| `Expr.const name levels` | 常量引用（定义/定理） | ★★★★★ | 构造: `mkConst`; 提取: `constName?` |
| `Expr.fvar fvarId` | 自由变量（局部上下文中的变量） | ★★★★★ | 通过 `getLCtx` 查询 |
| `Expr.mvar mvarId` | 元变量（未解决的目标/hole） | ★★★★☆ | 构造: `mkFreshExprMVar`; 赋值: `MVarId.assign` |
| `Expr.lam name type body bi` | λ 表达式 | ★★★★☆ | 构造: `mkLambda`; 展开: `lambdaTelescope` |
| `Expr.forallE name type body bi` | ∀/→ 类型 | ★★★★☆ | 构造: `mkForall`; 展开: `forallTelescope` |
| `Expr.letE name type value body nonDep` | let 绑定 | ★★★☆☆ | — |
| `Expr.lit literal` | 字面量（自然数/字符串） | ★★★☆☆ | 构造: `mkNatLit` |
| `Expr.sort level` | Sort（Type u / Prop） | ★★☆☆☆ | — |
| `Expr.bvar index` | 绑定变量（de Bruijn 索引） | ★★☆☆☆ | 通过 telescope 系列避免直接操作 |
| `Expr.mdata data expr` | 元数据注解 | ★☆☆☆☆ | — |
| `Expr.proj typeName idx struct` | 结构体投影 | ★☆☆☆☆ | — |

**关键类型**：

- `MVarId`：元变量标识（每个未解决目标对应一个）
- `FVarId`：自由变量标识（局部上下文中的变量）
- `LocalContext`：局部声明集合（通过 `getLCtx` 获取）
- `LocalDecl`：单个局部声明（`.userName`、`.type`、`.toExpr` 字段）
- `Environment`：全局环境（所有定义/定理/公理）

# A.13 速查：按任务查 API
%%%
tag := "appendix-api-task-lookup"
%%%

## "我想检查目标的结构"
%%%
tag := "appendix-api-task-inspect-goal"
%%%

```
let goal ← getMainGoal
let target ← goal.getType       -- 或 getMainTarget
let target ← whnf target        -- 规约定义包裹
match_expr target with
| Eq α lhs rhs => ...           -- 等式
| And p q      => ...           -- 合取
| _            => throwError "unsupported shape"
```

## "我想在假设中搜索"
%%%
tag := "appendix-api-task-search-hyps"
%%%

```
withMainContext do
  let target ← getMainTarget
  let lctx ← getLCtx
  for decl in lctx do
    if decl.isImplementationDetail then continue
    if ← isDefEq decl.type target then
      (← getMainGoal).assign decl.toExpr
      return
  throwError "no matching hypothesis"
```

## "我想拆分目标为子目标"
%%%
tag := "appendix-api-task-split-goal"
%%%

```
let goal ← getMainGoal
let sub1 ← mkFreshExprMVar (some typeA)
let sub2 ← mkFreshExprMVar (some typeB)
let proof := mkApp2 (mkConst ``And.intro) sub1 sub2
goal.assign proof
replaceMainGoal [sub1.mvarId!, sub2.mvarId!]
```

## "我想调用别的 tactic"
%%%
tag := "appendix-api-task-call-tactic"
%%%

```
evalTactic (← `(tactic| simp [Nat.add_comm]))
-- 或组合多个 tactic
evalTactic (← `(tactic| constructor <;> assumption))
```

## "我想构造证明项"
%%%
tag := "appendix-api-task-build-proof"
%%%

```
-- 方式 1：mkAppM（自动处理隐式参数和 universe，推荐首选）
let proof ← mkAppM ``Eq.refl #[a]

-- 方式 2：手动 mkApp（更底层，需自己处理隐式参数）
let proof := mkApp2 (mkConst ``Eq.refl [levelOne]) ty a
-- ↑ 注意：需要手动提供 universe level 和类型参数

-- 方式 3：从语法精化（最方便但有 elaboration 开销）
let proof ← elabTerm (← `(Eq.refl $stx)) (some expectedType)
```

## "我想处理绑定结构（∀ / λ）"
%%%
tag := "appendix-api-task-binders"
%%%

```
-- 展开 ∀，操作 body，再重建
forallTelescope goalType fun fvars body => do
  -- fvars: 量化变量（fvar），body: bvar 已替换
  let newBody := ...
  mkForallFVars fvars newBody     -- 重建 ∀

-- 展开 λ，类似
lambdaTelescope expr fun fvars body => do
  let result := ...
  mkLambdaFVars fvars result      -- 重建 λ
```

## "我想查找 type class 实例"
%%%
tag := "appendix-api-task-typeclass"
%%%

```
-- 推荐：先用 synthInstance?，优雅处理搜索失败
match ← synthInstance? (← mkAppM ``Inhabited #[α]) with
| some inst => ...
| none      => throwError "no Inhabited instance"

-- 确信存在时
let inst ← synthInstance instType
```

## "我想探测而不留副作用"
%%%
tag := "appendix-api-task-probe"
%%%

```
-- isDefEq 有副作用（赋值元变量），用 withoutModifyingState 隔离
let matches ← withoutModifyingState do
  isDefEq a b
```

## "我想用回溯尝试多种策略"
%%%
tag := "appendix-api-task-backtrack"
%%%

```
let saved ← saveState
try
  firstStrategy
catch _ =>
  restoreState saved
  secondStrategy
```

# A.14 章节-API 交叉索引
%%%
tag := "appendix-api-chapter-index"
%%%

| 章节 | 核心 API |
|------|----------|
| Ch01 | `CoreM`, `MetaM`, `TacticM`, `elab`, `inferType`, `isDefEq`, `getMainGoal`, `mkFreshExprMVar`, `forallTelescope`, `mkEqRefl` |
| Ch02 | `Expr` 构造子, `match_expr`, `let_expr`, `whnf`, `isProof`, `isProp`, `getAppFn`, `getAppArgs`, `kabstract`, `mkApp*` |
| Ch03 | `getMainGoal`, `goal.assign`, `goal.getType`, `getLCtx`, `isDefEq`, `evalTactic`, `throwTacticEx`, `withContext` |
| Ch04 | `getGoals`, `setGoals`, `replaceMainGoal`, `focus`, `saveState`, `restoreState`, `getUnsolvedGoals`, `logInfo` |
| Ch05 | `mkAppM`, `synthInstance`, `synthInstance?`, `isInstance`, `withOptions`, `withNewLocalInstance` |
| Ch06 | `simp`, `isDefEq`, `DiscrTree.getMatch` |
| Ch07 | `ring`, `evalTactic`, `logInfo`, `mkConst` |
| Ch08 | `omega`, `evalTactic`, `macro`, `decide` |
| Ch09 | `linarith`, `nlinarith`, `polyrith` |
| Ch10 | `norm_num`, `decide`, `native_decide` |
| Ch11 | `aesop`, `@[aesop]` |
| Ch12 | `grind`, `@[grind]` |
| Ch13 | `decide`, `native_decide`, `Decidable` |
| Ch14 | `positivity`, `mkAppM`, `@[positivity]` |
| Ch15 | `fun_prop`, `@[fun_prop]` |
| Ch16 | `gcongr`, `@[gcongr]` |
| Ch17 | `field_simp`, `ring` |
| Ch18 | `intro`, `cases`, `constructor` |
| Ch19 | `MetaM`, `TacticM`, `closeMainGoal`, `instantiateMVars`, `isDefEq`, `mkAppM`, `DiscrTree`, `match_expr` |

# A.15 进阶 API 🔧
%%%
tag := "appendix-api-advanced"
%%%

> **提示**：以下 API 面向需要直接操作 Lean 内核环境或 discrimination tree 的高级场景。普通 tactic 开发通常不需要这些 API，建议在掌握 A.1–A.9 后再按需学习。

## `setEnv` 🔧
%%%
tag := "appendix-api-setenv"
%%%

- **签名**: `Environment → CoreM Unit`
- **用途**: 直接替换当前全局环境
- **注意**: ⚠️ **普通 tactic 开发不需要此 API**。直接操作环境可能破坏一致性（如引入循环依赖或类型不正确的声明）。绝大多数场景应通过 `addAndCompile` 或 `addDecl` 等高层接口操作环境
- **推荐掌握时机**: 仅在开发 Lean 编译器插件或环境操作工具时

## `addAndCompile` 🔧
%%%
tag := "appendix-api-addandcompile"
%%%

- **签名**: `Declaration → CoreM Unit`
- **用途**: 向环境添加声明并编译（生成字节码）
- **注意**: ⚠️ **普通 tactic 开发不需要此 API**。添加前要确保名字未被占用，且声明通过类型检查。仅在需要在运行时动态创建新定义时使用（如代码生成工具）
- **推荐掌握时机**: 仅在开发 Lean 编译器插件或 metaprogram 生成工具时

## `DiscrTree.getMatch` 🔧
%%%
tag := "appendix-api-discrtree-getmatch"
%%%

- **签名**: `DiscrTree α → Expr → MetaM (Array α)`
- **用途**: 用 discrimination tree（判别树，一种按表达式结构快速索引和查找的数据结构）快速按表达式结构查找匹配规则
- **注意**: 这是 `simp`、`aesop` 等 tactic 的内部索引机制。理解它有助于理解这些 tactic 的工作原理，但直接使用它需要对索引结构有深入了解。入门阶段建议通过 `@[simp]`、`@[aesop]` 等属性间接使用 discrimination tree，而不是直接操作
- **推荐掌握时机**: Ch19 后，仅在需要开发自定义规则索引时
- **出现章节**: Ch05, Ch06, Ch19
