import VersoManual
import LeanTacticBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "examples"
set_option verso.exampleModule "Examples.AppendixApiReference"

set_option maxRecDepth 100000

#doc (Manual) "附录 A：Metaprogramming API 目录" =>
%%%
file := "AppendixApiReference"
tag := "appendix-api-reference"
%%%

本附录是面向 Lean `v4.32.2` 的可审计 API 目录。它在保留旧版全部 API 主题的基础上，在文档编译时读取当前 `Environment`，按声明实际所属模块生成表格。因此，工具链升级造成的新增、删除或签名变化会直接反映在构建结果中。

收录规则如下：

- 枚举所列来源模块或模块前缀中的全部环境常量；
- 排除 private 名称以及 Lean 生成的 internal / numeric 名称；
- 按 `Name.quickCmp` 排序，保证同一工具链下输出稳定；
- 展示声明种类、完整类型、unsafe / partial 状态、实际来源模块和官方 docstring 首段；
- “随 Lean 版本演进”表示元编程 API 受工具链版本约束，并不表示该声明已弃用。

“穷尽”在这里有三个不同口径：常量表穷尽其标题所列的来源模块或模块前缀；旧版 72 个常量型 API 由审计脚本逐名回归；`elab`、quotation、`match_expr` 和属性等非 `ConstantInfo` 机制则由专节列出并说明边界。目录以*能力*组织，而不是按正文位置组织。

# A.1 Monad 层级与最小工作流
%%%
tag := "appendix-api-monad-stack"
%%%

四个主要 monad 逐层增加上下文和状态：

:::codeBox "pseudocode"
```
CoreM
  └─ MetaM
       └─ TermElabM
            └─ TacticM
```
:::

其权威定义可概括为：

:::codeBox "code"
```
CoreM     := ReaderT Core.Context (StateRefT Core.State (EIO Exception))
MetaM     := ReaderT Meta.Context (StateRefT Meta.State CoreM)
TermElabM := ReaderT Term.Context (StateRefT Term.State MetaM)
TacticM   := ReaderT Tactic.Context (StateRefT Tactic.State TermElabM)
```
:::

上层通常可以通过 monad lifting 使用下层能力；反方向则需要显式构造并运行所缺的上下文与状态。

## Monad 提升、状态探测与回溯
%%%
tag := "appendix-api-monad-lifting"
%%%

`TacticM` 可直接使用 `TermElabM`、`MetaM` 和 `CoreM` 的能力；`TermElabM` 可直接使用 `MetaM` 和 `CoreM` 的能力。把会产生新目标的 `MVarId → MetaM (List MVarId)` 提升到 tactic 层时使用 `liftMetaTactic`。只想探测而不保留元变量赋值时用 `withoutModifyingState`；需要在多个完整策略间回退时使用 `saveState` / `restoreState`。

:::codeBox "code"
```
let matched ← withoutModifyingState do
  isDefEq candidateType target

let saved ← saveState
try
  firstStrategy
catch _ =>
  restoreState saved
  secondStrategy
```
:::

## 读取并检查当前目标
%%%
tag := "appendix-api-minimal-tactic"
%%%

```anchor appendix_inspect_goal
elab "inspect_goal" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  let target ← whnf target
  logInfo m!"goal: {target}"
```

## 构造表达式并核对类型
%%%
tag := "appendix-api-minimal-meta"
%%%

```anchor appendix_inspect_expr
def inspectExpr (expr : Expr) : MetaM Unit := do
  let type ← inferType expr
  let type ← instantiateMVars type
  logInfo m!"type: {type}"
```

## 修改目标列表
%%%
tag := "appendix-api-minimal-goals"
%%%

```anchor appendix_close_or_keep
elab "close_or_keep" : tactic => do
  let goal ← getMainGoal
  if ← goal.isAssigned then
    replaceMainGoal []
  else
    replaceMainGoal [goal]
```

# A.2 名称、宇宙、表达式与句法
%%%
tag := "appendix-api-representations"
%%%

这一组回答“Lean 内部怎样表示程序”。`Name` 标识声明和局部对象，`Level` 表示宇宙层级，`Expr` 是核心项语言，`Syntax` 则保留解析阶段的语法结构与源码信息。

:::apiCatalog "名称操作" "Lean.Data.Name" "Name" "纯数据；部分查询读取名称结构"
:::

:::apiCatalog "宇宙层级" "Lean.Level" "Level" "纯数据；部分操作维护层级结构"
:::

:::apiCatalog "核心表达式" "Lean.Expr" "Expr" "纯构造与分析；unsafe 项另行标记"
:::

:::apiCatalog "语法树" "Lean.Syntax" "Syntax" "语法数据；宏作用域和源码位置相关"
:::

:::apiCatalog "基础元编程定义" "Init.Meta.Defs" "Name / Syntax / Meta 基础" "纯构造、标识符与基础元编程状态"
:::

## Expr 构造子速览
%%%
tag := "appendix-api-expr-overview"
%%%

:::table +header
* - 构造子
  - 含义
  - 常用构造 / 分析 API
* - `Expr.app fn arg`
  - 函数应用
  - `mkApp*`、`getAppFn`、`getAppArgs`
* - `Expr.const name levels`
  - 全局常量
  - `mkConst`、`constName?`
* - `Expr.fvar fvarId`
  - 局部上下文中的自由变量
  - `getLCtx`、`FVarId.getType`
* - `Expr.mvar mvarId`
  - 元变量或未解决目标
  - `mkFreshExprMVar`、`MVarId.assign`
* - `Expr.lam name type body bi`
  - lambda 表达式
  - `mkLambda`、`lambdaTelescope`、`mkLambdaFVars`
* - `Expr.forallE name type body bi`
  - forall 或函数类型
  - `mkForall`、`forallTelescope`、`mkForallFVars`
* - `Expr.letE name type value body nonDep`
  - let 绑定
  - `letTelescope`、`mkLetFVars`
* - `Expr.lit literal`
  - 字面量
  - `mkNatLit`、`lit?`
* - `Expr.sort level`
  - `Prop` / `Type u`
  - `mkSort`、`sortLevel?`
* - `Expr.bvar index`
  - de Bruijn 绑定变量
  - 优先用 telescope API 操作
* - `Expr.mdata data expr`
  - 元数据注解
  - `mdata!`、`consumeMData`
* - `Expr.proj typeName idx struct`
  - 结构体投影
  - `proj?`、投影归约 API
:::

## Expr 匹配、quotation 与反 quotation
%%%
tag := "appendix-api-expr-syntax-quotation"
%%%

`match_expr` / `let_expr` 用声明名匹配核心表达式；term、tactic 和 command quotation 构造有类别的 `Syntax`；`$x`、`$xs,*` 等 antiquotation 将已有语法插入模板。这些是 elaborator 语法，不是环境常量，因此不会出现在生成表中。

:::codeBox "code"
```
match_expr target with
| Eq α lhs rhs => ...
| And p q => ...
| _ => throwError "unsupported target"

let tacticSyntax ← `(tactic| simp [$(mkIdent lemmaName)])
let termSyntax ← `(Eq.refl $term)
```
:::

# A.3 环境、局部状态与诊断
%%%
tag := "appendix-api-state-diagnostics"
%%%

`Environment` 保存已加载声明及扩展状态；`LocalContext` 与 `MetavarContext` 分别保存自由变量和元变量信息；消息、异常与日志模块负责把失败和诊断信息送到调用者。

:::apiCatalog "环境与声明" "Lean.Environment" "Environment / CoreM" "读取环境；更新操作返回或安装新环境"
:::

:::apiCatalog "局部上下文" "Lean.LocalContext" "LocalContext / MetaM" "读取或构造局部声明上下文"
:::

:::apiCatalog "元变量上下文" "Lean.MetavarContext" "MetavarContext / MetaM" "读取、分配或更新元变量状态"
:::

:::apiCatalog "消息" "Lean.Message" "Message / CoreM" "构造和格式化诊断消息"
:::

:::apiCatalog "异常" "Lean.Exception" "Exception / CoreM" "构造、传播或呈现异常"
:::

:::apiCatalog "日志" "Lean.Log" "CoreM" "写入消息日志或记录诊断信息"
:::

:::apiCatalog "选项" "Lean.Data.Options" "Options / CoreM" "读取、覆盖或局部修改 pretty-printer 与 elaborator 选项"
:::

:::apiCatalog "环境 monad 接口" "Lean.MonadEnv" "MonadEnv / CoreM" "读取或替换环境；直接更新会影响后续 elaboration"
:::

:::apiCatalog "回溯状态" "Lean.Util.MonadBacktrack" "MonadBacktrack" "保存、恢复或隔离可回溯状态"
:::

:::apiCatalog "声明安装" "Lean.AddDecl" "CoreM" "校验、安装和编译环境声明；高风险环境修改"
:::

# A.4 CoreM 基础能力
%%%
tag := "appendix-api-corem"
%%%

`CoreM` 提供环境、选项、消息、文件位置和核心状态。它不提供类型推断、统一化或目标管理。

:::apiCatalog "CoreM 与基础服务" "Lean.CoreM" "CoreM" "读取环境/选项并更新 Core 状态；可记录消息"
:::

# A.5 MetaM 与证明状态
%%%
tag := "appendix-api-metam"
%%%

`MetaM` 在 `CoreM` 之上增加局部上下文、元变量上下文、透明度与类型类配置。类型推断、definitional equality、规约、统一化和元变量赋值都位于这一层。

:::table +header
* - 能力
  - 代表性来源模块
  - 典型入口
* - 基础上下文与元变量
  - `Lean.Meta.Basic`
  - `withLocalDecl`、`mkFreshExprMVar`
* - 规约与定义等价
  - `Lean.Meta.Reduce`、`Lean.Meta.WHNF`
  - `reduce`、`whnf`、`isDefEq`
* - 类型推断与检查
  - `Lean.Meta.InferType`、`Lean.Meta.Check`
  - `inferType`、`isProp`、`isProof`
* - 类型类搜索
  - `Lean.Meta.SynthInstance`、`Lean.Meta.Instances`
  - `synthInstance?`、`isInstance`
* - 表达式与应用构造
  - `Lean.Meta.AppBuilder`、`Lean.Meta.Constructions`
  - `mkAppM`、`mkEqRefl`
* - 目标变换
  - `Lean.Meta.Tactic.*`
  - `MVarId.intro`、`MVarId.apply`
* - 索引与匹配
  - `Lean.Meta.DiscrTree.*`
  - `DiscrTree.getMatch`
:::

下面的折叠表不是精选列表，而是 `Lean.Meta` 整个来源模块族中满足可见性规则的全部环境声明。

:::apiCatalog "Lean.Meta 完整模块族" "Lean.Meta" "MetaM / MVarId / 元编程基础设施" "可能读取或更新元变量、局部上下文、缓存与证明状态"
:::

# A.6 TermElabM
%%%
tag := "appendix-api-termelabm"
%%%

`TermElabM` 负责把 `Syntax` elaboration 为 `Expr`。它在 `MetaM` 能力上增加期望类型、待处理 synthetic metavariable、命令作用域和 elaborator 状态。

:::apiCatalog "项 elaboration 模块族" "Lean.Elab.Term" "TermElabM" "读取并更新项 elaborator 状态；可创建与推迟约束"
:::

# A.7 TacticM
%%%
tag := "appendix-api-tacticm"
%%%

`TacticM` 管理有序目标列表并提供 tactic 语法求值入口。多数自定义 tactic 从 `getMainGoal` 取得 `MVarId`，调用 `MetaM` API 处理它，再用 `replaceMainGoal` 写回剩余目标。

:::apiCatalog "Tactic elaboration 模块族" "Lean.Elab.Tactic" "TacticM / MetaM" "读取并替换目标列表；执行 tactic elaborator 与内建 tactic"
:::

# A.8 Tactic 声明、宏与属性
%%%
tag := "appendix-api-declarations-attributes"
%%%

## `syntax`、`macro`、`elab` 与规则族
%%%
tag := "appendix-api-tactic-declarations"
%%%

- `syntax` 只声明解析形式；`macro` / `macro_rules` 把语法展开为语法。
- `elab` / `elab_rules` 注册真正的 elaborator，可进入 `TacticM` 实现语义。
- `@[tactic name]`、`@[term_elab name]`、`@[command_elab name]` 是较底层的 elaborator 注册入口。
- 简单组合优先用 macro；需要检查目标、类型或环境时使用 tactic elaborator。

```anchor appendix_tactic_declarations
syntax "my_assumption" : tactic

macro "my_rfl" : tactic => `(tactic| rfl)

elab_rules : tactic
  | `(tactic| my_assumption) => do
      evalTactic (← `(tactic| assumption))
```

## 常用属性
%%%
tag := "appendix-api-attributes"
%%%

属性是环境扩展的注册入口，不是普通函数 API。下表完整保留旧版讨论的属性族；某个属性是否可用取决于导入的 Lean / Mathlib 模块。

:::table +header
* - 属性
  - 注册用途
  - 典型消费者
* - `@[simp]`
  - 化简引理
  - `simp`
* - `@[aesop]`
  - 安全、不安全或规范化搜索规则
  - `aesop`
* - `@[norm_num]`
  - 数值规范化插件
  - `norm_num`
* - `@[positivity]`
  - 正性传播规则
  - `positivity`
* - `@[grind]`
  - E-matching / 推理规则
  - `grind`
* - `@[field_simp]`
  - 分母消去规则
  - `field_simp`
* - `@[gcongr]`
  - 广义合同与单调性规则
  - `gcongr`
* - `@[fun_prop]`
  - 函数性质传播规则
  - `fun_prop`
* - `@[ext]`
  - extensionality 引理
  - `ext`
* - `@[instance]`
  - 类型类实例
  - 类型类合成
:::

# A.9 按任务反查与工作流
%%%
tag := "appendix-api-by-task"
%%%

:::table +header
* - 任务
  - 起点
  - 继续查阅
* - 取得当前目标
  - `getMainGoal`
  - TacticM 与目标管理
* - 读取目标类型
  - `MVarId.getType`
  - MetaM 基础能力
* - 推断表达式类型
  - `inferType`
  - MetaM 基础能力
* - 比较 definitional equality
  - `isDefEq`
  - MetaM 基础能力
* - 规约表达式
  - `whnf`、`reduce`
  - MetaM 基础能力、规约
* - 创建或赋值元变量
  - `mkFreshExprMVar`、`MVarId.assign`
  - MetaM 基础能力、元变量上下文
* - 管理局部变量
  - `withLocalDecl`、`withLocalDeclD`
  - MetaM 基础能力、局部上下文
* - 遍历并检查局部假设
  - `getLCtx`、`LocalDecl.type`、`isDefEq`
  - 局部上下文、MetaM 基础能力
* - 拆分目标并安装子目标
  - `MVarId.intro`、`MVarId.apply`、`replaceMainGoal`
  - 目标引入、Tactic elaboration 模块族
* - elaboration 一段项语法
  - `elabTerm`、`elabTermEnsuringType`
  - 项 elaboration
* - 改写剩余目标
  - `replaceMainGoal`
  - TacticM 与目标管理
* - 读取声明信息
  - `getConstInfo`、`Environment.find?`
  - 环境与声明、MetaM 基础能力
* - 输出诊断
  - `logInfo`、`logWarning`、`throwError`
  - CoreM 与基础服务、消息、异常、日志
* - 构造证明项并补全隐式参数
  - `mkAppM`、`mkEqRefl`
  - 应用与证明项构造
* - 搜索类型类实例
  - `synthInstance?`、`synthInstance`
  - 类型类合成
* - 探测定义等价而不留副作用
  - `withoutModifyingState`、`isDefEq`
  - 回溯状态、MetaM 基础能力
* - 在多个策略间回退
  - `saveState`、`restoreState`
  - 回溯状态
* - 调用已有 tactic
  - `evalTactic`
  - Tactic elaboration 模块族
* - 动态添加声明
  - `addAndCompile`、`setEnv`
  - 声明安装、环境 monad 接口
* - 建立表达式索引
  - `DiscrTree.getMatch`
  - 判别树
:::

# A.10 审计口径与限制
%%%
tag := "appendix-api-audit"
%%%

## 旧版主题迁移矩阵
%%%
tag := "appendix-api-legacy-topic-migration"
%%%

:::table +header
* - 旧版主题
  - 新版落点
  - 覆盖检查
* - A.1 CoreM
  - A.3、A.4
  - 来源模块穷尽；旧常量逐名回归
* - A.2 MetaM
  - A.3、A.5
  - `Lean.Meta` 完整模块族穷尽；旧常量逐名回归
* - A.3 TermElabM
  - A.6
  - `Lean.Elab.Term` 模块族穷尽；旧常量逐名回归
* - A.4 TacticM
  - A.7
  - `Lean.Elab.Tactic` 模块族穷尽；旧常量逐名回归
* - A.5 错误处理与日志
  - A.3、A.4、A.5
  - Message / Exception / Log 模块穷尽；旧常量逐名回归
* - A.6 Expr 构造函数
  - A.2、A.5
  - Expr / AppBuilder 模块穷尽；旧常量逐名回归
* - A.7 Expr 匹配与分析
  - A.2
  - Expr 模块穷尽；`match_expr` 语法单列
* - A.8 Name / Level / Syntax
  - A.2
  - 各来源模块穷尽；quotation 单列
* - A.9 Tactic 声明方式
  - A.8
  - 非 `ConstantInfo` 语法族逐项保留
* - A.10 常用属性
  - A.8
  - 旧版属性族逐项保留
* - A.11 Monad 层级提升
  - A.1、A.3
  - 回溯 / MonadEnv 模块穷尽；工作流保留
* - A.12 Expr 构造子速览
  - A.2
  - 十二种 `Expr` 构造子全部列出
* - A.13 按任务查 API
  - A.9
  - 九类旧任务全部保留并扩充
* - A.14 章节-API 交叉索引
  - 不迁移
  - 旧章节编号已失效；它是导航数据，不是 API 主题
* - A.15 进阶 API
  - A.3、A.5、A.9
  - 三个旧常量逐名回归，所属模块穷尽
:::

这里的“模块穷尽”是可机械验证的：每个折叠框都对应一个明确的来源模块前缀。它不表示 Lean 为“遍历假设”或“构造证明项”等语义任务提供了一个封闭、官方标注的 API 集合；Lean 环境没有这种能力分类元数据。

每个折叠框都对应一个明确的来源模块前缀。生成器从 `env.constants.toList` 取得导入与当前模块的完整声明集合，以 `Environment.getModuleIdxFor?` 和 `Environment.allImportedModuleNames` 确认实际来源；它不根据命名空间猜测模块。表中计数就是应用可见性过滤后的声明数。

工具链升级后，可先运行 `lake env lean scripts/audit-api-catalog.lean`。审计脚本与文档生成器共用收集逻辑，会输出每组数量，并在分组为空、声明重复或旧版 72 个常量型 API 有任一遗漏时失败。

本目录的“完整”是指：所列模块范围内、在当前编译环境中可见且名称非 private / internal 的全部常量声明。它不等同于 `Lean.Meta.*` 或 `Lean.Elab.*` 整个源码目录的符号转储，也不承诺这些接口跨 Lean 版本保持不变。没有官方 docstring 的条目明确显示“无源码说明”，不根据名称臆测用途。

签名使用开启 universe、explicit argument 和 full name 的 pretty-printer 生成。遇到含局部变量的表达式时，实际调用仍必须位于与该表达式匹配的 `LocalContext` 和 `MetavarContext` 中。
