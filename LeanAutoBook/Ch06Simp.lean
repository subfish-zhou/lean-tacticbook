import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch06Simp"

#doc (Manual) "simp——化简的瑞士军刀" =>
%%%
file := "Ch06Simp"
tag := "ch06-simp"
%%%

**本章目标**：前半章掌握 `simp` 的用法、配置与调试；后半章从 Lean 4 真实源码层面拆解 simp 的完整实现——入口分发、核心类型、重写循环、引理匹配、congruence、discharger——面向想深入理解内部机制的读者。

# 用法详解
%%%
tag := "simp-usage"
%%%

## 核心思想
%%%
tag := "simp-core-idea"
%%%

`simp` 是一个**项重写系统（term rewriting system）**，工作流程概括为四步：

```
loop:
  1. 在目标（或假设）中找到一个子项 t
  2. 在规则集中找到一条引理  lhs = rhs  使得 t 匹配 lhs
  3. 把 t 替换为 rhs
  4. 如果目标发生了变化，回到 1；否则停止
```

停止的条件有两个：**收敛**（没有规则能继续应用）或**超时**（超过 `maxSteps` 限制）。

## 重写规则集：simp lemmas
%%%
tag := "simp-lemmas"
%%%

任何被标记了 `@[simp]` 的定理都会被加入全局 simp 规则集。

**四种引理形式**——等式引理、条件等式、命题引理、iff 引理：

```
-- [可运行]
@[simp] theorem Nat.add_zero (n : Nat) : n + 0 = n := by omega

-- 条件等式：simp 必须先证明前提 h : p
-- @[simp] theorem if_pos (h : p) : (if p then a else b) = a

-- 命题引理：simp 遇到 n < n 时化为 False
-- @[simp] theorem Nat.lt_irrefl (n : Nat) : ¬(n < n)

-- iff 引理
-- @[simp] theorem not_and : ¬(p ∧ q) ↔ (p → ¬q)
```

## 方向性：只从左到右
%%%
tag := "directionality-lhs-to-rhs"
%%%

simp 只会把引理的 **LHS 重写为 RHS**，永远不会反过来。编写原则：

- **LHS 比 RHS 复杂**：化简应让表达式变"简单"
- **RHS 不引入新变量**：RHS 的自由变量必须都出现在 LHS 中
- **不能左右对称**：`a + b = b + a` 会导致无限循环

反方向使用：`simp [← h]`。

## simp 家族一览
%%%
tag := "simp-family"
%%%

- `simp`：通用重写化简，加载全局 `@[simp]` 集 + 用户传入引理
- `simp only [...]`：精确控制重写集，不加载全局集，只用方括号内指定的引理
- `simp?` / `simp_all?`：查找实际用到的引理，输出 `Try this: simp only [...]`，用于替换为精确版本
- `simp_all`：化简目标**和**所有假设，假设间可互相化简，多轮迭代到不动点
- `dsimp`：只做 definitional equality 化简，只用 `rfl` 引理 + beta/iota/zeta 规约，不生成 proof 项
- `simpa`：`simp` + `assumption`，化简后自动尝试用假设关闭目标
- `simp_rw`：精确控制重写位置，逐条应用引理，每条按 `rw` 语义（不化简子项）
- `field_simp`：消分母，Mathlib 提供，先消分母再化简

## 何时该用 `simp only`
%%%
tag := "when-simp-only"
%%%

在证明脚本中，**首选 `simp only`**。原因：

1. **可复现性**——`simp only` 不受全局 `@[simp]` 集变化的影响。新增一条 `@[simp]` 引理可能让远处的 `simp` 调用行为突变甚至失败。
2. **性能**——全局 simp 集可能有数千条引理（Mathlib 下尤其如此），`simp only` 大幅缩小 DiscrTree 搜索空间。
3. **可读性**——读者可以一眼看出化简依赖了哪些引理。

**推荐工作流**：先写 `simp?`，复制输出的 `simp only [...]` 替换原来的 `simp`。

```
-- [可运行]
-- 第一步：写 simp?
-- example (n : Nat) : n + 0 = n := by simp?
-- 第二步：替换为 simp? 的建议
example (n : Nat) : n + 0 = n := by simp only [Nat.add_zero]
```

**例外**——以下场景可以直接写 `simp`：

- 一次性脚本或 `decide` 能解决的简单目标
- 最终目标是 `True` / `rfl` 等显然命题
- 探索阶段——先用 `simp` 快速推进，稳定后再替换为 `simp only`

## 什么时候不要第一反应用 simp
%%%
tag := "when-not-to-simp"
%%%

`simp` 是通用工具，但不是万能的。以下情况应优先考虑其他 tactic：

- **只需应用一条等式** → `rw [h]`：精确、快速、可控
- **需要反方向重写** → `rw [← h]`：`simp [← h]` 会同时做其他化简，可能不是你想要的
- **线性算术** → `omega`：simp 的 arith 模块不如 omega 强大
- **多项式/环等式** → `ring`：simp 无法处理多项式范式化
- **需要逐步控制位置** → `conv` + `rw`：simp 递归遍历所有子项，无法精确定位
- **证明 `False` 或矛盾** → `contradiction` / `omega`：simp 不擅长矛盾推理

**经验法则**：如果你需要 simp 做的事情可以用一两个 `rw` 替代，就用 `rw`。`simp` 的价值在于**批量**化简和**深层**递归。

## 配置
%%%
tag := "simp-config"
%%%

在 tactic 中传入 `(config := { ... })`。常用字段：

- `maxSteps`（默认 100000）：最大重写步数
- `maxDischargeDepth`（默认 2）：条件证明的递归深度
- `contextual`（默认 false）：上下文化简（if 分支）
- `memoize`（默认 true）：缓存子项结果
- `zeta`（默认 true）：展开 let 绑定
- `beta` / `eta` / `iota`（默认 true）：对应规约
- `failIfUnchanged`（默认 true）：目标不变则报错

## 调试
%%%
tag := "debugging-simp"
%%%

```
-- [可运行]
set_option trace.Meta.Tactic.simp.rewrite true in
example : 0 + 1 = 1 := by simp

-- simp? 告诉你实际使用了哪些引理
example : 0 + 1 = 1 := by simp?
-- Try this: simp only [Nat.zero_add]
```

## 常见失败模式
%%%
tag := "ch06-common-failure-patterns"
%%%

1. **循环**（`a + b → b + a → ...`）：不要把交换律标 `@[simp]`。
2. **无进展**（`simp made no progress`）：自定义函数需要 `simp [myFun]` 展开。
3. **意外展开**：用 `simp only` 或关闭特定规约。
4. **太慢**：用 `simp only` 减小引理集。

## 更多 debug 场景
%%%
tag := "more-debug-scenarios"
%%%

**场景 1：simp 化简了一半就停了**

```
-- [可运行]
example (a b : Nat) (h : a = 0) : a + b = b := by
  simp  -- stuck: simp 不知道 h
  sorry
-- 修复：
-- simp [h]  或  simp_all
```

诊断：局部假设默认不在 simp 集中。需要 `simp [h]` 显式传入，或用 `simp_all`（自动添加所有假设）。

**场景 2：simp 超时或步数超限**

```
`simp` failed: maximum number of steps exceeded
```

诊断：通常因为引理集中有"几乎循环"的规则（每一步都在变化但不收敛），或目标表达式极大。

修复：

1. `set_option maxRecDepth 4096` 临时提高限制（不推荐长期使用）
2. 用 `simp only` 精确控制引理集
3. 先用 `rw` 手动化简到更小的目标，再 `simp`

**场景 3：`simp` 化简结果不是你想要的**

```
-- [可运行]
set_option trace.Meta.Tactic.simp.rewrite true in
example : (0 : Nat) + 1 + 2 = 3 := by
  simp
  -- trace 会显示每一步重写，帮你定位哪一步引入了意外变换
```

诊断：开启 `trace.Meta.Tactic.simp.rewrite` 查看完整重写链，找到导致问题的那一步。然后用 `simp only` 排除该引理，或者用 `simp [-problematic_lemma]` 移除它。

## 更多替代 tactic
%%%
tag := "more-alternatives"
%%%

`simp` 强大但不万能。以下场景应该优先考虑其他 tactic：

- **纯算术等式/不等式** → `omega`（更快、更完备）
- **多项式恒等式** → `ring`（判定过程，保证成功）
- **线性算术** → `linarith`（实数/有理数线性不等式）
- **目标是某个具体值** → `decide` 或 `native_decide`
- **需要搜索引理库** → `exact?` 或 `apply?`
- **simp 化简后还剩复杂目标** → 先手动拆解（`constructor` / `intro` / `cases`），再对子目标用 simp

记住：`simp` 不是万能胶水。它是重写引擎，不是搜索器（搜索器是 `aesop`），也不是判定过程（判定过程是 `ring` / `omega`）。

# 源码全景：文件结构与调用链
%%%
tag := "source-overview"
%%%

从这一节开始，我们进入 Lean 4 v4.30.0-rc1 的真实源码。下面所有代码片段都标注了文件路径和行号。

> **版本说明**：本章源码拆解基于 Lean 4 **v4.30.0-rc1**（与本书运行环境一致）。读者若使用不同版本，函数签名和行号可能有细微差异，但核心架构稳定——`simpLoop`、`rewrite?`、`Methods` 等骨架自 v4.4 以来基本未变。

> **Lean 核心 vs Mathlib**：本章拆解的是 **Lean 核心**的 simp 引擎实现（`Lean/Meta/Tactic/Simp/`）。Mathlib 不修改核心引擎骨架，而是贡献大量 `@[simp]` 引理、simproc 扩展（如 `norm_num` 作为 simproc）、以及 `field_simp` / `simp_rw` 等变体 tactic。读者在 Mathlib 环境下使用 simp 时，引擎不变，但可用的规则库大幅扩展。

## 源码文件一览
%%%
tag := "source-files"
%%%

- `Lean/Elab/Tactic/Simp.lean`（758 行）：tactic 入口、参数解析、`evalSimp`/`evalSimpAll`/`evalDSimp`
- `Lean/Meta/Tactic/Simp/Types.lean`（1000 行）：核心类型：`SimpM`、`Methods`、`Config`、`Result`、`Step`、`Simproc`
- `Lean/Meta/Tactic/Simp/Main.lean`（963 行）：主循环：`simpImpl`、`simpLoop`、`simpStep`、`simpApp`、`congr`
- `Lean/Meta/Tactic/Simp/Rewrite.lean`（659 行）：重写逻辑：`rewrite?`、`tryTheorem?`、`discharge?'`、`synthesizeArgs`
- `Lean/Meta/Tactic/Simp/SimpTheorems.lean`（725 行）：引理注册：`SimpTheorem`、`Origin`、`SimpTheorems`、`@[simp]` 属性
- `Lean/Meta/Tactic/Simp/SimpCongrTheorems.lean`（155 行）：congruence lemma：`SimpCongrTheorem`、`@[congr]` 属性

## 完整调用链
%%%
tag := "call-chain"
%%%

```
用户写 `simp [foo]`
  → Parser 生成 Syntax
    → evalSimp                          [Elab/Tactic/Simp.lean:L684]
      → mkSimpContext                   [Elab/Tactic/Simp.lean:L452]
        → elabSimpArgs                  [Elab/Tactic/Simp.lean:L309]
      → simpLocation                    [Elab/Tactic/Simp.lean:L658]
        → simpGoal                      [Meta/Tactic/Simp/Main.lean:L875]
          → simp (MetaM 层)             [Meta/Tactic/Simp/Main.lean:L772]
            → Simp.mainCore             [Meta/Tactic/Simp/Main.lean:L745]
              → simpImpl                [Meta/Tactic/Simp/Main.lean:L716]
                → simpLoop              [Meta/Tactic/Simp/Main.lean:L677]
                  → pre / simpStep / post
```

## tactic 入口：evalSimp
%%%
tag := "eval-simp"
%%%

以下是 `evalSimp` 的真实源码：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Simp.lean:L684-L696]
@[builtin_tactic Lean.Parser.Tactic.simp] def evalSimp : Tactic := fun stx =>
  withMainContext do withSimpDiagnostics do
  let r@{ ctx, simprocs, dischargeWrapper, simpArgs } ← mkSimpContext stx (eraseLocal := false)
  -- ^^^ 解析 config、only、[lemmas]、discharger，构建 Simp.Context
  if ctx.config.suggestions then
    throwError "+suggestions requires using simp? instead of simp"
  let stats ← dischargeWrapper.with fun discharge? =>
    withLoopChecking r do
      simpLocation ctx simprocs discharge? (expandOptLocation stx[5])
      -- ^^^ 根据 `at` 位置决定化简目标还是假设
  if tactic.simp.trace.get (← getOptions) then
    traceSimpCall stx stats.usedTheorems
    -- ^^^ simp? 的核心：记录使用了哪些引理，输出 "Try this: simp only [...]"
  else if Linter.getLinterValue linter.unusedSimpArgs (← Linter.getLinterOptions) then
    withRef stx do
      warnUnusedSimpArgs simpArgs stats.usedTheorems
  return stats.diag
```

这里的 `mkSimpContext` 是关键入口——它解析全部 tactic 参数并构建 `Simp.Context`：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Simp.lean:L452-L477]
def mkSimpContext (stx : Syntax) (eraseLocal : Bool) (kind := SimpKind.simp)
    (ignoreStarArg : Bool := false) (simpTheorems : CoreM SimpTheorems := getSimpTheorems) :
    TacticM MkSimpContextResult := do
  -- ...
  let dischargeWrapper ← mkDischargeWrapper stx[2]
  let simpOnly := !stx[simpOnlyPos].isNone
  -- ^^^ 判断是否 simp only
  let mut simpTheorems ← if simpOnly then
    simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
    -- ^^^ simp only 时从空集开始，只加入 eq_self 和 iff_self
  else
    simpTheorems
    -- ^^^ 裸 simp 加载全局 @[simp] 集
  let simprocs ← if simpOnly then pure {} else Simp.getSimprocs
  let congrTheorems ← getSimpCongrTheorems
  let config ← elabSimpConfig stx[1] (kind := kind)
  if config.locals then
    simpTheorems ← elabSimpLocals simpTheorems kind
    -- ^^^ +locals 模式：自动把局部定义加入展开集
  let ctx ← Simp.mkContext
     (config := config)
     (simpTheorems := #[simpTheorems])
     congrTheorems
  let r ← elabSimpArgs stx[4] (eraseLocal := eraseLocal) (kind := kind)
      (simprocs := #[simprocs]) (ignoreStarArg := ignoreStarArg) ctx
  -- ^^^ 处理 [foo, bar, ← baz, -qux, *] 参数列表
  return { r with dischargeWrapper }
```

## 参数解析：elabSimpArgs 内部
%%%
tag := "elab-simp-args"
%%%

`elabSimpArgs` 逐个处理方括号内的参数，每个参数可以是多种形式：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Simp.lean:L220-L278]
private def elabSimpArg (indexConfig : Meta.ConfigWithKey) (eraseLocal : Bool)
    (kind : SimpKind) (arg : Syntax) : TacticM ElabSimpArgResult := withRef arg do
  try
    if arg.getKind == ``Lean.Parser.Tactic.simpErase then
      -- ^^^ `-foo` 语法：从引理集移除
      let fvar? ← if eraseLocal then Term.isLocalIdent? arg[1] else pure none
      if let some fvar := fvar? then
        return .erase (.fvar fvar.fvarId!)
      else
        let id := arg[1]
        if let .ok declName ← observing (realizeGlobalConstNoOverloadWithInfo id) then
          if (← Simp.isSimproc declName) then
            return .eraseSimproc declName
          else
            return .erase (.decl declName)
        -- ...
    else if arg.getKind == ``Lean.Parser.Tactic.simpLemma then
      -- ^^^ `foo` 或 `← foo` 或 `↓ foo` 语法
      let post :=
        if arg[0].isNone then true
        else arg[0][0].getKind == ``Parser.Tactic.simpPost
      -- ^^^ `↓` 前缀表示 pre 阶段，默认（无前缀或 `↑`）是 post 阶段
      let inv  := !arg[1].isNone
      -- ^^^ `←` 表示反方向
      let term := arg[2]
      match (← resolveSimpIdTheorem? term) with
      | .expr e  =>
        let name ← mkFreshId
        elabDeclToUnfoldOrTheorem indexConfig (.stx name arg) e post inv kind
        -- ^^^ 判断是定义展开还是等式引理
      | .simproc declName =>
        return .addSimproc declName post
        -- ^^^ 用户传入的是一个 simproc
      | .ext ext₁? ext₂? h =>
        return .ext ext₁? ext₂? h
        -- ^^^ 用户传入的是一个 simp 扩展集（如自定义 simp attribute 名）
      -- ...
    else if arg.getKind == ``Lean.Parser.Tactic.simpStar then
      return .star
      -- ^^^ `*` 语法：添加所有局部假设
    -- ...
```

参数处理后的结果在主循环中逐一加入 `SimpTheorems`：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Simp.lean:L334-L361]
-- (在 elabSimpArgs 内部)
for (ref, arg) in args do
  match arg with
  | .addEntries entries =>
    for entry in entries do
      thms := thms.uneraseSimpEntry entry
      thms := thms.addSimpEntry entry
      -- ^^^ 添加引理到 DiscrTree
  | .addLetToUnfold fvarId =>
    thms := thms.addLetDeclToUnfold fvarId
    -- ^^^ let 变量标记为可展开
  | .addSimproc declName post =>
    simprocs ← simprocs.add declName post
  | .erase origin =>
    if origin matches .fvar _ then
      thms := thms.eraseCore origin
    else if ctx.config.autoUnfold then
      thms := thms.eraseCore origin
    else
      thms ← withRef ref <| thms.erase origin
      -- ^^^ 带检查的移除（确认引理确实存在）
  | .ext simpExt? simprocExt? _ =>
    if let some simpExt := simpExt? then
      thmsArray := thmsArray.push (← simpExt.getTheorems)
      -- ^^^ 整个扩展集作为新的 SimpTheorems 层
  -- ...
```

## simpMatch：match 表达式的化简
%%%
tag := "simp-match"
%%%

`simpMatch` 是一个内置 simproc，处理 `match` 表达式。它先尝试直接规约（ι 规约），失败则尝试用 match 的方程引理逐一匹配：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Rewrite.lean:L366-L377]
def simpMatch : Simproc := fun e => do
  unless (← getConfig).iota do
    return .continue
    -- ^^^ config.iota = false 则跳过 match 化简
  if let some e ← withSimpMetaConfig <| reduceRecMatcher? e then
    return .visit { expr := e }
    -- ^^^ 直接 ι 规约成功（match 的判别式是构造子）
  let .const declName _ := e.getAppFn
    | return .continue
  let some info ← getMatcherInfo? declName
    | return .continue
  if let some r ← simpMatchDiscrs? info e then
    return .visit r
    -- ^^^ 化简 match 的判别式（discriminant），看能否触发规约
  simpMatchCore declName e
  -- ^^^ 用 match 的方程引理逐一尝试匹配
```

# 核心类型拆解
%%%
tag := "core-types"
%%%

## Simp.Result
%%%
tag := "simp-result"
%%%

每一步重写的结果。注意 `proof?` 的存在——simp 是一个 **proof-producing rewriter**。

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Types.lean:L24-L37]
structure Result where
  /-- The simplified version of `e` -/
  expr           : Expr
  /-- A proof that `$e = $expr`, where the simplified expression is on the RHS.
  If `none`, the proof is assumed to be `refl`. -/
  proof?         : Option Expr := none
  /--
  If `cache := true` the result is cached.
  Warning: we will remove this field in the future. It is currently used by
  `arith := true`, but we can now refactor the code to avoid the hack.
  -/
  cache          : Bool := true
  deriving Inhabited
```

`proof? = none` 表示改写前后 definitionally equal（证明是 `rfl`）。当多步改写链式组合时，用 `Eq.trans` 拼接：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Types.lean:L47-L48]
def Result.mkEqTrans (r₁ r₂ : Result) : MetaM Result :=
  mkEqTransOptProofResult r₁.proof? r₁.cache r₂
```

## Simp.Step
%%%
tag := "simp-step"
%%%

`pre`/`post` 钩子的返回值，决定后续控制流：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Types.lean:L313-L334]
inductive Step where
  /-- For `pre`: returns result without visiting subexpressions.
      For `post`: returns the result. -/
  | done (r : Result)
  /-- For `pre`: the resulting expression is passed to `pre` again.
      For `post`: passed to `pre` again IF not singlePass and expr changed. -/
  | visit (e : Result)
  /-- For `pre`: continue by visiting subexpressions, then executing `post`.
      For `post`: equivalent to `visit`. -/
  | continue (e? : Option Result := none)
  deriving Inhabited
```

## Simp.Context
%%%
tag := "simp-context"
%%%

simp 引擎的只读上下文：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Types.lean:L61-L120]
structure Context where
  private mk ::
  config            : Config := {}
  zetaDeltaSet      : FVarIdSet := {}
  initUsedZetaDelta : FVarIdSet := {}
  metaConfig        : ConfigWithKey := default
  indexConfig       : ConfigWithKey := default
  maxDischargeDepth : UInt32 := UInt32.ofNatTruncate config.maxDischargeDepth
  simpTheorems      : SimpTheoremsArray := {}
  -- ^^^ 引理集数组（全局 @[simp] + 用户传入 + 局部假设）
  congrTheorems     : SimpCongrTheorems := {}
  -- ^^^ congruence lemma 集
  parent?           : Option Expr := none
  -- ^^^ 当前子项的"父表达式"，用于 arith 等扩展避免重复处理
  dischargeDepth    : UInt32 := 0
  lctxInitIndices   : Nat := 0
  inDSimp : Bool := false
  -- ^^^ 是否在 dsimp 模式（只做 definitional equality 变换）
  deriving Inhabited
```

## Simp.State
%%%
tag := "simp-state"
%%%

可变状态——缓存、步数计数、已使用引理记录：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Types.lean:L245-L251]
structure State where
  cache        : Cache := {}
  congrCache   : CongrCache := {}
  dsimpCache   : ExprStructMap Expr := {}
  usedTheorems : UsedSimps := {}
  numSteps     : Nat := 0
  diag         : Diagnostics := {}
```

## SimpM monad
%%%
tag := "simp-m"
%%%

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Types.lean:L265]
abbrev SimpM := ReaderT MethodsRef $ ReaderT Context $ StateRefT State MetaM
```

三层 Reader/State 叠加在 `MetaM` 上：`MethodsRef`（可插拔方法）、`Context`（只读配置）、`State`（可变状态）。

## Methods：可插拔的钩子
%%%
tag := "simp-methods"
%%%

这是 simp 可扩展性的关键。`dsimp`、`simp_all` 等变体通过替换这些方法改变行为：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Types.lean:L421-L434]
structure Methods where
  pre        : Simproc  := fun _ => return .continue
  post       : Simproc  := fun e => return .done { expr := e }
  dpre       : DSimproc := fun _ => return .continue
  dpost      : DSimproc := fun e => return .done e
  discharge? : Expr → SimpM (Option Expr) := fun _ => return none
  /--
  `wellBehavedDischarge` must **not** be set to `true` IF `discharge?`
  access local declarations with index >= `Context.lctxInitIndices` when
  `contextual := false`.
  Reason: it would prevent us from aggressively caching `simp` results.
  -/
  wellBehavedDischarge : Bool := true
  deriving Inhabited
```

`Simproc` 就是 `Expr → SimpM Step`：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Types.lean:L340]
abbrev Simproc := Expr → SimpM Step
```

## SimpTheorem：单条引理
%%%
tag := "simp-theorem"
%%%

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/SimpTheorems.lean:L143-L165]
structure SimpTheorem where
  keys        : Array SimpTheoremKey := #[]
  -- ^^^ DiscrTree 索引键，从 LHS 编码而来
  levelParams : Array Name := #[]
  proof       : Expr
  priority    : Nat  := eval_prio default
  post        : Bool := true
  -- ^^^ true = post 阶段应用，false = pre 阶段应用
  perm        : Bool := false
  -- ^^^ true 表示 LHS 和 RHS 只差变量排列（如 a + b = b + a）
  origin      : Origin
  rfl         : Bool
  -- ^^^ true 表示 proof 是 rfl / Eq.refl / @[defeq] 定理
  deriving Inhabited
```

## Origin：引理来源
%%%
tag := "simp-origin"
%%%

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/SimpTheorems.lean:L57-L79]
inductive Origin where
  | decl (declName : Name) (post := true) (inv := false)
  -- ^^^ 全局声明，post=应用阶段，inv=是否反向 (←)
  | fvar (fvarId : FVarId)
  -- ^^^ 局部假设
  | stx (id : Name) (ref : Syntax)
  -- ^^^ 用户在 simp [...] 中直接传入的证明项
  | other (name : Name)
  deriving Inhabited, Repr
```

# DiscrTree：引理索引
%%%
tag := "discr-tree"
%%%

simp 的性能关键在于**不用逐一尝试所有引理**。DiscrTree（discrimination tree）是实现这一点的核心数据结构。

引理注册时，提取 LHS 的"骨架"编码为 `Key` 序列组织成前缀 trie；查找时用子项骨架快速定位候选集，再对候选做 `isDefEq` 精确匹配。

```
-- 引理 List.length_cons : (a :: l).length = l.length + 1
-- LHS = List.length (List.cons a l)
-- 编码为 Key 序列：
-- [const `List.length 1, const `List.cons 2, star, star]
--  ^head symbol        ^第一个参数的 head    ^a,l 是变量 → 通配符
```

在 Rewrite.lean 中，`rewrite?` 使用 DiscrTree 进行候选查找：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Rewrite.lean:L207-L235]
def rewrite? (e : Expr) (s : SimpTheoremTree) (erased : PHashSet Origin)
    (tag : String) (rflOnly : Bool) : SimpM (Option Result) := do
  if (← getConfig).index then
    rewriteUsingIndex?
  else
    rewriteNoIndex?
where
  rewriteUsingIndex? : SimpM (Option Result) := do
    let candidates ← withSimpIndexConfig <| s.getMatchWithExtra e
    -- ^^^ 用 DiscrTree 索引查找候选引理（带额外参数信息）
    if candidates.isEmpty then
      trace[Debug.Meta.Tactic.simp] "no theorems found for {tag}-rewriting {e}"
      return none
    else
      let candidates := candidates.insertionSort fun e₁ e₂ => e₁.1.priority > e₂.1.priority
      -- ^^^ 按优先级降序排列
      for (thm, numExtraArgs) in candidates do
        if inErasedSet thm then continue
        -- ^^^ 跳过被 `-` 移除的引理
        if rflOnly then
          unless thm.rfl do
            -- ... 诊断代码 ...
            continue
        if let some result ← tryTheoremWithExtraArgs? e thm numExtraArgs then
          -- ^^^ 尝试匹配并应用
          trace[Debug.Meta.Tactic.simp] "rewrite result {e} => {result.expr}"
          return some result
      return none
```

**性能特征**：LHS 越具体（通配符越少），索引越精确。LHS 是纯 metavariable 的引理会匹配所有子项，退化为线性扫描——这也是 Mathlib linter 会警告 LHS 太泛的 `@[simp]` 引理的原因。

## config.index 与退化模式
%%%
tag := "config-index"
%%%

`rewrite?` 同时实现了两种查找模式。当 `config.index = false` 时，退化为 Lean 3 风格的线性扫描：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Rewrite.lean:L241-L262]
  rewriteNoIndex? : SimpM (Option Result) := do
    let (candidates, numArgs) ← withSimpIndexConfig <| s.getMatchLiberal e
    -- ^^^ getMatchLiberal：只看根 symbol，忽略 DiscrTree 的精细结构
    if candidates.isEmpty then
      trace[Debug.Meta.Tactic.simp] "no theorems found for {tag}-rewriting {e}"
      return none
    else
      let candidates := candidates.insertionSort fun e₁ e₂ => e₁.priority > e₂.priority
      for thm in candidates do
        unless inErasedSet thm || (rflOnly && !thm.rfl) do
          let result? ← withNewMCtxDepth do
            let val  ← thm.getValue
            let type ← inferType val
            let (xs, bis, type) ← forallMetaTelescopeReducing type
            let type ← whnf (← instantiateMVars type)
            let lhs := type.appFn!.appArg!
            let lhsNumArgs := lhs.getAppNumArgs
            tryTheoremCore lhs xs bis val type e thm (numArgs - lhsNumArgs)
          if let some result := result? then
            diagnoseWhenNoIndex thm
            -- ^^^ 当 index=false 成功但 index=true 会失败时，记录诊断信息
            return some result
    return none
```

这个退化模式主要用于诊断：如果一条引理在 `index=true` 下不被找到但在 `index=false` 下被找到，说明引理的 DiscrTree key 有问题。`diagnoseWhenNoIndex` 负责记录这类引理。

## rewritePre 与 rewritePost
%%%
tag := "rewrite-pre-post"
%%%

重写分为 pre（子项递归前）和 post（子项递归后）两个阶段。每个阶段遍历所有 `SimpTheorems` 层：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Rewrite.lean:L379-L389]
def rewritePre (rflOnly := false) : Simproc := fun e => do
  for thms in (← getContext).simpTheorems do
    -- ^^^ 遍历所有 SimpTheorems 层（全局 + 用户传入 + 局部假设）
    if let some r ← rewrite? e thms.pre thms.erased (tag := "pre") (rflOnly := rflOnly) then
      return .visit r
      -- ^^^ 找到匹配，返回 .visit（表示需要继续递归）
  return .continue

def rewritePost (rflOnly := false) : Simproc := fun e => do
  for thms in (← getContext).simpTheorems do
    if let some r ← rewrite? e thms.post thms.erased (tag := "post") (rflOnly := rflOnly) then
      return .visit r
  return .continue
```

每层 `SimpTheorems` 维护两棵独立的 DiscrTree：`pre`（标记为 `↓` 的引理）和 `post`（默认，绝大多数引理）。`pre` 引理在子项递归之前应用，可以拦截表达式避免不必要的递归展开。

# 重写循环：Main.lean 逐函数拆解
%%%
tag := "rewrite-loop"
%%%

## simpImpl：顶层入口
%%%
tag := "simp-impl"
%%%

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Main.lean:L686-L691]
@[export lean_simp]
def simpImpl (e : Expr) : SimpM Result := withIncRecDepth do
  checkSystem "simp"
  if (← isProof e) then
    return { expr := e }
    -- ^^^ 不化简 proof 项！这是一个关键优化。
  trace[Meta.Tactic.simp.heads] "{repr e.toHeadIndex}"
  simpLoop e
```

## simpLoop：主循环
%%%
tag := "simp-loop"
%%%

这是 simp 的核心循环——pre → reduce → 结构递归 → post → 可能重入：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Main.lean:L648-L683]
partial def simpLoop (e : Expr) : SimpM Result := withIncRecDepth do
  let cfg ← getConfig
  if cfg.memoize then
    let cache := (← get).cache
    if let some result := cache.find? e then
      return result
      -- ^^^ 命中缓存，直接返回
  if (← get).numSteps > cfg.maxSteps then
    throwError "`simp` failed: maximum number of steps exceeded"
    -- ^^^ 步数限制防止无限循环
  else
    checkSystem "simp"
    modify fun s => { s with numSteps := s.numSteps + 1 }
    -- ^^^ 步数 +1
    match (← pre e) with
    | .done r  => cacheResult e cfg r
    -- ^^^ pre 已完全处理，不再递归
    | .visit r => cacheResult e cfg (← r.mkEqTrans (← simpLoop r.expr))
    -- ^^^ pre 返回修改后的表达式，重入 simpLoop
    | .continue none => visitPreContinue cfg { expr := e }
    -- ^^^ pre 不做处理，继续标准流程
    | .continue (some r) => visitPreContinue cfg r
where
  visitPreContinue (cfg : Config) (r : Result) : SimpM Result := do
    let eNew ← reduceStep r.expr
    -- ^^^ 先做 beta/iota/zeta/unfold 等基础规约
    if eNew != r.expr then
      trace[Debug.Meta.Tactic.simp] "reduceStep (pre) {e} => {eNew}"
      let r := { r with expr := eNew }
      cacheResult e cfg (← r.mkEqTrans (← simpLoop r.expr))
      -- ^^^ 规约改变了表达式，重入循环
    else
      let r ← r.mkEqTrans (← simpStep r.expr)
      -- ^^^ 按表达式结构递归化简子项
      visitPost cfg r
  visitPost (cfg : Config) (r : Result) : SimpM Result := do
    match (← post r.expr) with
    | .done r' => cacheResult e cfg (← r.mkEqTrans r')
    | .continue none => visitPostContinue cfg r
    | .visit r' | .continue (some r') => visitPostContinue cfg (← r.mkEqTrans r')
  visitPostContinue (cfg : Config) (r : Result) : SimpM Result := do
    let mut r := r
    unless cfg.singlePass || e == r.expr do
      r ← r.mkEqTrans (← simpLoop r.expr)
      -- ^^^ 表达式变了且非 singlePass，重入循环！这是"不动点迭代"的关键。
    cacheResult e cfg r
```

## simpStep：按表达式结构分发
%%%
tag := "simp-step-dispatch"
%%%

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Main.lean:L628-L641]
def simpStep (e : Expr) : SimpM Result := do
  match e with
  | .mdata m e   => let r ← simp e; return { r with expr := mkMData m r.expr }
  | .proj ..     => simpProj e
  | .app ..      => simpApp e        -- ← 函数应用，最常见
  | .lam ..      => simpLambda e     -- λ 抽象
  | .forallE ..  => simpForall e     -- ∀ / →
  | .letE ..     => simpLet e        -- let 绑定
  | .const ..    => simpConst e      -- 常量
  | .bvar ..     => unreachable!
  | .sort ..     => return { expr := e }
  | .lit ..      => return { expr := e }
  | .mvar ..     => return { expr := (← instantiateMVars e) }
  | .fvar ..     => return { expr := (← reduceFVar (← getConfig) (← getSimpTheorems) e) }
```

## simpApp：函数应用的处理
%%%
tag := "simp-app"
%%%

函数应用 `f a₁ a₂ ... aₙ` 是最常见的表达式形式。`simpApp` 先排除字面量，然后委托给 `congr`：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Main.lean:L621-L626]
def simpApp (e : Expr) : SimpM Result := do
  if isOfNatNatLit e || isOfScientificLit e || isCharLit e then
    -- ^^^ 字面量（如 OfNat.ofNat 42）不递归进入
    return { expr := e }
  else
    congr e
```

`congr` 先查用户标注的 `@[congr]` lemma，然后退回自动生成的 congruence theorem：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Main.lean:L608-L619]
def congr (e : Expr) : SimpM Result := do
  let f := e.getAppFn
  if f.isConst then
    let congrThms ← getSimpCongrTheorems
    let cs := congrThms.get f.constName!
    -- ^^^ 查找该函数是否有 @[congr] 标注的 congruence lemma
    for c in cs do
      match (← trySimpCongrTheorem? c e) with
      | none   => pure ()
      | some r => return r
    congrDefault e
    -- ^^^ 没有 @[congr]，退回自动 congruence
  else
    congrDefault e
```

`congrDefault` 尝试自动生成的 congruence theorem，失败则用 `simpAppUsingCongr`（逐参数 `congrArg`/`congrFun`）：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Main.lean:L516-L520]
def congrDefault (e : Expr) : SimpM Result := do
  if let some result ← tryAutoCongrTheorem? e then
    result.mkEqTrans (← visitFn result.expr)
  else
    withParent e <| simpAppUsingCongr e
```

## reduceStep：基础规约
%%%
tag := "reduce-step"
%%%

在 pre 和结构递归之间，`reduceStep` 做 beta/iota/zeta/proj/unfold：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Main.lean:L189-L220]
private def reduceStep (e : Expr) : SimpM Expr := do
  let cfg ← getConfig
  let f := e.getAppFn
  if f.isMVar then
    return (← instantiateMVars e)
  withSimpMetaConfig do
  if cfg.beta then
    if f.isHeadBetaTargetFn false then
      return f.betaRev e.getAppRevArgs
      -- ^^^ β 规约：(fun x => body) arg → body[x := arg]
  if cfg.proj then
    match (← reduceProj? e) with
    | some e => return e
    | none =>
    match (← reduceProjFn? e) with
    | some e => return e
    | none   => pure ()
  if cfg.iota then
    match (← reduceRecMatcher? e) with
    | some e => return e
    -- ^^^ ι 规约：match/recursor 计算
    | none   => pure ()
  if let .letE _ _ v b nondep := e then
    if cfg.zeta && (!nondep || cfg.zetaHave) then
      return expandLet b #[v] (zetaHave := cfg.zetaHave)
      -- ^^^ ζ 规约：展开 let 绑定
  match (← unfold? e) with
  | some e' =>
    trace[Meta.Tactic.simp.rewrite] "unfold {.ofConst e.getAppFn}, {e} ==> {e'}"
    recordSimpTheorem (.decl e.getAppFn.constName!)
    return e'
    -- ^^^ 展开 simp [myFun] 指定的定义
  | none => foldRawNatLit e
```

## simpForall 与 contextual simp
%%%
tag := "simp-forall"
%%%

`simpForall` 处理 `∀` 和 `→`。当 `contextual = true` 且箭头两侧都是命题时，化简右侧会**把左侧加入局部假设**：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Main.lean:L309-L339]
def simpArrow (e : Expr) : SimpM Result := do
  trace[Debug.Meta.Tactic.simp] "arrow {e}"
  let p := e.bindingDomain!
  let q := e.bindingBody!
  let rp ← simp p
  if (← pure (← getConfig).contextual <&&> isProp p <&&> isProp q) then
    -- ^^^ contextual 模式：化简 q 时把 rp.expr 加入假设
    trace[Debug.Meta.Tactic.simp] "ctx arrow {rp.expr} -> {q}"
    withLocalDeclD e.bindingName! rp.expr fun h => withNewLemmas #[h] do
      -- ^^^ h : rp.expr 被加入局部 simp 引理集
      let rq ← simp q
      match rq.proof? with
      | none    => mkImpCongr e rp rq
      | some hq =>
        let hq ← mkLambdaFVars #[h] hq
        if rq.expr.containsFVar h.fvarId! then
          return { expr := (← mkForallFVars #[h] rq.expr),
                   proof? := (← withDefault <| mkImpDepCongrCtx (← rp.getProof) hq) }
        else
          return { expr := e.updateForallE! rp.expr rq.expr,
                   proof? := (← withDefault <| mkImpCongrCtx (← rp.getProof) hq) }
  else
    mkImpCongr e rp (← simp q)
```

`withNewLemmas` 是 contextual simp 的核心辅助——它把新引入的局部变量（如果是 proof）加入 simp 引理集：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Main.lean:L244-L263]
def withNewLemmas {α} (xs : Array Expr) (f : SimpM α) : SimpM α := do
  if (← getConfig).contextual then
    withFreshCache do
      let mut s ← getSimpTheorems
      let mut updated := false
      let ctx ← getContext
      for x in xs do
        if (← isProof x) then
          s ← s.addTheorem (.fvar x.fvarId!) x (config := ctx.indexConfig)
          -- ^^^ 把局部 proof 加入引理集
          updated := true
      if updated then
        withSimpTheorems s f
      else
        f
  else if (← getMethods).wellBehavedDischarge then
    f
  else
    withFreshCache do f
```

## Proof 组合：为什么 simp 不是纯 AST 变换
%%%
tag := "proof-composition"
%%%

初学者容易把 simp 想象成"模式匹配 → 替换子树"的 AST 变换。实际上，每一步重写都必须产出一个类型正确的等式证明。`Result` 的 `proof?` 字段揭示了这一点。

**proof 组合的核心原语**——在 Types.lean 中定义：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Types.lean:L582-L598]
-- 函数参数化简：f = g → f a = g a
def mkCongrFun (r : Result) (a : Expr) : MetaM Result :=
  match r.proof? with
  | none   => return { expr := mkApp r.expr a, proof? := none }
  | some h => return { expr := mkApp r.expr a, proof? := (← Meta.mkCongrFun h a) }

-- 参数化简：a = b → f a = f b
def mkCongrArg (f : Expr) (r : Result) : MetaM Result :=
  match r.proof? with
  | none   => return { expr := mkApp f r.expr, proof? := none }
  | some h => return { expr := mkApp f r.expr, proof? := (← Meta.mkCongrArg f h) }

-- 双侧化简：f = g → a = b → f a = g b
def mkCongr (r₁ r₂ : Result) : MetaM Result :=
  let e := mkApp r₁.expr r₂.expr
  match r₁.proof?, r₂.proof? with
  | none,     none   => return { expr := e, proof? := none }
  | some h,  none    => return { expr := e, proof? := (← Meta.mkCongrFun h r₂.expr) }
  | none,    some h  => return { expr := e, proof? := (← Meta.mkCongrArg r₁.expr h) }
  | some h₁, some h₂ => return { expr := e, proof? := (← Meta.mkCongr h₁ h₂) }
```

注意 `proof? = none` 的优化：当改写前后 definitionally equal 时不构造证明项，大幅减少 proof term 大小。

**λ 抽象的 proof 组合**——需要 `funExt`：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Types.lean:L925-L933]
def Result.addLambdas (r : Result) (xs : Array Expr) : MetaM Result := do
  if xs.isEmpty then return r
  let eNew ← mkLambdaFVars xs r.expr
  match r.proof? with
  | none   => return { expr := eNew }
  | some h =>
    let p ← xs.foldrM (init := h) fun x h => do
      mkFunExt (← mkLambdaFVars #[x] h)
      -- ^^^ 每个 λ 变量都需要一层 funExt 包装
    return { expr := eNew, proof? := p }
```

**Proof 复杂度急剧上升的三个来源**：

1. **Dependent arguments**：当函数的后续参数类型依赖于前面的参数时，改写前面的参数导致后续参数类型变化，需要 `cast`/`Eq.mpr`。
2. **Congruence**：在 `f a₁ ... aₙ` 中化简某个 `aᵢ` 时，需要 congruence lemma 把局部等式提升为全局等式。
3. **Cast 传播**：依赖类型上下文中（如 `Vector α n` 中化简 `n`），类型本身在变化，simp 必须插入 `cast` 维持类型正确性。

这也是为什么 simp 源码中大量代码在处理 proof 构造和组合——真正的工程难点不只是"匹配到哪条引理"，而是"怎样把局部改写拼成全局合法证明"。

## congrArgs：逐参数化简的 proof 构造
%%%
tag := "congr-args"
%%%

`congrArgs` 展示了 simp 如何逐参数化简函数应用并正确组合 proof：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Types.lean:L633-L663]
def congrArgs (r : Result) (args : Array Expr) : SimpM Result := do
  if args.isEmpty then
    return r
  else
    let cfg ← getConfig
    let infos := (← getFunInfoNArgs r.expr args.size).paramInfo
    let mut r := r
    let mut i := 0
    for arg in args do
      if h : i < infos.size then
        let info := infos[i]
        if cfg.ground && info.isInstImplicit then
          r ← mkCongrFun r arg
          -- ^^^ ground 模式下跳过实例参数
        else if !info.hasFwdDeps then
          r ← mkCongr r (← simp arg)
          -- ^^^ 无前向依赖：正常 simp + mkCongr
        else if (← whnfD (← inferType r.expr)).isArrow then
          r ← mkCongr r (← simp arg)
        else
          r ← mkCongrFun r (← dsimp arg)
          -- ^^^ 有前向依赖：只做 dsimp（保持 definitional equality）
      else if (← whnfD (← inferType r.expr)).isArrow then
        r ← mkCongr r (← simp arg)
      else
        r ← mkCongrFun r (← dsimp arg)
      i := i + 1
    return r
```

关键决策：**有前向依赖的参数只做 `dsimp`**。因为如果用 `simp` 改变了参数值（产生非 `rfl` 的 proof），后续参数的类型会变化，需要 cast——而 `dsimp` 保证 definitional equality，类型不变。

# 单步重写：Rewrite.lean
%%%
tag := "single-step-rewrite"
%%%

## tryTheorem?：匹配 → 实例化 → discharge → 构造 proof
%%%
tag := "try-theorem"
%%%

这是 simp 的最内层核心。给定一个表达式 `e` 和一条引理 `thm`，尝试用 `isDefEq` 匹配 LHS，然后 synthesize 隐式参数和 discharge 前提：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Rewrite.lean:L187-L202]
def tryTheorem? (e : Expr) (thm : SimpTheorem) : SimpM (Option Result) := do
  withNewMCtxDepth do
    -- ^^^ 创建新的 metavariable 上下文，确保不污染外层
    let val  ← thm.getValue
    let type ← inferType val
    let (xs, bis, type) ← forallMetaTelescopeReducing type
    -- ^^^ 把引理的全称量化变量替换为新鲜 metavariable
    let type ← whnf (← instantiateMVars type)
    let lhs := type.appFn!.appArg!
    -- ^^^ 提取等式的 LHS
    match (← tryTheoremCore lhs xs bis val type e thm 0) with
    | some result => return some result
    | none =>
      let lhsNumArgs := lhs.getAppNumArgs
      let eNumArgs   := e.getAppNumArgs
      if eNumArgs > lhsNumArgs then
        tryTheoremCore lhs xs bis val type e thm (eNumArgs - lhsNumArgs)
        -- ^^^ 处理 e 比 LHS 多出的参数（部分应用匹配）
      else
        return none
```

`tryTheoremCore` 做实际的匹配工作：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Rewrite.lean:L115-L176]
private def tryTheoremCore (lhs : Expr) (xs : Array Expr) (bis : Array BinderInfo)
    (val : Expr) (type : Expr) (e : Expr) (thm : SimpTheorem)
    (numExtraArgs : Nat) : SimpM (Option Result) := do
  recordTriedSimpTheorem thm.origin
  let rec go (e : Expr) : SimpM (Option Result) := do
    trace[Debug.Meta.Tactic.simp] "trying {← ppSimpTheorem thm} to rewrite{indentExpr e}"
    if (← withSimpMetaConfig <| isDefEq lhs e) then
      -- ^^^ 核心：用 isDefEq 匹配 lhs 和 e
      unless (← synthesizeArgs thm.origin bis xs) do
        return none
        -- ^^^ 合成实例参数 + discharge 前提
      let proof? ← if (← useImplicitDefEqProof thm) then
        pure none
        -- ^^^ rfl 引理不需要显式 proof
      else
        let proof ← instantiateMVars (mkAppN val xs)
        if (← hasAssignableMVar proof) then
          trace[Meta.Tactic.simp.rewrite] "{← ppSimpTheorem thm}, has unassigned metavariables"
          return none
        pure <| some proof
      let rhs := (← instantiateMVars type).appArg!
      -- ^^^ 实例化后的 RHS
      if (← instantiateMVars e) == rhs then
        -- ^^^ 重写后表达式没变，跳过
        return none
      if thm.perm then
        if !(← acLt rhs e .reduceSimpleOnly) then
          trace[Meta.Tactic.simp.rewrite] "{← ppSimpTheorem thm}, perm rejected"
          return none
          -- ^^^ 排列引理（如 add_comm）：只在 rhs < e 时应用，防止循环
      trace[Meta.Tactic.simp.rewrite] "{← ppSimpTheorem thm}:{indentExpr e}\n==>{indentExpr rhs}"
      recordSimpTheorem thm.origin
      return some { expr := rhs, proof? }
    else
      unless lhs.isMVar do
        trace[Meta.Tactic.simp.unify] "{← ppSimpTheorem thm}, failed to unify"
      return none
  -- ... 处理 extraArgs ...
```

## synthesizeArgs：合成参数与 discharge 前提
%%%
tag := "synthesize-args"
%%%

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Rewrite.lean:L58-L95]
def synthesizeArgs (thmId : Origin) (bis : Array BinderInfo) (xs : Array Expr) :
    SimpM Bool := do
  let skipAssignedInstances := tactic.skipAssignedInstances.get (← getOptions)
  for x in xs, bi in bis do
    let type ← inferType x
    if !skipAssignedInstances && bi.isInstImplicit then
      unless (← synthesizeInstance x type) do
        return false
        -- ^^^ 实例隐式参数：尝试类型类合成
    if (← instantiateMVars x).isMVar then
      -- ^^^ 参数仍未赋值
      if (← isClass? type).isSome then
        if (← synthesizeInstance x type) then
          continue
          -- ^^^ 先尝试类型类合成
      if (← isProp type) then
        unless (← discharge?' thmId x type) do
          return false
          -- ^^^ 命题参数：调用 discharger 证明
  return true
```

## 默认 pre/post 钩子
%%%
tag := "default-pre-post"
%%%

默认的 pre/post 钩子组合了多个 simproc。以 `postDefault` 为例：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Rewrite.lean:L532-L537]
def postDefault (s : SimprocsArray) : Simproc :=
  rewritePost >>
  -- ^^^ 用 post DiscrTree 查找并尝试引理
  userPostSimprocs s >>
  -- ^^^ 用户注册的 simproc
  simpGround >>
  -- ^^^ ground term evaluation
  simpArith >>
  -- ^^^ 线性算术化简
  simpUsingDecide
  -- ^^^ 用 decide 证明
```

`>>` 是 `Simproc` 的组合子（`andThen`）：如果前一个返回 `continue`，则调用下一个。

# Congruence Lemma
%%%
tag := "congruence-lemma"
%%%

## 为什么需要 congruence lemma
%%%
tag := "why-congr"
%%%

标准递归化简逐参数处理，但有些函数的参数之间有**依赖关系**。经典例子——`if`：化简 then 分支时应假设条件为真。congruence lemma 告诉 simp 在化简各参数时应该假设什么。

## SimpCongrTheorem 的定义
%%%
tag := "simp-congr-theorem"
%%%

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/SimpCongrTheorems.lean:L23-L28]
structure SimpCongrTheorem where
  theoremName   : Name
  funName       : Name
  hypothesesPos : Array Nat
  -- ^^^ 哪些参数位置是"假设"（需要在特定条件下化简）
  priority      : Nat
  deriving Inhabited, Repr
```

## @\[congr\] 注册
%%%
tag := "congr-registration"
%%%

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/SimpCongrTheorems.lean:L142-L150]
builtin_initialize
  registerBuiltinAttribute {
    name  := `congr
    descr := "congruence theorem"
    add   := fun declName stx attrKind => do
      let prio ← getAttrParamOptPrio stx[1]
      discard <| addSimpCongrTheorem declName attrKind prio |>.run {} {}
  }
```

## trySimpCongrTheorem?：应用 congruence lemma
%%%
tag := "try-congr-theorem"
%%%

这是一个复杂但关键的函数。它用 `isDefEq` 匹配 LHS，然后对每个 hypothesis 位置调用 `processCongrHypothesis`（实质上是递归 `simp` 子项）：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Main.lean:L557-L606]
def trySimpCongrTheorem? (c : SimpCongrTheorem) (e : Expr) :
    SimpM (Option Result) := withNewMCtxDepth do withParent e do
  recordCongrTheorem c.theoremName
  let thm ← mkConstWithFreshMVarLevels c.theoremName
  let thmType ← inferType thm
  let (xs, bis, type) ← forallMetaTelescopeReducing thmType
  -- ^^^ 实例化 congr lemma 的全称量化变量
  if c.hypothesesPos.any (· ≥ xs.size) then
    return none
  let lhs := type.appFn!.appArg!
  let rhs := type.appArg!
  -- ...处理 extra args...
  if (← withSimpMetaConfig <| isDefEq lhs e) then
    -- ^^^ 匹配 congr lemma 的 LHS 和当前表达式
    let mut modified := false
    for i in c.hypothesesPos do
      let h := xs[i]!
      let hType ← instantiateMVars (← inferType h)
      try
        if (← processCongrHypothesis h hType) then
          modified := true
          -- ^^^ 递归化简该 hypothesis 对应的子项
      catch _ =>
        return none
    unless modified do
      return none
      -- ^^^ 没有子项被修改，不应用
    unless (← synthesizeArgs (.decl c.theoremName) bis xs) do
      return none
    let eNew ← instantiateMVars rhs
    let mut proof ← instantiateMVars (mkAppN thm xs)
    -- ... 处理 iff → propext ...
    if (← hasAssignableMVar proof <||> hasAssignableMVar eNew) then
      return none
    congrArgs { expr := eNew, proof? := proof } extraArgs
  else
    return none
```

`processCongrHypothesis` 对每个 hypothesis 做递归 simp：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Main.lean:L523-L554]
def processCongrHypothesis (h : Expr) (hType : Expr) : SimpM Bool := do
  forallTelescopeReducing hType fun xs hType => withNewLemmas xs do
    -- ^^^ 展开 hypothesis 的全称量化（可能带来新的局部假设）
    let lhs ← instantiateMVars hType.appFn!.appArg!
    let r ← simp lhs
    -- ^^^ 递归 simp 化简 lhs
    let rhs := hType.appArg!
    rhs.withApp fun m zs => do
      let val ← mkLambdaFVars zs r.expr
      unless (← withSimpMetaConfig <| isDefEq m val) do
        throwCongrHypothesisFailed
      let mut proof ← r.getProof
      -- ... 处理 iff ...
      unless (← isDefEq h (← mkLambdaFVars xs proof)) do
        throwCongrHypothesisFailed
      return r.proof?.isSome || (xs.size > 0 && lhs != r.expr)
```

## 自动生成 vs @\[congr\] 手写
%%%
tag := "auto-vs-hand-congr"
%%%

Lean 为大多数函数自动生成 congruence theorem（通过 `mkCongrSimp?`）。自动生成的逻辑会分析每个参数的依赖关系，将参数分为 `fixed`、`eq`、`cast`、`subsingletonInst` 几类。只有当自动生成不足（如 `if` 分支需要条件假设）时，才需要手写 `@[congr]` lemma。

# Discharger
%%%
tag := "discharger"
%%%

## discharge?' 的真实实现
%%%
tag := "discharge-impl"
%%%

当引理有前提时，`synthesizeArgs` 会调用 `discharge?'` 来证明。以下是完整实现：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Rewrite.lean:L32-L56]
def discharge?' (thmId : Origin) (x : Expr) (type : Expr) : SimpM Bool := do
  let r : DischargeResult ← withTraceNode `Meta.Tactic.simp.discharge (fun
      | .ok .proved       => return m!"{← ppOrigin thmId} discharge {checkEmoji}{indentExpr type}"
      | .ok .notProved    => return m!"{← ppOrigin thmId} discharge {crossEmoji}{indentExpr type}"
      | .ok .maxDepth     => return m!"{← ppOrigin thmId} discharge {crossEmoji} max depth"
      | .ok .failedAssign => return m!"{← ppOrigin thmId} discharge {crossEmoji} failed to assign proof"
      | .error err        => return m!"{← ppOrigin thmId} discharge {crossEmoji}{indentD err.toMessageData}")
    do
    let ctx ← getContext
    if ctx.dischargeDepth >= ctx.maxDischargeDepth then
      return .maxDepth
      -- ^^^ 超过最大递归深度（默认 2），放弃
    else withIncDischargeDepth do
      let usedTheorems := (← get).usedTheorems
      -- ^^^ 保存当前已使用引理集，失败时回滚
      match (← withPreservedCache <| (← getMethods).discharge? type) with
      | some proof =>
        unless (← isDefEq x proof) do
          modify fun s => { s with usedTheorems }
          return .failedAssign
        return .proved
      | none =>
        modify fun s => { s with usedTheorems }
        -- ^^^ discharge 失败，回滚 usedTheorems
        return .notProved
  return r = .proved
```

关键点：discharge 失败时**回滚** `usedTheorems`，确保未成功的 discharge 不会污染 trace。

## 默认 discharger
%%%
tag := "default-discharger"
%%%

默认 discharger 定义在 Rewrite.lean 末尾：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Rewrite.lean:L627-L638]
def dischargeDefault? (e : Expr) : SimpM (Option Expr) := do
  let e := e.cleanupAnnotations
  if isEqnThmHypothesis e then
    -- ^^^ 特殊处理 match 方程的 hypothesis（形如 ∀ ..., a = b → ... → False）
    if let some r ← dischargeUsingAssumption? e then return some r
    if let some r ← dischargeEqnThmHypothesis? e then return some r
  let r ← simp e
  -- ^^^ 递归调用 simp 尝试把前提化简为 True
  if let some p ← dischargeRfl r.expr then
    return some (mkApp4 (mkConst ``Eq.mpr [levelZero]) e r.expr (← r.getProof) p)
  else if r.expr.isTrue then
    return some (← mkOfEqTrue (← r.getProof))
    -- ^^^ 化简为 True，构造 proof
  else
    return none
```

## 自定义 discharger 的实现
%%%
tag := "custom-discharger"
%%%

用户写 `simp (discharger := omega)` 时，`tacticToDischarge` 把 tactic 包装成 `discharge?`：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Simp.lean:L37-L62]
def tacticToDischarge (tacticCode : Syntax) :
    TacticM (IO.Ref Term.State × Simp.Discharge) := do
  let tacticCode ← `(tactic| try ($tacticCode:tacticSeq))
  let ref ← IO.mkRef (← getThe Term.State)
  let ctx ← readThe Term.Context
  let disch : Simp.Discharge := fun e => do
    let mvar ← mkFreshExprSyntheticOpaqueMVar e `simp.discharger
    -- ^^^ 创建一个类型为 e 的 goal
    let s ← ref.get
    let runTac? : TermElabM (Option Expr) :=
      try
        Term.withoutModifyingElabMetaStateWithInfo do
          Term.withSynthesize (postpone := .no) do
            Term.runTactic (report := false) mvar.mvarId! tacticCode .term
            -- ^^^ 运行用户指定的 tactic（如 omega）
          let result ← instantiateMVars mvar
          if result.hasExprMVar then
            return none
          else
            return some result
      catch _ =>
        return none
    let (result?, s) ← liftM (m := MetaM) <| Term.TermElabM.run runTac? ctx s
    ref.set s
    return result?
  return (ref, disch)
```

# simp\_all 的特殊逻辑
%%%
tag := "simp-all"
%%%

## 入口
%%%
tag := "simp-all-entry"
%%%

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Simp.lean:L698-L713]
@[builtin_tactic Lean.Parser.Tactic.simpAll] def evalSimpAll : Tactic := fun stx =>
  withMainContext do withSimpDiagnostics do
  let r@{ ctx, simprocs, dischargeWrapper := _, simpArgs } ←
    mkSimpContext stx (eraseLocal := true) (kind := .simpAll) (ignoreStarArg := true)
    -- ^^^ eraseLocal := true 允许从引理集中移除局部假设
    -- ^^^ ignoreStarArg := true 因为 simp_all 隐式使用所有假设
  if ctx.config.suggestions then
    throwError "+suggestions requires using simp_all? instead of simp_all"
  let (result?, stats) ←
    withLoopChecking r do
      simpAll (← getMainGoal) ctx (simprocs := simprocs)
      -- ^^^ 调用 simpAll 而不是 simpLocation
  match result? with
  | none => replaceMainGoal []
  | some mvarId => replaceMainGoal [mvarId]
  -- ... trace ...
```

`simp_all` 与 `simp` 的核心区别：

1. **化简所有假设和目标**，不仅仅是目标。
2. **假设之间可以互相化简**——化简假设 `hᵢ` 时，把其他假设加入引理集。
3. **多轮迭代直到不动点**：每轮化简后更新引理集，使后续假设能看到前面的结果。
4. 假设化简为 `True` 则丢弃，化简为 `False` 则 `contradiction` 结束。

## simp\_all vs simp at \*
%%%
tag := "simp-all-vs-star"
%%%

`simp at *` 对每个假设独立运行 simp，引理集在整个过程中不变。`simp_all` 每化简一个假设后更新引理集，能力更强但也更重。

```
-- [可运行]
-- simp_all 能解决，simp at * 不一定能
example (h1 : a = 0) (h2 : a + b = 5) : b = 5 := by
  simp_all
  -- 第一轮：用 h1 化简 h2 → 0 + b = 5 → b = 5
  -- 然后目标被新的 h2 直接解决
```

# dsimp 的实现
%%%
tag := "dsimp-impl"
%%%

`dsimp` 复用 simp 框架但替换 `Methods`，只做 definitional equality 变换。

## dsimpImpl
%%%
tag := "dsimp-impl-detail"
%%%

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Main.lean:L492-L500]
@[export lean_dsimp]
private partial def dsimpImpl (e : Expr) : SimpM Expr := do
  let cfg ← getConfig
  unless cfg.dsimp do
    return e
  let m ← getMethods
  let pre := m.dpre >> doNotVisitOfNat >> doNotVisitOfScientific
      >> doNotVisitCharLit >> doNotVisitProofs
  -- ^^^ 组合多个 DSimproc：跳过字面量和 proof 项
  let post := m.dpost >> dsimpReduce
  -- ^^^ dpost 钩子 + 基础规约
  withInDSimpWithCache fun cache => do
    transformWithCache e cache (usedLetOnly := cfg.zeta || cfg.zetaUnused)
        (pre := pre) (post := post)
```

## dsimp 与 simp 的核心区别
%%%
tag := "dsimp-vs-simp"
%%%

- **等式类型**：simp 使用 propositional equality，dsimp 使用 definitional equality
- **引理要求**：simp 可用任意 `@[simp]` 引理，dsimp 只用 `rfl` 引理（`proof` 是 `rfl`/`Eq.refl`）
- **产出**：simp 产出 `Result`（含 `proof?`），dsimp 产出 `Expr`（新表达式，无需 proof）
- **discharge**：simp 支持，dsimp 不支持（`fun _ => return none`）
- **用途**：simp 尽可能化简，dsimp 只做 beta/iota/zeta + rfl 引理

`dsimp` 的结果与原表达式 definitionally equal，因此旧目标和新目标在类型检查器看来是同一个命题——不需要任何 proof 项中转。这使得 `dsimp` 在依赖类型上下文中更安全，也更快。

## dsimp 的 DSimproc
%%%
tag := "dsimp-simproc"
%%%

`DSimproc` 类似 `Simproc` 但返回 `DStep`（即 `TransformStep`），不需要 proof：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Types.lean:L339]
abbrev DSimproc := Expr → SimpM DStep
```

dsimp 的 drewritePre/drewritePost 只用 `rflOnly := true` 的引理：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Rewrite.lean:L391-L401]
def drewritePre : DSimproc := fun e => do
  for thms in (← getContext).simpTheorems do
    if let some r ← rewrite? e thms.pre thms.erased (tag := "dpre") (rflOnly := true) then
      return .visit r.expr
      -- ^^^ 只返回表达式，不返回 proof
  return .continue

def drewritePost : DSimproc := fun e => do
  for thms in (← getContext).simpTheorems do
    if let some r ← rewrite? e thms.post thms.erased (tag := "dpost") (rflOnly := true) then
      return .visit r.expr
  return .continue
```

## 何时用 dsimp
%%%
tag := "when-dsimp"
%%%

- 化简后类型不变（beta/iota）：`dsimp` 更快，无证明开销。
- 在 `conv` 中做局部化简：`dsimp` 不改变外层类型。
- 依赖类型上下文中化简：`dsimp` 更安全，不引入 `Eq.mpr`。
- 需要应用非 `rfl` 的等式引理：只能用 `simp`。

# 调试：trace 输出详解
%%%
tag := "trace-debugging"
%%%

## trace 开关一览
%%%
tag := "ch06-trace-options"
%%%

```
-- [可运行]
set_option trace.Meta.Tactic.simp.rewrite true    -- 每条重写
set_option trace.Meta.Tactic.simp.discharge true   -- discharge 过程
set_option trace.Meta.Tactic.simp true             -- 所有内部步骤
set_option trace.Meta.Tactic.simp.congr true       -- congruence lemma 使用
```

## 常见 trace 模式与诊断
%%%
tag := "trace-patterns"
%%%

**模式 1：没有任何 rewrite trace**

诊断：没有引理的 LHS 匹配。原因：自定义函数未展开 / 引理不在 simp 集中 / DiscrTree key 不匹配。

修复：`simp [myFun]` 展开定义，或检查引理是否在集合中。

**模式 2：引理匹配了但 discharge 失败**

```
[Meta.Tactic.simp.discharge] Nat.sub_add_cancel discharge ✗ 1 ≤ n
```

诊断：条件引理的 LHS 匹配成功，但前提无法被默认 discharger 证明。

修复：`have h : 1 ≤ n := ...` 或 `simp (discharger := omega)`。

**模式 3：反复出现同一对重写**

诊断：simp 循环——`a + b → b + a → a + b → ...`。

修复：从 simp 集中移除导致循环的引理，改用 `rw` 手动定向重写。

## 组合调试策略
%%%
tag := "combined-debug-strategy"
%%%

1. **先用 `simp?`**——看实际用了哪些引理；
2. **开 `trace.Meta.Tactic.simp.rewrite`**——看重写序列；
3. **怀疑 discharge 问题，加开 `trace.Meta.Tactic.simp.discharge`**；
4. **trace 完全为空，检查引理是否在 simp 集中**。

# 扩展点与自定义
%%%
tag := "extension-points"
%%%

## Simproc 机制
%%%
tag := "simproc-mechanism"
%%%

`Simproc`（simplification procedure）是 simp 的主要扩展点。它是一个函数 `Expr → SimpM Step`，可以注册为 pre 或 post 钩子。

例如 `simpUsingDecide`——用 `decide` 证明布尔命题：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Rewrite.lean:L276-L291]
@[inline] def simpUsingDecide : Simproc := fun e => do
  unless (← getConfig).decide do
    return .continue
  if e.hasFVar || e.hasMVar || e.isTrue || e.isFalse then
    return .continue
    -- ^^^ 只处理不含自由变量的 ground 命题
  try
    let d ← mkDecide e
    let r ← withDefault <| whnf d
    if r.isConstOf ``true then
      return .done { expr := mkConst ``True,
        proof? := mkAppN (mkConst ``eq_true_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``true))] }
    else if r.isConstOf ``false then
      return .done { expr := mkConst ``False,
        proof? := mkAppN (mkConst ``eq_false_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``false))] }
    else
      return .continue
  catch _ =>
    return .continue
```

## Simproc 的组合
%%%
tag := "simproc-composition"
%%%

多个 Simproc 用 `>>` (`andThen`) 组合成管道：

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Types.lean:L370-L377]
@[always_inline]
def andThen (f g : Simproc) : Simproc := fun e => do
  match (← f e) with
  | .done r            => return .done r
  -- ^^^ f 返回 done，直接采纳
  | .continue none     => g e
  -- ^^^ f 放弃，交给 g
  | .continue (some r) => mkEqTransResultStep r (← g r.expr)
  -- ^^^ f 做了部分修改，把 proof 传递给 g
  | .visit r           => return .visit r
  -- ^^^ f 返回 visit，跳过 g
```

## mkDefaultMethods：默认方法的组装
%%%
tag := "mk-default-methods"
%%%

```
-- [Lean 4 v4.30.0-rc1, Lean/Meta/Tactic/Simp/Rewrite.lean:L642-L652]
def mkMethods (s : SimprocsArray) (discharge? : Discharge)
    (wellBehavedDischarge : Bool) : Methods := {
  pre        := preDefault s
  -- ^^^ rewritePre >> simpMatch >> userPreSimprocs >> simpUsingDecide
  post       := postDefault s
  -- ^^^ rewritePost >> userPostSimprocs >> simpGround >> simpArith >> simpUsingDecide
  dpre       := dpreDefault s
  dpost      := dpostDefault s
  discharge?
  wellBehavedDischarge
}

def mkDefaultMethodsCore (simprocs : SimprocsArray) : Methods :=
  mkMethods simprocs dischargeDefault? (wellBehavedDischarge := true)
```

## 编写自定义 simp-like tactic 的最小检查清单
%%%
tag := "custom-simp-checklist"
%%%

1. **定义你的 `Simp.Methods`**——至少实现 `post`（核心重写逻辑）。如果只是添加领域特定规则，用 `pre` 钩子拦截特定表达式即可。
2. **确保 proof 项正确组合**——每一步重写必须产出 `proof? : Option Expr`。
3. **处理步数限制和缓存**——复用 `Simp.State` 的 `numSteps` 和 `cache`。
4. **考虑 congruence**——决定是否复用 simp 的 congruence lemma 查找。
5. **提供 trace 输出**——在关键决策点输出 trace。

# 架构全景图
%%%
tag := "architecture-overview"
%%%

```
用户层
┌─────────────────────────────────────────────────┐
│  simp [foo, bar]  /  simp only [...]            │
│  simp_all  /  dsimp                             │
└─────────┬───────────────────────────────────────┘
          │
Tactic 层 (TacticM)                [Elab/Tactic/Simp.lean]
┌─────────┴───────────────────────────────────────┐
│  evalSimp / evalSimpAll / evalDSimp              │
│  · 解析参数 (config, only, lemmas, discharger)  │
│  · 构建 Simp.Context                            │
│  · 调用 simpLocation / simpAll                  │
└─────────┬───────────────────────────────────────┘
          │
Meta 层 (MetaM / SimpM)           [Meta/Tactic/Simp/Main.lean]
┌─────────┴───────────────────────────────────────┐
│  simpImpl → simpLoop  ←── 核心递归               │
│  ├── pre 钩子 (rewritePre >> simpMatch >> ...)  │
│  ├── reduceStep (beta/iota/zeta/unfold)         │
│  ├── simpStep (按结构分发)                       │
│  │   ├── simpApp → congr                        │
│  │   │   ├── trySimpCongrTheorem? (@[congr])    │
│  │   │   └── tryAutoCongrTheorem? (自动)         │
│  │   ├── simpForall / simpArrow (contextual)    │
│  │   └── simpLambda / simpLet / simpProj        │
│  ├── post 钩子 (rewritePost >> simprocs >> ...)  │
│  │   └── rewrite?                               │
│  │       ├── DiscrTree.getMatchWithExtra (索引)  │
│  │       ├── tryTheorem? → isDefEq (匹配)        │
│  │       └── discharge?' (条件证明)              │
│  └── 缓存 + 步数检查 + 不动点重入               │
└─────────────────────────────────────────────────┘

数据层                             [Meta/Tactic/Simp/Types.lean]
┌─────────────────────────────────────────────────┐
│  SimpTheoremsArray → DiscrTree (LHS → 候选引理)  │
│  SimpCongrTheorems (函数 → congruence lemma)     │
│  Simp.Config / Context / State / Result / Step   │
│  Methods { pre, post, dpre, dpost, discharge? }  │
└─────────────────────────────────────────────────┘
```

# 源码阅读路线图
%%%
tag := "source-reading-guide"
%%%

如果你打算从源码层面深入理解 simp，建议按以下 6 步顺序阅读：

1. **`Types.lean`**——先读数据类型。理解 `Result`、`Step`、`Methods`、`Config`、`SimpM` 的结构，这是所有后续代码的"词汇表"。

2. **`Main.lean`**——核心递归。重点读 `simpImpl`、`simpLoop`、`simpStep`、`simpApp`，理解 pre → reduce → 结构递归 → post 的流程。

3. **`Rewrite.lean`**——引理匹配。重点读 `rewrite?` 和 `tryTheoremCore`，理解 DiscrTree 候选筛选 → `isDefEq` 匹配 → discharge 的三阶段流程。

4. **`SimpTheorems.lean`**——引理管理。理解 `SimpTheorem`、`Origin`、`@[simp]` 注册流程。

5. **`SimpCongrTheorems.lean`**——congruence lemma。理解 `@[congr]` 属性的注册和 `mkSimpCongrTheorem` 的验证逻辑。

6. **`Elab/Tactic/Simp.lean`**——tactic 入口。最后读用户界面层。此时你已理解引擎内部，tactic 层代码会非常清晰。

> **提示**：每个文件中搜索 `trace` 关键字，可以快速定位到关键的控制流分支——trace 输出点通常就是逻辑分支点。

# 练习
%%%
tag := "ch06-exercises"
%%%

## 练习 1（热身）：基本 simp
%%%
tag := "exercise-6-1"
%%%

```
-- [可运行]
example : [1, 2, 3].length = 3 := by
  sorry

example (n : Nat) : n + 0 + 0 + 0 = n := by
  sorry
```

## 练习 2（simp only）
%%%
tag := "exercise-6-2"
%%%

```
-- [可运行]
-- 先用 simp? 找出需要的引理，再改写为 simp only 版本。
example (a b : Nat) : a + 0 + (b + 0) = a + b := by
  sorry
```

## 练习 3（debug）：为什么 simp 失败了？
%%%
tag := "exercise-6-3"
%%%

```
-- [可运行]
def double (n : Nat) := 2 * n

example : double 3 = 6 := by
  simp  -- simp made no progress!
  sorry
```

提示：simp 不认识 `double`。你需要告诉它展开。

## 练习 4（综合）
%%%
tag := "exercise-6-4"
%%%

```
-- [可运行]
example (n : Nat) (h : n > 0) :
    [n].length + (n - 1 + 1) = n + 1 := by
  sorry
  -- 提示：先用 simp 化简 [n].length，再用 omega 处理算术
```

## 练习 5（源码阅读）
%%%
tag := "exercise-6-5"
%%%

阅读 `simpLoop` 的源码（Main.lean:L648-L683），回答以下问题：

1. `pre` 返回 `.done` 和 `.visit` 的区别是什么？
2. 什么条件下 `simpLoop` 会重入自身？
3. `singlePass` 配置如何改变循环行为？

# 下一章预告
%%%
tag := "ch06-next-chapter"
%%%

`simp` 擅长"逐步重写化简"，但有些等式它处理不了——比如多项式恒等式 `(a + b)² = a² + 2ab + b²`。下一章进入 `ring`：基于**范式化（normalization）** 的判定过程，专门解决可交换环上的等式问题。
