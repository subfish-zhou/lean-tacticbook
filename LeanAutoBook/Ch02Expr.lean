import VersoManual

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch02Expr"

#doc (Manual) "第二章 Expr：Lean 4 的内部表示" =>
%%%
file := "Ch02Expr"
tag := "ch02-expr"
%%%

*本章目标*：理解 {moduleTerm}`@Expr` 的构造方式、模式匹配惯用法，以及在元程序中操作表达式的基本技巧。

# Expr 是什么
%%%
tag := "what-is-expr"
%%%

Lean 4 中的每个项——数值、函数、命题、证明——在内核里都表示为 {moduleTerm}`@Expr` 类型的值。当你写 `fun n => n + 1`，Lean 解析并精化后，内部存储的就是一棵 {moduleTerm}`@Expr` 树。

理解 {moduleTerm}`@Expr` 是写 tactic 的基础：你的 tactic 读取目标（一个 {moduleTerm}`@Expr`），分析它的结构，构造新的 {moduleTerm}`@Expr` 作为证明项。

# Expr 的构造子
%%%
tag := "expr-constructors"
%%%

{moduleTerm}`@Expr` 定义在 {lit}`Lean/Expr.lean` 中，有以下核心构造子：

```
inductive Expr where
  | bvar    (deBruijnIndex : Nat)           -- 绑定变量（de Bruijn 索引）
  | fvar    (fvarId : FVarId)               -- 自由变量（局部上下文中的变量）
  | mvar    (mvarId : MVarId)               -- 元变量（未解决的目标/hole）
  | sort    (u : Level)                     -- Sort（Type u / Prop）
  | const   (declName : Name) (us : List Level)  -- 常量（定义/定理的引用）
  | app     (fn : Expr) (arg : Expr)        -- 函数应用
  | lam     (binderName : Name) (binderType : Expr) (body : Expr) (bi : BinderInfo)  -- λ
  | forallE (binderName : Name) (binderType : Expr) (body : Expr) (bi : BinderInfo)  -- ∀/→
  | letE    (declName : Name) (type : Expr) (value : Expr) (body : Expr) (nonDep : Bool)  -- let
  | lit     (l : Literal)                   -- 字面量（数值/字符串）
  | mdata   (data : MData) (expr : Expr)    -- 元数据注解
  | proj    (typeName : Name) (idx : Nat) (struct : Expr)  -- 结构体投影
```

看起来很多，但日常 tactic 编写中最常遇到的是 `app`、`const`、`fvar`、`mvar`、`lam`、`forallE` 这六个。

# 表达式如何编码：几个例子
%%%
tag := "expr-encoding-examples"
%%%

> 以下树形结构是*示意图*，用于说明 `app` 的嵌套方式，而不是逐字符精确的 elaborated form。

## 例 1：`Nat.add 2 3`
%%%
tag := "example-nat-add"
%%%

```
app
├── app
│   ├── const `Nat.add []
│   └── lit (Literal.natVal 2)
└── lit (Literal.natVal 3)
```

Lean 4 中多参数函数是 curried 的：`f a b` 表示为 `app (app f a) b`。

## 例 2：`fun n : Nat => n + 1`
%%%
tag := "example-lambda"
%%%

```
lam `n (const `Nat [])
  (app (app (const `HAdd.hAdd [...]) (bvar 0)) (lit 1))
  BinderInfo.default
```

注意 body 中用 `bvar 0` 指代最近的绑定变量 `n`——这是 de Bruijn 索引。

## 例 3：`∀ n : Nat, n = n`
%%%
tag := "example-forall"
%%%

```
forallE `n (const `Nat [])
  (app (app (app (const `Eq [...]) (const `Nat [])) (bvar 0)) (bvar 0))
  BinderInfo.default
```

`∀` 和 `→` 都用 `forallE`；如果 body 不引用绑定变量（即 `bvar 0` 不出现），那就是 `→`。

# 模式匹配 Expr：`match_expr` 和 `let_expr`
%%%
tag := "pattern-matching-expr"
%%%

手动 match {moduleTerm}`@Expr` 构造子非常繁琐（要处理 `app (app (const ...) ...) ...`）。Lean 提供了两个语法糖：

> *注意*：`match_expr` 和 `let_expr` 是专门的模式匹配语法糖，不是普通函数名。你不能对它们用 `#check`（不像 {moduleTerm}`forallTelescope` 那样是一个可查类型的函数）。它们的作用是按 *head constant* 匹配表达式（如 `Eq`、`And`、`Or`），自动拆开嵌套的 `app`。对于 `forallE` 这类 binder 构造子，应该用普通的 `Expr.isForall` 或直接 `match`。

## `match_expr`
%%%
tag := "match-expr"
%%%

```
match_expr goalType with
| Eq α lhs rhs =>
  -- goalType 是 @Eq α lhs rhs
  logInfo m!"This is an equality: {← ppExpr lhs} = {← ppExpr rhs}"
| And p q =>
  -- goalType 是 And p q
  logInfo m!"This is a conjunction"
| _ =>
  logInfo m!"Unknown shape"
```

`match_expr` 按 head constant 匹配：`Eq α lhs rhs` 匹配 `@Eq α lhs rhs`，自动解开所有 `app`。

## `let_expr`
%%%
tag := "let-expr"
%%%

用于 `do` 块中的 pattern matching（类似 `let some x := ... | return`）：

```
let_expr Eq α lhs rhs := goalType | throwError "not an equality"
-- 到这里 lhs, rhs 就是绑定好的 Expr
```

`let_expr` 在 tactic 代码中用得更多，因为失败时可以直接跳出。

# 构造 Expr
%%%
tag := "constructing-expr"
%%%

读取 {moduleTerm}`@Expr` 用模式匹配，构造 {moduleTerm}`@Expr` 用 {moduleTerm}`mkApp` 系列函数：

## 手动构造
%%%
tag := "manual-construction"
%%%

```
-- 构造 @Eq Nat a b
let eqExpr := mkApp3 (mkConst ``Eq) (mkConst ``Nat) a b

-- 构造 @Eq.refl Nat a  (即 rfl 的证明项)
let rflExpr := mkApp2 (mkConst ``Eq.refl) (mkConst ``Nat) a
```

常用构造函数：

- `mkConst n`：常量引用
- `mkApp f a`：单参数应用
- `mkApp2/3/4/5/6`：多参数应用
- `mkAppN f #[a,b,c]`：数组参数应用
- `mkLambda n bi t body`：构造 λ 表达式
- `mkForall n bi t body`：构造 ∀ 表达式

## 用引号构造（quotation）
%%%
tag := "quotation-construction"
%%%

在 {moduleTerm}`@TermElabM` / {moduleTerm}`@TacticM` 中，可以用 quotation + `elabTerm` 从语法直接构造：

```
let e ← elabTerm (← `(Nat.add 2 3)) none
-- e 是精化后的 Expr
```

这更方便，但有额外开销（要走一遍 elaboration）。在性能敏感的 tactic 中，手动 {moduleTerm}`mkApp` 更好。

# de Bruijn 索引 vs 自由变量
%%%
tag := "debruijn-vs-fvar"
%%%

{moduleTerm}`@Expr` 中有两种变量：

- *`bvar n`*（bound variable）：de Bruijn 索引，表示"向外数第 n 个 λ/∀ 绑定者"。索引 0 = 最近的绑定。
- *`fvar id`*（free variable）：局部上下文中的变量，用唯一 ID 标识。

在元程序中，我们通常借助 {moduleTerm}`forallTelescope`、{moduleTerm}`lambdaTelescope` 等 API 打开绑定结构；这些 API 会把 body 中对应的 `bvar` 替换成当前局部上下文里的 `fvar`，因此日常 tactic 代码里更常直接操作 `fvar`。关键 API：

```
-- 进入 ∀ 类型，把绑定变量转为 fvar
forallTelescope goalType fun fvars body => do
  -- fvars : Array Expr  （每个都是 fvar）
  -- body  : Expr        （bvar 已被替换为 fvar）
  ...

-- 进入 λ 表达式
lambdaTelescope e fun fvars body => do
  ...
```

{moduleTerm}`forallTelescope` 和 {moduleTerm}`lambdaTelescope` 是处理绑定结构的标准方式。它们：
1. 创建新的 `fvar` 加入局部上下文
2. 把 body 中的 `bvar` 替换为对应 `fvar`
3. 回调结束后自动清理

*注意*：`fvar` 只在创建它的 {moduleTerm}`@LocalContext` 中有效。不要把一个 telescope 回调里的 `fvar` 泄漏到外面。

# 实用工具函数
%%%
tag := "expr-utility-functions"
%%%

{moduleTerm}`@MetaM` 提供了大量操作 {moduleTerm}`@Expr` 的工具：

## 类型相关
%%%
tag := "type-related-utils"
%%%

```
inferType (e : Expr) : MetaM Expr         -- 推断 e 的类型
isDefEq (a b : Expr) : MetaM Bool          -- a 和 b 定义等价？（可能触发 unification）
whnf (e : Expr) : MetaM Expr               -- 弱头范式
isProof (e : Expr) : MetaM Bool            -- e 是证明项？
isProp (e : Expr) : MetaM Bool             -- e 的类型是 Prop？
```

## 结构分析
%%%
tag := "structural-analysis-utils"
%%%

```
Expr.getAppFn (e : Expr) : Expr            -- 获取应用头（剥掉所有 app）
Expr.getAppArgs (e : Expr) : Array Expr    -- 获取所有参数
Expr.isApp (e : Expr) : Bool               -- 是 app？
Expr.isConst (e : Expr) : Bool             -- 是 const？
Expr.constName (e : Expr) : Name           -- const 的名字（前提：isConst）
```

## 替换与遍历
%%%
tag := "substitution-traversal"
%%%

```
kabstract (e : Expr) (t : Expr) : MetaM Expr  -- 把 e 中匹配 t 的子项抽象为 bvar（支持 occurrences 控制）
replace (e : Expr) (f : Expr → Option Expr) : Expr  -- 自定义替换
Expr.foldlM (init : α) (f : α → Expr → MetaM α) (e : Expr) : MetaM α  -- 遍历
```

# 小结
%%%
tag := "ch02-summary"
%%%

- {moduleTerm}`@Expr`：Lean 中一切项的内部表示，树形结构
- `app`：函数应用，多参数 = 嵌套 app（curried）
- `bvar` / `fvar`：绑定变量 vs 自由变量；元程序中用 `fvar`
- `match_expr` / `let_expr`：按 head constant 模式匹配，避免手动解 app
- `mkApp*`：手动构造表达式；性能敏感时优于 `elabTerm`
- {moduleTerm}`forallTelescope`：进入 ∀ 类型的标准方式

# 常见失败模式与 debug
%%%
tag := "ch02-common-failures"
%%%

## 失败 1：`match_expr` 匹配不上，明明目标看起来是对的
%%%
tag := "failure-match-expr-whnf"
%%%

`match_expr` 按 head constant 匹配，但 {moduleTerm}`whnf` 没有自动调用。如果目标被 `let` 或 `abbrev` 包了一层，需要先 {moduleTerm}`whnf`：

```
-- [示意]
let target ← whnf (← goal.getType)  -- 先规约
match_expr target with
| Eq α lhs rhs => ...
| _ => throwError "not an equality"
```

## 失败 2：`Expr.constName` panic
%%%
tag := "failure-constname-panic"
%%%

`constName` 在表达式不是 `const` 时会 panic。安全做法是先检查：

```
-- [示意]
if e.isConst then
  let name := e.constName
  ...
```

或用 `Expr.constName?` 返回 `Option Name`。

## 失败 3：`fvar` 泄漏出 telescope 回调
%%%
tag := "failure-fvar-leak"
%%%

{moduleTerm}`forallTelescope` 里创建的 `fvar` 只在回调内有效。如果你把它存到外面的变量里再使用，会得到 `unknown free variable` 错误。

```
-- [示意] 错误做法
let mut leaked : Expr := default
forallTelescope goalType fun fvars body => do
  leaked := fvars[0]!  -- ❌ fvar 会在回调结束后失效
-- 在这里用 leaked 会出错
```

正确做法：把需要的结果在回调内计算完，只返回不含 `fvar` 的值。

## 失败 4：手动 `mkApp` 参数个数错
%%%
tag := "failure-mkapp-arity"
%%%

`mkApp3 (mkConst Eq) a b` 会构造出类型错误的表达式（`Eq` 需要 3 个参数：类型 α、lhs、rhs）。这类错误不会立即 panic，而是在后续 {moduleTerm}`isDefEq` 或 `check` 时才报 type mismatch。

*建议*：用 `mkEq`、`mkEqRefl` 等高层 API，而不是手动数参数。

# 练习
%%%
tag := "ch02-exercises"
%%%

## 练习 2.1（热身）：用 `#check @Eq` 观察 Expr 结构
%%%
tag := "exercise-2-1"
%%%

在 VS Code 中运行：

```
import Lean
open Lean
```

```anchor check_eq_types
#check @Eq         -- Eq : α → α → Prop
#check @And        -- And : Prop → Prop → Prop
#check @Eq.refl    -- Eq.refl : ∀ {α} (a : α), a = a
```

观察每个常量需要几个参数。这能帮你理解为什么 `match_expr` 写 `Eq α lhs rhs`（3 个参数）而 `And p q`（2 个参数）。

## 练习 2.2（热身）：打印目标的 head constant
%%%
tag := "exercise-2-2"
%%%

写一个 tactic，打印当前目标的 head constant 名字：

```
import Lean
open Lean Elab Tactic Meta
```

```anchor show_head
elab "show_head" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.getType
    let head := target.getAppFn
    if head.isConst then
      logInfo m!"Head constant: {head.constName}"
    else
      logInfo m!"Head is not a constant: {← ppExpr head}"

example (n : Nat) : n + 0 = n := by
  show_head   -- 应输出: Head constant: Eq
  simp
```

> 和 Ch1 的 `trace_goal` 一样，这类只打印信息不改变目标的 tactic 可能触发 "tactic does nothing" 警告，可以忽略。

## 练习 2.3（debug）：找出 `match_expr` 失败的原因
%%%
tag := "exercise-2-3"
%%%

以下 tactic 想匹配 `∀ x, P x` 形式的目标，但总是走到 `_` 分支。为什么？

```
-- 这段代码有逻辑错误
import Lean
open Lean Elab Tactic Meta

elab "check_forall" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.getType
    match_expr target with
    | ForAll _ _ => logInfo "Found a forall!"
    | _ => logInfo "Not a forall"

example : ∀ n : Nat, n = n := by
  check_forall   -- 为什么输出 "Not a forall"？
  intro n; rfl
```

提示：`match_expr` 匹配的是 head *constant*（如 `Eq`、`And`），而 `∀` 不是一个常量——它是 `Expr.forallE` 构造子。要检查 `∀`，应该用普通的 `Expr.isForall` 或直接 `match` 构造子。

## 练习 2.4（综合）：实现 `show_structure` tactic
%%%
tag := "exercise-2-4"
%%%

写一个 `show_structure` tactic，对当前目标做以下分类并打印：

- 如果是等式 `a = b`：打印 `"Equality: {a} = {b}"`
- 如果是合取 `P ∧ Q`：打印 `"Conjunction: {P} ∧ {Q}"`
- 如果是 `∀` 类型：打印 `"Forall"` 和绑定变量的类型
- 否则：打印 `"Other: {target}"`

测试用例：

```
-- [可运行] 实现 show_structure 后测试
example : 1 + 1 = 2 := by show_structure; norm_num
example : True ∧ True := by show_structure; exact ⟨trivial, trivial⟩
example : ∀ n : Nat, n = n := by show_structure; intro n; rfl
example : True := by show_structure; trivial
```

下一章：用 {moduleTerm}`@Expr` 和 {moduleTerm}`@TacticM` 写出你的第一个有用的 tactic。
