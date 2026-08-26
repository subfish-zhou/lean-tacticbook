import VersoManual
import LeanTacticBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "examples"
set_option verso.exampleModule "Examples.Ch09Ring"

#doc (Manual) "ring：带证明的多项式规范化" =>
%%%
file := "Ch09Ring"
tag := "ch09-ring"
%%%

> *本章目标*：解释两个长得不同的多项式为什么能被机械地判定为相等。我们先手算一种统一写法，再实现一个只含变量、常数、加法和乘法的小语言；读者理解这个模型后，才把它对应到 Mathlib 的生产表示。
>
> *版本基准*：Lean `leanprover/lean4:v4.32.2`；Mathlib revision `905b95818eb32af7874a58b427f50c1711a5e96c`。

`(x + y)^2` 与 `x^2 + 2*x*y + y^2` 不是同一棵表达式树，所以 `rfl` 不能关闭它们的等式。人工证明会反复使用分配律、交换律和结合律。`ring` 把这些步骤组织成一种固定算法：把左右两边都改写成统一形式，再比较结果。

这里的关键不是“算出一样”这一件事。Lean 还要求每次改写都带着证明，最终才能交给内核检查。

# 平方展开到底证明了什么
%%%
tag := "ch09-s01"
%%%

```anchor ring_identity
theorem ringIdentity (x y : ℤ) :
    (x + y)^2 = x^2 + 2*x*y + y^2 := by
  ring
```

用户只写一行 `ring`。内部不是把等式算成一个 Bool 再要求内核相信，而是构造普通证明项。先把算法的共同目标叫作 normal form（规范形）：每个多项式都有一种约定好的标准写法。粗略说，`ring` 得到：

:::codeBox "pseudocode"
```
leftProof  : (x + y)^2 = x^2 + 2*x*y + y^2
rightProof : (x^2 + 2*x*y + y^2) = x^2 + 2*x*y + y^2

finalProof := leftProof.trans rightProof.symm
```
:::

实际 normal form 的括号、系数表示和幂结构更精细，但可信性主线就是这两条带证明的计算结果。

# 三个入口各做什么
%%%
tag := "ch09-s03"
%%%

```table
- 名称
- 职责
- 成功后的目标
---
- `ring1`
- 对一个等式调用核心证明过程
- 规范形相同则关闭；不同则失败
---
- `ring_nf`
- 递归改写目标或指定假设中的 ring 表达式
- 保留规范化后的 residual goal，可能顺手关闭
---
- `ring`
- 先试 `ring1`；关闭不了时运行 `ring_nf` 并给诊断
- 可能关闭，也可能成功返回一个规范化 residual
```

用户常把 tactic 的“返回成功”和“目标已关闭”混为一谈。`ring` 在无法关掉等式时会调用 `ring_nf`；这个分支可以正常返回，同时把更清楚的 residual 留给后续 tactic。

# `ring_nf` 会改写现场
%%%
tag := "ch09-s04"
%%%

```anchor ring_nf_hypothesis
theorem ringNfHypothesis (x y : ℤ) (h : (x + y)^2 = 0) :
    x^2 + 2*x*y + y^2 = 0 := by
  ring_nf at h ⊢
  exact h
```

`ring_nf at h ⊢` 同时规范化假设与目标。两者最终变成相同的多项式等式，随后 `exact h` 关闭目标。

```anchor ring_normalized_residual
example (x y : ℤ) : x * (y + 1) = x*y + x := by
  ring_nf
```

这个例子在规范化后直接关闭。若你只想判断原等式是否为恒等式，用 `ring`；若你还想把规范形交给后续 tactic，用 `ring_nf`。

# 先手算什么叫“同一种写法”
%%%
tag := "ch09-s07"
%%%

先暂时把 `x`、`y`、`z` 当作不可再拆的符号，并约定顺序 `x < y < z`。这种在多项式算法里作为整体处理的符号稍后叫作 atom（原子）。表达式

:::codeBox "pseudocode"
```
(y + x) * (x + 2)
```
:::

展开后按单项式排序，可写成：

:::codeBox "pseudocode"
```
x^2 + x*y + 2*x + 2*y
```
:::

规范形至少要固定三件事：

1. 每个单项式内部按 atom 次序排列；
2. 相同 atom 的幂合并；
3. 单项式之间按确定次序排列并合并同类项。

如果只展开而不排序，`x*y` 与 `y*x` 仍长得不同；如果只排序而不合并，`x+x` 与 `2*x` 仍长得不同。规范化不是“多做几次 simp”，而是针对一种专用语言设计的决定过程。

# 用一个小语言固定算法契约
%%%
tag := "ch09-s15"
%%%

下面的小语言只有一个变量、整数常数、加法和乘法。`ToyExpr` 是这门小语言的语法树；`eval` 规定每棵树代表哪个整数函数；`toPoly` 把树转换成 Mathlib 已有的整数多项式。定理 `eval_toPoly` 证明转换前后的求值相同。

```anchor ring_toy_normalizer
inductive ToyExpr where
  | var
  | const (z : ℤ)
  | add (lhs rhs : ToyExpr)
  | mul (lhs rhs : ToyExpr)

def ToyExpr.eval : ToyExpr → ℤ → ℤ
  | .var, x => x
  | .const z, _ => z
  | .add lhs rhs, x => lhs.eval x + rhs.eval x
  | .mul lhs rhs, x => lhs.eval x * rhs.eval x

noncomputable def ToyExpr.toPoly : ToyExpr → Polynomial ℤ
  | .var => Polynomial.X
  | .const z => Polynomial.C z
  | .add lhs rhs => lhs.toPoly + rhs.toPoly
  | .mul lhs rhs => lhs.toPoly * rhs.toPoly

theorem ToyExpr.eval_toPoly (e : ToyExpr) (x : ℤ) :
    e.toPoly.eval x = e.eval x := by
  induction e <;> simp_all [ToyExpr.toPoly, ToyExpr.eval]
```

这个模型先建立一条最重要的契约：转换后的数据可以用于计算，但必须另有定理说明转换保存语义。它与生产实现的差别有三点：

1. 直接复用 Mathlib `Polynomial ℤ`，没有自行设计生产实现的三层内部表示；这些实现名到生产管线一节才引入；
2. 正确性是对整个语法树归纳证明，不是每次 Meta 运算返回 Result proof；
3. 它处理自定义 AST，不从任意 Lean Expr 中识别 atoms 和结构实例。

这段代码给出算法契约，生产 `ring` 则把同一想法搬到 open-world Expr 和 typeclass 环境中。

# 把小模型搬到任意 Lean `Expr`
%%%
tag := "ch09-s02"
%%%

:::codeBox "pseudocode"
```
Lean equality goal
→ 识别左右两边所在的代数结构
→ 把能识别的加、乘、幂翻进专用多项式语言
→ 把不能继续解析的子项登记成 atoms
→ 规范化加、乘、负号、幂与 coefficients
→ 比较两边规范形结构
→ 拼接原式 = 规范形的 proofs
→ 给原目标赋值
→ kernel 检查 proof Expr
```
:::

把一般 Lean `Expr` 翻成一门专用内部语言，叫作 reification（重化）。Toy 例子中的 `toPoly` 已经做了同类工作，只是输入不是任意 `Expr`。重化和“译补”不是同一步：项译补器先把用户 Syntax 变成 Expr，`ring` 再从 Expr 中识别加法、乘法和幂。

# 认不出的子项怎样成为 atom
%%%
tag := "ch09-s05"
%%%

核心语言包含数值 coefficient（系数）、加法、乘法、自然数幂，以及在相应交换代数结构中可解释的负号和减法。遇到不属于这门语言、却有合适类型的完整子表达式时，算法把它登记成一个 atom。atom 的含义是“内部不再分析，但每次出现都当作同一个变量”。

遇到看不懂的子表达式，`ring` 通常不立刻失败，而是把整个子项登记为一个 atom。比如 `f x` 没有多项式定义，它仍可作为变量参与外层恒等式：

```anchor ring_unknown_atoms
theorem ringUnknownAtoms (f : ℤ → ℤ) (x : ℤ) :
    (f x + 1)^2 = (f x)^2 + 2 * f x + 1 := by
  ring
```

这解释了 `ring` 的一个强项：它不需要知道 `f` 是什么，只需保证所有出现的 `f x` 被一致地认作同一个 atom。

## atom 相同依赖定义等价
%%%
tag := "ch09-s06"
%%%

Atom map 比较表达式时会受 transparency 影响。普通 `ring` 不会任意展开所有定义；`ring!` 使用更激进的透明度。两项在当前透明度下定义等价，才会共享 atom 编号。这里依赖 Ch05 的 `isDefEq` 边界：成功比较可能给 mctx 赋值，因此候选式 atom 匹配仍要遵守 Meta 状态纪律。

# 生产表示：Base、Prod、Sum
%%%
tag := "ch09-s08"
%%%

Mathlib 的核心表示分三层。锁定版本使用下面的 `ExBase / ExProd / ExSum` 稀疏和式表示，不是另一种常见教材里的 Horner 规范形；不要用对其它 `ring` 实现的印象替换这里的源码结构：

:::codeBox "pseudocode"
```
ExBase
  atom | 嵌套的 sum

ExProd
  const coefficient | base ^ exponent × remaining product

ExSum
  zero | product + remaining sum
```
:::

具体类型位于 `Mathlib/Tactic/Ring/Common.lean`。它们不只是裸数据；规范化函数返回的 `Result` 同时保存原始 Expr、规范形和证明。Addition、multiplication 与 power 运算都接收旧 Result，返回新 Result，并构造保持语义的等式证明。

# Proof-carrying Result
%%%
tag := "ch09-s09"
%%%

把内部契约缩成伪代码：

:::codeBox "pseudocode"
```
Result e 表示：
  normal : NormalForm
  proof  : e = denote normal

add (r₁ : Result e₁) (r₂ : Result e₂) : Result (e₁ + e₂)
mul (r₁ : Result e₁) (r₂ : Result e₂) : Result (e₁ * e₂)
pow (r : Result e) (n : Nat) : Result (e ^ n)
```
:::

`add` 的元层代码可以算错排序；若它配套构造的 proof 不能证明新等式，内核会拒绝最终项。反过来，算法也可能算对规范形却拼错 proof，这同样只是 tactic 失败，不会把错误等式变成定理。

# 加法与乘法为什么最费工
%%%
tag := "ch09-s10"
%%%

加法要归并两个有序 product 列表。头部单项式次序不同时，取较小者；相同时相加 coefficients，为零则删掉。乘法要做分配律，把每对 products 相乘，再将结果插回有序 sum。

:::codeBox "pseudocode"
```
addSum [] ys = ys
addSum xs [] = xs
addSum (x::xs) (y::ys):
  if x < y: x :: addSum xs (y::ys)
  if y < x: y :: addSum (x::xs) ys
  if x = y: combine coefficients, then continue

mulSum xs ys:
  normalize and merge every x*y
```
:::

元层实现追求共享与效率，证明层则反复应用交换律、结合律、分配律和 coefficient 正确性引理。正因为每个运算都带 proof，生产代码不会先算完一个巨大语法树，再从零猜一条证明。

# Coefficients 与 `norm_num`
%%%
tag := "ch09-s11"
%%%

常数不只包括自然数字面量。在环和域样结构中，负数、有理数及 casts 都需要规范解释。Ring normalizer 把 coefficient 算术交给 `norm_num` 支持，得到数值结果及其证明。

要区分两种失败：

- coefficient 算术无法在当前结构中解释；
- 整个表达式含有不属于 ring 语言的运算。

后一类可能退成 atom，前一类往往在解析或证明构造处失败。

# 除法不是一般 ring 运算
%%%
tag := "ch09-s12"
%%%

```anchor ring_division_boundary
example (x : ℚ) (hx : x ≠ 0) : x / x = 1 := by
  ring
  field_simp
```

生产实现先把除法证明性地改写成乘逆元，再分别规范化分子、分母与逆元。数值逆元可以继续化简；变量逆元通常登记为 atom。它不会在没有非零证明时把 `x * x⁻¹` 约成 1。这个例子先由 `ring` 留下规范化 residual，再由 `field_simp` 使用 `hx : x ≠ 0` 清除分母。

特别要警惕 `0 / 0`。结构化重化除法不等于无条件约分；任何声称“把分子分母同乘即可”的规范化都会在零分母处出错。

# Typed quotation 插页
%%%
tag := "ch09-s13"
%%%

Ring 源码大量使用 Qq。普通 quotation `` `(term| ...) `` 产生 Syntax；Qq 的 typed quotation 直接在 Meta 程序中构造带类型索引的 Expr 表示。

:::codeBox "code"
```
Q(α)          -- quoted Expr 的类型
q($x + $y)    -- 构造 quoted Expr 的值，并 splice 已有值
q($lhs = $rhs)
```
:::

类型索引帮助宿主 Lean 在编译 tactic 源码时排除一部分拼接错误。它不替代目标 Lean 程序的内核检查，也不意味着 quoted Expr 自动证明任何命题。

# 两边如何闭合
%%%
tag := "ch09-s14"
%%%

`proveEq` 对等式两边分别求 Result。若 normal-form structures 相等，设左证据为 `hL : lhs = nf`，右证据为 `hR : rhs = nf`，最终证明就是：

:::codeBox "code"
```
hL.trans hR.symm
```
:::

如果结构比较不相等，`ring1` 失败。用户层 `ring` 随后调用 `ring_nf`，把两边各自改写为规范形，于是你看到的是一个更诚实的 residual，而不是一句没有信息的“证明失败”。

# 可信性与公理锥
%%%
tag := "ch09-s16"
%%%

```anchor ring_axiom_probe
#print axioms ringIdentity
#print axioms ringUnknownAtoms
```

锁定版本的输出为：

:::codeBox "code"
```
ringIdentity depends on axioms: [propext]
ringUnknownAtoms depends on axioms: [propext]
```
:::

这是具体 theorem 在当前环境中的公理锥，不应外推成“所有 ring 证明永远只依赖 propext”。能从这里得到的信任结论更窄：`ring` 的元层规范化结果不作为公理加入；它必须构造由内核检查的普通 proof Expr。

```table
- 部件
- 可信性角色
---
- atom 编号、排序、normal-form 比较
- 不可信元层计算；错误会漏解或生成不可检 proof
---
- coefficient 计算
- 由 `norm_num` 产生配套证明
---
- Result operations
- 构造原式等于规范形的 proof Expr
---
- kernel
- 检查最终等式证明
```

# 源码纵切
%%%
tag := "ch09-s17"
%%%

按下面次序读：

:::codeBox "pseudocode"
```
Mathlib/Tactic/Ring/RingNF.lean
  `ring` 宏、`ring_nf` 译补器、位置与递归改写

Mathlib/Tactic/Ring/Basic.lean
  ring1、proveEq、两边规范化、闭合

Mathlib/Tactic/Ring/Common.lean
  ExBase / ExProd / ExSum / Result
  expression evaluator 与带证明的代数运算

Mathlib/Tactic/Ring/PNat.lean
  需要变量指数时再读
```
:::

沿 `x * (y + 1)` 只追一条纵线：识别 `x`、`y` 为 atoms；构造 `y+1` 的 sum Result；做乘法分配；排序出 `x*y+x`；与右边 normal form 比较；拼 proof。第一遍不要同时读 casts、scalar multiplication 和 variable exponents。

# 失败边界
%%%
tag := "ch09-s18"
%%%

```table
- 现象
- 原因或下一步
---
- `ring` 留下 residual
- 两边规范形不同；查看 `ring_nf` 输出
---
- 含一般除法
- 需要非零条件与 `field_simp`，或把子项当 atom
---
- 非交换乘法
- `ring` 的语义不适用；考虑 `noncomm_ring`
---
- 只有加法交换群结构
- 考虑 `abel`
---
- 定义包装阻止 atom 对齐
- 比较 `ring` 与 `ring!` 的 transparency
---
- 表达式爆炸
- 检查展开、幂和 atom 数；不要先手工 `simp` 到更大
```

# 练习
%%%
tag := "ch09-s19"
%%%

## 基础一：手算规范形
%%%
tag := "ch09-s20"
%%%

固定 `x < y`，手算 `(y+x)*(x+2)` 的有序单项式列表，并指出每次合并用到的环律。

## 基础二：atoms
%%%
tag := "ch09-s21"
%%%

证明 `(f x + g y)^2 = (f x)^2 + 2*f x*g y + (g y)^2`，再把第二个 `g y` 改成定义等价但表面不同的表达式，比较 `ring` 与 `ring!`。

## 进阶一：损坏 normalizer
%%%
tag := "ch09-s22"
%%%

修改 toy `toPoly`，故意把乘法写成加法。`eval_toPoly` 应停止编译。解释这与“生产 normalizer 算错但内核仍安全”的对应关系。

## 进阶二：Result 风格
%%%
tag := "ch09-s23"
%%%

不再用一次性归纳 theorem；为 toy 语言定义 `Result e`，分别实现 const、var、add、mul，每个函数返回 polynomial 与 `eval` 等式证明。

## 挑战：从 Expr 识别一元语言
%%%
tag := "ch09-s24"
%%%

写一个 Meta 程序，只识别整数上的一个 atom、加法与乘法；其他子项整体登记为新 atom。要求输出重化结果和 atom 表，不必生成 proof。然后写清楚：没有 proof 的版本为什么只能做诊断，不能给目标赋值。

# 本章边界
%%%
tag := "ch09-s25"
%%%

`ring` 展示了带证明的确定性计算。下一章 `linarith` 不再由规范形唯一决定答案：它要从多条不等式中搜索一组系数。搜索器可以不可信，但找到的 coefficients 必须被 Lean 端重建成矛盾证明；其中“线性组合等于零”正由本章的 `ring1` 负责。
