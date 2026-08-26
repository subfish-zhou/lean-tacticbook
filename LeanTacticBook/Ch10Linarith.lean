import VersoManual
import LeanTacticBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "examples"
set_option verso.exampleModule "Examples.Ch10Linarith"

#doc (Manual) "linarith：寻找线性矛盾证书，并重建证明" =>
%%%
file := "Ch10Linarith"
tag := "ch10-linarith"
%%%

> *本章目标*：从“把两条不等式相加得到矛盾”开始。先由人写出乘数，再让程序搜索这些乘数；最后检查搜索结果怎样被重新组成普通 Lean 证明。`nlinarith` 只作为末尾扩展。
>
> *版本基准*：Lean `leanprover/lean4:v4.32.2`；Mathlib revision `905b95818eb32af7874a58b427f50c1711a5e96c`。

若已知 `x ≤ 3` 和 `5 ≤ x`，把两式移到左边并相加，就得到 `2 ≤ 0`。矛盾并不来自某条神秘定理，而来自“选哪些不等式、各乘多少、怎样相加”。`linarith` 自动寻找这组乘数，再让 Lean 检查相加过程。

# 从反对称性开始
%%%
tag := "ch10-s01"
%%%

```anchor linarith_basic
theorem antisymmByLinarith (x y : ℚ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  linarith
```

这里可直接用反对称性定理，但 `linarith` 采用统一策略：暂时假设目标不成立，再尝试从这个假设与已有比较式中推出矛盾。这个例子只含一次式，没有乘积或平方。

# `linear_combination`：由人写出系数
%%%
tag := "ch10-s02-linear-combination"
%%%

linear combination（线性组合）是把若干等式或不等式分别乘上常数，再把结果相加。`linear_combination` 让用户亲自指定这些乘数，证明术负责重建代数证明。下面两式各乘 `1` 后相加，`y` 消去，得到目标 `2*x = 6`。

```anchor linarith_linear_combination
theorem explicitLinearCombination (x y : ℚ)
    (h₁ : x + y = 5) (h₂ : x - y = 1) : 2*x = 6 := by
  linear_combination h₁ + h₂
```

这里没有自动程序猜乘数，也没有从不等式系统中找矛盾。它适合乘数已经清楚、希望直接写进脚本的证明。`linarith` 则先自动寻找一组乘数，再按这些乘数重建证明；本章后面才给“搜索程序、乘数记录、重建步骤”分别命名。二者都要生成普通 Lean proof，自动化的位置不同。

# 把“选哪些倍数”写成证书
%%%
tag := "ch10-s02"
%%%

程序搜索时，不需要返回一整段 Lean 代码。它只返回“第几条事实乘多少”的表。这张可由另一段程序检查的小答案叫 certificate（证书）。在本章中，乘数都是非负自然数；乘负数会翻转不等号方向，因此不允许直接放进证书。

```anchor linarith_strict_certificate
theorem strictContradiction (x y : ℚ) (h₁ : x < y) (h₂ : y ≤ x) : False := by
  linarith only [h₁, h₂]
```

`x < y` 写成 `x-y < 0`，`y ≤ x` 写成 `y-x ≤ 0`。两项各乘 `1` 后，左边代数和为零；因为第一项是严格不等式，相加又告诉我们这个零严格小于零。证书可读成“事实一乘 1，事实二乘 1”。

```anchor linarith_manual_reading
theorem weightedContradiction (x : ℚ) (h₁ : x ≤ 3) (h₂ : 5 ≤ x) : False := by
  linarith only [h₁, h₂]
```

这里两条事实写成 `x-3 ≤ 0` 与 `5-x ≤ 0`，相加得到 `2 ≤ 0`，已经矛盾。生产 verifier 为了把各种矛盾统一成“同一个代数式既等于零又严格小于零”，会额外放入一条永远成立的事实 `-1 < 0`。锁定 trace 给出的 certificate 是 `(0,2), (1,1), (2,1)`，也就是额外事实乘 `2`，两条用户事实各乘 `1`：

:::codeBox "pseudocode"
```
2 * (-1) + (x - 3) + (5 - x) = 0
2 * (-1) + (x - 3) + (5 - x) < 0
```
:::

其中编号 `0` 不是用户假设，而是系统加入的 `-1 < 0`。生产代码还会重排预处理结果，并为等式补上取负版本，所以原始 certificate index（证书编号）指向内部数组位置，不是稳定的用户假设编号。第一遍不需要记重排公式；需要记住的是：数字表本身不是证明，后端必须按实际数组重新构造每一步。

# 完整管线
%%%
tag := "ch10-s03"
%%%

:::codeBox "pseudocode"
```
目标取反 / equality 分支
→ preprocessors
→ 全部写成 t R 0
→ parse 成 monomial ↦ coefficient map
→ 加入 synthetic -1<0，并为等式补取负版本
→ oracle 搜索非负 coefficients
→ 数乘并相加这些 comparison proofs
→ ring1 证明完整代数线性组合归零
→ False
```
:::

坏 certificate 会在空证书检查、strictness bookkeeping、`ring1` 代数检查、类型检查或 kernel 检查处失败。

# 前处理决定问题的真实形状
%%%
tag := "ch10-s04"
%%%

默认 preprocessors 拆 conjunction，过滤非比较式，将 `NNReal` 移到 `Real`，将 Nat 提升到 Int，补 Nat 非负事实，强化整数严格不等式，改写为与零比较，消去数值分母，并按载体类型分组。拆 conjunction 会从一个输入产生同一分支内的多个 facts，不会生成多个目标分支。真正会分支的是 `splitNe` 等可选预处理器；默认配置不启用它们。接口因此也不只是简单的 `Expr → Expr`。

这里还要分清两个“负”：`addNegEqProofs` 为等式 `t = 0` 补的是 additive negation `-t = 0`，不是处理 disequality `t ≠ 0`。默认 `filterComparisons` 会丢弃 disequality；启用 `splitNe := true` 才把它拆成有序情形，并可能造成指数分支。

```anchor linarith_integer_strict
example (x y : ℤ) (h : x < y) : x + 1 ≤ y := by
  linarith
```

整数上的 `x < y` 可加强为 `x+1 ≤ y`；稠密有序域上不能这样做。前处理必须根据载体生成合法 proof。

# Parser 的多项式不是 Ring 的规范形
%%%
tag := "ch10-s05"
%%%

Parsing 把线性式表示成 monomial 到 coefficient 的有限映射：

:::codeBox "pseudocode"
```
2*x - 3*y + 5
→ x ↦ 2, y ↦ -3, constant ↦ 5
```
:::

Parser 会递归规范化一般多项式乘法，并把每个不同 monomial 当成 oracle 眼中的独立线性变量。于是 `linarith` 能利用两处相同的 `x*y` 做线性抵消，却不知道这个 monomial 与 `x`、`y` 之间的乘法关系；后者需要 `nlinarith` 额外生成有限推论。Linarith 使用自己的 polynomial-map 表示，并不直接复用 Ch09 `Ring.Common` 的 `ExSum`。两章的直接连接在 verification：默认 discharger 用 `ring1` 证明加权和归零。

下面的目标只要求把同一个 monomial `x*y` 当成原子抵消；它不需要推导任何乘法性质：

```anchor linarith_monomial_as_atom
theorem monomialCancellation (x y : ℚ) (h₁ : x*y ≤ 0) (h₂ : 1 ≤ x*y) : False := by
  linarith
```

# Oracle 只负责寻找乘数
%%%
tag := "ch10-s06"
%%%

:::codeBox "pseudocode"
```
input  : Array Comparison
output : Option (Array Nat)
```
:::

Mathlib 把“只读线性比较式、尝试找出乘数”的可替换搜索程序叫作 oracle。这里的词没有神谕或公理含义。锁定实现中的 simplex 和 Fourier–Motzkin 都是 Lean 进程内的程序，不是像 Ch12 CaDiCaL 那样的外部进程；“不受信任”只表示其答案必须经 proof reconstruction 检查。

一种搜索法是 Fourier–Motzkin elimination（傅里叶－莫茨金消元）：把某变量系数一正一负的两式组合，逐步消去变量，并同时记录每条新式来自哪些旧式。它直观，但中间式可能迅速增多。锁定版本默认使用 sparse simplex（稀疏单纯形法）；tableau、basic variable 和 pivot 等数据结构属于算法实现，第一次阅读只需知道它仍然只返回一组候选乘数。

把三个问题分开：

```table
- 问题
- 锁定实现中的答案
---
- Oracle 在哪里运行？
- Lean 进程内；不是外部 executable
---
- Oracle 是否属于逻辑可信基？
- 不属于；它只给乘数，答案必须重建成 proof
---
- Oracle 失败能否证明证书不存在？
- 不能；只说明本次搜索没有交出可验证证书
```

Oracle 可以超时、因资源限制漏掉解，或返回坏 coefficients。只要 verification 拒绝坏证书，这些仍是性能或完备性故障，不是直接的逻辑后门。不要把“进程内但不受信”误写成“外部求解器”，也不要把一次失败改写成“这种非负线性组合不存在”。

# 搜索结果必须重新组成 Lean 证明
%%%
tag := "ch10-s07"
%%%

verification（验证）阶段按证书中的 coefficient（系数）对原比较式证明取非负整数倍，再逐项相加。它同时记录当前关系是 `<` 还是 `≤`，检查至少一个严格项真的以正系数参与，并调用 `ring1` 检查整个代数和确实为零；最后从“零严格小于零”推出 `False`。

Linarith 源码明确没有用 reflection 检查 certificate；它按数据重建 proof。Certificate 的 coefficient 类型本来就是 `Nat`，负数无法表示。更真实的损坏方式是返回空表、把某个正 coefficient 改错而使加权和不再为零，或把所有严格项的 coefficient 置零；重建必须拒绝这些结果。

# Trace 逐层显示数据
%%%
tag := "ch10-s08"
%%%

```anchor linarith_trace
set_option trace.linarith true in
theorem tracedLinear (x y : ℚ) (h₁ : 2*x + y ≤ 3) (h₂ : 4 ≤ x + y) : x ≤ -1 := by
  linarith
```

锁定输出显示三条预处理后的 facts，并找到 coefficients `(1,1,1)`。第三条 `-1-x < 0` 来自目标 `x ≤ -1` 的否定。加权和为：

:::codeBox "pseudocode"
```
(2*x + y - 3) + (4 - (x + y)) + (-1 - x) = 0
```
:::

代数上为零，同时严格小于零。

# 用户接口与调试
%%%
tag := "ch10-s09"
%%%

`linarith [extra]` 添加显式 proofs；`linarith only [h₁,h₂]` 排除其它局部比较式。`linarith?` 尝试减少未使用输入并生成可重放调用。建议给出一组足够假设，不承诺数学意义上的唯一最小 certificate。

```table
- 现象
- 最先检查
---
- 看不见某假设
- 是否真是 comparison proof，是否被类型分组
---
- Nat/Int 结果反直觉
- natToInt 与 strict integer strengthening
---
- 有乘积后失败
- 线性 parser 不处理变量乘变量
---
- proof reconstruction 失败
- coefficients、strictness、分母与 `ring1` residual
```

# `nlinarith` 是有限的非线性前处理
%%%
tag := "ch10-s10"
%%%

```anchor linarith_nonlinear_boundary
example (x : ℚ) (h : x^2 ≤ 0) : x = 0 := by
  fail_if_success linarith
  nlinarith
```

`nlinarith` 加入 syntactically occurring squares/self-products 的非负性，并生成部分 comparisons 的成对乘积；再把不同 monomials 当成线性 oracle 的新变量。它继续复用同一 oracle 和 verifier。

这不是 CAD、一般 Gröbner basis 或完整 SOS。新增推论有限，成对乘积还可能二次增长；本章主体仍是 `linarith` 核。

# 公理锥与信任账本
%%%
tag := "ch10-s11"
%%%

```anchor linarith_axiom_probe
#print axioms antisymmByLinarith
#print axioms strictContradiction
```

锁定环境中的输出为 `[propext, Classical.choice, Quot.sound]`。这是具体 theorem 的环境公理锥；关键结论是没有 tactic-specific axiom 要求内核相信 simplex 或 Fourier–Motzkin 的答案。

```table
- 部件
- 角色
---
- Preprocessors / parser
- 变换输入并生成相应 proofs
---
- Oracle
- 不可信搜索；返回 coefficients
---
- Verification + ring1
- 根据 certificate 构造矛盾 proof Expr
---
- Kernel
- 检查最终 proof
```

# 源码纵切
%%%
tag := "ch10-s12"
%%%

:::codeBox "pseudocode"
```
Frontend.lean
  目标取反、类型分组、参数、nlinarith extras
Preprocessing.lean
  默认 preprocessors
Parsing.lean / Datatypes.lean
  polynomial maps、comparisons、certificate
Oracle/SimplexAlgorithm/
  默认 sparse simplex
Oracle/FourierMotzkin.lean
  消元与来源向量
Verification.lean
  coefficients → proof → ring1 → False
```
:::

第一遍只追 trace 例子的三条 facts，每过一层抄下真实数组；不要同时展开所有 extension points。

# 练习
%%%
tag := "ch10-s13"
%%%

## 基础：手写 coefficients
%%%
tag := "ch10-s14"
%%%

为 `x ≤ 3`、`5 ≤ x` 写出与零比较形式和 coefficients，并说明矛盾来自常数项。

## 进阶：坏 oracle
%%%
tag := "ch10-s15"
%%%

固定返回三类坏证书：空表、使变量项未抵消的错误 coefficient、所有严格项 coefficient 为零。要求 verification 全部拒绝。

## 进阶：来源向量
%%%
tag := "ch10-s16"
%%%

手算一轮 Fourier–Motzkin；每条新比较式同时记录原事实来源向量，禁止只记公式。

## 挑战：小型 verifier
%%%
tag := "ch10-s17"
%%%

只支持 `ℚ` 上 `a*x+b ≤ 0` 与 `< 0`，输入 Nat coefficients，构造加权 comparison proof，并调用 `ring1` 证明归零。测试一个正确与三个损坏 certificates。

# 本章边界
%%%
tag := "ch10-s18"
%%%

`linarith` 把全部事实压成一个线性系统，oracle 返回一张短 certificate。下一章 `grind` 维护共享 E-graph，让等式合并、定理实例、逻辑传播、算术求解器与 case split 轮流写回新事实，直到闭合或达到资源界限。
