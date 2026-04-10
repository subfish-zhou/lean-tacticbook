import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch10NormNum"

#doc (Manual) "第十章 `norm_num`：数值计算框架" =>
%%%
file := "Ch10NormNum"
tag := "ch10-norm-num"
%%%

*本章目标*：理解 `norm_num` 的插件化架构与证明策略，学会编写自定义插件，
掌握它与 `simp`、`decide`、`omega` 的边界。

# `norm_num` 解决什么问题
%%%
tag := "norm-num-what-it-solves"
%%%

`norm_num` 证明*具体数值的命题*——等式、不等式、整除性、素性等：

```
-- 四则运算
#check (by norm_num : (2 : ℝ) + 3 = 5)
-- ⊢ 判定结果为 True，内核验证通过

-- 素性判定
#check (by norm_num : Nat.Prime 127)
-- 内部调用 Miller-Rabin 风格的确定性素性测试

-- 整除
#check (by norm_num : (10 : ℤ) ∣ 1000)

-- 有理数比较
#check (by norm_num : (3 : ℚ) / 4 < 1)
```

关键区分：`decide` 把命题归约到 `Bool` 并让 kernel 枚举；
`norm_num` 在 *meta 层* 做算术，然后构造一个让 kernel 验证的证明项。
二者的性能差异在大数上极为明显：

```
-- decide 会超时：内核需要展开 ~2^31 步
-- #check (by decide : Nat.Prime 2147483647)  -- timeout

-- norm_num 秒出：meta 层做确定性素性测试，构造证书
#check (by norm_num : Nat.Prime 2147483647)
```

# 核心架构：插件注册表
%%%
tag := "core-architecture-plugin-registry"
%%%

`norm_num` 的设计是一个*可扩展的插件注册表*。
每个插件负责处理以特定 head symbol 开头的表达式。

## Result 类型
%%%
tag := "result-type"
%%%

插件的返回类型 `NormNum.Result` 有三个构造子。
下面是简化后的核心形状，省略了部分字段；完整定义见 `Mathlib.Tactic.NormNum.Core`：

```
inductive Result where
  | isNat (inst : Expr) (lit : Expr) (proof : Expr)
    -- 表达式 = Nat.cast lit，proof : e = Nat.cast lit
  | isNegNat (inst : Expr) (lit : Expr) (proof : Expr)
    -- 表达式 = -Nat.cast lit
  | isBool (val : Bool) (proof : Expr)
    -- 命题为 True/False
```

`isNat` 和 `isNegNat` 把任意数值表达式规范化为*自然数字面量*或其负值，
附带一个证明该等式的 `proof`。`isBool` 用于布尔判定（如素性）。

## 插件注册
%%%
tag := "plugin-registration"
%%%

用 `@[norm_num <pattern>]` attribute 注册插件：

```
-- pattern 指定该插件能处理的 head symbol
@[norm_num Nat.Prime _]
def evalPrime : NormNumExt where
  eval {u α} (e : Expr) : SimpM (Option Result) := do
    -- e 是待规范化的表达式
    -- 返回 some result 表示成功，none 表示该插件不处理
    ...
```

`norm_num` 收到一个目标时的分派流程：

1. 提取目标表达式的 head symbol
2. 在注册表中查找匹配的插件
3. 依次尝试匹配的插件，直到某个返回 `some`
4. 用返回的 `Result` 构造最终证明

## 内置插件清单
%%%
tag := "builtin-plugins"
%%%

| 插件 | 处理的 head symbol | 示例 |
|------|--------------------|------|
| `evalAdd` | `HAdd.hAdd` | `2 + 3 = 5` |
| `evalMul` | `HMul.hMul` | `6 * 7 = 42` |
| `evalPow` | `HPow.hPow` | `2 ^ 10 = 1024` |
| `evalDiv` | `HDiv.hDiv` | `(10 : ℚ) / 3` |
| `evalMod` | `HMod.hMod` | `17 % 5 = 2` |
| `evalPrime` | `Nat.Prime` | `Nat.Prime 127` |
| `evalGcd` | `Nat.gcd` | `Nat.gcd 12 8 = 4` |
| `evalDvd` | `Dvd.dvd` | `(3 : ℤ) ∣ 12` |
| `evalLe` | `LE.le` | `(2 : ℝ) ≤ 3` |
| `evalLt` | `LT.lt` | `(1 : ℚ) < 2` |

# 证明构造策略
%%%
tag := "proof-construction-strategy"
%%%

`norm_num` 的核心思想：*在 meta 层做计算，在 object 层给出证书*。

## 加法示例
%%%
tag := "addition-example"
%%%

证明 `37 + 45 = 82`：

```
-- meta 层：Lean 原生 Nat 加法，瞬间得到 82
-- object 层：构造如下证明项
-- norm_num 不是直接 rfl——它把大数拆成 kernel 容易验证的步骤

-- 内部大致流程：
-- 1. 37 和 45 都已是 Nat literal，无需进一步规范化
-- 2. meta 层计算 37 + 45 = 82
-- 3. 构造 proof : 37 + 45 = 82
--    利用 Nat literal 的 kernel reduction 特性
--    kernel 验证 isNatLit 37 + isNatLit 45 →β isNatLit 82 ✓
```

## 素性示例
%%%
tag := "primality-example"
%%%

证明 `Nat.Prime 127`：

```
-- meta 层：
-- 1. 检查 127 > 1
-- 2. 试除 2, 3, 5, 7, 11（≤ √127 ≈ 11.3）
-- 3. 确认无因子

-- object 层：
-- 构造 minFac 证书：minFac 127 = 127
-- 这比让 kernel 枚举所有可能的因子快得多
-- kernel 只需验证证书的正确性，不需要自己搜索
```

## 与 kernel computation 的对比
%%%
tag := "comparison-with-kernel-computation"
%%%

| | `norm_num` | `decide` / `native_decide` |
|---|---|---|
| 计算位置 | meta 层（elaborator） | kernel / 编译器 |
| 输出 | 证明项（证书） | `rfl : decide p = true` |
| 大数性能 | 优秀 | 可能超时 |
| 可信基 | kernel 验证证书 | 信任 kernel reduction / native code |
| 可扩展性 | 插件系统 | 需要 `Decidable` 实例 |

# 编写自定义插件
%%%
tag := "writing-custom-plugins"
%%%

## 插件的结构
%%%
tag := "plugin-structure"
%%%

一个 `norm_num` 插件只需做三件事：模式匹配、meta 层计算、构造证明。
下面用伪代码展示骨架——不涉及 `Qq` 等元编程细节：

```
@[norm_num MyFunc _]            -- ❶ 注册：声明处理哪个 head symbol
def evalMyFunc : NormNumExt where
  eval (e : Expr) := do
    -- ❷ 模式匹配：提取 MyFunc 的参数
    let arg ← 从 e 中提取参数，失败则 return none

    -- ❸ meta 层计算：用 Lean 原生函数得到结果
    let result := myFuncImpl arg

    -- ❹ 构造证明：给 kernel 一个可验证的证书
    let proof ← 构造 "MyFunc arg = result" 的证明项
    return some (.isNat ... result proof)
```

> *关键设计规则*：当插件无法处理当前表达式时，*返回 `none`* 而非抛出
> `failure`。`none` 让 `norm_num` 继续尝试其他插件；`failure` 会中断
> 整个 pipeline，导致本可由其他插件处理的目标也一起失败。

完整的可编译示例（为 `Nat.fib` 编写插件）留作练习 10.4；
它需要用到 `NormNumExt`、`Qq` quoted expression 和 proof construction，
属于进阶元编程内容。

## 插件开发要点
%%%
tag := "plugin-development-tips"
%%%

*模式匹配要精确*：`@[norm_num Nat.fib _]` 中的 pattern 决定何时触发。
写错 pattern 会导致插件永远不被调用，且无任何报错。

*证明构造是难点*：meta 层计算很容易，但构造让 kernel 接受的证明项需要
对 Lean 的类型系统和 kernel reduction 规则有深入理解。
常用策略：

- 小范围：直接用 `mkDecideProof`，让 kernel reduce
- 大范围：构造分步证书（如素性的 minFac 证书）
- 通用：用 `Qq` quoted expression 确保类型安全

# `norm_num` 与 `simp` 的配合
%%%
tag := "norm-num-with-simp"
%%%

## 作为 simp 的 discharger
%%%
tag := "as-simp-discharger"
%%%

`simp` 在化简条件引理时可以调用 `norm_num` 来 discharge 数值侧条件：

```
-- 引理 div_add_mod 有侧条件 b ≠ 0
-- simp 在应用该引理时需要证明 3 ≠ 0
-- norm_num 作为 discharger 自动处理
example (n : ℤ) : n % 3 + 3 * (n / 3) = n := by
  simp [Int.emod_add_ediv]
  -- simp 内部：需要 (3 : ℤ) ≠ 0 → norm_num discharge ✓
```

## 管线组合
%%%
tag := "pipeline-combination"
%%%

常见的组合模式：

```
-- 模式 1：simp 化简结构，norm_num 收尾数值
example : (2 : ℝ) * 3 + 1 = 7 := by
  norm_num
  -- norm_num 单独即可，不需要 simp

-- 模式 2：simp 展开定义后 norm_num 计算
example : Nat.factorial 5 = 120 := by
  simp [Nat.factorial]
  -- 展开 factorial 定义
  norm_num
  -- 计算具体值

-- 模式 3：norm_num 作为 simp extension
-- 在 simp set 中启用 norm_num
example : (2 : ℝ) + 3 ≠ 6 := by
  simp (config := { decide := false }) only []
  norm_num
```

# 失败模式与诊断
%%%
tag := "failure-modes-and-diagnostics"
%%%

## 含变量的表达式
%%%
tag := "expressions-with-variables"
%%%

```
-- ✗ norm_num 无法处理含自由变量的表达式
example (x : ℝ) : x + 0 = x := by
  norm_num  -- 失败！x 不是具体数值
  -- 应使用：simp 或 ring
```

`norm_num` 只处理*完全具体*的数值表达式。
一旦出现自由变量，它会返回 `none`，tactic 报错。

## 缺少插件
%%%
tag := "missing-plugin"
%%%

```
-- ✗ 没有处理 Nat.sqrt 的内置插件
-- example : Nat.sqrt 49 = 7 := by norm_num  -- 失败

-- 解法 1：展开定义后用其他 tactic
example : Nat.sqrt 49 = 7 := by native_decide

-- 解法 2：编写自定义插件（见 10.4 节）
```

当 `norm_num` 失败时，检查目标的 head symbol 是否有对应插件。
`set_option trace.Meta.NormNum true` 可以查看插件分派过程。

## 类型不匹配
%%%
tag := "ch10-type-mismatch"
%%%

```
-- ✗ 默认数值类型是 Nat，Nat 上没有减法负数
-- example : 3 - 5 = -2 := by norm_num
-- 类型错误：Nat 上 3 - 5 = 0（截断减法）

-- ✓ 指定整数类型
example : (3 : ℤ) - 5 = -2 := by norm_num
```

`norm_num` 对类型敏感。确保数值表达式在正确的类型上工作。

## 诊断工具
%%%
tag := "diagnostic-tools"
%%%

```
-- 查看 norm_num 的插件分派和执行过程
set_option trace.Meta.NormNum true in
example : (2 : ℝ) + 3 = 5 := by norm_num

```

# 适用范围速查
%%%
tag := "applicability-quick-reference"
%%%

| 目标形式 | 推荐 tactic | 原因 |
|----------|-------------|------|
| `2 + 3 = 5` | `norm_num` | 具体数值等式 |
| `Nat.Prime 127` | `norm_num` | 有内置素性插件 |
| `(3/4 : ℚ) * 4 = 3` | `norm_num` | 有理数算术 |
| `x + 0 = x` | `simp` / `ring` | 含变量 |
| `x + 1 > x` | `omega` / `linarith` | 线性不等式 |
| `Nat.Prime 2147483647` | `norm_num` | 大素数，meta 层计算 |
| `2 ^ 32 = 4294967296` | `norm_num` | 幂运算 |
| `n % 2 = 0 ∨ n % 2 = 1` | `omega` | 含变量的模算术 |
| `Nat.sqrt 49 = 7` | `native_decide` | 无 `norm_num` 插件 |

经验法则：*目标中没有自由变量且涉及算术* → 先试 `norm_num`。

# 与其他 tactic 的边界
%%%
tag := "boundaries-with-other-tactics"
%%%

`omega` 处理*线性整数算术*（Presburger arithmetic），可以含变量；
`ring` 证明*交换环上的多项式恒等式*，可以含变量但只处理等式；
`decide` 通过 kernel reduction 判定，小规模可用，大数超时。

```
example (n : Nat) : n + 0 = n := by omega          -- 含变量，norm_num 不行
example (x : ℝ) : (x + 1) ^ 2 = x ^ 2 + 2*x + 1 := by ring  -- 多项式恒等式
example : (3 : ℝ) < 4 := by norm_num               -- 具体不等式，ring 不行
example : Nat.Prime 104729 := by norm_num           -- 大素数，decide 超时
```

# 练习
%%%
tag := "ch10-exercises"
%%%

*练习 10.1*（基础）：用 `norm_num` 证明以下命题。

```
-- (a) 有理数算术
example : (7 : ℚ) / 3 + 5 / 3 = 4 := by sorry

-- (b) 整数整除
example : (15 : ℤ) ∣ 450 := by sorry

-- (c) 素性
example : Nat.Prime 1009 := by sorry
```

*练习 10.2*（诊断）：解释为什么以下 `norm_num` 调用失败，并给出正确的 tactic。

```
-- (a)
example (n : Nat) : n * 1 = n := by norm_num  -- 为什么失败？

-- (b)
example : (5 : Nat) - 8 = 0 := by norm_num    -- 能成功吗？

-- (c)
example : Nat.sqrt 100 = 10 := by norm_num    -- 为什么失败？
```

*练习 10.3*（组合）：选择合适的 tactic 组合证明以下命题。

```
-- (a)
example : Nat.factorial 6 = 720 := by sorry

-- (b)
example (n : ℤ) (h : n > 0) : n + 3 > 2 := by sorry

-- (c)
example : (2 : ℝ) ^ 8 - 1 = 255 := by sorry
```

*练习 10.4*（进阶）：为 `Nat.fib` 编写一个 `norm_num` 插件，
使得 `by norm_num : Nat.fib 10 = 55` 能够通过。
提示：参考 10.4.1 节的框架，重点在证明构造部分。

# 小结
%%%
tag := "ch10-summary"
%%%

| 概念 | 要点 |
|------|------|
| 定位 | 具体数值命题的快速证明，无自由变量 |
| 架构 | 插件注册表，`@[norm_num head _]` 注册 |
| 证明策略 | meta 层计算 + 构造 kernel 可验证的证书 |
| vs `decide` | meta 计算 vs kernel reduction，大数性能差异巨大 |
| vs `omega` | `norm_num` 不含变量；`omega` 处理线性整数算术 |
| vs `ring` | `norm_num` 处理具体数值；`ring` 处理多项式恒等式 |
| 与 `simp` 配合 | 作为 discharger 处理数值侧条件 |
| 扩展 | 实现 `NormNumExt`，返回 `Result`，注册到 head symbol |
| 失败诊断 | `trace.Meta.NormNum` 查看分派过程 |

下一章我们将学习 `aesop`——一个可配置的前向/后向搜索引擎。
