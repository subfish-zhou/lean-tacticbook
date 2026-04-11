import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch08Omega"

#doc (Manual) "omega：Presburger 算术决策过程" =>
%%%
file := "Ch08Omega"
tag := "ch08-omega"
%%%

**本章目标**：前半章掌握 `omega` 的用法、能力边界与调试技巧；后半章从 Lean 4 真实源码层面拆解 omega 的完整实现——入口调用链、核心数据结构、预处理管线、消元算法、证明项构造——面向想深入理解内部机制的读者。

`omega` 是 Lean 4 内置的 **Presburger 算术**决策过程，完全在 Lean 核心实现，不依赖 Mathlib。它能自动证明关于 `Nat` 和 `Int` 的**线性算术**命题——即只涉及加法、常数乘法和比较的等式与不等式。实现基于 William Pugh 的 Omega Test（1991），但做了面向程序验证的工程化取舍：实现了最常用的 real shadow（Fourier-Motzkin 消元），未实现 dark shadow 和 grey shadow——在实际编程验证中几乎不会遇到需要它们的场景。

# 用法详解
%%%
tag := "ch08-usage"
%%%

## omega 解决什么问题
%%%
tag := "ch08-what-omega-solves"
%%%

omega 判定**整数线性算术**——变量取值在 `Nat` 或 `Int` 上，运算只涉及加法、常数乘法、比较、整除和取模：

```
-- 基本不等式
example (n : Nat) : n + 1 > n := by omega

-- 整数线性约束
example (a b : Int) (h : a < b) : a + 1 ≤ b := by omega

-- 多变量线性组合
example (x y : Nat) (h1 : x ≤ 10) (h2 : y ≤ 10) : x + y ≤ 20 := by omega

-- 整除与模运算
example (n : Int) (h : n % 2 = 0) : ∃ k, n = 2 * k := by omega

-- Nat 截断减法
example (n : Nat) : n - (n + 1) = 0 := by omega

-- min / max
example (a b : Nat) : max a b ≥ a := by omega
```

## omega 不能做什么
%%%
tag := "ch08-omega-limitations"
%%%

omega 的边界清晰——超出线性算术的命题一律拒绝：

- **变量乘法**（非线性）：`x * y = 0` 涉及两个变量相乘，omega 无法处理
- **指数 / 幂运算**：`2 ^ n ≥ 1` 不是线性的，需要归纳法
- **实数或其他域**：omega 只处理 `Nat`、`Int` 和 `Fin n`
- **未展开的定义**：omega 不会展开自定义定义，需要先 `unfold` 或 `simp only [...]`

## Nat / Int / Fin 的处理
%%%
tag := "ch08-nat-int-fin"
%%%

omega 内部统一在 `Int` 域上工作。所有 `Nat` 表达式都被提升（cast）到 `Int`，附加非负约束 `0 ≤ ↑x`。

**Nat 截断减法**是特殊难点：`3 - 5 = 0` 在 `Nat` 上成立，但在 `Int` 上 `3 - 5 = -2`。omega 通过**二分法**处理——对每个 `↑(a - b : Nat)`，生成析取：

- 情况 1：`b ≤ a → ↑(a - b) = ↑a - ↑b`
- 情况 2：`a < b → ↑(a - b) = 0`

```
-- omega 知道截断减法的完整语义
example (n m : Nat) (h : m ≤ n) : n - m + m = n := by omega
example (a b : Nat) : a - b ≤ a := by omega
```

**整数除法和取模**：`x / k`（`k` 为正常数）被注册为新原子 `α`，生成约束 `k * α ≤ x < k * α + k`。取模 `x % k` 改写为 `x - (x / k) * k`。

**Fin n**：`Fin n` 的值被提升到 `Nat`，自动添加 `0 ≤ x.val` 和 `x.val < n` 约束。但 `Fin` 的模算术运算（如 `Fin` 上的加法）需要先用 `simp [Fin.val_add]` 展开。

## 配置选项
%%%
tag := "ch08-config"
%%%

omega 的行为通过 `OmegaConfig` 控制：

```
-- 关闭 Nat 减法二分（避免指数爆炸）
omega (config := { splitNatSub := false })

-- 关闭所有 case split，只做纯线性判定
omega (config := { splitDisjunctions := false, splitNatSub := false,
                    splitNatAbs := false, splitMinMax := false })
```

四个配置项：`splitDisjunctions`（析取 case split）、`splitNatSub`（Nat 减法二分）、`splitNatAbs`（Int.natAbs 二分）、`splitMinMax`（展开 min/max）。默认全部为 `true`。

## omega 与 linarith 的区别
%%%
tag := "ch08-omega-vs-linarith"
%%%

omega 和 Mathlib 的 `linarith` 都处理线性算术，但定位不同：

| 维度 | omega | linarith |
|------|-------|----------|
| 所在位置 | Lean 核心 | Mathlib |
| 数域 | Int、Nat、Fin | 任意线性有序域（R、Q、Z 等） |
| 整除性 | 支持（`k ∣ x`、`x % k`） | 不支持 |
| Nat 减法 | 自动二分处理 | 不处理 |
| 实数 | 不支持 | 支持 |

**选择原则**：Nat/Int 线性 + 整除 → `omega`；实数线性 → `linarith`；非线性 → `nlinarith`。

```
-- omega 的强项：整除推理（linarith 做不到）
example (a b : Int) (h : a % 2 = 0) (h2 : b % 2 = 0) :
    (a + b) % 2 = 0 := by omega

-- linarith 的强项：实数域（omega 做不到）
-- example (x : Real) (h : x > 0) : x + 1 > 1 := by linarith
```

## 与其他 tactic 的组合
%%%
tag := "ch08-omega-combos"
%%%

omega 经常作为"收尾"tactic 出现：

```
-- 先简化，再 omega
-- simp <;> try omega

-- 作为 simp 的 discharger
-- simp (discharger := omega)

-- 在 decide 策略中作为后备
-- first | omega | norm_num | simp
```

omega 会自动扫描 `LocalContext` 中所有线性算术假设，**无需手动指定**。但自定义定义不会被展开——调用前先 `unfold` 或 `simp only [...]`。

# 源码全景
%%%
tag := "ch08-source-overview"
%%%

omega 的源码分布在两个目录：`Lean/Elab/Tactic/Omega/`（tactic 层与算法）和 `Init/Omega/`（数据结构与引理）。核心文件：

| 文件 | 内容 | 行数 |
|------|------|------|
| `Frontend.lean` | tactic 入口、预处理管线、`omegaImpl`、case split | ~714 |
| `Core.lean` | `Problem`、`Fact`、`Justification`、消元算法 | ~578 |
| `OmegaM.lean` | `OmegaM` monad、原子管理、缓存 | ~262 |
| `MinNatAbs.lean` | 系数分析辅助（困难等式选择） | ~150 |

omega 的工程复杂度远超核心消元算法。复杂度来自三个方面：**(a)** 命题翻译层——把 Lean 语法世界的命题逐步降解为约束求解器的内部表示；**(b)** Nat/Int/Fin 语义桥接——截断减法、整数除法、Fin 模算术的精确翻译；**(c)** 延迟证明构造——`Justification` 追踪每一步推导的来源，最终构造可检查的证明项。

## 架构全景图
%%%
tag := "ch08-architecture"
%%%

```
用户层
┌─────────────────────────────────────────────────────┐
│  omega                                              │
│  omega (config := { splitNatSub := false })         │
└─────────┬───────────────────────────────────────────┘
          │
Tactic 层 (TacticM)
┌─────────┴───────────────────────────────────────────┐
│  evalOmega                                          │
│  · 先尝试 assumption                                │
│  · 解析配置                                          │
│  · omegaTactic                                      │
│    · falseOrByContra (转化目标为 False)              │
│    · 收集局部假设                                    │
│    · 调用 omega (MetaM 入口)                         │
└─────────┬───────────────────────────────────────────┘
          │
Meta 层 (OmegaM)
┌─────────┴───────────────────────────────────────────┐
│  omegaImpl  ←── 主循环                              │
│  ├── processFacts (预处理)                           │
│  │   └── addFact (命题分类)                          │
│  │       └── asLinearCombo (线性化)                  │
│  ├── Problem.elimination (消元)                     │
│  │   ├── solveEqualities (等式消元)                  │
│  │   └── fourierMotzkin (FM 消元)                   │
│  └── splitDisjunction (析取 case split)             │
│      └── omegaImpl (递归)                            │
└─────────────────────────────────────────────────────┘

数据层
┌─────────────────────────────────────────────────────┐
│  Coeffs (稠密系数向量)                               │
│  LinearCombo { const, coeffs }                      │
│  Constraint { lowerBound, upperBound }              │
│  Fact { coeffs, constraint, justification }         │
│  Problem { assumptions, constraints, equalities }   │
│  MetaProblem { problem, facts, disjunctions }       │
└─────────────────────────────────────────────────────┘
```

# 核心数据结构
%%%
tag := "ch08-data-structures"
%%%

## Coeffs：稠密系数向量
%%%
tag := "ch08-coeffs"
%%%

最底层是 `IntList`（`List Int` 的类型别名），用于稠密表示整数系数向量。`Coeffs` 是 `IntList` 的类型别名，超出列表长度的位置视为 0。核心运算定义在 `Init/Omega/IntList.lean` 和 `Init/Omega/Coeffs.lean`：

```
-- [Lean 4 v4.30.0-rc1, Init/Omega/IntList.lean]
abbrev IntList := List Int
abbrev Coeffs := IntList

def get (xs : IntList) (i : Nat) : Int := xs[i]?.getD 0

-- 点积——约束求值的核心
def dot (xs ys : IntList) : Int := (xs * ys).sum

-- 线性组合——FM 消元的基本操作
def combo (a : Int) (xs : IntList) (b : Int) (ys : IntList) : IntList :=
  List.zipWithAll (fun x y => a * x.getD 0 + b * y.getD 0) xs ys
```

其他操作包括 `neg`、`smul`（标量乘法）、`sdiv`（带符号除法）、`gcd`（所有元素绝对值的最大公因数）、`bmod`（平衡取模）等。

## LinearCombo：线性组合
%%%
tag := "ch08-linear-combo"
%%%

`LinearCombo` 表示一个**常数项 + 系数向量**的线性表达式：

```
-- [Lean 4 v4.30.0-rc1, Init/Omega/LinearCombo.lean]
structure LinearCombo where
  const : Int := 0       -- 常数项
  coeffs : Coeffs := []  -- 各原子的系数
```

语义：`const + Σᵢ coeffs[i] * atoms[i]`。算术运算（`add`、`sub`、`neg`）逐分量操作。**乘法只在一个因子是常数时有效**——代码在使用前检查 `xl.coeffs.isZero ∨ yl.coeffs.isZero`。

## Constraint：约束的上下界
%%%
tag := "ch08-constraint"
%%%

`Constraint` 用一对可选的上下界表示约束：

```
-- [Lean 4 v4.30.0-rc1, Init/Omega/Constraint.lean]
structure Constraint where
  lowerBound : Option Int
  upperBound : Option Int
```

语义是 `lowerBound ≤ value ≤ upperBound`，`none` 表示无约束。预定义特殊约束：

```
-- [Lean 4 v4.30.0-rc1, Init/Omega/Constraint.lean]
def trivial    : Constraint := ⟨none, none⟩       -- 无约束
def impossible : Constraint := ⟨some 1, some 0⟩   -- 不可满足（1 ≤ x ≤ 0）
def exact (r : Int) : Constraint := ⟨some r, some r⟩  -- 等式（x = r）
```

关键操作：

```
-- [Lean 4 v4.30.0-rc1, Init/Omega/Constraint.lean]
-- 合取（取更紧的界）
def combine (x y : Constraint) : Constraint where
  lowerBound := Option.merge max x.lowerBound y.lowerBound
  upperBound := Option.merge min x.upperBound y.upperBound

-- 线性组合
def combo (a : Int) (x : Constraint) (b : Int) (y : Constraint) : Constraint :=
  add (scale a x) (scale b y)

-- 不可满足判定
def isImpossible (c : Constraint) : Bool :=
  match c.lowerBound, c.upperBound with
  | some l, some u => u < l
  | _, _ => false
```

`combine` 是同系数约束合并的核心——把两个约束取交集（更紧的界）。`combo` 是 Fourier-Motzkin 消元的基本操作——两个约束的线性组合。

## Justification：推导树
%%%
tag := "ch08-justification"
%%%

`Justification` 是一个归纳类型，记录约束的推导历史。它的索引类型参数精确追踪约束和系数，保证证明项构造的类型安全：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Core.lean:42-59]
inductive Justification : Constraint → Coeffs → Type
  | assumption (s : Constraint) (x : Coeffs) (i : Nat) : Justification s x
  | tidy (j : Justification s c) :
      Justification (tidyConstraint s c) (tidyCoeffs s c)
  | combine {s t c} (j : Justification s c) (k : Justification t c) :
      Justification (s.combine t) c
  | combo {s t x y} (a : Int) (j : Justification s x)
                     (b : Int) (k : Justification t y) :
      Justification (Constraint.combo a s b t) (Coeffs.combo a x b y)
  | bmod (m : Nat) (r : Int) (i : Nat) {x}
      (j : Justification (.exact r) x) :
      Justification (.exact (Int.bmod r m)) (bmod_coeffs m i x)
```

各构造子对应不同的推导步骤：

| 构造子 | 含义 |
|--------|------|
| `assumption` | 来自原始假设 `Problem.assumptions[i]` |
| `tidy` | 约束规范化（GCD 除法、系数归正） |
| `combine` | 同系数约束的合取（取更紧界） |
| `combo` | 两个约束的线性组合（Fourier-Motzkin 的核心操作） |
| `bmod` | 平衡取模（处理困难等式消元） |

**关键设计**：omega 不在搜索过程中构造 Lean 证明项——先在 `Justification` 中记录推导树，只有找到矛盾后才调用 `Justification.proof` 转化为 `Expr`。这种**延迟证明构造**避免了为最终不需要的搜索分支生成证明。

## Fact 与 Problem
%%%
tag := "ch08-fact-and-problem"
%%%

`Fact` 把约束、系数和推导绑定在一起：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Core.lean:129-136]
structure Fact where
  coeffs : Coeffs
  constraint : Constraint
  justification : Justification constraint coeffs
```

`Problem` 是约束求解器的核心状态：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Core.lean:167-195]
structure Problem where
  assumptions : Array Proof := ∅
  numVars : Nat := 0
  constraints : Std.HashMap Coeffs Fact := ∅
  equalities : Std.HashSet Coeffs := ∅
  eliminations : List (Fact × Nat × Int) := []
  possible : Bool := true
  proveFalse? : Option Proof := none
  proveFalse?_spec : possible || proveFalse?.isSome := by rfl
  explanation? : Thunk String := ""
```

设计要点：

- **以 `Coeffs` 为键的 HashMap**：同系数约束自动合并（通过 `combine` 取更紧界）
- **`equalities` 集合**：追踪等式以便优先消元
- **`possible` + `proveFalse?` 不变量**：一旦发现矛盾就停止，`proveFalse?_spec` 在类型层面保证这个不变量
- **`eliminations` 列表**：记录已用于消元的等式，新约束入库时需要 `replayEliminations` 重放

`MetaProblem` 在 `Problem` 之上加了预处理队列：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Frontend.lean:59-69]
structure MetaProblem where
  problem : Problem := {}
  facts : List Expr := []
  disjunctions : List Expr := []
  processedFacts : Std.HashSet Expr := ∅
```

`facts` 是待处理的假设队列，`disjunctions` 是待 case split 的析取，`processedFacts` 做去重。

# 预处理：命题翻译
%%%
tag := "ch08-preprocessing"
%%%

omega 的预处理分两步：**命题分类**（`addFact`）和**表达式线性化**（`asLinearCombo`）。

## 入口：evalOmega
%%%
tag := "ch08-eval-omega"
%%%

omega 的 tactic 入口定义在 `Frontend.lean`：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Frontend.lean:703-710]
@[builtin_tactic Lean.Parser.Tactic.omega]
def evalOmega : Tactic
  | `(tactic| omega%$tk $cfg:optConfig) => do
    Meta.withReducibleAndInstances (evalAssumption tk) <|> do
    let cfg ← elabOmegaConfig cfg
    omegaTactic cfg
  | _ => throwUnsupportedSyntax
```

注意第一行的 `evalAssumption`：omega 会**先尝试 `assumption`**——如果目标已经在假设中，直接结束，避免启动重型算法。这种"短路"模式是高效 tactic 设计的常见手法。

`omegaTactic` 做三件关键的事：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Frontend.lean:680-696]
def omegaTactic (cfg : OmegaConfig) : TacticM Unit := do
  recordExtraModUse (isMeta := false) `Init.Omega
  liftMetaFinishingTactic fun g => do
    if debug.terminalTacticsAsSorry.get (← getOptions) then
      g.admit
    else
      let some g ← g.falseOrByContra | return ()
      g.withContext do
        let type ← g.getType
        let g' ← mkFreshExprSyntheticOpaqueMVar type
        let hyps := (← getLocalHyps).toList
        trace[omega] "analyzing {hyps.length} hypotheses:\n\
          {← hyps.mapM inferType}"
        omega hyps g'.mvarId! cfg
        let e ← mkAuxTheorem type
          (← instantiateMVarsProfiling g') (zetaDelta := true)
        g.assign e
```

1. **`falseOrByContra`**：把目标转化为 `False`——omega 通过矛盾法证明
2. **收集假设**：`getLocalHyps` 获取所有局部假设
3. **`mkAuxTheorem` 封装**：omega 的证明项通常非常大，封装为辅助定义避免拖慢类型检查

## 命题分类：addFact
%%%
tag := "ch08-add-fact"
%%%

`addFact` 对每个假设进行模式匹配，把数学命题分类并翻译为线性约束：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Frontend.lean:425-508]
partial def addFact (p : MetaProblem) (h : Expr) :
    OmegaM (MetaProblem × Nat) := do
  if ! p.problem.possible then return (p, 0)
  let t ← instantiateMVars (← whnfR (← inferType h))
  match t with
  | .forallE _ x y _ =>
    if ← pure t.isArrow <&&> isProp x <&&> isProp y then
      -- 蕴含 p → q 转化为析取 ¬p ∨ q
      p.addFact (mkApp4 (.const ``Decidable.not_or_of_imp []) x y
        (.app (.const ``Classical.propDecidable []) x) h)
    ...
  | .app _ _ =>
    match_expr t with
    | Eq α x y => ...       -- 等式
    | LE.le α _ x y => ...  -- ≤
    | LT.lt α _ x y => ...  -- <
    | Not p => ...           -- ¬
    | And p q => ...         -- ∧
    | Or _ _ => ...          -- ∨（加入析取队列）
    | Dvd.dvd α _ x y => ...-- ∣
    ...
```

各类命题的转化方式：

| 输入命题 | 转化为 | 说明 |
|----------|--------|------|
| `x = y` (Int) | `x - y = 0` | 等式 → 常数约束 |
| `x = y` (Nat) | `↑x - ↑y = 0` | 提升到 Int |
| `x ≤ y` (Int) | `0 ≤ y - x` | 不等式 → 下界约束 |
| `x < y` (Int) | `0 ≤ y - x - 1` | 严格 → 非严格 |
| `x ≠ y` | `x < y ∨ x > y` | 不等 → 析取 |
| `p ∧ q` | 拆分为两个独立假设 | 合取直接拆分 |
| `p ∨ q` | 加入析取队列 | 延后 case split |
| `k ∣ x` | `x % k = 0` | 整除 → 模约束 |
| `¬(k ∣ x)` | `x % k > 0` | 不整除 → 模正约束 |
| `p → q` | `¬p ∨ q` | 蕴含 → 析取 |

**关键细节**：所有 Nat 运算都被提升到 Int 处理。`addFact` 自动把 `Nat` 类型的等式/不等式通过 `Int.ofNat` 提升，然后在 Int 域上工作。

析取的处理是**延迟的**——先加入 `disjunctions` 队列，等核心消元无法找到矛盾时再做 case split。这种策略避免了不必要的分支搜索。

对于否定假设，`pushNot` 函数把否定推入内部：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Frontend.lean:371-420]
def pushNot (h P : Expr) : MetaM (Option Expr) := do
  let P ← whnfR P
  match P with
  | .app _ _ =>
    match_expr P with
    | LT.lt α _ x y => match_expr α with
      | Nat => return some (mkApp3 (.const ``Nat.le_of_not_lt []) x y h)
      | Int => return some (mkApp3 (.const ``Int.le_of_not_lt []) x y h)
      ...
    | LE.le α _ x y => match_expr α with
      | Nat => return some (mkApp3 (.const ``Nat.lt_of_not_le []) x y h)
      ...
    | Eq α x y => match_expr α with
      | Nat => return some
          (mkApp3 (.const ``Nat.lt_or_gt_of_ne []) x y h)
      ...
    | Not P =>
      return some (mkApp3 (.const ``Decidable.of_not_not []) P
        (.app (.const ``Classical.propDecidable []) P) h)
    ...
```

`¬(x < y)` 变为 `y ≤ x`，`¬(x = y)` 变为 `x < y ∨ x > y`（析取），`¬¬P` 变为 `P`。

## 表达式线性化：asLinearCombo
%%%
tag := "ch08-as-linear-combo"
%%%

`asLinearComboImpl` 递归地把一个整数表达式转化为 `LinearCombo`，返回三元组 `(LinearCombo, Proof, NewFacts)`：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Frontend.lean:131-241]
partial def asLinearComboImpl (e : Expr) :
    OmegaM (LinearCombo × OmegaM Expr × List Expr) := do
  match groundInt? e with
  | some i =>
    -- 地面整数常量：直接作为常数项
    let lc := {const := i}
    return ⟨lc, mkEvalRflProof e lc, ∅⟩
  | none => ...
    match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, e₁, e₂]) => do
    -- 加法：递归分解，合并系数
    let (l₁, prf₁, facts₁) ← asLinearCombo e₁
    let (l₂, prf₂, facts₂) ← asLinearCombo e₂
    ...
    pure (l₁ + l₂, prf, facts₁ ++ facts₂)
  | (``HSub.hSub, #[_, _, _, _, e₁, e₂]) => do
    -- 减法：类似加法
    ...
  | (``HMul.hMul, #[_, _, _, _, x, y]) =>
    -- 乘法：仅当一个因子是常数时展开
    let (xl, ...) ← asLinearCombo x
    let (yl, ...) ← asLinearCombo y
    if xl.coeffs.isZero ∨ yl.coeffs.isZero then
      pure (LinearCombo.mul xl yl, ...)
    else
      mkAtomLinearCombo e  -- 非线性乘法 → 当作原子
  | (``HMod.hMod, #[_, _, _, _, n, k]) =>
    -- 取模：改写为 x - (x / k) * k
    match groundNat? k with
    | some k' => do rewrite ... (mkApp2 (.const ``Int.emod_def []) n k')
    | none => mkAtomLinearCombo e
  | (``HDiv.hDiv, #[_, _, _, _, x, z]) =>
    -- 除以常数 → 新原子 + 界约束
    ...
  | _ => mkAtomLinearCombo e  -- 无法分解 → 新原子
```

**Nat → Int 的提升**（`handleNatCast`）把各种 Nat 运算推入 cast 内部：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Frontend.lean:255-298]
  handleNatCast (e i n : Expr) : ... := do
    match n.getAppFnArgs with
    | (``Nat.succ, #[n]) =>
        rewrite e (.app (.const ``Int.natCast_succ []) n)
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
        rewrite e (mkApp2 (.const ``Int.natCast_add []) a b)
    | (``HMul.hMul, #[_, _, _, _, a, b]) =>
        -- ↑(a * b) → ↑a * ↑b，并添加非负约束
        let (lc, prf, r) ←
          rewrite e (mkApp2 (.const ``Int.natCast_mul []) a b)
        pure (lc, prf,
          r.insert (mkApp2 (.const ``Int.ofNat_mul_nonneg []) a b))
    | (``HDiv.hDiv, #[_, _, _, _, a, b]) =>
        rewrite e (mkApp2 (.const ``Int.natCast_ediv []) a b)
    | (``HMod.hMod, #[_, _, _, _, a, b]) =>
        rewrite e (mkApp2 (.const ``Int.natCast_emod []) a b)
    ...
```

`↑(a + b)` 变为 `↑a + ↑b`，`↑(a * b)` 变为 `↑a * ↑b` 并附加非负约束。这种"提升推入"（push cast inward）使 omega 能在纯 Int 域工作。

## processFacts：批量预处理
%%%
tag := "ch08-process-facts"
%%%

`processFacts` 反复从队列中取出假设调用 `addFact`，直到队列为空：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Frontend.lean:515-527]
partial def processFacts (p : MetaProblem) :
    OmegaM (MetaProblem × Nat) := do
  match p.facts with
  | [] => pure (p, 0)
  | h :: t =>
    if p.processedFacts.contains h then
      processFacts { p with facts := t }
    else
      let (p₁, n₁) ← MetaProblem.addFact { p with
        facts := t
        processedFacts := p.processedFacts.insert h } h
      let (p₂, n₂) ← p₁.processFacts
      return (p₂, n₁ + n₂)
```

去重通过 `processedFacts : HashSet Expr` 实现——同一个假设不会被处理两次。注意 `addFact` 可能生成新的假设（如 Nat 提升的非负约束），这些新假设会被追加到队列头部，确保完整处理。

# 消元算法
%%%
tag := "ch08-elimination"
%%%

预处理完成后，`Problem` 包含一组线性约束。核心算法分两阶段：**等式消元** → **Fourier-Motzkin 消元**。

## 算法主循环
%%%
tag := "ch08-main-loop"
%%%

`runOmega` 和 `elimination` 是互相递归的：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Core.lean:555-573]
partial def runOmega (p : Problem) : OmegaM Problem := do
  trace[omega] "Running omega on:\n{p}"
  if p.possible then
    let p' ← p.solveEqualities
    elimination p'
  else
    return p

partial def elimination (p : Problem) : OmegaM Problem :=
  if p.possible then
    if p.isEmpty then
      return p
    else do
      trace[omega] "Running Fourier-Motzkin elimination on:\n{p}"
      runOmega (← p.fourierMotzkin)
  else
    return p
```

流程：先用等式消元消去所有等式约束，然后做一轮 FM 消元（消去一个变量），递归。直到问题为空（所有变量被消去）或发现矛盾。

## 等式消元
%%%
tag := "ch08-equality-elimination"
%%%

等式约束（上下界相等）可以直接用来消去一个变量，是优先处理的。

**选择等式**——`selectEquality` 从 `equalities` 集合中选择最优等式：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Core.lean:289-300]
def selectEquality (p : Problem) : Option (Coeffs × Nat) :=
  p.equalities.fold (init := none) fun
  | none, c => (c, c.minNatAbs)
  | some (r, m), c =>
    if 2 ≤ m then
      let m' := c.minNatAbs
      if (m' < m || m' = m && c.maxNatAbs < r.maxNatAbs) then
        (c, m')
      else
        (r, m)
    else
      (r, m)
```

优先选系数绝对值最小的等式——理想情况是 ±1，这是"简单等式"。

### 简单等式消元（系数为 ±1）
%%%
tag := "ch08-easy-equality"
%%%

如果变量 `xᵢ` 的系数是 ±1，可以直接求解 `xᵢ = -(c₀ + c₂·x₂ + ...)`，然后代入所有其他约束：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Core.lean:316-331]
def solveEasyEquality (p : Problem) (c : Coeffs) : Problem :=
  let i := c.findIdx? (·.natAbs = 1) |>.getD 0
  let sign := c.get i |> Int.sign
  match p.constraints[c]? with
  | some f =>
    let init :=
    { assumptions := p.assumptions
      eliminations := (f, i, sign) :: p.eliminations }
    p.constraints.fold (init := init) fun p' coeffs g =>
      match Coeffs.get coeffs i with
      | 0 =>
        p'.addConstraint g
      | ci =>
        let k := -1 * sign * ci
        p'.addConstraint (Fact.combo k f 1 g).tidy
  | _ => p
```

找到系数为 ±1 的变量 `xᵢ`，用等式把它从所有约束中代入消去。消元结果记录在 `eliminations` 列表中，之后新加入的约束需要 `replayEliminations` 重放这些消元。

### 困难等式消元（平衡取模）
%%%
tag := "ch08-hard-equality"
%%%

当所有系数绝对值都大于 1 时，使用**平衡取模**（balanced mod, bmod）技巧。设最小系数绝对值为 `m-1`，取 `m = minNatAbs + 1`：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Core.lean:340-356]
def dealWithHardEquality (p : Problem) (c : Coeffs) :
    OmegaM Problem :=
  match p.constraints[c]? with
  | some ⟨_, ⟨some r, some r'⟩, j⟩ => do
    let m := c.minNatAbs + 1
    let x := mkApp3 (.const ``bmod_div_term [])
      (toExpr m) (toExpr c) (← atomsCoeffs)
    let (i, facts?) ← lookup x
    if hr : r' = r then
      match facts? with
      | none => throwError
          "When solving hard equality, new atom had been seen before!"
      | some facts => if ! facts.isEmpty then
        throwError
          "When solving hard equality, unexpected new facts!"
      return p.addConstraint
        { coeffs := _, constraint := _,
          justification := (hr ▸ j).bmod m r i }
    else
      throwError "Invalid constraint, expected an equation."
  | _ => return p
```

思路：对等式 `r + c₀·x₀ + c₁·x₁ + ... = 0` 做 bmod m，得到新等式 `bmod(r,m) + bmod(c₀,m)·x₀ + ... = m·α`，其中 `α` 是新变量。由于 `bmod(m-1, m)` 的值为 ±1，原来系数最小的变量在新等式中系数变为 ±1——困难等式变成了简单等式。

虽然引入了新变量，但词典序 `(minNatAbs, maxNatAbs)` 严格递减，保证终止。

`solveEqualities` 循环处理所有等式：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Core.lean:369-374]
partial def solveEqualities (p : Problem) : OmegaM Problem :=
  if p.possible then
    match p.selectEquality with
    | some (c, m) => do (← p.solveEquality c m).solveEqualities
    | none => return p
  else return p
```

## MinNatAbs：辅助系数分析
%%%
tag := "ch08-min-nat-abs"
%%%

困难等式消元依赖 `minNatAbs`——系数列表中最小的非零绝对值。它定义在 `MinNatAbs.lean`：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/MinNatAbs.lean:41]
def nonzeroMinimum (xs : List Nat) : Nat :=
  xs.filter (· ≠ 0) |>.min? |>.getD 0

-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/MinNatAbs.lean:134]
def minNatAbs (xs : List Int) : Nat :=
  xs.map Int.natAbs |> nonzeroMinimum
```

该文件还包含 `minNatAbs` 的完整形式化性质证明（`minNatAbs_eq_zero_iff`、`minNatAbs_eq_nonzero_iff`、`nonzeroMinimum_le` 等），这些引理用于保证等式消元的终止性和正确性。

## Fourier-Motzkin 消元
%%%
tag := "ch08-fourier-motzkin"
%%%

等式消元后，剩下的约束都是不等式。Fourier-Motzkin 消元选一个变量，把涉及它的约束配对消去。

### 步骤 1：分类约束
%%%
tag := "ch08-fm-classify"
%%%

`fourierMotzkinData` 对每个变量分类所有约束：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Core.lean:481-503]
def fourierMotzkinData (p : Problem) :
    Array FourierMotzkinData := Id.run do
  let n := p.numVars
  let mut data : Array FourierMotzkinData :=
    (List.range p.numVars).foldl
      (fun a i => a.push { var := i}) #[]
  for (_, f@⟨xs, s, _⟩) in p.constraints do
    for i in *...n do
      let x := Coeffs.get xs i
      data := data.modify i fun d =>
        if x = 0 then
          { d with irrelevant := f :: d.irrelevant }
        else Id.run do
          let s' := s.scale x
          let mut d' := d
          if s'.lowerBound.isSome then
            d' := { d' with
              lowerBounds := (f, x) :: d'.lowerBounds
              lowerExact := d'.lowerExact && x.natAbs = 1 }
          if s'.upperBound.isSome then
            d' := { d' with
              upperBounds := (f, x) :: d'.upperBounds
              upperExact := d'.upperExact && x.natAbs = 1 }
          return d'
  return data
```

对每个变量 `xᵢ`，约束被分为三类：

| 分类 | 条件 | 含义 |
|------|------|------|
| 下界 (lower) | `coeffs[i] > 0` | 给出 `xᵢ` 的下界 |
| 上界 (upper) | `coeffs[i] < 0` | 给出 `xᵢ` 的上界 |
| 无关 (irrelevant) | `coeffs[i] = 0` | 不含 `xᵢ` |

`FourierMotzkinData` 还记录 `lowerExact` 和 `upperExact`——所有系数是否为 ±1。如果是，消元是**精确的**（real shadow = dark shadow），不会引入伪解。

### 步骤 2：选择变量
%%%
tag := "ch08-fm-select"
%%%

`fourierMotzkinSelect` 选择消去"代价"最小的变量：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Core.lean:511-532]
def fourierMotzkinSelect (data : Array FourierMotzkinData) :
    MetaM FourierMotzkinData := do
  let data := data.filter fun d => ¬ d.isEmpty
  trace[omega] "Selecting variable to eliminate from \
    (idx, size, exact) triples:\n\
    {data.map fun d => (d.var, d.size, d.exact)}"
  let mut bestIdx := 0
  let mut bestSize := data[0]!.size
  let mut bestExact := data[0]!.exact
  if bestSize = 0 then return data[0]!
  for h : i in 1...data.size do
    let exact := data[i].exact
    let size := data[i].size
    if size = 0 || !bestExact && exact
        || (bestExact == exact) && size < bestSize then
      if size = 0 then return data[i]
      bestIdx := i
      bestExact := exact
      bestSize := size
  return data[bestIdx]!
```

优先级：

1. **size = 0**：所有约束都与该变量无关，免费消去
2. **精确消元**（exact = true）：所有系数为 ±1，不引入伪解
3. **最小乘积**：`|lower| × |upper|` 最小，生成最少新约束

### 步骤 3：消元
%%%
tag := "ch08-fm-eliminate"
%%%

对每对 (下界, 上界) 做线性组合消去选定变量：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Core.lean:538-548]
def fourierMotzkin (p : Problem) : MetaM Problem := do
  let data := p.fourierMotzkinData
  let ⟨_, irrelevant, lower, upper, _, _⟩ ←
    fourierMotzkinSelect data
  let mut r : Problem :=
    { assumptions := p.assumptions,
      eliminations := p.eliminations }
  for f in irrelevant do
    r := r.insertConstraint f
  for ⟨f, b⟩ in lower do
    for ⟨g, a⟩ in upper do
      r := r.addConstraint (Fact.combo a f (-b) g).tidy
  return r
```

新约束数 = `|lower| × |upper|`——这就是 FM 的复杂度瓶颈，每消一个变量约束数可能平方增长。但实际问题中约束通常稀疏，增长可控。

每个新约束都经过 `tidy` 规范化：**(1)** 令首个非零系数为正；**(2)** 除以所有系数的 GCD（常数项取整保持整数正确性）；**(3)** 如果已有同系数约束，用 `combine` 取更紧界。

## 约束插入与矛盾检测
%%%
tag := "ch08-constraint-insertion"
%%%

`addConstraint` 是约束入库的核心——同系数约束自动合并：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Core.lean:254-278]
def addConstraint (p : Problem) : Fact → Problem
  | f@⟨x, s, j⟩ =>
    if p.possible then
      match p.constraints[x]? with
      | none =>
        match s with
        | .trivial => p
        | _ => p.insertConstraint f
      | some ⟨x', t, k⟩ =>
        if h : x = x' then
          let r := s.combine t
          if r = t then p           -- 旧约束已经更紧
          else if r = s then
            p.insertConstraint ⟨x, s, j⟩  -- 新约束严格更紧
          else
            p.insertConstraint
              ⟨x, s.combine t, j.combine (h ▸ k)⟩
        else p
    else p
```

`insertConstraint` 在插入时检查矛盾——如果约束的 `isImpossible` 返回 `true`（`upperBound < lowerBound`），问题立即标记为不可满足：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Core.lean:231-248]
def insertConstraint (p : Problem) : Fact → Problem
  | f@⟨x, s, j⟩ =>
    if s.isImpossible then
      { p with
        possible := false
        proveFalse? := some (proveFalse j p.assumptions)
        explanation? := Thunk.mk fun _ => j.toString
        proveFalse?_spec := rfl }
    else
      { p with
        numVars := max p.numVars x.length
        constraints := p.constraints.insert x f
        proveFalse?_spec := p.proveFalse?_spec
        equalities :=
        if f.constraint.isExact then p.equalities.insert x
        else p.equalities }
```

# 证明构造
%%%
tag := "ch08-proof-construction"
%%%

omega 的证明构造采用**延迟策略**：先在 `Justification` 中记录推导树，只有找到矛盾后才转化为 Lean 证明项。

## Justification → Proof
%%%
tag := "ch08-justification-to-proof"
%%%

`Justification.proof` 递归地把推导树转化为 `Expr`：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Core.lean:117-124]
def proof (v : Expr) (assumptions : Array Proof) :
    Justification s c → Proof
  | assumption s c i => assumptions[i]!
  | @tidy s c j =>
      return tidyProof s c v (← proof v assumptions j)
  | @combine s t c j k =>
    return combineProof s t c v
      (← proof v assumptions j) (← proof v assumptions k)
  | @combo s t x y a j b k =>
    return comboProof s t a x b y v
      (← proof v assumptions j) (← proof v assumptions k)
  | @bmod m r i x j => do
      bmodProof m r i x v (← proof v assumptions j)
```

每个构造子对应一个证明项构造函数：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Core.lean:88-112]
def tidyProof (s : Constraint) (x : Coeffs)
    (v prf : Expr) : Expr :=
  mkApp4 (.const ``tidy_sat []) (toExpr s) (toExpr x) v prf

def combineProof (s t : Constraint) (x : Coeffs)
    (v ps pt : Expr) : Expr :=
  mkApp6 (.const ``Constraint.combine_sat' [])
    (toExpr s) (toExpr t) (toExpr x) v ps pt

def comboProof (s t : Constraint) (a : Int) (x : Coeffs)
    (b : Int) (y : Coeffs) (v px py : Expr) : Expr :=
  mkApp9 (.const ``combo_sat' [])
    (toExpr s) (toExpr t) (toExpr a) (toExpr x)
    (toExpr b) (toExpr y) v px py
```

## proveFalse：从矛盾到 False
%%%
tag := "ch08-prove-false"
%%%

最终的 `False` 证明通过 `Constraint.not_sat'_of_isImpossible` 引理构造：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Core.lean:218-225]
def proveFalse {s x} (j : Justification s x)
    (assumptions : Array Proof) : Proof := do
  let v := ← atomsCoeffs
  let prf ← j.proof v assumptions
  let x := toExpr x
  let s := toExpr s
  let impossible ←
    mkDecideProof (← mkEq
      (mkApp (.const ``Constraint.isImpossible []) s)
      (.const ``true []))
  return mkApp5
    (.const ``Constraint.not_sat'_of_isImpossible [])
    s impossible x v prf
```

逻辑链条：

1. `prf` 证明 `s.sat' x atoms`（矛盾约束在当前原子赋值下成立）
2. `impossible` 通过 `decide` 证明 `s.isImpossible = true`
3. `not_sat'_of_isImpossible` 结合两者导出 `False`

证明项通常非常大（嵌套的 `combo_sat'`、`tidy_sat` 和 `decide`），所以 `omegaTactic` 用 `mkAuxTheorem` 封装为辅助定义，避免拖慢后续类型检查。

# OmegaM monad
%%%
tag := "ch08-omega-monad"
%%%

omega 使用多层 monad 栈管理状态。

## Monad 栈结构
%%%
tag := "ch08-monad-stack"
%%%

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/OmegaM.lean:49-71]
structure Context where
  cfg : OmegaConfig

structure State where
  atoms : Std.HashMap Expr Nat := {}

abbrev OmegaM' :=
  StateRefT State (ReaderT Context CanonM)

@[expose] def Cache : Type :=
  Std.HashMap Expr (LinearCombo × OmegaM' Expr)

abbrev OmegaM := StateRefT Cache OmegaM'
```

两层状态分别管理：**State.atoms**（`Expr → Nat` 映射，通过 `CanonM` 保证 defeq 的表达式映射到同一编号）和 **Cache**（子表达式 → `(LinearCombo, Proof)` 的缓存，避免重复分析）。

整个 monad 栈通过 `OmegaM.run` 初始化和运行：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/OmegaM.lean:74-75]
def OmegaM.run (m : OmegaM α) (cfg : OmegaConfig) : MetaM α :=
  m.run' (∅ : Std.HashMap ..) |>.run' {} { cfg } |>.run'
```

## 原子管理：lookup
%%%
tag := "ch08-lookup"
%%%

当遇到无法进一步分解的表达式时，omega 把它注册为一个**原子**：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/OmegaM.lean:247-260]
def lookup (e : Expr) :
    OmegaM (Nat × Option (List Expr)) := do
  let c ← getThe State
  let e ← canon e
  match c.atoms[e]? with
  | some i => return (i, none)
  | none =>
  trace[omega] "New atom: {e}"
  let facts ← analyzeAtom e
  if ← isTracingEnabledFor `omega then
    unless facts.isEmpty do
      trace[omega] "New facts: \
        {← facts.mapM fun e => inferType e}"
  let i ← modifyGetThe State fun c =>
    (c.atoms.size,
     { c with atoms := c.atoms.insert e c.atoms.size })
  return (i, some facts)
```

`canon e` 先做规范化（处理 definitional equality），然后查找。如果是新原子，调用 `analyzeAtom` 生成附加约束。

## analyzeAtom：原子约束生成
%%%
tag := "ch08-analyze-atom"
%%%

`analyzeAtom` 根据原子的结构自动生成额外的线性约束：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/OmegaM.lean:166-235]
def analyzeAtom (e : Expr) : OmegaM (List Expr) := do
  match e.getAppFnArgs with
  | (``Nat.cast, #[.const ``Int [], _, e']) =>
    -- ↑(x : Nat) 非负
    let mut r :=
      [Expr.app (.const ``Int.natCast_nonneg []) e']
    match (← cfg).splitNatSub, e'.getAppFnArgs with
      | true, (``HSub.hSub, #[_, _, _, _, a, b]) =>
        -- ↑(a - b : Nat) 二分
        r := r.insert
          (mkApp2 (.const ``Int.ofNat_sub_dichotomy []) a b)
      | _, (``Int.natAbs, #[x]) =>
        r := r.insert
          (mkApp (.const ``Int.le_natAbs []) x)
        r := r.insert
          (mkApp (.const ``Int.neg_le_natAbs []) x)
      | _, (``Fin.val, #[n, i]) =>
        r := r.insert (mkApp2 (.const ``Fin.isLt []) n i)
      ...
    return r
  | (``HDiv.hDiv, #[_, _, _, _, x, k]) =>
    -- x / k 的界约束
    match natCast? k with
    | some _ =>
      pure [mkApp3 (.const ``Int.mul_ediv_self_le [])
              x k ...,
            mkApp3 (.const ``Int.lt_mul_ediv_self_add [])
              x k ...]
    ...
  | (``Min.min, #[_, _, x, y]) =>
    pure [mkApp2 (.const ``Int.min_le_left []) x y,
          mkApp2 (.const ``Int.min_le_right []) x y]
  | (``Max.max, #[_, _, x, y]) =>
    pure [mkApp2 (.const ``Int.le_max_left []) x y,
          mkApp2 (.const ``Int.le_max_right []) x y]
  ...
```

| 原子类型 | 生成的约束 |
|----------|-----------|
| `↑(x : Nat)` | `0 ≤ ↑x` |
| `x / k` | `k * (x/k) ≤ x < k * (x/k) + k` |
| `x % k` | `0 ≤ x % k < k` |
| `↑(a - b : Nat)` | 二分：`b ≤ a ∧ result = a - b` 或 `a < b ∧ result = 0` |
| `Int.natAbs a` | `a ≤ natAbs a` 且 `-a ≤ natAbs a` |
| `min a b` | `min a b ≤ a` 且 `min a b ≤ b` |
| `max a b` | `a ≤ max a b` 且 `b ≤ max a b` |
| `Fin.val i` | `i.val < n` |

这些自动生成的约束是 omega 能处理 Nat 减法、绝对值、min/max 等非线性构造的关键——它们把超出线性算术的构造"线性化"。

## 缓存与事务
%%%
tag := "ch08-cache-transactions"
%%%

`asLinearCombo` 使用缓存避免重复分析同一子表达式：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Frontend.lean:105-114]
partial def asLinearCombo (e : Expr) :
    OmegaM (LinearCombo × OmegaM Expr × List Expr) := do
  let cache ← get
  match cache.get? e with
  | some (lc, prf) =>
    return (lc, prf, ∅)
  | none =>
    let (lc, proof, r) ← asLinearComboImpl e
    modifyThe Cache fun cache =>
      (cache.insert e (lc, proof.run' cache))
    pure (lc, proof, r)
```

`commitWhen` 提供事务性操作——用于乘法处理时的试探性分析。如果两个因子都有非零系数（非线性乘法），回滚状态，把整个乘积当作原子：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/OmegaM.lean:92-99]
def commitWhen (t : OmegaM (α × Bool)) : OmegaM α := do
  let state ← getThe State
  let cache ← getThe Cache
  let (a, r) ← t
  if !r then do
    modifyThe State fun _ => state
    modifyThe Cache fun _ => cache
  pure a
```

# omegaImpl 与析取处理
%%%
tag := "ch08-omega-impl"
%%%

`omegaImpl` 是 omega 的算法主循环：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Frontend.lean:649-664]
partial def omegaImpl (m : MetaProblem) : OmegaM Expr := do
  let (m, _) ← m.processFacts
  guard m.facts.isEmpty
  let p := m.problem
  trace[omega] "Extracted linear arithmetic problem:\n\
    Atoms: {← atomsList}\n{p}"
  let p' ← if p.possible then p.elimination else pure p
  trace[omega] "After elimination:\n\
    Atoms: {← atomsList}\n{p'}"
  match h₁ : p'.possible, h₂ : p'.proveFalse?,
      p'.proveFalse?_spec with
  | true, _, _ =>
    splitDisjunction m
  | false, .some prf, _ =>
    trace[omega] "Justification:\n{p'.explanation?.get}"
    let prf ← instantiateMVars (← prf)
    return prf
  | false, none, h₃ => by simp [h₁, h₂] at h₃
```

流程：**(1)** 预处理所有假设（`processFacts`）；**(2)** 消元求解（`elimination`）；**(3)** 如果发现矛盾，返回 `False` 证明；如果未发现矛盾，尝试 case split。

析取处理通过 `splitDisjunction`——逐个拆分析取，在每个分支中递归调用 `omegaImpl`：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Frontend.lean:620-646]
partial def splitDisjunction (m : MetaProblem) :
    OmegaM Expr := do
  match m.disjunctions with
  | [] => throwError "omega could not prove the goal:\n\
      {← formatErrorMessage m.problem}"
  | h :: t => do
    let hType ← whnfD (← inferType h)
    let_expr Or hType₁ hType₂ := hType | ...
    -- 分支 1：假设 h₁ : P
    let p?₁ ← withoutModifyingState do
      withLocalDeclD `h₁ hType₁ fun h₁ => do
        let m₁ := { m with facts := [h₁], disjunctions := t }
        let (m₁, n) ← m₁.processFacts
        if 0 < n then
          some (← omegaImpl m₁ >>= mkLambdaFVars #[h₁])
        else none
    -- 分支 2：假设 h₂ : Q（类似）
    ...
    -- 合并：Or.elim h proof₁ proof₂
```

**优化**：尝试分支 1 时使用 `withoutModifyingState`——如果分支 1 没有贡献新约束（`n = 0`），跳过这个析取。这避免了无用的 case split。

析取处理是递归的——每个分支内可能产生新析取需要进一步 split，最坏情况下是指数级的。这就是为什么 Nat 减法太多时 omega 会超时。

# 调试手册
%%%
tag := "ch08-debugging"
%%%

## trace 开关
%%%
tag := "ch08-trace"
%%%

omega 提供详细的 trace 输出：

```
set_option trace.omega true in
example : ... := by omega
```

trace 输出涵盖：

- 假设分析：`"adding fact: ..."`
- 新原子发现：`"New atom: ..."`
- 自动生成的约束：`"New facts: ..."`
- 提取的线性问题：`"Extracted linear arithmetic problem: ..."`
- 变量选择：`"Selecting variable to eliminate from ..."`
- 消元后的问题：`"After elimination: ..."`
- Case split：`"Case splitting on ..."`
- 矛盾发现：`"omega found a contradiction"`

## 常见失败模式
%%%
tag := "ch08-failure-modes"
%%%

**模式 1：omega 成功但很慢**

症状：trace 中出现大量嵌套 case split。原因：Nat 减法或 min/max 引入了过多二分（n 个产生 2^n 种情况）。修复：手动 `have` 确定不等式后再 `omega`；或 `omega (config := { splitNatSub := false })`。

**模式 2：omega 报 "could not prove the goal"**

症状：报错并给出可能的反例。原因：目标涉及非线性乘法、缺少假设、或 `a * b` 与 `b * a` 被视为不同原子。修复：检查反例，补充假设或改用 `nlinarith`。

**模式 3：非线性项被当作原子**

症状：`x * y ≤ z * w` 中 omega 把 `x * y` 和 `z * w` 当作独立原子。原因：`asLinearCombo` 只在一个因子是常数时展开乘法。修复：用 `nlinarith` 或手动 `have`。

**模式 4：Fin 的模算术**

症状：`Fin n` 上的加法不被正确处理。原因：omega 把 `Fin.val` 提升到 Nat 但不处理模算术。修复：`simp [Fin.val_add]` 先展开，再 `omega`。

**模式 5：未展开的定义**

症状：目标"看起来"是线性的但 omega 失败。原因：自定义定义未展开。修复：`unfold myDef` 或 `simp only [myDef]` 后再 `omega`。

## 错误信息解读
%%%
tag := "ch08-error-messages"
%%%

omega 失败时的错误信息格式：

```
omega could not prove the goal:
a possible counterexample may satisfy the constraints
  a ≥ 0
  -a + b ≤ 1
where
  a := ↑n
  b := ↑m
```

"可能反例"是从剩余约束中推导的赋值——展示的是"omega 看到的世界"。它能帮你判断是缺假设、目标不可证、还是预处理丢失了关键信息。注意这只是线性约束系统的满足赋值，不一定是原始命题的真反例。

错误信息的生成逻辑在 `formatErrorMessage` 中：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega/Frontend.lean:533-548]
def formatErrorMessage (p : Problem) :
    OmegaM MessageData := do
  if p.possible then
    if p.isEmpty then
      return m!"No usable constraints found. ..."
    else
      let as ← atoms
      return .ofLazyM (es := as) do
        let mask ← mentioned as p.constraints
        let names ← varNames mask
        return m!"a possible counterexample may satisfy \
          the constraints\n"
          ++ m!"{prettyConstraints names p.constraints}\n\
               where\n{prettyAtoms names as mask}"
  else
    return "it is trivially solvable"
```

如果看到 `"No usable constraints found"`，说明 omega 完全无法从假设和目标中提取线性算术信息——通常是类型不匹配或定义未展开。

# Omega Test 的理论背景
%%%
tag := "ch08-theory"
%%%

omega tactic 实现的是 Omega Test 的变种。经典 Omega Test 基于三个"影子"（shadow）：

| 影子 | 含义 | Lean 实现 |
|------|------|-----------|
| Real shadow | Fourier-Motzkin 消元（当作实数） | 已实现 |
| Dark shadow | 加强的 FM 约束（考虑整数间隙） | 未实现 |
| Grey shadow | 枚举整数解候选 | 未实现 |

Real shadow 是必要条件——如果不可满足，原问题一定不可满足。但 real shadow 可满足不代表存在整数解——当系数不全为 ±1 时，FM 消元可能引入非整数解。

**为什么通常够用**：实际编程验证中，大多数线性约束的系数都是 ±1 或小常数（如数组索引界 `0 ≤ i < n`）。这种情况下 real shadow 就足够了。omega 的变量选择启发式也优先选精确消元（系数为 ±1），进一步保证了 real shadow 的充分性。

源码中 `Lean/Elab/Tactic/Omega.lean` 的模块文档详细讨论了三个影子的理论：

```
-- [Lean 4 v4.30.0-rc1, Lean/Elab/Tactic/Omega.lean:101-166]
-- 实现注释节选：
-- Currently we do not implement either the dark or grey shadows,
-- and thus if the real shadow is satisfiable we must fail...
-- In practical problems, it appears to be relatively rare that
-- we fail because of not handling the dark and grey shadows.
-- Fortunately, in many cases it is possible to choose a variable
-- to eliminate such that the real and dark shadows coincide,
-- and the grey shadows are empty.
```

# 练习
%%%
tag := "ch08-exercises"
%%%

## 练习 1：基础线性推理
%%%
tag := "ch08-exercise-1"
%%%

判断以下哪些目标 `omega` 能直接证明，并尝试证明：

```
-- (a)
example (n : Nat) (h : n > 0) : 2 * n ≥ 2 := by
  sorry

-- (b)
example (a b : Int) (h1 : a + b = 10) (h2 : a - b = 4) :
    a = 7 := by
  sorry

-- (c) 包含变量乘法
example (n : Nat) : n * (n + 1) / 2 ≥ 0 := by
  sorry

-- (d)
example (x : Int) (h : x % 3 = 0) :
    x % 6 = 0 ∨ x % 6 = 3 := by
  sorry
```

提示：(a) 和 (d) 是线性的，omega 能直接处理；(b) 检查解是否正确（a = 7, b = 3）；(c) 包含 `n * (n + 1)` 变量乘法。

## 练习 2：诊断失败
%%%
tag := "ch08-exercise-2"
%%%

以下每个 `omega` 调用都会失败。解释失败原因，给出修复方案：

```
-- (a) 非线性项
example (n : Nat) : n ^ 2 ≥ 0 := by
  omega  -- ✗

-- (b) 未展开的定义
def triple (n : Nat) := 3 * n
example (n : Nat) : triple n ≥ n := by
  omega  -- ✗

-- (c) 缺少前置条件
example (n : Nat) : n - 1 + 1 = n := by
  omega  -- ✗
```

提示：(a) 用 `positivity` 或 `exact Nat.zero_le _`；(b) 先 `unfold triple`；(c) 需要 `n ≥ 1` 假设。

## 练习 3：trace 分析
%%%
tag := "ch08-exercise-3"
%%%

对以下目标开启 `set_option trace.omega true`，观察 trace 输出，回答问题：

```
example (a b : Nat) (h : a + b = 10) : a ≤ 10 := by
  omega
```

问题：

1. omega 发现了哪些原子？
2. 预处理后生成了哪些约束？
3. 消元过程中选择了哪个变量消去？

## 练习 4：omega 与 linarith 的边界
%%%
tag := "ch08-exercise-4"
%%%

找出一个命题使得 `omega` 能证明但 `linarith` 不能，以及一个命题使得 `linarith` 能证明但 `omega` 不能。解释原因。

提示：考虑整除性（omega 的强项）和实数域（linarith 的强项）。
