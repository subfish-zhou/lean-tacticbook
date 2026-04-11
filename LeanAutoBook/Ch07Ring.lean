import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch07Ring"

#doc (Manual) "ring 和 `ring_nf`：代数范式化" =>
%%%
file := "Ch07Ring"
tag := "ch07-ring"
%%%

**本章目标**：前半章掌握 `ring` 家族（`ring` / `ring_nf` / `ring1`）的用法、配置与调试；后半章从 Mathlib 真实源码层面拆解 ring 的完整实现——入口调用链、多项式范式数据结构、规范化算法、系数计算、类型提升——面向想深入理解内部机制的读者。

# 用法详解
%%%
tag := "ch07-usage"
%%%

## ring 解决什么问题
%%%
tag := "ch07-what-ring-solves"
%%%

`ring` 证明**交换（半）环**上的多项式恒等式。它是一个**完备决策过程**：对于交换环公理可推出的任何多项式等式，`ring` 一定能判定。

```
-- 基础展开
example (x y : ℤ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring
  -- ✅ ring 把两边规范化为同一个 Horner 范式，得到 rfl

-- 因式分解方向同样成立
example (a b : ℝ) : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by
  ring
  -- ✅ 方向无关：ring 总是规范化到唯一范式再比较

-- 多变量高次
example (a b c : ℚ) :
    (a + b + c) ^ 3 =
      a ^ 3 + b ^ 3 + c ^ 3 +
      3 * (a ^ 2 * b + a ^ 2 * c + b ^ 2 * a + b ^ 2 * c + c ^ 2 * a + c ^ 2 * b) +
      6 * a * b * c := by
  ring
  -- ✅ 变量数和次数不影响正确性，只影响性能

-- 变量指数
example (n : ℕ) (m : ℤ) : 2^(n+1) * m = 2 * 2^n * m := by ring
```

`ring` 的三条核心边界：

1. **不处理序**——`ring` 不能证明 `x + 1 > x`，那是 `linarith` / `positivity` 的领域
2. **不展开函数**——`ring` 把 `sin x`、`f n` 等当作不透明原子
3. **不处理除法约分**——`x / y * y = x` 需要 `y ≠ 0`，超出环公理

## ring 家族一览
%%%
tag := "ch07-ring-family"
%%%

- `ring`：尝试 `ring1` 关闭目标；若失败回退到 `ring_nf` 并提示用户
- `ring1`：直接证明等式目标（不做 fallback）
- `ring_nf`：只做范式化，不要求等式两边相等；可作用于假设
- `ring!` / `ring1!` / `ring_nf!`：使用更激进的可约性设置（`.default` 代替 `.reducible`）

`ring` 和 `ring_nf` 都同时支持 tactic 模式和 conv 模式。

## ring\_nf：只做范式化
%%%
tag := "ch07-ring-nf"
%%%

`ring_nf` 执行与 `ring` 相同的规范化过程，但**不要求两边相等**。它把目标（或假设）中的代数子表达式化简为范式形式。

```
-- 化简目标
example (x : ℤ) : (x + 1) ^ 2 - 1 = x ^ 2 + 2 * x := by
  ring_nf
  -- ring_nf 把两边分别化简为范式
  -- 如果化简后两边相同，目标自动关闭

-- 化简假设
example (x : ℤ) (h : (x + 1) ^ 2 = 9) : x ^ 2 + 2 * x = 8 := by
  ring_nf at h
  -- h 从 (x + 1) ^ 2 = 9 变为 x ^ 2 + 2 * x + 1 = 9
  linarith
```

**何时用 `ring_nf` 而非 `ring`**：

- 目标不是等式但含有环表达式——用 `ring_nf` 化简后交给其他 tactic
- 需要化简假设中的代数表达式——`ring_nf at h`
- 探索性使用：只想看化简结果

经验法则：如果等式纯粹是代数恒等式，先用 `ring`。失败后再考虑 `ring_nf` + 其他 tactic 的组合。

## ring1：底层等式证明器
%%%
tag := "ch07-ring1"
%%%

`ring1` 是 `ring` 的核心——只接受等式目标，不做 fallback。`ring` 宏在内部先调用 `ring1`，失败后才回退到 `ring_nf`。直接使用 `ring1` 的场景较少，主要用于元编程或需要精确控制行为时。

## 支持的代数结构
%%%
tag := "ch07-supported-structures"
%%%

- **交换环 `CommRing`**（`ℤ`, `ℚ`, `ℝ`, `ℂ`, `ZMod n`）：完整支持
- **交换半环 `CommSemiring`**（`ℕ`）：加法和乘法正常工作；减法受限（截断减法不满足环公理）
- **域 `Field`**（`ℚ`, `ℝ`, `ℂ`）：不处理 `a/a = 1` 约分（用 `field_simp` + `ring`）
- **`ℕ+` 等非半环类型**：通过 `CSLift` 类型提升机制支持（见源码拆解部分）

**ℕ 上的减法陷阱**：

```
-- ✅ 没有减法，ring 正常工作
example (n : ℕ) : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring

-- ❌ 有减法，ring 失败
-- example (n : ℕ) : (n + 1) - 1 = n := by ring  -- fails
-- 正确做法：用 omega
example (n : ℕ) : (n + 1) - 1 = n := by omega
```

**实践规则**：在 `ℕ` 上，只要目标含有减法，不要首选 `ring`——优先考虑 `omega` 或先转换到 `ℤ`。

## 常见搭档 tactic
%%%
tag := "ch07-companion-tactics"
%%%

**`linear_combination`**——`ring` 最重要的搭档。给定等式假设，找到系数使目标成为这些假设的线性组合 + `ring` 恒等式：

```
example (a b : ℤ) (h1 : a + b = 5) (h2 : a - b = 1) : a = 3 := by
  linear_combination (h1 + h2) / 2
```

**`field_simp` + `ring`**——处理含分式的等式：

```
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a + 1 / b = (a + b) / (a * b) := by
  field_simp; ring
```

**`push_cast` + `ring`**——类型转换会阻碍 `ring`，`push_cast` 把 cast 推到最内层：

```
example (m n : ℕ) : ((m + n : ℕ) : ℤ) = (m : ℤ) + (n : ℤ) := by
  push_cast; ring
```

## 常见失败模式与诊断
%%%
tag := "ch07-failure-diagnosis"
%%%

当 `ring` 失败时，按以下顺序检查：

```
ring 失败
  │
  ├─ 目标是不等式？ ──→ 用 linarith / nlinarith / positivity
  │
  ├─ 等式依赖假设？ ──→ 用 linear_combination / subst / rw 先处理
  │
  ├─ 含有函数调用？ ──→ 用 simp 先展开，或手动 rw 相关引理
  │
  ├─ ℕ 上有减法？   ──→ 用 omega 或转换到 ℤ
  │
  ├─ 含有除法？     ──→ 用 field_simp 先消分母
  │
  ├─ 类型 coercion？ ──→ 用 push_cast / pull_cast 统一类型
  │
  └─ ring 失败但 ring! 成功？ ──→ 透明度问题，见下文
```

**透明度问题**：`ring` 使用 `.reducible` 透明度，只展开 `@[reducible]` 定义；`ring!` 使用 `.default` 透明度，展开更多定义。如果等式涉及非 `@[reducible]` 的定义（如 `def myTwo : ℤ := 2`），`ring` 无法"看穿"它，但 `ring!` 可以。

```
def myTwo : ℤ := 2
example (x : ℤ) : myTwo * x = x + x := by ring!  -- ring 失败，ring! 成功
```

**缺实例报错**：错误信息包含 `failed to synthesize CommSemiring` 时，确认类型确实有对应的代数结构实例。如果类型可以嵌入到有实例的类型中，考虑提供 `CSLift` 实例。

# 源码全景：文件结构与调用链
%%%
tag := "ch07-source-overview"
%%%

> **源码版本说明**：以下引用基于 Mathlib 的 `Mathlib/Tactic/Ring/` 目录。`ring` 完全在 Mathlib 中实现，不依赖 Lean 核心的 tactic 框架（不同于 `simp`）。

## 文件结构
%%%
tag := "ch07-file-structure"
%%%

- `Ring/Common.lean`（~1340 行）：核心算法——数据结构、规范化函数（`eval`/`evalAdd`/`evalMul`/`evalPow`）、`RingCompute` 接口、`Cache`
- `Ring/Basic.lean`（~605 行）：`RatCoeff` 有理系数处理、`proveEq`/`ringCore` 入口、`ring1` 注册、`CSLift` 类型提升
- `Ring/RingNF.lean`（~236 行）：`ring` 宏定义、`ring_nf` tactic、`cleanup` 清理例程
- `Ring/Compare.lean`（~259 行）：不等式自动化（`proveLE`/`proveLT`），用于 `linear_combination` 的 discharger
- `Ring/PNat.lean`（~52 行）：`CSLift ℕ+ ℕ` 实例

与 `simp` 的关键区别：`simp` 是**通用重写引擎**（在 Lean 核心实现），而 `ring` 是**特化的判定过程**（在 Mathlib 实现）。`ring` 不做重写搜索，而是把等式两边**规范化**为同一个范式，然后比较。

## 入口调用链：从 `ring` 到范式比较
%%%
tag := "ch07-call-chain"
%%%

当你在 tactic 模式中写下 `ring`，经过以下调用链：

```
用户写 `ring`
  → ring 宏展开为 `first | ring1 | try_this ring_nf ...`
    → ring1 tactic (Tactic 层, TacticM)
      → proveEq (Meta 层入口)
        → ringCore (构建 Cache + 调用 eval)
          → Common.eval e₁ 和 Common.eval e₂ (核心规范化)
            → 比较两个范式是否相等 (ExSum.eq)
              → 返回证明 proof : e₁ = e₂
```

## `ring` 宏
%%%
tag := "ch07-ring-macro"
%%%

`ring` 本身是一个**宏**（不是 elaborator），展开为先尝试 `ring1` 关闭目标，失败后回退到 `ring_nf` 并用 `try_this` 提示用户：

```
-- [Mathlib, Mathlib/Tactic/Ring/RingNF.lean:196-207]
macro (name := ring) "ring" : tactic =>
  `(tactic| first | ring1 | try_this ring_nf
  "\n\nThe `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
  \nNote that `ring` works primarily in *commutative* rings. \
  If you have a noncommutative ring, abelian group or module, consider using \
  `noncomm_ring`, `abel` or `module` instead.")
@[tactic_alt ring] macro "ring!" : tactic =>
  `(tactic| first | ring1! | try_this ring_nf!
  "\n\nThe `ring!` tactic failed to close the goal. Use `ring_nf!` to obtain a normal form.
  \nNote that `ring!` works primarily in *commutative* rings. \
  If you have a noncommutative ring, abelian group or module, consider using \
  `noncomm_ring`, `abel` or `module` instead.")
```

这里体现了 `ring` 与 `ring_nf` 的精准分工：**`ring` = 规范化 + 关闭目标**，**`ring_nf` = 规范化 + 回写表达式**。

## `ring1` tactic 注册
%%%
tag := "ch07-ring1-registration"
%%%

```
-- [Mathlib, Mathlib/Tactic/Ring/Basic.lean:599-602]
elab (name := ring1) "ring1" tk:"!"? : tactic => liftMetaMAtMain fun g ↦ do
  AtomM.run (if tk.isSome then .default else .reducible) (proveEq g)

@[tactic_alt ring1] macro "ring1!" : tactic => `(tactic| ring1 !)
```

关键细节：

- **`liftMetaMAtMain`**：从 `TacticM` 提升到 `MetaM`，拿到当前主目标 `g : MVarId`
- **`AtomM.run`**：进入 `AtomM` monad——这是 `ring` 的专用工作 monad，管理**原子**（不可分解的子表达式）的编号和状态
- **`tk:"!"?`**：`ring1!` 时使用 `.default` 可约性（更激进）；普通 `ring1` 使用 `.reducible`（更保守）

## `proveEq`：Meta 层入口
%%%
tag := "ch07-prove-eq"
%%%

```
-- [Mathlib, Mathlib/Tactic/Ring/Basic.lean:551-575]
def proveEq (g : MVarId) : AtomM Unit := do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
    | throwError "ring failed: not an equality"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  let sα ←
    try Except.ok <$> synthInstanceQ q(CommSemiring $α)
    catch e => pure (.error e)
  have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
  let eq ← match sα with
  | .ok sα => ringCore sα e₁ e₂
  | .error e =>
    let β ← mkFreshExprMVarQ q(Type v)
    let e₁' ← mkFreshExprMVarQ q($β)
    let e₂' ← mkFreshExprMVarQ q($β)
    let (sβ, (pf : Q($e₁' = $e₂' → $e₁ = $e₂))) ← try
      let _l ← synthInstanceQ q(CSLift $α $β)
      let sβ ← synthInstanceQ q(CommSemiring $β)
      let _ ← synthInstanceQ q(CSLiftVal $e₁ $e₁')
      let _ ← synthInstanceQ q(CSLiftVal $e₂ $e₂')
      pure (sβ, q(of_lift (a := $e₁) (b := $e₂)))
    catch _ => throw e
    pure q($pf $(← ringCore sβ e₁' e₂'))
  g.assign eq
```

步骤解读：

1. **提取等式**：用 `Expr.eq?` 从目标类型中提取 `α`、`e₁`、`e₂`。如果目标不是等式，直接报错。
2. **推断 universe**：需要知道 `α : Type v` 的 universe level `v`。
3. **合成实例**：尝试为 `α` 合成 `CommSemiring` 实例——这是 `ring` 工作的最低要求。
4. **分支**：如果合成成功，走路径 A（`ringCore` 直接规范化）；否则尝试路径 B（通过 `CSLift` 提升到交换半环类型，见"类型提升"一节）。

## `ringCore`：核心证明生成
%%%
tag := "ch07-ring-core"
%%%

```
-- [Mathlib, Mathlib/Tactic/Ring/Basic.lean:577-589]
where
  ringCore {v : Level} {α : Q(Type v)} (sα : Q(CommSemiring $α))
      (e₁ e₂ : Q($α)) : AtomM Q($e₁ = $e₂) := do
    let c ← Common.mkCache sα
    profileitM Exception "ring" (← getOptions) do
      let ⟨a, va, pa⟩ ← Common.eval rcℕ (ringCompute c) c e₁
      let ⟨b, vb, pb⟩ ← Common.eval rcℕ (ringCompute c) c e₂
      unless va.eq rcℕ (ringCompute c) vb do
        let g ← mkFreshExprMVar (← (← ringCleanupRef.get) q($a = $b))
        throwError "ring failed, ring expressions not equal\n{g.mvarId!}"
      have : $a =Q $b := ⟨⟩
      return q(of_eq $pa $pb)
```

这是 `ring` 的核心循环，四步：

1. **构建 Cache**：缓存 `CommRing`、`Semifield`、`CharZero` 等可选实例，避免重复合成
2. **规范化**：对 `e₁` 和 `e₂` 分别调用 `Common.eval`，得到范式表达式 `a`/`b`、范式数据 `va`/`vb`、等式证明 `pa : e₁ = a`/`pb : e₂ = b`
3. **比较**：用 `va.eq vb` 判断两个范式是否结构相等。如果不等，报错并显示规范化后的残余目标 `a = b`
4. **构造证明**：范式相等意味着 `a` 和 `b` 是同一个 `Qq` 表达式（definitionally equal），用 `of_eq pa pb` 拼出 `e₁ = e₂` 的证明

`of_eq` 的签名是 `e₁ = c → e₂ = c → e₁ = e₂`。当 `a =Q b`（即 `a` 和 `b` 在 type checker 中 definitionally equal），`pa` 和 `pb` 可以直接拼成 `e₁ = e₂`，无需额外的等式证明。

# 核心数据结构：ExBase / ExProd / ExSum
%%%
tag := "ch07-data-structures"
%%%

`ring` 的核心思想是把任意环表达式规范化为**有序多项式范式**。这一范式由三个互相递归的归纳类型定义。

## 三个类型族
%%%
tag := "ch07-three-type-families"
%%%

```
-- [Mathlib, Mathlib/Tactic/Ring/Common.lean:208-256]
mutual

-- 基：原子或嵌套的和
meta inductive ExBase {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) → Type)
    (sα : Q(CommSemiring $α)) : (e : Q($α)) → Type
  | atom {e} (id : ℕ) : ExBase BaseType sα e
  | sum {e} (_ : ExSum BaseType sα e) : ExBase BaseType sα e

-- 积（单项式）：系数 × 幂的乘积链
meta inductive ExProd {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) → Type)
    (sα : Q(CommSemiring $α)) : (e : Q($α)) → Type
  | const {e : Q($α)} (value : BaseType e) : ExProd BaseType sα e
  | mul {x : Q($α)} {e : Q(ℕ)} {b : Q($α)} :
    ExBase BaseType sα x → ExProdNat e → ExProd BaseType sα b →
      ExProd BaseType sα q($x ^ $e * $b)

-- 和（多项式）：单项式的有序链表
meta inductive ExSum {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) → Type)
    (sα : Q(CommSemiring $α)) : (e : Q($α)) → Type
  | zero : ExSum BaseType sα q(0 : $α)
  | add {a b : Q($α)} :
    ExProd BaseType sα a → ExSum BaseType sα b → ExSum BaseType sα q($a + $b)

end
```

类似地，自然数版本 `ExBaseNat` / `ExProdNat` / `ExSumNat` 专门用于表示**指数**（指数总是自然数）。它们与主版本结构相同但独立定义，因为 `BaseType` 是参数而非索引——如果放在索引位置，`ExProd` 的 universe 会从 `Type` 升到 `Type 1`，而 Lean 的核心 monad 类型不支持 `Type 1` 中的计算。

```
-- [Mathlib, Mathlib/Tactic/Ring/Common.lean:145-200]
mutual

meta inductive ExBaseNat : (e : Q(ℕ)) → Type
  | atom {e} (id : ℕ) : ExBaseNat e
  | sum {e} (_ : ExSumNat e) : ExBaseNat e

meta inductive ExProdNat : (e : Q(ℕ)) → Type
  | const {e : Q(ℕ)} (value : btℕ e) : ExProdNat e
  | mul {x : Q(ℕ)} {e : Q(ℕ)} {b : Q(ℕ)} :
    ExBaseNat x → ExProdNat e → ExProdNat b → ExProdNat q($x ^ $e * $b)

meta inductive ExSumNat : (e : Q(ℕ)) → Type
  | zero : ExSumNat q(0)
  | add {a b : Q(ℕ)} : ExProdNat a → ExSumNat b → ExSumNat q($a + $b)

end
```

## 范式的直觉理解
%%%
tag := "ch07-normal-form-intuition"
%%%

以 `(x + y)² + 3xy` 为例，展开为 `x² + 2xy + y² + 3xy = x² + 5xy + y²`：

```
ExSum                                    -- 多项式 = 单项式链表
  .add                                   -- 第一项: x² · 1
    (ExProd.mul                          --   单项式 = base^exp * tail
      (ExBase.atom 0)                    --   base = x (原子 #0)
      (ExProdNat: 2)                     --   exp = 2
      (ExProd.const 1))                  --   tail = 系数 1
    .add                                 -- 第二项: x¹ · y¹ · 5
      (ExProd.mul
        (ExBase.atom 0)                  --   base = x
        (ExProdNat: 1)                   --   exp = 1
        (ExProd.mul
          (ExBase.atom 1)                --   base = y (原子 #1)
          (ExProdNat: 1)                 --   exp = 1
          (ExProd.const 5)))             --   系数 5
      .add                               -- 第三项: y² · 1
        (ExProd.mul
          (ExBase.atom 1)                --   base = y
          (ExProdNat: 2)                 --   exp = 2
          (ExProd.const 1))
        .zero                            -- 结束
```

## 范式的规范性保证
%%%
tag := "ch07-canonicity-invariants"
%%%

范式之所以"规范"，靠的是以下不变量：

**单项式排序**：`ExSum` 中的单项式按**全序**排列。排序规则由 `ExProd.cmp` 定义：

```
-- [Mathlib, Mathlib/Tactic/Ring/Common.lean:462-467]
partial def ExProd.cmp {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)}
    (rc : RingCompare bt) {a b : Q($α)} :
    ExProd bt sα a → ExProd bt sα b → Ordering
  | .const i, .const j => rc.compare i j
  | .mul a₁ a₂ a₃, .mul b₁ b₂ b₃ =>
    (a₁.cmp rc b₁).then (a₂.toExProd.2.cmp rcℕ b₂.toExProd.2) |>.then (a₃.cmp rc b₃)
  | .const _, .mul .. => .lt
  | .mul .., .const _ => .gt
```

**基排序**：`ExBase.cmp` 对原子按编号排序，原子 < 嵌套和：

```
-- [Mathlib, Mathlib/Tactic/Ring/Common.lean:453-459]
partial def ExBase.cmp {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)}
    (rc : RingCompare bt) {a b : Q($α)} :
    ExBase bt sα a → ExBase bt sα b → Ordering
  | .atom i, .atom j => compare i j
  | .sum a, .sum b => a.cmp rc b
  | .atom .., .sum .. => .lt
  | .sum .., .atom .. => .gt
```

**不变量清单**：

1. `ExSum` 中的单项式按 `ExProd.cmp` 全序排列
2. 同类项（相同基和指数模式）的系数已合并
3. 零系数项已删除
4. 每个单项式内部，`ExProd.mul` 链按基递增有序
5. 指数本身已规范化为 `ExSumNat`/`ExProdNat`
6. 每步操作附带等式证明（`Result` 类型）

这些不变量保证了**同一个环表达式有且仅有一种范式表示**——这是 `ring` 正确性的基础。

## `Result` 类型
%%%
tag := "ch07-result-type"
%%%

```
-- [Mathlib, Mathlib/Tactic/Ring/Common.lean:265-271]
structure Result {α : Q(Type u)} (E : Q($α) → Type*) (e : Q($α)) where
  expr : Q($α)         -- 规范化后的表达式
  val : E expr          -- 范式数据结构
  proof : Q($e = $expr) -- 等式证明：原始 = 规范化
```

每一步规范化都产生一个 `Result`，**同时携带数据和证明**。这是"verified by construction"的设计——规范化的每一步都有证明，不存在"先计算后验证"的信任缺口。

# 规范化算法：eval / evalAdd / evalMul / evalPow
%%%
tag := "ch07-normalization-algorithms"
%%%

## `eval`：核心递归引擎
%%%
tag := "ch07-eval-function"
%%%

`eval` 是规范化的核心——给定一个 Lean 表达式，返回其范式表示。它对表达式做 WHNF 展开，根据 head function 分发到对应的处理分支：

```
-- [Mathlib, Mathlib/Tactic/Ring/Common.lean:1271-1338]
partial def eval  {u : Lean.Level}
    {α : Q(Type u)} {bt : Q($α) → Type} {sα : Q(CommSemiring $α)} (rc : RingCompute bt sα)
    (c : Cache sα) (e : Q($α)) : AtomM (Result (ExSum bt sα) e) := Lean.withIncRecDepth do
  let els := do
    try rc.derive e
    catch _ => evalAtom rc rcℕ e
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n, c.rα, c.dsα with
  | ``HAdd.hAdd, _, _ | ``Add.add, _, _ => match e with
    | ~q($a + $b) =>
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨_, vb, pb⟩ ← eval rc c b
      let ⟨c, vc, p⟩ ← evalAdd rc rcℕ va vb
      pure ⟨c, vc, q(add_congr $pa $pb $p)⟩
    | _ => els
  | ``HMul.hMul, _, _ | ``Mul.mul, _, _ => match e with
    | ~q($a * $b) =>
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨_, vb, pb⟩ ← eval rc c b
      let ⟨c, vc, p⟩ ← evalMul rc rcℕ va vb
      pure ⟨c, vc, q(mul_congr $pa $pb $p)⟩
    | _ => els
  | ``HPow.hPow, _, _ | ``Pow.pow, _, _ => match e with
    | ~q($a ^ $b) =>
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨b, vb, pb⟩ ← eval rcℕ .nat b
      let ⟨b', vb'⟩ := vb.toExSumNat
      have : $b =Q $b' := ⟨⟩
      let ⟨c, vc, p⟩ ← evalPow rc rcℕ va vb'
      pure ⟨c, vc, q(pow_congr $pa $pb $p)⟩
    | _ => els
  | ``Neg.neg, some rα, _ => match e with
    | ~q(-$a) =>
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨b, vb, p⟩ ← evalNeg rc rα va
      pure ⟨b, vb, q(neg_congr $pa $p)⟩
    | _ => els
  | ``HSub.hSub, some rα, _ | ``Sub.sub, some rα, _ => match e with
    | ~q($a - $b) => do
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨_, vb, pb⟩ ← eval rc c b
      let ⟨c, vc, p⟩ ← evalSub rc rcℕ rα va vb
      pure ⟨c, vc, q(sub_congr $pa $pb $p)⟩
    | _ => els
  | ``Inv.inv, _, some dsα => match e with
    | ~q($a⁻¹) =>
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨b, vb, p⟩ ← va.evalInv rc rcℕ dsα c.czα
      pure ⟨b, vb, q(inv_congr $pa $p)⟩
    | _ => els
  | ``HDiv.hDiv, _, some dsα | ``Div.div, _, some dsα => match e with
    | ~q($a / $b) => do
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨_, vb, pb⟩ ← eval rc c b
      let ⟨c, vc, p⟩ ← evalDiv rc rcℕ dsα c.czα va vb
      pure ⟨c, vc, q(div_congr $pa $pb $p)⟩
    | _ => els
  | _, _, _ => els
```

算法逻辑：

1. **WHNF 展开**：对表达式做 weak-head normal form 展开，拿到 head function
2. **模式匹配**：根据 head function 分发到对应的处理分支
3. **递归规范化**：每个分支先递归规范化子表达式，再用对应的范式操作合并结果
4. **回退**：如果 head function 不是已知运算符，尝试用 `norm_num`（`rc.derive`）识别常量，或当作不可分解的**原子**（`evalAtom`）

注意 `Neg.neg` 和 `Sub.sub` 分支需要 `c.rα = some _`（即 `CommRing` 实例），`Inv.inv` 和 `Div.div` 分支需要 `c.dsα = some _`（即 `Semifield` 实例）。如果类型只是 `CommSemiring`，这些分支不会被匹配，对应的操作会回退到 `evalAtom`。

## 原子管理：`AtomM` monad
%%%
tag := "ch07-atom-management"
%%%

当 `eval` 遇到无法分解的表达式（如自由变量 `x`、未知函数 `f a`）时，调用 `evalAtom`，它通过 `AtomM` monad 管理原子编号：

1. 检查这个表达式是否已经见过（用 `isDefEq` 判断）
2. 如果见过，返回之前分配的编号
3. 如果没见过，分配新编号并记录

原子编号是**范式定义的组成部分**。变量编号的顺序直接决定了范式中单项式的排列顺序——`ExBase.cmp` 对原子按编号比较。这意味着编号小的变量在所有单项式中排在前面，保证了 `x*y` 和 `y*x` 规范化后得到完全相同的范式结构。

## 加法规范化：`evalAdd`
%%%
tag := "ch07-eval-add"
%%%

```
-- [Mathlib, Mathlib/Tactic/Ring/Common.lean:573-594]
partial def evalAdd {a b : Q($α)} (va : ExSum bt sα a) (vb : ExSum bt sα b) :
    MetaM <| Result (ExSum bt sα) q($a + $b) := do
  Lean.Core.checkSystem decl_name%.toString
  match va, vb with
  | .zero, vb => return ⟨b, vb, q(add_pf_zero_add $b)⟩
  | va, .zero => return ⟨a, va, q(add_pf_add_zero $a)⟩
  | .add (a := a₁) (b := _a₂) va₁ va₂, .add (a := b₁) (b := _b₂) vb₁ vb₂ =>
    have va := .add va₁ va₂; have vb := .add vb₁ vb₂
    match ← (evalAddOverlap rc rcℕ va₁ vb₁).run with
    | some (.nonzero ⟨_, vc₁, pc₁⟩) =>
      let ⟨_, vc₂, pc₂⟩ ← evalAdd va₂ vb₂
      return ⟨_, .add vc₁ vc₂, q(add_pf_add_overlap $pc₁ $pc₂)⟩
    | some (.zero pc₁) =>
      let ⟨c₂, vc₂, pc₂⟩ ← evalAdd va₂ vb₂
      return ⟨c₂, vc₂, q(add_pf_add_overlap_zero $pc₁ $pc₂)⟩
    | none =>
      if let .lt := va₁.cmp rcℕ rc vb₁ then
        let ⟨_c, vc, pc⟩ ← evalAdd va₂ vb
        return ⟨_, .add va₁ vc, q(add_pf_add_lt $a₁ $pc)⟩
      else
        let ⟨_c, vc, pc⟩ ← evalAdd va vb₂
        return ⟨_, .add vb₁ vc, q(add_pf_add_gt $b₁ $pc)⟩
```

这是一个**有序链表归并**（类似归并排序的 merge 步骤）：

- 两个多项式都按单项式排序
- 同类项（相同基和指数模式）的系数相加（`evalAddOverlap`）
- 如果系数和为零，删除该项（`.zero` 分支）
- 非同类项按序保留

`evalAddOverlap` 负责检测和合并同类项：

```
-- [Mathlib, Mathlib/Tactic/Ring/Common.lean:528-546]
def evalAddOverlap {a b : Q($α)} (va : ExProd bt sα a) (vb : ExProd bt sα b) :
    OptionT MetaM (Overlap bt sα q($a + $b)) := do
  Lean.Core.checkSystem decl_name%.toString
  match va, vb with
  | .const za, .const zb => do
    let ⟨⟨_, zc, pf⟩, isZero⟩ ← rc.add za zb
    match isZero with
    | .some pf => pure <| .zero q($pf)
    | .none =>
      assumeInstancesCommute
      pure <| .nonzero ⟨_, .const zc, q($pf)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃, .mul (x := b₁) (e := b₂) vb₁ vb₂ vb₃ => do
    guard (va₁.eq rcℕ rc vb₁ && va₂.toExProd.2.eq rcℕ rcℕ vb₂.toExProd.2)
    have : $a₁ =Q $b₁ := ⟨⟩; have : $a₂ =Q $b₂ := ⟨⟩
    match ← evalAddOverlap va₃ vb₃ with
    | .zero p => pure <| .zero q(add_overlap_pf_zero $a₁ $a₂ $p)
    | .nonzero ⟨_, vc, p⟩ =>
      pure <| .nonzero ⟨_, .mul va₁ va₂ vc, q(add_overlap_pf $a₁ $a₂ $p)⟩
  | _, _ => OptionT.fail
```

## 乘法规范化：`evalMul`
%%%
tag := "ch07-eval-mul"
%%%

乘法使用**分配律**：`(a₁ + a₂) * b = a₁ * b + a₂ * b`，递归地把多项式乘法拆解为单项式乘法，然后用 `evalAdd` 合并：

```
-- [Mathlib, Mathlib/Tactic/Ring/Common.lean:689-697]
def evalMul {a b : Q($α)} (va : ExSum bt sα a) (vb : ExSum bt sα b) :
    MetaM <| Result (ExSum bt sα) q($a * $b) := do
  match va with
  | .zero => return ⟨_, .zero, q(zero_mul $b)⟩
  | .add va₁ va₂ =>
    let ⟨_, vc₁, pc₁⟩ ← evalMul₁ rc rcℕ va₁ vb
    let ⟨_, vc₂, pc₂⟩ ← evalMul va₂ vb
    let ⟨_, vd, pd⟩ ← evalAdd rc rcℕ vc₁ vc₂
    return ⟨_, vd, q(add_mul $pc₁ $pc₂ $pd)⟩
```

单项式乘法 `evalMulProd` 处理幂的合并——当两个单项式的**基相同**时合并指数（`x^e * x^f = x^(e+f)`），当基不同时按排序插入：

```
-- [Mathlib, Mathlib/Tactic/Ring/Common.lean:624-656]
partial def evalMulProd {a b : Q($α)} (va : ExProd bt sα a) (vb : ExProd bt sα b) :
    MetaM <| Result (ExProd bt sα) q($a * $b) := do
  Lean.Core.checkSystem decl_name%.toString
  match va, vb with
  | .const za, .const zb =>
    let ⟨_, zc, pf⟩ ← rc.mul za zb
    assumeInstancesCommute
    return ⟨_, .const zc, q($pf)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃, vb@(.const _) =>
    let ⟨_, vc, pc⟩ ← evalMulProd va₃ vb
    return ⟨_, .mul va₁ va₂ vc, q(mul_pf_left $a₁ $a₂ $pc)⟩
  | va@(.const _), .mul (x := b₁) (e := b₂) vb₁ vb₂ vb₃ =>
    let ⟨_, vc, pc⟩ ← evalMulProd va vb₃
    return ⟨_, .mul vb₁ vb₂ vc, q(mul_pf_right $b₁ $b₂ $pc)⟩
  | .mul (x := xa) (e := ea) vxa vea va₂, .mul (x := xb) (e := eb) vxb veb vb₂ =>
    have va := .mul vxa vea va₂; have vb := .mul vxb veb vb₂
    let ⟨ea', vea'⟩ := vea.toExProd
    let ⟨eb', veb'⟩ := veb.toExProd
    if vxa.eq rcℕ rc vxb then
      have : $xa =Q $xb := ⟨⟩
      if let some (.nonzero ⟨ec', vec', pec'⟩) ← (evalAddOverlap rcℕ rcℕ vea' veb').run then
        let ⟨_, vc, pc⟩ ← evalMulProd va₂ vb₂
        let ⟨ec, vec⟩ := vec'.toExProdNat
        have : $ea =Q $ea' := ⟨⟩; have : $eb =Q $eb' := ⟨⟩; have : $ec =Q $ec' := ⟨⟩
        return ⟨_, .mul vxa vec vc, q(mul_pp_pf_overlap $xa $pec' $pc)⟩
    if let .lt := (vxa.cmp rcℕ rc vxb).then (vea'.cmp rcℕ rcℕ veb') then
      let ⟨_, vc, pc⟩ ← evalMulProd va₂ vb
      return ⟨_, .mul vxa vea vc, q(mul_pf_left $xa $ea $pc)⟩
    else
      let ⟨_, vc, pc⟩ ← evalMulProd va vb₂
      return ⟨_, .mul vxb veb vc, q(mul_pf_right $xb $eb $pc)⟩
```

## 幂规范化：`evalPow`
%%%
tag := "ch07-eval-pow"
%%%

```
-- [Mathlib, Mathlib/Tactic/Ring/Common.lean:1047-1058]
def evalPow {a : Q($α)} {b : Q(ℕ)} (va : ExSum bt sα a) (vb : ExSumNat b) :
    MetaM <| Result (ExSum bt sα) q($a ^ $b) := do
  match vb with
  | .zero =>
    let ⟨_, one, pf⟩ := rc.one
    assumeInstancesCommute
    return ⟨_, (ExProd.const (one)).toSum, q(pow_zero $a $pf)⟩
  | .add vb₁ vb₂ =>
    let ⟨_, vc₁, pc₁⟩ ← evalPow₁ rc rcℕ va vb₁
    let ⟨_, vc₂, pc₂⟩ ← evalPow va vb₂
    let ⟨_, vd, pd⟩ ← evalMul rc rcℕ vc₁ vc₂
    return ⟨_, vd, q(pow_add $pc₁ $pc₂ $pd)⟩
```

幂运算利用 `a^(b₁+b₂) = a^b₁ * a^b₂` 拆分指数，最终归约到基本情况。对于**具体自然数指数**（如 `x^3`），通过 `evalPowNat` 用二进制快速幂展开：

```
-- [Mathlib, Mathlib/Tactic/Ring/Common.lean:870-889]
partial def evalPowNat {a : Q($α)} (va : ExSum bt sα a) (n : Q(ℕ)) :
    MetaM <| Result (ExSum bt sα) q($a ^ $n) := do
  let nn := n.natLit!
  if nn = 1 then
    have : $n =Q 1 := ⟨⟩
    return ⟨_, va, q(pow_one $a)⟩
  else
    let nm := nn >>> 1
    have m : Q(ℕ) := mkRawNatLit nm
    if nn &&& 1 = 0 then
      have : $n =Q 2 * $m := ⟨⟩
      let ⟨_, vb, pb⟩ ← evalPowNat va m
      let ⟨_, vc, pc⟩ ← evalMul rc rcℕ vb vb
      return ⟨_, vc, q(pow_bit0 $pb $pc)⟩
    else
      have : $n =Q 2 * $m + 1 := ⟨⟩
      let ⟨_, vb, pb⟩ ← evalPowNat va m
      let ⟨_, vc, pc⟩ ← evalMul rc rcℕ vb vb
      let ⟨_, vd, pd⟩ ← evalMul rc rcℕ vc va
      return ⟨_, vd, q(pow_bit1 $pb $pc $pd)⟩
```

对于**变量指数**（如 `x^n`），保留为 `ExProd.mul (atom x) (atom n) (const 1)` 的形式。

## 取负和减法
%%%
tag := "ch07-neg-sub"
%%%

取负需要 `CommRing`（不仅仅是 `CommSemiring`），对每个单项式的系数取负：

```
-- [Mathlib, Mathlib/Tactic/Ring/Common.lean:712-723]
def evalNegProd {a : Q($α)} (rα : Q(CommRing $α)) (va : ExProd bt sα a) :
    MetaM <| Result (ExProd bt sα) q(-$a) := do
  Lean.Core.checkSystem decl_name%.toString
  match va with
  | .const za =>
    let ⟨b, zb, pb⟩ ← rc.neg q($rα) za
    return ⟨b, .const zb,  q($pb)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃ =>
    let ⟨_, vb, pb⟩ ← evalNegProd rα va₃
    assumeInstancesCommute
    return ⟨_, .mul va₁ va₂ vb, q(neg_mul $a₁ $a₂ $pb)⟩
```

减法被展开为加法加取负 `a - b = a + (-b)`：

```
-- [Mathlib, Mathlib/Tactic/Ring/Common.lean:754-760]
def evalSub {a b : Q($α)}
    (rα : Q(CommRing $α)) (va : ExSum bt sα a) (vb : ExSum bt sα b) :
    MetaM <| Result (ExSum bt sα) q($a - $b) := do
  let ⟨_c, vc, pc⟩ ← evalNeg rc rα vb
  let ⟨d, vd, pd⟩ ← evalAdd rc rcℕ va vc
  assumeInstancesCommute
  return ⟨d, vd, q(sub_pf $pc $pd)⟩
```

## 除法和求逆
%%%
tag := "ch07-div-inv"
%%%

除法需要 `Semifield`，被转化为 `a * b⁻¹`：

```
-- [Mathlib, Mathlib/Tactic/Ring/Common.lean:1184-1189]
def evalDiv {a b : Q($α)} (rα : Q(Semifield $α)) (czα : Option Q(CharZero $α))
    (va : ExSum bt sα a) (vb : ExSum bt sα b) : AtomM (Result (ExSum bt sα) q($a / $b)) := do
  let ⟨_c, vc, pc⟩ ← vb.evalInv rc rcℕ rα czα
  let ⟨d, vd, pd⟩ ← evalMul rc rcℕ va vc
  assumeInstancesCommute
  pure ⟨d, vd, q(div_pf $pc $pd)⟩
```

注意 `ring` **不会**做 `a/a = 1` 约分——它只会把 `b⁻¹` 当作一个新原子（如果 `b` 是非常数多项式）或用 `norm_num` 计算具体数值的逆（如果 `b` 是常数）。

## 结构等式比较
%%%
tag := "ch07-structural-equality"
%%%

```
-- [Mathlib, Mathlib/Tactic/Ring/Common.lean:436-443]
partial def ExSum.eq
    {u : Lean.Level} {α : Q(Type u)} {bt} {sα : Q(CommSemiring $α)} (rc : RingCompare bt)
    {a b : Q($α)} :
    ExSum bt sα a → ExSum bt sα b → Bool
  | .zero, .zero => true
  | .add a₁ a₂, .add b₁ b₂ => a₁.eq rc b₁ && a₂.eq rc b₂
  | _, _ => false
```

逐项递归比较。由于范式保证了唯一性，结构相等等价于语义相等。`ring` **不**用 Lean 的 `isDefEq` 来比较规范化后的表达式——`ExSum.eq` 在纯数据结构上操作，近乎免费。

# 系数计算：norm\_num 作为后端
%%%
tag := "ch07-coefficient-computation"
%%%

## `RingCompute` 接口
%%%
tag := "ch07-ring-compute"
%%%

`ring` 的规范化算法通过 `RingCompute` 结构体与系数类型解耦：

```
-- [Mathlib, Mathlib/Tactic/Ring/Common.lean:290-321]
structure RingCompute {u : Lean.Level} {α : Q(Type u)} (BaseType : Q($α) → Type)
  (sα : Q(CommSemiring $α)) extends RingCompare BaseType where
  add {x y : Q($α)} : BaseType x → BaseType y →
    MetaM ((Result BaseType q($x + $y)) × (Option Q(IsNat ($x + $y) 0)))
  mul {x y : Q($α)} : BaseType x → BaseType y → MetaM (Result BaseType q($x * $y))
  cast (v : Lean.Level) (β : Q(Type v)) (_ : Q(CommSemiring $β))
      (_ : Q(SMul $β $α)) (x : Q($β)) :
    AtomM (Σ y : Q($α), ExSum BaseType sα q($y) × Q(∀ a : $α, $x • a = $y * a))
  neg {x : Q($α)} (rα : Q(CommRing $α)) : BaseType x → MetaM (Result BaseType q(-$x))
  pow {x : Q($α)} {b : Q(ℕ)} : BaseType x → (vb : ExProdNat q($b)) →
    OptionT MetaM (Result BaseType q($x ^ $b))
  inv {x : Q($α)} (czα : Option Q(CharZero $α)) (fα : Q(Semifield $α)) : BaseType x →
    AtomM (Option <| Result BaseType q($x⁻¹))
  derive (x : Q($α)) : MetaM (Result (ExSum BaseType sα) q($x))
  isOne {x : Q($α)} : BaseType x → Option Q(NormNum.IsNat $x 1)
  one : Result BaseType q((nat_lit 1).rawCast)
```

每个方法对应一种系数运算，且**必须同时返回计算结果和证明**。

## `RatCoeff`：有理系数
%%%
tag := "ch07-rat-coeff"
%%%

```
-- [Mathlib, Mathlib/Tactic/Ring/Common.lean:108-113]
structure _root_.Mathlib.Tactic.Ring.RatCoeff {u : Lean.Level} {α : Q(Type u)} (e : Q($α)) where
  value : ℚ
  hyp : Option Expr
deriving Inhabited
```

`ring` 在 `ℚ` 系数上工作——即使用户的类型是 `ℤ`，`ring` 也能处理有理系数（当然在 `ℤ` 上不会出现非整数系数）。`value` 是有理数值，`hyp` 在系数不是整数时存储分母非零的证明。

## 具体的 `ringCompute` 实现
%%%
tag := "ch07-ring-compute-impl"
%%%

```
-- [Mathlib, Mathlib/Tactic/Ring/Basic.lean:493-506]
partial def _root_.Mathlib.Tactic.Ring.ringCompute
    {u : Lean.Level} {α : Q(Type u)} {sα : Q(CommSemiring $α)} (cα : Common.Cache sα) :
    Common.RingCompute RatCoeff sα where
  add := add sα
  mul := mul sα
  cast := cast sα cα
  neg := neg
  pow := pow sα
  inv := inv sα
  derive := derive sα
  isOne := isOne sα
  one := ⟨q((nat_lit 1).rawCast), ⟨1, none⟩, q(rfl)⟩
  toRingCompare := ringCompare
```

关键洞察：**`ring` 的系数计算委托给 `norm_num`**。`ring` 自己不做数值计算——它只负责多项式结构的规范化，数值计算交给 `norm_num` 这个更专业的工具。例如 `add` 方法内部调用 `NormNum.Result.add`，`mul` 调用 `NormNum.Result.mul`。

系数比较直接在 `ℚ` 值上进行：

```
-- [Mathlib, Mathlib/Tactic/Ring/Basic.lean:487-491]
partial def _root_.Mathlib.Tactic.Ring.ringCompare {u : Lean.Level} {α : Q(Type u)} :
    Common.RingCompare (α := α) RatCoeff where
  eq zx zy := zx.value == zy.value
  compare zx zy := compare zx.value zy.value
```

这是 `ring` 效率的一个来源——不需要在 Lean 表达式层面做 `isDefEq` 判断。

# 类型提升：CSLift
%%%
tag := "ch07-cslift"
%%%

## 问题与机制
%%%
tag := "ch07-cslift-mechanism"
%%%

有些类型（如 `ℕ+`）不是 `CommSemiring`，但可以嵌入到一个更大的 `CommSemiring` 中。`ring` 通过 `CSLift` 机制处理这种情况：

```
-- [Mathlib, Mathlib/Tactic/Ring/Basic.lean:519-531]
class CSLift (α : Type u) (β : outParam (Type u)) where
  lift : α → β
  inj : Function.Injective lift

class CSLiftVal {α} {β : outParam (Type u)} [CSLift α β] (a : α) (b : outParam β) : Prop where
  eq : b = CSLift.lift a
```

使用流程：当 `CommSemiring α` 合成失败时，`proveEq` 尝试：

1. 合成 `CSLift α β` 找到目标类型 `β`
2. 确认 `β` 是 `CommSemiring`
3. 把 `e₁`、`e₂` 通过 `CSLiftVal` 提升到 `β`
4. 在 `β` 上运行 `ringCore`
5. 用 `CSLift.inj` 的单射性把证明拉回到 `α`

最后一步使用 `of_lift` 引理：

```
-- [Mathlib, Mathlib/Tactic/Ring/Basic.lean:535-537]
theorem of_lift {α β} [inst : CSLift α β] {a b : α} {a' b' : β}
    [h1 : CSLiftVal a a'] [h2 : CSLiftVal b b'] (h : a' = b') : a = b :=
  inst.2 <| by rwa [← h1.1, ← h2.1]
```

## PNat 实例
%%%
tag := "ch07-pnat-instance"
%%%

```
-- [Mathlib, Mathlib/Tactic/Ring/PNat.lean:24-25]
instance : CSLift ℕ+ Nat where
  lift := PNat.val
  inj := PNat.coe_injective
```

这让 `ring` 可以在 `ℕ+` 上工作，尽管 `ℕ+` 本身没有 `CommSemiring` 实例（它没有零元素）。相应的 `CSLiftVal` 实例把 `ℕ+` 上的运算（加法、乘法、幂）分配到提升后的 `ℕ` 上：

```
-- [Mathlib, Mathlib/Tactic/Ring/PNat.lean:41-48]
instance {n n' k k'} [h1 : CSLiftVal (n : ℕ+) n'] [h2 : CSLiftVal (k : ℕ+) k'] :
    CSLiftVal (n + k) (n' + k') := ⟨by simp [h1.1, h2.1, CSLift.lift]⟩

instance {n n' k k'} [h1 : CSLiftVal (n : ℕ+) n'] [h2 : CSLiftVal (k : ℕ+) k'] :
    CSLiftVal (n * k) (n' * k') := ⟨by simp [h1.1, h2.1, CSLift.lift]⟩

instance {n n' k} [h1 : CSLiftVal (n : ℕ+) n'] :
    CSLiftVal (n ^ k) (n' ^ k) := ⟨by simp [h1.1, CSLift.lift]⟩
```

用户可以为自定义类型提供 `CSLift` 实例来扩展 `ring` 的适用范围——只需一个到 `CommSemiring` 类型的单射嵌入，核心规范化逻辑完全不变。

# 与 Horner 形式的关系
%%%
tag := "ch07-horner-relation"
%%%

传统的多项式 Horner 形式是 `(...((aₙx + aₙ₋₁)x + aₙ₋₂)x + ... + a₁)x + a₀`。`ring` 的范式更通用：

- **多变量**：Horner 形式本质上是单变量的，而 `ExBase`/`ExProd`/`ExSum` 的互相递归天然支持多变量
- **嵌套**：`ExBase.sum` 允许在基中嵌套完整的多项式，处理 `(a + b)^n` 这类表达式
- **有理系数**：通过 `BaseType` 参数化系数类型，`ring` 在 `ℚ` 系数上工作（不仅仅是 `ℤ` 或 `ℕ`）
- **变量指数**：`ExProdNat` 中的指数也是多项式，允许 `2^n` 等变量指数出现

这种 Horner-like form 并不是唯一自然的选择——例如也可以用稀疏展开、DAG 表示或递归 Horner scheme。`ring` 选择当前范式是因为它**足够好**（多变量天然有序）、**足够可比较**（结构相等即语义相等）、**足够利于递归构造 proof**（每步操作对应一条等式引理）。

# 性能考量
%%%
tag := "ch07-performance"
%%%

`ring` 的复杂度与表达式大小多项式相关，但高次幂会导致项数爆炸：

```
-- ✅ 快速：变量少、次数低
example (x : ℤ) : (x + 1) ^ 4 = x ^ 4 + 4 * x ^ 3 + 6 * x ^ 2 + 4 * x + 1 := by
  ring

-- ⚠️ 较慢：(a + b + c + d + e) ^ 10 展开后有大量项
```

性能提示：

- 太慢时先手动化简子表达式，或拆分证明步骤
- `ring` 使用二进制快速幂（`evalPowNat`），但展开后的乘法合并仍然是瓶颈
- 变量指数（如 `x^n`）不做展开，因此 `2^(n+1) * m = 2 * 2^n * m` 是快速的
- 系数运算委托给 `norm_num`，大数系数不是性能问题

# ring\_nf 实现
%%%
tag := "ch07-ring-nf-impl"
%%%

## 核心函数：`evalExpr`
%%%
tag := "ch07-eval-expr"
%%%

```
-- [Mathlib, Mathlib/Tactic/Ring/RingNF.lean:61-73]
def evalExpr (e : Expr) : AtomM Simp.Result := do
  let e ← withReducible <| whnf e
  guard e.isApp
  let ⟨u, α, e⟩ ← inferTypeQ' e
  let sα ← synthInstanceQ q(CommSemiring $α)
  let c ← Common.mkCache sα
  let ⟨a, _, pa⟩ ← match
    (← Common.isAtomOrDerivable (ringCompute c) c q($e)) with
  | none => Common.eval rcℕ (ringCompute c) c e
  | some none => failure
  | some (some r) => pure r
  pure { expr := a, proof? := pa }
```

关键的预检查 `isAtomOrDerivable`：

- **`none`**：表达式有代数运算（加/乘/幂等），值得完整规范化
- **`some none`**：纯原子，`ring_nf` 不做任何事
- **`some (some r)`**：虽然没有代数结构，但 `norm_num` 能化简（如 `2 + 3` → `5`）

## 清理例程：`cleanup`
%%%
tag := "ch07-cleanup"
%%%

规范化后的表达式可能包含冗余的 `+ 0`、`* 1`、`^ 1` 等。`cleanup` 用一组 simp 引理清理：

```
-- [Mathlib, Mathlib/Tactic/Ring/RingNF.lean:91-105]
def cleanup (cfg : RingNF.Config) (r : Simp.Result) : MetaM Simp.Result := do
  match cfg.mode with
  | .raw => pure r
  | .SOP => do
    let thms : SimpTheorems := {}
    let thms ← [``add_zero, ``_root_.mul_one, ``_root_.pow_one, ``mul_neg, ``add_neg
      ].foldlM (·.addConst ·) thms
    let thms ← [``nat_rawCast_0, ``nat_rawCast_1, ``nat_rawCast_2, ``int_rawCast_neg,
      ``nnrat_rawCast, ``rat_rawCast_neg, ``add_assoc_rev, ``mul_assoc_rev
      ].foldlM (·.addConst · (post := false)) thms
    let ctx ← Simp.mkContext { zetaDelta := cfg.zetaDelta }
      (simpTheorems := #[thms])
      (congrTheorems := ← getSimpCongrTheorems)
    pure <| ←
      r.mkEqTrans (← Simp.main r.expr ctx (methods := Lean.Meta.Simp.mkDefaultMethodsCore {})).1
```

两种模式：**SOP**（默认）用 simp 清除冗余项并重排结合律为左结合；**raw** 不做任何清理，直接返回内部原始表示。`ring_nf (config := { mode := .raw })` 可以输出 `ring` 的内部原始范式，用于调试。

## `ring_nf` tactic 注册
%%%
tag := "ch07-ring-nf-registration"
%%%

```
-- [Mathlib, Mathlib/Tactic/Ring/RingNF.lean:135-141]
elab (name := ringNF) "ring_nf" tk:"!"? cfg:optConfig loc:(location)? : tactic => do
  let mut cfg ← elabConfig cfg
  if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  let s ← IO.mkRef {}
  let m := AtomM.recurse s cfg.toConfig (wellBehavedDischarge := true) evalExpr (cleanup cfg)
  transformAtLocation (m ·) "`ring_nf`" loc cfg.failIfUnchanged false
```

`ring_nf` 被集成到 `simp` 框架中——通过 `AtomM.recurse` 和 `transformAtLocation` 递归地对目标中的每个子表达式尝试规范化。这也是 `ring_nf` 能处理 `sin (x + y) + sin (y + x) = 2 * sin (x + y)` 这种嵌套场景的原因——它会在 `sin` 的**参数**中做环规范化。

## `Cache`：实例缓存
%%%
tag := "ch07-cache"
%%%

```
-- [Mathlib, Mathlib/Tactic/Ring/Common.lean:1061-1074]
structure Cache {α : Q(Type u)} (sα : Q(CommSemiring $α)) where
  rα : Option Q(CommRing $α)
  dsα : Option Q(Semifield $α)
  czα : Option Q(CharZero $α)

def mkCache {α : Q(Type u)} (sα : Q(CommSemiring $α)) : MetaM (Cache sα) :=
  return {
    rα := (← trySynthInstanceQ q(CommRing $α)).toOption
    dsα := (← trySynthInstanceQ q(Semifield $α)).toOption
    czα := (← trySynthInstanceQ q(CharZero $α)).toOption }
```

`Cache` 在 `proveEq` 开始时构建一次，之后在整个规范化过程中反复使用。它决定了 `eval` 的哪些分支可用：

- `rα = some _`：允许 `Neg.neg`、`HSub.hSub`
- `dsα = some _`：允许 `HDiv.hDiv`、`Inv.inv`
- `czα = some _`：求逆时使用，保证除以非零

# 证明引理系统
%%%
tag := "ch07-proof-lemmas"
%%%

## 证明策略
%%%
tag := "ch07-proof-strategy-detail"
%%%

`ring` 不在最后一步生成一个大证明，而是**在规范化的每一步都附带证明**。每个 `eval*` 函数返回的 `Result` 中包含一个 `proof : Q($e = $expr)` 项。proof 沿着分配律、结合律、cast、系数计算一路累积——每步操作的输出不是一个值，而是一个 `Result` 三元组。

## 关键引理族
%%%
tag := "ch07-key-lemma-families"
%%%

规范化的每一步都引用预定义的等式引理：

**加法归并引理**：

```
-- [Mathlib, Mathlib/Tactic/Ring/Common.lean:548-563]
theorem add_pf_zero_add (b : R) : 0 + b = b := by simp
theorem add_pf_add_zero (a : R) : a + 0 = a := by simp

theorem add_pf_add_overlap
    (_ : a₁ + b₁ = c₁) (_ : a₂ + b₂ = c₂) : (a₁ + a₂ : R) + (b₁ + b₂) = c₁ + c₂ := by
  subst_vars; simp [add_assoc, add_left_comm]

theorem add_pf_add_overlap_zero
    (h : IsNat (a₁ + b₁) (nat_lit 0)) (h₄ : a₂ + b₂ = c) : (a₁ + a₂ : R) + (b₁ + b₂) = c := by
  subst_vars; rw [add_add_add_comm, h.1, Nat.cast_zero, add_pf_zero_add]

theorem add_pf_add_lt (a₁ : R) (_ : a₂ + b = c) : (a₁ + a₂) + b = a₁ + c := by simp [*, add_assoc]

theorem add_pf_add_gt (b₁ : R) (_ : a + b₂ = c) : a + (b₁ + b₂) = b₁ + c := by
  subst_vars; simp [add_left_comm]
```

**乘法引理**：

```
-- [Mathlib, Mathlib/Tactic/Ring/Common.lean:598-612]
theorem one_mul (a : R) : (nat_lit 1).rawCast * a = a := by simp [Nat.rawCast]
theorem mul_one (a : R) : a * (nat_lit 1).rawCast = a := by simp [Nat.rawCast]

theorem mul_pf_left (a₁ : R) (a₂) (_ : a₃ * b = c) :
    (a₁ ^ a₂ * a₃ : R) * b = a₁ ^ a₂ * c := by
  subst_vars; rw [mul_assoc]

theorem mul_pf_right (b₁ : R) (b₂) (_ : a * b₃ = c) :
    a * (b₁ ^ b₂ * b₃) = b₁ ^ b₂ * c := by
  subst_vars; rw [mul_left_comm]

theorem mul_pp_pf_overlap {ea eb e : ℕ} (x : R) (_ : ea + eb = e) (_ : a₂ * b₂ = c) :
    (x ^ ea * a₂ : R) * (x ^ eb * b₂) = x ^ e * c := by
  subst_vars; simp [pow_add, mul_mul_mul_comm]
```

**幂运算引理**：

```
-- [Mathlib, Mathlib/Tactic/Ring/Common.lean:851-859]
theorem pow_one (a : R) : a ^ nat_lit 1 = a := by simp

theorem pow_bit0 {k : ℕ} (_ : (a : R) ^ k = b) (_ : b * b = c) :
    a ^ (Nat.mul (nat_lit 2) k) = c := by
  subst_vars; simp [Nat.succ_mul, pow_add]

theorem pow_bit1 {k : ℕ} {d : R} (_ : (a : R) ^ k = b) (_ : b * b = c) (_ : c * a = d) :
    a ^ (Nat.add (Nat.mul (nat_lit 2) k) (nat_lit 1)) = d := by
  subst_vars; simp [Nat.succ_mul, pow_add]
```

**congr 引理**（连接递归步骤与子表达式证明）：

```
-- [Mathlib, Mathlib/Tactic/Ring/Common.lean:1191-1227]
theorem add_congr (_ : a = a') (_ : b = b') (_ : a' + b' = c) : (a + b : R) = c := by
  subst_vars; rfl
theorem mul_congr (_ : a = a') (_ : b = b') (_ : a' * b' = c) : (a * b : R) = c := by
  subst_vars; rfl
theorem pow_congr {b b' : ℕ} (_ : a = a') (_ : b = b')
    (_ : a' ^ b' = c) : (a ^ b : R) = c := by subst_vars; rfl
theorem neg_congr {R} [CommRing R] {a a' b : R} (_ : a = a')
    (_ : -a' = b) : (-a : R) = b := by subst_vars; rfl
theorem sub_congr {R} [CommRing R] {a a' b b' c : R} (_ : a = a') (_ : b = b')
    (_ : a' - b' = c) : (a - b : R) = c := by subst_vars; rfl
```

**顶层拼接**：

```
-- [Mathlib, Mathlib/Tactic/Ring/Basic.lean:541]
theorem of_eq {α} {a b c : α} (_ : (a : α) = c) (_ : b = c) : a = b := by subst_vars; rfl
```

## `Qq` 的角色
%%%
tag := "ch07-qq-role"
%%%

所有证明项都通过 Lean 的 `Qq` 库构造。`Qq` 在**编译时**检查引用表达式的类型正确性——如果 `ring` 的证明构造有误，Mathlib 本身就无法编译。这是"verified by construction"设计的第二层保障。

例如在 `evalAdd` 中的 `q(add_pf_add_overlap $pc₁ $pc₂)`，`Qq` 会在编译时检查 `pc₁` 和 `pc₂` 的类型是否匹配 `add_pf_add_overlap` 的参数签名。

## 为什么 ring 不是纯数据算法
%%%
tag := "ch07-not-purely-data"
%%%

从前面的代码看，`ring` 的核心操作——加法归并、乘法分配、幂拆分——似乎只是在操作数据结构。但实际工程中远不止此。

**不变量维护是全局约束**。范式唯一性依赖一组严格不变量始终成立：`ExSum` 按全序排序、同类项已合并、零系数已删除、`ExProd` 幂链按基有序、指数本身已规范化。每一个 `evalAdd`/`evalMul`/`evalPow` 操作都必须**同时**维护所有这些不变量——不是"先算出结果再清理"，而是在构造过程中就保证输出满足全部约束。

**proof-producing normalization 才是真正的复杂性来源**。`evalAdd`/`evalMul`/`evalPow` 不只是在算新的数据结构——它们还得在每一步**同步拼出正确的等式证明**。加法归并的每次比较和合并都对应一条等式引理；乘法的分配律展开需要 `add_mul` 引理串联；幂的拆分需要 `pow_add` 引理组合。

**规范化过程中持续维护的不变量清单**：

1. **ExSum 项按全序排序**：`evalAdd` 通过归并维护此序
2. **同类项已合并**：`evalAddOverlap` 在归并时检测并合并同类项
3. **零系数已删除**：合并时的 `.zero` 分支消去零项
4. **ExProd 幂链按基有序**：`evalMulProd` 通过归并维护此序
5. **指数本身已规范化**：自然数版本的 `ExSumNat`/`ExProdNat` 保证
6. **每步操作附带等式证明**：所有 `eval*` 函数返回 `Result`

结论：`ring` 的整个实现都在维护唯一范式所需的不变量。表面上是多项式数据结构操作，实际上每一步都必须同时满足排序、合并、消零、proof 拼接四重约束。

# 不等式自动化：Compare.lean
%%%
tag := "ch07-compare"
%%%

`Ring/Compare.lean` 提供了 `proveLE` 和 `proveLT` 函数，可以在有序交换半环中自动证明某些不等式——具体来说是 ring-normal 形式只差一个**常数**的情况（如 `x + 3 + y < y + x + 4`）。

核心逻辑：先对两边分别做 ring 规范化，然后比较规范化后的结构。如果两个 `ExSum` 只在首项系数上不同，就用 `norm_num` 比较系数大小：

```
-- [Mathlib, Mathlib/Tactic/Ring/Compare.lean:123-156]
def evalLE {v : Level} {α : Q(Type v)}
    (ics : Q(CommSemiring $α)) (_ : Q(PartialOrder $α)) (_ : Q(IsOrderedRing $α))
    {a b : Q($α)} (va : Ring.ExSum q($ics) a) (vb : Ring.ExSum q($ics) b) :
    MetaM (Except ExceptType Q($a ≤ $b)) := do
  let lα : Q(LE $α) := q(le_of_po $α)
  assumeInstancesCommute
  let ⟨_, pz⟩ ← NormNum.mkOfNat α q(amwo_of_cs $α) q(nat_lit 0)
  let rz : NormNum.Result q((0:$α)) :=
    NormNum.Result.isNat q(amwo_of_cs $α) q(nat_lit 0) (q(NormNum.isNat_ofNat $α $pz):)
  match va, vb with
  | .zero, .zero => pure <| .ok (q(le_refl (0:$α)):)
  | .add (b := a') (.const (e := xa) ⟨ca, hypa⟩) va', .add (.const (e := xb) ⟨cb, hypb⟩) vb' => do
    unless va'.eq rcℕ ringCompare vb' do return .error notComparable
    let rxa := NormNum.Result.ofRawRat ca xa hypa
    let rxb := NormNum.Result.ofRawRat cb xb hypb
    let NormNum.Result.isTrue pf ← NormNum.evalLE.core lα rxa rxb | return .error tooSmall
    pure <| .ok (q(add_le_add_left (a := $a') $pf):)
  -- ... 更多分支处理 ca ≤ 0 和 0 ≤ cb 的情况
  | _, _ =>
    unless va.eq rcℕ ringCompare vb do return .error notComparable
    pure <| .ok (q(le_refl $a):)
```

`proveLE` 和 `proveLT` 的用户入口：

```
-- [Mathlib, Mathlib/Tactic/Ring/Compare.lean:206-229]
def proveLE (g : MVarId) : MetaM Unit := do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).le?
    | throwError "ring failed: not of the form `A ≤ B`"
  -- ... 合成 CommSemiring, PartialOrder, IsOrderedRing 实例
  -- 对两边做 ring 规范化
  -- 调用 evalLE 比较
  match ← evalLE ics ipo sα va vb with
  | .ok p => g.assign q(le_congr $pa $p $pb)
  | .error e => -- 报错：ring expressions not comparable 或 LHS is larger
```

这个自动化本身不直接面向用户，但作为 `linear_combination` 在不等式目标上的 discharger 间接可用——用户调用 `linear_combination` 时如果目标是不等式，会自动使用这里的逻辑。

# 扩展点与配置
%%%
tag := "ch07-extension-points"
%%%

## `RingCompute` 参数化
%%%
tag := "ch07-ring-compute-parametric"
%%%

`ring` 的规范化算法通过 `RingCompute` 接口与系数运算解耦。当前 `ring` 只有 `RatCoeff` 一种系数实现，但这个设计为未来扩展保留了空间——例如未来的 `algebra` tactic 可以用 `ring` 表达式作为系数类型。

## `ringCleanupRef`：清理钩子
%%%
tag := "ch07-cleanup-ref"
%%%

```
-- [Mathlib, Mathlib/Tactic/Ring/Basic.lean:548]
initialize ringCleanupRef : IO.Ref (Expr → MetaM Expr) ← IO.mkRef pure
```

`Ring/RingNF.lean` 在初始化时设置这个引用：

```
-- [Mathlib, Mathlib/Tactic/Ring/RingNF.lean:108-109]
initialize ringCleanupRef.set fun e => do
  return (← cleanup {} { expr := e }).expr
```

`ringCleanupRef` 在 `ringCore` 失败时用于**清理残余目标的显示**。当 `ring` 失败，它会用这个函数美化残余目标（如 `a + 0 = b * 1` 会被清理为 `a = b`），让用户更容易理解差距在哪里。这个可变引用让 `Basic.lean` 不依赖 `RingNF.lean`，同时允许 `RingNF.lean` 注入更好的显示逻辑。

## `RingMode` 配置
%%%
tag := "ch07-ring-mode"
%%%

```
-- [Mathlib, Mathlib/Tactic/Ring/RingNF.lean:32-37]
inductive RingMode where
  | SOP    -- Sum of Products：标准多项式形式
  | raw    -- 原始内部表示
  deriving Inhabited, BEq, Repr
```

`ring_nf (config := { mode := .raw })` 输出 `ring` 的内部原始表示（带 `+ 0`、`* 1`、`^ 1` 等冗余项），用于调试。默认的 `.SOP` 模式会通过 `cleanup` 清理这些冗余。

## 在元编程中调用 ring
%%%
tag := "ch07-metaprogramming"
%%%

**通过 `evalTactic`**——最简单的方式：

```
import Mathlib.Tactic.Ring

elab "try_ring" : tactic => do
  try
    Lean.Elab.Tactic.evalTactic (← `(tactic| ring))
  catch _ =>
    Lean.logInfo "ring failed, skipping"
```

**底层 API**——直接调用 `proveEq`：

```
open Lean Elab Tactic in
elab "ring_diagnose" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let some (_, _, lhs, rhs) := target.eq?
    | throwError "ring_diagnose: goal is not an equality"
  logInfo m!"LHS: {lhs}"
  logInfo m!"RHS: {rhs}"
  try
    evalTactic (← `(tactic| ring))
    logInfo "ring succeeded!"
  catch e =>
    logInfo m!"ring failed: {e.toMessageData}"
```

# 调试手册
%%%
tag := "ch07-debug-manual"
%%%

当 `ring` 失败时，它会显示规范化后的残余目标。下面列出最典型的失败模式。

## 模式 1：常数不等式
%%%
tag := "ch07-debug-constant-neq"
%%%

**症状**：`ring_nf` 把目标化简为 `0 = 1` 或类似的常数不等式。

**诊断**：原始等式在数学上就不成立。`ring` 的规范化是完备的——如果两边化简到不同的常数，说明等式确实为假。

**修复**：检查原始命题的数学正确性。

## 模式 2：残余含 `a / a` 或 `a * a⁻¹`
%%%
tag := "ch07-debug-division"
%%%

**症状**：残余目标包含未被约分的分式。

**诊断**：`ring` 不做 `a/a = 1` 约分。这超出了 `ring` 的处理模型——`a/a = 1` 需要 `a ≠ 0` 的前提，不属于无条件等式。

**修复**：用 `field_simp` 先消除分式，再用 `ring` 处理。

## 模式 3：ℕ 减法
%%%
tag := "ch07-debug-nat-sub"
%%%

**症状**：`ring` 在 `ℕ` 上的等式失败。

**诊断**：`ℕ` 只是 `CommSemiring`，没有 `CommRing` 实例。`ring` 会把 `-` 当作无法分解的原子处理。

**修复**：改用 `ℤ`（有完整环结构），或使用 `omega`。

## 模式 4：`ring` 失败但 `ring!` 成功
%%%
tag := "ch07-debug-transparency"
%%%

**症状**：`ring` 报错，但 `ring!` 成功。

**诊断**：透明度问题。`ring` 使用 `.reducible` 透明度；`ring!` 使用 `.default` 透明度，展开更多定义。

**修复**：使用 `ring!`；或先 `unfold` 手动展开再用 `ring`；或把定义标记为 `@[reducible]`。

## 辅助诊断工具
%%%
tag := "ch07-debug-tools"
%%%

- **`ring_nf`**：不关闭目标，只做规范化——看看规范化后的残余形式
- **`ring_nf (config := { mode := .raw })`**：输出 `ring` 内部的原始范式表示，用于深度调试
- **`set_option trace.Meta.Tactic.norm_num true`**：跟踪 `norm_num`（`ring` 依赖的系数计算引擎）的执行
- **`set_option trace.Meta.synthInstance true`**：排查类型类合成失败

# 架构全景图
%%%
tag := "ch07-architecture"
%%%

```
用户层
┌─────────────────────────────────────────────────────┐
│  ring / ring!                                       │
│  ring_nf / ring_nf!                                 │
│  ring1 / ring1!                                     │
└───────────┬─────────────────────────────────────────┘
            │
宏展开层
┌───────────┴─────────────────────────────────────────┐
│  ring → first | ring1 | try_this ring_nf ...        │
│  ring_nf → transformAtLocation evalExpr cleanup     │
└───────────┬─────────────────────────────────────────┘
            │
Tactic 层 (TacticM)
┌───────────┴─────────────────────────────────────────┐
│  ring1 elab                                         │
│  · AtomM.run (管理原子编号)                          │
│  · proveEq (提取等式、合成实例)                      │
│  · ringCore (核心证明生成)                           │
└───────────┬─────────────────────────────────────────┘
            │
规范化层 (AtomM / MetaM)
┌───────────┴─────────────────────────────────────────┐
│  Common.eval ←── 核心递归                           │
│  ├── 模式匹配 head function                         │
│  │   ├── +  → eval 两侧 → evalAdd (归并)           │
│  │   ├── *  → eval 两侧 → evalMul (分配)           │
│  │   ├── ^  → eval 底、指数 → evalPow              │
│  │   ├── -  → eval → evalNeg (系数取负)             │
│  │   ├── /  → eval → evalInv + evalMul              │
│  │   └── 其他 → derive (norm_num) 或 evalAtom       │
│  ├── 范式比较: ExSum.eq                              │
│  └── 证明拼接: of_eq pa pb                          │
└─────────────────────────────────────────────────────┘

数据层
┌─────────────────────────────────────────────────────┐
│  ExSum (多项式 = 单项式有序链表)                     │
│  ├── ExProd (单项式 = base^exp 乘积链)              │
│  │   └── ExBase (基 = 原子 | 嵌套和)                │
│  └── ExSumNat / ExProdNat / ExBaseNat (自然数指数)   │
│                                                     │
│  RingCompute (系数运算接口)                          │
│  ├── RatCoeff (有理系数)                             │
│  └── 委托 norm_num 做数值计算                        │
│                                                     │
│  Cache (类型类实例缓存)                              │
│  ├── CommRing? (允许取负/减法)                       │
│  ├── Semifield? (允许除法/求逆)                      │
│  └── CharZero? (保证非零除数)                        │
│                                                     │
│  Result (规范化表达式 + 范式数据 + 等式证明)          │
└─────────────────────────────────────────────────────┘
```

# 练习
%%%
tag := "ch07-exercises"
%%%

## 练习 1：基础展开
%%%
tag := "ch07-exercise-1"
%%%

证明以下等式：

```
-- (a) 立方和公式
example (a b : ℤ) :
    a ^ 3 + b ^ 3 = (a + b) * (a ^ 2 - a * b + b ^ 2) := by
  sorry

-- (b) 完全立方展开
example (x y : ℤ) :
    (x - y) ^ 3 = x ^ 3 - 3 * x ^ 2 * y + 3 * x * y ^ 2 - y ^ 3 := by
  sorry
```

## 练习 2：`ring_nf` 化简
%%%
tag := "ch07-exercise-2"
%%%

使用 `ring_nf` 化简假设后完成证明：

```
-- 提示：ring_nf at h 化简假设，然后用 linarith
example (x : ℤ) (h : (x + 2) ^ 2 = (x + 1) ^ 2 + 5) : x = 1 := by
  sorry
```

## 练习 3：`linear_combination`
%%%
tag := "ch07-exercise-3"
%%%

使用 `linear_combination` 完成以下证明。关键是找到正确的系数：

```
-- (a)
example (a b : ℤ) (h1 : a + b = 10) (h2 : a - b = 4) : a = 7 := by
  sorry
  -- 提示：h1 和 h2 应该以什么系数组合？

-- (b)
example (x y : ℤ) (h1 : x + y = 5) (h2 : x * y = 6) :
    x ^ 2 + y ^ 2 = 13 := by
  sorry
  -- 提示：x^2 + y^2 = (x+y)^2 - 2*x*y
```

## 练习 4：`field_simp` + ring
%%%
tag := "ch07-exercise-4"
%%%

消分母后用 `ring` 完成：

```
example (x : ℝ) (hx : x ≠ 0) :
    (x + 1 / x) ^ 2 = x ^ 2 + 2 + 1 / x ^ 2 := by
  sorry
  -- 提示：field_simp 然后 ring
```

## 练习 5：诊断失败
%%%
tag := "ch07-exercise-5"
%%%

以下 `ring` 调用都会失败。为每个找出失败原因并给出正确证明：

```
-- (a) 为什么失败？用什么替代？
-- example (n : ℕ) : n * (n + 1) / 2 + (n + 1) = (n + 1) * (n + 2) / 2 := by ring

-- (b) 为什么失败？用什么替代？
-- example (x : ℤ) (h : x > 0) : x ^ 2 > 0 := by ring

-- (c) 为什么失败？用什么替代？
-- example (x y : ℤ) (h : x = y + 1) : x ^ 2 = y ^ 2 + 2 * y + 1 := by ring
```

## 练习 6（源码阅读）
%%%
tag := "ch07-exercise-6"
%%%

阅读 `evalAdd` 的源码（Common.lean:573-594），回答以下问题：

1. `evalAddOverlap` 返回 `.zero` 时意味着什么？对应的数学操作是什么？
2. `va₁.cmp rcℕ rc vb₁` 返回 `.lt` 时，为什么选择 `va₁` 留在前面？
3. 如果两个多项式都只有一个单项式且不同类，`evalAdd` 需要几步递归？

# 下一章预告
%%%
tag := "ch07-next-chapter"
%%%

`ring` 解决的是可交换环上的**等式**问题。下一章进入 `omega`——线性整数/自然数算术的完备决策过程，它能处理 `ring` 无法触及的**不等式**和**自然数减法**。
