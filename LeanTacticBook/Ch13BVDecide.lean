import VersoManual
import LeanTacticBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "examples"
set_option verso.exampleModule "Examples.Ch13BVDecide"

#doc (Manual) "BVDecide：位向量怎样变成可检查证明" =>
%%%
file := "Ch13BVDecide"
tag := "ch13-bv-decide"
%%%

> *本章目标*：从固定宽度位向量只有有限种输入开始。我们先把位运算拆成布尔门，再把“存在反例吗”交给 SAT 求解器；求解器若声称没有反例，必须带回一份 Lean 能检查的记录。最后单独核对原生计算怎样把检查结果送入逻辑。
>
> *版本基准*：Lean `leanprover/lean4:v4.32.2`，commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`。

`BitVec w` 表示恰有 `w` 个 bit 的无符号向量。加法和乘法按模 `2^w` 计算；例如 `BitVec 8` 的值超出范围后按模 256 回绕。它不是任意精度自然数。

固定宽度带来一个直接办法：枚举所有输入，检查等式是否总成立。宽度增加时，输入数呈指数增长，逐个枚举很快失去实用性。本章寻找更紧凑的办法：把运算翻译成布尔约束，询问“是否存在使目标失败的输入”。

# 第一步：把 Lean 目标收进一门有限语言
%%%
tag := "ch13-s03"
%%%

先把目标改写成反证问题。证明 `x * y = y * x`，等价于证明“不存在 `x * y ≠ y * x` 的输入”。前端先做普通化简，再把支持的位向量表达式翻译成一门只描述固定宽度运算和布尔连接词的内部语言。

这种“从一般 Lean Expr 翻进专用内部语言”的步骤与 Ch10 相同，叫 reification（重化，也常称反射输入构造）。生产前处理还包含结构体、枚举、整数到位向量的转换、合取扁平化等规则；第一遍只追位向量乘法。

若遇到不支持的子表达式，系统可能把它整体当作 opaque atom（内部不分析的原子）。这种抽象会忘掉原子的某些语义关系，因此后面找到的反例可能只是抽象问题的反例。它可用于诊断，不能自动成为原命题为假的证明。

# 内部语言还必须有语义
%%%
tag := "ch13-s04"
%%%

内部语言分三层：`BVExpr` 表示固定宽度位向量运算，`BVPred` 表示相等和大小比较，`BVLogicalExpr` 用“且、或、非”等布尔连接词组合命题。

只有语法树还不够。denotation（语义解释）规定每棵内部语法树在一组输入下算出哪个实际 `BitVec` 或 `Bool` 值。正确性定理再把内部求值与原 Lean Expr 联系起来。

反射正确性需要两端：

1. Meta 层从 Lean Expr 建出正确 reflected syntax；
2. theorem 层证明 reflected syntax 的 denotation 与原 Expr 对应。

只有数据结构没有语义 theorem，仍只是另一个程序表示。

# 第二步：把每个宽运算拆成布尔门
%%%
tag := "ch13-s05"
%%%

一个 `w` 位变量可以拆成 `w` 个布尔变量。把位向量运算逐位编译成 AND、OR、XOR、NOT 等布尔门，叫 bit-blasting（位爆破）。名字听起来猛烈，实质就是把“宽数据”摊成“每一位怎么计算”。

以加法为例，加法器从低位到高位维护 carry（进位）：

:::codeBox "pseudocode"
```
sum_i       = x_i xor y_i xor carry_i
carry_{i+1} = ((x_i xor y_i) and carry_i) or (x_i and y_i)
            = atLeastTwo(x_i, y_i, carry_i)
```
:::

低位不依赖高位。生产 carry gate 使用上面的 xor/and/or 公式，正确性层再证明它等价于 `Bool.atLeastTwo`；对应锚点包括 `denote_mkFullAdderCarry` 与 `atLeastTwo_eq_halfAdder`。每一位的实现位于 `Circuit/Impl/Operations/`，配套正确性 theorem 位于 `Circuit/Lemmas/Operations/`。读源码时应把实现与对应 lemma 成对阅读。

下面的小型加法交换律在锁定环境中被预处理直接关闭，没有暴露 native SAT axiom；它提醒我们不能凭 tactic 名判断实际走了哪条路径。

```anchor bv_small_preprocessed
theorem bvSmallAdderPreprocessed (x y : BitVec 4) : x + y = y + x := by
  bv_decide
```

完整乘法例才是本章的 trust probe。

# 重复子电路必须共享
%%%
tag := "ch13-s06"
%%%

直接把所有布尔门展开成树，会复制大量相同子电路。AIG 是 and-inverter graph（与门反相图）：它只用“与”和“取反”表示电路，并用 directed acyclic graph（有向无环图，DAG）让多个父节点共享同一子电路。hash-consing 在构造时查找已有的相同节点，避免重复创建。每个输出只需指向某个节点或它的反相。

AIG 的节点编号、共享策略和简化都属于计算层。下一步还要把共享电路转成求解器能接收的子句；到转换一节再定义这种格式以及对应的正确性定理。

# 第三个问题：电路是否存在使目标失败的输入
%%%
tag := "ch13-s02-vocab"
%%%

SAT 问题只问一件事：一组布尔约束是否存在满足它的真假 assignment（赋值）。若存在，称为 SAT（可满足）；若不存在，称为 UNSAT（不可满足）。在本章，SAT 赋值对应一个可能的反例输入；UNSAT 表示没有反例。

求解器常接收 CNF（合取范式）。Boolean variable 取 `true` 或 `false`；literal（文字）是变量 `p` 或否定 `¬p`；clause（子句）是若干文字的“或”；CNF 是若干子句的“且”。empty clause（空子句）一个可选文字也没有，所以永远不满足；能从原子句推出空子句，就证明整组约束 UNSAT。

unit clause（单位子句）只含一个文字，因此强制该文字为真。unit propagation（单位传播）反复利用这种强制选择简化其它子句。例如：

:::codeBox "pseudocode"
```
clause 1:  p
clause 2: ¬p ∨ q

要用 RUP 检查新 clause 3: q：
  暂时加入 ¬q
  clause 2 变成 ¬p
  与 clause 1 的 p 冲突
所以当前 CNF 蕴含 q
```
:::

“等可满足”只要求旧公式有满足赋值当且仅当新公式有满足赋值；它不要求两份公式使用同一组变量，也不要求字面相等。Tseitin 转换正是借助辅助变量得到体积受控的等可满足 CNF。

# 把共享电路翻成求解器输入
%%%
tag := "ch13-s07"
%%%

AIG 适合共享电路，SAT 求解器则接收 CNF。Tseitin conversion（蔡廷转换）为每个内部电路节点引入一个辅助变量，再用少量局部子句约束该变量与子节点的关系。这样避免把共享电路展开成巨大公式。

转换结果要求 equisatisfiable（等可满足）：原电路存在满足赋值，当且仅当新 CNF 存在满足赋值。两份公式可以使用不同变量，也不要求逐字等价。

:::codeBox "pseudocode"
```
z ↔ (x ∧ y)
→ (¬z ∨ x)
  (¬z ∨ y)
  (z ∨ ¬x ∨ ¬y)
```
:::

DIMACS relabeling 又把内部 literals 映到 solver 使用的整数编号。证书回来时必须沿同一映射解释 clause ids 和 literals。

# 外部 SAT 求解器只负责搜索
%%%
tag := "ch13-s08"
%%%

本书锁定环境调用外部程序 CaDiCaL 搜索 CNF。它可能返回：

- SAT 时返回 assignment；
- UNSAT 时返回一份逐步推出矛盾的记录；下一节再给这种记录写出格式名；
- 也可能超时、崩溃、输出 malformed 文件或给错误答案。

CaDiCaL 的 UNSAT 字符串不能直接关闭 Lean goal。只有 LRAT 被解析并由 checker 接受，后续 soundness chain 才能推进。Solver 因而不在直接逻辑信任边界中；它仍在可用性、性能、资源和文件 IO 边界中。

# UNSAT 答案必须附带可检查记录
%%%
tag := "ch13-s09"
%%%

求解器若声称 UNSAT，不能只返回一个字符串。它还输出一串可重放动作，说明怎样从原子句逐步推出空子句。这份记录叫 certificate（证书）；本章使用的格式叫 LRAT。动作带有 clause id（子句编号），可以添加新子句、给出检查 hints（提示）或删除不再需要的旧子句。

RUP (reverse unit propagation) 检查：暂时加入目标 clause 的否定，按 hints 做 unit propagation；若产生冲突，目标 clause 由当前 CNF 蕴含。

RAT (resolution asymmetric tautology) 检查：选 pivot，对含互补 pivot 的 clauses 检查 resolvents 具有适当的 RUP 性质。RAT 更强，也更复杂。

Deletion 不会破坏 checker 的 soundness，但删掉后续 hints 仍需引用的 clause 会让检查失败。正确的删除主要用于控制工作集合与性能；soundness theorem 保证删除本身不会让无效推导变有效。

# Lean 先解析记录，再逐步检查
%%%
tag := "ch13-s10"
%%%

外部 `.lrat` 文件先由 parser（解析器）读成紧凑动作数组 `Array IntAction`。`compactLratChecker` 逐条消费数组，需要时才把当前 `IntAction` 展开成便于检查的 `DefaultClauseAction`；它不会预先再造一份完整证书。

checker（检查器）是返回 `Bool` 的可执行程序。单有程序仍不够；soundness theorem（健全性定理）证明：若 checker 返回 `true`，原 CNF 确实 UNSAT。

仓库固定了两份负例：第一份不是 LRAT 文本；第二份仍能解析，但把合法证书中的一个 literal 改反。`#guard_msgs` 让二者的失败都成为可编译回归测试：

```anchor bv_reject_bad_certificates
/--
error: SAT solver produced invalid LRAT: offset 0: digit expected
-/
#guard_msgs in
example (x y : BitVec 4) : x * y = y * x := by
  bv_check (binaryProofs := false) "Fixtures/ch13-malformed.lrat"

/--
error: Tactic `bv_decide` failed: The LRAT certificate could not be verified; evaluating the following term returned `false`:
  Std.Tactic.BVDecide.Reflect.verifyBVExpr _example._expr_def_1 _example._cert_def_1
-/
#guard_msgs in
example (x y : BitVec 4) : x * y = y * x := by
  bv_check (binaryProofs := false) "Fixtures/ch13-invalid-proof.lrat"
```

第一例在 parser 处报 `digit expected`；第二例到 checker 才得到 `verifyBVExpr ... returned false`。这一区分说明只测 parser 不能证明 checker 会拒绝语法合法的伪 RUP/RAT。

# `verifyBVExpr` 汇合两条链
%%%
tag := "ch13-s11"
%%%

`verifyBVExpr expr cert` 重新 bit-blast reflected expression、构造 AIG/CNF，并运行 LRAT checker。其正确性 theorem 把：

- checker soundness；
- certificate/CNF 对齐；
- AIG-to-CNF equisatisfiability；
- bit-blaster correctness；
- reflected expression semantics

串成 `expr` unsatisfiable。最后 `reflectionResult.proveFalse` 把反射结论送回原目标。

# 计算链与定理链必须分开
%%%
tag := "ch13-s02"
%%%

计算链：

:::codeBox "pseudocode"
```
original goal
→ normalization / contradiction form
→ BVLogicalExpr
→ bit-blasted AIG
→ relabeled CNF
→ external CaDiCaL
→ LRAT certificate or SAT assignment
→ parse and check
→ verifyBVExpr expr cert = true
```
:::

逻辑链：

:::codeBox "pseudocode"
```
LRAT.check_sound
→ verifyCert_correct
→ AIG.toCNF_equisat
→ BVLogicalExpr.unsat_of_bitblast
→ unsat_of_verifyBVExpr_eq_true
→ reflectionResult.proveFalse
→ original goal
```
:::

第一条链成功运行不等于第二条链已经有 proof。连接点正是 `verifyBVExpr expr cert = true`。

# `nativeEqTrue` 怎样把计算结果送入逻辑
%%%
tag := "ch13-s12"
%%%

问题是怎样得到 premise：

:::codeBox "code"
```
verifyBVExpr expr cert = true
```
:::

Lean 4.32.2 的 `LratCert.toReflectionProof` 调用 `nativeEqTrue`。它把闭合 Boolean checker expression 编译成本机代码并执行；若结果为 true，就向 Environment 加入一条断言该 equality 的 axiom。随后才把这条 axiom 交给形式化 soundness theorem。

因此真实描述是：

:::codeBox "pseudocode"
```
native compiler/runtime computes true
→ generated local axiom: checker = true
→ kernel-checked soundness theorems consume that premise
→ proof of original goal
```
:::

“Checker 已经形式化，所以只信 kernel”少算了原生求值桥。实际 TCB 还包括 native code generation、runtime 和 `nativeEqTrue` 加 axiom 的机制。

# 同一个 tactic 名可能走不同证明路径
%%%
tag := "ch13-s01"
%%%

一个容易被预处理直接关闭的目标：

```anchor bv_normalization_only
theorem bvNormalizationOnly (x : BitVec 8) : x + 0 = x := by
  bv_decide
```

一个强制走完整 SAT/LRAT 管线的目标：

```anchor bv_full_pipeline
set_option trace.Meta.Tactic.bv true in
set_option trace.Meta.Tactic.sat true in
theorem bvFullPipeline (x y : BitVec 8) : x * y = y * x := by
  bv_decide
```

Trace 确认后者反射成：

:::codeBox "code"
```
!((var0 * var1) == (var1 * var0))
AIG has 735 nodes
SAT solver found a proof
Compiling and evaluating reflection proof term
```
:::

两者的公理锥不同：

```anchor bv_axiom_probe
#print axioms bvNormalizationOnly
#print axioms bvFullPipeline
#print axioms bvSmallAdderPreprocessed
```

锁定输出中，`bvNormalizationOnly` 只有 `propext`；完整乘法例还出现 `Classical.choice`、`Quot.sound` 和：

:::codeBox "code"
```
bvFullPipeline._native.bv_decide.ax_1_5
```
:::

简单目标在前处理阶段已经关闭，复杂目标才进入 SAT/LRAT 路线。公理锥的差异说明不能只看脚本中都写了 `bv_decide`，还要追踪实际执行路径。

# 三张信任图
%%%
tag := "ch13-s13"
%%%

## 外部搜索边界
%%%
tag := "ch13-s13-external"
%%%

CaDiCaL、LRAT trimming、临时文件与 parser 可以造成拒绝、超时和性能损失；错误 UNSAT 必须被 checker 拒绝，不能直接变成 theorem。

## 形式化逻辑边界
%%%
tag := "ch13-s13-formal"
%%%

Bit-blaster、AIG/CNF、LRAT checker 与 reflection 的 correctness theorems 由 kernel 检查。若这些 theorem 本身有逻辑错误或内核有 bug，健全性受影响。

## 原生求值边界
%%%
tag := "ch13-s13-native"
%%%

Checker-equals-true 通过 native execution 和 generated axiom 进入。该桥是 `bv_decide` 完整 SAT 路线特有的可见公理来源。

# `bv_decide?` 与 `bv_check`
%%%
tag := "ch13-s14"
%%%

`bv_decide?` 保存 LRAT artifact，并建议：

:::codeBox "code"
```
bv_check "path/to/proof.lrat"
```
:::

仓库保存了一份由锁定版本生成并裁剪的 4-bit 乘法 LRAT fixture。下面把 `sat.solver` 故意设成不存在的路径，仍能只靠 `bv_check` 重放：

```anchor bv_offline_replay
set_option sat.solver "/definitely/not/a/solver" in
theorem bvOfflineReplay (x y : BitVec 4) : x * y = y * x := by
  bv_check (binaryProofs := false) "Fixtures/ch13-mul4.lrat"

#print axioms bvOfflineReplay
```

这证明 `bv_check` 在重放时读取固定 certificate，不再调用 CaDiCaL，因而移除了构建时 solver 依赖。

它没有移除 `nativeEqTrue`。上面的 `#print axioms` 仍显示 `bvOfflineReplay._native.bv_decide.ax_1_5`，因为 certificate checker 仍由 native bridge 计算并断言为 true。离线 replay 与 kernel-only verification 不是同义词。

# SAT 与 counterexample 路线
%%%
tag := "ch13-s15"
%%%

若 CaDiCaL 找到 assignment，前端把 bits 映回 reflected atoms，生成 counterexample 诊断。即使表达式完全受支持，这条 SAT assignment 在 `bv_decide` 中仍是诊断数据，不是 Lean 中“原命题为假”的证明对象；它只是更可靠地指出一个可复查输入。若 opaque unsupported atoms 参与，assignment 甚至可能不能对应原表达式的真实取值。

无论哪种 counterexample 都不是 proof object。因此，“SAT 返回一个赋值”最多让 `bv_decide` 报告候选反例并停止，不能在逻辑中证明否定命题。`bv_decide` 作为证明术只在 UNSAT certificate 路线成功关闭目标。

下面三句都错，闭卷复述时若说出其中一句，就说明信任链还没学会：

1. “SAT assignment 确凿证明原命题为假。”——错；在本 tactic 中它是待复查诊断，不是 Lean 的否定证明。
2. “`bv_check` 不调用 solver，所以只剩 kernel。”——错；离线重放仍使用 `nativeEqTrue`。
3. “复杂 SAT 目标还有一条 `rfl`/formal 模式，可让内核直接规约整个 LRAT checker 且公理锥为零。”——本章锁定实现没有把它作为 `bv_decide` 完整 SAT 路线的替代模式。简单目标若在前处理阶段关闭，只说明根本没有进入完整 SAT/LRAT 路线。

# 失败实验
%%%
tag := "ch13-s16"
%%%

```table
- 实验
- 应观察
---
- 把 LRAT 文件替换成普通文本
- parser 拒绝并给 offset
---
- 修改一个 clause id 或 hint
- checker 拒绝
---
- replay 时把 solver path 设成不存在
- `bv_check` 仍成功
---
- 对假命题运行 `bv_decide`
- SAT assignment / potentially spurious counterexample，不产生 proof
---
- 对不支持的 opaque expression
- 抽象警告或无法支持，不得假装完整
---
- 比较 normalization-only 与 full SAT 公理锥
- 后者出现 native axiom
```

# 生产源码纵切
%%%
tag := "ch13-s17"
%%%

:::codeBox "pseudocode"
```
Lean/Elab/Tactic/BVDecide/BVDecide.lean
Lean/Meta/Tactic/BVDecide/Main.lean
Prover/Basic.lean → Prover/Bitblast.lean

Std/Tactic/BVDecide/Bitblast/BVExpr/Basic.lean
Reflect/*
Circuit/Impl/Operations/Add.lean
Circuit/Lemmas/Operations/Add.lean

Std/Sat/AIG/CNF.lean
External.lean
LRAT/Cert.lean → Actions.lean
Internal/CompactLRATChecker.lean
Internal/CompactLRATCheckerSound.lean
LRAT/Checker.lean

Std/Tactic/BVDecide/Reflect.lean
Lean/Meta/Native.lean
BVTrace.lean / BVCheck.lean
```
:::

读源码要坚持“一个实现文件配一个 correctness theorem”。只读 Meta control flow 会漏掉逻辑链；只读 soundness theorem 又会漏掉 `nativeEqTrue` 的 premise 来源。

# 练习
%%%
tag := "ch13-s18"
%%%

## 基础：给管线边分类
%%%
tag := "ch13-s19"
%%%

把完整管线每条箭头标成 computation、IO、theorem application 或 proof production。

## 基础：两位加法器
%%%
tag := "ch13-s20"
%%%

手算 2-bit adder 的低位与 carry，并把每个 gate 对应到 Boolean equation。

## 进阶：Tseitin clauses
%%%
tag := "ch13-s21"
%%%

验证 `z ↔ (x ∧ y)` 的三个 clauses 对全部八种 assignments 的行为。

## 进阶：手查 RUP
%%%
tag := "ch13-s22"
%%%

给一个小 CNF 和 hints，手做 unit propagation，推出 empty clause。再故意删除一个 hint，确认检查停止。

## 挑战：微型 certificate checker
%%%
tag := "ch13-s23"
%%%

实现只支持 RUP additions 的 checker及 soundness theorem。先用普通 kernel reduction证明 `checker cert = true`；再改用 native axiom bridge，比较两个 theorem 的 axiom cones。

# 全书自动化路线的收束
%%%
tag := "ch13-s24"
%%%

五章的架构依次为：

:::codeBox "pseudocode"
```
exact?     结构索引 + apply + 小型局部搜索 + 可重放建议
ring       带证明的确定性规范化
linarith   不可信 certificate 搜索 + Lean proof reconstruction
Grind      E-graph 上的共享饱和与有界分支
bv_decide  外部 SAT + LRAT checker + native axiom bridge
```
:::

比较这些证明术，不能只看它们能证明哪些题；还要逐项核对内部表示、proof 生成方式、失败含义、资源界限和信任边界。
