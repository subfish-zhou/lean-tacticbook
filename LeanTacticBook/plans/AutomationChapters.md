# Ch08–Ch12 自动化证明术写作计划

> 状态：待作者审定后逐章实施。
>
> 版本基准：Lean `leanprover/lean4:v4.32.2`；Mathlib revision `905b95818eb32af7874a58b427f50c1711a5e96c`。
>
> 前置：Ch04 `CoreM`、Ch05 `MetaM`、Ch06 `TermElabM`、Ch07 `TacticM`。其中 Ch05 完整承担 Expr、局部上下文、元变量与证明项工程；Ch06 承担 expected type、postponement、synthetic mvar 与 recovery；Ch07 承担活动目标队列、dispatcher 与回滚。

## 一、总体次序

```text
Ch08  exact?：从 apply 到全库搜索
Ch09  ring：带证明的多项式规范化
Ch10  linarith：寻找证书，重建矛盾
Ch11  grind：共享推理状态上的饱和搜索
Ch12  bv_decide：外部求解器、LRAT 证书与实际信任边界
```

次序沿系统复杂度推进：

```text
局部 apply
→ 全库候选搜索
→ 确定性规范化
→ oracle 与证书重建
→ 多引擎协同推理
→ 外部求解器、形式化 checker 与原生求值桥
```

- Ch08 紧接 Ch06 的 `exact?%` 与 Ch07 的 `apply`，打开此前当作后端使用的 Library Search。
- Ch09 引入重化、规范形和 proof-carrying computation。
- Ch10 依赖 Ch09：当前 `linarith` verification 默认用 `ring1` 验证线性组合归零；`nlinarith` 只作末尾扩展。
- Ch11 综合索引、统一、E-graph、E-matching、专用求解器、分支与回溯。
- Ch12 收束反射、bit-blasting、外部 SAT、LRAT checker、soundness theorem、`nativeEqTrue` 与真实 TCB。

## 二、共同写作契约

每章同时服务两种用途：

1. **章首导论**：一至两节，含真实例子、完整管线图、算法核心和信任结论；教师可只讲此部分。
2. **自学正文**：逐步展开每条箭头，含生产源码纵切、受控缩小版、成功与失败实验、练习和答案。

共同叙事顺序：

```text
真实例子与输出
→ 数学或搜索契约
→ 朴素实现的困难
→ 内部表示
→ 主算法
→ proof / certificate 怎样产生
→ 状态、失败和资源边界
→ 生产源码纵切
→ 受控缩小版
→ 故意失败的实验
→ API 回查表
→ 练习
```

每章最低产物：

- 一个从用户命令到最终 proof 的完整调用图；
- 一个生产源码纵切；
- 一个受控缩小版实现；
- 一个成功 trace；
- 一个可重复的失败 trace；
- 一个状态、证明或证书损坏实验；
- 一张信任账本；
- 一张算法边界表；
- 基础练习正文答案；
- 进阶练习测试与提示，完整实现放 examples；
- 一个独立 examples module；
- `#print axioms` 或等价公理锥检查。

## 三、Ch08 `exact?`：从 `apply` 到全库搜索

### 3.1 章首导论

主图：

```text
目标类型
→ lazy discrimination tree 粗筛
→ 候选 declaration
→ Meta apply
→ solveByElim 处理子目标
→ 成功后的 mctx
→ Try this 建议或正式 proof Expr
```

核心契约：Library Search 根据目标形状寻找一条主引理，再用小规模局部搜索处理参数；它不承担任意深度的全库证明搜索。

### 3.2 贯穿例

在独立 namespace 建一座可控小型定理库，含：

- 唯一结论头候选；
- 结论相似但前提不可解的干扰候选；
- 当前文件候选与 imported candidate；
- `Iff` 的两个方向；
- 对称等式目标；
- 应用后留下两个子目标的 theorem。

沿同一目标观察索引、排序、apply、子目标搜索、partial result 与建议生成。

### 3.3 正文节次

1. 从 Ch06 `exact?%` 回到 Library Search 后端。
2. 查询对象：intros、目标类型、instantiate mvars、head-beta。
3. 声明入索引：打开 `∀` 前缀、提取结论、过滤声明、`Iff.mp`/`.mpr`。
4. Lazy discrimination tree：key path、常量头、箭头、projection、literal、wildcard、specificity。
5. Imported index 与当前文件 declarations 的分工。
6. 候选召回与排序：当前文件优先、具体匹配分数、稳定次序、原目标/对称目标交错、star fallback、heartbeat。
7. 候选应用：constant Expr、modifier、`MVarId.apply`、参数 mvars、统一。
8. `solveByElim`：局部事实、默认小引理、DFS、最大深度、构造子政策、required terms、可选 Grind discharger。
9. 状态纪律：每个候选的 Meta snapshot、失败恢复、完整解与 partial mctx。
10. `exact?`、`apply?`、`exact?%`、`+all` 的提交、建议与 sorry/admit 边界。
11. TryThis：pretty-print、初始状态重放、`expose_names`、source ref、suggestion validation。
12. 可信性与失败分类：漏召回、排序、资源耗尽、统一失败、建议失败、kernel 拒绝。
13. `toy_exact?`：当前文件、结论头分桶、apply、assumption、rollback、建议。
14. 生产源码纵切与 API 回查表。
15. 基础、进阶、挑战练习。

### 3.4 源码入口

```text
Lean/Meta/Tactic/LibrarySearch.lean
Lean/Meta/LazyDiscrTree.lean
Lean/Meta/Tactic/SolveByElim.lean
Lean/Elab/Tactic/LibrarySearch.lean
Lean/Meta/Tactic/TryThis.lean
```

### 3.5 关键边界

- discrimination tree 返回值得尝试的 declarations，不返回证明；
- `exact?` 正常成功、`apply?` 部分建议、collect-all、`exact?%` recovery 必须分写；
- “显示 Try this”与“替换后独立重编译通过”是两件事。

## 四、Ch09 `ring`：带证明的多项式规范化

### 4.1 章首导论

```text
Lean Expr
→ 识别代数结构与原子
→ 重化为多项式规范形
→ 两边规范化
→ 比较规范形
→ 拼接“原式 = 规范形”的证明
→ kernel
```

核心命题：`ring` 把等式证明化为确定性规范化；规范化的每一步都携带等式证明。

### 4.2 正文节次

1. `ring`、`ring1`、`ring_nf` 的真实输出与职责。
2. 支持的交换半环/环语言及边界：常量、加乘、幂、负号、减法、casts、scalar multiplication、未知原子。
3. 逐条重写的组合爆炸与规范形策略。
4. 数学多项式规范形与手算例。
5. 生产三层表示：`ExBase`、`ExProd`、`ExSum`、coefficients、atom indices、exponents、ordering invariants。
6. 原子分配：停止解析的位置、atom map、definitional equality、transparency、`ring!`。
7. Qq 读法插页：typed quotation、splice、`Q($α)`、typed equality witness。
8. Proof-carrying result：原 Expr、规范形、原式等于规范形的证明。
9. numeral/rational coefficient 与 `norm_num`。
10. 加法规范化与证明。
11. 乘法、分配律、单项式排序与证明。
12. 负号、减法、幂、casts、scalar multiplication。
13. 两边规范形比较及最终证明拼接。
14. `ring` macro 如何先试 `ring1`，再用 `ring_nf` 给出提示。
15. `ring_nf` 的目标/假设/conv/recursive 行为。
16. 可信性账本：元层排序、atom 编号、系数计算、proof Expr、kernel。
17. 受控 toy normalizer 与生产源码对照。
18. 失败边界、性能实验、源码纵切、练习。

### 4.3 源码入口

```text
Mathlib/Tactic/Ring/Common.lean
Mathlib/Tactic/Ring/Basic.lean
Mathlib/Tactic/Ring/RingNF.lean
```

沿 `x * (y + z)` 追一条完整 proof-carrying normalization 路径。

## 五、Ch10 `linarith`：寻找证书，重建矛盾

### 5.1 章首导论

```text
目标取反
→ 比较式预处理
→ 线性多项式
→ oracle 寻找非负系数
→ verification 重建不等式证明
→ ring1 证明线性组合等于零
→ False
```

核心命题：oracle 负责找证书，Lean 端依据证书重建矛盾证明；oracle 的正确性不进入信任基础。

### 5.2 正文节次

1. 从可手算的三条比较式开始。
2. 数学证书：`tᵢ Rᵢ 0`、非负整数系数、严格项参与、线性组合归零。
3. equality、weak/strict comparison、dense order 与整数边界。
4. 目标取反、比较式引入、等式目标、非比较目标的 `exfalso`。
5. 公共预处理：conjunction、negation、Nat→Int、Nat 非负、整数严格不等式、`t R 0`、分母、按类型分组、branching preprocessors。
6. 线性表达式解析：atom map、coefficients、常数齐次化、线性乘法、透明度。
7. Oracle 接口：比较式列表到 certificate coefficients；不构造 Lean proof。
8. 手写固定 oracle：正确证书通过，错误证书被 verification 拒绝。
9. Fourier–Motzkin：消元、来源向量、中间式增长、证书回读。
10. Simplex：LP 化、tableau、basic/nonbasic、pivot、Bland rule、正向量提取。
11. Verification 主线：按系数数乘证明、逐项相加、strictness bookkeeping、构造归零等式、`ring1`、推出 `False`。
12. `linarith?`、unused-hypothesis minimization、`only`、custom preprocessors/oracles、trace。
13. `nlinarith` 扩展：平方非负、成对差之积、ring normalization、单项式线性化、规模增长与不完备性。
14. 可信性账本、源码纵切、受控 parser/oracle/verifier、练习。

### 5.3 源码入口

```text
Mathlib/Tactic/Linarith/Frontend.lean
Mathlib/Tactic/Linarith/Preprocessing.lean
Mathlib/Tactic/Linarith/Parsing.lean
Mathlib/Tactic/Linarith/Datatypes.lean
Mathlib/Tactic/Linarith/Oracle/SimplexAlgorithm/
Mathlib/Tactic/Linarith/Oracle/FourierMotzkin.lean
Mathlib/Tactic/Linarith/Verification.lean
```

### 5.4 内容比例

正文主体讲 `linarith` 核。`nlinarith` 占本章末尾约一成，只解释它如何生成有限的非线性推论并复用同一 oracle/verifier。

## 六、Ch11 `grind`：共享推理状态上的饱和搜索

### 6.1 章首导论

```text
规范化
→ internalize 到 E-graph
→ congruence closure
→ theorem E-matching
→ propagators
→ theory solvers
→ case split
→ 新事实写回
→ 饱和、闭合或达到资源界限
```

核心命题：Grind 维护共享推理状态，让等式、定理实例、逻辑传播和理论求解器反复交换新事实。

### 6.2 正文节次

1. 三个递进例：congruence、E-matching、算术与逻辑协作。
2. 与 Library Search 对照：逐候选搜索与事实饱和。
3. GrindM/GoalM、e-nodes、equivalence classes、facts、origins、generations、queues、solver states、branches、counters。
4. 预处理：simp/simprocs、reducible、projection、subsingleton、normalization、canonicalization、hash-consing。
5. Internalization：命题与 True/False 类、等式触发 merge。
6. Congruence closure：union-find 直觉、application signatures、collision、disequality、constructor disjointness/injectivity、proof origins。
7. E-matching：active theorems、patterns、head-symbol app map、modulo equality、choice stack、generation 与 instance limits。
8. Propagators：逻辑、等式、constructor、projection、injectivity、forall、算术事实。
9. Theory solver 总接口及 Nat/Int arithmetic、linear ring、commutative ring/Grobner、order、AC、injectivity 概览。
10. 选一个 solver 做完整纵切，其余放源码索引。
11. 调度与饱和：worklist、delayed facts、rounds、stuck、success、failure。
12. Case split、CPS、branch-local state、非时间顺序回溯、model-based theory combination。
13. 默认资源界限及启发式不完备性。
14. Proof reconstruction：fact origin、merge reason、theorem instance、solver proof、case split proof、最终 Expr。
15. Diagnostics：`trace.grind.assert`、counters、split/E-match trace、`grind?`。
16. `+suggestions` premise selector；默认 Grind 不扫描全库。
17. theorem pattern 与小型 grind-set；propagator API 仅作挑战。
18. 源码纵切、成功/失败实验、练习。

### 6.3 源码入口

```text
Lean/Elab/Tactic/Grind/
Lean/Meta/Tactic/Grind/Types.lean
Lean/Meta/Tactic/Grind/Main.lean
Lean/Meta/Tactic/Grind/Internalize.lean
Lean/Meta/Tactic/Grind/Core.lean
Lean/Meta/Tactic/Grind/EMatch.lean
Lean/Meta/Tactic/Grind/Propagate.lean
Lean/Meta/Tactic/Grind/Split.lean
Lean/Meta/Tactic/Grind/Action.lean
Lean/Meta/Tactic/Grind/Finish.lean
Lean/Meta/Tactic/Grind/Proof.lean
Lean/Meta/Tactic/Grind/CheckResult.lean
```

## 七、Ch12 `bv_decide`：证书与实际信任边界

### 7.1 章首先看公理锥

用真正进入 SAT 管线的 BitVec 乘法交换律：

```lean
import Std.Tactic.BVDecide

theorem mul_comm_bv8 (x y : BitVec 8) : x * y = y * x := by
  bv_decide

#print axioms mul_comm_bv8
```

Lean 4.32.2 的公理锥会出现形如：

```text
mul_comm_bv8._native.bv_decide.ax_...
```

章首先提出：

1. LRAT checker 已有 soundness theorem，为什么仍有新增公理？
2. 这条公理断言什么？
3. CaDiCaL 是否进入公理锥？
4. `bv_check` 能否删除该公理？

### 7.2 完整管线

```text
原目标
→ 前处理与反证化
→ BVLogicalExpr
→ bit-blasting
→ AIG
→ AIG.toCNF
→ CaDiCaL
→ LRAT / SAT assignment
→ Lean parser + LRAT checker
→ verifyBVExpr expr cert = true
→ checker、CNF、bit-blaster soundness
→ BVLogicalExpr.Unsat
→ reflectionResult.proveFalse
→ 原目标
```

### 7.3 正文节次

1. `Decidable P`、`decide P : Bool`、反射语义和 checker bridge。
2. 前处理与反射：`bvNormalize`、`reflectBV`、`bvExpr`、`expr`、`proveFalse`、unused hypotheses、不透明 atoms。
3. `BVExpr`、`BVPred`、`BVLogicalExpr` 与 denotation。
4. Bit-blasting：选加法器完整讲，乘法、比较、shift、extract、append 建索引表；每项分 Impl 与 Lemmas。
5. AIG：共享节点与语义。
6. AIG→CNF：Tseitin 风格子句、辅助变量、`AIG.toCNF_equisat`、DIMACS relabeling。
7. CaDiCaL 的职责：SAT assignment、UNSAT+LRAT、恶意或错误 solver 的各类结果。
8. LRAT 数据：literal、clause、CNF、ids、RUP、RAT、hints、deletion、empty clause。
9. RUP 的单位传播检查及 soundness。
10. RAT 的 pivot/resolvent 检查及 soundness。
11. Parser、`IntAction`、compact checker、failure results、malformed certificate。
12. Checker soundness 链：`compactLratChecker_sound`、`LRAT.check_sound`、`verifyCert_correct`、`unsat_of_verifyBVExpr_eq_true`。
13. `verifyBVExpr` 汇合 bit-blasting、AIG/CNF 与 LRAT 正确性。
14. Proof production：辅助定义、certificate data、reflection proof、`proveFalse`、目标赋值。
15. **中心节：`nativeEqTrue`**。闭合 Bool Expr 被原生编译和运行；得到 true 后，系统加入 `verifyBVExpr expr cert = true` 的局部 axiom，再应用 soundness theorem。
16. 三张 TCB 图：外部搜索边界、形式化逻辑边界、原生求值边界。
17. `bv_decide?` 保存 LRAT；`bv_check` 离线重放，不调用 solver，但仍使用 `nativeEqTrue`，不会消除 `_native.bv_decide.ax...`。
18. SAT/counterexample 路径：assignment 映回 atoms，诊断数据与证明的区别。
19. 规范化直接关闭与真正进入 SAT 的两个目标做 `#print axioms` 对照。
20. 损坏证书、错误 clause id、无效 parser 输入、solver timeout、离线重放实验。
21. 源码纵切、信任矩阵、练习。

### 7.4 信任结论

严禁写成“CaDiCaL 不可信，所以最终只信 kernel”。准确结论：

- CaDiCaL 的 UNSAT 声明必须附带 LRAT，因此它不进入直接的健全性边界；
- bit-blasting、AIG/CNF、LRAT checker 与 reflection 的正确性由 Lean theorem 约束；
- Lean 4.32.2 通过 `nativeEqTrue` 原生执行 checker 并加入等式公理；实际 TCB 还包含原生代码生成、运行时与该 axiom bridge；
- `bv_check` 消除构建时外部 solver 依赖，不消除原生求值公理。

### 7.5 源码入口

```text
Lean/Elab/Tactic/BVDecide/
Lean/Meta/Tactic/BVDecide/Main.lean
Lean/Meta/Tactic/BVDecide/Normalize/
Lean/Meta/Tactic/BVDecide/Reflect/
Lean/Meta/Tactic/BVDecide/Prover/
Lean/Meta/Tactic/BVDecide/External.lean
Lean/Meta/Tactic/BVDecide/LRAT/
Std/Tactic/BVDecide/Bitblast/
Std/Tactic/BVDecide/LRAT/
Lean/Meta/Native.lean
```

## 八、跨章内容账本

| 主题 | 首次完整讲解 | 后章引用方式 |
|---|---|---|
| 候选 apply 与 mctx 回滚 | Ch08 | Ch11 只比较搜索结构 |
| 重化与 proof-carrying normalization | Ch09 | Ch10、Ch12 直接引用 |
| oracle 与 certificate verification | Ch10 | Ch12 提升到外部 solver |
| discrimination tree | Ch08 | Ch11 只讲 appMap/pattern 索引 |
| E-graph 与饱和 | Ch11 | Ch12 不重复 |
| 外部证书与 formal checker | Ch12 | 全书信任专题收束 |
| `nlinarith` | Ch10 末尾 | 不单立章 |
| `grobner` | Ch11 theory solver | 不单立章 |

## 九、逐章验收门

每章分别通过：

- examples module 构建；
- highlighted examples 构建；
- anchor 与 examples 对齐；
- 章节局部构建；
- 整书构建；
- HTML 渲染；
- source path 与 pinned revision 核对；
- 关键行为 probe 与失败 probe；
- `#print axioms`；
- 技术审读；
- 教学审读；
- 主线程逐句文风审读；
- `git diff --check` 与本地链接检查。
