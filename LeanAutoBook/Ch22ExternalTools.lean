import VersoManual
import LeanAutoBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Ch22ExternalTools"

#doc (Manual) "第二十二章 对接外部工具" =>
%%%
file := "Ch22ExternalTools"
tag := "ch22-external-tools"
%%%

*本章目标*：理解 Lean 4 如何与外部求解器（SAT/SMT/CAS/LLM）交互，
掌握证书模式和 oracle 模式的安全性区别，
学会使用 `IO.Process` API 实现外部调用，
并理解 LLM 辅助证明搜索的架构和信任模型。

在前两章我们学习了反射和性能工程。
但有些问题*超出 Lean 内部 tactic 的能力或效率边界*——
SAT 求解器处理百万变量的命题逻辑、
CAS 做 Gröbner 基计算、SMT 求解器做线性算术——
这些工具经过几十年优化，在 Lean 中重新实现既不现实也无必要。

本章讨论如何*安全地*借用外部计算能力，
同时保持 Lean 内核作为最终信任锚。

# 22.1 为什么对接外部工具
%%%
tag := "why-external-tools"
%%%

| 问题域 | 外部工具 | 为什么 Lean 不自己做 |
|--------|----------|---------------------|
| 命题 SAT | CaDiCaL、Kissat | CDCL 算法 + 启发式需百万行优化代码 |
| SMT | Z3、cvc5 | 理论组合框架极其复杂 |
| 符号计算 | Sage、Mathematica | Gröbner 基、积分、级数求和 |
| ITP 桥接 | Coq、Isabelle | 复用其他证明助手的引理库 |
| 证明搜索 | LLM（GPT、Claude） | 启发式 tactic 建议 |

核心张力：外部工具能*快速给出答案*，但 Lean 的保证依赖*内核检查*。
设计问题归结为：*如何利用外部计算能力而不破坏信任模型？*

# 22.2 证书（Certificate）模式
%%%
tag := "certificate-mode"
%%%

最安全的方式：外部工具生成*证书*，Lean 验证证书。

## 工作流程
%%%
tag := "certificate-workflow"
%%%

```
❶ Lean 把问题编码为外部格式（DIMACS、SMT-LIB、JSON）
❷ 启动外部进程，发送问题
❸ 外部工具求解，返回证书（resolution proof、多项式系数等）
❹ Lean 解析证书，在内核中验证正确性
❺ 验证通过 → 构造 Lean 证明项
```

*安全性*：即使外部工具有 bug 或返回垃圾数据，
Lean 内核会拒绝不正确的证书。外部工具*不在可信基础（TCB）中*。

## 案例：`polyrith`
%%%
tag := "case-polyrith"
%%%

```
-- [示意] polyrith 的使用
example (a b : ℚ) (h1 : a + b = 3) (h2 : a - b = 1) :
    a = 2 := by
  polyrith
  -- ▸ 内部流程：
  -- ❶ 编码：把 h1、h2 和目标转为多项式约束，序列化为 JSON
  -- ❷ 调用：发送给 Sage 服务器（远程 HTTP 请求）
  -- ❸ 求解：Sage 计算 Gröbner 基，找到系数 1/2 * h1 + 1/2 * h2
  -- ❹ 返回：系数作为证书
  -- ❺ 验证：Lean 用系数构造 linear_combination，由 ring 验证
```

关键：Sage 不在 TCB 中——验证完全由 `ring` 在 Lean 内核完成。

## 案例：SAT 证书
%%%
tag := "case-sat-certificate"
%%%

```
❶ Lean 把命题编码为 CNF（DIMACS 格式）
❷ 调用 CaDiCaL
❸ 求解器返回 LRAT 证书（resolution proof 的紧凑表示）
❹ Lean 中的 LRAT checker 验证每一步 resolution
```

LRAT 是 SAT 竞赛标准——Lean 只需一个高效 LRAT checker 即可对接任意求解器。

## 证书模式的代价
%%%
tag := "certificate-cost"
%%%

- *编码/解析开销*：MetaM 端代码量不小
- *验证开销*：内核验证证书消耗 heartbeats
- *证书膨胀*：SAT 的 resolution proof 可达 GB 级
- *工具依赖*：需要外部工具可用（网络或本地安装）

# 22.3 Oracle 模式
%%%
tag := "oracle-mode"
%%%

不安全但方便：*直接信任*外部工具的结果。

```
-- [示意] ⚠️ 不安全：引入新公理
axiom smt_oracle : ∀ p : Prop, Decidable p
-- ▸ 这不是合法公理——可以用它证明 False
```

## Oracle vs `native_decide`
%%%
tag := "oracle-vs-native-decide"
%%%

| | `native_decide` | Oracle（`sorry`/自定义公理） |
|---|---|---|
| 逻辑层面 | *不引入新公理* | 引入不可验证的假设 |
| 可信基础 | Lean 内核 + 编译器 | Lean + 外部工具 |
| 失败时 | 类型错误 | 可能引入矛盾 |
| Mathlib | 谨慎使用 | 不接受 |

*`native_decide` 不是 oracle*——它在已信任的编译环境中做更快的判定计算。

## Oracle 的合理场景
%%%
tag := "oracle-reasonable-scenarios"
%%%

```
❶ 快速原型：用 sorry 标记子目标，先完成整体架构
❷ 开发迭代：信任外部结果以加速编辑-编译循环
❸ 最终替换：逐步把 sorry 替换为证书模式或手动证明
```

永远不要把含 `sorry` 的代码合并到主分支。
`#check_no_sorry` 和 Mathlib CI 强制执行这一纪律。

# 22.4 实现外部调用
%%%
tag := "implementing-external-calls"
%%%

## `IO.Process.spawn`——流式交互
%%%
tag := "io-process-spawn"
%%%

```
-- [示意] 启动外部进程并流式通信
def callSolver (problem : String) : IO String := do
  let child ← IO.Process.spawn {
    cmd := "z3"                    -- ❶ 可执行文件
    args := #["-in", "-smt2"]     -- ❷ 命令行参数
    stdin := .piped                -- ❸ 管道式 stdin/stdout
    stdout := .piped
    stderr := .piped
  }
  child.stdin.putStr problem       -- ❹ 写入问题
  child.stdin.flush
  let stdout ← child.stdout.readToEnd  -- ❺ 读取输出
  let exitCode ← child.wait
  if exitCode ≠ 0 then
    throw <| IO.userError s!"z3 failed with exit code {exitCode}"
  return stdout
```

## `IO.Process.output`——一次性调用
%%%
tag := "io-process-output"
%%%

```
-- [示意] 简便版本，适合短时脚本
def callScript (input : String) : IO String := do
  let result ← IO.Process.output {
    cmd := "python3"
    args := #["solver_script.py", "--input", input]
  }
  -- ▸ result : { exitCode : UInt32, stdout : String, stderr : String }
  if result.exitCode ≠ 0 then
    throw <| IO.userError s!"script failed: {result.stderr}"
  return result.stdout
```

## 在 tactic 中使用
%%%
tag := "external-in-tactic"
%%%

`TacticM` → `MetaM` → 可执行 `IO`：

```
-- [示意] 在 tactic 中调用外部工具
elab "external_solve" : tactic => do
  let goal ← getMainTarget
  let smt2 := encodeGoal goal          -- ❶ 编码
  let result ← callSolver smt2         -- ❷ 调用（IO 操作）
  match parseSolverOutput result with   -- ❸ 解析
  | .sat cert =>
    let proof ← verifyCertificate cert goal  -- ❹ 验证证书
    closeMainGoal proof
  | .unsat   => throwError "solver says unsat"
  | .unknown => throwError "solver returned unknown"
```

# 22.5 编码与解码
%%%
tag := "encoding-decoding"
%%%

对接外部工具的大量工作在于*编码*（Lean Expr → 外部格式）和*解码*（外部输出 → 证书）。

```
-- [示意] 编码：Lean Expr → SMT-LIB
partial def encodeToSMT (e : Expr) : MetaM String := do
  if let some (a, b) ← matchAnd? e then       -- ❶ 匹配 And
    return s!"(and {← encodeToSMT a} {← encodeToSMT b})"
  else if let some (a, b) ← matchOr? e then   -- ❷ 匹配 Or
    return s!"(or {← encodeToSMT a} {← encodeToSMT b})"
  else if let some a ← matchNot? e then        -- ❸ 匹配 Not
    return s!"(not {← encodeToSMT a})"
  else                                          -- ❹ 不可识别 → 不透明变量
    let name ← mkFreshUserName `x
    return s!"{name}"
```

和反射中的 quote 一样，编码覆盖范围*直接决定工具能力边界*——
不可识别的构造被当作不透明变量，求解器无法分析其语义。

# 22.6 案例：LLM 辅助证明搜索
%%%
tag := "llm-assisted-proof-search"
%%%

## 架构
%%%
tag := "llm-architecture"
%%%

```
  Lean Server ──→ LLM API ──→ tactic 候选 ["simp", "ring", ...]
  (目标 + 上下文)                       │
       └── 逐个尝试执行 ←──────────────┘
           验证通过 → 接受；全部失败 → 报错
```

## 实现骨架
%%%
tag := "llm-implementation-skeleton"
%%%

```
-- [示意]
elab "llm_suggest" : tactic => do
  let goal ← getMainTarget
  let ctx ← getLocalHypotheses
  let response ← callLLM (formatPrompt goal ctx)  -- ❶ 调用 LLM
  let candidates ← parseTactics response           -- ❷ 解析候选
  for tac in candidates do                          -- ❸ 逐个尝试
    try
      evalTacticStr tac    -- 在 MetaM 中执行
      return               -- 成功 → 结束
    catch _ => continue
  throwError "all LLM suggestions failed"
```

## 信任模型与防护
%%%
tag := "llm-trust-model"
%%%

LLM 不在 TCB 中——和 SAT 求解器地位相同：提供候选，Lean 内核裁决。

```
LLM 可能生成：             应对：
  正确 tactic             → 内核验证通过 ✓
  错误 tactic             → 内核拒绝 ✓
  包含 sorry 的 tactic     → 框架层面过滤 ⚠️
```

*防护措施*：过滤 `sorry`、每个候选设 heartbeat 上限、执行后检查目标是否全部关闭。

# 22.7 三种模式对比
%%%
tag := "three-modes-comparison"
%%%

| | 证书模式 | Oracle 模式 | LLM 辅助 |
|---|---|---|---|
| *安全性* | 高 | 低 | 高 |
| *TCB* | Lean 内核 | Lean + 外部工具 | Lean 内核 |
| *确定性* | 确定 | 确定 | 不确定 |
| *适用* | SAT/SMT、Gröbner | 开发迭代 | 探索性证明 |
| *Mathlib* | 接受 | 不接受 | 结果可接受 |
| *代表* | `polyrith`、`bv_decide` | `sorry` 工作流 | LeanDojo、ReProver |

# 22.8 实践考量
%%%
tag := "practical-considerations"
%%%

## 可用性与 fallback
%%%
tag := "availability-fallback"
%%%

```
polyrith 需要网络 → 失败时打印系数，用户手动写 linear_combination
SAT tactic 需本地安装 → 提供安装指引或 Docker 镜像
LLM tactic 需 API key → 优雅降级，给出清晰错误
```

## 可复现性
%%%
tag := "reproducibility"
%%%

外部工具引入不确定性。解决方案：

- *缓存证书*：`polyrith` 支持 `--only` 模式使用缓存系数
- *固化 LLM 建议*：成功的 tactic 替换为确定性版本
- *CI 独立*：不依赖外部服务，只用缓存结果

# 22.9 失败模式
%%%
tag := "external-failure-modes"
%%%

## 失败 1：外部工具不可用
%%%
tag := "failure-tool-unavailable"
%%%

```
-- [示意]
-- ✗ 用户没装 z3
-- 错误：z3: command not found
-- ✓ tactic 应捕获 IO 错误并给出安装提示
-- ✓ 提供不依赖外部工具的 fallback
```

## 失败 2：编码不完整
%%%
tag := "failure-incomplete-encoding"
%%%

```
-- [示意]
-- ✗ 目标涉及自定义类型，编码函数不识别 → 求解器返回 unknown
-- ✓ 诊断：打印编码后的 SMT-LIB 查看遗漏
-- ✓ 修复：扩展编码函数，或先 unfold/simp 消除未识别构造
```

## 失败 3：证书验证失败
%%%
tag := "failure-certificate-verification"
%%%

```
-- [示意]
-- ✗ 外部工具 bug 导致错误证书 → Lean 验证失败
-- ✓ 这正是证书模式的价值——错误被捕获，不引入矛盾
-- ✓ 更新工具版本或报告 bug
```

## 失败 4：Oracle 引入矛盾
%%%
tag := "failure-oracle-contradiction"
%%%

```
-- [示意]
-- ✗ 自定义公理 axiom smt_says (p : Prop) : p → 可证明 False
-- ✓ 用 sorry 而非自定义公理——sorry 至少有编译器警告
-- ✓ oracle 公理永远不要进入生产代码
```

## 失败 5：LLM 建议含 `sorry`
%%%
tag := "failure-llm-sorry"
%%%

```
-- [示意]
-- ✗ LLM 返回 "intro h; sorry" → 框架不过滤则证明不完整
-- ✓ 执行前过滤 sorry；执行后检查无剩余目标
```

## 失败 6：证书膨胀导致验证超时
%%%
tag := "failure-certificate-bloat"
%%%

```
-- [示意]
-- ✗ 10 万变量 SAT 问题，resolution proof 100 万步 → heartbeats 爆炸
-- ✓ 用 native_decide 验证证书（而非内核归约）
-- ✓ 使用更紧凑的证书格式
```

# 22.10 设计检查清单
%%%
tag := "external-design-checklist"
%%%

| 检查项 | 问题 |
|--------|------|
| *信任模型* | 证书模式还是 oracle？生产代码必须用证书模式 |
| *编码范围* | 需要编码哪些构造？不识别的如何处理？ |
| *证书格式* | 返回什么格式？如何在 Lean 中验证？ |
| *可用性* | 工具不可用时的 fallback？ |
| *可复现性* | 证书缓存？CI 能否不依赖外部服务？ |
| *性能* | 编码 + 调用 + 验证的总时间可接受？ |
| *错误信息* | 各种失败场景是否有清晰提示？ |

# 22.11 练习
%%%
tag := "external-exercises"
%%%

## 练习 1（设计）：选择集成模式
%%%
tag := "exercise-choose-integration"
%%%

对以下场景，选择证书模式、oracle 模式或 LLM 辅助，说明理由：

```
(a) Mathlib PR 中需要证明一个 200 变量的 SAT 问题。
(b) 个人项目探索阶段，需快速验证一批代数恒等式。
(c) 教学工具：学生输入定理，系统尝试自动找到证明。
```

*提示*：(a) 必须证书模式——Mathlib 不接受 sorry；
(b) oracle（sorry）加速迭代，后续替换；
(c) LLM 辅助——不确定性可接受，内核保证正确性。

## 练习 2（分析）：可信基础对比
%%%
tag := "exercise-tcb-comparison"
%%%

列出以下证明方式的 TCB，从小到大排序：

```
(a) by ring
(b) by native_decide
(c) by polyrith（调用 Sage 后用 ring 验证）
(d) by sorry（信任外部 SMT 的口头声明）
```

*提示*：(a) Lean 内核；(b) 内核 + 编译器；
(c) 和 (a) 相同（Sage 不在 TCB 中——证书由 ring 验证）；
(d) 内核 + 外部 SMT + 人工判断。

## 练习 3（进阶）：设计编码函数签名
%%%
tag := "exercise-encoding-signatures"
%%%

为以下场景设计类型签名（不需实现）：

```
-- (a) 把 Prop 目标编码为 SMT-LIB，需要返回变量映射以便解码
-- def encodeGoalToSMT : ??? := ...

-- (b) 解析 LRAT 证书
-- def parseLRAT : ??? := ...
```

*提示*：
(a) `Expr → MetaM (String × HashMap Expr String)`
(b) `String → MetaM (List LRATStep)`

# 22.12 小结
%%%
tag := "external-summary"
%%%

| 概念 | 关键点 |
|------|--------|
| 外部工具的价值 | 利用专门求解器补充 Lean 内部 tactic |
| 证书模式 | 外部工具给证书，Lean 验证——外部工具不在 TCB 中 |
| Oracle 模式 | 直接信任外部结果——不安全，仅限开发迭代 |
| `native_decide` ≠ oracle | 不引入新公理，只是更快的判定计算 |
| `IO.Process` API | `spawn`（流式）和 `output`（一次性）两种方式 |
| 编码/解码 | 覆盖范围决定工具能力边界（同反射的 quote） |
| LLM 辅助 | LLM 提供候选，Lean 验证——安全但不确定 |
| 可复现性 | 缓存证书，CI 不依赖外部服务 |
| 主要陷阱 | 工具不可用、编码不全、oracle 矛盾、证书膨胀 |

*一句话总结*：对接外部工具的核心原则是*计算外包，验证内留*——
让专门的求解器做它擅长的计算，但证明正确性由 Lean 内核担保。

下一章讨论自动化方法论——如何从手动证明中系统地发现可自动化的模式。
