# Ch08–Ch12 前置知识缺口总账

> 作用：写自动化五章时逐项回查 Ch01–Ch07。只有后章无法就地首次讲清、且前章已经实际使用却未解释的知识，才回补前章；不要把所有新概念倒灌到基础章。

## Ch08 `exact?`

| 检查项 | 前章现状 | 决定 |
|---|---|---|
| `exact?%` 与 `exact?` 的语法类别 | Ch06 已完整区分项译补器 (term elaborator) 与 tactic frontend，并追踪成功、partial、synthetic sorry | 不回补；Ch08 从后端接续 |
| `MVarId.apply`、参数洞和活动目标队列 | Ch05、Ch07 已讲 | 不回补 |
| Meta/Tactic saved state 与失败回滚 | Ch05、Ch07 已分别讲 Meta 与 Tactic 回滚 | Ch08 直接复用并比较候选级 snapshot |
| `headBeta` 与 `intros` | Ch06 已在 `exact?%` 主线出现 | Ch08 简短回指，不倒灌新小节 |
| `EnvExtension`、lazy discrimination tree | 前章未讲，也未依赖 | 属 Ch08 新内容，在本章首次完整讲 |
| TryThis、source replacement、建议重放 | Ch07 只提到 InfoTree/TacticInfo，没有解释代码建议 | 属 Ch08 的输出端，不回补 Ch07 |
| `LibrarySuggestions` selector | 前章未使用 | Ch08 只说明与 `exact?` 候选树不同；Ch11 `+suggestions` 再引用 |

## Ch09 `ring`

| 检查项 | 前章现状 | 决定 |
|---|---|---|
| 重化与专用 AST | Ch03 讲 Syntax/macro，但没有把 Expr 重化为代数 AST | 属 Ch09 新机制，在本章从 Expr→ExSum 首次讲 |
| Qq typed quotation | 前章只有 Syntax quotation | Ch09 在源码使用前设置独立插页，不回补 Ch03 |
| 定义等价与 transparency | Ch05 已完整讲 `isDefEq` 和状态边界 | 直接回指 |
| `#print axioms` | Ch04 已讲并有可运行命令 | 直接复用 |
| proof-carrying computation | 前章没有成熟实例 | 属 Ch09 主题，不倒灌 |


## Ch10 `linarith`

| 检查项 | 前章现状 | 决定 |
|---|---|---|
| `ring1` 的 proof-producing 归零 | Ch09 已讲 | 直接作为 verifier discharger 引用 |
| `linear_combination` | 前章未使用 | Ch10 用一个等式例子对照“用户写系数”与“oracle 搜系数”，不回补 |
| 不等式、Nat/Int casts | 属读者已有基本数学 Lean 经验 | 本章只补 tactic 特有 preprocessors |
| oracle/certificate 区分 | 前章未讲 | Ch10 首次建立，并供 Ch12 复用 |
| `linarith` frontend 的 goal negation | Ch07 已讲 goal assignment，但未讲比较式前端 | 本章就地讲，不回补 |


## Ch11 `grind`

| 检查项 | 前章现状 | 决定 |
|---|---|---|
| 候选索引与回滚 | Ch08 已讲 | 只做逐候选搜索与饱和的对照 |
| E-graph / congruence closure | 前章未使用 | Ch11 新内容 |
| CPS 与 branch-local state | Ch07 已讲 saved state、`first`、`<;>`，未讲 CPS | Ch11 从分支需求首次讲；无需提前塞入 Ch07 |
| theory solver proof 回写 | Ch09/10 已给两个 concrete solver | Ch11 建立共同接口，避免 API 罗列 |
| InfoTree / suggestions | Ch08 已讲 TryThis | `grind?` 只讲差异 |


## Ch12 `bv_decide`

| 检查项 | 前章现状 | 决定 |
|---|---|---|
| `#print axioms` 与公理锥 | Ch04、Ch09–Ch11 已反复使用 | 直接用于 normalization/full-SAT 对照 |
| reflection 与 proof-producing computation | Ch09 已建立 | Ch12 扩展到 Bool checker 与外部 certificate |
| oracle/certificate/verifier | Ch10 已建立 | 复用后提升到 CaDiCaL/LRAT |
| Bool/CNF/AIG/LRAT | 前章未使用 | Ch12 先交代 `BitVec w` 的固定宽度与模 `2^w` 语义，再自包含讲 Boolean pipeline，不回补 |
| native compilation / generated axiom | 前章未使用 | Ch12 中心新边界；不得埋入 CoreM 概览 |
| 外部进程与文件 | 前章只讲一般 IO | Ch12 结合 solver/certificate 首次讲 |

## 写作触发的前章纠错

| 位置 | 发现 | 修订 |
|---|---|---|
| Ch01 编译流程 | 旧文把 Expr 一概写成“最后执行”，并把译补简化成按 name 找唯一 elaborator | 改成 parser、macro、分派式 elaboration、kernel checking、按需 code generation 五层；明确定理证明通常只检查不执行 |
| Ch01 全书结构 | 旧路线仍列出尚不存在的 Ch13–Ch25 | 改成当前实际 Ch01–Ch12 结构 |
| Ch02 章内链接 | 两处把 Markdown 目标误写成 `## 标题`，生成了不存在的 URL | 改为对应显式 Verso tag 的 fragment 链接 |
| Ch03 `ring` / `linarith!` | 把 `ring1` 叫“快速路径”，没有连接新章 | 改成真实等式关闭器与 `ring_nf` residual 路线，并前向连接 Ch09、Ch10 |
| Ch04 公理锥 | 容易被读成 tactic 搜索可信性的完整审计 | 补明公理锥只审计最终声明，还须检查是否重建普通 proof Expr 或经 axiom bridge 接入计算 |

## 当前回补结论

两轮写作与独立审读没有发现“前章已经承重使用、却完全未解释”的缺口。Qq、EnvExtension、E-graph、CNF、native bridge 都是后章首次真正需要的新概念，已在使用前就地引入。独立审读曾指出 Ch12 首稿没有兑现“自包含”：随后已补入 `BitVec w` 的模 `2^w` 语义、SAT 最小词汇表、具体 RUP 手算、合法/损坏 LRAT fixtures 与离线 `bv_check` 重放。因而不需要把这些概念倒灌进 Ch01–Ch07。

