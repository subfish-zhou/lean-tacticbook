# Ch04–Ch12 费曼式重写总账

## 冻结边界

本轮只允许修改：

- `LeanTacticBook/Ch04CoreM.lean`
- `LeanTacticBook/Ch05MetaM.lean`
- `LeanTacticBook/Ch06TermElabM.lean`
- `LeanTacticBook/Ch07TacticM.lean`
- `LeanTacticBook/Ch08Exact.lean`
- `LeanTacticBook/Ch09Ring.lean`
- `LeanTacticBook/Ch10Linarith.lean`
- `LeanTacticBook/Ch11Grind.lean`
- `LeanTacticBook/Ch12BVDecide.lean`
- 上述章节直接使用的 examples、计划账本与整书入口。

本轮不得修改：

- `LeanTacticBook/Ch02Syntax.lean`，冻结 SHA-256：`1475ed96ead5edbcb6a386bc4f6678e6c17f63ea7867a1e6f25bc636d07aa85d`
- `LeanTacticBook/Ch03Macros.lean`，冻结 SHA-256：`47d0f72e212dfa9e5eab0e693b1cdfaf580d06d66dd81ba284decb817ffbd2e8`
- `examples/Examples/Ch03Macros.lean`

## 读者起点

进入 Ch04 时，只假定读者会：

1. 阅读普通 Lean 声明、`example`、`theorem` 和 `by` 证明；
2. 区分源代码文本与 parser 产生的 `Syntax`；
3. 知道 macro 把一种 `Syntax` 改写成另一种 `Syntax`；
4. 阅读最基本的函数类型、结构体字段、`do` 与 `←`，但不假定读者已经理解 monad transformer、Reader、State、metavariable、双向译补、饱和、SAT 或证书。

若后章需要更多知识，必须在首次消费处自行搭桥，不得把未解释术语倒推成“前章应该已经知道”。

## 每个概念的固定出场顺序

1. 先给一个读者看得见的问题或运行现象。
2. 尝试只用此前知识解决。
3. 明确指出朴素办法缺少哪一项信息或能力。
4. 此时才给新概念命名，并在第一次出现时给中文定义；英文名只作检索线索。
5. 用一个最小例子让读者亲眼看见该概念解决问题。
6. 再写正式接口、数据结构和源码路径。
7. 给失败例，说明它不能解决什么。
8. 明说“此刻不需要知道”的内部细节。

源码地图、API 表和术语清单不得出现在读者第一次看见现象之前。

## 章节依赖树

### Ch04 CoreM

可见问题：一条命令怎样知道当前文件里已经有哪些声明，并把结果写到消息窗口？

递进路径：

```text
普通纯函数
→ 发现每层都要手传环境、选项、位置和消息
→ “一段要在现场中运行的计算”
→ action 与返回值的区别
→ CoreM
→ 只读现场 Context
→ 会变化的现场 State
→ 失败通道与显式恢复
→ CommandElabM 怎样把命令接到 CoreM
→ 用这些能力实现最小公理依赖命令
→ 最后才读 collectAxioms 的缓存和模块扩展
```

首次术语最小桥：

| 术语 | 首次出现前的现象 | 最小解释/例子 | 此刻不需要知道 |
|---|---|---|---|
| action / monadic computation | `realize...` 不能直接当 `List Name` | `let x := action` 与 `let x ← action` | transformer 的通用理论 |
| Context | 子调用要读 namespace，退出后不改变外层 | `withRef` 的局部替换 | 全字段列表 |
| State | 连续两次操作共享消息与环境更新 | 同一 `liftCoreM do` 中 warning 去重 | cache、snapshot 全部细节 |
| exception | 后续语句不再运行，但先前状态可能保留 | 先生成 fresh name 再抛错 | EIO 的实现 |
| saved state | 搜索分支失败后需要选择性恢复 | 保存、修改、恢复、逐字段比较 | 增量编译协议 |
| Environment | 查询当前已经注册的声明 | `find?` 一个名字 | 环境扩展序列化 |
| 传递闭包 | A 只引用 B，B 引用公理 C | 三节点图 | 图算法优化 |

### Ch05 MetaM

可见问题：`rw [h]` 为什么既能把目标文字换掉，又仍然交出可由内核检查的证明？

递进路径：

```text
目标是一个待填的证明洞
→ 目标和局部假设已经是 Expr
→ 局部变量必须凭内部身份查类型
→ 创建一个最小 metavariable 并观察赋值
→ 定义等价可能在比较时产生赋值
→ 改写不能只替换文字，必须构造运输证明
→ rewrite 先返回结果
→ replaceTargetEq 才提交旧目标
→ side goal 从哪里来
→ 最后才展开 spine、binder、kabstract 与 motive
```

关键限制：`Expr.fvar`、`Expr.bvar`、de Bruijn index、spine、motive 不得在读者还不知道“为什么字符串替换不够”时连续出现。

### Ch06 TermElabM

可见问题：同一个 `0` 为什么在 `Nat`、`Int` 等位置会变成不同的 Expr？

递进路径：

```text
Syntax 本身没有唯一类型
→ 外层位置给出“期望得到的类型”
→ 预期类型帮助译补内层
→ 内层结果也能反过来约束外层未知类型
→ 信息不足时不能猜，先延期
→ 有些洞不是用户证明目标，而是待完成任务
→ 多个 elaborator 可竞争同一种 Syntax
→ unsupported、用户错误、延期三路必须分开
→ 最后用 exact?% 连接 Library Search
```

`exact?%` 不再作为章首第一个概念；先建立预期类型和延期的必要性，再把它作为综合案例。

### Ch07 TacticM

可见问题：`constructor` 把一个目标变成两个后，Lean 怎么决定下一条 tactic 处理哪一个？

递进路径：

```text
屏幕上一个目标
→ constructor 后两个目标
→ 每个目标本质上是一个 MVarId
→ mctx 记录洞是否赋值
→ goals 列表记录用户接下来处理的顺序
→ apply 同时改 mctx 和目标队列
→ replaceMainGoal 的队列政策
→ focus / all_goals / <;>
→ 候选失败时两层状态必须一起恢复
→ dispatcher 和 recovery policy
```

### Ch08 exact? / Library Search

可见问题：目标明明已有现成定理，为什么还要人工记住定理名？

递进路径：

```text
手写 exact theorem
→ 不知道名字时需要候选搜索
→ 先用最小局部候选观察成功与失败
→ “找到候选”“给目标赋值”“显示建议”“命令成功”是四件事
→ exact? 与 apply? 的 complete/partial 区别
→ 只有候选太多时才引入按结论形状预筛
→ 再命名判别树、惰性索引、discharger
→ 最后讲 TryThis 重放和公理边界
```

### Ch09 ring

可见问题：`(x + y)^2` 与展开式长得不同，为什么 `rfl` 不成立而 `ring` 成立？

递进路径：

```text
rfl 失败
→ 展开和交换结合能手证，但步骤迅速膨胀
→ 把相同多项式变成同一种规范形
→ 规范形相同还不够，Lean 需要等式证明
→ 反射：在 Lean 内表示、计算并重建证明
→ 最小 ToyExpr
→ 再对照生产 ExBase/ExProd/ExSum 与 Qq
→ ring / ring1 / ring_nf
→ 未知原子、除法与 field_simp 边界
```

### Ch10 linarith

可见问题：两条不等式怎样相加得到矛盾？

递进路径：

```text
人工把前提乘系数再相加
→ 系数选对后，剩下只是 ring 规范化
→ 自动化真正搜索的是这些系数
→ 这组系数叫线性证书
→ Lean 重新检查证书
→ 严格不等式与等式怎样编码
→ 多项式先规范化成“原子”的线性组合
→ monomial 可整体当原子，但 linarith 不懂乘法关系
→ 预处理、分支、nlinarith 扩展
→ 最后才比较 simplex / Fourier–Motzkin
```

### Ch11 grind

可见问题：一个证明需要反复做“拆假设、代换相等项、调用局部规则”，为什么单个 tactic 各做一步仍很累？

递进路径：

```text
手工完成一个四五步小证明
→ 把当前已知事实写成一张不断扩充的工作板
→ 新事实触发规则，直到不再产生新事实
→ 这叫饱和
→ 相等项合并成等价类
→ 函数应用必须尊重相等，得到同余闭包
→ 规则左端寻找已知实例，得到匹配
→ 有选择时才引入 split / backtracking
→ 最后才讲 E-graph、E-matching、origin/proof data 和资源上限
```

### Ch12 bv_decide

可见问题：固定宽度位向量的恒等式状态有限，能否把所有输入逐一检查？

递进路径：

```text
2 位/3 位手工真值表
→ 宽度增加后逐值枚举爆炸
→ 把运算拆成布尔门
→ 把“是否存在反例”写成布尔约束
→ SAT 只回答是否存在满足赋值
→ 外部求解器不在 Lean 内核中，不能只信答案
→ 求解器附带可重放证书
→ CNF、Tseitin、RUP、RAT、LRAT 逐个由同一个小例子逼出
→ Lean 内部 checker 重放
→ 最后审计 native bridge 与公理锥
```

## 学习者复述验收协议

每轮把当前章节交给两个彼此独立的 Copilot 模型。提示中禁止它们批评、润色或列问题，只允许按阅读顺序复述：

1. 章首问题是什么；
2. 每个新概念为何必须出现；
3. 用自己的话解释最小例子；
4. 说出概念不能做什么；
5. 不看原文重建章节主数据流；
6. 标出自己只能背诵、无法解释因果的地方。

主会话不把“语言流畅”当作学会。逐项判卷：

- 若学习者使用了讲义没有先定义的词，追查该词是否只是照抄；
- 若学习者混淆对象层级，说明讲义桥梁失败；
- 若两位学习者在同处产生不同误解，重写该处而非追加术语注释；
- 修改后必须让同一模型重新从头复述，不把上一轮纠正直接告诉它；
- 两位学习者都能独立重建主线、最小例子和失败边界，才算该章收敛。

## 构建不是教学验收

每轮仍需构建，但绿色构建只证明代码和文档结构成立。最终验收同时要求：

1. examples 与正文 anchors 一致；
2. 章节、整书、HTML 构建成功；
3. 公理锥与信任边界符合正文；
4. 两位零基础学习者能正确复述；
5. Ch02、Ch03 冻结文件哈希不变。
