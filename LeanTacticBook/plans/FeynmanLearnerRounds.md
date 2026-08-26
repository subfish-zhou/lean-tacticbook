# 费曼学习者复述轮次

## 角色约束

学习者只读每轮冻结的 `snapshot.md`，不得联网、查源码、批评讲义或提出改稿建议。它只能按首次阅读顺序复述自己学到的因果链、例子、术语、失败边界和信任边界。主会话不接受“我学会了”的自评，而是逐句判卷。

## Gemini 3.7 Flash

模型已通过 Copilot CLI 的 JSON 事件确认：`model.call_start.model = gemini-3.7-flash`。

### R1

产物：

- `/home/azureuser/.hermes/workspace/_tasks/feynman-readers/r1/snapshot.md`
- `/home/azureuser/.hermes/workspace/_tasks/feynman-readers/r1/PROMPT.md`
- `/home/azureuser/.hermes/workspace/_tasks/feynman-readers/r1/gemini-r1.md`

判卷发现：

1. 把 `realizeGlobalConstWithInfos` 的 `List Name` 复述成唯一名称；
2. 把 expected type 混入 `Term.Context`；
3. 把 Ch10 oracle 误当外部进程；
4. 把部分搜索失败说成证书不存在；
5. 没有稳定区分 `apply?` 完整成功与 partial/admit 分支；
6. 对 Ch12 SAT assignment 的诊断地位表述过强。

据此定点补写 Ch04、Ch06、Ch08、Ch10、Ch12；没有在 learner prompt 中直接教授纠正答案。

### R2

产物：

- `/home/azureuser/.hermes/workspace/_tasks/feynman-readers/r2/snapshot.md`
- `/home/azureuser/.hermes/workspace/_tasks/feynman-readers/r2/gemini-r2.md`

前述大部分误解已消失；仍发现：

1. 将 `pendingMVars` 概括成保存完整延期任务的表；
2. `apply?` 的完整成功/partial 分支在闭卷摘要中仍被压缩；
3. 若干实现名第一次出现仍早于概念定义。

据此加入 `syntheticMVars`、`pendingMVars` 与 placeholder declaration 三者对照，并把 Ch08 前端控制流改成显式判定树；同时机械审计各章首次术语位置。

### R3

产物：

- `/home/azureuser/.hermes/workspace/_tasks/feynman-readers/r3/snapshot.md`
- `/home/azureuser/.hermes/workspace/_tasks/feynman-readers/r3/gemini-r3.md`

Ch04–Ch08 主链已能正确重建；仍发现学习者用既有模型知识覆盖锁定实现：

1. Ch09 擅自换成 Horner 规范形；
2. Ch10 再次把进程内 oracle 说成外部 LP 求解器；
3. Ch12 把 SAT assignment 说成 Lean 中确凿反证；
4. Ch12 发明完整 SAT 路线的 `rfl`/formal 零公理替代模式。

据此在 Ch09 明确锁定实现为 `ExBase / ExProd / ExSum`，在 Ch10 加入“运行位置 / TCB / 失败含义”三问表，在 Ch12 加入三条禁止误述及逐条反驳。

### R4

范围缩至仍有误解的 Ch09–Ch12，使用新快照与新 Copilot 会话。产物：

- `/home/azureuser/.hermes/workspace/_tasks/feynman-readers/r4/snapshot.md`
- `/home/azureuser/.hermes/workspace/_tasks/feynman-readers/r4/gemini-r4.md`

判卷通过：学习者明确复述了锁定 `ring` 使用 `ExBase / ExProd / ExSum` 而非 Horner；Ch10 oracle 在 Lean 进程内但不属于 TCB，失败不证明证书不存在；Ch12 SAT assignment 只是诊断、`bv_check` 仍含 `nativeEqTrue`、完整 SAT 路线不存在 `rfl`/formal 零公理替代模式。其闭卷数据流与失败边界也一致。Gemini lane 收敛。

## 补充三路学习者复述

`deleg_5ab69d23` 的三名只读学习者分别复述 Ch04–Ch06、Ch07–Ch09、Ch10–Ch12。该批次读取的是费曼循环中途快照，因此不替代最终 Gemini R4，但可作独立交叉检查：

- Ch07–Ch09 学习者正确区分 mctx/goal queue、`apply?` 完整成功与 partial/admit，并把 `ring` 复述为带证明的规范化；
- Ch10–Ch12 学习者正确复述 oracle 失败不证明证书不存在、SAT assignment 只是诊断、`bv_check` 仍保留 `nativeEqTrue`；
- Ch04–Ch06 学习者在中途稿上仍说自己没有学会 postponed payload、`pendingMVars` 与 placeholder 的存储分工。该缺口随后已在正文中拆成三项，并由更新后 Gemini R3 正确复述为 payload 位于 `syntheticMVars` 的 `postponed savedContext`，`pendingMVars` 只保存待重访编号。

完整结果位于 `/home/azureuser/.hermes/cache/delegation/subagent-summary-{0,1,2}-20260824_102325_*.txt`。

## Grok 4.6 学习者复述

最初只猜测 `grok-code-fast-1` 与 `grok` 两个标识并据失败结果误报阻塞，这是调度错误。随后通过当前账号的 live model list 得到可用 Grok：

- `grok-4.5`
- `grok-4.6`

本轮选用较新的 `grok-4.6`。JSON 事件 `session.tools_updated.data.model` 与 `model.call_start.data.model` 均确认实际模型为 `grok-4.6`。

只读学习者产物：

- `/home/azureuser/.hermes/workspace/_tasks/feynman-readers/grok-r1/snapshot.md`
- `/home/azureuser/.hermes/workspace/_tasks/feynman-readers/grok-r1/PROMPT.md`
- `/home/azureuser/.hermes/workspace/_tasks/feynman-readers/grok-r1/grok-r1.md`

主会话逐章判卷结果：Ch04–Ch12 的概念动机、最小例子、状态分层、失败含义、证明重建和信任边界均正确。特别是它正确区分 action/普通值、mctx/goal queue、完整/partial 搜索、带证明规范化、进程内 oracle、SAT assignment 诊断以及 `bv_check`/`nativeEqTrue`。它列为“没有学会”的均是讲义明确后置的源码字段或算法细节，没有承重概念缺失。因此 Grok lane 第一轮即满足收敛条件，无需为凑轮数机械续跑。

## 较弱模型的预训练知识污染检查

用户进一步指定 `gpt-5-mini` 与 `mai-code-1.1-flash`。两者的 JSON 事件 `session.tools_updated`、`model.call_start` 和 `assistant.message` 均确认实际模型未被替换。

### GPT-5 Mini R1

产物：

- `/home/azureuser/.hermes/workspace/_tasks/feynman-readers/gpt5mini-r1/snapshot.md`
- `/home/azureuser/.hermes/workspace/_tasks/feynman-readers/gpt5mini-r1/gpt5mini-r1.md`

prompt 要求模型假装没有预训练知识，讲义未推出的内容必须写“我没有从讲义学会”。它正确复述了九章的因果链、最小例子、失败边界与信任边界；未把 `pendingMVars` 当 payload 存储，未把 oracle 当外部进程，也未把 SAT assignment 当 proof object。其额外技术名词均可在快照中定位，没有发现靠外援补出的承重结论。

### MAI Code 1.1 Flash R1/R2

R1 把九章合并为一个 132853 字符快照。模型只读到 Ch04，随后错误声称后续章节没有正文。这是长文件读取协议失败，不能拿来判定教材缺章或理解失败。

R2 将输入拆成九个逐章文件，并在 prompt 中逐一列名、要求交卷前回报已读清单：

- `/home/azureuser/.hermes/workspace/_tasks/feynman-readers/mai11-r2/`

模型随后确实列出并复述 Ch04–Ch12。它正确区分 action/普通值、Meta 状态/目标队列、完整/partial 搜索、oracle/验证器、SAT assignment/LRAT proof path 和 `bv_check`/native bridge；“没有学会”的内容只剩生产字段与算法细部。因此 R2 判卷通过。这个实验同时说明弱模型可减少“凭背景补课”的风险，但必须用逐章快照防止上下文读取假完成。

本轮未暴露新的正文教学缺口，因此没有为了制造改动而重写正文；只把“弱模型先验控制 + 长快照逐章读取门”补进技术写作 skill。

## 保护区

本轮未修改 Ch02/Ch03。终验记录：

- `Ch02Syntax.lean` mtime `2026-08-24 09:23:40 +0000`，SHA-256 `1475ed96ead5edbcb6a386bc4f6678e6c17f63ea7867a1e6f25bc636d07aa85d`；
- `Ch03Macros.lean` mtime `2026-08-24 09:18:29 +0000`，SHA-256 `47d0f72e212dfa9e5eab0e693b1cdfaf580d06d66dd81ba284decb817ffbd2e8`。
