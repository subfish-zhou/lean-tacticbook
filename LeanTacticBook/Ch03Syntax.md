更新了待办事项列表

我会把三个问题分开核实：它是不是 Lean 的标准机制、它对应哪类通用解析算法、以及“最流行”能否成立。重点会区分 Lean 特有术语 `leading/trailing parser` 与编译原理里的 Pratt、LL、LR 等算法家族。

Ran terminal command:  grep -R -n -m 80 -E 'Pratt|precedence climbing|leading parser|trailing parser|leading_parser|trailing_parser|left recursive' /home/azureuser/.elan/toolchains/leanprover--lean4---v4.32.2/src/lean/Lean /home/azureuser/.elan/toolchains/leanprover--lean4---v4.32.2/doc | head -n 180

Read [](file:///home/azureuser/.elan/toolchains/leanprover--lean4---v4.32.2/src/lean/Lean/Parser/Basic.lean)

Read [](file:///home/azureuser/.elan/toolchains/leanprover--lean4---v4.32.2/src/lean/Lean/Parser/Extension.lean)

源码给出了明确答案：Lean 注释直接称所有内建 parser category 为 Pratt parser。`leading/trailing` 是 Lean 对 Pratt 两类 parselet 的命名，不是编译原理中所有解析器的通用分法；我会据此给出它在整个 parser 谱系中的位置。




已创建 4 个待办事项








我们知道对于假设中的或命题可以使用rcases拆分：

example {p q : Prop} (h : p ∨ q) : False := by
  rcases h with h | h
  . -- h : p
    sorry
  . -- h : q
    sorry
对于多个命题的或依然可以使用rcases ，但是代码会随着命题的个数增长：

example {p q r : Prop} (h : p ∨ q ∨ r) : False := by
  rcases h with h | h | h
  . -- h : p
    sorry
  . -- h : q
    sorry
  . -- h : r
    sorry
搜索Mathlib可用tactic列表发现可以使用casesm实现多个命题的或的拆分，并且代码不会随着命题的个数增长：

example {p q r : Prop} (h : p ∨ q ∨ r) : False := by
  casesm* _ ∨ _
  . -- h : p
    sorry
  . -- h : q
    sorry
  . -- h : r
    sorry

在旧版本上casesm会导致h变成匿名，新版本修复了这个问题。但是使用上述写法依然有以下问题：

上述写法会将上下文中所有的或命题拆开，无法指定拆开哪个假设。
example {p q r s : Prop} (h1 : p ∨ q) (h2 : r ∨ s) : False := by
  casesm* _ ∨ _
  . -- h1 : p
    -- h2 : r
    sorry
  . -- h1 : p
    -- h2 : s
    sorry
  . -- h1 : q
    -- h2 : r
    sorry
  . -- h1 : q
    -- h2 : s
    sorry
为了解决上述问题，考虑使用contrapose!配合split_ands实现多个命题的或的拆分：

example {p q r : Prop} (h : p ∨ q ∨ r) : False := by
  contrapose! h
  split_ands
  all_goals contrapose! h
  . -- h : p
    sorry
  . -- h : q
    sorry
  . -- h : r
    sorry
问题顺利解决。为了方便使用将上述写法打包成一个tactic：

macro "split_ors" h:ident : tactic =>
  `(tactic| (contrapose! $h; split_ands; all_goals contrapose! $h))
最后测试一下，运行良好。

example {p q r : Prop} (h : p ∨ q ∨ r) : False := by
  split_ors h
  . -- h : p
    sorry
  . -- h : q
    sorry
  . -- h : r
    sorry




:::codeBox "可运行"
```
import Lean

syntax:max "twice(" term ")" : term
macro_rules
  | `(twice($t)) => `($t + $t)

example : twice(21) = 42 := rfl
```
:::

也可以把声明和唯一规则合写：

:::codeBox "示意"
```
macro "twice(" t:term ")" : term =>
  `($t + $t)
```
:::



更新了待办事项列表

你说得对，刚才我只完成了代码审校，却漏掉了你明确要求的后续组织计划。下面直接补上，并把它写成可执行的章节路线，而不是泛泛建议。

计划已经补齐，核心调整是把现有 `#inspect_syntax` 从“Lean 解析器”移到新的“操作句法树”，因为它检查的是已经由命令语法解析出的 `Syntax`；随后再讲动态调用解析器，层次会更准确。



是我漏掉了。建议在“实战案例”和“Lean 解析器”之间新增完整一章：

# 操作句法树

## 1. `Syntax` 的数据结构

从真实输出入手，介绍四种构造：

- `Syntax.missing`
- `Syntax.atom`
- `Syntax.ident`
- `Syntax.node`

用 `simp only [↓ ← h]` 展示树形结构，解释：

- 节点种类 `SyntaxNodeKind`
- 子节点数组
- 原子与标识符
- `nullKind`
- 源码位置信息

## 2. `Syntax` 与 `TSyntax`

解释：

- `Syntax`是无类别约束的原始树。
- `TSyntax k`表示已知属于类别`k`的句法。
- `Term`、`Tactic`、`Command`、`Ident`都是常用别名。
- `.raw`用于取出底层`Syntax`。
- 类型只保证句法类别，不保证已经具有语义。

这里正好解释当前命令中的：

```lean
t : Tactic
t.raw : Syntax
```

## 3. 读取句法树

按由浅入深的顺序介绍：

```lean
stx.getKind
stx.isOfKind k
stx.getArgs
stx[i]
stx.getId
stx.isIdent
stx.isAtom
```

同时说明直接使用数字下标非常脆弱，只适合调试或结构固定的底层代码。

## 4. 用句法模式拆解树

回到刚展示过的`rw`宏：

```lean
match s with
| `(rwRuleSeq| [$rs,*]%$rbrak) => ...
```

逐项解释：

- 带类别的句法引用
- 句法模式
- `$x`
- `$xs,*`
- `%$token`
- `$(x)?`
- `$[$x:cat]?`
- 模式不匹配与`Macro.throwUnsupported`

这一节只讲“怎样匹配树”，暂不讲宏展开机制。

## 5. 构造句法树

先讲推荐方式：

```lean
`(term| ...)
`(tactic| ...)
```

再讲反引用如何插入：

- 单节点
- 可选节点
- 重复节点
- 带分隔符的节点

最后简要介绍底层构造器：

```lean
Syntax.node
Syntax.atom
Syntax.ident
mkIdent
```

强调通常应优先使用句法引用，因为手工构造容易破坏节点形状和源码信息。

## 6. 标识符与卫生性

介绍：

- 标识符的源码拼写
- `getId`
- 完整名称
- 宏作用域
- `eraseMacroScopes`
- 预解析名称

这里只建立观察模型；卫生宏的行为留到宏章节深入讲。

## 7. 源码位置与合成节点

介绍：

- `SourceInfo`
- 原始节点与合成节点
- `getPos?`、`getTailPos?`
- `logInfoAt`、`throwErrorAt`
- 为什么宏生成的节点可能没有普通源码范围

这能解释真实 tactic 为什么会把错误准确标在某个 token 上。

## 8. 遍历句法树

把当前`syntaxKinds`发展成树形检查器：

```text
Lean.Parser.Tactic.simp
  Lean.Parser.Tactic.optConfig
  Lean.Parser.Tactic.simpLemma
    Lean.Parser.Tactic.simpPre
```

依次演示：

- 前序遍历
- 收集指定 kind
- 查找标识符
- 跳过`nullKind`
- 保留层级，而不是只输出扁平数组

## 9. 完整调试命令

最终实现：

```lean
#inspect_syntax simp only [↓ ← h]
```

输出：

- 节点层级
- kind
- atom/ident 内容
- 源码范围
- 是否为 synthetic

这会成为后续宏、译补器章节一直复用的工具。

## 与“Lean 解析器”的衔接

当前的`#inspect_syntax`并没有主动调用解析器。命令声明中的`t:tactic`已经让Lean在执行命令译补器之前完成了解析。

因此后面的“Lean解析器”应从这个区别开始：

1. 静态类别参数`t:tactic`如何触发解析。
2. 解析器类别和环境中的解析规则。
3. 何时需要`Parser.runParserCategory`动态解析字符串。
4. 解析成功、宏展开成功和译补成功的区别。
5. token、Pratt解析、优先级和最长匹配的底层模型。

这样叙事顺序就是：

```text
声明句法
→ 阅读真实句法
→ 观察和操作 Syntax
→ 理解 Syntax 如何由解析器产生
→ 使用宏变换 Syntax
→ 将 Syntax 译补为语义
```

这比 metaprogramming-book 把操作 API 集中快速列出更细，也能让每个 API 都由前面的真实源码自然引出。

已创建 1 个待办事项