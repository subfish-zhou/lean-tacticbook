import VersoManual
import LeanTacticBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "examples"
set_option verso.exampleModule "Examples.Ch03Macros"

#doc (Manual) "宏" =>
%%%
file := "Ch03Macros"
tag := "ch03-macros"
%%%

> *本章目标*：用 `macro` 和 `macro_rules` 定义 term、tactic 与 command 宏，可选项和重复项，展开顺序与卫生性，区分宏包装、tactic elaborator 与 builtin tactic。

# 何为宏
%%%
tag := "what-is-macro"
%%%

宏是批处理。具体来说，宏就是给一些项或证明步骤打了个包并起了个名字。

> _The finding that math is about compression is not new ... word length measures size, and naming a substring for reuse—a macro—compresses it. —— Compression is all you need: Modeling Mathematics_
> _数学的本质在于压缩，这不新鲜……以词长衡量大小，为重用而命名子串——宏——就实现了压缩。——《压缩即是一切》_

如果再套用“压缩即智能”的观点，宏就是智能！

# 第一个宏
%%%
tag := "first-macro"
%%%

上一章我们用{kw}`notation`定义过异或运算符。实际上，我们也可以用宏来定义它：

```anchor macro_XOR
macro:10 l:term:10 " XOR " r:term:11 : term => `((!$l && $r) || ($l && !$r))

#eval true XOR true -- false
#eval true XOR false -- true
#eval false XOR true -- true
#eval false XOR false -- false
```

下面逐词解释。
* {kw}`macro`就是声明这个宏的关键字。
* {anchorTerm macro_XOR}`l` 和 {anchorTerm macro_XOR}`r` 是宏的两个参数，它们属于 {anchorTerm macro_XOR}`term` 类型。{anchorTerm macro_XOR}`" XOR "`是这个宏的记号。此处我们定义的是中缀运算符，所以参数写在记号的两边。
* {anchorTerm macro_XOR}`" XOR "`两边的空格是为了将来这个运算符出现在Lean Infoview里的时候也能保留空格。
* Lean 中万事万物都有类型。必须要声明 {anchorTerm macro_XOR}`l:term:10 " XOR " r:term:11`这一整块是{anchorTerm macro_XOR}`term` 类型的。
* {anchorTerm macro_XOR}`=>`后面是宏的具体语义，也就是说它压缩的内容。`` `() ``是句法引号（syntax quotation），类型是 ``MacroM (TSyntax `term)``，这意味着 Lean 要将括号内的项解析成一棵 `term` 类别的 `Syntax` 句法树。{anchorTerm macro_XOR}`$l` 和 {anchorTerm macro_XOR}`$r` 称为反引（antiquotation），Lean 把它们解析成代表两个参数的句法树节点。

其实这个最简单的宏是以下这段代码的语法糖：

```anchor macro_desugering1
syntax:10 term:10 " XOR₁ " term:11 : term

macro_rules
  | `($l:term XOR₁ $r:term) => `((!$l && $r) || ($l && !$r))
```

此处你可以看到，句法和宏规则其实是分开的两种功能，句法层定义这个宏要如何被调用，而宏规则声明这个宏实际上做了什么。而宏规则又被 {kw}`=>` 分成两部分，分别对应着两棵句法树，其中左边是*匹配模式*，右边是*展开式*。当解析器遇到形如匹配模式的句法时，就会把它替换成展开式。

实际上{kw}`macro_rules`又是下面这段的语法糖：

```anchor macro_desugering2
syntax:10 (name := xor2) term:10 " XOR₂ " term:11 : term

@[macro xor2] def xor₂ : Macro
  | `($l:term XOR₂ $r:term) => `((!$l && $r) || ($l && !$r))
  | _ => Macro.throwUnsupported
```

这个最不甜的版本好像有点看不懂了，让我来详细解释。
* {anchorTerm macro_desugering2}`@[macro xor2]`是一个属性标记，告诉 Lean 这个对象是一个宏展开器，并且对应到{anchorTerm macro_desugering2}`name := xor2`的句法。
* {anchorTerm macro_desugering2}`def xor₂ : Macro`声明了一个名为 `xor₂` 的宏展开器，它的类型是 {anchorTerm macro_desugering2}`Macro`。
* 这个宏有两个分支：第一个分支匹配形如 `$l XOR₂ $r` 的语法，并返回展开后的语法；如果匹配不到第一个分支，由第二个分支抛出 {anchorTerm macro_desugering2}`Macro.throwUnsupported` 异常，表示这个宏不支持该输入。注意你必须在文件头`import Lean`和`open Lean`之后才能使用 {anchorTerm macro_desugering2}`Macro.throwUnsupported`，因为它在 `Lean` 模块中定义。

这三种版本在功能上几乎没有区别，但单独声明{kw}`syntax`有些重要的工程优势。其一，我们实际上可以为单个句法定义多个宏规则，让我们可以根据不断扩展的需求来扩展宏的语义。第二，有了独立声明的语法之后宏就可以被递归调用。这些让{kw}`macro_rules`成为最常用的宏定义方式。下一节会马上看到一个例子。

# 证明术宏
%%%
tag := "tactic-macro"
%%%

宏最重要的功能是打包一些证明步骤。比如，`Init/Tactics` 里有一个证明术叫 {kw}`trivial`，它会尝试若干个证明方案，直到找到一个能关闭当前目标的方案为止。它是这样实现的：

```anchor macro_rules_trivial
syntax "mytrivial" : tactic -- 避免与`trivial`冲突，用一个新名字

macro_rules | `(tactic| mytrivial) => `(tactic| assumption)
macro_rules | `(tactic| mytrivial) => `(tactic| rfl)
macro_rules | `(tactic| mytrivial) => `(tactic| contradiction)
macro_rules | `(tactic| mytrivial) => `(tactic| decide)
macro_rules | `(tactic| mytrivial) => `(tactic| apply True.intro)
macro_rules | `(tactic| mytrivial) => `(tactic| apply And.intro <;> mytrivial)
```

第一行先把 {anchorTerm macro_rules_trivial}`mytrivial` 声明成一种不带参数的 {anchorTerm macro_rules_trivial}`tactic` 句法类型。每条 {kw}`macro_rules` 左边的 {anchorTerm macro_rules_trivial}`` `(tactic| mytrivial) `` 都是在匹配{anchorTerm macro_rules_trivial}`mytrivial`这棵证明术句法树，右边的 `` `(tactic| ...) `` 则构造一棵新的证明术句法树。这里的 `tactic|` 是句法引号关键字的一部分，它明确指明解析器应当把引号里的内容按证明术来解析。在上一节里我们省略句法引号类别时它默认为项类别，也就是类似于 `` `(term| x + 1) `` 。此外还有命令类型 `` `(command| def x := 1) ``。

六条规则给同一种句法注册了六个候选展开。越晚定义的宏会被越先尝试。如果这些证明术都没生效，那只能抛出 {anchorTerm macro_desugering2}`Macro.throwUnsupported` 异常了，也就是说这个证明术宏无法推进当前的证明。

最后一条负责合取：`apply And.intro` 把目标 `P ∧ Q` 拆成 `P` 与 `Q` 两个目标，`<;>` 再把 `mytrivial` 应用于产生的每个目标。由于 `mytrivial` 的句法已经由前面的 {kw}`syntax` 独立声明，展开结果可以再次引用它，于是嵌套的合取也能被逐层拆开。

如果不考虑那个递归调用，它其实跟下面这种写法是等价的，只不过你想扩展它的时候就得从代码堆翻出来改：

```anchor macro_trivial
macro "mytrivial₁" : tactic =>
  `(tactic| first  -- 也可以不换行
    | apply True.intro
    | decide
    | contradiction
    | rfl
    | assumption)
```

但是如果你想递归调用就会报错，因为解析器暂时还找不到`mytrivial_error`的定义。

:::codeBox "error code"
```
macro "mytrivial_error" : tactic =>
  `(tactic| first
    | ...
    | apply And.intro <;> mytrivial_error) -- 报错：unknown macro `mytrivial_error`
```
:::

在{anchorTerm macro_trivial}`"mytrivial₁"`里你可能会注意到两点。第一是有一个{kw}`first`控制器，它会从第一个开始依次尝试每个分支，直到其中一个成功，否则失败。这也导致第二点是，各证明术与{kw}`macro_rules`的版本是倒序的。

{kw}`first`实际上也是一个证明术。它会成为将来TacticM一章的例子。常用控制器还有：

```table
| 写法 | 详细说明 | 典型片段 |
|------|----------|----------|
| `first` | 按书写顺序尝试各分支，选择第一个不失败的分支。分支只要执行成功即可，不要求关闭目标。 | `first \| rfl \| assumption` |
| `solve` | 按书写顺序尝试各分支，但只接受能够关闭当前全部目标的分支。适合在若干完整证明方案之间选择。 | `solve \| aesop \| omega` |
| `skip` | 什么也不做并立即成功，证明状态保持不变。常用作 first 的兜底分支或暂时的空操作。 | `first \| simp \| skip` |
| `try` | 尝试执行一次证明术；若失败则回滚状态并仍然成功，若成功则保留结果。它等价于以 skip 兜底的 first。 | `try simp [h]` |
| `repeat` | 在当前主目标上反复执行证明术，直到下一次执行失败；最后整体成功。若证明术成功却不推进状态，可能不会终止。 | `repeat intro` |
| `repeat'` | 递归地对证明术产生的所有子目标重复执行，适合遍历树状展开出的目标，而不只是沿主目标继续。 | `repeat' constructor` |
| `all_goals` | 对当前所有目标分别运行同一个证明术；任一目标上的执行失败都会使整个控制器失败。 | `all_goals simp [h]` |
| `any_goals` | 在所有当前目标上尝试证明术，保留成功目标上的结果并跳过失败者；只有在全部目标上都失败时才失败。 | `any_goals assumption` |
| `focus` | 暂时只把主目标交给内部证明术，其他目标不参与这次执行；内部证明术成功即可，不要求关闭主目标。 | `focus rw [h]` |
| `·` | tactic 序列中的项目符号：聚焦下一个目标，并要求这个项目符号下的证明块关闭它产生的全部目标。常用于逐个处理分支。 | `· exact hp` |
| `<;>` | 先执行左侧证明术，再把右侧证明术应用于左侧产生的每一个目标。右侧在任一目标失败，整个组合就失败。 | `constructor <;> assumption` |
| `done` | 不改变证明状态，只检查当前是否已经没有目标；仍有任何目标时立即失败。常放在脚本末尾作完整性断言。 | `all_goals assumption; done` |
```

# 示例：多项式方程求解宏
%%%
tag := "macro-poly-roots"
%%%

本节用多项式方程求解来演示一个“从普遍模式抽提出宏”的过程。先从二次方程开始。数学上先做因式分解，再用零乘积性质读出根；Lean 证明也可以逐字照做：

```anchor macro_poly_roots_direct_quadratic
example (x : ℚ) : x^2 - 5*x + 6 = 0 ↔ x = 2 ∨ x = 3 := by
  rw [show x^2 - 5*x + 6 = (x - 2) * (x - 3) by ring]
  simp only [mul_eq_zero, sub_eq_zero]
```

`show ... by ring` 负责验证因式分解，`rw` 用乘积替换原多项式，最后两条引理依次把“乘积为零”变成析取、把“差为零”变成等式。

三次方程仍旧：

```anchor macro_poly_roots_direct_cubic
example (x : ℚ) :
    x^3 - 6*x^2 + 11*x - 6 = 0 ↔ x = 1 ∨ x = 2 ∨ x = 3 := by
  rw [show x^3 - 6*x^2 + 11*x - 6 = (x - 1) * ((x - 2) * (x - 3)) by ring]
  simp only [mul_eq_zero, sub_eq_zero]
```

这里特意把乘积写成右结合。若写成通常的 `(x - 1) * (x - 2) * (x - 3)`，Lean 按左结合解析它，`mul_eq_zero` 会产生 `(x = 1 ∨ x = 2) ∨ x = 3`；而目标 `x = 1 ∨ x = 2 ∨ x = 3` 是右结合的。数学上两者等价，句法树却不相同，还要额外处理结合律。

现在重复模式已经出现了，但二次和三次证明中的因式个数不同，还不能直接抽成一个固定模板。我们能立即想到的一个简单方案是让调用者提供根列表，再统一构造

\[
\prod_i(x-r_i).
\]

也就是说，我们可以期待一个这样的宏：

:::codeBox "code"
```
poly_roots 多项式 with [根₁,根₂,...] in 变量
```
:::

三次方程证明改写成列表乘积后是：

```anchor macro_poly_roots_list_cubic
example (x : ℚ) :
    x^3 - 6*x^2 + 11*x - 6 = 0 ↔ x = 1 ∨ x = 2 ∨ x = 3 := by
  rw [show x^3 - 6*x^2 + 11*x - 6 =
      ([1, 2, 3].map (fun r => x - r)).prod by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    ring]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    mul_eq_zero, sub_eq_zero]
```

这一次 `List.map_cons`、`List.map_nil`、`List.prod_cons` 和 `List.prod_nil` 用来把列表字面量上的 `map` 和 `prod` 展开成右结合的因式乘积。到这里，二次、三次乃至更高次数的证明已经具有同一个模板，变化的只有多项式、根列表和变量。这很容易固化成宏：

```anchor macro_poly_roots
syntax "poly_roots " term " with " term " in " term : tactic

macro_rules
  | `(tactic| poly_roots $poly:term with $roots:term in $x:term) =>
      `(tactic|
          rw [show $poly = (($roots).map (fun r => $x - r)).prod by
            simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
            ring] <;>
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
            mul_eq_zero, sub_eq_zero])

example (x : ℚ) : x^2 - 5*x + 6 = 0 ↔ x = 2 ∨ x = 3 := by
  poly_roots x^2 - 5*x + 6 with [2, 3] in x

example (x : ℚ) :
    x^3 - 6*x^2 + 11*x - 6 = 0 ↔ x = 1 ∨ x = 2 ∨ x = 3 := by
  poly_roots x^3 - 6*x^2 + 11*x - 6 with [1, 2, 3] in x
```

下面介绍几种变体。假如我不想写列表，而是直接写类似于`with 1 2 3`，只需要做一点微小的改动：

```anchor macro_poly_roots_1
syntax "poly_roots₁ " term " with " term:max+ " in " term : tactic

macro_rules
  | `(tactic| poly_roots₁ $poly:term with $roots:term* in $x:term) =>
      `(tactic
        | rw [show $poly = (([$roots,*]).map (fun r => $x - r)).prod by
            simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
            ring] <;>
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
            mul_eq_zero, sub_eq_zero])
example (x : ℚ) : x^2 - 5*x + 6 = 0 ↔ x = 2 ∨ x = 3 := by
  poly_roots₁ x^2 - 5*x + 6 with 2 3 in x
```

还记得我们上一章介绍的用 `term:max+` 接受空格分隔的多个 term 的技巧吗？匹配模式中的 `$roots:term*` 捕获这一列根，输出模式中的 `[$roots,*]` 再用逗号把它们组接成列表。

如果我想同时接收这两种写法，可以继续封装一层：

```anchor macro_poly_roots_both
syntax "poly_roots_both " term " with " term:max+ " in " term : tactic

macro_rules
  | `(tactic| poly_roots_both $poly:term with [$roots,*] in $x:term) =>
      `(tactic| poly_roots $poly with [$roots,*] in $x)
  | `(tactic| poly_roots_both $poly:term with $roots:term* in $x:term) =>
      `(tactic| poly_roots $poly with [$roots,*] in $x)

example (x : ℚ) : x^2 - 5*x + 6 = 0 ↔ x = 2 ∨ x = 3 := by
  poly_roots_both x^2 - 5*x + 6 with [2, 3] in x

example (x : ℚ) : x^2 - 5*x + 6 = 0 ↔ x = 2 ∨ x = 3 := by
  poly_roots_both x^2 - 5*x + 6 with 2 3 in x
```

值得一提的是句法引号的两种变体`[$roots,*]`和`$roots:term*`是如何匹配句法规则`term:max+`的：前者实际上把`[2,3]`整体匹配为一个`term`，它内部再解析句法反引提出参数；但要注意后者实际上也能匹配列表！这导致这两个分支不能反过来写，列表写法首先命中更具体的 `[$roots,*]` 分支才能往下继续成功解析；空格分隔写法不能匹配第一种模式才落入第二个通用分支。

或许你会想，能否在句法引号里面直接写类似 `with [$roots,*] <|> $roots:term*` 的选择？不行。`<|>` 属于解析器描述语言，用来组合两条解析规则；句法引号中的内容则必须由某个已经声明好的类别解析成一棵具体句法树，`<|>` 不会成为“匹配左边或右边”的模式节点。

这里的 `*` 和 `,*` 看起来像解析器组合子，其实是 quotation 专门支持的*重复反引用*（antiquotation splice）记法。`term:max+` 在解析输入时生成一个保存若干子节点的重复节点，模式中的 `$roots:term*` 捕获这些子节点；`[$roots,*]` 则先匹配作为单个 `term` 的列表，再捕获列表内部逗号分隔的元素。展开式中的相同记法可以把 `TSyntaxArray` 或 `TSepArray` 插回相应的重复位置。它们操作的是解析器已经确定的重复树形，并没有在引号内定义新的解析选择。若一种表面语法确实需要二选一，应在 {kw}`syntax` 声明中表达选择，再用不同的宏模式处理相应树形。

练习：如果我以这样的格式书写命题`example (x : ℚ) (h : x^2 - 5*x + 6 = 0) : x = 2 ∨ x = 3 := sorry`，如何定义宏？

其实这个宏语法里还有很多“作为用户不想写的细节”，比如说我不想每次都写 `in x`，或者不想每次都写 `with 2 3`，因为这明明都可以从题干当中推断出来呀。但是对调用形式仅为 `by poly_roots` 的 tactic 宏来说，能力确实到此为止了：宏函数收到的输入只有 `poly_roots` 这棵 `Syntax`，目标从二次方程换成三次方程时，输入语法完全没有变化。`MacroM` 没有当前目标和局部上下文，因而没有信息可以区分这两种情况。

这里的限制不是“宏永远不能从命题中提取变量和数字”。如果把整段命题显式作为宏参数传入，或者定义一个包住整个声明的 command 宏，那么宏可以匹配其表面语法，从 `x = 2 ∨ x = 3` 中拆出标识符 `x` 和数字语法 `2`、`3`。但这只是句法提取：宏不知道 `x` 的类型，不知道两个写法是否定义等价，也不能透过定义、记法和强制转换识别同一个数学表达式。对于普通 tactic 调用，命题已经作为待证目标存在于证明状态中，而不在宏的输入语法里；要读取它必须进入 `TacticM`。

`MacroM` 并非完全没有上下文，只是只开放了很窄的查询接口。常用的信息提取 API 如下：

```table
| API | 返回值 | 能知道什么 |
|-----|--------|------------|
| `Syntax.getKind stx` | `SyntaxNodeKind` | 输入节点由哪条句法规则产生 |
| `Syntax.getArgs stx` | `Array Syntax` | 输入节点的直接子节点 |
| `Syntax.getId stx` | `Name` | 标识符节点携带的名字；对非标识符会 panic |
| `Syntax.getPos? stx` | `Option String.Pos.Raw` | 输入的源码起始位置（若有） |
| `Macro.getCurrNamespace` | `MacroM Name` | 文件当前位置的命名空间 |
| `Macro.hasDecl n` | `MacroM Bool` | 全局环境是否含有名为 `n` 的声明 |
| `Macro.resolveNamespace n` | `MacroM (List Name)` | `n` 在当前 namespace/open 状态下可能指向的命名空间 |
| `Macro.resolveGlobalName n` | `MacroM (List (Name × List String))` | `n` 可能指向的全局声明及其可能的投影后缀 |
| `Macro.expandMacro? stx` | `MacroM (Option Syntax)` | `stx` 的最外层是否还能展开一步，以及该步结果 |
```

前四项 `Syntax` 查询只检查调用者传入的句法树；后五项查询由 `MacroM` 的受限 methods 提供。它没有通用的 `getEnv`，更没有 `getMainTarget`、`getLCtx`、`inferType` 或 `isDefEq`。下面这个 command 宏展示了查询边界：它能按当前位置解析一个全局名称并确认声明存在，最后生成普通的 `#check` 命令。

```anchor macro_environment_query
namespace MacroEnvironmentDemo

def answer := 42

syntax "#resolve_decl " ident : command

macro_rules
  | `(#resolve_decl $name:ident) => do
      let ns ← Macro.getCurrNamespace
      let candidates ← Macro.resolveGlobalName name.getId
      let some (declName, projections) := candidates.head?
        | Macro.throwErrorAt name s!"unknown declaration `{name.getId}` in namespace `{ns}`"
      unless projections.isEmpty do
        Macro.throwErrorAt name s!"`{name.getId}` was parsed using field notation"
      unless ← Macro.hasDecl declName do
        Macro.throwErrorAt name s!"resolved name `{declName}` is not a declaration"
      let resolved := mkIdentFrom name declName
      `(command| #check $resolved)

#resolve_decl answer

end MacroEnvironmentDemo
```

这里 `resolveGlobalName` 只做名称解析，`hasDecl` 只回答是否存在；它们不会返回声明的类型或值。若把 `#resolve_decl answer` 改成不存在的名字，宏可以利用当前命名空间生成定位准确的错误，但它仍无法询问任何证明目标。下一章的 `elab_rules` 正是跨过这条边界。


## `rw` 与 `rwa`
%%%
tag := "macro-rw"
%%%

`unicode("← ", "<- ")`用同一个解析器接受Unicode和ASCII箭头；末尾的`?`让箭头可选。`rwRule,*,?`表示零个或多个逗号分隔的规则，并允许最后留下一个逗号，所以`[]`、`[h]`、`[← h, g]`和`[h,]`都符合`rwRuleSeq`。方括号内部使用`withoutPosition`，表示显式定界符已经足以确定范围，不再继承外面的缩进约束。

最后一行从左到右依次读取`rewrite`、零个或多个配置项、必需的规则列表和可选的位置说明。`(name := rewriteSeq)`把根节点种类固定为`Lean.Parser.Tactic.rewriteSeq`，真正的证明术译补器正是按这个名字注册的。

常用的`rw`并不是另一个独立译补器，而是宏：

```anchor syntax_source_rw (module := Examples.SyntaxSources)
macro (name := rwSeq) "rw " c:optConfig s:rwRuleSeq l:(location)? : tactic =>
  match s with
  | `(rwRuleSeq| [$rs,*]%$rbrak) =>
    `(tactic| (rewrite $c [$rs,*] $(l)?; with_annotate_state $rbrak (try (with_reducible rfl))))
  | _ => Macro.throwUnsupported

macro "rwa " rws:rwRuleSeq loc:(location)? : tactic =>
  `(tactic| (rw $rws:rwRuleSeq $[$loc:location]?; assumption))
```

`macro`在`=>`左边仍使用本章一直在读的句法描述语言：`c:optConfig`、`s:rwRuleSeq`和`l:(location)?`分别捕获配置、规则列表和可选位置。`=>`右边开始操作已经解析好的`Syntax`，这里先只解释读源码所必需的记号：

* `` `(rwRuleSeq| ...) ``是`rwRuleSeq`类别的句法模式；`$rs,*`捕获逗号分隔的所有规则，`%$rbrak`额外捕获右方括号这个原子。
* `` `(tactic| ...) ``构造一棵`tactic`句法树。`$c`和`$rbrak`插入单个句法对象，`[$rs,*]`重新插入分隔列表，`$(l)?`插入可选对象。
* `$[$loc:location]?`是另一种可选反引用写法，并显式标出其类别为`location`。
* 如果输入没有形成预期的`rwRuleSeq`结构，`Macro.throwUnsupported`让该宏规则拒绝处理它。

展开结果也很直观：`rw`先运行`rewrite`，再尝试用可约化透明度下的`rfl`关闭目标；`with_annotate_state`把这次尝试前后的状态挂在右方括号位置，供编辑器显示。`rwa`则在`rw`之后继续运行`assumption`。关于句法模式、引用和反引用的系统规则将在下一章讲宏时展开。



# 多条规则如何工作
%%%
tag := "macro-rules-order"
%%%

同一个 syntax kind 可以有多条宏规则。某条规则若 pattern 不匹配，或显式调用 `Macro.throwUnsupported`，框架会继续尝试别的 expander。

```anchor macro_first_rule
open Lean Macro

syntax:max "firstRule" : term

macro_rules
  | `(firstRule) => `(41 + 1)

macro_rules
  | `(firstRule) => Macro.throwUnsupported

example : firstRule = 42 := rfl
```

`throwUnsupported` 表示“这个 expander 不处理该输入”，不是用户错误。上例先注册成功规则，再注册拒绝规则；v4.32.2 会先尝试后注册的拒绝规则，它返回 unsupported 后再落到较早的成功规则。`Macro.throwError` 则表示已经确认输入属于自己，但内容非法，应当停止并报告。

同一 `macro_rules` 块内，应把 pattern 写成互不冗余的分支，按书写顺序匹配。两个完全相同的 pattern 会被 linter 判为 redundant，不能靠第一条 `throwUnsupported` 在块内模拟 fallback。跨多个独立注册块时，同优先级 expander 的注册顺序会影响尝试次序，后注册者通常先被尝试。若正确性依赖顺序，最好让不同 pattern 边界清楚，并为当前版本写回归测试。

规则重叠时至少准备三类测试：

1. 每条规则的唯一命中输入；
2. 重叠输入，明确谁应优先；
3. 谁都不应处理的输入，确认失败路径。

# 真实源码里的四种 tactic 宏
%%%
tag := "macro-real-four-roles"
%%%

Lean 与 Mathlib 的 tactic 宏主要承担四种工作：

1. 给已有 term 或 tactic 加短入口；
2. 拼接分支、重复与收尾控制；
3. 固定配置、lemma 集和领域 rule set；
4. 给同一个 syntax kind 留出可扩展的规则插槽。

这是后文反复使用的分类地图，不是接下来四节的机械目录。阅读顺序先从短包装走到控制器，再借 `trivial` 看多规则回退和开放式扩展；卫生性讲完后，领域配置才补上第三类。每次都分清两件事：宏生成哪段 tactic 语法，展开后的 tactic 又由谁读取目标并执行语义。

## 最薄的包装：`exfalso`、`infer_instance`、`linarith!`
%%%
tag := "macro-real-thin-wrappers"
%%%

Lean 本体中的 `exfalso` 与 `infer_instance` 都只包一层：

:::codeBox "code"
```
macro "exfalso" : tactic => `(tactic| refine False.elim ?_)
macro "infer_instance" : tactic => `(tactic| exact inferInstance)
```
:::

Mathlib 的 `linarith!` 甚至只调整 token，把紧邻名称的叹号改写成 elaborator 接受的独立参数：

:::codeBox "code"
```
macro "linarith!" rest:linarithArgsRest : tactic =>
  `(tactic| linarith ! $rest:linarithArgsRest)
```
:::

```anchor macro_builtin_examples
example (P : Prop) (h : False) : P := by
  exfalso
  exact h

example : Nonempty Nat := by
  infer_instance

example (x y : Rat) (h : x ≤ y) : x ≤ y + 1 := by
  linarith!
```

宏没有寻找矛盾、综合实例或运行线性算术。它只选择现有入口；真正的语义工作留给 `refine`、term 译补和 `linarith` elaborator。Ch10 会再把 `linarith` 内部的证书搜索与证明验证分开。

## 控制器：`try`、`<;>` 与 `ring`
%%%
tag := "macro-real-controllers"
%%%

`try` 展开成 `first` 的两条分支：用户 tactic 失败时，`skip` 兜底。

:::codeBox "code"
```
macro "try " t:tacticSeq : tactic =>
  `(tactic| first | $t | skip)
```
:::

`<;>` 先聚焦主目标，再把右侧 tactic 送到左侧产生的每个目标：

:::codeBox "code"
```
macro:1 x:tactic tk:" <;> " y:tactic:2 : tactic => `(tactic|
  focus
    $x:tactic
    with_annotate_state $tk skip
    all_goals $y:tactic)
```
:::

Mathlib 的 `ring` 采用同一种策略编排，只是候选更专业：`ring1` 是实际的等式关闭器；若它失败，`ring_nf` 分支仍可能成功规范化并留下 residual goal，同时生成建议。Ch09 会沿这两条路径追到带证明的规范形。

:::codeBox "code"
```
macro "ring" : tactic =>
  `(tactic| first
    | ring1
    | try_this ring_nf "The `ring` tactic failed to close the goal. ...")
```
:::

`ring1` 与 `ring_nf` 是 elaborator；宏只安排尝试顺序。

```anchor macro_controller_examples
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor <;> assumption

example : (1 : Int) + 2 = 3 := by
  ring
```

## 多条规则和回退：真实的 `trivial`
%%%
tag := "macro-real-trivial"
%%%

Lean 4.32.2 的 `trivial` 没有 tactic elaborator。`Init/Tactics.lean:1150,1484-1489` 先声明语法，再注册六条宏规则：

:::codeBox "code"
```
syntax "trivial" : tactic

macro_rules | `(tactic| trivial) => `(tactic| assumption)
macro_rules | `(tactic| trivial) => `(tactic| rfl)
macro_rules | `(tactic| trivial) => `(tactic| contradiction)
macro_rules | `(tactic| trivial) => `(tactic| decide)
macro_rules | `(tactic| trivial) => `(tactic| apply True.intro)
macro_rules | `(tactic| trivial) => `(tactic| apply And.intro <;> trivial)
```
:::

这些规则本身不读取目标。tactic 分派先展开一个候选；展开后的 tactic 若在译补或执行中失败，框架再尝试同一 syntax kind 的其他注册候选。最后一条递归调用 `trivial`，因此合取目标可以逐层拆开。

```anchor macro_trivial_use
example (P : Prop) (h : P) : P := by
  trivial

example : True ∧ True := by
  trivial
```

这个例子把 `macro_rules`、回退、递归和 `<;>` 接到一起。先学会单规则宏再看它，源码就不再像六个互不相干的魔法咒语。

# 展开不是只走一次
%%%
tag := "macro-recursive-expansion"
%%%

宏输出仍是一棵 `Syntax`，其中可能包含其他宏，甚至再次包含自己。elaborator 处理当前节点时会继续展开该节点，直到得到当前译补器能够处理的非宏形态。这里不是先对整份文件做一轮独立的全树 fixed-point 预处理。

分层设计因此成立：高层宏生成较低层的便捷语法，低层宏再生成当前 elaborator 能直接处理的非宏语法形态。代价是一个非常朴素的灾难：

:::codeBox "error code"
```
macro "loop" : term => `(loop)
```
:::

输入没变，展开永远有下一轮。真实错误可能表现为递归深度、heartbeat 或宏展开栈异常。遇到它时，不要先提高限制；先比较规则输入和输出，确认每次展开是否朝某个终态前进。

递归宏若处理列表，通常要有明确的空列表基例，并让递归参数严格变短。把“看起来少了一点”换成可以在 pattern 上数出来的下降量。

## 递归与开放式规则集：`iterate`、`decreasing_trivial`、discharger
%%%
tag := "macro-real-extensible"
%%%

`iterate n tac` 在宏展开期读取数字。零次变成 `skip`，后继次数变成一次 `tac` 加更小的 `iterate`。不写次数时，它展开成 `try tac; iterate tac`，所以只有当 `tac` 最终失败时才会停止。

`decreasing_trivial` 服务于递归定义的终止性证明；`get_elem_tactic_extensible` 负责数组、列表和区间下标的边界义务；Mathlib 的 `gcongr_discharger` 与 `use_discharger` 负责自动化产生的 side goal。四者都把同一个 syntax kind 留给多个模块扩展，按导入闭包继续增加候选。

```anchor macro_builtin_recursion
example (n : Nat) (h : n > 0) : n - 1 < n := by
  decreasing_trivial

example (n : Nat) : n = n := by
  iterate 1 rfl
```

开放式规则集不能被描述成“固定展开为某一段脚本”。准确说法是：当前导入闭包向该 syntax kind 注册了哪些候选。

# 卫生性：两个都叫 `x`，不一定是一个名字
%%%
tag := "macro-hygiene"
%%%

看这个宏：

```anchor macro_hygienic_let
macro "hygienicLet(" t:term ")" : term =>
  `(let x := $t; x)

example (x : Nat) : hygienicLet(x + 1) = x + 1 := rfl
```

展开后肉眼看似得到：


:::codeBox "code"
```
let x := x + 1; x
```
:::

若按字符串替换理解，右边 `x + 1` 可能被新 `let x` 捕获，结果就错了。Lean 的卫生宏不会这样做：

- 模板中新写的 `x` 获得当前宏作用域；
- antiquote 进来的 `$t` 保留调用点作用域；
- `let` 的 binder 与 body 中模板写出的 `x` 对应；
- `$t` 里的调用点 `x` 仍指向外层参数。

卫生性并不是“自动挑一个很丑的新字符串”。它依靠标识符携带的 macro scopes 和名字解析信息区分来源。

## 捕获有时是故意的
%%%
tag := "macro-intentional-names"
%%%

若调用者明确提供 binder 名，可以 antiquote 同一个 ident：

```anchor macro_identity_let
macro "identityLet(" n:ident ", " t:term ")" : term =>
  `(let $n := $t; $n)

example : identityLet(y, 7) = 7 := rfl
```

这里的关联是语法接口的一部分，卫生机制并没有失效。

生成调用点之后要引用的顶层声明时，也应让调用者提供 `ident`。固定写在 quotation 里的声明名带宏作用域，外面裸写同样字符可能得到 `Unknown identifier`。这是卫生性在保护你，不是 Lean 忘了自己刚定义过什么。

# 固定领域配置：`continuity` 与 local `map_simp`
%%%
tag := "macro-real-domain-config"
%%%

Mathlib 的 `continuity`、`measurability`、`finiteness`、`arith_mult`、`aesop_cat` 等宏把领域 rule set 与配置交给通用搜索器。例如 `continuity` 的展开骨架是 configured `aesop`，真实源码用 `mkIdent` 构造卫生的 rule-set 名。

```anchor macro_external_examples
example : Continuous (fun x : Real => x) := by
  continuity

example : Measurable (fun x : Real => x) := by
  measurability
```

Mathlib 还有 22 个 local tactic macro，全部位于椭圆曲线实现文件。它们把固定的 `simp only` lemma 集命名为 `map_simp`、`eval_simp`、`C_simp`、`derivative_simp`、`matrix_simp` 或 `pderiv_simp`。这些短名不会泄漏成公共 API，也没有“导入 Mathlib 后直接调用”的用户例子。

# 宏能知道什么
%%%
tag := "macro-information-boundary"
%%%

宏能知道：

- 输入匹配了哪一种语法；
- 各个参数的 `Syntax`；
- source info、syntax kind、孩子和 macro scope；
- 当前宏展开上下文允许访问的信息。

宏不能凭空知道：

- 一个 term 译补后是什么类型；
- `+` 最终解析到哪个常量；
- 当前 tactic goal 是等式还是合取；
- 局部上下文里有哪些假设；
- 两个表达式是否定义等价；
- 某个类型类实例能否综合出来。

这些信息要等译补或元编程阶段才存在。

宏适合做：

- 新记法和语法糖；
- 固定证明模板；
- 参数化地拼接已有 tactic；
- 把冗长 command 包成较短接口。

宏不适合做：

- 根据目标类型选择算法；
- 搜索局部假设；
- 调用 `isDefEq`；
- 直接赋值目标元变量；
- 需要类型驱动反馈的 DSL。

# 第一次撞上宏的边界
%%%
tag := "macro-first-boundary"
%%%

假设要写：


:::codeBox "pseudocode"
```
smart_step
```
:::

要求它在目标是 `True` 时关闭目标，在目标是合取时拆成两项，在局部上下文有匹配假设时使用该假设。

调用处永远只有同一个 token `smart_step`。宏看到的输入也永远是同一棵语法树。目标从 `True` 换成 `P ∧ Q`，宏的输入没有任何变化，所以它没有依据产生不同输出。

当然可以把宏固定展开成已有的搜索 tactic，例如 `first | trivial | constructor | assumption`。这仍是合法而有用的宏，但“观察现场并决定”的工作由那些 tactic 完成，宏只是把它们排成模板。

若要亲手写这段决策程序，就必须让程序进入当前证明现场：读目标列表、返回查询结果、处理失败并继续下一步。下一章从这里开始，而不是从 Monad 的定义背起。

# 宏怎么调
%%%
tag := "macro-debugging"
%%%

## 先分清失败发生在哪一层
%%%
tag := "ch02-h15"
%%%

- `unexpected token`：多半是 parser；
- `unexpected syntax` 或没有宏规则支持：多半是 macro pattern；
- 展开后出现类型不匹配：宏可能已经成功，错误发生在 elaboration；
- tactic 运行后仍留目标：展开和译补都可能成功，证明程序没有完成任务。

层次分错，调试会很滑稽。你可以花一小时改宏 pattern，最后发现只是生成的 `Nat` 项被放进了 `String` 位置。

## 看展开步骤
%%%
tag := "ch02-h16"
%%%

v4.32.2 可以打开 elaboration step trace：

```anchor macro_trace_use
syntax:max "twiceTrace(" term ")" : term
macro_rules | `(twiceTrace($t)) => `($t + $t)

set_option trace.Elab.step true in
#check twiceTrace(2)
```

trace 会显示 `twiceTrace(2)` 变成 `2 + 2`，随后 `+` 继续进入普通译补流程。

可用 API 还包括：

:::codeBox "code"
```
Macro.expandMacro?
Macro.throwUnsupported
Macro.throwError
```
:::

不要假定 `MacroM` 里可以直接 `logInfo`。该 monad 在当前版本没有通用 `MonadLog` 实例。若要稳定打印输入树，可以像上一章一样临时写 command elaborator，或在拥有消息能力的 elaborator 层记录。

## 最小化展开
%%%
tag := "ch02-h17"
%%%

宏出错时，把输出先缩成一个常量：


:::codeBox "code"
```
macro_rules | `(mySyntax ...) => `(0)
```
:::

若仍失败，问题在 parser 或 pattern；若成功，再逐层放回输出模板。对递归宏，额外记录每轮输入规模，找出没有下降的分支。

# 本章练习
%%%
tag := "macro-exercises"
%%%

1. 写 term 宏 `unless0 n then t`，展开成 `if n = 0 then 0 else t`。测试 `Nat` 和 `Int` 上的类型推断差异，并解释差异不是宏做出的。
2. 写 command 宏 `defNats a := 1, b := 2`，用重复 antiquotation 生成多个 `def`。要求声明名来自调用者 ident。
3. 扩展 `poly_roots`，让调用者显式传入多项式表达式，并先用 `ring` 证明它等于候选因式乘积，再从原假设得到乘积为零。
4. 构造一个会发生字符串捕获的纸面展开，再用 Lean 卫生宏实现并证明调用点变量没有被捕获。
5. 给同一个 syntax kind 注册两条重叠规则。写测试确认当前版本的实际优先顺序，然后重构 pattern，使正确性不再依赖跨注册块顺序。
6. 设计一个需求，分别说明用宏实现的版本和必须用 elaborator 的版本。判断标准必须写成“是否需要译补后的类型、目标或局部上下文”，不能写成“复杂就用 elaborator”。

配套文件 `Examples/Ch02Macros.lean` 包含固定宏、参数宏、列表 splice、卫生性、fallback、`poly_roots`，以及 Lean/Mathlib 纯宏探针和 elaborator 边界对照。源码 census 的计数口径固定为 Lean 4.32.2 与 Mathlib commit `905b95818eb32af7874a58b427f50c1711a5e96c`。

# 附录：纯 tactic macro 的分类索引与扫描口径
%%%
tag := "macro-real-census-appendix"
%%%

本节的 *census* 与 *运行探针* 是两份不同证据。逐项文件、行号、展开骨架和排除理由另存于仓库内 `drafts/Ch02PureMacroTacticCensus.md`；正文保留可读的分类索引。

- census 覆盖固定源码树中的全部定义，并记录 public、scoped、local 与混合宏/elaborator 分支；
- 配套文件提供 63 个纯宏运行探针，并另放裸 `positivity`、`gcongr` 等 elaborator 边界对照，不承诺每个内部名称都有独立 theorem 示例。

## Lean 4.32.2 分类索引
%%%
tag := "macro-real-lean-index"
%%%

`Init/` 与 `Lean/` 的主清单按用户可调用的表面形式计 68 项。Std 另有 Do 证明模式宏和数据结构内部 scoped 宏。

- *基础与控制*：`exfalso`、`next`、`try`、`<;>`、`rfl`、`rfl'`、`sorry`、`admit`、`infer_instance`、`rw`、`rwa`、`refine_lift`、`have`、`suffices`、`let`、`let rec`、`refine_lift'`、`have'`、`let'`、`stop`、`unhygienic`、`exists`、`nofun`、`nomatch`、`haveI`、`letI`、`funext`、`solve`、tactic `if`、`by_cases`、`iterate`、`and_intros`，以及多参数或结构模式的 `mintro`。
- *化简、重写与规范化包装*：`erw`、`simp!`、`simp_all!`、`dsimp!`、`simp?!`、`simp_all?!`、`dsimp?!`、`simpa!`、`simpa?`、`simpa?!`、`rw_mod_cast`、`exact_mod_cast`、`apply_mod_cast`、`bv_omega`、`assumption_mod_cast`、`norm_cast`、`ac_nf`、`ext1`。
- *扩展钩子与内部辅助*：`simp_wf`、`clean_wf`、`decreasing_trivial`、`decreasing_trivial_pre_omega`、`decreasing_with`、`decreasing_tactic`、`deriving_ReflEq_tactic`、`deriving_LawfulEq_tactic_step`、`deriving_LawfulEq_tactic`、`get_elem_tactic_extensible`、`get_elem_tactic`、`array_get_dec`、`array_mem_dec`、`sizeOf_list_dec`、`∎`、scoped `order`、scoped `purity_tac`。

Std 的用户相关宏包括 `mleave`、复合 `mintro`、复合 `mrevert`、`mspec_no_simp`、`mspec`、`mvcgen_trivial_extensible` 与 `mvcgen_trivial`。DHashMap/DTreeMap 中的 `wf_trivial`、`empty`、`simp_to_raw`、`simp_to_model` 和 `tree_tac` 是内部 scoped 宏。

## Mathlib v4.32.2 分类索引
%%%
tag := "macro-real-mathlib-index"
%%%

固定 commit `905b95818eb32af7874a58b427f50c1711a5e96c` 共扫描 8264 个 Lean 文件。源码定义计数为 82 个非局部直接 tactic macro、37 个 `syntax + macro_rules` 形式和 22 个 local tactic macro。

- *控制与目标管理*：`assumption'`、`repeat1`、`existsi`、`observe?`、`rsuffices`、`choose!`、`peel ... using`、`bound [...]`、`conv_lhs`、`conv_rhs`、`clean`、`set!`。
- *重写与转换*：`nth_rewrite`、`nth_rw`、`grw`、`apply_rewrite`、`apply_rw`、`nth_grewrite`、`nth_grw`、`convert!`、`convert_to!`、`ac_change`、`ac_change!`、`qify`、`zify`、`rify`、`bdsimp`。
- *逻辑包装*：`by_cases!`、`by_contra!`、带变量的 `contrapose`、`contrapose!`、`itauto!`、`tauto_set`。
- *代数与算术包装*：`ring`、`ring!`、`ring1!`、`ring_nf!`、`ring1_nf!`、`abel`、`abel!`、`abel1!`、`abel_nf!`、`linarith!`、`linarith?!`、`nlinarith!`、`polynomial!`、`polynomial_nf!`、`noncomm_ring`、`group`、`order`、`compute_degree!`、`monicity`、`monicity!`、`fin_omega`、`pnat_to_nat`、`enat_to_nat`。
- *自动化配置与 discharger*：`continuity`、`continuity?`、`measurability`、`measurability?`、`finiteness`、`finiteness?`、`finiteness_nonterminal`、`arith_mult`、`arith_mult?`、`compactness`、`compactness?`、`closedness`、`closedness?`、`positivity [hs]`、`gcongr_discharger`、`use_discharger`、`cfc_tac`、`cfc_cont_tac`、`cfc_zero_tac`。
- *专用包装*：`algebraize_only`、`eval_det`、`isBoundedDefault`、`bddDefault`、`compareOfLessAndEq_rfl`、scoped `trunc`、`volume_tac`、`uniqueDiffWithinAt_Ici_Iic_univ`、`frac_tac`、`smul_tac`、`slice_lhs`、`slice_rhs`。
- *领域模块*：`mem_tac`、`witt_truncateFun_tac`、`map_fun_tac`、`ghost_simp`、scoped `hopf_tensor_induction`、`subst_hom_lift`、`discrete_cases`、`valid`、`rfl_cat`、`aesop_cat`、`aesop_cat?`、`aesop_cat_nonterminal`、三个 scope 中的 `transfer_rw`/`transfer`、`bitwise_assoc_tac`、`unit_interval`、`restrict_tac`、`restrict_tac?`、`aesop_mat`、`aesop_graph`、`aesop_graph?`、`aesop_graph_nonterminal`、scoped `sz_positivity`、`toFinite_tac`、`to_encard_tac`、`apply_gmonoid_gnpowRec_zero_tac`、`apply_gmonoid_gnpowRec_succ_tac`。

22 个 local 宏是椭圆曲线文件中的 `map_simp`、`eval_simp`、`C_simp`、`derivative_simp`、`matrix_simp`、`pderiv_simp` 重复局部版本。完整逐项文件与行号保存在本次源码审计产物中；正文按语义压缩同名 scope 与重载形式，所以这里称“分类索引”，不称“119 项逐行全表”。

## 常见排除项
%%%
tag := "macro-real-exclusions"
%%%

`simp`、`omega`、`exact`、`apply`、`intro`、`cases`、`all_goals` 由 Lean builtin tactic 或 elaborator 执行。Mathlib 的 `linarith`、`nlinarith`、无参数 `positivity`、`gcongr`、`norm_num`、`ring1`、`ring_nf`、`abel1`、`abel_nf`、`compute_degree`、`polynomial`、`polynomial_nf`、`tauto`、`by_contra`、`convert`、`convert_to`、`set`、`observe` 也不是纯宏；相邻的 `!`、`?` 或复合表面形式才可能是宏。

判断方法是追踪 syntax kind 最终注册了 `Macro` expander 还是 `Tactic` elaborator。一个 tactic 可以同时包含两层：`positivity [h]` 是宏，展开后的无参数 `positivity` 是 elaborator。
