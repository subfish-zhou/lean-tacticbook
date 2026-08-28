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

宏接住一种已经声明的句法，把它展开成另一棵句法树。常见用途是给重复的项、命令或证明步骤提供短写法。

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
* {anchorTerm macro_XOR}`l` 和 {anchorTerm macro_XOR}`r` 是宏的两个参数，都按 {anchorTerm macro_XOR}`term` 句法类别解析。{anchorTerm macro_XOR}`" XOR "`是这个宏的记号。此处我们定义的是中缀运算符，所以参数写在记号的两边。
* {anchorTerm macro_XOR}`" XOR "`两边的空格是为了将来这个运算符出现在Lean Infoview里的时候也能保留空格。
* 末尾的 `: term` 声明 {anchorTerm macro_XOR}`l:term:10 " XOR " r:term:11` 这一整块新记号也属于 {anchorTerm macro_XOR}`term` 句法类别。
* {anchorTerm macro_XOR}`=>` 后面是宏的展开式，也就是它压缩的句法。`` `() ``是句法引号（syntax quotation），类型是 ``MacroM (TSyntax `term)``，这意味着 Lean 要将括号内的项解析成一棵 `term` 类别的 `Syntax` 句法树。{anchorTerm macro_XOR}`$l` 和 {anchorTerm macro_XOR}`$r` 称为反引（antiquotation），负责把调用处捕获的两棵句法树插入展开式。

其实这个最简单的宏是以下这段代码的语法糖：

```anchor macro_desugering1
syntax:10 term:10 " XOR₁ " term:11 : term

macro_rules
  | `($l:term XOR₁ $r:term) => `((!$l && $r) || ($l && !$r))
```

此处你可以看到，句法和宏规则其实是分开的两种功能，句法层定义这个宏要如何被调用，而宏规则声明这个宏实际上做了什么。而宏规则又被 {kw}`=>` 分成两部分，分别对应着两棵句法树，其中左边是*匹配模式*，右边是*展开式*。解析器先按照句法声明生成句法树；宏展开器遇到与左侧模式匹配的宏节点时，再把它替换成右侧展开式。

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

六条规则给同一种句法注册了六个候选展开。越晚注册的宏会被越先尝试。如果这些证明术都没生效就只能失败了。

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

但是如果你想递归调用就会报错，因为解析器暂时还不认识 `mytrivial_error` 这条证明术句法。

:::codeBox "error code"
```
macro "mytrivial_error" : tactic =>
  `(tactic| first
    | ...
    | apply And.intro <;> mytrivial_error) -- 报错：unknown tactic
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

值得一提的是句法引号的两种变体 `[$roots,*]` 和 `$roots:term*` 是如何匹配句法规则 `term:max+` 的：前者实际上把 `[2,3]` 整体匹配为一个 `term`，再从列表内部捕获逗号分隔的参数；但要注意，后者实际上也能匹配列表！这导致两个分支不能反过来写，列表命中`[$roots,*]` 模式才能正确沿该分支展开。空格分隔写法直接不能匹配第一个分支。

或许你会想，能否在句法引号里面直接写类似 `with [$roots,*] <|> $roots:term*` 的选择？不行。`<|>` 属于解析器描述语言，用来组合两条解析规则；句法引号中的内容则必须由某个已经声明好的类别解析成一棵具体句法树，`<|>` 不会成为“匹配左边或右边”的模式节点。

这里的 `*` 和 `,*` 看起来像解析器组合子，其实是 quotation 专门支持的*重复反引用*（antiquotation splice）记法。`term:max+` 在解析输入时生成一个保存若干子节点的重复节点，模式中的 `$roots:term*` 捕获这些子节点；`[$roots,*]` 则先匹配作为单个 `term` 的列表，再捕获列表内部逗号分隔的元素。展开式中的相同记法可以把 `TSyntaxArray` 或 `TSepArray` 插回相应的重复位置。它们操作的是解析器已经确定的重复树形，并没有在引号内定义新的解析选择。若一种表面语法确实需要二选一，应在 {kw}`syntax` 声明中表达选择，再用不同的宏模式处理相应树形。

练习：如果我以这样的格式书写命题`example (x : ℚ) (h : x^2 - 5*x + 6 = 0) : x = 2 ∨ x = 3 := sorry`，如何定义宏？

其实这个宏语法里还有很多“作为用户不想写的细节”，比如说我不想每次都写 `in x`，或者不想每次都写 `with 2 3`，因为这明明都可以从题干当中推断出来呀。但是对调用形式仅为 `by poly_roots` 的 tactic 宏来说，能力确实到此为止了：宏函数收到的输入只有 `poly_roots` 这棵 `Syntax`，目标从二次方程换成三次方程时，输入语法完全没有变化。`MacroM` 没有当前目标和局部上下文，因而没有信息可以区分这两种情况。

这里的限制不是“宏永远不能从命题中提取变量和数字”。如果把整段命题显式作为宏参数传入，或者定义一个包住整个声明的 command 宏，那么宏可以匹配其表面语法，从 `x = 2 ∨ x = 3` 中拆出标识符 `x` 和数字语法 `2`、`3`。但这只是句法提取：宏不知道 `x` 的类型，不知道两个写法是否定义等价，也不能透过定义、记法和强制转换识别同一个数学表达式。对于普通 tactic 调用，命题已经作为待证目标存在于证明状态中，而不在宏的输入语法里；要读取它必须进入 `TacticM`。

# 宏没有收到的名字
%%%
tag := "ch03-macro-missing-name"
file := "ch03-macro-missing-name"
%%%

最后一版 `poly_roots` 仍给每个调用处留下一件烦人的工作。眼前的命题明明已经写着多项式、根和变量，我们却还得把三者再写一遍。普通宏都不能偷看证明目标来省掉这些参数：它们只拿得到自身调用的 `Syntax` 树。但宏展开计算仍能查询少量展开现场。下面用一个命令宏读取当前命名空间，并在那里解析一个名字。

本章的伴随示例模块已经 `import Lean` 并 `open Lean`；以下片段按出现顺序放在同一个命名空间中。若把片段单独移进新文件，也要先补上这两项环境。

```anchor macro_environment_query
namespace MacroEnvironmentDemo

def answer := 42

syntax "#resolve_decl " ident : command

macro_rules
  | `(#resolve_decl $name:ident) => do
      let ns ← Macro.getCurrNamespace
      let candidates ← Macro.resolveGlobalName name.getId
      let some (declName, projections) := candidates.head?
        | Macro.throwErrorAt name
            s!"unknown declaration `{name.getId}` in namespace `{ns}`"
      unless projections.isEmpty do
        Macro.throwErrorAt name
          s!"`{name.getId}` was parsed using field notation"
      unless ← Macro.hasDecl declName do
        Macro.throwErrorAt name
          s!"resolved name `{declName}` is not a declaration"
      let resolved := mkIdentFrom name declName
      `(command| #check $resolved)

#resolve_decl answer

end MacroEnvironmentDemo
```

模式捕获的 `name` 类型是 `TSyntax`，句法类别为 `ident`；`name.getId` 从中取出 `Name`。`Macro.resolveGlobalName` 返回一份候选列表，每一项由声明名与字段记法投影列表组成。`head?` 把空表变成 `none`；`let some (declName, projections) := ... | ...` 在得到首项时拆出这两个分量，得到 `none` 时则走竖线后的报错分支。后面的 `unless condition do ...` 只在条件为假时运行其分支。

这个命令会打印 `MacroEnvironmentDemo.answer` 的类型。宏从未收到这个完整限定名。它拿到标识符 `answer`，读取当前命名空间，请 Lean 找出这个名字在当前位置可见的全局候选项，排除小命令不支持的两种情况，最后把解析出的名字放进一条普通的 `#check` 命令。

运行成功时，输出中应出现 `MacroEnvironmentDemo.answer : Nat`；编辑器也可能把 `Nat` 显示为 `ℕ`。

先停在函数体的第一行：

```anchor macro_environment_namespace
      let ns ← Macro.getCurrNamespace
```

`Macro.getCurrNamespace` 的类型不是 `Name`，而是 `MacroM Name`。`Name` 已经是名字；`MacroM Name` 则是一项计算：Lean 在当前宏展开上下文中运行它时，可以读取上下文、更新宏状态，也可能失败，成功后才产出 `Name`。普通的 `let ns := ...` 会把计算本身绑定给 `ns`；左箭头则先运行计算，再把得到的 `Name` 绑定给 `ns`。

下一行形状相同，不过这次得到的是列表：

```anchor macro_environment_candidates
      let candidates ← Macro.resolveGlobalName name.getId
```

第二项动作依赖模式捕获的句法；后面的错误又同时依赖原始标识符与第一项动作返回的命名空间。`do` 让我们按执行顺序写出这些依赖。底层的 `bind` 接收一项计算，再接收一个函数；这个函数拿到前一项计算的成功结果后，构造后续计算（continuation）：

:::codeBox "code"
```
bind : M α → (α → M β) → M β
```
:::

对于读取命名空间的那一行，`M` 是 `MacroM`，`α` 是 `Name`，后续就是宏函数体剩下的全部内容。读取命名空间若成功，`bind` 就把那个 `Name` 交给后续；若失败，`ns` 根本不会出现，后续也不会运行。

有时下一个值已经是普通值。`pure` 把它放回同一类计算中：

:::codeBox "code"
```
pure : α → M α
```
:::

`do` 块里的 `return` 使用的就是这项操作。`#resolve_decl` 最后的引用已经具有预期的 `MacroM (TSyntax …)` 类型，句法类别为 `command`，所以函数体直接以它收尾即可。假如我们先把命令句法构造成普通值 `cmd`，那么 `return cmd` 会把它放入 `MacroM` 再交给调用者。

几个错误分支也说明了函数体为什么始终留在 `MacroM` 中。`Macro.throwErrorAt name msg` 会停止当前展开，并把失败定位到 `name`；余下的 bind 都不会再运行，我们也不必在每一行之后手动传递错误值。

最后那个标识符值得再看一眼：

```anchor macro_environment_resolved
      let resolved := mkIdentFrom name declName
```

这一行确实用了普通的 `:=`。取得 `declName` 之后，定义在 `Init/Meta/Defs.lean` 中的 `mkIdentFrom` 会立即构造句法，并从用户写下的标识符复制源位置。这里没有 `MacroM` 动作要运行。因此，`:=` 与 `←` 的区别不在个人偏好，也不在异步执行。只要看右侧的类型：普通的 `α` 留在 `:=` 后面；`M α` 则必须先用 `←` 运行，后续代码才能使用里面的 `α`。

# `M` 所携带的计算
%%%
tag := "ch03-phase-computation"
file := "ch03-phase-computation"
%%%

同样的四种形状会贯穿 Lean 的元编程 API：

:::codeBox "pseudocode"
```
ordinary result       α
phase computation     M α
lift a result         pure : α → M α
sequence computations bind : M α → (α → M β) → M β
```
:::

在 `#resolve_decl` 中，计算先读取当前命名空间，再解析名字，然后检查声明，任一步都可能抛出带源位置的错误。若每个辅助函数都要手动传递上下文、状态以及结果或异常，真正的命令就会被这些传递步骤盖住。`MacroM` 一次规定好传递规则；`bind` 把各段接起来；`do` 则恢复我们自然阅读这些工作的顺序。

这个例子没有写入任何文件，但读取隐含上下文、分配卫生作用域、积累跟踪消息以及失败后停止，同样都是计算效应。运行 `MacroM α` 时，Lean 会按这套规则穿过这些效应，成功后交出 `α`。

Monad 律保证我们重构代码时，这套记法不会悄悄换掉含义。把普通值替换成 `pure value` 后立即 bind，不应凭空多做工作；连续三个 bind 重新分组，也不应只因括号挪了位置就改变结果。Lean 把长长的 `do` 块翻成嵌套 bind 时，我们需要的正是这些保证。

## 可选：`MacroM` 的能力从哪里来
%%%
tag := "ch03-macrom-stack"
file := "ch03-macrom-stack"
%%%

本章余下内容只需要上面的操作性读法。想看看这些操作从何而来，可以在这里短暂拐进变换器（transformer）栈；否则直接跳过这一节。

Lean 4.32.2 在 `Init/Prelude.lean` 中的实际定义很短：

:::codeBox "code"
```
abbrev MacroM := ReaderT Macro.Context
  (EStateM Macro.Exception Macro.State)
```
:::

从里向外读。`EStateM Macro.Exception Macro.State` 携带宏状态与失败；`ReaderT Macro.Context` 再加上一份只读的展开上下文。

`ReaderT` 中的 `T` 代表变换器。它接过一种已有的计算，再为这种计算加上读取只读上下文的能力；改变的是计算能做什么，最终的 `Name` 本身并没有多包一层数据容器。内层本来就会携带状态和失败；变换后的结果既保留这些能力，也能读取上下文。组合后的计算仍然提供 `pure` 与 `bind`，所以同一套 `do` 记法就能把所有动作依次连起来。

后面的层也按同样方式构造：

:::codeBox "pseudocode"
```
CoreM     := ReaderT Core.Context (StateRefT Core.State (EIO Exception))
MetaM     := ReaderT Meta.Context (StateRefT Meta.State CoreM)
TermElabM := ReaderT Term.Context (StateRefT Term.State MetaM)
TacticM   := ReaderT Tactic.Context (StateRefT Tactic.State TermElabM)
```
:::

每个外层变换器都加入另一个阶段所需的上下文或状态，同时保留下层已有的能力。后续章节会等到真正的证明术需要它们时，再逐层拆开。

`MacroM` 刻意窄得多。它没有通用的 `getEnv`，没有证明目标或局部假设，也走不到类型推断或定义相等性那里。Lean 只通过一组不透明方法，允许它询问少量展开期问题，其中包括 `hasDecl`、`resolveNamespace` 和 `resolveGlobalName`。这些受限的名字查询并没有把整个 `Environment` 交给宏；`#resolve_decl` 只能走这组方法。

# 宏可以问的少数事情
%%%
tag := "ch03-macro-narrow-api"
file := "ch03-macro-narrow-api"
%%%

既然 `#resolve_decl` 已经给了我们使用这些操作的理由，现在放一张紧凑的表正合适。

```table
| 宏中的需要 | 可用操作 | 返回内容 |
|---|---|---|
| 检查捕获的句法 | `Syntax.getKind`, `Syntax.getArgs`, `Syntax.getId`, `Syntax.getPos?` | 树形、子节点、标识符文字或源位置 |
| 读取当前命名空间 | `Macro.getCurrNamespace` | `MacroM Name` |
| 解析命名空间名字 | `Macro.resolveNamespace` | 候选命名空间名字 |
| 解析全局名字 | `Macro.resolveGlobalName` | 候选声明名字，以及可能的字段记法投影 |
| 检查声明是否存在 | `Macro.hasDecl` | `MacroM Bool` |
| 在当前根节点展开一步宏 | `Macro.expandMacro?` | `none`，或一个展开后的 `Syntax` 结果 |
| 定位消息 | `getRef`, `Macro.throwErrorAt` | 当前引用，或带位置的失败 |
| 拒绝一个输入 | `Macro.throwUnsupported` | 控制权返回候选项选择过程 |
| 记录展开信息 | `Macro.trace` | 存入宏状态的跟踪消息 |
```

这些操作只够宏查看输入树和展开位置；`poly_roots` 所缺的证明目标、局部上下文、推断类型和定义相等性仍在门外。

# 两条规则都想接住同一个输入时
%%%
tag := "ch03-macro-candidates"
file := "ch03-macro-candidates"
%%%

`poly_roots_both` 已经迫使我们把列表形状的模式放在一般项序列之前。那是一种顺序：同一个 `macro_rules` 块里的备选项从上到下依次尝试。一旦某个模式匹配，生成的展开器就接管这个分支；从右侧抛出 `Macro.throwUnsupported` 只会拒绝这个展开器，不会回到同一代码块里的下一个模式。Lean 在 `Lean/Elab/MacroRules.lean` 中组装这种展开器。

还有一种更简单的错误，Lean 会在我们来得及猜测顺序之前就抓住它：

:::codeBox "error code"
```
syntax:max "sameRule" : term

macro_rules
  | `(sameRule) => `(41)
  | `(sameRule) => `(42)  -- error: redundant alternative #2
```
:::

第二个模式永远到不了，所以冗余备选项检查器（linter）会拒绝它。彼此重叠却不完全相同的模式仍然很有用，`poly_roots_both` 的列表形式与空格分隔形式已经展示过；但如果一般形式也能吃掉同一棵树，具体形式就必须放在前面。

分开的 `macro_rules` 声明会创建分开的展开器。`Lean/KeyedDeclsAttribute.lean` 中的键控声明表，会把同一句法种类中新注册的展开器放到旧展开器前面：

```anchor macro_first_rule
open Lean Macro

syntax:max "firstRule" : term

macro_rules
  | `(firstRule) => `(41 + 1)

macro_rules
  | `(firstRule) => Macro.throwUnsupported

example : firstRule = 42 := rfl
```

后写的声明会先尝试。它用 `throwUnsupported` 拒绝，于是 Lean 回到候选链，询问较旧的展开器；旧展开器给出 `41 + 1`。开放规则集正是这样获得新候选项，而不必修改原始定义。

`Macro.throwErrorAt` 作的是另一种决定：候选项已经接住输入，却判定它无效。根宏引擎会返回这个错误，不再询问更旧的项宏或命令宏展开器。成功展开同样会结束根候选项选择。若返回的项后来译补失败，Lean 不会重新打开旧的项宏候选项，再问它们要一个答案。

证明术分派器在根宏引擎外又包了一层回溯。它先保存证明术状态，再一起运行宏展开与生成的证明术；如果宏成功展开，生成的证明术却随后失败，分派器便恢复状态，改试另一个已注册的证明术候选项。因此，分开的 `trivial` 规则表现得像一连串证明尝试，而不只是句法备选项。根宏引擎仍遵守上面的约定，回溯是 `evalTactic` 加在外面的。把这两重循环分开，才能避免一条诱人却错误的规则：“译补失败总会尝试下一个宏。”

# 展开可以露出另一个宏
%%%
tag := "ch03-recursive-expansion"
file := "ch03-recursive-expansion"
%%%

递归的 `mytrivial` 规则在 `apply And.intro` 拆开合取之后，生成了一个新的 `mytrivial`。Lean 不需要特殊的“递归调用”指令。它收到新的证明术句法，开始处理这段句法，在当前节点又遇到一个宏，于是接着展开它。

`Macro.expandMacro?` 只执行一步根节点展开。如果传入的句法是宏调用，它会返回一次展开；它不承诺追完结果内部的每个宏。`Init/Meta/Defs.lean` 中的辅助函数 `Macro.expandMacros` 还带有一道谓词边界：当前节点获准时，它反复展开根节点，根不再展开后才递归子节点；递归使用的默认谓词会在 `byTactic` 处保留整棵子树，不预先钻进去。生产中的项、命令和证明术译补器也会在处理节点时逐个展开。Lean 不会先对整份文件运行不动点预处理，把所有宏全部替换掉。

所以，递归需要的东西与普通函数一样：必须前进。下面这个宏一步也没走：

```anchor macro_loop_tac
syntax "loopTac" : tactic
macro_rules
  | `(tactic| loopTac) => `(tactic| loopTac)
```

:::codeBox "error code"
```
example : True := by loopTac
-- error: maximum recursion depth has been reached
```
:::

输出与输入形状完全相同，于是展开器一次次回到同一个节点，直到递归深度守卫截住它。提高 `maxRecDepth` 只是把走廊修得更长一些。

`Init/TacticsExtra.lean` 中 Lean 自己的 `iterate` 定义，把递减量直接摆了出来：

:::codeBox "code"
```
syntax "iterate" (ppSpace num)? ppSpace tacticSeq : tactic
macro_rules
  | `(tactic| iterate $seq:tacticSeq) =>
      `(tactic| try ($seq:tacticSeq); iterate $seq:tacticSeq)
  | `(tactic| iterate $n $seq:tacticSeq) =>
      match n.1.toNat with
      | 0   => `(tactic| skip)
      | n+1 => `(tactic| ($seq:tacticSeq); iterate $(quote n) $seq:tacticSeq)
```
:::

带数字的形式在每次生成的递归调用中，都把写下的自然数减一。零会展开为 `skip`，所以重复展开最终会抵达基例。展开与证明术执行交错进行：生成的序列先执行第一个证明术，之后分派器才会走到下一个 `iterate` 节点。

不带数字的形式没有句法上递减的计数器。这里的 `try` 接收的是整段证明术序列，等价地可读成“尝试当前 `$seq`，成功后再递归 `iterate $seq`；其中任一步失败，就退回这一轮之前并以 `skip` 成功结束”。因此，每个成功并推进状态的轮次都会抵达下一轮；第一次失败截住递归，并保留更早轮次已经取得的进展。若 `$seq` 永远成功却从不前进，递归就不会遇到这个停止信号，最终只能由深度守卫截断。

开放规则集也需要相似的纪律。若新增的 `trivial` 或 `decreasing_trivial` 规则会递归回到同一个开放槽，它就必须关闭目标，或者让一个明确的良基度量严格下降。仅仅把目标改成另一个形状并不够：两条规则仍可能让目标来回切换。候选项失败并恢复状态，只保证候选链能够继续尝试，也不能单独证明递归终止。开放让添加规则变得便宜，却不会替新增规则证明终止性。

# 为什么两个 `x` 不会相撞
%%%
tag := "ch03-hygiene"
file := "ch03-hygiene"
%%%

宏展开可以插入绑定符（binder）。如果展开只是文本替换，下面例子中新生成的绑定符就会捕获调用者的 `x`：

```anchor macro_hygienic_let
macro "hygienicLet(" t:term ")" : term =>
  `(let x := 0; ($t, x))

example (x : Nat) : hygienicLet(x + 1) = (x + 1, 0) := rfl
```

按文本替换，调用看起来会变成 `let x := 0; (x + 1, x)`，括号里的两个 `x` 都会指向新绑定符。这个例子能得到 `(x + 1, 0)`，是因为引用是卫生的。

`Lean/Elab/Quotation.lean` 中的 Lean 引用译补器，会给模板里写下的标识符分配宏作用域。模板引入的绑定符 `x` 与模板末尾的那个 `x` 会取得匹配的作用域信息，因此相互指向。通过 `$t` 插入的句法则保留调用处的名字信息，其中的 `x` 仍然指向外面；新生成的绑定符捕获不到它。打印出来的文本或许有三个字符完全相同的 `x`，名字解析看到的却不止这些字符。

有时我们就是想要捕获。那就应让调用者显式提供名字：

```anchor macro_identity_let
macro "identityLet(" n:ident ", " t:term ")" : term =>
  `(let $n := $t; $n)

example : identityLet(y, 7) = 7 := rfl
```

两处绑定符都来自反引用标识符 `$n`，因此这层联系是有意建立的，并且直接显露在调用处。同一条规则对命令宏也很有用。若生成的代码会引入一个顶层声明，而调用者稍后还要提到它，就请调用者传入 `ident`，再反引用进去；只在引用模板里写死的声明名会得到宏作用域，事后未必还能用同一个裸名访问。

这些内容已经足够我们设计卫生宏。完整的名字解析系统还携带预解析的全局名、命名空间信息，并会特殊处理受保护常量的标识符。等我们构造译补器并检查 `Expr` 时，这些细节才会派上用场；要解释调用者的 `x` 为什么能从这个 `let` 里幸存下来，还用不着它们。

# 阅读 Lean 自己使用的宏
%%%
tag := "ch03-production-macros"
file := "ch03-production-macros"
%%%

我们的小宏已经露出了足够多的机械结构，现在可以开始读生产代码，不必逐个翻译记号（token）。先看 `Init/Tactics.lean` 里的 `rw` 和 `rwa`，因为它们的用户接口已经很熟悉：

:::codeBox "code"
```
macro (name := rwSeq) "rw " c:optConfig s:rwRuleSeq l:(location)? : tactic =>
  match s with
  | `(rwRuleSeq| [$rs,*]%$rbrak) =>
    `(tactic|
      (rewrite $c [$rs,*] $(l)?;
       with_annotate_state $rbrak (try (with_reducible rfl))))
  | _ => Macro.throwUnsupported

macro "rwa " rws:rwRuleSeq loc:(location)? : tactic =>
  `(tactic| (rw $rws:rwRuleSeq $[$loc:location]?; assumption))
```
:::

重复拼接 `$rs,*` 把已经解析好的重写规则搬进 `rewrite` 调用。位置之类的可选句法只在存在时才会拼进去。右方括号被单独保存在 `$rbrak` 中，这样生成的 `rfl` 尝试便能把显示的证明状态定位到用户预期的源位置。`rw` 并不实现重写；它打包 `rewrite`，再廉价地试一下反身性。`rwa` 又把这个接口包了一层，随后接上 `assumption`。

懂得引用之后，`Init/Tactics.lean` 中 `try` 和 `<;>` 的源码也把委托关系写得很直白：

:::codeBox "code"
```
macro "try " t:tacticSeq : tactic =>
  `(tactic| first | $t | skip)

macro:1 x:tactic tk:" <;> " y:tactic:2 : tactic =>
  `(tactic|
    focus
      $x:tactic
      with_annotate_state $tk skip
      all_goals $y:tactic)
```
:::

`try` 把选择与状态恢复交给 `first`，它自己的宏只负责提供 `skip` 这个成功的后备项。`<;>` 把目标调度交给 `focus` 和 `all_goals`，同时保留运算符记号，供编辑器标注状态。两个宏都不检查目标。生成的证明术会稍后在证明术执行期间做这件事。纯句法宏由此可以提供复杂的证明接口，而不亲自完成语义工作。

现在把先前重建的 `mytrivial` 与 `Init/Tactics.lean` 中 Lean 的真实规则放在一起看：

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

练习背后没有藏着另一个 `trivial` 引擎。生产定义使用的正是同样的开放注册，以及同样的递归合取规则。

`Init/WFTactics.lean` 中的 `decreasing_trivial` 把开放槽用在一项针对特定领域的工作上：

:::codeBox "code"
```
syntax "decreasing_trivial" : tactic

macro_rules
  | `(tactic| decreasing_trivial) =>
      `(tactic| (simp +arith -failIfUnchanged) <;> done)
macro_rules | `(tactic| decreasing_trivial) => `(tactic| omega)
macro_rules | `(tactic| decreasing_trivial) => `(tactic| assumption)
```
:::

其他模块引入一族新的例行终止性义务时，可以再注册规则。宏建立一个稳定入口；导入的代码提供候选项；语义证明术完成证明。这是一个由句法注册与证明术回溯搭成的扩展槽。

直到这里，一小段分类才值得保留下来。生产宏常常像 `rwa` 一样提供短入口，像 `try` 和 `<;>` 一样编排现有证明术，像 `trivial` 一样留下开放规则集，或像 `decreasing_trivial` 一样打包针对特定领域的配置；这些作用往往彼此重叠。读源码时，有用的问题仍然很具体：这个宏保留了哪些句法，生成了哪些句法，又由后面的哪一个译补器或证明术完成依赖类型和目标的工作？

读生产证明术源码时，还会遇到 `@[builtin_tactic ...]`。这个名字容易让人误画出第三个执行阶段。前两类的可操作分界已经出现：宏包装运行 `MacroM` 并返回新的 `Syntax`；证明术译补器接收 `Syntax`，运行 `TacticM`，直接改变证明术状态。builtin tactic 并不是第三个执行阶段，而是直接用 `@[builtin_tactic 句法种类]` 注册的证明术译补器。Lean 在 `Lean/Elab/Tactic/BuiltinTactic.lean` 中这样注册 `done`：

:::codeBox "code"
```
@[builtin_tactic Lean.Parser.Tactic.«done»] def evalDone : Tactic := fun _ =>
  done
```
:::

这里的 `Tactic` 就是 `Syntax → TacticM Unit`。看到函数返回一项修改证明状态的 `TacticM` 计算，便知道它属于证明术译补器；`builtin_tactic` 属性只说明它直接按句法种类注册。Lean 的源码注释也建议用户代码通常优先使用 `elab` 或 `elab_rules`，而不是直接写这个属性。

# 找到失败开始的那一层
%%%
tag := "ch03-debug-layers"
file := "ch03-debug-layers"
%%%

一个小宏可能在任何证明步骤运行之前就失败，也可能直到成功展开很久以后才失败。我们拿同一个对象，在四个不同位置把它弄坏：

```anchor macro_trace_use
syntax:max "twiceTrace(" term ")" : term
macro_rules
  | `(twiceTrace($t)) => do
      Macro.trace `Elab.step "expanding twiceTrace"
      `($t + $t)

set_option trace.Elab.step true in
#check twiceTrace(2)
```

先删掉右括号，破坏调用。解析器无法构造声明过的 `twiceTrace` 句法，因此没有任何宏模式运行。展开器跟踪消息不会出现，因为程序从未抵达展开器。修补文本，直到解析器能够产出这个节点。

再改动宏模式，让它期待另一棵树，却不动句法声明和调用。解析成功了，展开器却拒绝这个节点，Lean 最终会报告该宏句法不受支持。检查节点种类与捕获字段，或者暂时用一个匹配整个声明形式的模式替换复杂模式，便能把引用模式不匹配与解析器问题隔开。

恢复模式，再生成一段能解析却不能译补的项，例如调用一个未知标识符。跟踪记录说明 `twiceTrace` 已经展开：宏已经完成句法到句法的工作，错误始于生成句法的译补。先把输出缩成 `` `(0) `` 这样的已知常量，再逐片恢复模板，直到坏名字、类别、优先级或缺失的反引用重新出现。

最后，让证明术宏生成一个有效却会在当前目标上失败的证明术。解析器与宏都已成功，生成的证明术甚至可能已经开始改变证明状态。为了改试其他候选，证明术分派器会保存失败现场，再恢复这次分派开始前的状态；若最终没有候选成功，它会恢复选中的失败现场再抛出错误。只要可以，就在同一个目标上直接运行生成的证明术。这样便把实验移出宏，让证明术自身的错误消息指出失败的证明步骤。

四个实验留下了一条好用的路径：

:::codeBox "pseudocode"
```
text rejected
  → inspect the parser declaration
syntax accepted but no pattern owns it
  → inspect the macro pattern and node shape
expansion produced syntax that cannot elaborate
  → shrink and rebuild the generated template
generated tactic runs and fails
  → debug tactic execution and proof state
```
:::

`trace.Elab.step` 会显示嵌套的译补与展开事件。它并非宏专用。普通译补步骤会与 `Macro.trace` 记录的消息一起出现。要询问一个根节点能否展开并检查这一步的结果时，`Macro.expandMacro?` 更合适。面对递归宏，则在每次展开时记录输入或某个大小度量。若度量没有朝基例下降，那么在 `maxRecDepth` 确认循环之前，跟踪就已经找到它了。

源位置也会泄露失败所在的层。解析器错误指向调用文本；`Macro.throwErrorAt` 可以有意指向某个捕获参数；除非引用保留了有用的源引用，译补错误往往会指进生成的句法。`rw` 之类的生产宏之所以携带标点记号，部分原因就是要让编辑器反馈落在用户正在看的地方。操作 `Syntax` 而非字符串，还能换来更好的诊断。

# 练习
%%%
tag := "ch03-exercises"
file := "ch03-exercises"
%%%

1. 定义项宏 `twice(t)`，将它展开为 `t + t`。用一个含有局部变量的调用者表达式测试它，再通过命令或跟踪检查一次展开。哪些标识符来自模板，哪些通过反引用进入？

2. 定义一种逗号分隔的项形式，用重复反引用捕获其中各项，再把它展开成列表。加入第二种表层形式，接受以空格分隔的项；安排模式顺序，使列表字面量仍走进预期分支。

3. 调整 `poly_roots`，让它处理如下形式的假设：

   :::codeBox "pseudocode"
   ```
   example (x : ℚ) (h : x^2 - 5*x + 6 = 0) : x = 2 ∨ x = 3 := by
     ...
   ```
   :::

   让调用者显式写出假设名。根与变量仍作为句法参数；这个练习仍只操作句法，不读取目标。

4. 给 `poly_roots_both` 再加一种句法形式。编译之前，先写下哪些模式能够接收同一棵解析树，以及哪个分支必须放在其他分支之前。再故意加入一次完全相同的模式，观察冗余备选项错误。

5. 写一个卫生宏，引入 `let tmp := ...`，并在调用者已经有名为 `tmp` 的变量时使用它。再写一个宏，让它接收绑定符作为 `ident`，有意建立这层绑定关系。

6. 为同一句法种类分别注册三个项宏。让最新的一个用 `Macro.throwUnsupported` 拒绝，再检查出现的是哪个较旧结果。把拒绝换成 `Macro.throwErrorAt`，比较结果。用证明术宏重复这个实验：让最新候选项成功展开成一个失败的证明术，解释证明术分派器为什么仍可能抵达较旧的候选项。

7. 在形如 `∀ a b c : Nat, True` 的目标上跟踪 `iterate 3 intro`。记录每次生成的递归调用中的自然数，找出零分支，再关闭余下的 `True` 目标。接着构造一个输出不会变小的递归宏，确认递归深度错误发生在展开期间，而不是证明执行期间。

8. 从导入的 Lean 或 Mathlib 模块中读一个宏。回答完下面这些问题之后再给它分类：它匹配哪棵树，保留哪些源信息，生成什么，规则集能否扩展，又由后面的哪个阶段完成所有依赖目标的工作？

9. 判断下面每项需求应该使用宏还是译补器：
   - 为一组固定的证明术组合提供较短写法；
   - 检查当前目标最外层的联结词后选择展开；
   - 把两种表层形式转换成一种规范句法形式；
   - 在局部上下文中寻找类型定义相等的假设；
   - 生成一个声明，其公开名字由调用者提供。

   每个答案都要指出实现必须读取哪些信息。若调用的 `Syntax` 中没有这些信息，增加更多宏规则也不会把它召唤出来。

宏可以重写 `Syntax`，却不能根据当前证明目标选择展开。第 4 章会回到 `poly_roots` 留下的接口缺口：译补能够读取那份状态。
