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


# `MacroM` 还能看到什么
%%%
tag := "macro-context"
%%%

普通 tactic 宏看不到目标，并不等于 `MacroM` 里面什么都没有。Command 宏运行在文件中某个确定的位置，它至少得知道当前位置属于哪个命名空间；输入里若有一个名字，宏展开器也可以借用几项受限的解析功能。下面这个命令把名字解析成全名，再生成普通的 `#check`：

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

这里先停一下：

:::codeBox "code"
```
let ns ← Macro.getCurrNamespace
```
:::

`Macro.getCurrNamespace` 的返回类型不是 `Name`，而是 `MacroM Name`。`Name` 表示已经拿到手的名字；`MacroM Name` 则是一段尚待运行的宏展开计算。一般的 `MacroM` 计算可以读取现场、留下新的宏状态或失败；眼前这一项只读取当前 namespace，成功后返回一个 `Name`。`←` 运行右边的计算，再把得到的普通值交给后面的代码。

## 插曲：这个 `M` 不是名字末尾的装饰
%%%
tag := "macro-monad-interlude"
%%%

如果你没学过函数式编程，先不要把 Monad 想成某种高深的数据结构。眼前这几行代码已经足够逼出它最小的形状。

普通函数拿到参数便能算出结果，例如 `Nat.succ 3` 的结果是 `4`。`Macro.getCurrNamespace` 却不能凭空算出命名空间；同一段宏放在两个 namespace 里，结果会变。`Macro.throwErrorAt` 更不会返回正常结果，它会让当前展开当场失败。这里需要描述的不是一个孤零零的值，而是“一段要在特定现场运行、运行中还可能失败的计算”。类型 `MacroM α` 中的 `M` 说明这段计算运行在怎样的世界里，`α` 才是成功后真正得到的值。

把这样的计算接起来只需要两个动作。`pure` 把普通值放回当前计算世界，却不额外读取或修改现场；`bind` 先运行一段 `M α`，再把得到的 `α` 交给下一段 `α → M β`。`do` 记法把一串 `bind` 按执行顺序排开，所以：

:::codeBox "code"
```
do
  let ns ← Macro.getCurrNamespace
  let candidates ← Macro.resolveGlobalName name.getId
  pure (ns, candidates)
```
:::

读起来就是“先取 namespace，再查询候选，最后返回二者”。第二步可以依赖第一步，任何一步抛错都会阻止后续代码继续。对于眼前的宏，这已经是 Monad 最重要的用法。只想继续写宏，可以直接跳到下一节。

### 深水区，可跳：`MacroM` 怎样叠出来

Lean 4.32.2 对 `MacroM` 的真实定义是：

:::codeBox "code"
```
abbrev MacroM :=
  ReaderT Macro.Context
    (EStateM Macro.Exception Macro.State)
```
:::

`ReaderT Macro.Context` 给计算增加一份只读现场；`EStateM Macro.Exception Macro.State` 带着可变化的宏状态运行，也允许以 `Macro.Exception` 失败。当前卫生作用域放在 Context；State 保存 fresh scope 计数器、trace 和已展开宏声明等可变信息；Exception 则区分“这条规则不处理”与真正的错误。

这里真正的 Monad transformer 是外层 `ReaderT`；内层 `EStateM` 本身把状态与异常合成一个基础计算。Transformer 不是给一个值反复套盒子，而是在已有 Monad 外再加一层现场或状态，同时保留 `pure`、`bind` 和 `do` 的连接方式。以后几章会看到 `ReaderT` 与 `StateRefT` 继续向外叠加：

:::codeBox "code"
```
CoreM     := ReaderT Core.Context
               (StateRefT Core.State (EIO Exception))
MetaM     := ReaderT Meta.Context
               (StateRefT Meta.State CoreM)
TermElabM := ReaderT Term.Context
               (StateRefT Term.State MetaM)
TacticM   := ReaderT Tactic.Context
               (StateRefT Tactic.State TermElabM)
```
:::

现在不需要记住这些 Context 和 State 的字段。先记住读法：每向外加一层 transformer，就增加当前阶段专用的一份现场或状态；底层已有的能力仍然可以继续使用。只想写宏的读者读到这里已经够了，Ch05 至 Ch08 会逐层拆开。

`MacroM` 的边界还有一点容易说错。它没有通用的 `getEnv`，也没有 IO；宏不能取得整个 `Environment` 随意查询。但宏展开框架通过不透明的 `Macro.Methods` 开放了几项窄接口，所以 `hasDecl` 和 `resolveGlobalName` 仍然可用。框架只肯替宏回答几类事先规定好的问题。

## 用过以后再查 API

刚才的例子已经给这些 API 建立了共同语法，现在可以把常用入口放在一起备查：

```table
|| API || 返回值 || 当前能做的事
| `Syntax.getKind stx` | `SyntaxNodeKind` | 查看节点由哪种句法产生
| `Syntax.getArgs stx` | `Array Syntax` | 取得直接子节点
| `Syntax.getId stx` | `Name` | 取得标识符携带的名字
| `Syntax.getPos? stx` | `Option String.Pos.Raw` | 取得源码起始位置
| `Macro.getCurrNamespace` | `MacroM Name` | 读取当前 namespace
| `Macro.hasDecl n` | `MacroM Bool` | 询问一个全名是否对应声明
| `Macro.resolveGlobalName n` | `MacroM (List (Name × List String))` | 解析全局名字及投影后缀
| `Macro.expandMacro? stx` | `MacroM (Option Syntax)` | 尝试把最外层宏再展开一步
| `Macro.trace cls msg` | `MacroM Unit` | 把自定义消息写入指定 trace class
| `Macro.throwUnsupported` | `MacroM α` | 把输入交给别的宏候选
| `Macro.throwErrorAt ref msg` | `MacroM α` | 在指定 Syntax 位置报告错误
```

前四项直接检查 Syntax；后面的操作要运行在 `MacroM` 中。`Syntax.getId` 本身不会替你验证节点类别，非标识符会得到 `Name.anonymous`；若匿名名不合法，应先检查 `stx.isIdent`。这些 API 仍然不能取得当前证明目标、局部上下文或一个表达式的类型。`#resolve_decl` 能确认名字存在，却不能取出声明类型；真正的 `#check` 是宏生成的下一条命令，类型查询发生在命令译补阶段。

# 两条规则都能匹配时
%%%
tag := "macro-rules-order"
%%%

`poly_roots_both` 已经让我们碰到一种重叠：`$roots:term*` 也能把整个列表当成一个 term 接住，所以更具体的 `[$roots,*]` 必须写在前面。同一个 `macro_rules` 块按书写顺序检查分支；两个完全相同的模式还会被 redundant linter 拒绝，不能在同一块里靠第一条 `throwUnsupported` 假装回退。

分开注册的规则又是另一层顺序：

```anchor macro_first_rule
open Lean Macro

syntax:max "firstRule" : term

macro_rules
  | `(firstRule) => `(41 + 1)

macro_rules
  | `(firstRule) => Macro.throwUnsupported

example : firstRule = 42 := rfl
```

后注册的规则先拿到输入，但它调用 `throwUnsupported`，意思是“这个 expander 不处理”，框架于是继续找较早注册的候选。上例是 term 宏；在普通 term 或 command 的展开循环里，`Macro.throwError` 表示当前规则已经认领输入，错误会直接交给用户，不会因为生成结果后来译补失败而回到较早的宏。

Tactic 宏多一层回退。它的分派器把“展开候选并运行生成的 tactic”一起放在可恢复现场中；某个候选抛普通错误或生成的 tactic 执行失败时，状态可以恢复，随后继续试别的 tactic expander：

```anchor macro_tactic_fallback
syntax "fallbackTac" : tactic

macro_rules
  | `(tactic| fallbackTac) => `(tactic| assumption)

macro_rules
  | `(tactic| fallbackTac) => `(tactic| exact True.intro)

example (P : Prop) (h : P) : P := by
  fallbackTac
```

后注册的 `exact True.intro` 先运行，却不能证明任意 `P`；分派器恢复现场后，较早注册的 `assumption` 才用 `h` 关闭目标。真实 `trivial` 也依赖这条恢复路径，不过它的候选按注册顺序反向尝试：最后写下的递归合取分支最先拿到目标，`assumption` 反而最后。`throwError` 在 term/command 宏中可以提交错误，却不能被概括成“在所有 tactic 宏中永久截断候选链”。

顺序真正重要时，最可靠的实验很直接：给每条规则各找一个只有它能匹配的输入，再找一个重叠输入，看谁先接住；最后补一个谁都不该处理的输入。Term/command 宏不要把普通错误冒充 unsupported；tactic 候选若故意依赖执行失败回退，还要用回归测试确认状态确实恢复。

# 展开以后还有宏
%%%
tag := "macro-recursive-expansion"
%%%

前面写 `mytrivial` 时，合取分支展开成：

:::codeBox "code"
```
apply And.intro <;> mytrivial
```
:::

展开结果里仍然有 `mytrivial`，证明却能继续。宏输出不是最后的 Expr，而是另一棵 Syntax；译补器处理相应节点时若仍能找到宏，就会继续展开，直到得到下一阶段能够处理的形态。Lean 不是先把整份文件拿去做一次全树 fixed-point 预处理，展开跟着当前节点向下走。

这个机制允许高层宏调用低层宏，也允许宏递归。它也允许你写出：

:::codeBox "error code"
```
macro "loop" : term => `(loop)
```
:::

输入和输出完全相同，每轮以后仍然还有下一轮。Lean 最终会以递归深度一类错误停下，但提高限制没有用；规则没有朝终态前进，再高的限制也只是让它多绕几圈。

递归宏最好让下降量直接出现在模式里。处理列表时给空列表一个基例，递归分支每次去掉一个元素；处理自然数时让后继变成更小的数。Lean 的 `iterate n tac` 就按这个办法展开，零次变成 `skip`，后继次数变成一次 `tac` 和更小的 `iterate`。不写次数的版本则把停止条件交给 tactic 失败。

```anchor macro_builtin_recursion
example (n : Nat) (h : n > 0) : n - 1 < n := by
  decreasing_trivial

example (n : Nat) : n = n := by
  iterate 1 rfl
```

`decreasing_trivial`、`get_elem_tactic_extensible` 和若干 discharger 会把同一种 Syntax 留给别的模块继续注册规则。它们没有一段脱离导入环境的“唯一展开结果”；当前能尝试哪些候选，取决于导入闭包注册了什么。

# 两个 `x` 为什么没有撞在一起
%%%
tag := "macro-hygiene"
%%%

下面这个宏在模板里新写了一个 `x`：

```anchor macro_hygienic_let
macro "hygienicLet(" t:term ")" : term =>
  `(let x := $t; x)

example (x : Nat) : hygienicLet(x + 1) = x + 1 := rfl
```

只看展开后的字符，它很像：

:::codeBox "code"
```
let x := x + 1; x
```
:::

如果宏只是字符串替换，右边 `x + 1` 中原本属于调用者的 `x` 会被新 binder 抓走。Lean 的 quotation 不会抹掉名字来源。模板中新写的 binder 和 body 中的 `x` 获得当前宏作用域，所以它们彼此对应；反引用进来的 `$t` 保留调用点作用域，其中的 `x` 仍然指向外面的参数。

卫生性阻止意外捕获，不阻止明确的名字关联。调用者若把 binder 名传给宏，模板可以反引用同一个 ident：

```anchor macro_identity_let
macro "identityLet(" n:ident ", " t:term ")" : term =>
  `(let $n := $t; $n)

example : identityLet(y, 7) = 7 := rfl
```

同一原则也约束宏生成的顶层名字。需要形成公开接口时，让调用者显式提供 ident，比试图绕过卫生性可靠得多。

# 现在去读真正的宏
%%%
tag := "macro-real-source"
%%%

宏的输入、展开、候选、递归和名字来源都已经有了。现在回到 Lean 与 Mathlib 的源码，只看前文原则组合以后仍然承重的地方。

## `rw` 与 `rwa`
%%%
tag := "macro-rw"
%%%

Ch02 已经拆过 `rwRuleSeq` 的 parser，所以这里不再解释可选箭头和逗号列表。现在只看它们怎样被宏接走：

```anchor syntax_source_rw (module := Examples.SyntaxSources)
macro (name := rwSeq) "rw " c:optConfig s:rwRuleSeq l:(location)? : tactic =>
  match s with
  | `(rwRuleSeq| [$rs,*]%$rbrak) =>
    `(tactic| (rewrite $c [$rs,*] $(l)?; with_annotate_state $rbrak (try (with_reducible rfl))))
  | _ => Macro.throwUnsupported

macro "rwa " rws:rwRuleSeq loc:(location)? : tactic =>
  `(tactic| (rw $rws:rwRuleSeq $[$loc:location]?; assumption))
```

`$rs,*` 取出已经解析好的重写规则，`%$rbrak` 另外保留右方括号这个原子，`with_annotate_state` 因而能把编辑器状态挂回用户看得见的位置。`rw` 先交给真正读取目标的 `rewrite`，然后尝试 `rfl`；`rwa` 又在 `rw` 后面接上 `assumption`。宏负责排脚本，证明语义仍由后面的 tactic 处理。

## 控制器和真实的 `trivial`

`try` 展开成 `first | t | skip`，`<;>` 把右边 tactic 发给左边产生的每个目标。源码只负责把控制结构排出来：

:::codeBox "code"
```
macro "try " t:tacticSeq : tactic => `(tactic| first | $t | skip)

macro:1 x:tactic tk:" <;> " y:tactic:2 : tactic => `(tactic|
  focus
    $x:tactic
    with_annotate_state $tk skip
    all_goals $y:tactic)
```
:::

真正值得确认的是，失败、目标队列和回滚都由展开后的 tactic 处理。

```anchor macro_controller_examples
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor <;> assumption

example : (1 : Int) + 2 = 3 := by
  ring
```

真实 `trivial` 和前面写过的 `mytrivial` 几乎走同一条路。`Init/Tactics.lean` 按下面的源码顺序注册六条规则：

:::codeBox "code"
```
macro_rules | `(tactic| trivial) => `(tactic| assumption)
macro_rules | `(tactic| trivial) => `(tactic| rfl)
macro_rules | `(tactic| trivial) => `(tactic| contradiction)
macro_rules | `(tactic| trivial) => `(tactic| decide)
macro_rules | `(tactic| trivial) => `(tactic| apply True.intro)
macro_rules | `(tactic| trivial) => `(tactic| apply And.intro <;> trivial)
```
:::

这些规则都注册在同一个 Syntax kind 下；注册表让后注册的候选先试，所以运行时从递归合取分支向上回退，最后才到 `assumption`。这里没有另一个“宏候选优先级”字段；`macro (priority := ...)` 调整的是新建 syntax parser 的优先级，不是这条候选链。你已经亲手写过这些规则需要的回退、递归和 `<;>`，所以不必再把六个分支逐项讲一遍。

```anchor macro_trivial_use
example (P : Prop) (h : P) : P := by
  trivial

example : True ∧ True := by
  trivial
```

领域宏有时只把固定配置或 rule set 交给通用引擎：

```anchor macro_external_examples
example : Continuous (fun x : Real => x) := by
  continuity

example : Measurable (fun x : Real => x) := by
  measurability
```

这些例子看完以后，生产宏的常见工作才值得压成一张表：

```table
|| 工作 || 例子 || 宏真正做的事
| 给已有功能一个短入口 | `exfalso`、`infer_instance` | 生成更底层的 term 或 tactic
| 编排控制流 | `try`、`<;>`、`ring` | 安排候选、重复和收尾
| 留出开放规则槽 | `trivial`、`decreasing_trivial` | 让同一 Syntax kind 接受多个候选
| 固定领域配置 | `continuity`、`measurability` | 把 rule set 交给通用处理器
```

完整名字清单会随版本和导入闭包变化，适合放进 API 附录，不适合挤进这条学习路线。

# 宏出错时，先看它死在哪一层
%%%
tag := "macro-debugging"
%%%

一个“宏不能用”至少可能指四件不同的事。输入若连 parser 都没接住，错误发生在 Syntax 产生之前；输入能够解析但没有宏模式匹配，框架会继续找候选，最后报告 unsupported syntax；宏若成功生成新 Syntax，新代码仍可能在译补时类型错误；tactic 即使完成译补，也可能运行后留下目标。

这四层的修法不同。Parser 错误先缩小输入并确认类别和优先级；pattern 错误检查 quotation 类别、重复项和可选项；生成代码的错误去看展开结果；执行失败则回到目标状态和真正运行的 tactic。

`trace.Elab.step` 可以显示译补过程中经过的展开步骤；宏内部也能用 `Macro.trace` 把自己的消息写进同一个 trace class：

```anchor macro_trace_use
syntax:max "twiceTrace(" term ")" : term
macro_rules
  | `(twiceTrace($t)) => do
      Macro.trace `Elab.step "expanding twiceTrace"
      `($t + $t)

set_option trace.Elab.step true in
#check twiceTrace(2)
```

若只想检查最外层的一步，可在 `MacroM` 中调用 `Macro.expandMacro?`。它返回 `none` 表示当前节点没有可用宏，返回 `some stx` 才是一步展开结果。调试复杂模板时，与其先打印整棵树，不如暂时把输出缩成一个肯定能译补的常量，再逐块放回；哪一块放回以后开始失败，缺口就在那一层。

递归宏还要额外记录每轮输入是否真的变小。看到递归深度错误时提高 `maxRecDepth`，通常只是给死循环续命。

# 本章练习

1. 写一个 term 宏，把 `twice t` 展开成 `t + t`，再说明模板中重复出现 `$t` 会不会让一个 effectful term 在运行期执行两次。
2. 写一个 command 宏，接受逗号分隔的多个名字，为每个名字生成一个 `#check`。
3. 给 `poly_roots_both` 增加第三种表面写法，并设计唯一命中、重叠和完全不命中的测试。
4. 修改 `hygienicLet`，让调用者显式给出 binder 名；再解释为什么这不算卫生性失效。
5. 写两个独立注册的同 kind 宏规则，让后注册规则先 `throwUnsupported`，再把它改成 `throwError`，比较错误路径。
6. 判断下面需求该由宏还是证明术译补器完成：调用形式固定为 `by solve_here`，但展开结果要依据当前目标和局部假设而变。说明你的判断依赖哪一项输入信息。

宏到这里已经完成自己的工作：它能检查和重建 Syntax，也能借用一小块宏展开现场，却不能从不存在于输入里的证明目标选择行为。下一章不让读者等到四层 Monad 全部讲完；我们先把 `poly_roots` 留下的缺口补上，直接写能够读取目标的证明术译补器。
