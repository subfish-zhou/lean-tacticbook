import VersoManual
import LeanTacticBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "examples"
set_option verso.exampleModule "Examples.Ch02Syntax"

#doc (Manual) "句法" =>
%%%
file := "Ch02Syntax"
tag := "ch02-syntax"
%%%

# 句法声明
%%%
tag := "syntax-declaration"
%%%

声明句法是非常简单的：

```anchor syntax_declaration
syntax "MyTerm" : term

#check_failure MyTerm
```

我们声明了一个新的项 `MyTerm`。要注意的是，这个项当前没有任何的语义，它是一个完全的文字空壳，到了宏和译补的章节我们才能够给它赋予语义。这使得{kw}`#check_failure`会报告：

:::codeBox "error code"
```
-- `termMyTerm` 的译补函数还未实现
elaboration function for `termMyTerm` has not been implemented
  MyTerm
```
:::

`term`是这个句法的类别（category）。你所熟知的 Lean 的类型论当中的项都可以作为句法项。我们还可以定义其它类别的句法，例如证明术`tactic`和命令`command`，只需要把 {anchorTerm syntax_declaration}`term` 改成相应的类别即可。Lean 还支持其它的一些类别，之后遇到的时候我们再讲。我们甚至可以用{kw}`declare_syntax_cat`来声明一个新的句法类别。

句法也可以带参数，比如说常用的`exact`证明术被定义为：

```anchor syntax_parameter
syntax (name := myexact) "myexact " term : tactic
```

{anchorTerm syntax_parameter}`(name := myexact)`是该条句法的名字，事后定义该句法的语义时顺着名字可以找到它。如果省略`(name := ...)`，Lean会根据句法类别和声明中的固定原子自动生成一个名字，并在发生重名时追加编号。例如前面的`syntax "MyTerm" : term`没有显式命名，Lean为它生成了`termMyTerm`；这正是报错信息中出现的名字。自动命名适合简单声明，但如果之后要为该句法编写宏、译补器或直接检查节点种类，显式命名会更稳定、更清楚。`term`则表示这里可以放一个项。注意`"myexact "`留了一个空格，这是为了让雅印器在 InfoView 里面显示这个证明术的时候留一个空格，显得更雅。

有时候我们可能想定义不只包含一个关键词的语法，比如一个像是`‖x‖`表示向量模长的运算符：

```anchor syntax_norm
syntax "‖" term "‖" : term
```

或者我们想定义一个有多个参数的句法，比如一个像是`10 ≡ 1 [mod 3]`表示同余的运算符：

```anchor syntax_congruence
syntax term " ≡ " term " [mod " term "]" : term
```

# 运算符的简便声明
%%%
tag := "syntax-notation"
%%%

你使用 Lean 的过程中很可能已经见过，其实可以用{kw}`notation`关键字来直接定义一些简单的运算符的句法加语义。例如我可以定义一个异或运算符：

```anchor syntax_xor
notation:10 l:10 " XOR " r:11 => (!l && r) || (l && !r)
```

* {kw}`=>` 左边就是句法，右边就是语义。{anchorTerm syntax_xor}`l` 和 {anchorTerm syntax_xor}`r` 是运算符的两个参数，它们自动属于 `term` 类别。
* 既然我们定义的是中缀运算符就要涉及优先级。{anchorTerm syntax_xor}`notation:10` 中的 {anchorTerm syntax_xor}`10` 是整个表达式的优先级；{anchorTerm syntax_xor}`l:10` 和 {anchorTerm syntax_xor}`r:11` 中的数字是左右参数的优先级。此处它是左结合的。这里机制比较复杂，等会儿我们单开一节来讲。

上一节末尾定义的模长运算符在Mathlib里面实际上就是这样定义的：

```anchor syntax_norm_notation
class MyNorm (E : Type*) where
  norm : E → ℝ

notation "‖" e "‖" => MyNorm.norm e
```

而同余运算符在Mathlib里面实际上就是这样定义的：
```anchor syntax_mod
def MyNat.ModEq (n a b : ℕ) :=
  a % n = b % n

notation:50 a " ≡ " b " [MOD " n "]" =>
  MyNat.ModEq n a b
```

## 前缀、后缀与中缀运算符
%%%
tag := "syntax-mixfix"
%%%

对于常见的一元、二元运算符，Lean提供了五个比{kw}`notation`更直接的声明命令：

```anchor syntax_mixfix
prefix:75 "NEG " => fun n : Int => -n  -- 前缀一元运算符
postfix:max "²" => fun n : Nat => n ^ 2  -- 后缀一元运算符
infix:50 " EVENMOD " => fun a b : Nat => a % 2 = b % 2  -- 不可结合中缀二元运算符
infixl:65 " -ₗ " => fun a b : Int => a - b  -- 左结合中缀二元运算符
infixr:65 " -ᵣ " => fun a b : Int => a - b  -- 右结合中缀二元运算符

#eval NEG 3               -- -3
#eval 5²                  -- 25
example : 5 EVENMOD 3 := by decide
#eval (10 : Int) -ₗ 3 -ₗ 2 -- 5，即 (10 -ₗ 3) -ₗ 2
#eval (10 : Int) -ᵣ 3 -ᵣ 2 -- 9，即 10 -ᵣ (3 -ᵣ 2)
```

它们的共同形式是`命令:优先级 "运算符" => 函数`。Lean会自动补出参数，并把运算符应用翻译成右侧函数的应用。

## 优先级规则
%%%
tag := "syntax-precedence"
%%%

优先级是解析器*决定表达式如何分组*的规则。这种规则实际上是靠“约束”来实现的。有两条基础约束：
1. 每个项都有级别，参数优先级的值规定该项_至少_要达到的级别
2. 在当前解析位置，Lean 总是试图获得能成功匹配的最长结果
这听上去很抽象，下面用减法来演示不同优先级设置的效果：

```anchor syntax_precedence
notation:10 l:10 " SUBL " r:11 => l - r
notation:10 l:11 " SUBR " r:10 => l - r
notation:10 l:10 " SUBR₂ " r:10 => l - r
notation:10 l:11 " SUBX " r:11 => l - r

#eval 10 SUBL 3 SUBL 2 -- 5，即 (10 SUBL 3) SUBL 2
#eval 10 SUBR 3 SUBR 2 -- 9，即 10 SUBR (3 SUBR 2)
#eval 10 SUBR₂ 3 SUBR₂ 2 -- 9，依然是右结合的
#eval 10 SUBX (3 SUBX 2) -- 9，SUBX 不允许连续使用，必须带括号
```

`SUBL` 的优先级读法是，这个表达式整体的优先级为10，左参数_至少_为10，右参数至少为11。`10 SUBL 3 SUBL 2`的解析规则只能是`(10 SUBL 3):10 SUBL 2`，反过来`10 SUBL (3 SUBL 2):10`会因为右参数不满足“至少为11”而失败。{kw}`infixl` 正是这种机制。你可以自己思考一下`SUBR`为什么是右结合的。相应地它对应着{kw}`infixr`。

`SUBR₂`是右结合的理由则需要结合第二项约束。详细的原理我会放到解析器一章单独来讲。作为经验准则，可以把解析过程理解为先左后右的解析尝试：读到第一个 `SUBR₂` 时，它左边的 `10` 已经通过约束（原因看下一段）被允许成为了左参数，接下来才读取右参数。但是并不是读到了下一个数字解析器就会立即解析右参数！它还会继续往下读，在优先级约束允许的范围内尽量向右延伸。对于 `10 SUBR₂ 3 SUBR₂ 2`，右参数不只读到 `3`，它可以继续读成 `3 SUBR₂ 2`，发现后者的优先级仍为10，满足 `term:10` 的约束，而且匹配得更长，因此第一个算符的右参数取 `3 SUBR₂ 2`，整句解析成 `10 SUBR₂ (3 SUBR₂ 2)`，表现为右结合。

`SUBX`的优先级设置是左右参数都至少为11，而整体优先级为10。此时`10 SUBX 3 SUBX 2`的解析尝试会失败，因为第一个算符的右参数`3 SUBX 2`不满足“至少为11”的约束。你必须写成`10 SUBX (3 SUBX 2)`才能成功。

`max` 表示最高优先级，而实际上它被设定为1024。也就是说，我可以写`macro:max ...`等价于写`macro:1024 ...`。标识符和括号的优先级实际上就被设为`max`。（这实际上解释了`10 SUBL 3`自己是如何解析的，因为`10`和`3`的优先级是1024，满足“至少10或11”的参数优先级约束）`arg` 表示函数应用这个操作的优先级，它被设为1023。如果你不写宏的优先级，此时会使用默认值1022，而如果你不写参数的优先级，此时会使用默认值0。也就是说

```anchor syntax_default_precedence
notation l " SUB₁ " r => l - r
-- 等价于
notation:1022 l:0 " SUB₂ " r:0 => l - r
```

# 更复杂的句法
%%%
tag := "syntax-complex"
%%%

## 句法缩写
%%%
tag := "syntax-abbreviation"
%%%

定义复杂的语法的时候我们会希望给一些常见的模式起一个名字。Lean称其为`syntaxAbbrev`，它用`syntax ... := ...`来声明，和普通的定义很像：

```anchor syntax_abbrev
syntax simpPre  := "↓"
syntax simpPost := "↑"
syntax simpStar := "*"
```

以上都是`simp`证明术中的真实定义。这样一来我们就可以用这些名字来指称这些对象了。

## 可有可无的部分
%%%
tag := "syntax-optional"
%%%

可以用`?`标记灵活的可有可无的部分。下面是 Mathlib 中`lift`证明术的定义：

```anchor syntax_lift
syntax (name := MyLift)
  "my_lift " term
  " to " term
  (" using " term)?
  (" with " ident (ppSpace colGt ident)? (ppSpace colGt ident)?)? : tactic
```

用起来可能会像这样：

:::codeBox "pseudocode"
```
my_lift n + 3 to ℕ using hn with k hk
```
:::

详细解释一下：
1. `( ... )?`表示括号内的内容是可有可无的，可以出现零次或一次。此处`" using " term`和`" with " ident ...`以及里面的第二和第三个参数都是可有可无的。
2. `with`中参数的类型`ident`也是句法类型，称为标识符。它的范围要比`term`小，只接受名字，例如`x`，`h₁`，`Nat.add`，而`1`、`x + 1`等等就不行。
3. `ppSpace`是雅印器的控制符，表示在雅印时输出一个空格，或者在行太长时进行软换行。详表见[雅印器控制符](#syntax-pretty-printer-controllers)。
4. `colGt`是解析器的控制符，在解析时要求后续的标识符缩进比前一个标识符更深。在这里，意思是如果你在填写第二个或第三个标识符时换行的话，必须比前一个标识符有更多的缩进，否则无法被解析成参数。详表见[解析器位置控制符](#syntax-parser-position-controllers)。

## 在几种写法中选择
%%%
tag := "syntax-alternative"
%%%

`p <|> q`表示匹配`p`或`q`中的一种。在`rw`等证明术中允许从右往左地使用等价关系，只需要在你想用的定理前加一个`←`或者`<-`。我们很想给两种不同的箭头写法起个统一的名字：

```anchor syntax_alternative
syntax larrow := "←" <|> "<-"
```

另一个重要的例子是`binderIdent`，它是绑定位置所用的可复用句法解析器：

```anchor syntax_binderident
syntax binderIdent := ident <|> hole
```

具体来说，`ident`匹配一个名字，而`hole`实际上是句法中下划线`_`的类型。因此函数参数既可以命名为`x`，也可以写成`_`表示不为它命名。Lean在许多绑定位置都会用到`binderIdent`，我们以后会经常见到它。

## 重复
%%%
tag := "syntax-repetition"
%%%

`p,*`表示零个或多个用逗号分隔的`p`，比如回忆一下{kw}`rw`证明术的用法`rw [p1, p2, ...]`，我们可以如此声明句法：

```anchor syntax_repetition
syntax "my_rw" " [" term,* "]" : term
```

注意到我们把`"my_rw" " ["`拆成了两个字符串。在{kw}`syntax`声明中，每个字符串只能表示一个句法原子，不能合写成包含内部空白的`"my_rw ["`。字符串首尾的空白只用于指示雅印器排版，不是被匹配的源码字符。

同一族写法中，`p*`表示连续匹配零个或多个`p`，其间没有专门的分隔符，并不能简单理解成“用空格分隔”。例如当`p`是`ident`时，`ident*`可以把`p1 p2 p3`匹配成三个标识符，`p1, p2, p3`则不能匹配。`term*`解析`(p1)p2`得到的则是`(p1)`和`p2`两个项，但解析`p1 p2`时得到的甚至是`p1`函数应用在`p2`上的一个项，因为解析器只判断句法结构，不判断语义类型。因此使用它时要小心。很聪明的用法来自 `intro` 证明术的完整句法声明：

```anchor syntax_source_intro (module := Examples.SyntaxSources)
syntax (name := intro) "intro" notFollowedBy("|") (ppSpace colGt term:max)* : tactic
```

这里每一项都必须达到最高优先级`max`，而函数应用的优先级`arg`比它低，所以`p1 p2`不能再被读成一个函数应用项，而会成为两个项。`notFollowedBy(p)`也可以写作`!p`，此处要求接下来的文本禁止以`|`开头。

`p+`和`p,+`代表一次或多次。 `cases`的主声明如下：

```anchor syntax_source_cases (module := Examples.SyntaxSources)
syntax (name := cases) "cases " elimTarget,+ (" using " term)? (inductionAlts)? : tactic
```

其中句法缩写`elimTarget`既允许普通项，也允许`h : e`形式的带名目标；`inductionAlts`描述可选的`with`分支。主声明中的`elimTarget,+`要求至少一个目标，由逗号分隔。

对句法缩写也可以使用重复，比如说如果我们想升级一下前一个`my_rw`，解析可带可不带左箭头的项：

```anchor syntax_reuse
syntax rwTerm := (larrow)? term
syntax "my_rw2" " [" rwTerm,* "]" : tactic
```

`rwTerm`由一个可选的反向箭头和一个必需的`term`组成。这里必须写成`(larrow)?`；若写成`larrow?`，问号会被当作标识符的一部分，Lean便会尝试寻找名为`larrow?`的解析器。

# `Syntax`类型和解析器
%%%
tag := "syntax-type-parser"
%%%

以上的介绍像是在陈列句法声明工具箱，接下来我们要操作句法本身。如果你只想学如何声明句法，那么你完全可以跳到下一节。更多的理论总是有用的！作为一种动机演示，也同样作为学习本节的奖励，最终成果将会是一个“判断给定字符串是否符合某个句法解析器”的函数。上一章的函数、构造子和容器读法已经足够支撑下面的代码。

上一章已经练习过从构造子声明的结果类型往回读。用同样的方法看，`Syntax`也是一个归纳类型：

```anchor syntax_type_definition
inductive Syntax where
  | missing : Syntax
  | node   (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) : Syntax
  | atom   (info : SourceInfo) (val : String) : Syntax
  | ident  (info : SourceInfo) (rawVal : Substring.Raw) (val : Name)
      (preresolved : List Syntax.Preresolved) : Syntax
```

详细解释：

- {anchorTerm syntax_type_definition}`SourceInfo`主要是给解析器提供源信息。一个重要的应用是它可以用来实现鼠标悬停时的信息演示。它比较复杂，我们先跳过。
- {anchorTerm syntax_type_definition}`missing`就是一个在解析错误时的占位符，一般不必关心。
- {anchorTerm syntax_type_definition}`node`就是句法树节点。{anchorTerm syntax_type_definition}`kind : SyntaxNodeKind`其实就是名字，实际上`abbrev SyntaxNodeKind := Lean.Name`。{anchorTerm syntax_type_definition}`args : Array Syntax`保存这个节点的直接子节点；元素类型说明每一项仍是`Syntax`，Array则方便后续代码读取`size`或按索引取得某个子节点。
- {anchorTerm syntax_type_definition}`atom`表示字符串句法原子。
- {anchorTerm syntax_type_definition}`Substring.Raw`是“带起始位置的字符串切片”数据结构，经常在解析器里使用。`Raw`表示这个切片没被证明不越界。
- {anchorTerm syntax_type_definition}`ident`专门表示标识符。注意这个构造子和前面`ident`句法类别虽有联系但并不相同。`rawVal`保存你输入的原始文本，`val`保存、规范化并进行卫生宏处理后的名字；`preresolved`则保存预解析出的候选命名空间、全局声明或节变量，供卫生宏处理名字绑定。

例如，直接手工搭出一棵表示`myexact h`的句法树：

```anchor syntax_manual_construction
def myexactSyntax : Syntax :=
  Syntax.node SourceInfo.none `myexact #[
    Syntax.atom SourceInfo.none "myexact",
    Syntax.ident SourceInfo.none "h".toRawSubstring `h []
  ]

#eval myexactSyntax.getKind == `myexact -- true
```

先解释一下反引号`` ` ``记号，它标识一个`Name`。还可以使用双反引号``` `` ```记号标识已定义的名字，它会解析当前环境中的声明来检查是否存在这个名字。

根节点的{anchorTerm syntax_type_definition}`kind`是`` `myexact``，其子节点按源码顺序包含字符串`"myexact"`和标识符`h`。{anchorTerm syntax_manual_construction}`"h".toRawSubstring`提供标识符的原始文字，紧随其后的名称字面量则是解析后的`Name`；这里没有命名空间之类的东西，所以最后一个参数是空列表。因为这棵树不是从源码解析而来，三个节点都使用`SourceInfo.none`。

实际编写元程序时通常不必直接调用这些构造子，可以使用`mkIdent`、`mkApp`等等[构造语法的辅助函数](https://www.leanprover.cn/reference-manual/latest/Notations-and-Macros/Defining-New-Syntax/#syntax-construction-helpers)，本书中用不到，读者可以自行查阅手册。

解析器实际上就是在把Lean文件中的字符串转换成`Syntax`对象。实际上，我们用`syntax`关键字声明句法时声明的其实是解析规则，解析器拿这些规则去构造句法对象。而声明句法时声明的`term`、`tactic`、`command`等等_句法类别_（syntax category）实际上是“解析规则注册表”，它们本身是`Parser.Category`类型的项，我们声明这个类别的句法就是向这个表里注册规则。当然在我们之前Lean自己已经给这些类别注册了很多基础句法规则，例如使得字符串或者数字都可以属于`term`。`ident`有所不同，`Lean.Parser.ident`是一个固定的解析器，一次读取一个非保留标识符，并直接产生`Syntax.ident`，它不是一张可由`syntax ... : ident`扩展的`ParserCategory`表。

理解了这些，下面我们稍微借一点Lean的内部API和译补器的能力，来实现一个小工具：判断给定字符串是否符合某个句法解析器。我们希望实现命令`#matches_syntax`，给它一个句法类别、一条句法规则和一个字符串，它只回答`true`或`false`，表示整个字符串是否在该类别中符合这条规则。例如，前文声明的`myexact`属于`tactic`类别，要求关键字后必须有一个`term`，我们希望得到类似下面的命令：

:::codeBox "code"
```
#matches_syntax tactic myexact "myexact True.intro" -- true
#matches_syntax tactic myexact "myexact"            -- false
```
:::

完整实现如下：

```anchor parser_matches_syntax
def matchesSyntax (env : Environment) (categoryName : Name)
    (kind : SyntaxNodeKind) (input : String) : Bool :=
  match Parser.runParserCategory env categoryName input with
  | .ok stx => stx.getKind == kind
  | .error _ => false

elab "#matches_syntax " category:ident kind:ident input:str : command => do
  let env ← getEnv
  let category := category.getId
  let kind ← resolveGlobalConstNoOverload kind
  let input := input.getString
  logInfo m!"{matchesSyntax env category kind input}"

#matches_syntax tactic myexact "myexact True.intro" -- true
#matches_syntax tactic myexact "myexact"            -- false
#matches_syntax tactic myexact "exact True.intro"   -- false
```

先看函数定义。环境`env`储存了类别解析规则表和记号（token）表，记号指的是，假如说你定义了一个`syntax "something" : term`，那么`"something"`就被注册为一个记号。`Parser.runParserCategory env categoryName input`在当前环境`env`下运行指定类别`categoryName`的解析器来解析`input`。这个函数有两种可能的返回值：解析成功时返回`.ok stx`，其中`stx`是个句法对象；类别不存在或输入不符合该类别时结果都是`.error`，函数返回`false`。解析成功之后还得检查这是不是我们要的那个句法，所以再判断一个`stx.getKind == kind`，以防它能解析但使用的是别的规则。

> 你能定义的`term`、`tactic`、`command`等句法类别的解析器生成的都是句法树，顶部都是`Syntax.node`，所以都会有真的`kind`，这就是为什么我们可以用规则名去匹配解析结果的根节点。其它三个构造子句法对象其实也能`.getKind`但使用的是约定的行为，`Syntax.missing`返回`` `missing``，`Syntax.atom`返回反引号+字符串，`Syntax.ident`返回`` `ident``。

再看命令的声明。这里需要注意，`matchesSyntax`接收的是Lean对象：`Environment`、两个`Name`和一个`String`；但命令译补器中的`category:ident`、`kind:ident`和`input:str`是解析命令时捕获的句法对象，其类型分别是`Ident`、`Ident`和`StrLit`，因此调用函数前需要把它们转换成普通对象：`category.getId`取出标识符表示的`Name`；`resolveGlobalConstNoOverload kind`在当前环境和命名空间中解析规则名，得到它实际指向的`Name`；`input.getString`则取出字符串字面量的内容，并去掉源码中的引号和转义。四条`let`还展示了两种不同的绑定方法。`:=`是纯值绑定；`←`则是绑定单子计算的结果。细节我们以后讲译补器时再说。

最后，`m!"..."`是Lean的消息插值语法，作用类似产生`String`的`s!"..."`，但结果类型是`MessageData`，正好可以传给`logInfo`。花括号中的表达式会通过`ToMessageData`转换后嵌入消息；这里嵌入的是`matchesSyntax env category kind input`计算出的布尔值，因此最终显示`true`或`false`。


# 常用功能列表
%%%
tag := "syntax-features"
%%%

下面各表按来源和用途分别列出`syntax`声明中常用的预定义解析器、固定原子与句法类别、解析器组合子、空白与布局控制以及雅印控制。它们不是所有可用功能的封闭清单：Lean允许库注册新的解析器别名，也允许句法声明引用自定义的`Parser`，因此任何固定表格都不可能穷举所有扩展。错误恢复、禁用词法单元上下文、插值字符串等进阶功能见官方手册的[语法规则](https://www.leanprover.cn/reference-manual/latest/Notations-and-Macros/Defining-New-Syntax/#syntax-rules)与[缩进](https://www.leanprover.cn/reference-manual/latest/Notations-and-Macros/Defining-New-Syntax/#syntax-indentation)两节及底层`Parser` API。

这些写法在源码中分为几层。`Lean/Parser/Syntax.lean`定义了`syntax`命令右侧所用的句法描述语言；`Lean/Elab/Syntax.lean`把描述译补成`ParserDescr`；`Lean/Parser/Extension.lean`中的`compileParserDescr`再把它编译成真正的`Parser`。实际执行词法读取、选择、重复和位置检查的基础实现主要位于`Lean/Parser/Basic.lean`，较高级的缩进与雅印控制则位于`Lean/Parser/Extra.lean`。

## 预定义解析器
%%%
tag := "syntax-lexical-parsers"
%%%

Lean预先注册的小型`Parser`。它们直接匹配一种基础句法并产生相应的句法节点。

```table
| 写法 | 匹配内容 | 产生的节点 |
|------|----------|------------|
| `ident` | 标识符，可包含命名空间。 | 标识符节点；保留关键字须写成`«...»`。 |
| `rawIdent` | 不检查保留关键字的原始标识符。 | 与`ident`相同的标识符节点。 |
| `num` | 十进制、十六进制、八进制或二进制数字字面量。 | `numLitKind`节点。 |
| `hexnum` | 不带`0x`前缀的十六进制数字；必须紧跟在另一个解析器之后使用。 | `hexnumKind`节点。 |
| `scientific` | 科学计数法字面量，例如`1.3e-24`。 | `scientificLitKind`节点。 |
| `str` | 字符串字面量。 | `strLitKind`节点。 |
| `interpolatedStr(p)` | 插值字符串；花括号内用解析器`p`匹配，例如`interpolatedStr(term)`。 | `interpolatedStrKind`节点，依次保存文字片段和插值结果。 |
| `char` | 字符字面量。 | `charLitKind`节点。 |
| `name` | 名称字面量。 | `nameLitKind`节点。 |
| `hole` | 普通占位符`_`。 | `Lean.Parser.Term.hole`节点；译补时产生由上下文推断的元变量。 |
| `syntheticHole` | 合成占位符`?_`或`?name`。 | `Lean.Parser.Term.syntheticHole`节点；产生不会由统一化自动解决的合成元变量。 |
```

## 固定原子与句法类别
%%%
tag := "syntax-specifiers"
%%%

`syntax`声明所使用的几种基础说明符。它们的表面语法定义在`Lean/Parser/Syntax.lean`。

```table
| 写法 | 作用 | 备注或等价写法 |
|------|------|----------------|
| `"atom"` | 匹配固定原子，例如关键字或标点。 | 字符串首尾空格只提供雅印提示，不要求源码中出现空格。 |
| `&"atom"` | 匹配固定原子，但不把它注册成保留关键字。 | 适合仍需允许作为标识符使用的文字。 |
| `unicode("u", "a")` | 用同一解析器接受Unicode原子`u`和ASCII原子`a`。 | 雅印时通常输出Unicode写法。 |
| `cat`、`cat:prec` | 匹配句法类别`cat`；可附加最低优先级。 | 例如`term`、`term:max`、`tactic`。 |
```

## 解析器组合子
%%%
tag := "syntax-parser-combinators"
%%%

从已有解析器`p`、`q`构造新的解析器，或改变它们的组合、重复、前瞻与失败行为。这些写法也有“语法糖”和“真实组合子”两层。`p?`、`p*`、`p+`、`p <|> q`以及四种逗号后缀在`Init/Notation.lean`中声明并分别展开为`optional`、`many`、`many1`、`orelse`、`sepBy`或`sepBy1`。

```table
| 写法 | 作用 | 备注或等价写法 |
|------|------|----------------|
| `p q` | 先后匹配`p`与`q`。 | 用空白并列多个说明符。 |
| `(p)` | 把复合说明符`p`组合成一个整体。 | 常用于给一组说明符添加`?`、`*`等修饰符。 |
| `p <\|> q` | 匹配`p`或`q`。 | 也可写作`orelse(p, q)` |
| `lookahead(p)` | 仅检查`p`能够匹配。 | 正向前瞻；成功后恢复位置 |
| `!p`、`notFollowedBy(p)` | 当`p`不能匹配时成功，能匹配时失败。 | 负向前瞻 |
| `atomic(p)` | 匹配`p`，但在失败时恢复到运行`p`之前的位置。 | 常写成`atomic(p) <\|> q`以允许失败后尝试`q`。 |
| `patternIgnore(p)` | 正常匹配`p`，但在句法模式中忽略所得子树。 | 适合只负责定界、不需要被宏捕获的部分。 |
| `p?` | 匹配零个或一个`p`。 | 等价于`optional(p)`。 |
| `p*` | 匹配零个或多个连续的`p`。 | 等价于`many(p)`。 |
| `p+` | 匹配一个或多个连续的`p`。 | 等价于`many1(p)`。 |
| `p,*`、`p,+` | 匹配逗号分隔的`p`；分别允许零个或要求至少一个。 | 分别等价于`sepBy(p, ",")`和`sepBy1(p, ",")`。 |
| `p,*,?`、`p,+,?` | 与上一行相同，但允许最后再写一个逗号。 | 对应带`allowTrailingSep`的`sepBy`或`sepBy1`。 |
| `sepBy(p, "s")` | 匹配零个或多个由`s`分隔的`p`。 | 不允许尾随分隔符。 |
| `sepBy1(p, "s")` | 匹配一个或多个由`s`分隔的`p`。 | 名字中的`1`表示至少一个。 |
| `sepBy(p, "s", psep)` | 与`sepBy`相同，但实际使用解析器`psep`匹配分隔位置。 | 字符串`s`只用于雅印。 |
| `sepBy1(p, "s", psep)` | 与`sepBy1`相同，但实际使用解析器`psep`匹配分隔位置。 | 字符串`s`只用于雅印。 |
| `sepBy(p, "s", psep, allowTrailingSep)` | 四参数`sepBy`允许尾随分隔符。 | 项目数量仍可为零。 |
| `sepBy1(p, "s", psep, allowTrailingSep)` | 四参数`sepBy1`允许尾随分隔符。 | 仍要求至少一个项目。 |
```

## 解析器位置控制符
%%%
tag := "syntax-parser-position-controllers"
%%%

主要用于控制缩进和换行的约束。

```table
| 控制符 | 检查条件 |  典型用途 |
|--------|----------|--------------|
| `ws` | 当前 token 前存在空白。 | 要求两个词法单元之间留有空白。 |
| `noWs` | 当前 token 前不存在空白。 | 要求符号紧贴前一个词法单元。 |
| `linebreak` | 当前位置之前至少有一次换行。 | 要求后续结构另起一行。 |
| `colGt` | 当前 token 的列严格大于保存位置的列。 | 让 tactic 参数保持在更深缩进中，避免吞掉下一条同级 tactic。 |
| `colGe` | 当前 token 的列大于或等于保存位置的列。 | 保证一个块没有退出当前缩进范围。 |
| `colEq` | 当前 token 的列等于保存位置的列。 | 要求块中的同级项目对齐。 |
| `lineEq` | 当前 token 与保存位置位于同一行。 | 防止复合关键字被换行拆开。 |
| `withPosition(p)` | 保存当前位置，再在该基准下解析`p`。 | 为列与行检查建立作用域和比较基准。 |
| `withPositionAfterLinebreak(p)` | 若前一段句法的尾随空白含换行，则保存当前位置，再解析`p`；否则沿用外层基准。 | 让可换行结构只在实际换行后建立新的缩进基准。 |
| `withoutPosition(p)` | 暂时清除保存位置，再解析`p`。 | 在括号等定界结构内临时关闭缩进约束。 |
| `manyIndent(p)`、`many1Indent(p)` | 在首项位置建立基准，后续各项不得退到其左侧。 | 分别匹配零个或多个、一个或多个缩进范围内的`p`。 |
| `sepByIndent(p, "s")`、`sepBy1Indent(p, "s")` | 匹配由`s`或对齐换行分隔的`p`。 | 用于既允许显式分隔符、又允许按布局分项的列表。 |
```

## 雅印器控制符
%%%
tag := "syntax-pretty-printer-controllers"
%%%

都以`pp*`(Pretty Printer的首字母)开头。没有解析作用，只向雅印器传递布局意图。定义于`Lean/Parser/Extra.lean`。

```table
| 控制符 | 雅印作用 | 解析阶段 |
|--------|----------|----------|
| `ppHardSpace` | 输出一个不可换行的固定空格。 | `skip`，不消费文本。 |
| `ppSpace` | 输出空格或软换行，由行宽决定。 | `skip`，不消费文本。 |
| `ppLine` | 输出强制换行。 | `skip`，不消费文本。 |
| `ppRealFill(p)` | 使用 fill 模式排版`p`，尽量填满当前行。 | 等价于`p`。 |
| `ppRealGroup(p)` | 把`p`作为一个排版整体，尽量保持在同一行。 | 等价于`p`。 |
| `ppIndent(p)` | 增加`p`的缩进。 | 等价于`p`。 |
| `ppGroup(p)` | 对`p`组合使用 fill 与缩进；即`ppRealFill (ppIndent p)`。 | 等价于`p`。 |
| `ppDedent(p)` | 减少`p`的缩进，抵消默认缩进。 | 等价于`p`。 |
| `ppAllowUngrouped` | 允许外围句法不采用默认分组。 | `skip`，不消费文本。 |
| `ppDedentIfGrouped(p)` | 仅在外围已经分组时减少`p`的缩进。 | 等价于`p`。 |
| `ppHardLineUnlessUngrouped` | 已分组时强制换行，否则使用软换行。 | `skip`，不消费文本。 |
```

现在我们已经做好了充分的准备来看一些真实的句法案例了。

# 实战案例
%%%
tag := "syntax-examples"
%%%

本节将演示`rewrite`、`simp`、`induction`证明术的句法声明。它们也会成为之后章节中我们考察的例子。

## 共用的配置与位置句法
%%%
tag := "syntax-shared-tactic"
%%%

```anchor syntax_source_shared (module := Examples.SyntaxSources)
syntax posConfigItem := " +" noWs ident
syntax negConfigItem := " -" noWs ident
syntax valConfigItem := atomic(" (" notFollowedBy(&"discharger" <|> &"disch") ident " := ") withoutPosition(term) ")"
syntax configItem := posConfigItem <|> negConfigItem <|> valConfigItem
syntax optConfig := (colGt configItem)*

syntax locationWildcard := " *"
syntax locationType := patternIgnore(atomic("|" noWs "-") <|> "⊢")
syntax locationHyp := (ppSpace colGt (term:max <|> locationType))+
syntax location := withPosition(ppGroup(" at" (locationWildcard <|> locationHyp)))
```

这一大串看上去很复杂很长，实际上只有{anchorTerm syntax_source_shared (module := Examples.SyntaxSources)}`optConfig`和{anchorTerm syntax_source_shared (module := Examples.SyntaxSources)}`location`在后面实际会用到，其它都是局部声明。这里面每一个符号都在上面的章节介绍过，我直接把前半段五个声明直译为自然语言：

- {anchorTerm syntax_source_shared (module := Examples.SyntaxSources)}`posConfigItem` = "+" 无空格
 `ident`
- {anchorTerm syntax_source_shared (module := Examples.SyntaxSources)}`negConfigItem` = "-" 无空格
 `ident`
- {anchorTerm syntax_source_shared (module := Examples.SyntaxSources)}`valConfigItem` = "(" 不是 `discharger` 或 `disch`（不注册记号）`ident` " := " `term`（空格缩进无所谓） ")"，" := "之前匹配不上就失败了。`atomic`不把后面全包住是为了更聪明的错误处理逻辑，成功出现" := "就说明它应该是个配置项而不是别的，后面再写错就报告缺少 term 或 ")" 而不是直接失败。
- {anchorTerm syntax_source_shared (module := Examples.SyntaxSources)}`configItem` = {anchorTerm syntax_source_shared (module := Examples.SyntaxSources)}`posConfigItem` 或 {anchorTerm syntax_source_shared (module := Examples.SyntaxSources)}`negConfigItem` 或 {anchorTerm syntax_source_shared (module := Examples.SyntaxSources)}`valConfigItem`
- {anchorTerm syntax_source_shared (module := Examples.SyntaxSources)}`optConfig` = 任意个，每次出现缩进更深的 {anchorTerm syntax_source_shared (module := Examples.SyntaxSources)}`configItem`

后四个留作练习！

## `rewrite`
%%%
tag := "syntax-rw"
%%%

这真的很简单：

```anchor syntax_source_rewrite (module := Examples.SyntaxSources)
syntax rwRule    := unicode("← ", "<- ")? term
syntax rwRuleSeq := " [" withoutPosition(rwRule,*,?) "]"

syntax (name := rewriteSeq) "rewrite" optConfig rwRuleSeq (location)? : tactic
```

## `simp`
%%%
tag := "syntax-simp"
%%%

我觉得这好像也不需要我解释什么：

```anchor syntax_source_simp (module := Examples.SyntaxSources)
syntax discharger := atomic(" (" patternIgnore(&"discharger" <|> &"disch")) " := " withoutPosition(tacticSeq) ")"

syntax simpPre   := "↓"
syntax simpPost  := "↑"
syntax simpLemma := ppGroup((simpPre <|> simpPost)? unicode("← ", "<- ")? term)
syntax simpErase := "-" term:max
syntax simpStar  := "*"

syntax (name := simp) "simp" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)? : tactic
```

## 布局敏感的`induction`
%%%
tag := "syntax-induction"
%%%

`rw`和`simp`主要依靠标点划分结构。`induction`更独特：它的`with`分支还依赖换行和缩进。先看一个真实用例：

```anchor syntax_induction_use
example (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih
```

对应的完整句法声明是：

```anchor syntax_source_elim (module := Examples.SyntaxSources)
syntax inductionAltLHS := ppDedent(ppLine) withPosition("| " (("@"? ident) <|> hole) (colGt (ident <|> hole))*)
syntax inductionAlt  := inductionAltLHS+ (" => " (hole <|> syntheticHole <|> tacticSeq))?
syntax inductionAlts := " with" (ppSpace colGt tactic)? withPosition((colGe inductionAlt)*)

syntax elimTarget := atomic(binderIdent " : ")? term
```

```anchor syntax_source_induction (module := Examples.SyntaxSources)
syntax (name := induction) "induction " elimTarget,+ (" using " term)?
  (" generalizing" (ppSpace colGt term:max)+)? (inductionAlts)? : tactic
```

通过这个例子来体会布局敏感句法声明的精妙环节。`inductionAlts`末尾的`withPosition((colGe inductionAlt)*)`。约束分支区域：`withPosition`在开始读取分支时保存当前位置，通常就是第一个`|`所在的列；每次重复前的`colGe`要求下一个分支不能位于该基准列左侧。因此各分支共享同一个最小缩进边界，但不必严格对齐，更深缩进的分支同样可以解析。`inductionAltLHS`内部另有一层`withPosition`：它以当前分支的`|`为基准，而`(colGt (ident <|> hole))*`要求构造子之后的每个参数位于`|`的右侧。
