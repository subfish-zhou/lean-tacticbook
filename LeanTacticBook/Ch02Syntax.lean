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

```
-- `termMyTerm` 的译补函数还未实现
elaboration function for `termMyTerm` has not been implemented
  MyTerm
```

`term`是这个句法的类型。你所熟知的 Lean 的类型论当中的项都可以作为句法项。我们还可以定义其它类型的句法，例如证明术`tactic`和命令`command`，只需要把 {anchorTerm syntax_declaration}`term` 改成相应的类型即可。Lean 还支持其它的一些类型，之后遇到的时候我们再讲。我们甚至可以用{kw}`declare_syntax_cat`来声明一个新的句法类型。

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

* {kw}`=>` 左边就是句法，右边就是语义。{anchorTerm syntax_xor}`l` 和 {anchorTerm syntax_xor}`r` 是运算符的两个参数，它们自动属于 `term` 类型。
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

```
my_lift n + 3 to ℕ using hn with k hk
```

详细解释一下：
1. `( ... )?`表示括号内的内容是可有可无的，可以出现零次或一次。此处`" using " term`和`" with " ident ...`以及里面的第二和第三个参数都是可有可无的。
2. `with`中参数的类型`ident`也是句法类型，称为标识符。它的范围要比`term`小，只接受名字，例如`x`，`h₁`，`Nat.add`，而`1`、`x + 1`等等就不行。
3. `ppSpace`是雅印器的控制符，表示在雅印时输出一个空格，或者在行太长时进行软换行。详表见[雅印器控制符](## 雅印器控制符)。
4. `colGt`是解析器的控制符，在解析时要求后续的标识符缩进比前一个标识符更深。在这里，意思是如果你在填写第二个或第三个标识符时换行的话，必须比前一个标识符有更多的缩进，否则无法被解析成参数。详表见[解析器位置控制符](## 解析器位置控制符)。

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

# `Syntax`类型
%%%
tag := "syntax-type"
%%%

以上的介绍像是在陈列句法声明工具箱，接下来我们要操作句法本身。如果你只想学如何声明句法，那么你完全可以跳到下一节。更多的理论总是有用的！作为一种动机演示，也同样作为学习本节的奖励，最终成果将会是一个“判断给定字符串是否符合某个句法解析器”的函数。

前面声明句法时，Lean都会在背后自动运行解析器。开始研究解析器之后，我们首先需要一种办法来查看解析结果：给定一段源码，它会产生哪些句法节点？为此可以自己定义一个调试命令：

```anchor parser_inspect_kind
partial def syntaxKinds : Syntax → Array SyntaxNodeKind
  | .node _ kind args => args.foldl (fun kinds arg => kinds ++ syntaxKinds arg) #[kind]
  | _ => #[]

elab "#inspect_syntax " t:tactic : command => do
  for kind in syntaxKinds t.raw do
    if kind != nullKind then
      logInfo m!"{kind}"

#inspect_syntax myexact True.intro
#inspect_syntax simp only [↓ ← h]
```

`elab "#inspect_syntax " t:tactic : command`同时声明了命令句法和译补逻辑。参数`t`的类型已经规定为`tactic`，所以调用时直接写待检查的证明术即可，不再需要手工传入类别、字符串或预期名称。Lean会先按`tactic`类别解析这段输入，再把得到的语法树交给命令实现。

`syntaxKinds`按先根后子的顺序递归收集所有具名节点。可选项、重复项等组合结构还会生成一些`nullKind`节点，命令将它们过滤掉。第一次调用只输出：

```
tacticbook_syntax.myexact
```

这正是前面`(name := myexact)`指定的名称。第二次调用则输出：

```
Lean.Parser.Tactic.simp
Lean.Parser.Tactic.optConfig
Lean.Parser.Tactic.simpLemma
Lean.Parser.Tactic.simpPre
```

这说明`syntaxAbbrev`不只方便复用解析器；成功匹配后，它也会在较大的语法树中留下以声明名为种类的节点。因此递归检查可以看出`simp only [↓ ← h]`依次使用了整个证明术、配置、引理和前序遍历标记这四层句法。若只关心最外层规则，直接查看`t.raw.getKind`即可；若要连原子、标识符和源码位置一起查看，则可以输出`repr t.raw`。

最后，解析成功只说明这段文字符合某条句法规则，不说明它具有语义。上面的`myexact True.intro`能够成功解析，但由于我们还没有为`myexact`实现宏展开或译补函数，把它真正写进证明时仍然会报错。解析、宏展开和译补是三个不同阶段。



# 常用功能列表
%%%
tag := "syntax-features"
%%%

本节详细列出上面所涉及的常用功能的列表备查。

下面各表按来源和用途分别列出`syntax`声明中常用的预定义词法解析器、固定原子与句法类别、解析器组合子、空白与布局控制以及雅印控制。它们不是所有可用功能的封闭清单：Lean允许库注册新的解析器别名，也允许句法声明引用自定义的`Parser`，因此任何固定表格都不可能穷举所有扩展。错误恢复、禁用词法单元上下文、插值字符串等进阶功能见官方手册的[语法规则](https://www.leanprover.cn/reference-manual/latest/Notations-and-Macros/Defining-New-Syntax/#syntax-rules)与[缩进](https://www.leanprover.cn/reference-manual/latest/Notations-and-Macros/Defining-New-Syntax/#syntax-indentation)两节及底层`Parser` API。

## 预定义词法解析器
%%%
tag := "syntax-lexical-parsers"
%%%

这些名字不是用`declare_syntax_cat`声明的句法类别，而是Lean预先注册的叶子`Parser`别名；它们直接匹配一个词法项并产生相应的句法节点。

```table
| 写法 | 匹配内容 | 产生的节点 |
|------|----------|------------|
| `ident` | 标识符，可包含命名空间。 | 标识符节点；保留关键字须写成`«...»`。 |
| `rawIdent` | 不检查保留关键字的原始标识符。 | 与`ident`相同的标识符节点。 |
| `num` | 十进制、十六进制、八进制或二进制数字字面量。 | `numLitKind`节点。 |
| `scientific` | 科学计数法字面量，例如`1.3e-24`。 | `scientificLitKind`节点。 |
| `str` | 字符串字面量。 | `strLitKind`节点。 |
| `char` | 字符字面量。 | `charLitKind`节点。 |
| `name` | 名称字面量。 | `nameLitKind`节点。 |
```

## 固定原子与句法类别
%%%
tag := "syntax-specifiers"
%%%

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

从已有解析器`p`、`q`构造新的解析器，或改变它们的组合、重复、前瞻与失败行为。

```table
| 写法 | 作用 | 备注或等价写法 |
|------|------|----------------|
| `p q` | 先后匹配`p`与`q`。 | 用空白并列多个说明符。 |
| `(p)` | 把复合说明符`p`组合成一个整体。 | 常用于给一组说明符添加`?`、`*`等修饰符。 |
| `p <\|> q` | 匹配`p`或`q`。 | 也可写作`orelse(p, q)`；分支消费记号后便不会回溯。 |
| `lookahead(p)` | 仅检查`p`能够匹配。 | 正向前瞻；成功后恢复位置，不消费输入或捕获句法。 |
| `!p`、`notFollowedBy(p)` | 当`p`不能匹配时成功，能匹配时失败。 | 负向前瞻；不消费输入，也不捕获句法。 |
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

都以`pp*`(Pretty Printer的首字母)开头。没有解析作用，只向雅印器传递布局意图。

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

下面的声明都来自 Lean 4.32.2 的`src/lean/Init/Tactics.lean`。本节完整展示这些证明术的句法声明以及`rw`、`rwa`的宏定义；证明术如何执行属于译补阶段，不在这里展开。为了能读懂主声明，我们先看它们共同复用的配置和位置子句法。

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

配置可以写成`+opt`、`-opt`或者`(opt := value)`。这里有几种尚未详细见过的控制符：

1. `noWs`不消费字符，只检查下一个词法单元必须紧贴前一个词法单元。因此`+zeta`可以匹配`" +" noWs ident`，而`+ zeta`不行。
2. `&"discharger"`和普通的`"discharger"`匹配相同文字，但不会把它注册为保留关键字。这样`discharger`在其它位置仍然可以作为普通标识符。
3. `notFollowedBy(p)`在`p`不能匹配时成功，而且不消费输入。这里用它排除`(discharger := ...)`和`(disch := ...)`，把这两种写法留给`simp`自己的`discharger`子句。
4. Lean的`p <|> q`不会在`p`消费了一部分输入后自动回溯。`atomic(p)`会在`p`失败时把位置恢复到运行`p`之前，因此`atomic(p) <|> q`能够安全地尝试第二个分支。上面的`atomic`正是为了在读到左括号后仍能把不属于配置项的输入完整退回。
5. `withoutPosition(p)`暂时清除外围保存的缩进基准，再运行`p`。配置值中的`term`因此不会误受外层证明术缩进的限制。

`optConfig`把配置项重复零次或多次；`colGt`要求换行后的配置项位于外层基准列的右侧。位置子句则可以是`at *`、`at h₁ h₂`或者`at h₁ ⊢`。`patternIgnore(p)`照常解析`p`，但把所得子树标记为在句法模式中忽略；因此`⊢`和ASCII写法`|-`只负责表示“目标”，不会成为译补器关心的参数。`withPosition(p)`为内部的`colGt`保存新的位置基准，`ppGroup`和`ppSpace`只控制雅印布局，不改变接受哪些源码。

## `rewrite`、`rw`与`rwa`
%%%
tag := "syntax-rw"
%%%

先看实际执行重写的`rewrite`：

```anchor syntax_source_rewrite (module := Examples.SyntaxSources)
syntax rwRule    := unicode("← ", "<- ")? term
syntax rwRuleSeq := " [" withoutPosition(rwRule,*,?) "]"

syntax (name := rewriteSeq) "rewrite" optConfig rwRuleSeq (location)? : tactic
```

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

## `simp`的源码
%%%
tag := "syntax-simp"
%%%

`simp`不是宏，它有自己的证明术译补器。下面是主声明以及它直接依赖的全部子句法：

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

`discharger`匹配`(discharger := tac)`或`(disch := tac)`。前面的通用`valConfigItem`特意用`notFollowedBy`避开这两个名字，所以输入会留到这里处理。`patternIgnore`让关键字只充当定界标记，`tacticSeq`则允许等号右侧放一串证明术，而不只是一个`tactic`。

一条`simpLemma`由三层组成：可选的`↓`或`↑`指定在进入子项之前还是之后使用规则，可选的`←`或`<-`反向使用等式，最后的`term`给出定理。`ppGroup`希望雅印器尽量把这三部分排在一起。`simpErase`中的`term:max`要求减号后先匹配一个最高优先级的项；复杂表达式需要括号明确边界，避免它吞掉后面的`simp`参数。`simpStar`就是`*`，表示使用所有局部假设。

主声明依次组合：配置、可选discharger、可选`only`、可选参数列表和可选位置。`&" only"`使用非保留关键字形式，所以声明`simp`不会顺带禁止用户在其它上下文中使用名字`only`。参数列表内部的每个元素都会保留`simpStar`、`simpErase`或`simpLemma`节点种类；译补器正是检查这些种类来区分三种语义，而不是重新分析原始文本。

## 布局敏感的`induction`
%%%
tag := "syntax-induction"
%%%

`rw`和`simp`主要依靠标点划分结构。`induction`更独特：它的`with`分支还依赖换行和缩进。先看一个真实用法：

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

从最内层开始读：

1. `inductionAltLHS`匹配`| zero`或`| succ n ih`这样的分支左侧。构造器名前可选的`@`要求显式列出隐式参数；构造器也可以写成`_`。后续参数是零个或多个`ident <|> hole`，`colGt`要求换行后的参数缩进到分支起点右侧。
2. `ppLine`建议在分支前换行，`ppDedent`抵消外围默认缩进；二者只影响雅印。`withPosition`则真正影响解析，它把当前分支起点保存为内部列检查的基准。
3. 一个`inductionAlt`可以有一个或多个左侧，因此可以让多个构造器分支共享同一个`=>`右侧。右侧还可以省略，或者写普通占位符`_`、合成占位符`?_`/`?name`以及完整的`tacticSeq`。`syntheticHole`正是匹配后两种问号写法的项句法。
4. `inductionAlts`先读`with`，随后可以有一个对所有分支运行的共同`tactic`，再读取若干分支。`colGe`要求每个分支不能退到保存基准的左侧，这样解析器遇到外层同级代码时就会停止收集分支。
5. `elimTarget`既可以是普通项`e`，也可以是`h : e`。`atomic(binderIdent " : ")`保证只有在名字和冒号都匹配成功时才采用带名形式；否则回退后让后面的`term`从原位置解析。
6. 主声明中的`elimTarget,+`要求至少一个逗号分隔的归纳目标。之后还可以用`using term`指定归纳原理，用`generalizing term...`列出至少一个需要先泛化的项，最后接可选的`with`分支。

这个例子补上了前面列表和运算符例子没有展示的一层：Lean的句法不只描述词法单元的先后关系，还可以利用保存的位置和列约束描述布局敏感的块结构。



# 解析器
%%%
tag := "syntax-parser"
%%%


是的，*leading/trailing parser 是 Lean parser 的标准实现机制*。Lean 源码明确说明：

> All builtin parser categories are Pratt's parsers.

也就是说，`term`、`tactic` 等可扩展语法类别使用的是 *Pratt parser*。

*Lean 如何解析表达式*

可以粗略理解为：

```
parseTerm(最低优先级):
  lhs := 调用 leading parser 解析起始项

  while 后面存在满足优先级要求的 trailing parser:
    lhs := 调用 trailing parser，并传入已有 lhs

  return lhs
```

两类 parser 分工如下：

- *leading parser*：不需要已有左项，例如标识符、字面量、括号、前缀运算符。
- *trailing parser*：接在已有左项后，例如中缀运算符、后缀运算符、函数应用和字段投影。

例如：

```
10 SUBR₂ 3
```

执行形状大致是：

```
leading parser 解析 10
trailing parser 接收 lhs = 10
trailing parser 读取 SUBR₂ 3
```

声明：

```
macro:10 l:term:10 " SUBR₂ " r:term:10 : term => ...
```

在文法上是直接左递归：

```
term ::= term " SUBR₂ " term
```

Lean 将开头的第一个 `term` 提取为已有 `lhs`，剩余部分编译为 trailing parser，从而避免无限递归。

注意，*trailing parser 不意味着左结合*。结合方向仍由左右参数的 binding power 决定。

*它是最流行的实现吗？*

Pratt parser 是解析*表达式和运算符优先级*最流行的方法之一，但不是通用语言 parser 中唯一或绝对最流行的方法。

`leading parser` 和 `trailing parser` 还是 Lean 的命名。其他 Pratt parser 实现更常称为：

- `nud` / null denotation：对应 leading parser
- `led` / left denotation：对应 trailing parser
- prefix parselet / infix parselet

常见解析技术还有：

| 方法 | 常见用途 |
|---|---|
| 递归下降、LL | 手写语言 parser，结构直观 |
| LR、LALR、SLR | Yacc/Bison 等生成式 parser |
| Pratt / TDOP | 表达式、前中后缀算符和优先级 |
| Precedence climbing | 较简单的运算符优先级解析 |
| PEG / Packrat | 按顺序选择、支持回溯的文法 |
| Parser combinator | 函数式组合小 parser |
| Earley / GLR | 一般上下文无关文法和歧义文法 |

Lean 的选择特别适合它的需求：用户可以随时通过 `syntax`、`macro`、`notation` 添加新语法和新运算符。传统固定 LR 表不容易这样动态扩展，而 Pratt parser 只需向 leading/trailing 表注册新的 parselet。
