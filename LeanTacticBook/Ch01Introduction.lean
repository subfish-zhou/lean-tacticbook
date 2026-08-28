import VersoManual
import LeanTacticBook.Helpers

open Verso.Genre Manual
open Verso Code External

set_option verso.exampleProject "examples"
set_option verso.exampleModule "Examples.Ch01Introduction"

#doc (Manual) "看 Lean 如何处理一份文件" =>
%%%
file := "Ch01Introduction"
tag := "introduction"
%%%

一份 Lean 文件起初只是文本：有的片段声明定理，有的定义程序，还有的要求 Lean 当场做一件事。Lean 用同一套前端处理它们，但并非每一条路最后都会运行机器码。动手写元程序之前，我们得先认清 Lean 此刻拿着什么对象，以及哪一种程序能够接触这个对象。

先把地图画得简单一些：

:::codeBox "pseudocode"
```
源代码文本
    |
    | parser
    v
Syntax
    |
    | 宏展开与译补按当前节点协作
    v
各类别自己的结果或作用：
Expr、证明状态变化、诊断消息、环境更新
    |
    | command 译补可以完成声明
    v
安全声明由 kernel 检查

可生成代码的定义还可以被编译
已编译定义 + 执行请求 → 运行时行为
```
:::

这张图先标对象怎样变化。parser 按 syntax category 读取文本，留下 `Syntax`；宏把 `Syntax` 改写成新的 `Syntax`，译补器则利用类型、名字和上下文产生各类别需要的结果。安全声明还要交给 kernel 检查。一个定理可以停在已检查声明，不会因为写进文件便自行运行；可执行定义即使已经生成代码，也要等执行请求到来才会产生运行时行为。

图上把接口名字写简单了。parser 并不真是一个 `String → Syntax` 函数，各类译补器也不都会返回 `Expr`。先用几件普通的 Lean 工具观察源码处理，随后再回来展开这些箭头。

# 从源码处理中说一句 Hello World
%%%
tag := "hello-from-source-processing"
%%%

元程序出错时，最终错误往往不如前一步拿到的对象有用。最便宜的检查办法，是让 Lean 在处理文件时把那个对象报告出来。先从传统问候开始：

```anchor ch01_hello_log
import Lean

open Lean

run_cmd
  logInfo m!"Hello, world!"
```

`run_cmd` 让其中的程序在 Lean 处理这条 command 时运行，`logInfo` 把消息送进诊断日志；命令行编译器和支持 Lean 诊断的编辑器都能把它显示出来。先确认这条观察通道畅通，随后再把解析得到的名字、刚生成的表达式或当前证明目标送进来。

后面的片段继续写在同一份示例文件里，沿用 `import Lean` 和 `open Lean`；标成“内置定义形状”或“前文摘录”的代码只供阅读，不要再次声明。

固定文本还不能证明我们真的观察到了一个值。给程序一件可能变化的东西：

```anchor ch01_observe_value
run_cmd
  let stage := "elaboration"
  logInfo m!"Now observing: {stage}"
```

先改动 `stage`，预测消息，再重新编译。花括号会把当前值插进消息里。我们从 `logInfo` 开始，真正为的是这个短反馈环：构造对象，报告对象，把结果和预测比较，然后才让元程序继续长大。

如果要等程序真正运行时再打印，同一句问候可以这样写：

```anchor ch01_runtime_hello
def main : IO Unit :=
  IO.println "Hello, world!"
```

两句问候出现在不同时刻，因为包住它们的程序向 Lean 发出了不同请求。第一个程序位于 `run_cmd` 内，在 Lean 译补源码时运行，结果写入 Lean 的诊断系统；第二个程序要等 `main` 被执行时才打印，结果写入标准输出。所以判断运行时机时，要看调用外面包着什么，不能只猜 `logInfo` 或 `println` 的名字。

再给这条反馈环添两个入口：

```anchor ch01_observation_commands
#check IO.println
#eval 2 + 3
```

`#check` 请 Lean 译补一个表达式，并报告它的类型；它不会调用 `IO.println`。`#eval` 请 Lean 求出一个表达式的值，再报告结果。`logInfo` 与两者都不同：我们自己的元程序可以在运行到一半时调用它。于是三类问题各有一个入口：Lean 推出了什么类型，这个表达式算出什么值，我的元程序运行到这里究竟看见了什么？

在 Lean 4.32.2 中，`#check IO.println` 打印的类型比 `String → IO Unit` 更一般：

:::codeBox "code"
```
IO.println.{u_1} {α : Type u_1} [ToString α] (s : α) : IO Unit
```
:::

暂时只读末端即可：它接收一个 Lean 知道怎样转成文字的值，返回一段有 `IO Unit` 类型的程序。等我们回到前端接口时，再把 `IO Unit` 的形状讲清楚。


# 字符串、消息与名字
%%%
tag := "strings-messages-names"
%%%

第一条消息只有普通文本。以后，我们要把 Lean 内部对象插入诊断消息，又不想过早把它们压扁成字符串。Lean 提供了两种外观相近的插值形式，前缀决定结果类型：

```anchor ch01_interpolation
run_cmd
  let language := "Lean"
  let plain : String := s!"Hello, {language}!"
  let message : MessageData := m!"Hello, {language}!"
  logInfo message
```

`s!"..."` 构造 `String`，插入的值需要有 `ToString` 实例。`m!"..."` 构造 Lean 消息系统使用的结构化类型 `MessageData`，插入的值走 `ToMessageData`。String 本身可以变成消息数据，因此在这个例子里二者看起来一样。换成 `Expr`、证明目标这类依赖 Lean pretty printer 和当前消息上下文的对象，两种插值就不能互换。若过早把对象转成普通 String，这些结构也会一起丢掉。

假设一行配置包含三个十进制字段。先把它切开：

```anchor ch01_split_fields
run_cmd
  let raw := "10,oops,20"
  let fields := raw.splitOn ","
  logInfo m!"fields: {fields}"
```

`splitOn` 返回 `List String`。写宏之前不必背完 String 的全部操作；眼前这份输入只为我们挣来了这一项。

配置里还可能出现供元程序查找的点分名字，例如 `"Lean.Meta.mkAppM"`。我们先不查询它是否真有对应声明，只把点分文本变成结构化的 `Name`，再取出父级：

```anchor ch01_name
run_cmd
  let text := "Lean.Meta.mkAppM"
  let name : Name := text.toName
  let parent := name.getPrefix
  logInfo m!"name: {name}; parent: {parent}"
```

这里的点记法已经实际运行：`text.toName` 是 `String.toName text` 的写法，左边的 `text` 补入 `String.toName` 的字符串参数；`name.getPrefix` 同样可改写为 `Name.getPrefix name`。把两行改回普通调用，诊断消息不变。转换后的 `name` 具有 `Name` 的组成结构，但 `String.toName` 本身不会查询环境来证明该声明存在。


# 小函数、缺失值与容器
%%%
tag := "functions-options-collections"
%%%

`fields` 中有一项不是自然数。若转换函数坚持返回 `Nat`，它只好为这一项编造数字，或直接崩溃。Lean 的 `String.toNat?` 返回 `Option Nat`，把“可能没有结果”写进类型。可选值有两个构造子；把内置定义的形状摘出来看（不要重新声明）：

:::codeBox "code"
```
inductive Option (α : Type u) where
  | none
  | some (value : α)
```
:::

构造子声明可以从右往左读。`none` 和 `some` 最终都构造 `Option α`；`some` 在此之前要接收一个 `α` 类型的值。参数 `α` 让同一种结构可以装下一个可能存在的 Nat、String、Name 或其他类型。

用 `match` 可以把两种情形都摊开：

```anchor ch01_describe_option
def describeNat? (value : Option Nat) : String :=
  match value with
  | some n => s!"found {n}"
  | none => "missing"

#eval describeNat? "42".toNat?
#eval describeNat? "oops".toNat?
```

两次计算得到的 String 分别是 `found 42` 和 `missing`；`#eval` 显示 String 时会带上引号，所以输出是 `"found 42"` 与 `"missing"`。`none` 是普通数据。它没有抛异常，没有要求 tactic 回退，也没有偷偷填入默认数字。

`=>` 右边可以使用匹配时拆出的值。这里的 `n` 就是 `some` 携带的 Nat。整个具名定义的类型是 `Option Nat → String`：它接收一个可选自然数，返回 String。

下一步操作需要一个更小的函数，说明怎样处理单个字段。它不值得单独命名：

```anchor ch01_anonymous_function
#check (fun field : String => field.toNat?)
```

括号内是匿名函数，类型为 `String → Option Nat`。写 `f x` 就是在把参数 `x` 交给函数 `f`；只有分组不清楚时才需要括号。函数箭头向右结合，所以 `α → β → γ` 是 `α → (β → γ)`：先接收一个 `α`，再接收一个 `β`，最后产生 `γ`。

现在可以明确决定怎样处理坏字段了。`filterMap` 对每一项调用函数，保留 `some` 里的值，丢掉所有 `none`：

```anchor ch01_filter_map
run_cmd
  let fields := "10,oops,20".splitOn ","
  let values := fields.filterMap (fun field => field.toNat?)
  logInfo m!"parsed values: {values}"
```

输出中只剩 `[10, 20]`。这个操作没有证明所有字段都合法，而是选择了“省略非法字段”这条策略。真正的配置解析器也可以在遇到 `none` 时报告错误；无论丢掉还是报错，返回的 `Option` 都迫使我们当场作出选择。

`List` 本身也由两个构造子组成；把内置定义的形状摘出来看（不要重新声明）：

:::codeBox "code"
```
inductive List (α : Type u) where
  | nil
  | cons (head : α) (tail : List α)
```
:::

常见记号 `[]` 和 `head :: tail` 直接露出这两种情形。若一个函数总是拆出首项，再对尾部递归，这种结构恰好合手。眼前程序只需要第一项，一次 match 就够了：

```anchor ch01_first_field
def firstField : List String → String
  | [] => "<empty>"
  | head :: _ => head
```

另一些操作把列表当作整体。`map` 改变每一项，`foldl` 则从左向右携带累加值，最后交出一个结果：

```anchor ch01_list_pipeline
run_cmd
  let fields := "10,oops,20".splitOn ","
  let values := fields.filterMap (fun field => field.toNat?)
  let labels := values.map (fun n => s!"n={n}")
  let total : Nat := values.foldl (fun acc n => acc + n) 0
  logInfo m!"first: {firstField fields}; labels: {labels}; total: {total}"
```

这里新增的两个动作仍在推进同一条数据流：`map` 把每个幸存的 Nat 改成标签；`foldl` 从左向右带着总和继续走。

List 适合刚才的切分、筛选与首尾匹配。另一种观察任务更关心元素数量和位置：先写下一小段 token 序列，补上右括号，再检查中间一项。

```anchor ch01_array_tokens
run_cmd
  let tokens : Array String := #["(", "x"].push ")"
  logInfo m!"token count: {tokens.size}; middle: {tokens[1]?}"

  for piece in tokens do
    logInfo piece
```

`#[...]` 是 Array 字面量，和 List 的 `[...]` 不同。`push` 把右括号接到末尾，`size` 得到 `3`，`tokens[1]?` 则得到一个携带字符串 `"x"` 的 `some`；在当前诊断消息中，它显示成 `some (x)`。索引若不存在，带问号的读取会返回 `none`。最后的 `for` 按顺序取出三个元素，并把每一个交给循环体。

两种容器都能保存许多有序元素，选择取决于后续动作。程序若反复拆出 `head :: tail`，List 往往更顺手；若经常在末尾追加、读取 `size` 或按索引观察，Array 往往更合适。


# 读懂返回值之外发生了什么
%%%
tag := "effects-beyond-results"
%%%

到目前为止，`firstField` 一类具名定义都直接返回普通值。`run_cmd` 的程序却有另一种形状：

```anchor ch01_filter_map
run_cmd
  let fields := "10,oops,20".splitOn ","
  let values := fields.filterMap (fun field => field.toNat?)
  logInfo m!"parsed values: {values}"
```

`logInfo` 不只计算一个 `MessageData`，它还把诊断消息放进 Lean 当前的消息日志。在允许记录诊断消息的元编程 monad `M` 中，`logInfo` 返回 `M Unit`。

`Option`、`List`、`Array` 这样的类型构造子都还需要一个元素类型，`Option Nat`、`List String`、`Array Name` 才是完整类型。`M α` 也可以这样读：一段在 `M` 所描述的上下文中运行、并能产生 `α` 的计算。不过字母相同不代表能力相同；换一个 `M`，可读的环境、可改的状态和可调用的操作都可能变化。

`Unit` 只有一个普通值，写作 `()`。看到 `M Unit`，就不要期待它返回有趣的普通值；运行它的理由通常在返回值之外，例如记录消息、更新环境或改变证明状态。`IO Unit` 与 `CommandElabM Unit` 外形相似，却不在同一上下文运行，也不提供同一组操作。

`do` 把步骤按执行顺序写下，后面的步骤可以使用前面产生的值：

```anchor ch01_make_message
def makeMessage : IO String := do
  let base := "hello"
  let target := "Lean"
  return s!"{base}, {target}"
```

两个 `let` 都直接绑定普通值。`return` 把最后的 String 放进当前计算形状，于是整个定义有 `IO String` 类型。

真正需要 `←` 的地方会运行一段计算：

```anchor ch01_greet
def greet : IO Unit := do
  let message ← makeMessage
  IO.println message
```

`let message ← makeMessage` 先运行计算，再把它产生的 String 命名为 `message`。取出 `message` 后，`IO.println message` 接着运行：它只交回 `Unit`，却会把一行文字送到标准输出。在 `do` 中，`return value` 可以直接把值交回外围计算；普通表达式需要构造相同形状时，也会写 `pure value`。

`pure`、顺序执行、失败、上下文和状态怎样实现，先留到真正需要拆开这些 `M` 时再问。眼下只用这套读法去看 Lean 暴露的前端函数类型。


# 前端处理器的真实形状
%%%
tag := "frontend-handler-shapes"
%%%

现在回到开篇的地图。图中的数据方向没变，但箭头上的程序被我们写扁了。先省略命名空间和声明关键字，看 Lean 4.32.2 中 parser 的核心形状：

:::codeBox "code"
```
ParserFn := ParserContext → ParserState → ParserState
```
:::

parser 函数接收只读的解析上下文和当前解析状态，再返回更新后的状态。状态中保存输入位置、目前组装出的 syntax stack 和错误信息。因此，精确核心不是 `String → Syntax`：解析会推进一个更大的过程，构造出的句法和诊断信息都留在状态里。

Lean 还把 parser 函数与组合、选择 parser 时需要的信息包装在一起：

:::codeBox "code"
```
structure Parser where
  info : ParserInfo := {}
  fn   : ParserFn
```
:::

这段删去了 `Lean.Parser.Parser` 的命名空间等细节；`ParserInfo` 也先别拆，等组合 parser 时再看它怎样参与选择。现在先预测 `fn` 的动作：它推进解析状态，而不是计算句法树日后表示的项。

宏接口更接近开篇的简图：

:::codeBox "code"
```
Macro := Syntax → MacroM Syntax
```
:::

它接收 syntax，在 `MacroM` 中产生 syntax。这段计算可以使用宏展开上下文提供的有限信息，也可以拒绝输入，但类型里没有 expected `Expr`，也没有证明目标。所以宏可以改写眼前的句法，却不能凭这个接口询问 expected type 或当前证明目标。

开篇图把宏展开和译补压在同一个箭头上，现在可以看清其中的局部循环：分派器处理当前节点，成功的宏候选产生新 `Syntax`，新节点随即再次进入分派；其他候选怎样继续，由 command、term、tactic 各自的分派规则决定。尤其对 tactic 而言，宏生成的新 tactic 若执行失败，Lean 可以恢复状态，继续尝试较旧的宏候选或 tactic 译补器。因此，不能把这条循环简化成“只要存在宏，译补器便不会接手”。

译补器没有唯一的函数类型，因为不同 syntax category 要留下不同结果：

:::codeBox "code"
```
TermElab    := Syntax → Option Expr → TermElabM Expr
CommandElab := Syntax → CommandElabM Unit
Tactic      := Syntax → TacticM Unit
```
:::

term 译补器接收 term syntax 和一个可选的 expected `Expr`，最后产生 `Expr`。Lean 也用 `Expr` 表示类型，因此这里的可选 `Expr` 是 expected type，并非预期得到的运行时值。expected type 可以协助 Lean 消解重载记号、补充隐式信息及表面 term 省略的其他部分。

command 译补器接收 command syntax。它的重要工作可能加入声明、注册扩展或发出诊断消息，因此普通返回值只需 `Unit`。tactic 译补器也返回 `Unit`，重要结果却留在证明状态里：目标可以被关闭、生成、重排或改变。共同的后缀 `M` 不会抹去这些差异；`CommandElabM` 与 `TacticM` 暴露的是不同上下文和状态。

把三条类型并排后，阶段之间不能任意交换：宏拿不到 expected type 或证明目标，term 译补器才能借 expected type 产出 `Expr`，tactic 则沿活动目标修改证明状态。暂时不用打开这些 `M`；先把每种程序放回正确箭头，已经足以判断它何时运行、能拿到什么。

开头那句 Hello World 现在也还清了一笔解释债。`run_cmd` 的程序在 command 译补中执行，所以 `logInfo` 能接触 Lean 的译补期消息日志。该 command 的有用结果是写入日志的消息，不是代码块返回的那个没有信息量的 Unit 值。


# 同一套前端，两个终点
%%%
tag := "two-frontend-endpoints"
%%%

先预测下面这条定理最终停在哪里：

```anchor ch01_theorem_endpoint
theorem add_zero_example (n : Nat) : n + 0 = n := by
  simp
```

文件只请求 Lean 接纳这条定理，因此它停在环境中的已检查声明，不会再分出打印或运行程序的支路。

再回到前面的 `main`，预测哪些步骤相同，以及后续请求可以在哪里添出一条新分支。这里只重复展示前文定义，不要在运行文件中再次声明它：

```anchor ch01_runtime_hello
def main : IO Unit :=
  IO.println "Hello, world!"
```

`main` 也先成为声明；kernel 检查它能否进入受信环境，编译器可以在模块处理时为它生成代码。以后运行程序时新增的是启动这段代码及其运行时行为。

`#eval 2 + 3` 则在源码文件内部发出执行请求。`#eval` command 本身先被解析和译补；Lean 4.32.2 随后为这个表达式建立并编译一个临时辅助定义，再执行它。因此，“译补”和“求值”不能当作同义词：前者建立类型完整的表达式，后者请求拿这个表达式去计算。

至此，无须再背一张分类表，也能判断开头几件工具。`#check` 停在“报告类型”的请求上；`#eval` 请求一个值；`run_cmd logInfo ...` 运行 command 译补计算，并写入诊断消息；定理贡献一条经 kernel 检查的声明；`main` 定义以后还可以成为正在运行的程序。它们都从源码文本开始，包住文本的 command 决定 Lean 最终要走到哪里。

最后让同一个表达式走进三种观察入口：

```anchor ch01_three_observations
#check (2 + 3 : Nat)
#eval (2 + 3 : Nat)

run_cmd
  let value : Nat := 2 + 3
  logInfo m!"value during command elaboration: {value}"
```

编译前，分别写下三段代码运行在哪个阶段、报告的是类型、求值结果还是诊断消息。再把表达式改成 `2 * 3`，先预测三处变化，后编译。最后回看前面的 theorem 与 `main`：哪一个只要求 Lean 接纳声明，哪一个还可以在执行请求到来后产生运行时行为？

前端地图走到这里，parser 已经给我们留下一棵 Syntax 树。下一步就打开它，看看每个构造子究竟装着什么。遇到陌生代码时，不要只问它“是什么意思”；先问它接收什么数据、留下什么数据，以及它运行在哪一个阶段。
