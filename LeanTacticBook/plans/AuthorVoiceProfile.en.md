# Author Voice Profile for *Lean 4 Automation Internals*

Status: working English style specification. This document is based on all of Ch02 and on Ch03 through the paragraph immediately before the Macro information-extraction API table. Ch03 from that table onward is treated only as a negative language sample. It is not evidence about the author's voice.

## 1. The governing distinction

The author's prose is not defined by first person, jokes, short sentences, or a ban on tables. Its strongest signature is the way a sentence participates in a reader's act of discovery.

A characteristic passage does one or more of the following:

- turns a concrete desire into the next construction;
- follows an input through an actual parser, macro, or proof step;
- identifies the one tempting inference that would be wrong;
- spends words on a hidden boundary and omits what the reader can now derive;
- returns to an earlier example and repays an explanatory debt;
- hands a step to the reader exactly when the previous examples have made it derivable.

The prose becomes unlike the author when it organizes information primarily for coverage: complete taxonomies, evenly weighted entries, repeated role summaries, and explanations that restate code without changing the reader's model.

## 2. Narrator and reader

The narrator is present, but not as a decorative host. First person usually records an actual design choice or desire:

- “If I do not want to write a list…”
- “If I want to accept both forms…”
- “We can immediately think of a simple solution…”

Second person usually transfers a specific inference:

- “You can work out for yourself why `SUBR` is right-associative.”
- “Do you remember the `term:max+` trick from the previous chapter?”

The author rarely uses the reader as an audience for generic announcements. Avoid “we will explore,” “you will learn,” and “let us now examine” unless the sentence names a concrete action that begins immediately.

### Operational rule

Use **I** for an authorial choice, interface preference, or honest limitation. Use **you** when the reader can now perform a named inference or experiment. Use **we** when author and reader are carrying out the same derivation. Remove pronouns that merely make neutral exposition sound conversational.

## 3. Lexicon: ordinary verbs carrying technical mechanisms

The prose prefers physical, directional verbs over abstract service nouns. A parser “reads,” “keeps going,” “stops,” “consumes,” “fails,” or “falls into” another branch. A macro “wraps,” “packs,” “matches,” “replaces,” “throws,” or “calls itself.” A proof step “splits” a goal or “closes” it.

These verbs are not simplifications of the mechanism. They expose the mechanism's state changes. Prefer:

> The first branch has already consumed the left parenthesis when it fails, so the second branch can no longer start from the original input.

Over:

> `atomic` provides rollback behavior for alternative parsing.

The API name belongs after the action has become intelligible.

## 4. Sentence rhythm

The positive Chinese samples have a deliberately uneven rhythm. A very short sentence may open a new trial:

> 三次方程仍旧：

It may be followed by a long sentence that tracks a complete causal chain. The long sentence is allowed because each clause corresponds to another state transition in the computation.

Measured over the prose samples, positive sentences are both longer and more variable than the later AI text. The useful lesson is not a target number. It is the alternation:

1. short claim or question;
2. code or concrete object;
3. long causal explanation where needed;
4. short consequence, exercise, or transition.

Do not regularize this into uniformly medium-length sentences. Do not split a causal trace merely to reduce sentence length.

## 5. Transitions arise from desire, not document management

Characteristic transitions include:

- “Sometimes we may want…”
- “Or suppose we want…”
- “If I want both forms…”
- “Perhaps you are wondering whether…”
- “The repeated pattern has now appeared…”

They move because the current interface is inconvenient or the current example exposes a gap. Weak transitions merely manage the manuscript:

- “This section demonstrates…”
- “The following table lists…”
- “This is the classification map used below…”
- “Next we distinguish four roles…”

A heading already manages the document. The first paragraph should begin the intellectual action.

## 6. Deictic and local reference

The author often says “this version,” “that recursive call,” “this whole block,” or “these two forms.” Such expressions work because the referent is physically close and concrete. They produce the feeling of reading code together.

Do not replace every local reference with a full technical noun phrase. Repetition of full names can make a passage sound like generated documentation. Conversely, never use “this” when the preceding paragraph contains several plausible referents.

## 7. Correction words are functional

Words such as “actually,” “in fact,” and “that is” occur often in the positive sample. They should not be removed mechanically. They usually mark one of three real corrections:

1. another layer of desugaring;
2. a parse that differs from its surface appearance;
3. a boundary between syntax and semantics.

A correction marker is valid only when the reader can name the model being corrected. Delete it when the following sentence merely restates an ordinary fact.

## 8. Technical terms enter at the point of need

A term normally arrives after an ordinary-language action has made it necessary:

- the left side is a **pattern**;
- the right side is an **expansion**;
- `$roots:term*` captures repeated children, hence a **repeated antiquotation splice**;
- the macro cannot inspect the goal, hence the transition to `TacticM`.

Avoid opening with a formal definition whose role has not yet been earned. A finite object whose motivation is already established, such as the constructors of `Syntax`, may be listed directly and then grounded with a concrete construction.

## 9. Humor is attached to a technical fact

Good examples include:

- “Macros are intelligence!” after the compression analogy;
- “the least sugary version” while removing syntax sugar;
- “dig it out of the pile of code” when explaining the maintenance cost of a closed definition;
- “because surely this can be inferred from the proposition” when motivating the boundary of `MacroM`.

Each line names a real compression, implementation level, maintenance cost, or interface desire. Do not manufacture personality with isolated “this is easy,” “interestingly,” or “magic.” A joke must either compress a concept, expose a pain point, or motivate the next move.

## 10. Omission is part of the voice

The author does not explain every line that can be reconstructed from established principles. After one or two demonstrations, the prose may say that the rest is an exercise, provide a reference table, or show real source code without translating it line by line.

The omission test is strict:

- If the reader can derive the point compositionally from material already taught, omit it.
- If a plausible but wrong model would produce the wrong answer, state the correction.
- If the text introduces a genuinely new principle, explain it even when the code looks short.

This is why the terse `rewrite` and `simp` treatments in Ch02 are positive models, while the indentation boundary in `induction` receives an extra explanation.

## 11. Paragraph shape

A characteristic explanatory paragraph often has this internal motion:

1. name a concrete input or desired interface;
2. follow what Lean does;
3. stop at the surprising branch, failure, or mismatch;
4. state the mechanism that explains it;
5. optionally return one step to show what the mechanism also explains.

A paragraph need not display all five stages, but its clauses should form a causal path. Avoid paragraphs whose sentences are merely sibling facts.

## 12. Negative language patterns after the Ch03 API table

The later AI text contains useful information, but its language is a negative sample for future drafting.

### 12.1 Repeated explanations under new headings

The boundary of macros is explained before the API table, then restated in the table discussion, again in “What macros know,” and again in “The first boundary.” Multiple-rule ordering and `trivial` likewise reappear after they have already done their teaching work.

Before adding a section, ask whether it changes the reader's model. If it only recategorizes established facts, merge it into the earlier explanation or remove it.

### 12.2 Taxonomy before need

Phrases such as “macros mainly perform four roles” create a complete map before the reader has asked for one. Taxonomies are appropriate as references after the generative principle is known, not as repeated narrative spines.

### 12.3 Uniform explanatory units

The AI text often uses one compact paragraph per feature, each with a source fact, a scope qualification, and a forward reference. The units are polished but interchangeable. The authorial prose gives unequal space to unequal difficulties.

### 12.4 Manual-like restatement

Negative passages translate every syntax component into prose even when the reader can already read it. This delays the next discovery. Explain only the non-compositional part.

### 12.5 Formal hedging and semicolon packing

The later text relies more heavily on semicolons, scope qualifiers, “accurately speaking,” “usually,” and balanced exclusions. These are useful when the distinction is load-bearing. Repeated use makes the prose sound like an audit report rather than a book being taught aloud.

### 12.6 Manufactured vividness

Phrases such as “a very plain disaster,” “six unrelated magic spells,” and “debugging becomes comical” try to add life after the exposition has already become static. The author's humor normally causes or explains a transition; it is not pasted onto a completed explanation.

## 13. English-first drafting protocol

Future prose should begin with an English Markdown draft because the model writes clearer actions and causal movement in English. This English file is temporary semantic scaffolding, not the source of a future English edition.

### Step 1: Write the reader-state brief

Before prose, record:

- what the reader can already do;
- what they currently want to do;
- what they can safely infer;
- what misconception is likely;
- what new ability or payoff closes the section.

### Step 2: Write the English teaching draft

Use direct English verbs and explicit subjects. Prefer an executable example over a preliminary taxonomy. Let interface pressure reveal the abstraction. Keep reference material separate from the narrative.

### Step 3: Produce a complete Chinese initial draft

The Chinese version must preserve each paragraph's teaching job and factual content, but it need not preserve English clause order, pronouns, articles, passives, or connective words.

Common repairs:

- English passive → explicit Chinese actor or event sequence;
- abstract noun → concrete verb;
- “This means that…” → state the consequence directly;
- long pre-nominal modifier → move the condition into an earlier clause;
- repeated “however/therefore/additionally” → retain only the logical relations the Chinese paragraph actually needs;
- English copular definition → action-first Chinese when a mechanism is being explained.

The result must be complete prose rather than an expanded outline. Once the Chinese draft exists, it becomes the working text; the temporary English may remain as process evidence but no longer constrains later Chinese revision.

### Step 4: Recover the real semantic dynamic

Read the Chinese draft without trusting the outline. Record what the section actually does: where desire changes, ability compounds, an example leaves a residual problem, reference material becomes legitimate, or a boundary forces the next abstraction. Revise the plan to describe this real movement instead of forcing the prose back into the original outline.

### Step 5: Refine every sentence by action

Assign every sentence a job such as motivate, operate, trace, surprise, diagnose, correct, name, delimit, repay, transfer, exercise, or handoff. Delete or rewrite sentences with no unique action. Then run necessity, precision, cadence, and authorial-relation passes repeatedly.

### Step 6: Run the Feynman learner pipeline

Only after sentence-level refinement, give the section to isolated zero-prior learners. Repair the earliest cause of every misunderstanding without adding encyclopedia patches. Repeat sentence audit and learner replay until two consecutive hostile rounds find no new substantive problem.

## 14. Draft lifecycle, explanation budgets, and later English publication

The working lifecycle is:

```text
section brief → outline → temporary English semantic draft
→ complete Chinese initial draft → sentence-action refinement
→ Feynman learner loops → final user-edited Chinese
```

The final Chinese may diverge completely from the temporary English. No paragraph map or bilingual-isomorphism requirement applies.

### Explanation budgets

- **B0, no explanation**: established principles determine the result; keep only code or a reference.
- **B1, one corrective sentence**: the reader can almost derive it but may continue with one specific wrong model.
- **B2, local explanation**: the current example introduces a new mechanism without requiring its full implementation.
- **B3, trace or counterexample**: use for associativity, rollback order, phase boundaries, post-failure state, hygiene, or another error that would persist into later chapters.

Assign a budget by asking whether the reader can derive the point reliably, whether a mistake would survive, and whether later examples immediately reuse the explanation. Do not assign equal space merely because several APIs appear in the same declaration.

When an English edition is eventually published, translate afresh from the final user-edited Chinese and build a separate English Verso source. The early English draft is not canonical and must not be used to overwrite later Chinese decisions.

## 15. Miniature bilingual model

### English draft

The repeated pattern has now appeared. The quadratic and cubic proofs perform the same two steps; only the polynomial, the roots, and the variable change. A fixed macro template still cannot handle both examples because the number of factors changes. The simplest repair is to pass the roots as a list and build

\[
\prod_i (x-r_i).
\]

Before writing the macro, let us rewrite the cubic proof in that form. This checks that the representation really removes the difference we intend to abstract away.

### Chinese translation

现在重复模式已经出现了。二次和三次证明都只做两步，变化的只有多项式、根和变量；但因式数量不同，还不能直接塞进同一个固定模板。最简单的办法是让调用者传入根列表，再统一构造

\[
\prod_i(x-r_i).
\]

先别急着写宏。我们先把三次证明改成这个形式，确认根列表确实消掉了我们想抽象的差异。

The Chinese version does not mirror every English clause. It restores the author's cadence: a short observation, a compressed contrast, the mathematical object, then a concrete next action.
