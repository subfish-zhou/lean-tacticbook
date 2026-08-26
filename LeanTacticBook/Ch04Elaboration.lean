## 升级三：不写 `in x`
%%%
tag := "macro-poly-roots-infer-variable"
%%%

调用者确实不该重复写目标里已经明确出现的 `x`。但纯宏只看见自己的调用语法，无法看见目标 `x = 2 ∨ x = 3`，所以这一步不能再靠模板替换。我们保留同一个宏核心，在表面增加 tactic elaborator：

```anchor macro_poly_roots_infer_variable
syntax "poly_roots₂ " term " with " term:max+ : tactic

elab_rules : tactic
  | `(tactic| poly_roots₂ $poly:term with $suppliedRoots:term*) => withMainContext do
      let target ← instantiateMVars (← getMainTarget)
      let some (x, roots) := rootsAndVariable? (rootConclusion target)
        | throwError "poly_roots₂: expected a disjunction of equations with one common variable"
      if roots.size != suppliedRoots.size then
        throwError "poly_roots₂: the number of supplied roots does not match the target"
      let x ← Term.exprToSyntax x
      let roots : TSyntaxArray `term := suppliedRoots
      let rootList ← `(term| [$roots,*])
      evalTactic (← `(tactic| poly_roots_core $poly with $rootList in $x))

example (x : ℚ) (h : x^2 - 5*x + 6 = 0) : x = 2 ∨ x = 3 := by
  poly_roots₂ x^2 - 5*x + 6 with 2 3
```

这里省略了辅助函数的机械细节；它把右结合的 `Or` 展平为若干等式，检查每个等式左边是不是同一个表达式，再把这个公共表达式作为 `x`。这已经是目标驱动的程序，因此类型是 `TacticM`，不再是 `MacroM`。

## 升级四：连 `with` 也不写
%%%
tag := "macro-poly-roots-infer-all"
%%%

目标本身已经写着 `x = 2 ∨ x = 3`，所以验证这个目标时，根也可以从析取右侧读取。双条件命题中的多项式来自左侧等式；只有根析取作为目标时，elaborator 就在局部上下文中寻找包含同一变量的多项式等式：

```anchor macro_poly_roots_infer_all
syntax "poly_roots" : tactic

elab_rules : tactic
  | `(tactic| poly_roots) => withMainContext do
      let target ← instantiateMVars (← getMainTarget)
      let some (x, roots) := rootsAndVariable? (rootConclusion target)
        | throwError "poly_roots: expected a disjunction of equations with one common variable"
      let some poly := sourcePolynomial? target x (← getLCtx)
        | throwError "poly_roots: expected a polynomial equation in the target or local context"
      let poly ← Term.exprToSyntax poly
      let x ← Term.exprToSyntax x
      let rootList ← mkRootListSyntax roots
      evalTactic (← `(tactic| poly_roots_core $poly with $rootList in $x))

example (x : ℚ) (h : x^2 - 5*x + 6 = 0) : x = 2 ∨ x = 3 := by
  poly_roots
```

三次和四次的调用也只剩 tactic 名：

```anchor macro_poly_roots_cubic
example (x : ℚ) :
    x^3 - 6*x^2 + 11*x - 6 = 0 ↔
      x = 1 ∨ x = 2 ∨ x = 3 := by
  poly_roots
```

```anchor macro_poly_roots_quartic
example (x : ℚ) :
    x^4 - 10*x^3 + 35*x^2 - 50*x + 24 = 0 ↔
      x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by
  poly_roots
```

这里要准确区分“省略根参数”和“自动求根”。这个 elaborator 没有从系数算出 `2` 和 `3`；它从待证命题 `x = 2 ∨ x = 3` 中读出候选根，再用 `ring` 验证因式分解。证明 tactic 必须接受一个已经给定的目标，不能把目标中的问号改写成自己猜出的定理陈述。

若要真正从系数计算答案，需要另一个算法层：把表达式识别为一元多项式，提取系数，按底层类型选择有理根搜索或二次公式，再生成待验证的候选。二次公式还会遇到定义域问题：例如在 `ℚ` 上判别式未必有平方根，在 `ℝ` 上答案又包含 `Real.sqrt` 及相应边界条件。Mathlib 当前没有一个通用 tactic 能把任意二次、三次或四次表达式直接变成这种根析取；这已经不是宏压缩，而是一个专门的符号求解器。

现有实现根据根构造因式乘积，再由 `ring` 验证多项式恒等式，由 `mul_eq_zero` 和 `sub_eq_zero` 生成完整的根析取。它当前只直接支持*首一多项式*；非首一情形还需要额外接受或推断非零首项系数。

责任要划清：

- parser 识别 `poly_roots₁ ...`、`poly_roots₂ ...` 或 `poly_roots` 的调用结构；
- `poly_roots₁` 宏只负责捕获语法、生成根列表并调用共同核心；
- `poly_roots₂` 和 `poly_roots` elaborator 读取目标与局部上下文，再生成对共同核心的调用；
- `ring`、`mul_eq_zero` 和 `sub_eq_zero` 承担数学语义；
- 内核检查最后的证明项。

宏和 elaborator 都没有“看懂”二次公式。候选根写错时，它们仍会生成同样形状的因式分解检查，后面的 `ring` 失败。这样更安全：前端负责省字和读取证明现场，证明仍由可信检查链验收。

若直接展开 `List.map` 或 `List.prod`，目标会过早暴露为 `List.foldr`，妨碍后续的 `ring` 和零乘积化简。末尾不加 `try`，候选根错误时就让 tactic 当场失败，而不是静默留下未解决目标。对列表字面量，这个版本可以直接处理任意有限个候选根。
