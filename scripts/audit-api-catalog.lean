import LeanTacticBook.Helpers

open Lean Elab Command

private structure CatalogSpec where
  title : String
  source : Name

private def catalogSpecs : Array CatalogSpec := #[
  ⟨"名称操作", `Lean.Data.Name⟩,
  ⟨"宇宙层级", `Lean.Level⟩,
  ⟨"核心表达式", `Lean.Expr⟩,
  ⟨"语法树", `Lean.Syntax⟩,
  ⟨"环境与声明", `Lean.Environment⟩,
  ⟨"局部上下文", `Lean.LocalContext⟩,
  ⟨"元变量上下文", `Lean.MetavarContext⟩,
  ⟨"消息", `Lean.Message⟩,
  ⟨"异常", `Lean.Exception⟩,
  ⟨"日志", `Lean.Log⟩,
  ⟨"CoreM 与基础服务", `Lean.CoreM⟩,
  ⟨"选项", `Lean.Data.Options⟩,
  ⟨"环境 monad 接口", `Lean.MonadEnv⟩,
  ⟨"回溯状态", `Lean.Util.MonadBacktrack⟩,
  ⟨"声明安装", `Lean.AddDecl⟩,
  ⟨"基础元编程定义", `Init.Meta.Defs⟩,
  ⟨"Lean.Meta 完整模块族", `Lean.Meta⟩,
  ⟨"项 elaboration", `Lean.Elab.Term⟩,
  ⟨"TacticM 与目标管理", `Lean.Elab.Tactic⟩
]

private def requiredLegacyDecls : Array Name := #[
  `Lean.MonadEnv.getEnv,
  `Lean.MonadOptions.getOptions,
  `Lean.mkFreshId,
  `Lean.Meta.inferType,
  `Lean.Meta.isDefEq,
  `Lean.Meta.whnf,
  `Lean.Meta.reduce,
  `Lean.Meta.mkFreshExprMVar,
  `Lean.instantiateMVars,
  `Lean.Meta.forallTelescope,
  `Lean.Meta.lambdaTelescope,
  `Lean.Meta.withLocalDecl,
  `Lean.Meta.mkForallFVars,
  `Lean.Meta.mkLambdaFVars,
  `Lean.Meta.kabstract,
  `Lean.Meta.isProof,
  `Lean.Meta.isProp,
  `Lean.Meta.synthInstance?,
  `Lean.Meta.synthInstance,
  `Lean.Meta.isInstance,
  `Lean.Meta.mkAppM,
  `Lean.Meta.mkConstWithFreshMVarLevels,
  `Lean.Meta.mkEqRefl,
  `Lean.withoutModifyingState,
  `Lean.MonadWithOptions.withOptions,
  `Lean.Meta.withNewLocalInstance,
  `Lean.Elab.Term.elabTerm,
  `Lean.Elab.Term.elabType,
  `Lean.Elab.Tactic.getMainGoal,
  `Lean.Elab.Tactic.getMainTarget,
  `Lean.Elab.Tactic.getGoals,
  `Lean.Elab.Tactic.setGoals,
  `Lean.Elab.Tactic.getUnsolvedGoals,
  `Lean.Elab.Tactic.replaceMainGoal,
  `Lean.Elab.Tactic.closeMainGoal,
  `Lean.MVarId.assign,
  `Lean.MVarId.getType,
  `Lean.MVarId.isAssigned,
  `Lean.MVarId.intro,
  `Lean.MVarId.withContext,
  `Lean.Elab.Tactic.withMainContext,
  `Lean.MonadLCtx.getLCtx,
  `Lean.Elab.Tactic.focus,
  `Lean.MonadBacktrack.saveState,
  `Lean.MonadBacktrack.restoreState,
  `Lean.Elab.Tactic.tryTactic?,
  `Lean.Elab.Tactic.evalTactic,
  `Lean.Elab.Tactic.liftMetaTactic,
  `Lean.Meta.throwTacticEx,
  `Lean.logInfo,
  `Lean.logWarning,
  `Lean.Meta.ppExpr,
  `Lean.mkConst,
  `Lean.mkApp,
  `Lean.mkApp2,
  `Lean.mkApp3,
  `Lean.mkApp4,
  `Lean.mkAppN,
  `Lean.mkLambda,
  `Lean.mkForall,
  `Lean.mkNatLit,
  `Lean.Expr.getAppFn,
  `Lean.Expr.getAppArgs,
  `Lean.Expr.isApp,
  `Lean.Expr.isConst,
  `Lean.Expr.isForall,
  `Lean.Expr.constName,
  `Lean.Expr.constName?,
  `Lean.mkIdent,
  `Lean.setEnv,
  `Lean.addAndCompile,
  `Lean.Meta.DiscrTree.getMatch
]

private def requiredLegacyTopics : Array String := #[
  "A.1 CoreM", "A.2 MetaM", "A.3 TermElabM", "A.4 TacticM",
  "A.5 错误处理与日志", "A.6 Expr 构造函数", "A.7 Expr 匹配与分析",
  "A.8 Name / Level / Syntax", "A.9 Tactic 声明方式", "A.10 常用属性",
  "A.11 Monad 层级提升", "A.12 Expr 构造子速览", "A.13 按任务查 API",
  "A.14 章节-API 交叉索引", "A.15 进阶 API"
]

private def requiredLegacyWorkflows : Array String := #[
  "读取目标类型", "遍历并检查局部假设", "拆分目标并安装子目标",
  "调用已有 tactic", "构造证明项并补全隐式参数", "管理局部变量",
  "搜索类型类实例", "探测定义等价而不留副作用", "在多个策略间回退"
]

elab "#auditApiCatalog" : command => do
  let env ← getEnv
  let mut seen : NameMap String := {}
  let mut total := 0
  for spec in catalogSpecs do
    let declarations := apiCatalogDeclarations env spec.source
    if declarations.isEmpty then
      throwError "API catalogue group {spec.title} ({spec.source}) is empty"
    for (name, _, _) in declarations do
      if let some previous := seen.find? name then
        throwError "Declaration {name} appears in both {previous} and {spec.title}"
      seen := seen.insert name spec.title
    total := total + declarations.size
    logInfo m!"{spec.title}: {declarations.size}"
  let missingLegacy := requiredLegacyDecls.filter (!seen.contains ·)
  unless missingLegacy.isEmpty do
    throwError "Legacy API declarations missing from generated catalogues: {missingLegacy}"
  let appendix ← IO.FS.readFile "LeanTacticBook/AppendixApiReference.lean"
  let missingTopics := requiredLegacyTopics.filter (!appendix.contains ·)
  unless missingTopics.isEmpty do
    throwError "Legacy topics missing from migration matrix: {missingTopics}"
  let missingWorkflows := requiredLegacyWorkflows.filter (!appendix.contains ·)
  unless missingWorkflows.isEmpty do
    throwError "Legacy task workflows missing from the new appendix: {missingWorkflows}"
  logInfo m!"total: {total}; duplicates: 0; legacy declarations: {requiredLegacyDecls.size}/{requiredLegacyDecls.size}; legacy topics: {requiredLegacyTopics.size}/{requiredLegacyTopics.size}; legacy workflows: {requiredLegacyWorkflows.size}/{requiredLegacyWorkflows.size}"

#auditApiCatalog
