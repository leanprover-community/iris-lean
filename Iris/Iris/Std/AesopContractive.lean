module
public meta import Aesop
public meta import Lean

open Lean Elab Meta

declare_aesop_rule_sets [aesop_contractive]

macro (name := aesop_cat) "aesop_contractive" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop $c* (config := { warnOnNonterminal := true })
            (rule_sets := [$(Lean.mkIdent `aesop_contractive):ident]) (erase Aesop.BuiltinRules.rfl))

-- attribute [simp] Nat.repeat

syntax (name := aesop_contractive_attr) "aesop_contractive " Aesop.attr_rules : attr

open Aesop Frontend

meta def elabConfig (stx : Syntax) : TermElabM AttrConfig :=
  withRef stx do
    match stx with
    | `(attr| aesop_contractive $e:Aesop.rule_expr) => do
      let e ← `(Aesop.rule_expr| (rule_sets := [$(Lean.mkIdent `aesop_contractive):ident]) $e:Aesop.rule_expr)
      let r ← RuleExpr.elab e |>.run $ ← ElabM.Context.forAdditionalGlobalRules
      return { rules := #[r] }
    | `(attr| aesop_contractive [ $es:Aesop.rule_expr,* ]) => do
      let es ← es.getElems.mapM fun e => `(Aesop.rule_expr| (rule_sets := [$(Lean.mkIdent `aesop_contractive):ident]) $e:Aesop.rule_expr)
      let ctx ← ElabM.Context.forAdditionalGlobalRules
      let rs ← (es : Array Syntax).mapM λ e => RuleExpr.elab e |>.run ctx
      return { rules := rs }
    | _ => throwUnsupportedSyntax

meta def auxIfIsNonExpansiveDecl (declName : Name) : TermElabM Name := do
  let decl ← getConstInfo declName
  forallTelescope decl.type fun xs ty => do
    let .const fnName _ := ty.getAppFn | return declName
    let projName ←
      if fnName == `Iris.OFE.NonExpansive ||
         fnName == `Iris.OFE.NonExpansive₂ then
        pure `ne
      else if fnName == `Iris.OFE.Contractive then
        pure `distLater_dist
      else
        do return declName
    let declLvls := decl.levelParams.map Level.param
    let declWithArgs := mkAppN (mkConst declName declLvls) xs
    let proj ←  mkProjection declWithArgs projName
    withDeclNameForAuxNaming declName do
      let auxName ← mkAuxDeclName
      let e ← mkAuxDefinitionFor auxName proj
      trace[aesop] m!"{e}"
      return auxName

meta initialize registerBuiltinAttribute {
    name := `aesop_contractive_attr
    descr := "Adds a given declaration to the ruleset for the `aesop_contractive` tactic."
    applicationTime := .afterCompilation
    add := fun declName stx kind ↦ withRef stx do Aesop.runTermElabMAsCoreM do
      let declName ← auxIfIsNonExpansiveDecl declName
      let config ← elabConfig stx
      let rules ← config.rules.flatMapM (·.buildAdditionalGlobalRules declName)
      for (rule, rsNames) in rules do
        for rsName in rsNames do
          addGlobalRule rsName rule kind (checkNotExists := true)
    erase := λ decl =>
      let ruleFilter :=
        { name := decl, scope := .global, builders := #[], phases := #[] }
      eraseGlobalRules RuleSetNameFilter.all ruleFilter (checkExists := true)
  }
