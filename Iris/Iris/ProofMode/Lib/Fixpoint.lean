/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.BI.Lib.Fixpoint
public meta import Iris.ProofMode.Lib.Monotone
public meta import Lean.Elab.PreDefinition.FixedParams

namespace Iris.Fixpoint
open Lean Elab Command Meta Term

declare_syntax_cat monotoneClause
syntax "monotone_by " Lean.Parser.Tactic.tacticSeq : monotoneClause

declare_syntax_cat nonexpClause
syntax "nonexp_by " Lean.Parser.Tactic.tacticSeq : nonexpClause

/-- Register a closed definition, using its inferred type. -/
meta def emitDef (name : Name) (levels : List Name) (value : Expr) : TermElabM Unit := do
  let value ← instantiateMVars value
  addAndCompile <| .defnDecl {
    name, levelParams := levels, type := ← inferType value, value
    hints := .regular 0, safety := .safe
  }
  saveEqnAffectingOptions name
  enableRealizationsForConst name

/-- A packed expression reifies a list of expressions into a single left-associated Expr.
The `arity` field records the length of the list, to disambiguate `[(x, y)]` from `[x, y]`.
An empty list is packed as `Unit.unit`; a singleton keeps its original expression.
`expr` is the expression is the one we expect to be passed into the fixpoint constuct. -/
structure PackedExpr where
  expr : Expr
  arity : Nat

meta def PackedExpr.unit : PackedExpr where
  expr := mkConst ``Unit.unit
  arity := 0

meta def PackedExpr.pack (xs : Array Expr) : MetaM PackedExpr := do
  if xs.isEmpty then return .unit
  let expr ← xs[1:].foldlM (fun acc x => mkAppM ``Prod.mk #[acc, x]) xs[0]!
  return .mk expr xs.size

meta def PackedExpr.unpack (p : PackedExpr) : MetaM (Array Expr) := do
  if p.arity == 0 then return #[]
  let mut rest := p.expr
  let mut args := []
  for _ in [:p.arity - 1] do
    args := mkProj ``Prod 1 rest :: args
    rest := mkProj ``Prod 0 rest
  return (rest :: args).toArray

/-- The checked body of a recursive function, with its recursive reference bound as a parameter.
The general scheme is to take a recursive-like definition
```
variable (X Y : ..)
def myF (z w : ...) := body
```
and turn it into a single function
```
fun X Y self z w => body[myF := self]
```
Since we know the type of `myF` a priori, we can elaborate this expression and use it in the fixed
parameter analysis. -/
structure CheckedRecursiveBody where
  /-- Number of binders before `self` in `value`: section variables and auto-bound parameters. -/
  numOuter : Nat
  /-- Universe parameters used by `functionType` and `value`. -/
  levelParams : List Name
  /-- Original function type, including outer parameters but excluding the extra `self` binder.
  In the example above: `∀ X Y z w, resultType`. This is not the type of `value`. -/
  functionType : Expr
  /-- Checked body with shape `fun X Y self z w => body`, with no free local variables. -/
  value : Expr

/-- Convert a term `value` with free variables `outer`, where `self` a free variable intended to
refer to `value` itself, and construct a closed term `fun outer self => body` which can be
moved to a fresh context (such as the fixed parameter analysis). -/
meta def closeRecursiveBody (outer : Array Expr) (self value : Expr) :
    TermElabM CheckedRecursiveBody := do
  let functionType ← levelMVarToParam (← instantiateMVars (← mkForallFVars outer (← inferType self)))
  let value ← levelMVarToParam (← instantiateMVars (← mkLambdaFVars (outer.push self) value))
  let levelParams := (collectLevelParams (collectLevelParams {} functionType) value).params.toList
  if functionType.hasMVar || value.hasMVar then
    throwError "ifix: unresolved metavariables in the recursive body"
  if functionType.hasFVar || value.hasFVar then
    throwError "ifix: unbound variables in the recursive body"
  return { numOuter := outer.size, levelParams, functionType, value }

/-- Elaborate `name (binders) : ty := body` in the current context, and produce a closed recursive
body representing `fun context (self : ∀ binders, ty) binders => body`. -/
meta def elaborateBody (name : Ident) (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder))
    (ty body : Term) : CommandElabM CheckedRecursiveBody := do
  let signature ← if binders.isEmpty then pure ty else `(∀ $binders*, $ty)
  let bodyFn ← if binders.isEmpty then pure body else do
    let funBinders : TSyntaxArray ``Lean.Parser.Term.funBinder := binders.map fun b => ⟨b.raw⟩
    `(fun $funBinders* => $body)
  let fullName := (← getCurrNamespace) ++ name.getId
  runTermElabM fun sectionVars => withAutoBoundImplicit do
    -- Elaborate the full signature of the declaration (allowing autobound implicits).
    let selfType ← elabType signature
    synthesizeSyntheticMVarsNoPostponing
    let outer ← addAutoBoundImplicits sectionVars none
    withoutAutoBoundImplicit <| withAuxDecl name.getId selfType fullName fun self => do
      -- Elaborate the body, in a context which adds the free variable (self : ∀ binders, ty)
      let value ← elabTermEnsuringType bodyFn selfType
      synthesizeSyntheticMVarsNoPostponing
      closeRecursiveBody outer self (← instantiateMVars value)

/-- Use Lean's fixed parameter analysis to determine which arguments to a potentially recursive
function are potentially modified in a body. A parameter is fixed only if every recursive reference
supplies it unchanged (up to definitional equality); missing arguments are varying.

Returns a `FixedParamPerm`, Lean's datatype to describe which parameters are fixed vs varying.

To reuse Lean's analysis, we introduce a new context containing an axiom for the potentially
recursive function. This axiom only exists in the context of this analysis. -/
meta def identifyFixedParameters (checked : CheckedRecursiveBody) : MetaM FixedParamPerm :=
  withoutModifyingEnv do
    let recursiveName ← mkFreshUserName `recursive
    let levels := checked.levelParams.map mkLevelParam
    addDecl <| .axiomDecl {
      name := recursiveName, levelParams := checked.levelParams
      type := checked.functionType, isUnsafe := false
    }
    let value ← lambdaBoundedTelescope checked.value checked.numOuter fun outer body => do
      let recRef := mkAppN (mkConst recursiveName levels) outer
      mkLambdaFVars outer (mkApp body recRef).headBeta
    let preDef : PreDefinition := { (default : PreDefinition) with
      declName := recursiveName, levelParams := checked.levelParams
      type := checked.functionType, value }
    let perms ← getFixedParamPerms #[preDef]
    return perms.perms[0]!

section FixedParameterExamples

/- ## Example: Determimining fixed vs varying parameters

Recall that a `FixedParamPerm` is an array of `Option Nat`, with size equal to the arity of the
function under test. A `none` value means this parameter is varying, a `some i` value means the
parameter is the `i`th fixed parameter.

This section tests `closeRecursiveBody`, `elaborateBody` and `identifyFixedParameters`, in order
to demonstrate the parameter analysis used for the Iris fixpoint analysis.
-/

meta def expectFixedParameters (decl : TSyntax `command) (expected : FixedParamPerm) :
    CommandElabM Unit := do
  let `(command| def $name:ident $binders:bracketedBinder* : $ty := $body) := decl
    | throwUnsupportedSyntax
  let checked ← elaborateBody name binders ty body
  let actual ← liftTermElabM <| identifyFixedParameters checked
  unless actual == expected do
    throwErrorAt decl "expected {repr expected}, got {repr actual}"

-- `n` is unchanged, so is fixed.
run_cmd do
  expectFixedParameters (← `(command| def unchanged (n : Nat) : Nat := unchanged n))
    #[some 0]

-- `n` is changed, so is variable.
run_cmd do
  expectFixedParameters (← `(command| def changed (n : Nat) : Nat := changed (n + 1)))
    #[none]

-- Fixed parameters can be interleaved with varying ones.
run_cmd do
  expectFixedParameters (← `(command|
    def mixed (x setting y : Nat) : Nat := mixed y setting x))
    #[none, some 0, none]

-- Two non-defeq calls marks the parameter as varying.
run_cmd do
  expectFixedParameters (← `(command|
    def both (n : Nat) : Nat := both n + both (n + 1)))
    #[none]

end FixedParameterExamples

/-- Parameters available to a declaration body, classified by their behavior.
- The parameters that are fixed by the body
- The parameters that are not guaranteed to remain fixed
- The original array of all of the parameters
- The resulting type of the expression
-/
structure Parameters where
  fixed : Array Expr
  varying : Array Expr
  originalOrder : Array Expr
  resultType : Expr

/-- Introduce local variables from the function type and execute `k` with their classification.
Any expression returned or saved beyond `k` must bind the local variables it contains, including
references inside `resultType`. Inside `k`, those variables may be used freely. -/
meta def withParameters (checked : CheckedRecursiveBody) (perm : FixedParamPerm)
    (k : Parameters → TermElabM α) : TermElabM α := do
  -- Open the fixed parameters
  perm.forallTelescope checked.functionType fun fixed => do
    -- Substitute the fixed variables into the function type, leaving the varying binders.
    let varyingType ← perm.instantiateForall checked.functionType fixed
    -- Introduce local variables for the varying parameters.
    forallTelescope varyingType fun varying resultType =>
      -- Apply the continuation k with the opened and specialized fvars
      k { fixed, varying, resultType, originalOrder := perm.buildArgs fixed varying }

--  TODO: Continue reviewing from here

/-- Replace `self` with a function taking only the varying arguments.
Returns the updated function `fun self varying => body`: fixed parameters are stripped from all
call sites, and must be closed over. -/
meta def abstractRecursion (checked : CheckedRecursiveBody) (perm : FixedParamPerm)
    (params : Parameters) : MetaM Expr := do
  let selfType ← perm.instantiateForall checked.functionType params.fixed
  withLocalDeclD `self selfType fun self => do
    let outer := params.originalOrder.extract 0 checked.numOuter
    let args := params.originalOrder.extract checked.numOuter params.originalOrder.size
    let saved := (mkAppN checked.value outer).headBeta
    lambdaBoundedTelescope saved 1 fun recursive value => do
      let #[originalSelf] := recursive | throwError "ifix: missing recursive binder"
      let value := (mkAppN value args).headBeta
      let value ← Meta.transform (skipConstInApp := true) value fun e => e.withApp fun f args => do
        if f == originalSelf then
          return .continue (mkAppN self (perm.pickVarying (outer ++ args)))
        return .continue
      mkLambdaFVars #[self] (← mkLambdaFVars params.varying value)

/-- Ordinary products require independent argument types and an independent result type. -/
meta def checkIndependentArguments (params : Parameters) : MetaM Unit := do
  for arg in params.varying do
    for previous in params.varying do
      if (← inferType arg).containsFVar previous.fvarId! then
        throwError "ifix: dependent varying parameters are not supported"
    if params.resultType.containsFVar arg.fvarId! then
      throwError "ifix: the result type depends on a varying parameter"

/-- Convert the curried functional to `fun self tuple => body`, using the shared tuple layout. -/
meta def packArguments (functional : Expr) (params : Parameters) : MetaM Expr := do
  checkIndependentArguments params
  let tuple ← PackedExpr.pack params.varying
  let dom ← inferType tuple.expr
  let selfType ← mkArrow dom params.resultType
  withLocalDeclD `self selfType fun self => do
    let curriedSelf ← mkLambdaFVars params.varying (mkApp self tuple.expr)
    withLocalDeclD `args dom fun args => do
      let unpacked ← PackedExpr.unpack { tuple with expr := args }
      let value := mkAppN (mkApp functional curriedSelf) unpacked
      mkLambdaFVars #[self, args] value.headBeta

/-- Save the curried functional as `.pre`, or its packed adapter as `.pre'`. -/
meta def emitFunctional (name : Name) (levels : List Name) (params : Parameters)
    (functional : Expr) (suffix : Name := `pre) : TermElabM Expr := do
  emitDef (name ++ suffix) levels (← mkLambdaFVars params.fixed functional)
  return mkAppN (mkConst (name ++ suffix) (levels.map mkLevelParam)) params.fixed

structure ProofClauses where
  monotone : TSyntax ``Lean.Parser.Tactic.tacticSeq
  nonexp : TSyntax ``Lean.Parser.Tactic.tacticSeq

/-- Read proof clauses before generating any declarations. -/
meta def readProofClauses (mono : Option (TSyntax `monotoneClause))
    (ne : TSyntax `nonexpClause) : CommandElabM ProofClauses := do
  let monotone ← match mono with
    | some clause =>
      let `(monotoneClause| monotone_by $tac) := clause | throwUnsupportedSyntax
      pure tac
    | none => `(Lean.Parser.Tactic.tacticSeq| monotone)
  let `(nonexpClause| nonexp_by $nonexp) := ne | throwUnsupportedSyntax
  return { monotone, nonexp }

/-- Check the user's proofs of monotonicity and nonexpansiveness for the packed functional. -/
meta def proveRequirements (pre : Expr) (clauses : ProofClauses) : TermElabM Expr := do
  let monoType ← mkAppM ``BIMonoPred #[pre]
  let monoTac := clauses.monotone
  let neTac := clauses.nonexp
  let proof ← elabTermEnsuringType (← `(term| {
    mono_pred := by $monoTac
    mono_pred_ne := by $neTac
  })) monoType
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars proof

/-- Prove the unfolding equation using the chosen Iris fixpoint theorem. -/
meta def emitUnfolding (name unfolding : Name) (levels : List Name) (params : Parameters)
    (pre packed : Expr) : TermElabM Unit := do
  let tuple ← PackedExpr.pack params.varying
  let lhs := mkAppN (mkConst name (levels.map mkLevelParam)) params.originalOrder
  let recursiveFunction ← mkLambdaFVars params.varying lhs
  let rhs := mkAppN (mkApp pre recursiveFunction) params.varying
  let eqType ← mkEq lhs rhs
  let mono := mkAppN (mkConst (name ++ `pre_mono) (levels.map mkLevelParam)) params.fixed
  let proof := mkApp2 (← mkAppM unfolding #[packed]) tuple.expr mono
  unless ← isDefEq (← inferType proof) eqType do
    throwError "ifix: unexpected unfolding theorem type"
  addDecl <| .thmDecl {
    name := name ++ `unfold, levelParams := levels
    type := ← mkForallFVars params.originalOrder eqType
    value := ← instantiateMVars (← mkLambdaFVars params.originalOrder proof)
  }

/-- Register the proved instance, the requested fixpoint, and its unfolding theorem. -/
meta def emitDefinitions (fixpoint unfolding name : Name) (levels : List Name)
    (params : Parameters) (pre packed proofs : Expr) : TermElabM Unit := do
  emitDef (name ++ `pre_mono) levels (← mkLambdaFVars params.fixed proofs)
  registerInstance (name ++ `pre_mono) .global 1000
  let fixedPoint ← mkAppM fixpoint #[packed]
  let tuple ← PackedExpr.pack params.varying
  let call := mkApp fixedPoint tuple.expr
  emitDef name levels (← mkLambdaFVars params.originalOrder call)
  emitUnfolding name unfolding levels params pre packed

meta def elaborate (fixpoint unfolding : Name) (name : Ident)
    (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (ty body : Term)
    (mono : Option (TSyntax `monotoneClause)) (ne : TSyntax `nonexpClause) : CommandElabM Unit := do
  let clauses ← readProofClauses mono ne
  let checked ← elaborateBody name binders ty body
  let fixedParams ← liftTermElabM <| identifyFixedParameters checked
  let finalName := (← getCurrNamespace) ++ name.getId
  liftTermElabM <| withParameters checked fixedParams fun params => do
    let functional ← abstractRecursion checked fixedParams params
    let pre ← emitFunctional finalName checked.levelParams params functional
    let packed ← packArguments pre params
    let pre' ← emitFunctional finalName checked.levelParams params packed `pre'
    let proofs ← proveRequirements pre' clauses
    emitDefinitions fixpoint unfolding finalName checked.levelParams params pre pre' proofs

/-- Least Iris fixpoint using elaborated fixed-parameter analysis. -/
elab "ifix " name:ident binders:bracketedBinder*
    " : " ty:term " := " body:term mono:(monotoneClause)? ne:nonexpClause : command =>
  elaborate ``bi_least_fixpoint ``least_fixpoint_unfold name binders ty body mono ne

/-- Greatest Iris fixpoint using elaborated fixed-parameter analysis. -/
elab "icofix " name:ident binders:bracketedBinder*
    " : " ty:term " := " body:term mono:(monotoneClause)? ne:nonexpClause : command =>
  elaborate ``bi_greatest_fixpoint ``greatest_fixpoint_unfold name binders ty body mono ne

end Iris.Fixpoint
