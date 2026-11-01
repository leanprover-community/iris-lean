/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Markus de Medeiros
-/
module

public import Iris.BI.Lib.Lattice
public import Iris.ProofMode.Lib.Monotone
public meta import Lean.Elab.PreDefinition.PartialFixpoint
public meta import Lean.Elab.PreDefinition.FixedParams

/-! # Iris fixpoint commands

`ifix` and `icofix` define least and greatest Iris fixpoints with `partial_fixpoint`, using the
orders in `Iris.BI.Lib.Lattice`, and derive their Iris (co)induction principles from
`fix_iter`/`fix_coiter`.

`iguarded` defines a guarded fixpoint with `OFE.fixpoint`, after elaborating the body itself and
running Lean's fixed-parameter analysis on it. -/

namespace Iris.Fixpoint
open Lean Elab Command Meta Term BI

declare_syntax_cat monotoneClause
syntax "monotone_by " Lean.Parser.Tactic.tacticSeq : monotoneClause

declare_syntax_cat contractiveClause
syntax "contractive_by " Lean.Parser.Tactic.tacticSeq : contractiveClause

/-! ## `ifix` and `icofix` -/

/-- Add a definition, using its inferred type. Its body is exposed to other modules, which unfold
the generated definitions. -/
meta def emitDef (name : Name) (levels : List Name) (value : Expr) : TermElabM Unit := do
  let value ← instantiateMVars value
  let decl := .defnDecl {
    name, levelParams := levels, type := ← inferType value, value
    hints := .regular 0, safety := .safe }
  addDecl decl (forceExpose := true)
  compileDecl decl
  saveEqnAffectingOptions name
  enableRealizationsForConst name

/-- Add a theorem, letting the kernel check `value` against `type`. -/
meta def emitThm (name : Name) (levels : List Name) (type value : Expr) : TermElabM Unit := do
  addDecl <| .thmDecl {
    name, levelParams := levels
    type := ← instantiateMVars type, value := ← instantiateMVars value }

/-- A `partial_fixpoint` definition, opened in a local context where its fixed parameters are
free variables. The definition is `fun fixed => fix F hF` (possibly through `name.mutual`). -/
structure FixpointData where
  /-- `true` for `ifix`, `false` for `icofix`. -/
  least : Bool
  declName : Name
  levels : List Name
  perm : FixedParamPerm
  fixed : Array Expr
  /-- The curried type `∀ varying, PROP` that `fix` works over, and `PROP`. -/
  curriedType : Expr
  prop : Expr
  /-- The functional and its monotonicity proof. -/
  F : Expr
  hF : Expr
  /-- For a non-recursive body, a proof of `fix F hF = name` (they are not definitionally
  equal). For a recursive one, `none`: `name` unfolds to `fix F hF`. -/
  fixEq? : Option Expr := none

namespace FixpointData

meta def us (d : FixpointData) : List Level := d.levels.map mkLevelParam

/-- `name` applied to the fixed parameters and the varying arguments `vs`. -/
meta def fn (d : FixpointData) (vs : Array Expr) : Expr :=
  mkAppN (mkConst d.declName d.us) (d.perm.buildArgs d.fixed vs)

meta def pre (d : FixpointData) : Expr :=
  mkAppN (mkConst (d.declName ++ `pre) d.us) d.fixed

/-- `MonoFn G`, for `G : curriedType → curriedType`. `PROP` is given explicitly: instance search
would look for `BI ?PROP` before `BIPred` determines it. -/
meta def mkMonoFn (d : FixpointData) (G : Expr) : MetaM Expr :=
  mkAppOptM ``MonoFn #[d.prop, d.curriedType, d.curriedType, none, none, none, G]

/-- Rewrite `fix F hF` to `name` in the type of `proof`, for a non-recursive body. -/
meta def rewriteFix (d : FixpointData) (proof : Expr) : MetaM Expr := do
  let some h := d.fixEq? | return proof
  let_expr Eq ty lhs _ := ← inferType h | throwError "ifix: unexpected equation"
  let type ← instantiateMVars (← inferType proof)
  let motive := .lam `f ty (← kabstract type lhs) .default
  mkEqMP (← mkCongrArg motive h) proof

end FixpointData

/-- What `partial_fixpoint` produced for a definition: its fixed parameters, and its value,
`fun fixed => fix F hF` for a recursive body, or `fun params => body` for a non-recursive one, which
`partial_fixpoint` leaves as a plain definition with every parameter fixed. -/
structure DefShape where
  levels : List Name
  perm : FixedParamPerm
  value : Expr
  recursive : Bool

/-- Read the shape of the `partial_fixpoint` definition `declName`. -/
meta def readShape (declName : Name) : MetaM DefShape := do
  if let some info := Lean.Elab.PartialFixpoint.eqnInfoExt.find? (← getEnv) declName then
    let value := (← getConstInfo info.declNameNonRec).instantiateValueLevelParams!
      (info.levelParams.map mkLevelParam)
    return { levels := info.levelParams, perm := info.fixedParamPerms.perms[0]!, value
             recursive := true }
  let info ← getConstInfo declName
  let value := info.instantiateValueLevelParams! (info.levelParams.map mkLevelParam)
  let n ← lambdaTelescope value fun xs _ => pure xs.size
  return { levels := info.levelParams, perm := Array.ofFn fun (i : Fin n) => some i.val, value
           recursive := false }

/-- Open `shape` and run `k` on its fixed parameters, the curried type of its functional, the
functional `F`, and for a recursive body, the monotonicity proof of `F`. A non-recursive body is
the constant functional `fun _ => body`. -/
meta def DefShape.withFunctional (shape : DefShape)
    (k : (fixed : Array Expr) → (curriedType F : Expr) → Option Expr → TermElabM α) :
    TermElabM α := do
  if shape.recursive then
    lambdaBoundedTelescope shape.value shape.perm.numFixed fun fixed body => do
      let_expr Lean.Order.fix curriedType _ F hF := body
        | throwError "ifix: unexpected `partial_fixpoint` definition{indentExpr body}"
      k fixed curriedType F hF
  else
    lambdaTelescope shape.value fun fixed body => do
      let resTy ← inferType body
      k fixed resTy (.lam `self resTy body .default) none

/-- Open the `partial_fixpoint` definition `declName` for `ifix`/`icofix` and run `k` on it. -/
meta def withFixpointData (least : Bool) (declName : Name) (k : FixpointData → TermElabM α) :
    TermElabM α := do
  let shape ← readShape declName
  shape.withFunctional fun fixed curriedType F hF? => do
    let prop ← forallTelescope curriedType fun _ resTy => pure resTy
    let (hF, fixEq?) ← match hF? with
      | some hF => pure (hF, none)
      | none => do
        -- `fix F hF` for the constant `F`; `fix_eq` gives `fix F hF = F (fix F hF)`, whose right
        -- side is the body, that is `name`.
        let inst ← synthInstance (← mkAppM ``Lean.Order.CCPO #[prop])
        let order ← mkAppOptM ``Lean.Order.CCPO.toPartialOrder #[some prop, some inst]
        let hF ← mkAppOptM ``Lean.Order.monotone_const
          #[some prop, some order, some prop, some order, some F.bindingBody!]
        pure (hF, some (← mkAppOptM ``Lean.Order.fix_eq #[some prop, some inst, some F, some hF]))
    k { least, declName, levels := shape.levels, perm := shape.perm, fixed, curriedType, prop, F,
        hF, fixEq? }

/-- `name.pre`: the curried functional built by `partial_fixpoint`. -/
meta def emitPre (d : FixpointData) : TermElabM Unit := do
  emitDef (d.declName ++ `pre) d.levels (← mkLambdaFVars d.fixed d.F)

/-- `name.unfold`: one step of `fix_eq`, stated with `name` and `name.pre`. -/
meta def emitUnfold (d : FixpointData) : TermElabM Unit := do
  let curriedFn ← forallTelescope d.curriedType fun ws _ =>
    mkLambdaFVars (etaReduce := true) ws (d.fn ws)
  forallTelescope d.curriedType fun vs _ => do
    -- A non-recursive `name` unfolds to its body directly.
    let proof ← if d.fixEq?.isSome then mkEqRefl (d.fn vs) else
      vs.foldlM (fun h v => mkAppM ``congrFun #[h, v]) (← mkAppM ``Lean.Order.fix_eq #[d.hF])
    let args := d.perm.buildArgs d.fixed vs
    emitThm (d.declName ++ `unfold) d.levels
      (← mkForallFVars args (← mkEq (d.fn vs) (mkAppN (mkApp d.pre curriedFn) vs)))
      (← mkLambdaFVars args proof)

/-- `name.pre_mono`: the user's proof that the body is monotone, as an instance on `name.pre`.
The goal is stated on the body itself, so the proof can see it. -/
meta def emitPreMono (d : FixpointData) (monoTac : TSyntax ``Lean.Parser.Tactic.tacticSeq) :
    TermElabM Unit := do
  let proof ← elabTermEnsuringType (← `(by $monoTac)) (← d.mkMonoFn d.F)
  synthesizeSyntheticMVarsNoPostponing
  let name := d.declName ++ `pre_mono
  emitThm name d.levels (← mkForallFVars d.fixed (← d.mkMonoFn d.pre))
    (← mkLambdaFVars d.fixed proof)
  addInstance name .global 1000

/-- `∀ vs, body` in the BI, one quantifier per variable. -/
meta def mkBIForalls (vs : Array Expr) (body : Expr) : MetaM Expr :=
  vs.foldrM (fun v body => do mkAppM ``BIBase.forall #[← mkLambdaFVars #[v] body]) body

/-- `name.ind` / `name.coind`: the Iris (co)induction principle `fix_iter`/`fix_coiter`, with its
pointwise wands `wandAll` spelled out as quantifiers over the varying parameters. -/
meta def emitInd (d : FixpointData) : TermElabM Unit := do
  let (lemma, suffix) := if d.least then (``Iris.MonotoneFixpoint.fix_iter, `ind)
    else (``Iris.CoMonotoneFixpoint.fix_coiter, `coind)
  withLocalDeclD `Φ d.curriedType fun Φ => do
  -- `⊢ □ (∀ vs, pre Φ vs -∗ Φ vs) -∗ ∀ vs, name vs -∗ Φ vs`, or the reverse wands for `coind`.
  let (hyp, concl) ← forallTelescope d.curriedType fun vs _ => do
    let (pre, fn, Φ) := (mkAppN (mkApp d.pre Φ) vs, d.fn vs, mkAppN Φ vs)
    let wand (P Q : Expr) := mkAppM ``BIBase.wand (if d.least then #[P, Q] else #[Q, P])
    return (← mkBIForalls vs (← wand pre Φ), ← mkBIForalls vs (← wand fn Φ))
  let stmt ← mkAppM ``BIBase.EmpValid
    #[← mkAppM ``BIBase.wand #[← mkAppM ``BIBase.intuitionistically #[hyp], concl]]
  let proof ← d.rewriteFix (← mkAppOptM lemma
    #[d.prop, none, d.curriedType, none, none, none, d.pre, d.hF, none, Φ])
  emitThm (d.declName ++ suffix) d.levels (← mkForallFVars (d.fixed.push Φ) stmt)
    (← mkLambdaFVars (d.fixed.push Φ) proof)

/-- Elaborate `ifix` (`least := true`) or `icofix`. -/
meta def elabFixpoint (least : Bool) (name : Ident)
    (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (ty body : Term)
    (mono : Option (TSyntax `monotoneClause)) : CommandElabM Unit := do
  let monoTac ← match mono with
    | some clause =>
      let `(monotoneClause| monotone_by $tac) := clause | throwUnsupportedSyntax
      pure tac
    | none => `(Lean.Parser.Tactic.tacticSeq| monotone)
  let ns := if least then `Iris.MonotoneFixpoint else `Iris.CoMonotoneFixpoint
  -- Everything below runs with the matching order on `PROP` in scope.
  elabCommand (← `(command| section))
  try
    elabCommand (← `(command| open scoped $(mkIdent ns):ident))
    let binders ← if ← sectionProvidesBI ty then
        pure (#[← `(bracketedBinder| [BI $ty])] ++ binders)
      else pure binders
    elabDefinition name binders ty body
    dropNotRecursiveWarning
    -- Resolve the actual name, which is mangled in a private scope. If `partial_fixpoint` failed,
    -- it has already reported why.
    let declName ← try liftCoreM <| realizeGlobalConstNoOverload name catch _ => return
    liftTermElabM <| withFixpointData least declName fun d => do
      emitPre d
      emitUnfold d
      emitPreMono d monoTac
      emitInd d
  finally
    elabCommand (← `(command| end))
where
  /-- Define `name` with `partial_fixpoint`. Its monotonicity check rejects partially applied
  recursive calls such as `let next := name x; next y`, so on failure, retry with a proof that
  first reduces the `let`s and then handles bare applications of the recursive function. If that
  fails too, report the errors of the first attempt. -/
  elabDefinition (name : Ident) (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder))
      (ty body : Term) : CommandElabM Unit := do
    let env ← getEnv
    let msgs := (← get).messages
    let hasNewErrors : CommandElabM Bool := do
      let new := (← get).messages.unreported.toArray.extract msgs.unreported.size
      return new.any (·.severity == .error)
    elabCommand (← `(command| def $name:ident $binders* : $ty := $body partial_fixpoint))
    unless ← hasNewErrors do return
    let failed := (← get).messages
    setEnv env
    modify fun s => { s with messages := msgs }
    let tac ← `(Lean.Parser.Tactic.tacticSeq| (try dsimp only); open Lean.Order in
      repeat' (first
        | monotonicity
        | apply Lean.Order.monotone_apply
        | exact Lean.Order.monotone_id))
    elabCommand (← `(command|
      def $name:ident $binders* : $ty := $body partial_fixpoint monotonicity by $tac))
    if ← hasNewErrors then
      setEnv env
      modify fun s => { s with messages := failed }
  /-- `partial_fixpoint` warns about a non-recursive body, but the user never wrote it. -/
  dropNotRecursiveWarning : CommandElabM Unit := do
    let msgs := (← get).messages
    let mut kept := {}
    for m in msgs.unreported do
      unless (← m.data.toString).startsWith "unused `partial_fixpoint`" do kept := kept.push m
    modify fun s => { s with messages := { msgs with unreported := kept } }
  /-- Whether the `BI` instance for `ty` comes from a section variable. The definition then gets
  its own `[BI ty]` binder: a section instance its body does not mention would be dropped, and
  the order on `ty` needs it. -/
  sectionProvidesBI (ty : Term) : CommandElabM Bool :=
    runTermElabM fun _ => do
      let some tyE ← observing? (withoutErrToSorry (elabType ty)) | return false
      let some inst ← synthInstance? (← mkAppM ``BI #[tyE]) | return false
      return inst.isFVar

/-- Least Iris fixpoint, defined with `partial_fixpoint`. -/
elab "ifix " name:ident binders:bracketedBinder* " : " ty:term " := " body:term
    mono:(monotoneClause)? : command =>
  elabFixpoint true name binders ty body mono

/-- Greatest Iris fixpoint, defined with `partial_fixpoint`. -/
elab "icofix " name:ident binders:bracketedBinder* " : " ty:term " := " body:term
    mono:(monotoneClause)? : command =>
  elabFixpoint false name binders ty body mono

/-! ## `iguarded` -/

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
  let functionType ←
    levelMVarToParam (← instantiateMVars (← mkForallFVars outer (← inferType self)))
  let value ← levelMVarToParam (← instantiateMVars (← mkLambdaFVars (outer.push self) value))
  let levelParams := (collectLevelParams (collectLevelParams {} functionType) value).params.toList
  if functionType.hasMVar || value.hasMVar then
    throwError "iguarded: unresolved metavariables in the recursive body"
  if functionType.hasFVar || value.hasFVar then
    throwError "iguarded: unbound variables in the recursive body"
  return { numOuter := outer.size, levelParams, functionType, value }

/-- Elaborate `name (binders) : ty := body` in the current context, and produce a closed recursive
body representing `fun context (self : ∀ binders, ty) binders => body`. Auxiliary definitions, such
as matchers, are named after `name`, and are public when `exporting` is set. -/
meta def elaborateBody (name : Ident) (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder))
    (ty body : Term) (exporting : Bool) : CommandElabM CheckedRecursiveBody := do
  let signature ← if binders.isEmpty then pure ty else `(∀ $binders*, $ty)
  let bodyFn ← if binders.isEmpty then pure body else do
    let funBinders : TSyntaxArray ``Lean.Parser.Term.funBinder := binders.map fun b => ⟨b.raw⟩
    `(fun $funBinders* => $body)
  let fullName := (← getCurrNamespace) ++ name.getId
  runTermElabM fun sectionVars => withExporting (isExporting := exporting) <|
      withDeclName fullName <| withAutoBoundImplicit do
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
      let #[originalSelf] := recursive | throwError "iguarded: missing recursive binder"
      let value := (mkAppN value args).headBeta
      let value ← Meta.transform (skipConstInApp := true) value fun e => e.withApp fun f args => do
        if f == originalSelf then
          return .continue (mkAppN self (perm.pickVarying (outer ++ args)))
        return .continue
      mkLambdaFVars #[self] (← mkLambdaFVars params.varying value)

/-- Elaborate `iguarded`: `name := fun fixed => fixpoint (name.pre fixed)`, with the user's proof
that `name.pre` is contractive. -/
meta def elabGuarded (mods : TSyntax ``Lean.Parser.Command.declModifiers) (name : Ident)
    (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (ty body : Term)
    (contractive : Option (TSyntax `contractiveClause)) : CommandElabM Unit := do
  let some clause := contractive | throwErrorAt name "iguarded: provide a contractive_by proof"
  let `(contractiveClause| contractive_by $tac) := clause | throwUnsupportedSyntax
  let modifiers ← elabModifiers mods
  let checked ← elaborateBody name binders ty body (exporting := !modifiers.isPrivate)
  let perm ← liftTermElabM <| identifyFixedParameters checked
  let declName := (← getCurrNamespace) ++ name.getId
  let env ← getEnv
  let declName := if modifiers.isPrivate then mkPrivateName env declName else declName
  let levels := checked.levelParams
  let us := levels.map mkLevelParam
  liftTermElabM <| withParameters checked perm fun params => do
    let fixed := params.fixed
    let fn (vs : Array Expr) := mkAppN (mkConst declName us) (perm.buildArgs fixed vs)
    let curriedType ← perm.instantiateForall checked.functionType fixed
    -- `name.pre`: the functional `fun self varying => body`.
    let preName := declName ++ `pre
    emitDef preName levels (← mkLambdaFVars fixed (← abstractRecursion checked perm params))
    let pre := mkAppN (mkConst preName us) fixed
    -- `name.pre.contractive`: the user's proof of its one field.
    let contractiveType ← mkAppM ``OFE.Contractive #[pre]
    let proof ← elabTermEnsuringType (← `({ distLater_dist := by $tac })) contractiveType
    synthesizeSyntheticMVarsNoPostponing
    let contractiveName := preName ++ `contractive
    emitThm contractiveName levels (← mkForallFVars fixed contractiveType)
      (← mkLambdaFVars fixed (← instantiateMVars proof))
    addInstance contractiveName .global 1000
    -- `name` itself, with the user's modifiers. `mkAppM` would leave the trailing instance
    -- arguments of `fixpoint` and `toContractiveHom` unapplied.
    emitDef declName levels
      (← mkLambdaFVars fixed (← mkAppOptM ``Iris.fixpoint #[none, none, none, pre, none]))
    Term.applyAttributes declName modifiers.attrs
    addDocString' declName (mkNullNode binders) (modifiers.docString?.map fun d => ⟨d.1⟩)
    -- `name.unfold`: `fixpoint_unfold`, applied to the varying arguments.
    let curriedFn ← forallTelescope curriedType fun ws _ =>
      mkLambdaFVars (etaReduce := true) ws (fn ws)
    forallTelescope curriedType fun vs _ => do
      let hom ← mkAppOptM ``Function.toContractiveHom #[none, none, pre, none, none, none]
      let proof ← vs.foldlM (fun h v => mkAppM ``congrFun #[h, v])
        (← mkAppM ``Iris.fixpoint_unfold #[hom])
      let args := perm.buildArgs fixed vs
      emitThm (declName ++ `unfold) levels
        (← mkForallFVars args (← mkEq (fn vs) (mkAppN (mkApp pre curriedFn) vs)))
        (← mkLambdaFVars args proof)

/-- Guarded Iris fixpoint, defined with `OFE.fixpoint`. The body must be contractive in the
recursive function. -/
elab mods:declModifiers "iguarded " name:ident binders:bracketedBinder* " : " ty:term
    " := " body:term contractive:(contractiveClause)? : command =>
  elabGuarded mods name binders ty body contractive

end Iris.Fixpoint
