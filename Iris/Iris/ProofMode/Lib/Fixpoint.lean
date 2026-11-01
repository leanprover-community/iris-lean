/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Markus de Medeiros
-/
module

public import Iris.Algebra.Approx
public import Iris.BI.Lib.Lattice
public import Iris.ProofMode.Lib.Monotone
public meta import Lean.Elab.PreDefinition.PartialFixpoint

/-! # Iris fixpoint commands

`ifix` and `icofix` define least and greatest Iris fixpoints with `partial_fixpoint`, using the
orders in `Iris.BI.Lib.Lattice`. The `monotone_by` proof of `BIMono` gives `partial_fixpoint` its
monotonicity proof, and the Iris (co)induction principle from `fix_iter`/`fix_coiter`.

`iguarded` defines guarded fixpoints with `partial_fixpoint` too, into the approximation domain
`Iris.Approx`: the body's functional is lifted with `ApproxFun.lift`, which is monotone for any
body, and contractiveness makes the fixpoint exact. -/

namespace Iris.Fixpoint
open Lean Elab Command Meta Term BI

declare_syntax_cat monotoneClause
syntax "monotone_by " Lean.Parser.Tactic.tacticSeq : monotoneClause

declare_syntax_cat contractiveClause
syntax "contractive_by " Lean.Parser.Tactic.tacticSeq : contractiveClause

/-! ## `ifix` and `icofix` -/

/-- Add a definition, using its inferred type. -/
meta def emitDef (name : Name) (levels : List Name) (value : Expr) : TermElabM Unit := do
  let value ← instantiateMVars value
  addAndCompile <| .defnDecl {
    name, levelParams := levels, type := ← inferType value, value
    hints := .regular 0, safety := .safe }
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
  /-- The functional, its monotonicity proof, and its `BIMono` proof. -/
  F : Expr
  hF : Expr
  mono : Expr
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

/-- `BIMono G`, for `G : curriedType → curriedType`. -/
meta def mkBIMono (d : FixpointData) (G : Expr) : MetaM Expr :=
  mkAppOptM ``BIMono #[d.prop, none, d.curriedType, none, G]

/-- Rewrite `fix F hF` to `name` in the type of `proof`, for a non-recursive body. -/
meta def rewriteFix (d : FixpointData) (proof : Expr) : MetaM Expr := do
  let some h := d.fixEq? | return proof
  let_expr Eq ty lhs _ := ← inferType h | throwError "ifix: unexpected equation"
  let type ← instantiateMVars (← inferType proof)
  let motive := .lam `f ty (← kabstract type lhs) .default
  mkEqMP (← mkCongrArg motive h) proof

end FixpointData

/-- The data for a non-recursive body, which `partial_fixpoint` leaves as a plain definition.
Every parameter is fixed, and the functional is the constant `fun _ => body`. -/
meta def withNonRecursiveData (least : Bool) (declName : Name) (k : FixpointData → TermElabM α) :
    TermElabM α := do
  let info ← getConstInfo declName
  let levels := info.levelParams
  let value := info.instantiateValueLevelParams! (levels.map mkLevelParam)
  lambdaTelescope value fun fixed body => do
    let resTy ← inferType body
    let F := .lam `self resTy body .default
    let inst ← synthInstance (← mkAppM ``Lean.Order.CCPO #[resTy])
    let order ← mkAppOptM ``Lean.Order.CCPO.toPartialOrder #[some resTy, some inst]
    let hF ← mkAppOptM ``Lean.Order.monotone_const
      #[some resTy, some order, some resTy, some order, some body]
    -- `fix_eq` gives `fix F hF = F (fix F hF)`, whose right side is `body`, that is `name`.
    let fixEq ← mkAppOptM ``Lean.Order.fix_eq #[some resTy, some inst, some F, some hF]
    let mono ← mkAppOptM ``BIMono.const #[resTy, none, resTy, none, body]
    k { least, declName, levels, perm := Array.ofFn fun (i : Fin fixed.size) => some i.val,
        fixed, curriedType := resTy, prop := resTy, F, hF, mono, fixEq? := some fixEq }

/-- Open the `partial_fixpoint` definition `declName` and run `k` on it. -/
meta def withFixpointData (least : Bool) (declName : Name) (k : FixpointData → TermElabM α) :
    TermElabM α := do
  -- `partial_fixpoint` turns a non-recursive body into a plain definition.
  let some info := Lean.Elab.PartialFixpoint.eqnInfoExt.find? (← getEnv) declName
    | withNonRecursiveData least declName k
  let perm := info.fixedParamPerms.perms[0]!
  let levels := info.levelParams
  let nonRec ← getConstInfo info.declNameNonRec
  let value := nonRec.instantiateValueLevelParams! (levels.map mkLevelParam)
  lambdaBoundedTelescope value perm.numFixed fun fixed body => do
    let_expr Lean.Order.fix curriedType _ F hF := body
      | throwError "ifix: unexpected `partial_fixpoint` definition{indentExpr body}"
    let prop ← forallTelescope curriedType fun _ resTy => pure resTy
    k { least, declName, levels, perm, fixed, curriedType, prop, F, hF, mono := ← bimonoOf hF }
where
  /-- The `BIMono` proof `h` in the monotonicity proof `monotone_of_bimono h`, which
  `partial_fixpoint` may have moved into an auxiliary theorem. -/
  bimonoOf (hF : Expr) : MetaM Expr := do
    let isBIMono (e : Expr) := e.isAppOf ``Iris.MonotoneFixpoint.monotone_of_bimono ||
      e.isAppOf ``Iris.CoMonotoneFixpoint.monotone_of_bimono
    let hF ← if isBIMono hF then pure hF else
      let .const aux us := hF.getAppFn | unexpected hF
      let info ← getConstInfo aux
      let some value := info.value? (allowOpaque := true) | unexpected hF
      pure <| (value.instantiateLevelParams info.levelParams us).beta hF.getAppArgs
    unless isBIMono hF do unexpected hF
    return hF.appArg!
  unexpected {α} (hF : Expr) : MetaM α :=
    throwError "ifix: unexpected monotonicity proof{indentExpr hF}"

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

/-- `name.pre_mono`: the `monotone_by` proof that `name.pre` is `BIMono`. -/
meta def emitPreMono (d : FixpointData) : TermElabM Unit := do
  emitThm (d.declName ++ `pre_mono) d.levels (← mkForallFVars d.fixed (← d.mkBIMono d.pre))
    (← mkLambdaFVars d.fixed d.mono)

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
  let preMono := mkAppN (mkConst (d.declName ++ `pre_mono) d.us) d.fixed
  let proof ← d.rewriteFix (← mkAppOptM lemma
    #[d.prop, none, d.curriedType, none, none, none, d.pre, preMono, Φ])
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
    | none => `(Lean.Parser.Tactic.tacticSeq| imono)
  let ns := if least then `Iris.MonotoneFixpoint else `Iris.CoMonotoneFixpoint
  -- Everything below runs with the matching order on `PROP` in scope.
  elabCommand (← `(command| section))
  try
    elabCommand (← `(command| open scoped $(mkIdent ns):ident))
    let binders ← if ← sectionProvidesBI ty then
        pure (#[← `(bracketedBinder| [BI $ty])] ++ binders)
      else pure binders
    let monotone := mkIdent (ns ++ `monotone_of_bimono)
    let errors ← errorCount
    elabCommand (← `(command| def $name:ident $binders* : $ty := $body
      partial_fixpoint monotonicity $monotone (PROP := $ty) (by $monoTac)))
    dropNotRecursiveWarning
    -- If the definition failed, Lean has already reported why.
    if (← errorCount) > errors then return
    -- Resolve the actual name, which is mangled in a private scope.
    let declName ← liftCoreM <| realizeGlobalConstNoOverload name
    liftTermElabM <| withFixpointData least declName fun d => do
      emitPre d
      emitUnfold d
      emitPreMono d
      emitInd d
  finally
    elabCommand (← `(command| end))
where
  errorCount : CommandElabM Nat := do
    let msgs := (← get).messages.unreported
    return msgs.foldl (fun n m => if m.severity == .error then n + 1 else n) 0
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

/-- The arguments that `binders` bind, as they would be passed back: explicit ones positionally,
implicit ones by name. Instance arguments are left to instance search. -/
meta def binderArgs (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) :
    MacroM (Array Term) :=
  binders.foldlM (init := #[]) fun acc b => do
    let ids := b.raw[1].getArgs.filter (·.isIdent) |>.map (⟨·⟩ : Syntax → Ident)
    match b.raw.getKind with
    | ``Lean.Parser.Term.explicitBinder => return acc ++ ids.map (⟨·.raw⟩)
    | ``Lean.Parser.Term.implicitBinder | ``Lean.Parser.Term.strictImplicitBinder =>
      ids.foldlM (init := acc) fun acc id => do
        return acc.push ⟨(← `(Lean.Parser.Term.namedArgument| ($id := $id))).raw⟩
    | _ => return acc

/-- Elaborate `iguarded`. For `iguarded name binders : ty := body`, it emits
* `name.pre : (∀ binders, ty) → (∀ binders, ty) := fun name binders => body`,
* `name.pre.contractive`, from the `contractive_by` proof,
* `name.approx : ∀ binders, Approx ty`, the fixpoint of the lifted functional, by
  `partial_fixpoint`. It takes no parameters of its own, so its functional is exactly `lift pre`,
  whatever the fixed-parameter analysis decides,
* `name binders : ty`, its exact value, and `name.unfold`.

Everything is generated as syntax: the body is elaborated, and the fixpoint defined, by Lean. -/
meta def elabGuarded (mods : TSyntax ``Lean.Parser.Command.declModifiers) (name : Ident)
    (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (ty body : Term)
    (contractive : Option (TSyntax `contractiveClause)) : CommandElabM Unit := do
  let some clause := contractive | throwErrorAt name "iguarded: provide a contractive_by proof"
  let `(contractiveClause| contractive_by $tac) := clause | throwUnsupportedSyntax
  let vis ← if (← elabModifiers mods).isPrivate then `(declModifiers| private)
    else `(declModifiers|)
  let suffixed (s : Name) := mkIdentFrom name (name.getId ++ s)
  let (pre, approx) := (suffixed `pre, suffixed `approx)
  let (contractiveName, unfold) := (suffixed (`pre ++ `contractive), suffixed `unfold)
  let args ← liftMacroM <| binderArgs binders
  let funBinders : TSyntaxArray ``Lean.Parser.Term.funBinder := binders.map (⟨·.raw⟩)
  let lam (e : Term) : CommandElabM Term :=
    if binders.isEmpty then pure e else `(fun $funBinders* => $e)
  let app (f : Ident) : CommandElabM Term := if args.isEmpty then pure f else `($f $args*)
  let (sig, sigA) ← if binders.isEmpty then pure (ty, ← `(Iris.Approx $ty))
    else pure (← `(∀ $binders*, $ty), ← `(∀ $binders*, Iris.Approx $ty))
  elabCommand (← `(command| noncomputable section))
  try
    elabCommand (← `(command|
      $vis:declModifiers def $pre : $sig → $sig := fun ($name : $sig) => $(← lam body)))
    elabCommand (← `(command|
      instance $contractiveName:ident : Iris.OFE.Contractive ($pre : $sig → $sig) where
        distLater_dist := by $tac))
    elabCommand (← `(command|
      $vis:declModifiers def $approx : $sigA := Iris.ApproxFun.lift (τ := $sig) $pre $approx
      partial_fixpoint monotonicity Iris.ApproxFun.lift_mono _))
    elabCommand (← `(command|
      $mods:declModifiers def $name $binders* : $ty :=
        Iris.ApproxFun.get ($(← app approx) : Iris.Approx $ty)))
    -- `lift_fix_get` on the unfolding equation of `name.approx`, applied to the arguments.
    let approxEq := mkIdentFrom name (name.getId ++ `approx ++ `eq_1)
    elabCommand (← `(command|
      theorem $unfold $binders* :
          $(← app name) = $pre $(← lam (← `(($(← app name) : $ty)))) $args* :=
        congrArg (fun f => f $args*) (Iris.ApproxFun.lift_fix_get $pre (Eq.symm $approxEq))))
  finally
    elabCommand (← `(command| end))

/-- Guarded Iris fixpoint, defined with `partial_fixpoint` over approximations. The body must be
contractive in the recursive function. -/
elab mods:declModifiers "iguarded " name:ident binders:bracketedBinder* " : " ty:term
    " := " body:term contractive:(contractiveClause)? : command =>
  elabGuarded mods name binders ty body contractive

end Iris.Fixpoint
