/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Markus de Medeiros
-/
module

public import Iris.BI.Lib.Lattice
public import Iris.ProofMode.Lib.Fixpoint.Common
public import Iris.ProofMode.Lib.Fixpoint.Tupling
public meta import Lean.Elab.PreDefinition.PartialFixpoint

/-! # `ifix` and `icofix`

Least and greatest Iris fixpoints via `partial_fixpoint` and the orders of `Iris.BI.Lib.Lattice`.
The lemmas about `lfp`/`gfp` are restated for each definition through `Tupling`. -/

namespace Iris.Fixpoint
open Lean Elab Command Meta Term

/-! ## Adding definitions -/

/-- Add an exposed definition, with its inferred type. -/
meta def emitDef (name : Name) (levels : List Name) (value : Expr) : TermElabM Unit := do
  let value ← instantiateMVars value
  withExporting <| addAndCompile <| .defnDecl {
    name, levelParams := levels, type := ← inferType value, value
    hints := .regular 0, safety := .safe }
  saveEqnAffectingOptions name
  enableRealizationsForConst name

/-! ## The definition -/

/-- A `partial_fixpoint` definition `fun fixed => fix F hF`, opened with `fixed` as free
variables. A non-recursive one stays `fun fixed => body`, with `F := fun _ => body` and varying
parameters those of `body`'s type; a body `fun x => …` makes `x` fixed, like a parameter. -/
structure FixpointData where
  /-- `true` for `ifix`, `false` for `icofix`. -/
  least : Bool
  declName : Name
  levels : List Name
  perm : FixedParamPerm
  fixed : Array Expr
  /-- The curried type `∀ varying, PROP` that `fix` works over. -/
  curriedType : Expr
  /-- `PROP`. -/
  prop : Expr
  /-- The functional, and its monotonicity proof if recursive. -/
  F : Expr
  hF? : Option Expr

namespace FixpointData

meta def us (d : FixpointData) : List Level := d.levels.map mkLevelParam

/-- `name` applied to the fixed parameters and the varying arguments `vs`. -/
meta def fn (d : FixpointData) (vs : Array Expr) : Expr :=
  mkAppN (mkConst d.declName d.us) (d.perm.buildArgs d.fixed vs)

/-- `name.pre` applied to the fixed parameters. -/
meta def pre (d : FixpointData) : Expr :=
  mkAppN (mkConst (d.declName ++ `pre) d.us) d.fixed

/-- `name` applied to the fixed parameters. -/
meta def curriedFn (d : FixpointData) : MetaM Expr :=
  forallTelescope d.curriedType fun ws _ => mkLambdaFVars (etaReduce := true) ws (d.fn ws)

end FixpointData

/-- Open the `partial_fixpoint` definition `declName` and run `k` on it. -/
meta def withFixpointData (least : Bool) (declName : Name) (k : FixpointData → TermElabM α) :
    TermElabM α := do
  match Lean.Elab.PartialFixpoint.eqnInfoExt.find? (← getEnv) declName with
  | some info =>
    let perm := info.fixedParamPerms.perms[0]!
    let levels := info.levelParams
    let value := (← getConstInfo info.declNameNonRec).instantiateValueLevelParams!
      (levels.map mkLevelParam)
    lambdaBoundedTelescope value perm.numFixed fun fixed body => do
      let_expr Lean.Order.fix curriedType _ F hF := body
        | throwError "{if least then "ifix" else "icofix"}: unexpected `partial_fixpoint` \
            definition{indentExpr body}"
      let prop ← forallTelescope curriedType fun _ resTy => pure resTy
      k { least, declName, levels, perm, fixed, curriedType, prop, F, hF? := hF }
  | none =>
    let info ← getConstInfo declName
    let levels := info.levelParams
    let value := info.instantiateValueLevelParams! (levels.map mkLevelParam)
    lambdaTelescope value fun fixed body => do
      let curriedType ← inferType body
      let prop ← forallTelescope curriedType fun _ resTy => pure resTy
      k { least, declName, levels, perm := Array.ofFn fun (i : Fin fixed.size) => some i.val,
          fixed, curriedType, prop, F := .lam `self curriedType body .default, hF? := none }

/-- `name.pre`: the curried functional built by `partial_fixpoint`. -/
meta def emitPre (d : FixpointData) : TermElabM Unit := do
  emitDef (d.declName ++ `pre) d.levels (← mkLambdaFVars d.fixed d.F)
  -- Reducible, so that for a body `myPre name`, `name.pre` unifies with `myPre`.
  setReducibleAttribute (d.declName ++ `pre)

/-- `name.unfold`: `fix_eq`, stated with `name` and `name.pre`. -/
meta def emitUnfold (d : FixpointData) : TermElabM Unit := do
  let curriedFn ← d.curriedFn
  forallTelescope d.curriedType fun vs _ => do
    let proof ← match d.hF? with
      | some hF =>
        vs.foldlM (fun h v => mkAppM ``congrFun #[h, v]) (← mkAppM ``Lean.Order.fix_eq #[hF])
      | none => mkEqRefl (d.fn vs)
    let args := d.perm.buildArgs d.fixed vs
    emitThm (d.declName ++ `unfold) d.levels
      (← mkForallFVars args (← mkEq (d.fn vs) (mkAppN (mkApp d.pre curriedFn) vs)))
      (← mkLambdaFVars args proof)

/-! ## Monotonicity -/

/-- The curried statement of `BIMono (conj F)`, and its equation with it. Computed for a variable
`F`, so the rewrites do not reach `F`'s body. -/
meta def monoStatement (T : Tupling) (F : Expr) : MetaM (Expr × Option Expr) := do
  withLocalDeclD `F (← mkArrow T.curried T.curried) fun f => do
    let some stmt ← unfoldDefinition? (← mkAppM ``BIMono #[← T.conj f]) | unreachable!
    let (curried, eq?) ← T.curryStatement stmt
    let subst (e : Expr) : MetaM Expr := return (← mkLambdaFVars #[f] e).beta #[F]
    return (← Core.betaReduce (← subst curried), ← eq?.mapM subst)

/-- Prove `BIMono (conj F)` by `tac` on its curried statement. Returns the curried statement, its
proof, and the proof of `BIMono (conj F)`. -/
meta def proveMono (T : Tupling) (F : Expr) (tac : TSyntax ``Lean.Parser.Tactic.tacticSeq) :
    TermElabM (Expr × Expr × Expr) := do
  let (curried, eq?) ← monoStatement T F
  let proof ← elabTermEnsuringType (← `(by $tac)) curried
  synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  return (curried, proof, ← castAlong eq? proof (forward := false))

/-- `ifix_monotone tac` proves `monotone F` by `tac` on the curried statement of `BIMono`. -/
syntax (name := ifixMonotone) "ifix_monotone " Lean.Parser.Tactic.tacticSeq : tactic
@[inherit_doc ifixMonotone]
syntax (name := icofixMonotone) "icofix_monotone " Lean.Parser.Tactic.tacticSeq : tactic

meta def evalFixMonotone (least : Bool) (tac : TSyntax ``Lean.Parser.Tactic.tacticSeq) :
    Tactic.TacticM Unit := Tactic.withMainContext do
  let goal ← Tactic.getMainGoal
  let_expr Lean.Order.monotone τ _ _ _ F := ← whnfR (← goal.getType)
    | throwError "{if least then "ifix_monotone" else "icofix_monotone"}: \
        expected a `monotone` goal"
  let T ← Tupling.ofCurried τ
  let (_, _, hG) ← proveMono T F tac
  goal.assign (← T.monotone least F hG)
  Tactic.replaceMainGoal []

@[tactic ifixMonotone] public meta def evalIfixMonotone : Tactic.Tactic
  | `(tactic| ifix_monotone $tac) => evalFixMonotone true tac
  | _ => throwUnsupportedSyntax

@[tactic icofixMonotone] public meta def evalIcofixMonotone : Tactic.Tactic
  | `(tactic| icofix_monotone $tac) => evalFixMonotone false tac
  | _ => throwUnsupportedSyntax

/-- The proof of `BIMono (conj F)` inside `hF`, from `ifix_monotone`, so `monotone_by` runs only
once. Unfolds the auxiliary theorems `partial_fixpoint` may wrap `hF` in. -/
meta partial def bimonoOf? (hF : Expr) : MetaM (Option Expr) := do
  let hF := hF.headBeta
  match_expr hF with
  | monotone_conj _ _ _ _ _ _ _e _e' _he _he' hGMono _h => return hGMono.appArg!
  | _ => pure ()
  let .const n us := hF.getAppFn | return none
  let some (.thmInfo info) := (← getEnv).find? n | return none
  bimonoOf? ((info.value.instantiateLevelParams info.levelParams us).beta hF.getAppArgs)

/-- `name.pre_mono`, curried: the proof `partial_fixpoint` checked if `bimonoOf?` finds it, else
`monoTac`. Returns the proof of `BIMono (conj name.pre)`. -/
meta def emitPreMono (d : FixpointData) (T : Tupling)
    (monoTac : TSyntax ``Lean.Parser.Tactic.tacticSeq) : TermElabM Expr := do
  let (curried, proof, hG) ← match ← d.hF?.bindM (bimonoOf? ·) with
    | some hG =>
      let (curried, eq?) ← monoStatement T d.pre
      pure (curried, ← castAlong eq? hG (forward := true), hG)
    | none => proveMono T d.pre monoTac
  emitThm (d.declName ++ `pre_mono) d.levels (← mkForallFVars d.fixed curried)
    (← mkLambdaFVars d.fixed proof)
  return hG

/-! ## Restating the library's lemmas -/

/-- What restating a library lemma for `name` needs. -/
structure Restating where
  d : FixpointData
  T : Tupling
  /-- `conj name.pre`, the body on predicates on tuples. -/
  G : Expr
  /-- A proof of `BIMono G`. -/
  hG : Expr
  /-- The library's fixpoint `lfp G hG` (or `gfp`). -/
  fixpoint : Expr
  /-- `fixpoint = uncurry name`. -/
  eq : Expr

/-- The `Restating` for `name`. `eq` is `fix_iso`, plus `fix_eq` for a non-recursive `name`. -/
meta def Restating.of (d : FixpointData) (T : Tupling) (hG : Expr) : TermElabM Restating := do
  let G ← T.conj d.pre
  let (fixName, monoName) := if d.least
    then (``MonotoneFixpoint.lfp, ``MonotoneFixpoint.monotone_of_bimono)
    else (``CoMonotoneFixpoint.gfp, ``CoMonotoneFixpoint.monotone_of_bimono)
  let fixpoint ← mkAppOptM fixName #[d.prop, none, T.A, G, hG]
  let preMono ← T.monotone d.least d.pre hG
  let iso ← mkAppOptM ``fix_iso #[T.curried, ← mkArrow T.A T.prop, none, none, d.pre, G, preMono,
    ← mkAppM monoName #[hG], T.uncurry, T.curry, ← T.monoUncurry, ← T.uncurryCurry,
    ← pointwiseRfl T.curried (fun a => pure (T.curry.beta #[T.uncurry.beta #[a]])) pure,
    ← pointwiseRfl T.curried (fun a => pure (T.uncurry.beta #[mkApp d.pre a]))
      (fun a => pure (mkApp G (T.uncurry.beta #[a])))]
  let eq ← mkEqSymm iso
  let eq ← match d.hF? with
    | some _ => pure eq
    | none => mkEqTrans eq (← mkCongrArg T.uncurry (← mkAppM ``Lean.Order.fix_eq #[preMono]))
  let fn := T.uncurry.beta #[← d.curriedFn]
  return { d, T, G, hG, fixpoint, eq := ← mkExpectedTypeHint eq (← mkEq fixpoint fn) }

/-- `lemma` applied to `extra`, restated for `name` over the fixed parameters. -/
meta def Restating.restate (R : Restating) (lemma : Name) (extra : Array Expr) :
    TermElabM (Expr × Expr) := do
  let { d, T, G, hG, fixpoint, eq } := R
  -- Every lemma begins `{PROP} [BI PROP] {A} {F} (h : BIMono F)`.
  let args : Array (Option Expr) := #[d.prop, none, T.A, G, hG]
  let general ← mkAppOptM lemma (args ++ extra.map some)
  let (type, proof) ← T.restate general fixpoint eq (← d.curriedFn)
  return (← mkForallFVars d.fixed type, ← mkLambdaFVars d.fixed proof)

/-- Make binders whose type is a class (possibly under `∀`) instance-implicit, for instances such
as `name.persistent_absorbing`. -/
meta def instBinders (env : Environment) : Expr → Expr
  | .forallE n d b bi =>
    let d := instBinders env d
    let isClass := d.getForallBody.getAppFn.constName?.any (isClass env)
    .forallE n d (instBinders env b) (if isClass then .instImplicit else bi)
  | e => e

/-- `name.suffix`: the lemma `lemma`, restated; an instance if `lemma` is. -/
meta def Restating.emit (R : Restating) (suffix lemma : Name) (extra : Array Expr := #[]) :
    TermElabM Unit := do
  let (type, proof) ← R.restate lemma extra
  let name := R.d.declName ++ suffix
  let env ← getEnv
  if ← isInstance lemma then
    emitThm name R.d.levels (instBinders env type) proof
    addInstance name .global (eval_prio default)
  else
    emitThm name R.d.levels type proof

/-- `name.eq_lfp` (or `eq_gfp`). Only with one varying parameter: otherwise it is about tuples. -/
meta def Restating.emitEq (R : Restating) : TermElabM Unit := do
  let { d, T, eq, .. } := R
  unless T.arity == 1 do return
  let eq ← mkEqSymm eq
  emitThm (d.declName ++ if d.least then `eq_lfp else `eq_gfp) d.levels
    (← mkForallFVars d.fixed (← betaEta (← inferType eq))) (← mkLambdaFVars d.fixed eq)

/-- The lemmas of `Iris.BI.Lib.Lattice` to restate, with their suffixes. -/
meta def fixpointLemmas (least : Bool) : List (Name × Name) :=
  if least then
    [(`unfold_mp, ``MonotoneFixpoint.fix_unfold_mp),
     (`unfold_mpr, ``MonotoneFixpoint.fix_unfold_mpr),
     (`iter, ``MonotoneFixpoint.fix_iter), (`ind, ``MonotoneFixpoint.fix_ind),
     (`ind_wf, ``MonotoneFixpoint.fix_ind_wf), (`strong_mono, ``MonotoneFixpoint.fix_strong_mono),
     (`affine, ``MonotoneFixpoint.fix_affine), (`absorbing, ``MonotoneFixpoint.fix_absorbing),
     (`persistent_affine, ``MonotoneFixpoint.fix_persistent_affine),
     (`persistent_absorbing, ``MonotoneFixpoint.fix_persistent_absorbing)]
  else
    [(`unfold_mp, ``CoMonotoneFixpoint.fix_unfold_mp),
     (`unfold_mpr, ``CoMonotoneFixpoint.fix_unfold_mpr),
     (`coiter, ``CoMonotoneFixpoint.fix_coiter), (`coind, ``CoMonotoneFixpoint.fix_coind),
     (`paco, ``CoMonotoneFixpoint.fix_paco), (`strong_mono, ``CoMonotoneFixpoint.fix_strong_mono),
     (`absorbing, ``CoMonotoneFixpoint.fix_absorbing)]

/-! ## The commands -/

/-- Everything `ifix`/`icofix` generates for `d`. -/
meta def emitAll (d : FixpointData) (monoTac : TSyntax ``Lean.Parser.Tactic.tacticSeq) :
    TermElabM Unit := do
  emitPre d
  emitUnfold d
  let T ← Tupling.ofCurried d.curriedType
  let R ← Restating.of d T (← emitPreMono d T monoTac)
  R.emitEq
  for (suffix, lemma) in fixpointLemmas d.least do R.emit suffix lemma
  -- `name.ne`, when `name` takes OFE instances (unused section instances are dropped).
  if let some rel ← T.distRel? then
    R.emit `ne (if d.least then ``MonotoneFixpoint.fix_ne_rel else ``CoMonotoneFixpoint.fix_ne_rel)
      #[rel]

/-- Whether the attribute `attr` only applies when declaring: `expose` and reducibility. -/
meta def atDeclaration (attr : Syntax) : Bool :=
  attr[1].isOfKind ``Lean.Parser.Attr.simple &&
    [`expose, `reducible, `semireducible, `irreducible].contains attr[1][0].getId

/-- `mods`, with only the attributes for which `keep` holds. -/
meta def filterAttributes (mods : TSyntax ``Lean.Parser.Command.declModifiers)
    (keep : Syntax → Bool) : TSyntax ``Lean.Parser.Command.declModifiers :=
  match mods.raw[1].getOptional? with
  | none => mods
  | some attrs =>
    let kept := attrs[1].getSepArgs.filter keep
    ⟨mods.raw.setArg 1 <| if kept.isEmpty then mkNullNode
      else mkNullNode #[attrs.setArg 1 (mkNullNode (mkSepArray kept (mkAtom ",")))]⟩

/-- Define `name` with `partial_fixpoint` and `monoTac`, with only the declaration-time attributes.
Returns its full name, or `none` on error. -/
meta def defineFixpoint (least : Bool) (mods : TSyntax ``Lean.Parser.Command.declModifiers)
    (name : Ident) (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (ty body : Term)
    (monoTac : TSyntax ``Lean.Parser.Tactic.tacticSeq) : CommandElabM (Option Name) := do
  let binders ← if ← sectionProvidesBI then
      pure (#[← `(bracketedBinder| [BI $ty])] ++ binders)
    else pure binders
  let errors ← errorCount
  let monotone ← if least then `(tactic| ifix_monotone $monoTac)
    else `(tactic| icofix_monotone $monoTac)
  -- `partial_fixpoint` would also apply attributes to its auxiliary definitions.
  let mods := filterAttributes mods atDeclaration
  elabCommand (← `(command| $mods:declModifiers def $name:ident $binders* : $ty := $body
    partial_fixpoint monotonicity by $monotone:tactic))
  dropNotRecursiveWarning
  if (← errorCount) > errors then return none
  return some (← resolveDeclared name)
where
  errorCount : CommandElabM Nat := do
    let msgs := (← get).messages.unreported
    return msgs.foldl (fun n m => if m.severity == .error then n + 1 else n) 0
  /-- Drop `partial_fixpoint`'s warning about a non-recursive body: the user did not write it. -/
  dropNotRecursiveWarning : CommandElabM Unit := do
    let msgs := (← get).messages
    let mut kept := {}
    for m in msgs.unreported do
      unless (← m.data.toString).startsWith "unused `partial_fixpoint`" do kept := kept.push m
    modify fun s => { s with messages := { msgs with unreported := kept } }
  /-- Whether `BI ty` comes from a section variable nothing else uses. The definition then needs
  its own `[BI ty]`: the order on `ty` needs it, and an unmentioned section instance is dropped. -/
  sectionProvidesBI : CommandElabM Bool :=
    runTermElabM fun _ => do
      let some tyE ← observing? (withoutErrToSorry (elabType ty)) | return false
      let some inst ← synthInstance? (← mkAppM ``BI #[tyE]) | return false
      let .fvar instId := inst | return false
      -- A section instance built on it (`BIFUpdate`) keeps it; a second `BI` would not match.
      return !(← (← getLCtx).anyM fun decl => do
        return decl.fvarId != instId && (← instantiateMVars decl.type).containsFVar instId)

/-- Elaborate `ifix` (`least := true`) or `icofix`. -/
meta def elabFixpoint (least : Bool) (mods : TSyntax ``Lean.Parser.Command.declModifiers)
    (name : Ident) (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (ty body : Term)
    (mono : Option (TSyntax `monotoneClause)) : CommandElabM Unit := do
  let monoTac ← match mono with
    | some clause =>
      let `(monotoneClause| monotone_by $tac) := clause | throwUnsupportedSyntax
      pure tac
    | none => withRef name do
      defaultTactic (if least then `ifix else `icofix) `monotone_by `iris.fixpoint.monotoneDefault
        (← `(tactic| ifix_monotone_default)) "monotonicity"
  let ns := if least then `Iris.MonotoneFixpoint else `Iris.CoMonotoneFixpoint
  elabCommand (← `(command| section))
  let declName? ← try
      elabCommand (← `(command| open scoped $(mkIdent ns):ident))
      let some declName ← defineFixpoint least mods name binders ty body monoTac | pure none
      liftTermElabM <| withFixpointData least declName (emitAll · monoTac)
      pure (some declName)
    finally
      elabCommand (← `(command| end))
  -- The other attributes go after the `end`, which a `local` one would not survive.
  let later := (filterAttributes mods (!atDeclaration ·)).raw[1].getOptional?
  if let (some declName, some attrs) := (declName?, later) then
    liftTermElabM do Term.applyAttributes declName (← elabAttrs attrs[1].getSepArgs)

/-- Least Iris fixpoint, defined with `partial_fixpoint`. -/
elab mods:declModifiers "ifix " name:ident binders:bracketedBinder* " : " ty:term " := " body:term
    mono:(monotoneClause)? : command =>
  elabFixpoint true mods name binders ty body mono

/-- Greatest Iris fixpoint, defined with `partial_fixpoint`. -/
elab mods:declModifiers "icofix " name:ident binders:bracketedBinder* " : " ty:term " := " body:term
    mono:(monotoneClause)? : command =>
  elabFixpoint false mods name binders ty body mono

end Iris.Fixpoint
