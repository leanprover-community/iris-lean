/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Markus de Medeiros
-/
module

public import Iris.BI.Lib.Lattice
public import Iris.ProofMode.Lib.Monotone
public meta import Lean.Elab.PreDefinition.PartialFixpoint

/-! # Iris fixpoint commands

`ifix` and `icofix` define least and greatest Iris fixpoints with `partial_fixpoint`, using the
orders in `Iris.BI.Lib.Lattice`, and derive their Iris (co)induction principles from
`fix_iter`/`fix_coiter`.

`iguarded` is still a stub: the fixpoint and its unfolding theorem are `sorry`, and the proof
clause is ignored. -/

namespace Iris.Fixpoint
open Lean Elab Command Meta Term BI

/-- Placeholder for the fixpoint of `f`. -/
public def stubFixpoint {α : Sort _} (_f : α → α) : α := sorry

declare_syntax_cat monotoneClause
syntax "monotone_by " Lean.Parser.Tactic.tacticSeq : monotoneClause

declare_syntax_cat contractiveClause
syntax "contractive_by " Lean.Parser.Tactic.tacticSeq : contractiveClause

/-- Arity of the first application of `name` in `stx`. -/
meta partial def recursiveArity (name : Name) (stx : Syntax) : Option Nat :=
  match stx with
  | `($f:ident $args*) =>
    if f.getId == name then some args.size
    else (stx.getArgs.filterMap (recursiveArity name))[0]?
  | _ =>
    if stx.isIdent && stx.getId == name then some 0
    else (stx.getArgs.filterMap (recursiveArity name))[0]?

/-- Split `binders` into a prefix and a suffix made of the last `arity` explicit parameters. -/
meta def splitBinders (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (arity : Nat) :
    CommandElabM (Array (TSyntax ``Lean.Parser.Term.bracketedBinder) ×
      Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) := do
  let mut pre := binders
  let mut suffix := #[]
  let mut needed := arity
  while needed > 0 do
    let some b := pre.back? | throwError "fixpoint stub: recursive arity {arity} exceeds the parameters"
    pre := pre.pop
    let `(bracketedBinder| ($ids* : $t)) := b
      | throwErrorAt b "fixpoint stub: recursive parameters must be trailing explicit binders"
    if ids.size ≤ needed then
      suffix := #[b] ++ suffix
      needed := needed - ids.size
    else
      let keep := ids.extract 0 (ids.size - needed)
      let take := ids.extract (ids.size - needed) ids.size
      pre := pre.push (← `(bracketedBinder| ($keep* : $t)))
      suffix := #[← `(bracketedBinder| ($take* : $t))] ++ suffix
      needed := 0
  return (pre, suffix)

/-- Names of the explicit parameters bound by `binders`. -/
meta def explicitArgs (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) : Array Term :=
  binders.foldl (init := #[]) fun acc b =>
    match b with
    | `(bracketedBinder| ($ids* : $_)) => acc ++ ids.map fun i => ⟨i.raw⟩
    | _ => acc

/-- Names of the leading implicit (not instance) binders of `type`. -/
meta partial def leadingImplicitNames (type : Expr) : Array Name :=
  match type with
  | .forallE n _ body bi =>
    if bi == .default then #[]
    else (if bi == .instImplicit then #[] else #[n]) ++ leadingImplicitNames body
  | _ => #[]

/-- Emit `name.pre`, a placeholder definition of `name`, and a `sorry` unfolding theorem. -/
meta def elabStub (mods : TSyntax ``Lean.Parser.Command.declModifiers) (name : Ident)
    (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (ty body : Term)
    (contractive : Bool) : CommandElabM Unit := do
  let arity := (recursiveArity name.getId body).getD 0
  let (pre, suffix) ← splitBinders binders arity
  let selfType ← if suffix.isEmpty then pure ty else `(∀ $suffix*, $ty)
  let preArgs := explicitArgs pre
  let preName := mkIdentFrom name (name.getId ++ `pre)
  let unfoldName := mkIdentFrom name (name.getId ++ `unfold)
  elabCommand (← `(command| def $preName:ident $pre* ($name : $selfType) $suffix* : $ty := $body))
  -- Pin the implicit parameters of `name.pre` that its explicit arguments do not determine.
  let preType := (← getConstInfo ((← getCurrNamespace) ++ preName.getId)).type
  let implicitArgs : Array Term ← (leadingImplicitNames preType).mapM fun n => do
    return ⟨(← `(Lean.Parser.Term.namedArgument| ($(mkIdent n) := $(mkIdent n)))).raw⟩
  let preApp ← `($preName:ident $preArgs* $implicitArgs*)
  elabCommand (← `(command|
    $mods:declModifiers def $name:ident $pre* : $selfType := stubFixpoint $preApp))
  elabCommand (← `(command|
    theorem $unfoldName:ident $pre* : $name $preArgs* $implicitArgs* = $preApp ($name $preArgs*) :=
      sorry))
  if contractive then
    let contractiveName := mkIdentFrom name (name.getId ++ `pre ++ `contractive)
    elabCommand (← `(command|
      instance $contractiveName:ident $pre* : OFE.Contractive $preApp := sorry))

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
    k { least, declName, levels, perm := Array.ofFn fun (i : Fin fixed.size) => some i.val,
        fixed, curriedType := resTy, prop := resTy, F, hF, fixEq? := some fixEq }

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
    k { least, declName, levels, perm, fixed, curriedType, prop, F, hF }

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

/-- Guarded Iris fixpoint (stub). -/
elab mods:declModifiers "iguarded " name:ident binders:bracketedBinder* " : " ty:term
    " := " body:term (contractiveClause)? : command =>
  elabStub mods name binders ty body true

end Iris.Fixpoint
