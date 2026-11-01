/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Markus de Medeiros
-/
module

public import Iris.BI.Lib.Fixpoint
public import Iris.BI.Lib.Lattice
public import Iris.ProofMode.Lib.Monotone
public meta import Lean.Elab.PreDefinition.PartialFixpoint

/-! # Iris fixpoint commands

`ifix` and `icofix` define least and greatest Iris fixpoints with `partial_fixpoint`, using the
orders in `Iris.BI.Lib.Lattice`, and relate them to `bi_least_fixpoint`/`bi_greatest_fixpoint`.

`iguarded` is still a stub: the fixpoint and its unfolding theorem are `sorry`, and the proof
clause is ignored. -/

namespace Iris.Fixpoint
open Lean Elab Command Meta Term BI

/-- Placeholder for the fixpoint of `f`. -/
public def stubFixpoint {α : Sort _} (_f : α → α) : α := sorry

declare_syntax_cat monotoneClause
syntax "monotone_by " Lean.Parser.Tactic.tacticSeq : monotoneClause

declare_syntax_cat nonexpClause
syntax "nonexp_by " Lean.Parser.Tactic.tacticSeq : nonexpClause

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

/-- Pack `xs` into a left-nested tuple; `()` when `xs` is empty. -/
meta def pack (xs : Array Expr) : MetaM Expr := do
  if xs.isEmpty then return mkConst ``Unit.unit
  xs[1:].foldlM (fun acc x => mkAppM ``Prod.mk #[acc, x]) xs[0]!

/-- The type of `pack xs`, given the types of `xs`. -/
meta def packType (ts : Array Expr) : MetaM Expr := do
  if ts.isEmpty then return mkConst ``Unit
  ts[1:].foldlM (fun acc t => mkAppM ``Prod #[acc, t]) ts[0]!

/-- Project the `n` components out of a tuple built by `pack`. -/
meta def unpack (p : Expr) (n : Nat) : MetaM (Array Expr) := do
  if n == 0 then return #[]
  let mut rest := p
  let mut args := #[]
  for _ in [:n - 1] do
    args := #[← mkAppM ``Prod.snd #[rest]] ++ args
    rest ← mkAppM ``Prod.fst #[rest]
  return #[rest] ++ args

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

/-- Run `k` with an `OFE` instance for each type in `ts`: synthesized when possible, otherwise
bound as a new instance argument. `k` receives the new arguments. For a compound type such as
`α × α`, the new argument is `[OFE α]`, so the product instance comes from instance search. -/
meta partial def withOFEInstances (ts : Array Expr) (k : Array Expr → TermElabM α) :
    TermElabM α :=
  go (ts.toList.map (·, true)) #[]
where
  /-- `expand` says whether to try the type variables of `t` before `t` itself. -/
  go : List (Expr × Bool) → Array Expr → TermElabM α
    | [], acc => k acc
    | (t, expand) :: ts, acc => do
      let instType ← mkAppM ``OFE #[t]
      if (← synthInstance? instType).isSome then return ← go ts acc
      let atoms ← (Lean.collectFVars {} t).fvarIds.toList.filterM fun fv => do
        return (← inferType (mkFVar fv)).isSort
      let atoms := atoms.map mkFVar |>.filter (· != t)
      if expand && !atoms.isEmpty then
        go (atoms.map (·, false) ++ (t, false) :: ts) acc
      else
        withLocalDecl `inst .instImplicit instType fun x => go ts (acc.push x)

/-- A `partial_fixpoint` definition, opened in a local context where its fixed parameters are
free variables. The definition is `fun fixed => fix F hF` (possibly through `name.mutual`). -/
structure FixpointData where
  /-- `true` for `ifix`, `false` for `icofix`. -/
  least : Bool
  declName : Name
  levels : List Name
  perm : FixedParamPerm
  fixed : Array Expr
  /-- The curried type `∀ varying, resTy` that `fix` works over. -/
  curriedType : Expr
  /-- The `CCPO curriedType` instance `partial_fixpoint` chose. -/
  inst : Expr
  /-- The functional and its monotonicity proof. -/
  F : Expr
  hF : Expr
  /-- The types of the varying parameters, and their packed product. -/
  vtypes : Array Expr
  dom : Expr
  resTy : Expr
  /-- For a non-recursive body, a proof of `fix F hF = name` (they are not definitionally
  equal). For a recursive one, `none`: `name` unfolds to `fix F hF`. -/
  fixEq? : Option Expr := none

namespace FixpointData

meta def us (d : FixpointData) : List Level := d.levels.map mkLevelParam

/-- `name` applied to the fixed parameters and the varying arguments `vs`. -/
meta def fn (d : FixpointData) (vs : Array Expr) : Expr :=
  mkAppN (mkConst d.declName d.us) (d.perm.buildArgs d.fixed vs)

/-- `name` as a function of its varying parameters only. -/
meta def curriedFn (d : FixpointData) : MetaM Expr :=
  forallTelescope d.curriedType fun ws _ => mkLambdaFVars (etaReduce := true) ws (d.fn ws)

meta def pre (d : FixpointData) : Expr :=
  mkAppN (mkConst (d.declName ++ `pre) d.us) d.fixed

meta def pre' (d : FixpointData) : Expr :=
  mkAppN (mkConst (d.declName ++ `pre') d.us) d.fixed

/-- `e` uncurries: `fun f p => f p.1 p.2`. -/
meta def e (d : FixpointData) : MetaM Expr :=
  withLocalDeclD `f d.curriedType fun f => withLocalDeclD `p d.dom fun p => do
    mkLambdaFVars #[f, p] (mkAppN f (← unpack p d.vtypes.size))

/-- `e'` curries: `fun Φ x y => Φ (x, y)`. -/
meta def e' (d : FixpointData) : MetaM Expr := do
  withLocalDeclD `Φ (← mkArrow d.dom d.resTy) fun Φ => do
    let curried ← forallTelescope d.curriedType fun vs _ => do
      mkLambdaFVars vs (mkApp Φ (← pack vs))
    mkLambdaFVars #[Φ] curried

/-- Rewrite `fix F hF` to `name` in the type of `proof`, for a non-recursive body. -/
meta def rewriteFix (d : FixpointData) (proof : Expr) : MetaM Expr := do
  let some h := d.fixEq? | return proof
  let_expr Eq ty lhs _ := ← inferType h | throwError "ifix: unexpected equation"
  let type ← instantiateMVars (← inferType proof)
  let motive := .lam `f ty (← kabstract type lhs) .default
  mkEqMP (← mkCongrArg motive h) proof

end FixpointData

/-- The data for a non-recursive body, which `partial_fixpoint` leaves as a plain
definition. Every parameter is fixed, and the functional is the constant `fun _ => body`. -/
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
        fixed, curriedType := resTy, inst, F, hF, vtypes := #[], dom := mkConst ``Unit, resTy
        fixEq? := some fixEq }

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
    let_expr Lean.Order.fix curriedType inst F hF := body
      | throwError "ifix: unexpected `partial_fixpoint` definition{indentExpr body}"
    -- The varying parameters, which must be independent to be packed into a tuple.
    let (vtypes, resTy) ← forallTelescope curriedType fun vs resTy => do
      let vtypes ← vs.mapM (inferType ·)
      for t in vtypes do
        if vs.any (t.containsFVar ·.fvarId!) then
          throwError "ifix: dependent varying parameters are not supported"
      if vs.any (resTy.containsFVar ·.fvarId!) then
        throwError "ifix: the result type depends on a varying parameter"
      return (vtypes, resTy)
    k { least, declName, levels, perm, fixed, curriedType, inst, F, hF, vtypes, resTy
        dom := ← packType vtypes }

/-- `name.pre`: the curried functional built by `partial_fixpoint`. -/
meta def emitPre (d : FixpointData) : TermElabM Unit := do
  emitDef (d.declName ++ `pre) d.levels (← mkLambdaFVars d.fixed d.F)

/-- `name.pre'`: the packed functional `e ∘ name.pre ∘ e'`, the shape `BIMonoPred` needs. -/
meta def emitPre' (d : FixpointData) : TermElabM Unit := do
  let e ← d.e
  let e' ← d.e'
  let value ← withLocalDeclD `Φ (← mkArrow d.dom d.resTy) fun Φ => do
    mkLambdaFVars #[Φ] (← Core.betaReduce (mkApp e (mkApp d.pre (mkApp e' Φ))))
  emitDef (d.declName ++ `pre') d.levels (← mkLambdaFVars d.fixed value)

/-- `name.unfold`: one step of `fix_eq`, stated with `name` and `name.pre`. -/
meta def emitUnfold (d : FixpointData) : TermElabM Unit := do
  let curriedFn ← d.curriedFn
  forallTelescope d.curriedType fun vs _ => do
    -- A non-recursive `name` unfolds to its body directly.
    let proof ← if d.fixEq?.isSome then mkEqRefl (d.fn vs) else
      vs.foldlM (fun h v => mkAppM ``congrFun #[h, v]) (← mkAppM ``Lean.Order.fix_eq #[d.hF])
    let args := d.perm.buildArgs d.fixed vs
    emitThm (d.declName ++ `unfold) d.levels
      (← mkForallFVars args (← mkEq (d.fn vs) (mkAppN (mkApp d.pre curriedFn) vs)))
      (← mkLambdaFVars args proof)

/-- `name.pre_mono`: the user's proofs that `name.pre'` is a `BIMonoPred`. -/
meta def emitPreMono (d : FixpointData) (params : Array Expr)
    (monoTac neTac : TSyntax ``Lean.Parser.Tactic.tacticSeq) : TermElabM Unit := do
  let monoType ← mkAppM ``BIMonoPred #[d.pre']
  -- `monotone` can leave instance goals, such as `OFE Unit`, for typeclass search to close.
  let monoVal ← elabTermEnsuringType (← `({
    mono_pred := by ($monoTac); all_goals try infer_instance
    mono_pred_ne := by $neTac })) monoType
  synthesizeSyntheticMVarsNoPostponing
  let monoName := d.declName ++ `pre_mono
  emitDef monoName d.levels (← mkLambdaFVars params (← instantiateMVars monoVal))
  setReducibilityStatus monoName .instanceReducible
  addInstance monoName .global 1000

/-- The arguments shared by the `_of_iso` lemmas in `Iris.BI.Lib.Lattice`: the curry/uncurry
isomorphism, its monotonicity and inverse laws (all definitional), and the two functionals. -/
meta def isoArgs (d : FixpointData) : TermElabM (Array Expr) := do
  let e ← d.e
  let e' ← d.e'
  let n := d.vtypes.size
  let domFn ← mkArrow d.dom d.resTy
  let piInst ← mkAppOptM ``Lean.Order.instCCPOPi
    #[some d.dom, some (.lam `_ d.dom d.resTy .default), none]
  let rel (ty inst a b : Expr) : MetaM Expr := do
    let order ← mkAppOptM ``Lean.Order.CCPO.toPartialOrder #[some ty, some inst]
    mkAppOptM ``Lean.Order.PartialOrder.rel #[some ty, some order, some a, some b]
  let he ← withLocalDeclD `f d.curriedType fun f => withLocalDeclD `g d.curriedType fun g => do
    withLocalDeclD `h (← rel d.curriedType d.inst f g) fun h => withLocalDeclD `p d.dom fun p => do
      mkLambdaFVars #[f, g, h, p] (mkAppN h (← unpack p n))
  let he' ← withLocalDeclD `Φ domFn fun Φ => withLocalDeclD `Ψ domFn fun Ψ => do
    withLocalDeclD `h (← rel domFn piInst Φ Ψ) fun h => forallTelescope d.curriedType fun vs _ => do
      mkLambdaFVars (#[Φ, Ψ, h] ++ vs) (mkApp h (← pack vs))
  let rflAt (ty : Expr) (lhs : Expr → MetaM Expr) := withLocalDeclD `x ty fun x => do
    mkLambdaFVars #[x] (← mkEqRefl (← lhs x))
  let h₁ ← rflAt d.curriedType fun x => pure x
  let h₂ ← rflAt domFn fun x => pure x
  let hFG ← rflAt d.curriedType fun x => pure (mkApp e (mkApp d.pre x)).headBeta
  -- Pass `name.pre` rather than the raw functional, so statements mention `name.pre`.
  return #[e, e', he, he', h₁, h₂, d.pre, d.hF, d.pre', hFG]

/-- `name.eq_bi_fixpoint`: the packed fixpoint is the BI fixpoint of `name.pre'`. -/
meta def emitEqBiFixpoint (d : FixpointData) (params : Array Expr) : TermElabM Unit := do
  let (lemma, biFix) := if d.least then
      (``Iris.MonotoneFixpoint.fix_eq_bi_least_fixpoint_of_iso, ``bi_least_fixpoint)
    else (``Iris.CoMonotoneFixpoint.fix_eq_bi_greatest_fixpoint_of_iso, ``bi_greatest_fixpoint)
  let packedFn ← withLocalDeclD `p d.dom fun p => do
    mkLambdaFVars #[p] (d.fn (← unpack p d.vtypes.size))
  emitThm (d.declName ++ `eq_bi_fixpoint) d.levels
    (← mkForallFVars params (← mkEq packedFn (← mkAppM biFix #[d.pre'])))
    (← mkLambdaFVars params (← d.rewriteFix (← mkAppM lemma (← isoArgs d))))

/-- Prove `goal` by `lemma`, unifying its conclusion with `goal` and passing `args` as its
explicit arguments, in order. Unification may unfold the (irreducible) fixpoint definitions. -/
meta def applyLemma (lemma : Name) (goal : Expr) (args : Array Expr := #[]) : MetaM Expr :=
    withTransparency .all do
  let c ← mkConstWithFreshMVarLevels lemma
  let (mvars, bis, conclusion) ← forallMetaTelescope (← inferType c)
  let explicit := (mvars.zip bis).filter (·.2.isExplicit) |>.map (·.1)
  for m in explicit, arg in args do
    unless ← isDefEq m arg do throwError "ifix: bad argument for {lemma}{indentExpr arg}"
  unless ← isDefEq conclusion goal do
    throwError "ifix: {lemma} does not prove{indentExpr goal}"
  for m in mvars do
    if !(← m.mvarId!.isAssigned) && (← isClass? (← inferType m)).isSome then
      m.mvarId!.assign (← synthInstance (← inferType m))
  let proof ← instantiateMVars (mkAppN c mvars)
  if proof.hasExprMVar then throwError "ifix: could not apply {lemma} to{indentExpr goal}"
  return proof

/-- The entailment `P ⊢ Q`. -/
meta def mkEntails (P Q : Expr) : MetaM Expr := mkAppM ``BIBase.Entails #[P, Q]

/-- `∀ vs, body` in the BI, one quantifier per variable. -/
meta def mkBIForalls (vs : Array Expr) (body : Expr) : MetaM Expr :=
  vs.foldrM (fun v body => do mkAppM ``BIBase.forall #[← mkLambdaFVars #[v] body]) body

/-- The bodies of `P = ∀ x₁ … xₙ, A`, instantiated at `us`: `#[P, ∀ x₂ … xₙ, A u₁, …, A us]`. -/
meta def instantiateBIForalls (P : Expr) (us : Array Expr) : MetaM (Array Expr) :=
  us.foldlM (init := #[P]) fun acc u => do
    let_expr BIBase.forall _ _ _ lam := acc.back! | throwError "ifix: expected a quantifier"
    return acc.push (lam.beta #[u])

/-- Prove `P ⊢ target` for `P = ∀ x₁ … xₙ, A`, where `target` is `A us` up to reducing
projections of tuples. -/
meta def elimForalls (P : Expr) (us : Array Expr) (target : Expr) : MetaM Expr := do
  let bodies ← instantiateBIForalls P us
  let mut proof ← applyLemma ``BIBase.Entails.rfl (← mkEntails bodies.back! target)
  for i in (List.range us.size).reverse do
    -- `bodies[i] ⊢ target`, from `bodies[i + 1] ⊢ target`
    let step ← applyLemma ``forall_elim (← mkEntails bodies[i]! bodies[i + 1]!) #[us[i]!]
    proof ← applyLemma ``BIBase.Entails.trans (← mkEntails bodies[i]! target) #[step, proof]
  return proof

/-- `name.ind` / `name.coind`: the Iris (co)induction principle, curried in the varying
parameters. It is derived from the packed principle `fix_iter_of_iso`/`fix_coiter_of_iso`. -/
meta def emitInd (d : FixpointData) (params : Array Expr) : TermElabM Unit := do
  let (lemma, suffix) := if d.least then (``Iris.MonotoneFixpoint.fix_iter_of_iso, `ind)
    else (``Iris.CoMonotoneFixpoint.fix_coiter_of_iso, `coind)
  withLocalDeclD `Φ d.curriedType fun Φ => do
  -- The side condition: `Φ` is nonexpansive as a function of the packed arguments. It is
  -- automatic for zero varying parameters, and stated on `Φ` itself for one.
  let packedΦ := (mkApp (← d.e) Φ).headBeta.eta
  let neType ← mkAppM ``OFE.NonExpansive #[packedΦ]
  let withNE (k : Array Expr → Expr → TermElabM Unit) : TermElabM Unit := do
    if d.vtypes.isEmpty then k #[] (← applyLemma ``OFE.const_ne neType)
    else withLocalDecl `inst .instImplicit neType fun x => k #[x] x
  withNE fun neArgs neInst => do
  let packed ← d.rewriteFix (← mkAppM lemma ((← isoArgs d) ++ #[Φ, neInst]))
  -- The packed statement `⊢ □ X -∗ Y`.
  let_expr BIBase.EmpValid _ _ wand := ← instantiateMVars (← inferType packed)
    | throwError "ifix: unexpected (co)induction principle"
  let_expr BIBase.wand _ _ X Y := wand | throwError "ifix: unexpected (co)induction principle"
  let_expr BIBase.intuitionistically _ _ allA := X
    | throwError "ifix: unexpected (co)induction principle"
  let_expr BIBase.forall _ _ _ lamA := allA | throwError "ifix: unexpected (co)induction principle"
  let_expr BIBase.forall _ _ _ _ := Y | throwError "ifix: unexpected (co)induction principle"
  -- The curried statement `⊢ □ (∀ vs, A vs) -∗ ∀ vs, B vs`.
  let (allA', allB') ← forallTelescope d.curriedType fun vs _ => do
    let (a, b) := (mkAppN (mkApp d.pre Φ) vs, mkAppN Φ vs)
    let (A, B) ← if d.least then
        pure (← mkAppM ``BIBase.wand #[a, b], ← mkAppM ``BIBase.wand #[d.fn vs, b])
      else pure (← mkAppM ``BIBase.wand #[b, a], ← mkAppM ``BIBase.wand #[b, d.fn vs])
    return (← mkBIForalls vs A, ← mkBIForalls vs B)
  let X' ← mkAppM ``BIBase.intuitionistically #[allA']
  let stmt ← mkAppM ``BIBase.EmpValid #[← mkAppM ``BIBase.wand #[X', allB']]
  -- `X' ⊢ X`: specialize the curried hypothesis at the components of each tuple.
  let toPacked ← withLocalDeclD `p d.dom fun p => do
    mkLambdaFVars #[p] (← elimForalls allA' (← unpack p d.vtypes.size) (lamA.beta #[p]))
  let hX ← applyLemma ``intuitionistically_mono (← mkEntails X' X)
    #[← applyLemma ``forall_intro (← mkEntails allA' allA) #[toPacked]]
  -- `Y ⊢ allB'`: introduce the curried quantifiers, then specialize `Y` at their tuple.
  let hY ← forallTelescope d.curriedType fun vs _ => do
    let bodies ← instantiateBIForalls allB' vs
    let mut proof ← elimForalls Y #[← pack vs] bodies.back!
    for i in (List.range vs.size).reverse do
      proof ← applyLemma ``forall_intro (← mkEntails Y bodies[i]!)
        #[← mkLambdaFVars #[vs[i]!] proof]
    return proof
  let emp ← mkAppOptM ``BIBase.emp #[some d.resTy, none]
  let curried ← mkAppM ``BIBase.wand #[X', allB']
  let proof ← applyLemma ``BIBase.Entails.trans (← mkEntails emp curried)
    #[packed, ← applyLemma ``wand_mono (← mkEntails wand curried) #[hX, hY]]
  let binders := params ++ #[Φ] ++ neArgs
  emitThm (d.declName ++ suffix) d.levels (← mkForallFVars binders stmt)
    (← mkLambdaFVars binders proof)

/-- `name.ne`: `name` is nonexpansive in its packed varying parameters, so other fixpoints can
instantiate `Φ` in `name.ind`. -/
meta def emitNonExpansive (d : FixpointData) (params : Array Expr) : TermElabM Unit := do
  if d.vtypes.isEmpty then return
  let biFix := if d.least then ``bi_least_fixpoint else ``bi_greatest_fixpoint
  let packedFn ← withLocalDeclD `p d.dom fun p => do
    mkLambdaFVars #[p] (d.fn (← unpack p d.vtypes.size))
  let packedFn := packedFn.eta
  let eq := mkAppN (mkConst (d.declName ++ `eq_bi_fixpoint) d.us) params
  let biNE ← synthInstance (← mkAppM ``OFE.NonExpansive #[← mkAppM biFix #[d.pre']])
  let neFn ← withLocalDeclD `f (← inferType packedFn) fun f => do
    mkLambdaFVars #[f] (← mkAppM ``OFE.NonExpansive #[f])
  let proof ← mkAppM ``Eq.mpr #[← mkAppM ``congrArg #[neFn, eq], biNE]
  let name := d.declName ++ `ne
  emitDef name d.levels (← mkLambdaFVars params proof)
  setReducibilityStatus name .instanceReducible
  addInstance name .global 1000

/-- Elaborate `ifix` (`least := true`) or `icofix`. -/
meta def elabFixpoint (least : Bool) (name : Ident)
    (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (ty body : Term)
    (mono : Option (TSyntax `monotoneClause)) (ne : TSyntax `nonexpClause) : CommandElabM Unit := do
  let monoTac ← match mono with
    | some clause =>
      let `(monotoneClause| monotone_by $tac) := clause | throwUnsupportedSyntax
      pure tac
    | none => `(Lean.Parser.Tactic.tacticSeq| monotone)
  let `(nonexpClause| nonexp_by $neTac) := ne | throwUnsupportedSyntax
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
      emitPre' d
      emitUnfold d
      withOFEInstances d.vtypes fun extra => do
        let params := d.fixed ++ extra
        emitPreMono d params monoTac neTac
        emitEqBiFixpoint d params
        emitNonExpansive d params
        emitInd d params
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
    mono:(monotoneClause)? ne:nonexpClause : command =>
  elabFixpoint true name binders ty body mono ne

/-- Greatest Iris fixpoint, defined with `partial_fixpoint`. -/
elab "icofix " name:ident binders:bracketedBinder* " : " ty:term " := " body:term
    mono:(monotoneClause)? ne:nonexpClause : command =>
  elabFixpoint false name binders ty body mono ne

/-- Guarded Iris fixpoint (stub). -/
elab mods:declModifiers "iguarded " name:ident binders:bracketedBinder* " : " ty:term
    " := " body:term (contractiveClause)? : command =>
  elabStub mods name binders ty body true

end Iris.Fixpoint
