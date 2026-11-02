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
orders in `Iris.BI.Lib.Lattice`. The library works on predicates of one argument, so the varying
parameters are packed into a tuple (`Tupling`). The `monotone_by` proof gives `partial_fixpoint` its
monotonicity proof, and the lemmas about `lfp`/`gfp`, restated for the definition.

`iguarded` defines guarded fixpoints with `partial_fixpoint` too, over the approximation domain
`Iris.Approx`: the body is lifted with `Approx.lift`, which is monotone for any body, and
contractiveness makes the fixpoint exact. -/

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
free variables. A recursive definition is `fun fixed => fix F hF`. A non-recursive one is left as
a plain definition: every parameter is fixed, and `F` is the constant `fun _ => body`. -/
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
  /-- The functional, and for a recursive definition, its monotonicity proof. -/
  F : Expr
  hF? : Option Expr

namespace FixpointData

meta def us (d : FixpointData) : List Level := d.levels.map mkLevelParam

/-- `name` applied to the fixed parameters and the varying arguments `vs`. -/
meta def fn (d : FixpointData) (vs : Array Expr) : Expr :=
  mkAppN (mkConst d.declName d.us) (d.perm.buildArgs d.fixed vs)

meta def pre (d : FixpointData) : Expr :=
  mkAppN (mkConst (d.declName ++ `pre) d.us) d.fixed

/-- `name` applied to the fixed parameters, as a function of the varying ones. -/
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
        | throwError "ifix: unexpected `partial_fixpoint` definition{indentExpr body}"
      let prop ← forallTelescope curriedType fun _ resTy => pure resTy
      k { least, declName, levels, perm, fixed, curriedType, prop, F, hF? := hF }
  | none =>
    let info ← getConstInfo declName
    let levels := info.levelParams
    let value := info.instantiateValueLevelParams! (levels.map mkLevelParam)
    lambdaTelescope value fun fixed body => do
      let prop ← inferType body
      k { least, declName, levels, perm := Array.ofFn fun (i : Fin fixed.size) => some i.val,
          fixed, curriedType := prop, prop, F := .lam `self prop body .default, hF? := none }

/-- `name.pre`: the curried functional built by `partial_fixpoint`. -/
meta def emitPre (d : FixpointData) : TermElabM Unit := do
  emitDef (d.declName ++ `pre) d.levels (← mkLambdaFVars d.fixed d.F)

/-- `name.unfold`: one step of `fix_eq`, stated with `name` and `name.pre`. -/
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

/-! ### Tuples of arguments

The library states fixpoints on predicates `A → PROP` of one argument. `partial_fixpoint` defines
them on the curried type `∀ x y, PROP` of the varying parameters. A `Tupling` packs the varying
parameters into one tuple `⟨x, y⟩ : A`, a nest of `PSigma`s, and translates between the two. -/

/-- The type of tuples of the parameters of `∀ xs, PROP`: `PUnit`, the single parameter's type, or
a nest of `PSigma`s. -/
meta partial def tupleType : Expr → MetaM Expr
  | .forallE n d b bi => do
    unless b.isForall do return d
    withLocalDecl n bi d fun x => do mkAppM ``PSigma #[← mkLambdaFVars #[x] (← tupleType (b.instantiate1 x))]
  | _ => return mkConst ``PUnit [Level.one]

/-- The tuple of `xs`, for parameters `∀ xs, PROP`. -/
meta partial def mkTuple : Expr → List Expr → MetaM Expr
  | .forallE n d b bi, x :: xs => do
    unless b.isForall do return x
    let β ← withLocalDecl n bi d fun y => do mkLambdaFVars #[y] (← tupleType (b.instantiate1 y))
    mkAppOptM ``PSigma.mk #[d, β, x, ← mkTuple (b.instantiate1 x) xs]
  | _, _ => return mkConst ``PUnit.unit [Level.one]

/-- The components of the tuple `p`, for parameters `∀ xs, PROP`. -/
meta partial def mkProjs : Expr → Expr → MetaM (Array Expr)
  | .forallE _ _ b _, p => do
    unless b.isForall do return #[p]
    let x ← mkAppM ``PSigma.fst #[p]
    return #[x] ++ (← mkProjs (b.instantiate1 x) (← mkAppM ``PSigma.snd #[p]))
  | _, _ => return #[]

/-- Name the binders that `spellOut` introduces (`x`, `x'`) after the varying parameters: each run
of them, such as `∀ x x'`, is renamed `names` in order. -/
meta partial def renameArgs (names : List Name) (e : Expr) : Expr :=
  go names e
where
  go (rest : List Name) : Expr → Expr
    | .forallE n t b bi => let (n, rest') := pick n rest; .forallE n (go names t) (go rest' b) bi
    | .lam n t b bi => let (n, rest') := pick n rest; .lam n (go names t) (go rest' b) bi
    | .app f a => .app (go names f) (go rest a)
    | .mdata d e => .mdata d (go rest e)
    | e => e
  pick (n : Name) : List Name → Name × List Name
    | m :: rest => if n == `x || n == `x' || n == `p then (m, rest) else (n, names)
    | [] => (n, names)

structure Tupling where
  /-- The curried type `∀ xs, PROP`, `PROP`, and the tuple type `A`. -/
  curried : Expr
  prop : Expr
  A : Expr
  arity : Nat
  /-- `uncurry := fun f p => f p.1 p.2` and `curry := fun Φ x y => Φ ⟨x, y⟩`. -/
  uncurry : Expr
  curry : Expr

namespace Tupling

meta def ofCurried (curried : Expr) : MetaM Tupling := do
  let (prop, arity) ← forallTelescope curried fun xs r => pure (r, xs.size)
  let A ← tupleType curried
  let uncurry ← withLocalDeclD `f curried fun f => withLocalDeclD `p A fun p => do
    mkLambdaFVars #[f, p] (mkAppN f (← mkProjs curried p))
  let curry ← withLocalDeclD `Φ (← mkArrow A prop) fun Φ => forallTelescope curried fun xs _ => do
    mkLambdaFVars (#[Φ] ++ xs) (mkApp Φ (← mkTuple curried xs.toList))
  return { curried, prop, A, arity, uncurry, curry }

/-- `fun Φ => uncurry (F (curry Φ))`: the functional `F` on predicates on tuples. -/
meta def conj (T : Tupling) (F : Expr) : MetaM Expr := do
  withLocalDeclD `Φ (← mkArrow T.A T.prop) fun Φ => do
    mkLambdaFVars #[Φ] (T.uncurry.beta #[(mkApp F (T.curry.beta #[Φ])).headBeta])

/-- `monotone uncurry` and `monotone curry`: they apply the pointwise order argument by argument. -/
meta def monoUncurry (T : Tupling) : MetaM Expr :=
  withLocalDeclD `f T.curried fun f => withLocalDeclD `g T.curried fun g => do
  withLocalDeclD `h (← mkAppM ``Lean.Order.PartialOrder.rel #[f, g]) fun h => do
  withLocalDeclD `p T.A fun p => do
    mkLambdaFVars #[f, g, h, p] (mkAppN h (← mkProjs T.curried p))

meta def monoCurry (T : Tupling) : MetaM Expr := do
  let predTy ← mkArrow T.A T.prop
  withLocalDeclD `Φ predTy fun Φ => withLocalDeclD `Ψ predTy fun Ψ => do
  withLocalDeclD `h (← mkAppM ``Lean.Order.PartialOrder.rel #[Φ, Ψ]) fun h => do
  forallTelescope T.curried fun xs _ => do
    mkLambdaFVars (#[Φ, Ψ, h] ++ xs) (mkApp h (← mkTuple T.curried xs.toList))

/-- `∀ a, f a = g a` by `rfl`, for a binder of type `dom`. -/
meta def pointwiseRfl (dom : Expr) (f g : Expr → MetaM Expr) : MetaM Expr :=
  withLocalDeclD `a dom fun a => do
    mkLambdaFVars #[a] (← mkExpectedTypeHint (← mkEqRefl (← f a)) (← mkEq (← f a) (← g a)))

/-- `∀ Φ, uncurry (curry Φ) = Φ`, by `rfl`. -/
meta def uncurryCurry (T : Tupling) : MetaM Expr := do
  let predTy ← mkArrow T.A T.prop
  pointwiseRfl predTy (fun Φ => pure (T.uncurry.beta #[T.curry.beta #[Φ]])) pure

/-- `F` is monotone, from `BIMono (conj F)`. -/
meta def monotone (T : Tupling) (least : Bool) (F hG : Expr) : MetaM Expr := do
  let ns := if least then ``MonotoneFixpoint.monotone_of_bimono
    else ``CoMonotoneFixpoint.monotone_of_bimono
  let G ← T.conj F
  let hcomm ← pointwiseRfl T.curried (fun a => pure (mkApp F a))
    (fun a => pure (T.curry.beta #[mkApp G (T.uncurry.beta #[a])]))
  mkAppOptM ``monotone_conj #[T.curried, ← mkArrow T.A T.prop, none, none, F, G, T.uncurry,
    T.curry, ← T.monoUncurry, ← T.monoCurry, ← mkAppM ns #[hG], hcomm]

/-- Rewrite quantifiers over tuples, and over predicates on them, into curried ones. Returns the new
statement, and the equation from the old one. -/
meta def spellOut (T : Tupling) (type : Expr) : MetaM (Expr × Option Expr) := do
  let mut thms ← [``bimono_def, ``forall_psigma, ``forall_punit, ``bi_forall_psigma,
    ``bi_forall_punit].foldlM (·.addConst ·) ({} : SimpTheorems)
  -- With one parameter, the tuple is the parameter.
  unless T.arity == 1 do
    let h ← T.uncurryCurry
    thms ← thms.add (.other `forall_iso) #[] (← mkAppM ``forall_iso #[T.uncurry, T.curry, h])
    thms ← thms.add (.other `bi_forall_iso) #[]
      (← mkAppOptM ``bi_forall_iso #[T.prop, none, none, none, T.uncurry, T.curry, h])
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simp type ctx
  -- `fun x y => Φ x y` is `Φ`, by definition.
  let type ← Core.transform r.expr (post := fun e => return .done e.eta)
  return (type, r.proof?)

/-- Restore the binder names that `spellOut` replaced: predicates on tuples are named as before,
and the components of a tuple after the parameters. -/
meta def rename (T : Tupling) (before after : Expr) : MetaM Expr := do
  let preds := collect (← mkArrow T.A T.prop) before #[]
  return renameArgs T.curried.getForallBinderNames (renamePreds T.curried preds.toList after).1
where
  collect (ty : Expr) : Expr → Array Name → Array Name
    | .forallE n d b _, acc => collect ty b (collect ty d (if d == ty then acc.push n else acc))
    | .lam n d b _, acc => collect ty b (collect ty d (if d == ty then acc.push n else acc))
    | .app f a, acc => collect ty a (collect ty f acc)
    | .mdata _ e, acc => collect ty e acc
    | _, acc => acc
  renamePreds (ty : Expr) : List Name → Expr → Expr × List Name
    | ns, .forallE n d b bi =>
      let (n, ns) := if d == ty then (ns.headD n, ns.drop 1) else (n, ns)
      let (d, ns) := renamePreds ty ns d
      let (b, ns) := renamePreds ty ns b
      (.forallE n d b bi, ns)
    | ns, .lam n d b bi =>
      let (n, ns) := if d == ty then (ns.headD n, ns.drop 1) else (n, ns)
      let (d, ns) := renamePreds ty ns d
      let (b, ns) := renamePreds ty ns b
      (.lam n d b bi, ns)
    | ns, .app f a =>
      let (f, ns) := renamePreds ty ns f
      let (a, ns) := renamePreds ty ns a
      (.app f a, ns)
    | ns, .mdata m e => let (e, ns) := renamePreds ty ns e; (.mdata m e, ns)
    | ns, e => (e, ns)

end Tupling

/-- Prove `BIMono (conj F)`, by `tac` on its curried statement. Returns the curried statement, a
proof of it, and the proof of `BIMono (conj F)`. -/
meta def proveMono (T : Tupling) (F : Expr) (tac : TSyntax ``Lean.Parser.Tactic.tacticSeq) :
    TermElabM (Expr × Expr × Expr) := do
  let stmt ← mkAppM ``BIMono #[← T.conj F]
  let (curried, eq?) ← T.spellOut stmt
  let curried ← T.rename ((← unfoldDefinition? stmt).getD stmt) curried
  let proof ← elabTermEnsuringType (← `(by $tac)) curried
  synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  return (curried, proof, ← match eq? with
    | some eq => mkEqMPR eq proof
    | none => pure proof)

/-- `ifix_monotone tac` proves `monotone F` for the functional `F` of an `ifix`, by `tac` on the
curried statement of `BIMono`. -/
syntax (name := ifixMonotone) "ifix_monotone " Lean.Parser.Tactic.tacticSeq : tactic
@[inherit_doc ifixMonotone]
syntax (name := icofixMonotone) "icofix_monotone " Lean.Parser.Tactic.tacticSeq : tactic

meta def evalFixMonotone (least : Bool) (tac : TSyntax ``Lean.Parser.Tactic.tacticSeq) :
    Tactic.TacticM Unit := Tactic.withMainContext do
  let goal ← Tactic.getMainGoal
  let_expr Lean.Order.monotone τ _ _ _ F := ← whnfR (← goal.getType)
    | throwError "ifix_monotone: expected a `monotone` goal"
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

/-- `name.pre_mono`: the `monotone_by` proof that `name.pre` is monotone, stated with its arguments
spelled out. Returns `BIMono (conj name.pre)`, for the lemmas. -/
meta def emitPreMono (d : FixpointData) (T : Tupling)
    (monoTac : TSyntax ``Lean.Parser.Tactic.tacticSeq) : TermElabM Expr := do
  let (curried, proof, hG) ← proveMono T d.pre monoTac
  emitThm (d.declName ++ `pre_mono) d.levels (← mkForallFVars d.fixed curried)
    (← mkLambdaFVars d.fixed proof)
  return hG

/-- The lemmas about `lfp`/`gfp` in `Iris.BI.Lib.Lattice`, restated for each definition. -/
meta def fixpointLemmas (least : Bool) : List (Name × Name) :=
  if least then
    [(`unfold_mp, ``MonotoneFixpoint.fix_unfold_mp), (`unfold_mpr, ``MonotoneFixpoint.fix_unfold_mpr),
     (`iter, ``MonotoneFixpoint.fix_iter), (`ind, ``MonotoneFixpoint.fix_ind),
     (`ind_wf, ``MonotoneFixpoint.fix_ind_wf),
     (`affine, ``MonotoneFixpoint.fix_affine), (`absorbing, ``MonotoneFixpoint.fix_absorbing),
     (`persistent_affine, ``MonotoneFixpoint.fix_persistent_affine),
     (`persistent_absorbing, ``MonotoneFixpoint.fix_persistent_absorbing)]
  else
    [(`unfold_mp, ``CoMonotoneFixpoint.fix_unfold_mp),
     (`unfold_mpr, ``CoMonotoneFixpoint.fix_unfold_mpr),
     (`coiter, ``CoMonotoneFixpoint.fix_coiter), (`coind, ``CoMonotoneFixpoint.fix_coind),
     (`paco, ``CoMonotoneFixpoint.fix_paco),
     (`absorbing, ``CoMonotoneFixpoint.fix_absorbing)]

/-- `name.suffix`: the lemma `lemma` about `lfp (conj name.pre) hG` (or `gfp`), stated with `name`
and spelled out over the varying parameters. -/
meta def emitLemma (d : FixpointData) (T : Tupling) (hG : Expr) (suffix lemma : Name) :
    TermElabM Unit := do
  let G ← T.conj d.pre
  let args : Array (Option Expr) := #[d.prop, none, T.A, G, hG]
  let (fixName, monoName) := if d.least
    then (``MonotoneFixpoint.lfp, ``MonotoneFixpoint.monotone_of_bimono)
    else (``CoMonotoneFixpoint.gfp, ``CoMonotoneFixpoint.monotone_of_bimono)
  let fixpoint ← mkAppOptM fixName args
  let general ← mkAppOptM lemma args
  -- `lfp (conj name.pre) _ = uncurry name`: `fix_iso` across currying, and for a non-recursive
  -- `name`, one step of `fix_eq`.
  let fn := T.uncurry.beta #[← d.curriedFn]
  let hF ← T.monotone d.least d.pre hG
  let iso ← mkAppOptM ``fix_iso #[T.curried, ← mkArrow T.A T.prop, none, none, d.pre, G, hF,
    ← mkAppM monoName #[hG], T.uncurry, T.curry, ← T.monoUncurry, ← T.uncurryCurry,
    ← Tupling.pointwiseRfl T.curried (fun a => pure (T.curry.beta #[T.uncurry.beta #[a]])) pure,
    ← Tupling.pointwiseRfl T.curried (fun a => pure (T.uncurry.beta #[mkApp d.pre a]))
      (fun a => pure (mkApp G (T.uncurry.beta #[a])))]
  let eq ← mkEqSymm iso
  let eq ← match d.hF? with
    | some _ => pure eq
    | none => mkEqTrans eq (← mkCongrArg T.uncurry (← mkAppM ``Lean.Order.fix_eq #[hF]))
  let eq ← mkExpectedTypeHint eq (← mkEq fixpoint fn)
  let before ← instantiateMVars (← inferType general)
  let body ← kabstract before fixpoint
  let proof ← mkEqNDRec (.lam `f (← mkArrow T.A T.prop) body .default) general eq
  let (type, eq?) ← T.spellOut (body.instantiate1 fn)
  let proof ← match eq? with
    | some eq => mkEqMP eq proof
    | none => pure proof
  let type ← T.rename before type
  emitThm (d.declName ++ suffix) d.levels (← mkForallFVars d.fixed type)
    (← mkLambdaFVars d.fixed proof)

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
    let errors ← errorCount
    let monotone ← if least then `(tactic| ifix_monotone $monoTac)
      else `(tactic| icofix_monotone $monoTac)
    elabCommand (← `(command| def $name:ident $binders* : $ty := $body
      partial_fixpoint monotonicity by $monotone:tactic))
    dropNotRecursiveWarning
    -- If the definition failed, Lean has already reported why.
    if (← errorCount) > errors then return
    -- Resolve the actual name, which is mangled in a private scope.
    let declName ← liftCoreM <| realizeGlobalConstNoOverload name
    liftTermElabM <| withFixpointData least declName fun d => do
      emitPre d
      emitUnfold d
      let T ← Tupling.ofCurried d.curriedType
      let hG ← emitPreMono d T monoTac
      for (suffix, lemma) in fixpointLemmas least do emitLemma d T hG suffix lemma
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

/-- Add `attr` to the attributes in `mods`. -/
meta def addAttribute (mods : TSyntax ``Lean.Parser.Command.declModifiers)
    (attr : TSyntax ``Lean.Parser.Term.attrInstance) :
    CommandElabM (TSyntax ``Lean.Parser.Command.declModifiers) := do
  let old : Array (TSyntax ``Lean.Parser.Term.attrInstance) := match mods.raw[1].getOptional? with
    | some stx => stx[1].getSepArgs.map (⟨·⟩)
    | none => #[]
  let all : Syntax.TSepArray ``Lean.Parser.Term.attrInstance "," := .ofElems (old.push attr)
  let attrs ← `(Lean.Parser.Term.attributes| @[$all,*])
  return ⟨mods.raw.setArg 1 (mkNullNode #[attrs])⟩

/-- Elaborate `iguarded`. For `iguarded name binders : ty := body`, it emits
* `name.pre : (∀ binders, ty) → (∀ binders, ty) := fun name binders => body`,
* `name.pre.contractive`, from the `contractive_by` proof,
* `name.approx : Approx (∀ binders, ty) := lift name.pre name.approx`, by `partial_fixpoint`,
* `name.impl`, a `partial def` running the recursion (an `opaque` constant without binders),
  which compiled code uses for `name`,
* `name binders : ty`, the point of `name.approx`, and `name.unfold`, by `lift_fix_get`.

Everything is generated as syntax: the body is elaborated, and the fixpoint defined, by Lean. -/
meta def elabGuarded (mods : TSyntax ``Lean.Parser.Command.declModifiers) (name : Ident)
    (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (ty body : Term)
    (contractive : Option (TSyntax `contractiveClause)) : CommandElabM Unit := do
  let some clause := contractive | throwErrorAt name "iguarded: provide a contractive_by proof"
  let `(contractiveClause| contractive_by $tac) := clause | throwUnsupportedSyntax
  let isPrivate := (← elabModifiers mods).isPrivate
  let vis ← if isPrivate then `(declModifiers| private) else `(declModifiers|)
  let implMods ← if isPrivate then `(declModifiers| private partial) else `(declModifiers| partial)
  let suffixed (s : Name) := mkIdentFrom name (name.getId ++ s)
  let (pre, approx) := (suffixed `pre, suffixed `approx)
  let (contractiveName, unfold) := (suffixed (`pre ++ `contractive), suffixed `unfold)
  let impl := suffixed `impl
  let args ← liftMacroM <| binderArgs binders
  let funBinders : TSyntaxArray ``Lean.Parser.Term.funBinder := binders.map (⟨·.raw⟩)
  let lam (e : Term) : CommandElabM Term :=
    if binders.isEmpty then pure e else `(fun $funBinders* => $e)
  let app (f : Ident) : CommandElabM Term := if args.isEmpty then pure f else `($f $args*)
  let sig ← if binders.isEmpty then pure ty else `(∀ $binders*, $ty)
  elabCommand (← `(command|
    $vis:declModifiers def $pre : $sig → $sig := fun ($name : $sig) => $(← lam body)))
  elabCommand (← `(command|
    instance $contractiveName:ident : Iris.OFE.Contractive ($pre : $sig → $sig) where
      distLater_dist := by $tac))
  elabCommand (← `(command|
    $vis:declModifiers def $approx : Iris.Approx $sig := Iris.Approx.lift $pre $approx
    partial_fixpoint monotonicity Iris.Approx.lift_mono _))
  -- `Approx.get` is noncomputable, so compiled code runs the recursion directly instead. Without
  -- arguments there is nothing to recurse on, and evaluating would not terminate anyway.
  if binders.isEmpty then
    elabCommand (← `(command| $vis:declModifiers opaque $impl : $ty))
  else
    elabCommand (← `(command|
      $implMods:declModifiers def $impl $binders* : $ty := $pre $(← lam (← app impl)) $args*))
  let nameMods ← addAttribute mods (← `(Lean.Parser.Term.attrInstance| implemented_by $impl:ident))
  elabCommand (← `(command|
    $nameMods:declModifiers def $name $binders* : $ty := Iris.Approx.get $approx $args*))
  -- `lift_fix_get` on the unfolding equation of `name.approx`, applied to the arguments.
  let approxEq := mkIdentFrom name (name.getId ++ `approx ++ `eq_1)
  elabCommand (← `(command|
    theorem $unfold $binders* :
        $(← app name) = $pre $(← lam (← `(($(← app name) : $ty)))) $args* :=
      congrArg (fun f => f $args*) (Iris.Approx.lift_fix_get $pre (Eq.symm $approxEq))))

/-- Guarded Iris fixpoint, defined with `partial_fixpoint` over approximations. The body must be
contractive in the recursive function. -/
elab mods:declModifiers "iguarded " name:ident binders:bracketedBinder* " : " ty:term
    " := " body:term contractive:(contractiveClause)? : command =>
  elabGuarded mods name binders ty body contractive

end Iris.Fixpoint
