/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.BI.Lib.Lattice

/-! # Tuples of arguments

The library states fixpoints for predicates `A → PROP`; `partial_fixpoint` works on the curried
`∀ x y, PROP`. A `Tupling` packs the parameters into a `PSigma` tuple `⟨x, y⟩ : A`: lemmas are
applied on tuples, then their statements are curried back. -/

public section

namespace Iris.Fixpoint
open Lean Elab Command Meta Term BI

/-- Reduce `(fun x => e) a`, `⟨a, b⟩.1` and `fun x y => Φ x y` everywhere. -/
meta def betaEta (e : Expr) : MetaM Expr :=
  Core.transform e (post := fun e => do
    -- A beta step may expose new redexes: visit the result again.
    if e.isHeadBetaTarget then return .visit e.headBeta
    if (e.isAppOfArity ``PSigma.fst 3 || e.isAppOfArity ``PSigma.snd 3) &&
        e.appArg!.isAppOfArity ``PSigma.mk 4 then
      return .visit (e.appArg!.getArg! (if e.isAppOf ``PSigma.fst then 2 else 3))
    return .done e.eta)

/-- The tuples of the parameters of `∀ xs, PROP`: `PUnit`, the single type, or nested `PSigma`s. -/
meta partial def tupleType : Expr → MetaM Expr
  | .forallE n d b bi => do
    unless b.isForall do return d
    withLocalDecl n bi d fun x => do
      mkAppM ``PSigma #[← mkLambdaFVars #[x] (← tupleType (b.instantiate1 x))]
  | _ => return mkConst ``PUnit [Level.one]

/-- The tuple of `xs`, for parameters `∀ xs, PROP`. -/
meta partial def mkTuple : Expr → List Expr → MetaM Expr
  | .forallE n d b bi, x :: xs => do
    unless b.isForall do return x
    let β ← withLocalDecl n bi d fun y => do mkLambdaFVars #[y] (← tupleType (b.instantiate1 y))
    mkAppOptM ``PSigma.mk #[d, β, x, ← mkTuple (b.instantiate1 x) xs]
  | .forallE .., [] => throwError "mkTuple: too few arguments"
  | _, _ => return mkConst ``PUnit.unit [Level.one]

/-- The components of the tuple `p`, for parameters `∀ xs, PROP`. -/
meta partial def mkProjs : Expr → Expr → MetaM (Array Expr)
  | .forallE _ _ b _, p => do
    unless b.isForall do return #[p]
    let x ← mkAppM ``PSigma.fst #[p]
    return #[x] ++ (← mkProjs (b.instantiate1 x) (← mkAppM ``PSigma.snd #[p]))
  | _, _ => return #[]

/-- `(∀ p, P p) = ∀ xs, P ⟨xs⟩`, in `Prop` and in the BI, keeping the parameters' names. Proved
by normalizing both sides with `forall_psigma`. -/
meta def splitForall (curried prop A : Expr) : MetaM (Array Expr) := do
  let generic ← [``forall_psigma, ``forall_punit, ``bi_forall_psigma, ``bi_forall_punit].foldlM
    (·.addConst ·) ({} : SimpTheorems)
  let ctx ← Simp.mkContext (simpTheorems := #[generic]) (congrTheorems := ← getSimpCongrTheorems)
  let biForall (x b : Expr) : MetaM Expr := do mkAppM ``BIBase.forall #[← mkLambdaFVars #[x] b]
  let lemma (codomain : Expr) (all : Expr → Expr → MetaM Expr) : MetaM Expr := do
    withLocalDeclD `P (← mkArrow A codomain) fun P => do
      let lhs ← withLocalDeclD `p A fun p => do all p (mkApp P p)
      let rhs ← forallTelescope curried fun xs _ => do
        xs.foldrM all (mkApp P (← mkTuple curried xs.toList))
      let (l, _) ← simp lhs ctx
      let (r, _) ← simp rhs ctx
      unless ← isDefEq l.expr r.expr do throwError "splitForall: {lhs} and {rhs} differ"
      let proof ← match l.proof?, r.proof? with
        | some pl, some pr => mkEqTrans pl (← mkEqSymm pr)
        | some pl, none => pure pl
        | none, some pr => mkEqSymm pr
        | none, none => mkEqRefl lhs
      mkLambdaFVars #[P] (← mkExpectedTypeHint proof (← mkEq lhs rhs))
  return #[← lemma (.sort .zero) fun x b => mkForallFVars #[x] b, ← lemma prop biForall]

/-- `∀ a, f a = g a` by `rfl`, for a binder of type `dom`. -/
meta def pointwiseRfl (dom : Expr) (f g : Expr → MetaM Expr) : MetaM Expr :=
  withLocalDeclD `a dom fun a => do
    let fa ← f a
    mkLambdaFVars #[a] (← mkExpectedTypeHint (← mkEqRefl fa) (← mkEq fa (← g a)))

/-- Cast `proof` along `eq? : a = b`, either way; `none` means definitionally equal. -/
meta def castAlong (eq? : Option Expr) (proof : Expr) (forward : Bool) : MetaM Expr :=
  match eq? with
  | none => pure proof
  | some eq => if forward then mkEqMP eq proof else mkEqMPR eq proof

/-- The varying parameters of a fixpoint, packed into a tuple. -/
structure Tupling where
  /-- The curried type `∀ xs, PROP`. -/
  curried : Expr
  /-- `PROP`. -/
  prop : Expr
  /-- The type of tuples of `xs`. -/
  A : Expr
  /-- The number of parameters `xs`. -/
  arity : Nat
  /-- `fun f p => f p.1 p.2`. -/
  uncurry : Expr
  /-- `fun Φ x y => Φ ⟨x, y⟩`. -/
  curry : Expr
  /-- The rewrites that `curryStatement` uses, unless `arity = 1`. -/
  thms : SimpTheorems

namespace Tupling

/-- `fun Φ => uncurry (F (curry Φ))`: the functional `F` on predicates on tuples. -/
meta def conj (T : Tupling) (F : Expr) : MetaM Expr := do
  withLocalDeclD `Φ (← mkArrow T.A T.prop) fun Φ => do
    mkLambdaFVars #[Φ] (T.uncurry.beta #[(mkApp F (T.curry.beta #[Φ])).headBeta])

/-- `monotone uncurry`: the pointwise order applies argument by argument. -/
meta def monoUncurry (T : Tupling) : MetaM Expr :=
  withLocalDeclD `f T.curried fun f => withLocalDeclD `g T.curried fun g => do
  withLocalDeclD `h (← mkAppM ``Lean.Order.PartialOrder.rel #[f, g]) fun h => do
  withLocalDeclD `p T.A fun p => do
    mkLambdaFVars #[f, g, h, p] (mkAppN h (← mkProjs T.curried p))

/-- `monotone curry`. -/
meta def monoCurry (T : Tupling) : MetaM Expr := do
  let predTy ← mkArrow T.A T.prop
  withLocalDeclD `Φ predTy fun Φ => withLocalDeclD `Ψ predTy fun Ψ => do
  withLocalDeclD `h (← mkAppM ``Lean.Order.PartialOrder.rel #[Φ, Ψ]) fun h => do
  forallTelescope T.curried fun xs _ => do
    mkLambdaFVars (#[Φ, Ψ, h] ++ xs) (mkApp h (← mkTuple T.curried xs.toList))

/-- `NonExpansive uncurry`: step-indexed equality applies argument by argument. -/
meta def neUncurry (T : Tupling) : MetaM Expr := do
  let proof ← withLocalDeclD `n (mkConst ``Nat) fun n =>
    withLocalDeclD `f T.curried fun f => withLocalDeclD `g T.curried fun g => do
    withLocalDeclD `h (← mkAppM ``OFE.Dist #[n, f, g]) fun h => withLocalDeclD `p T.A fun p => do
      mkLambdaFVars #[n, f, g, h, p] (mkAppN h (← mkProjs T.curried p))
  mkAppOptM ``OFE.NonExpansive.mk #[T.curried, ← mkArrow T.A T.prop, none, none, T.uncurry, proof]

/-- `NonExpansive curry`. -/
meta def neCurry (T : Tupling) : MetaM Expr := do
  let predTy ← mkArrow T.A T.prop
  let proof ← withLocalDeclD `n (mkConst ``Nat) fun n =>
    withLocalDeclD `Φ predTy fun Φ => withLocalDeclD `Ψ predTy fun Ψ => do
    withLocalDeclD `h (← mkAppM ``OFE.Dist #[n, Φ, Ψ]) fun h =>
    forallTelescope T.curried fun xs _ => do
      mkLambdaFVars (#[n, Φ, Ψ, h] ++ xs) (mkApp h (← mkTuple T.curried xs.toList))
  mkAppOptM ``OFE.NonExpansive.mk #[predTy, T.curried, none, none, T.curry, proof]

/-- `∀ Φ, uncurry (curry Φ) = Φ`, by `rfl`. -/
meta def uncurryCurry (T : Tupling) : MetaM Expr := do
  let predTy ← mkArrow T.A T.prop
  pointwiseRfl predTy (fun Φ => pure (T.uncurry.beta #[T.curry.beta #[Φ]])) pure

/-- `monotone F`, from `hG : BIMono (conj F)`. `bimonoOf?` reads `hG` back off this shape. -/
meta def monotone (T : Tupling) (least : Bool) (F hG : Expr) : MetaM Expr := do
  let ofBimono := if least then ``MonotoneFixpoint.monotone_of_bimono
    else ``CoMonotoneFixpoint.monotone_of_bimono
  let G ← T.conj F
  let hcomm ← pointwiseRfl T.curried (fun a => pure (mkApp F a))
    (fun a => pure (T.curry.beta #[mkApp G (T.uncurry.beta #[a])]))
  mkAppOptM ``monotone_conj #[T.curried, ← mkArrow T.A T.prop, none, none, F, G, T.uncurry,
    T.curry, ← T.monoUncurry, ← T.monoCurry, ← mkAppM ofBimono #[hG], hcomm]

/-- `conj` as a map, its inverse `unconj`, and `∀ G, conj (unconj G) = G`, by `rfl`. -/
meta def conjIso (T : Tupling) : MetaM (Expr × Expr × Expr) := do
  let predTy ← mkArrow T.A T.prop
  let conjMap ← withLocalDeclD `G (← mkArrow T.curried T.curried) fun G => do
    mkLambdaFVars #[G] (← T.conj G)
  let unconjMap ← withLocalDeclD `G (← mkArrow predTy predTy) fun G =>
    withLocalDeclD `f T.curried fun f => do
      mkLambdaFVars #[G, f] (T.curry.beta #[mkApp G (T.uncurry.beta #[f])])
  let h ← pointwiseRfl (← mkArrow predTy predTy)
    (fun G => pure (conjMap.beta #[unconjMap.beta #[G]])) pure
  return (conjMap, unconjMap, h)

/-- The `Tupling` of `∀ xs, PROP`. Its rewrites split quantifiers over tuples (`splitForall`) and
curry those over predicates and functionals (`forall_iso` along `uncurry` and `conj`). -/
meta def ofCurried (curried : Expr) : MetaM Tupling := do
  let (prop, arity) ← forallTelescope curried fun xs r => pure (r, xs.size)
  let A ← tupleType curried
  let uncurry ← withLocalDeclD `f curried fun f => withLocalDeclD `p A fun p => do
    mkLambdaFVars #[f, p] (mkAppN f (← mkProjs curried p))
  let curry ← withLocalDeclD `Φ (← mkArrow A prop) fun Φ => forallTelescope curried fun xs _ => do
    mkLambdaFVars (#[Φ] ++ xs) (mkApp Φ (← mkTuple curried xs.toList))
  let T : Tupling := { curried, prop, A, arity, uncurry, curry, thms := {} }
  -- With one parameter, the tuple is the parameter.
  if arity == 1 then return T
  let mut thms : SimpTheorems := {}
  for h in ← splitForall curried prop A do thms ← thms.add (.other `split_forall) #[] h
  let h ← T.uncurryCurry
  thms ← thms.add (.other `forall_iso) #[] (← mkAppM ``forall_iso #[uncurry, curry, h])
  thms ← thms.add (.other `bi_forall_iso) #[]
    (← mkAppOptM ``bi_forall_iso #[prop, none, none, none, uncurry, curry, h])
  let (conjMap, unconjMap, h) ← T.conjIso
  thms ← thms.add (.other `forall_conj_iso) #[] (← mkAppM ``forall_iso #[conjMap, unconjMap, h])
  return { T with thms }

/-- `type`, curried by its structure: a quantifier over tuples becomes quantifiers over the
parameters, under their names, and one over a predicate or functional on tuples becomes one over a
curried one, under its own name. -/
meta partial def curryBinders (T : Tupling) (type : Expr) : MetaM Expr := do
  let predTy ← mkArrow T.A T.prop
  let funcTy ← mkArrow predTy predTy
  let (conjMap, _, _) ← T.conjIso
  let params := T.curried.getForallBinderNames
  let arg? := if T.arity == 1 then params.head? else none
  -- Library binders named like a parameter (or its primed copy, used by `ne`) are primed.
  let taken := params ++ params.map (·.appendAfter "'")
  let yield (n : Name) : Name := Id.run do
    let mut n := n
    for _ in [:taken.length] do
      unless taken.contains n do break
      n := n.appendAfter "'"
    return n
  -- Curry the binder `n : d`: its new binders, and its value in their terms.
  let binder {α} (n : Name) (bi : BinderInfo) (d : Expr) (k : Array Expr → Expr → MetaM α) :
      MetaM α := do
    -- With one parameter, only the library's point binders `x` and `y` take its name: its type
    -- may be that of others too, such as `ne`'s step index.
    if let some arg := arg? then
      let point := (n == `x || n == `y) && (← isDefEq d T.A)
      return ← withLocalDecl (if point then arg else yield n) bi d fun x => k #[x] x
    -- Up to defeq: the library's copy of a type need not be the same term.
    if ← isDefEq d T.A then
      -- The new binders take the library binder's info, except instances.
      forallTelescope T.curried fun xs _ => do
        let infos ← xs.mapM fun x => do
          let inst := (← x.fvarId!.getBinderInfo).isInstImplicit
          return (x.fvarId!, if inst then .instImplicit else bi)
        withNewBinderInfos infos do k xs (← mkTuple T.curried xs.toList)
    else if ← isDefEq d predTy then
      withLocalDecl (yield n) bi T.curried fun x => k #[x] (T.uncurry.beta #[x])
    else if ← isDefEq d funcTy then
      withLocalDecl (yield n) bi (← mkArrow T.curried T.curried) fun x => k #[x] (conjMap.beta #[x])
    else withLocalDecl (yield n) bi d fun x => k #[x] x
  -- Binder types are left alone, except an implication's premise, which is a statement.
  let rec go (e : Expr) : MetaM Expr := do
    match e with
    | .forallE n d b bi =>
      if !b.hasLooseBVar 0 && !(← isDefEq d T.A) then return .forallE n (← go d) (← go b) bi
      binder n bi d fun xs v => do mkForallFVars xs (← go (b.instantiate1 v))
    | .lam n d b bi =>
      withLocalDecl n bi d fun x => do mkLambdaFVars #[x] (← go (b.instantiate1 x))
    | .mdata m e => return .mdata m (← go e)
    | .app .. =>
      -- The BI's quantifier `∀ x, Φ x` is `BIBase.forall fun x => Φ x`.
      if e.isAppOfArity ``BIBase.forall 4 then
        if let .lam n d b bi := e.appArg! then
          return ← binder n bi d fun xs v => do
            xs.foldrM (init := ← go (b.instantiate1 v)) fun x body => do
              mkAppM ``BIBase.forall #[← mkLambdaFVars #[x] body]
      e.withApp fun f args => return mkAppN (← go f) (← args.mapM go)
    | e => return e
  go type

/-- The curried statement from `curryBinders`, and its equation with `type` (`none` if defeq),
proved by `simp` with the rewrites of `T`. -/
meta def curryStatement (T : Tupling) (type : Expr) : MetaM (Expr × Option Expr) := do
  let type ← Core.betaReduce type
  let curried ← betaEta (← T.curryBinders type)
  if T.arity == 1 then return (curried, none)
  let ctx ← Simp.mkContext (simpTheorems := #[T.thms]) (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simp type ctx
  unless ← isDefEq (← betaEta r.expr) curried do
    throwError "curryStatement: {indentExpr curried}\nis not{indentExpr r.expr}"
  return (curried, ← r.proof?.mapM fun eq => do mkExpectedTypeHint eq (← mkEq type curried))

/-- The statement of `general`, with `fixpoint` replaced by `name` along
`eq : fixpoint = uncurry name`, curried, and its proof. -/
meta def restate (T : Tupling) (general fixpoint eq name : Expr) : MetaM (Expr × Expr) := do
  let body ← kabstract (← instantiateMVars (← inferType general)) fixpoint
  let proof ← mkEqNDRec (.lam `f (← mkArrow T.A T.prop) body .default) general eq
  let (type, eq?) ← T.curryStatement (body.instantiate1 (T.uncurry.beta #[name]))
  return (type, ← castAlong eq? proof (forward := true))

/-- `fun n p q => p.1 ≡{n}≡ q.1 ∧ …`, when there are parameters, none dependent, each an OFE. -/
meta def distRel? (T : Tupling) : MetaM (Option Expr) := do
  if T.arity == 0 then return none
  let ok ← forallTelescope T.curried fun xs _ => xs.allM fun x => do
    let ty ← inferType x
    if ty.hasAnyFVar (xs.contains <| .fvar ·) then return false
    return (← observing? do synthInstance (← mkAppM ``OFE #[ty])).isSome
  unless ok do return none
  withLocalDeclD `n (mkConst ``Nat) fun n => withLocalDeclD `p T.A fun p =>
  withLocalDeclD `q T.A fun q => do
    let dists ← (← mkProjs T.curried p).zip (← mkProjs T.curried q) |>.mapM fun (a, b) =>
      mkAppM ``OFE.Dist #[n, a, b]
    return some (← mkLambdaFVars #[n, p, q] (← dists.pop.foldrM (mkAppM ``And #[·, ·]) dists.back!))

end Tupling

end Iris.Fixpoint

end
