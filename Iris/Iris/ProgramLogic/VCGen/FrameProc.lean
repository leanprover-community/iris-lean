/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

public import Iris.ProgramLogic.VCGen.SepTree
public import Iris.ProgramLogic.VCGen.WP
public meta import Lean
public import Lean.Elab.Tactic.VCGen.FrameProcAttr

@[expose] public section

/-!
# Frame inference for iris programs

The `@[frameproc]` for `IrisProg` cancels the resource atoms of a specification's precondition
against the atoms of the goal's precondition. Take the goal precondition
`P = l₁ ↦ a ∗ l₂ ↦ b ∗ R` and a specification precondition `specP`. There are two kinds of
specification:

* **Continuation form**, as `load_spec`: `specP = l ↦ ?v ∗ (l ↦ ?v -∗ Q ?v)`. The wand mentions
  the postcondition. Matching `l ↦ ?v` against `l₁ ↦ a` assigns `?l := l₁` and `?v := a`. The
  frame is `emp` and the footprint is all of `P`. The precondition VC
  `l₁ ↦ a ∗ l₂ ↦ b ∗ R ⊑ l₁ ↦ a ∗ (l₁ ↦ a -∗ Q a)` reduces to the residual
  `l₂ ↦ b ∗ R ⊑ l₁ ↦ a -∗ Q a`, and `vcgen` continues on it.
* **Frame form**, as a function specification `{l ↦ ?v} f #l {r. Φ r}`: `specP` mentions only
  resources. Matching assigns the logical variables as above. The footprint is the matched atoms
  `l₁ ↦ a`, the frame is the rest `l₂ ↦ b ∗ R`, and the precondition VC closes by permutation.

The atom matching is first fit up to `isDefEqS`. Entailments are proved by `SepTree.cancel_le` and
`SepTree.frame_le`, whose permutation side conditions are closed by `Eq.refl true`.

A specification whose precondition is a weakest precondition, a postcondition application or an
infimum declines framing (`decline`), since it holds no resource.
-/

open Lean Meta Elab Tactic Sym Sym.Internal Lean.Elab.Tactic.VCGen

namespace Iris.VCGen.FrameProc

/-- The atoms of a separating conjunction, dropping `emp`. -/
meta partial def sepAtoms (e : Expr) : Array Expr :=
  let e := e.consumeMData.headBeta
  if e.isAppOfArity ``Iris.BI.BIBase.sep 4 then sepAtoms e.appFn!.appArg! ++ sepAtoms e.appArg!
  else if e.isAppOfArity ``Iris.BI.BIBase.emp 2 then #[]
  else #[e]

/-- Whether a precondition holds resources to frame. A weakest precondition, a postcondition
application, an infimum and `⊤` hold none. -/
meta def holdsResources (pre : Expr) : Bool :=
  match pre.consumeMData.getAppFn with
  | .const n _ =>
    !(n == ``Std.WP.WP.wp || n == ``Lean.Order.iInf || n == ``Lean.Order.top ||
      n == ``cond || n == ``ite)
  | _ => false

/-- The precondition of the specification named `n`, with loose bound variables. -/
meta def specPre? (n : Name) : MetaM (Option Expr) := do
  let some ci := (← getEnv).find? n | return none
  let b := ci.type.getForallBody
  if b.isAppOfArity ``Std.WP.Triple 11 then return some b.getAppArgs[8]! else return none

/-- The term-building context: the carrier `PROP`, its universe and `BI` instance, and the `sep`
and `emp` heads as they occur in the goal. -/
structure Ctx where
  u : Level
  prop : Expr
  instBI : Expr
  sep : Expr
  emp : Expr

/-- Find the `BI` instance inside the lattice instance of the goal's order. -/
meta def mkCtx (le : Expr) (sep : Expr) : SymM Ctx := do
  let some inst := le.find? (·.isAppOf ``Iris.VCGen.instCompleteLattice_iris)
    | throwError "iris frameproc: no BI lattice instance in{indentExpr le}"
  let .const _ [u] := inst.getAppFn | throwError "iris frameproc: unexpected instance{indentExpr inst}"
  let args := sep.getAppArgs
  return { u, prop := inst.appFn!.appArg!, instBI := inst.appArg!, sep,
           emp := ← mkAppNS (← mkConstS ``Iris.BI.BIBase.emp sep.getAppFn.constLevels!)
             #[args[0]!, args[1]!] }

section Build
variable (c : Ctx)

meta def mkSepChain (atoms : Array Expr) : SymM Expr := do
  if atoms.isEmpty then return c.emp
  else atoms.pop.foldrM (fun a acc => mkAppNS c.sep #[a, acc]) atoms.back!

meta def mkTreeOfIdx (idxs : Array Nat) : SymM Expr := do
  if idxs.isEmpty then mkConstS ``SepTree.emp
  else
    let atom (i : Nat) := do mkAppNS (← mkConstS ``SepTree.atom) #[← mkLitS (.natVal i)]
    idxs.pop.foldrM (fun i acc => do mkAppNS (← mkConstS ``SepTree.sep) #[← atom i, acc])
      (← atom idxs.back!)

/-- The tree mirroring the separating conjunction `e`; `idx` numbers its atoms left to right. -/
meta partial def mirror (e : Expr) (idx : Array Nat) : StateT Nat SymM Expr := do
  let e := e.consumeMData.headBeta
  if e.isAppOfArity ``Iris.BI.BIBase.sep 4 then
    let a ← mirror e.appFn!.appArg! idx
    let b ← mirror e.appArg! idx
    mkAppNS (← mkConstS ``SepTree.sep) #[a, b]
  else if e.isAppOfArity ``Iris.BI.BIBase.emp 2 then mkConstS ``SepTree.emp
  else
    let i ← get
    set (i + 1)
    mkAppNS (← mkConstS ``SepTree.atom) #[← mkLitS (.natVal idx[i]!)]

meta def mkList (xs : Array Expr) : SymM Expr := do
  let nil ← mkAppNS (← mkConstS ``List.nil [c.u]) #[c.prop]
  let cons ← mkAppNS (← mkConstS ``List.cons [c.u]) #[c.prop]
  xs.foldrM (fun x acc => mkAppNS cons #[x, acc]) nil

meta def reflTrue : SymM Expr := do
  mkAppNS (← mkConstS ``Eq.refl [1]) #[← mkConstS ``Bool, ← mkConstS ``Bool.true]

end Build

/-- First-fit matching of `wanted` atoms against `have` atoms, up to `isDefEqS`. Returns the
index into `have` for each wanted atom, or `none` if some atom has no partner. -/
meta def matchAtoms (wanted have_ : Array Expr) : SymM (Option (Array Nat)) := do
  let mut used : Array Bool := Array.replicate have_.size false
  let mut res := #[]
  for w in wanted do
    let mut found := none
    for j in [0:have_.size] do
      if used[j]! then continue
      let mctx ← getMCtx
      if ← isDefEqS w have_[j]! then
        found := some j
        break
      else
        setMCtx mctx
    let some j := found | return none
    used := used.set! j true
    res := res.push j
  return some res

/-- Frame `emp` and take the whole precondition as the footprint; the solver forwards the
precondition VC. -/
meta def empSplit (c : Ctx) (i : FrameInferenceInfo) (goal : FrameGoal) : Grind.GrindM FrameSplit := do
  goal.frame.assign c.emp
  goal.footprint.assign i.pre
  let prf ← mkAppNS (← mkConstS ``SepTree.emp_frame_le [c.u])
    #[c.prop, c.instBI, i.pre, goal.framedApp.expr, goal.specProof]
  return { splitVCProof := prf, subgoals := [] }

meta def irisFrameInferenceProc : FrameInferenceProc := fun i => do
  if let some n := i.spec? then
    if let some pre ← specPre? n then
      unless holdsResources pre do return .decline
  return .commit i.unframedApp.excessArgs fun goal => do
    let pre ← instantiateMVarsS i.pre
    let c ← mkCtx i.le (← i.mkOpApp)
    let frameMVar := mkMVar goal.frame
    let preAtoms := sepAtoms pre
    -- Matching assigns the specification's logical variables, and an assigned variable can unfold
    -- to further atoms (an invariant `?inv u K`). Split and match again until the atoms are stable.
    let mut result := none
    for _ in [0:8] do
      let specAtoms := sepAtoms (← instantiateMVarsS goal.specPre)
      let (kAtoms, rAtoms) := specAtoms.partition fun a => (a.find? (· == frameMVar)).isSome
      let some matched ← matchAtoms rAtoms preAtoms | break
      result := some (specAtoms, kAtoms, matched)
      if (sepAtoms (← instantiateMVarsS goal.specPre)).size == specAtoms.size then break
    let some (specAtoms, kAtoms, matched) := result | empSplit c i goal
    let restIdx := (Array.range preAtoms.size).filter (!matched.contains ·)
    let ctxBase := preAtoms
    if kAtoms.isEmpty then
      -- Frame form: the matched atoms are the footprint, the rest is the frame.
      let frame ← mkSepChain c (restIdx.map (preAtoms[·]!))
      let footprint ← mkSepChain c (matched.map (preAtoms[·]!))
      goal.frame.assign frame
      goal.footprint.assign footprint
      let ctx ← mkList c ctxBase
      let tA ← mkTreeOfIdx matched
      let tR ← mkTreeOfIdx restIdx
      let (tP, _) ← (mirror pre (Array.range preAtoms.size)).run 0
      let specPre ← instantiateMVarsS goal.specPre
      let (tX, _) ← (mirror specPre matched).run 0
      let emp ← mkConstS ``SepTree.emp
      let refl ← reflTrue
      let empLe ← mkAppNS (← mkConstS ``Lean.Order.PartialOrder.rel_refl [mkLevelSucc c.u])
        #[c.prop, ← mkAppNS (← mkConstS ``Lean.Order.CompleteLattice.toPartialOrder [mkLevelSucc c.u])
            #[c.prop, ← mkAppNS (← mkConstS ``Iris.VCGen.instCompleteLattice_iris [c.u])
              #[c.prop, c.instBI]], c.emp]
      let preVCPrf ← mkAppNS (← mkConstS ``SepTree.cancel_le [c.u])
        #[c.prop, c.instBI, ctx, tA, tA, emp, tX, emp, refl, refl, empLe]
      goal.preVC.assign preVCPrf
      let splitPrf ← mkAppNS (← mkConstS ``SepTree.frame_le [c.u])
        #[c.prop, c.instBI, ctx, tP, tR, tA, goal.framedApp.expr, refl, goal.specProof]
      return { splitVCProof := splitPrf, subgoals := [] }
    else
      -- Continuation form: frame `emp`, cancel the matched atoms, continue on the residual.
      goal.frame.assign c.emp
      goal.footprint.assign pre
      let kAtoms ← kAtoms.mapM fun a => instantiateMVarsS a
      let ctx ← mkList c (ctxBase ++ kAtoms)
      let kIdx := (Array.range kAtoms.size).map (· + preAtoms.size)
      let tA ← mkTreeOfIdx matched
      let tR ← mkTreeOfIdx restIdx
      let tK ← mkTreeOfIdx kIdx
      let (tP, _) ← (mirror pre (Array.range preAtoms.size)).run 0
      let specPre ← instantiateMVarsS goal.specPre
      -- Number the spec atoms: resource atoms by their partner, continuation atoms after `pre`.
      let mut specIdx := #[]
      let mut ri := 0
      let mut ki := 0
      for a in specAtoms do
        if kAtoms.size > 0 && ((a.find? (· == frameMVar)).isSome) then
          specIdx := specIdx.push kIdx[ki]!; ki := ki + 1
        else
          specIdx := specIdx.push matched[ri]!; ri := ri + 1
      let (tX, _) ← (mirror specPre specIdx).run 0
      let rest ← mkSepChain c (restIdx.map (preAtoms[·]!))
      let kont ← mkSepChain c kAtoms
      let residual ← mkFreshExprSyntheticOpaqueMVar (← mkAppNS i.le #[rest, kont])
      let refl ← reflTrue
      let preVCPrf ← mkAppNS (← mkConstS ``SepTree.cancel_le [c.u])
        #[c.prop, c.instBI, ctx, tP, tA, tR, tX, tK, refl, refl, residual]
      goal.preVC.assign preVCPrf
      let prf ← mkAppNS (← mkConstS ``SepTree.emp_frame_le [c.u])
        #[c.prop, c.instBI, pre, goal.framedApp.expr, goal.specProof]
      return { splitVCProof := prf, subgoals := [residual.mvarId!] }

/-- The separating conjunction `@BIBase.sep PROP (BI.toBIBase inst)`, with the `BI` instance `inst`
taken from the lattice instance of the `wp` application. -/
meta def sepOfWPApp (info : WPApp) : MetaM Expr := do
  let some inst := info.args[4]!.find? (·.isAppOf ``Iris.VCGen.instCompleteLattice_iris)
    | throwError "iris frameproc: no BI lattice instance in{indentExpr info.args[4]!}"
  let .const _ [u] := inst.getAppFn | throwError "iris frameproc: unexpected instance{indentExpr inst}"
  let prop := inst.appFn!.appArg!
  let instBIBase := mkApp2 (mkConst ``Iris.BI.toBIBase [u]) prop inst.appArg!
  return mkApp2 (mkConst ``Iris.BI.BIBase.sep [u]) prop instBIBase

@[frameproc] meta def irisFP : FrameProc where
  prog := ``Iris.VCGen.IrisProg
  mkOpAppM := sepOfWPApp
  mkResourceTy info := pure info.Pred
  opHead := ``Iris.BI.BIBase.sep
  proc := irisFrameInferenceProc
  framesThm? := ``Iris.VCGen.frames_sep

end Iris.VCGen.FrameProc

/-! ## `grind` support for the verification conditions -/

namespace Iris.VCGen

open Iris Iris.BI Lean.Order

attribute [grind .] frames_sep
attribute [grind ←] le_ofProp PartialOrder.rel_of_eq

@[grind ←] theorem sep_le_of_le_right {PROP : Type _} [BI PROP] [BIAffine PROP] {P R X : PROP}
    (h : R ⊑ X) : BIBase.sep P R ⊑ X :=
  BIBase.Entails.trans sep_elim_right h

@[grind =, vcgen_simp] theorem emp_sep_eq {PROP : Type _} [BI PROP] (P : PROP) :
    BIBase.sep BIBase.emp P = P := BI.emp_sep.to_eq
@[grind =, vcgen_simp] theorem sep_emp_eq {PROP : Type _} [BI PROP] (P : PROP) :
    BIBase.sep P BIBase.emp = P := sep_emp.to_eq

end Iris.VCGen
