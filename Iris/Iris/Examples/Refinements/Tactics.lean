/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.Examples.Refinements.Refinement

/-! # Proof mode tactics for the source of the refinement logic

This file ports the source tactics of `theories/examples/refinements/refinement.v` of Transfinite
Iris (`src_pure`, `src_bind`, `src_load`, `src_store`). They act on a hypothesis `H : j ⤇ e`
(Rocq: `... in "H"`):

* `src_pure H` takes a pure step of the source thread in the goal `srcUpd E P` (which becomes
  `weakSrcUpd E P`), `weakSrcUpd E P`, or a target refinement weakest precondition `rwp e Φ` (for
  a non-value `e`, taking a step of the target at the same time).
* `src_pures H` takes as many pure source steps as possible.
* `src_bind focus in H` presents the source expression as `fill K focus`.
* `src_load H` and `src_store H` execute a load or store of the source, using a source points-to
  in the context.
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite.Refinement

open Iris Iris.Std Iris.BI Iris.HeapLang Iris.HeapLang.Transfinite ProgramLogic Language
open Language.Notation

set_option linter.unusedSectionVars false

variable {GF : BundledGFunctors} [G : RHeapG GF] [N : NatSourceG GF]

/-! ## Source updates in continuation form -/

/-- `rwp_take_step` with the continuation inside the source update. -/
theorem rwp_take_step_src {s : Stuckness} {E : CoPset} {e : Exp} {Φ : Val → IProp GF}
    (he : ToVal.toVal e = none) :
    srcUpd E (rswp (src := refSrc (GF := GF)) (ι := heapRefIrisGS) 1 s E e Φ) ⊢
      rwp (src := refSrc (GF := GF)) (ι := heapRefIrisGS) s E e Φ := by
  iintro H
  iapply rwp_take_step (src := refSrc (GF := GF)) he $$ [] H
  iintro H
  iexact H

/-- `rwp_weaken` with the continuation inside the source update. -/
theorem rwp_weaken_src {s : Stuckness} {E : CoPset} {e : Exp} {Φ : Val → IProp GF}
    (he : ToVal.toVal e = none) :
    srcUpd E (rwp (src := refSrc (GF := GF)) (ι := heapRefIrisGS) s E e Φ) ⊢
      rwp (src := refSrc (GF := GF)) (ι := heapRefIrisGS) s E e Φ := by
  iintro H
  iapply rwp_weaken (src := refSrc (GF := GF)) he $$ [] H
  iintro H
  iexact H

/-- `rwp_weaken'` with the continuation inside the weak source update. -/
theorem rwp_weaken_src' {s : Stuckness} {E : CoPset} {e : Exp} {Φ : Val → IProp GF}
    (he : ToVal.toVal e = none) :
    weakSrcUpd E (rwp (src := refSrc (GF := GF)) (ι := heapRefIrisGS) s E e Φ) ⊢
      rwp (src := refSrc (GF := GF)) (ι := heapRefIrisGS) s E e Φ := by
  iintro H
  iapply rwp_weaken' (src := refSrc (GF := GF)) he $$ [] H
  iintro H
  iexact H

theorem weakSrcUpd_return {E : CoPset} {P : IProp GF} : P ⊢ weakSrcUpd E P :=
  weakSrcUpdate_return (src := refSrc (GF := GF))

theorem weakSrcUpd_bind {E : CoPset} {P Q : IProp GF} :
    weakSrcUpd E P ∗ (P -∗ weakSrcUpd E Q) ⊢ weakSrcUpd E Q :=
  weakSrcUpdate_bind (src := refSrc (GF := GF))

/-! ## Tactic lemmas -/

theorem tac_src_pure_cred {Δ P : IProp GF} {E : CoPset} {j : Nat} (k : Nat) (K : List ECtxItem)
    (e₁ e₂ : Exp) {φ : Prop} (hexec : PureExec φ 1 e₁ e₂) (hφ : φ)
    (h : Δ ⊢ tpoolPointsTo j (fill K e₂) -∗ stutter k -∗ weakSrcUpd E P) :
    Δ ⊢ tpoolPointsTo j (fill K e₁) -∗ srcUpd E P := by
  have hexec' := EctxLanguage.pureExec_fill (K := K) φ 1 hexec
  have hp : fill K e₁ -ᵖ-> fill K e₂ := by
    obtain ⟨b, hb, hrest⟩ := Relation.Iterate.succ_head_inv (hexec'.pureExec hφ)
    cases hrest
    exact hb
  refine h.trans (wand_intro ?_)
  iintro ⟨H, Hj⟩
  iapply weakSrcUpdate_bind_r (src := refSrc (GF := GF))
  isplitl [Hj]
  · iapply step_pure_cred k E j _ _ hp $$ Hj
  · iintro ⟨Hj, Hc⟩
    iapply H $$ Hj Hc

theorem tac_src_change {Δ G : IProp GF} {j : Nat} {e e' : Exp} (heq : e = e')
    (h : Δ ⊢ tpoolPointsTo j e' -∗ G) : Δ ⊢ tpoolPointsTo j e -∗ G := heq ▸ h

theorem tac_src_pure_upd {Δ P : IProp GF} {E : CoPset} {j : Nat} (K : List ECtxItem)
    (e₁ e₂ : Exp) {φ : Prop} (hexec : PureExec φ 1 e₁ e₂) (hφ : φ)
    (h : Δ ⊢ tpoolPointsTo j (fill K e₂) -∗ weakSrcUpd E P) :
    Δ ⊢ tpoolPointsTo j (fill K e₁) -∗ srcUpd E P := by
  have hexec' := EctxLanguage.pureExec_fill (K := K) φ 1 hexec
  refine h.trans (wand_intro ?_)
  iintro ⟨H, Hj⟩
  iapply weakSrcUpdate_bind_r (src := refSrc (GF := GF))
  isplitl [Hj]
  · iapply steps_pure_exec (n := 0) E j _ _ hφ $$ Hj
  · iexact H

theorem tac_src_pure_weak {Δ P : IProp GF} {E : CoPset} {j : Nat} (K : List ECtxItem)
    (e₁ e₂ : Exp) {φ : Prop} (hexec : PureExec φ 1 e₁ e₂) (hφ : φ)
    (h : Δ ⊢ tpoolPointsTo j (fill K e₂) -∗ weakSrcUpd E P) :
    Δ ⊢ tpoolPointsTo j (fill K e₁) -∗ weakSrcUpd E P :=
  (tac_src_pure_upd K e₁ e₂ hexec hφ h).trans
    (wand_mono .rfl (srcUpdate_weakSrcUpdate (src := refSrc (GF := GF))))

theorem tac_src_pure_rwp {Δ : IProp GF} {s : Stuckness} {E : CoPset} {e : Exp}
    {Φ : Val → IProp GF} {j : Nat} (K : List ECtxItem) (e₁ e₂ : Exp) {φ : Prop}
    (hexec : PureExec φ 1 e₁ e₂) (hφ : φ) (he : ToVal.toVal e = none)
    (h : Δ ⊢ tpoolPointsTo j (fill K e₂) -∗
      rwp (src := refSrc (GF := GF)) (ι := heapRefIrisGS) s E e Φ) :
    Δ ⊢ tpoolPointsTo j (fill K e₁) -∗
      rwp (src := refSrc (GF := GF)) (ι := heapRefIrisGS) s E e Φ := by
  have hexec' := EctxLanguage.pureExec_fill (K := K) φ 1 hexec
  refine h.trans (wand_intro ?_)
  iintro ⟨H, Hj⟩
  iapply rwp_weaken (src := refSrc (GF := GF)) he $$ H
  iapply steps_pure_exec (n := 0) E j _ _ hφ $$ Hj

theorem tac_src_load_upd {Δ P : IProp GF} {E : CoPset} {j : Nat} (K : List ECtxItem) (l : Loc)
    (q : DFrac) (v : Val)
    (h : Δ ⊢ heapSPointsTo l q v -∗ tpoolPointsTo j (fill K (v : Exp)) -∗ weakSrcUpd E P) :
    Δ ⊢ heapSPointsTo l q v -∗ tpoolPointsTo j (fill K hl(!v(#l))) -∗ srcUpd E P := by
  refine h.trans (wand_intro (wand_intro ?_))
  iintro ⟨⟨H, Hl⟩, Hj⟩
  iapply weakSrcUpdate_bind_r (src := refSrc (GF := GF))
  isplitl [Hj Hl]
  · iapply step_load E j K l q v
    iframe
  · iintro ⟨Hj, Hl⟩
    iapply H $$ Hl Hj

theorem tac_src_load_weak {Δ P : IProp GF} {E : CoPset} {j : Nat} (K : List ECtxItem) (l : Loc)
    (q : DFrac) (v : Val)
    (h : Δ ⊢ heapSPointsTo l q v -∗ tpoolPointsTo j (fill K (v : Exp)) -∗ weakSrcUpd E P) :
    Δ ⊢ heapSPointsTo l q v -∗ tpoolPointsTo j (fill K hl(!v(#l))) -∗ weakSrcUpd E P :=
  (tac_src_load_upd K l q v h).trans
    (wand_mono .rfl (wand_mono .rfl (srcUpdate_weakSrcUpdate (src := refSrc (GF := GF)))))

theorem tac_src_load_rwp {Δ : IProp GF} {s : Stuckness} {E : CoPset} {e : Exp}
    {Φ : Val → IProp GF} {j : Nat} (K : List ECtxItem) (l : Loc) (q : DFrac) (v : Val)
    (he : ToVal.toVal e = none)
    (h : Δ ⊢ heapSPointsTo l q v -∗ tpoolPointsTo j (fill K (v : Exp)) -∗
      rwp (src := refSrc (GF := GF)) (ι := heapRefIrisGS) s E e Φ) :
    Δ ⊢ heapSPointsTo l q v -∗ tpoolPointsTo j (fill K hl(!v(#l))) -∗
      rwp (src := refSrc (GF := GF)) (ι := heapRefIrisGS) s E e Φ := by
  refine h.trans (wand_intro (wand_intro ?_))
  iintro ⟨⟨H, Hl⟩, Hj⟩
  iapply rwp_weaken (src := refSrc (GF := GF)) (P := iprop(tpoolPointsTo j (fill K (v : Exp)) ∗
    heapSPointsTo l q v)) he $$ [H] [Hj Hl]
  · iintro ⟨Hj, Hl⟩
    iapply H $$ Hl Hj
  · iapply step_load E j K l q v
    iframe

theorem tac_src_store_upd {Δ P : IProp GF} {E : CoPset} {j : Nat} (K : List ECtxItem) (l : Loc)
    (v v' : Val)
    (h : Δ ⊢ heapSPointsTo l (.own 1) v -∗ tpoolPointsTo j (fill K hl(#())) -∗ weakSrcUpd E P) :
    Δ ⊢ heapSPointsTo l (.own 1) v' -∗ tpoolPointsTo j (fill K hl(v(#l) ← &v)) -∗ srcUpd E P := by
  refine h.trans (wand_intro (wand_intro ?_))
  iintro ⟨⟨H, Hl⟩, Hj⟩
  iapply weakSrcUpdate_bind_r (src := refSrc (GF := GF))
  isplitl [Hj Hl]
  · iapply step_store E j K l v v'
    iframe
  · iintro ⟨Hj, Hl⟩
    iapply H $$ Hl Hj

theorem tac_src_store_weak {Δ P : IProp GF} {E : CoPset} {j : Nat} (K : List ECtxItem) (l : Loc)
    (v v' : Val)
    (h : Δ ⊢ heapSPointsTo l (.own 1) v -∗ tpoolPointsTo j (fill K hl(#())) -∗ weakSrcUpd E P) :
    Δ ⊢ heapSPointsTo l (.own 1) v' -∗ tpoolPointsTo j (fill K hl(v(#l) ← &v)) -∗
      weakSrcUpd E P :=
  (tac_src_store_upd K l v v' h).trans
    (wand_mono .rfl (wand_mono .rfl (srcUpdate_weakSrcUpdate (src := refSrc (GF := GF)))))

theorem tac_src_store_rwp {Δ : IProp GF} {s : Stuckness} {E : CoPset} {e : Exp}
    {Φ : Val → IProp GF} {j : Nat} (K : List ECtxItem) (l : Loc) (v v' : Val)
    (he : ToVal.toVal e = none)
    (h : Δ ⊢ heapSPointsTo l (.own 1) v -∗ tpoolPointsTo j (fill K hl(#())) -∗
      rwp (src := refSrc (GF := GF)) (ι := heapRefIrisGS) s E e Φ) :
    Δ ⊢ heapSPointsTo l (.own 1) v' -∗ tpoolPointsTo j (fill K hl(v(#l) ← &v)) -∗
      rwp (src := refSrc (GF := GF)) (ι := heapRefIrisGS) s E e Φ := by
  refine h.trans (wand_intro (wand_intro ?_))
  iintro ⟨⟨H, Hl⟩, Hj⟩
  iapply rwp_weaken (src := refSrc (GF := GF)) (P := iprop(tpoolPointsTo j (fill K hl(#())) ∗
    heapSPointsTo l (.own 1) v)) he $$ [H] [Hj Hl]
  · iintro ⟨Hj, Hl⟩
    iapply H $$ Hl Hj
  · iapply step_store E j K l v v'
    iframe

end Iris.Transfinite.Refinement

namespace Iris.ProofMode

open Lean hiding Expr
open Meta Elab Tactic Qq
open Iris.HeapLang Iris.BI Iris.Transfinite Iris.Transfinite.Refinement

/-- Split `f a₁ ... aₙ` into the arguments, if the head is the constant `c`. -/
meta def appArgsOf? (c : Name) (e : Lean.Expr) : Option (Array Lean.Expr) :=
  if e.isAppOf c then some e.getAppArgs else none

/-- The kinds of goals handled by the source tactics. -/
inductive SrcGoalKind where
  | upd | weak | rwp

meta def srcGoalKind (G : Lean.Expr) : MetaM SrcGoalKind := do
  let G ← whnfR G
  if G.isAppOf ``srcUpdate then return .upd
  if G.isAppOf ``weakSrcUpdate then return .weak
  if G.isAppOf ``rwp then return .rwp
  throwError "the goal must be a source update or a refinement weakest precondition"

/-- Replace the head `srcUpdate` of `G` by `weakSrcUpdate`. -/
meta def srcUpdToWeak (G : Lean.Expr) : MetaM Lean.Expr := do
  let G ← whnfR G
  return mkAppN (mkConst ``weakSrcUpdate G.getAppFn.constLevels!) G.getAppArgs

/-- The target expression of a goal `rwp s E e Φ`. -/
meta def rwpTargetExp (G : Lean.Expr) : MetaM Lean.Expr := do
  let G ← whnfR G
  let args := G.getAppArgs
  return args[args.size - 2]!

/-- Assign `mvar` with `pf`, checking that the types agree up to definitional equality. -/
meta def assignChecked (mvar : MVarId) (pf : Lean.Expr) : MetaM Unit := do
  let t ← inferType pf
  unless ← isDefEq t (← mvar.getType) do
    throwError "source tactic: proof of{indentExpr t}\ndoes not match goal{indentExpr (← mvar.getType)}"
  mvar.assign pf

/-- An evaluation context of a source expression: the source expression may be of the form
`fill K₀ e₀` for an abstract context `K₀` (Rocq: `strip_ectx`). -/
structure SrcCtx (α : Type) where
  result : α
  K : Q(List ECtxItem)
  e' : Q(Exp)
  /-- Fill the context with an expression. -/
  mkFill : Q(Exp) → MetaM Q(Exp)

meta def findSrcCtx {α : Type} (e : Q(Exp))
    (pred : Q(List ECtxItem) → Q(Exp) → ProofModeM α) : ProofModeM (Option (SrcCtx α)) := do
  let e ← instantiateMVars e
  if e.isAppOf ``ProgramLogic.fill then
    let args := e.getAppArgs
    let mut K₀m : Q(List ECtxItem) := args[args.size - 2]!
    let mut e₀m : Q(Exp) := args[args.size - 1]!
    -- normalize `fill (L ++ K₁) e₀` to `fill K₁ (fill L e₀)` for a literal list `L`
    repeat
      let K₀' ← instantiateMVars K₀m
      let some (L, K₁) := (do
          guard (K₀'.isAppOfArity ``HAppend.hAppend 6)
          let a := K₀'.getAppArgs
          pure (a[4]!, a[5]!)) | break
      have L : Q(List ECtxItem) := L
      e₀m ← HeapLang.fill L e₀m
      K₀m := K₁
    have K₀ : Q(List ECtxItem) := K₀m
    have e₀ : Q(Exp) := e₀m
    let some r ← findECtx e₀ pred | return none
    let Kin := r.K
    let Kall : Q(List ECtxItem) := q($Kin ++ $K₀)
    return some ⟨r.result, Kall, r.e',
      fun x => do return q(ProgramLogic.fill $K₀ $(← HeapLang.fill Kin x))⟩
  else
    let some r ← findECtx e pred | return none
    return some ⟨r.result, r.K, r.e', fun x => HeapLang.fill r.K x⟩

/-- A pure step of `e₁` (a single step, possibly a beta step of a function hidden behind a
definition). -/
meta def findSrcPureStep (useRec : Bool) (e₁ : Q(Exp)) :
    ProofModeM ((φ : Q(Prop)) × (n : Q(Nat)) × (e₂ : Q(Exp)) × Lean.Expr) := do
  if !useRec then
    let r@⟨_, n, _, _⟩ ← findAnyPureExec e₁
    have n : Q(Nat) := n
    guard <| ← isDefEq n q(1)
    return r
  else
    let ~q(Exp.app (Exp.ofVal $f) (Exp.ofVal $a)) := e₁ | failure
    let f' : Q(Val) ← whnf f
    let ~q(Val.rec_ $fb $xb $body) := f' | failure
    have : $f' =Q $f := ⟨⟩
    let e₂ := q(Exp.subst $xb $a (Exp.subst $fb $f $body))
    return ⟨q(True), q(1), e₂, q(@instPureExecBeta $fb $xb $body $a)⟩

/-- A pure step of the source thread in the goal `j ⤇ e -∗ G`. -/
meta def srcPureCore (useRec : Bool) : TacticM Unit :=
  ProofModeM.runTactic `src_pure fun mvar {prop, hyps, goal, ..} => do
    let goal ← instantiateMVars goal
    let some gargs := appArgsOf? ``BIBase.wand goal
      | throwIPMError "the goal must be of the form `j ⤇ e -∗ G`"
    let A ← whnfR gargs[gargs.size - 2]!
    let G := gargs[gargs.size - 1]!
    let some aargs := appArgsOf? ``tpoolPointsTo A
      | throwIPMError "the goal must be of the form `j ⤇ e -∗ G`"
    have e : Q(Exp) := aargs[aargs.size - 1]!
    let kind ← srcGoalKind G
    let some {result := ⟨φ, n, e₂, hexec⟩, K, e' := e₁, mkFill} ←
      findSrcCtx (α := ((_ : Q(Prop)) × (_ : Q(Nat)) × (_ : Q(Exp)) × Lean.Expr)) e
        fun _ e₁ => findSrcPureStep useRec e₁
      | throwIPMError "cannot find a pure step in the source expression {e}"
    let hφ ← iSolveSidecondition φ
    let e₂f ← mkFill e₂
    let ⟨e₂s, pfeq⟩ ← iWpExprSimp e₂f
    let A' := mkApp A.appFn! e₂s
    let G' ← match kind with
      | .upd => srcUpdToWeak G
      | _ => pure G
    have newGoal : Q($prop) := mkApp2 goal.appFn!.appFn! A' G'
    let pf ← addBIGoal hyps newGoal
    let pfc ← mkAppM ``tac_src_change #[pfeq, pf]
    let pf' ← match kind with
      | .upd => mkAppM ``tac_src_pure_upd #[K, e₁, e₂, hexec, hφ, pfc]
      | .weak => mkAppM ``tac_src_pure_weak #[K, e₁, e₂, hexec, hφ, pfc]
      | .rwp => do
        let et ← rwpTargetExp G
        let he ← mkEqRefl (← mkAppM ``ProgramLogic.ToVal.toVal #[et])
        let he ← mkExpectedTypeHint he
          (← mkEq (← mkAppM ``ProgramLogic.ToVal.toVal #[et]) (← mkAppOptM ``Option.none #[(← inferType (← mkAppM ``ProgramLogic.ToVal.toVal #[et])).appArg!]))
        mkAppM ``tac_src_pure_rwp #[K, e₁, e₂, hexec, hφ, he, pfc]
    assignChecked mvar pf'

elab "src_pure_core" : tactic => srcPureCore false
elab "src_rec_core" : tactic => srcPureCore true

/-- Present the source expression of `j ⤇ e -∗ G` as `fill K focus`. -/
elab "src_bind_core" colGt ppSpace focus:hl_exp:10 : tactic =>
  ProofModeM.runTactic `src_bind fun mvar {prop, hyps, goal, ..} => do
    let goal ← instantiateMVars goal
    let some gargs := appArgsOf? ``BIBase.wand goal
      | throwIPMError "the goal must be of the form `j ⤇ e -∗ G`"
    let A ← whnfR gargs[gargs.size - 2]!
    let some aargs := appArgsOf? ``tpoolPointsTo A
      | throwIPMError "the goal must be of the form `j ⤇ e -∗ G`"
    have e : Q(Exp) := aargs[aargs.size - 1]!
    let focus ← elabTermEnsuringTypeQ (← `(hl($focus))) q(HeapLang.Exp)
    let some {K, e', ..} ← findSrcCtx e fun _ e => do
      guard <| ← isDefEq e focus
      | throwIPMError "cannot find {focus} in an evaluation context of {e}"
    have e' : Q(Exp) := e'
    let A' := mkApp A.appFn! q(ProgramLogic.fill $K $e')
    have newGoal : Q($prop) := mkApp2 goal.appFn!.appFn! A' gargs[gargs.size - 1]!
    let pf ← addBIGoal hyps newGoal
    assignChecked mvar pf

/-- A load (`load := true`) or store of the source in the goal `l ↦s v -∗ j ⤇ e -∗ G`. -/
meta def srcHeapCore (tacName : Name) (load : Bool) : TacticM Unit :=
  ProofModeM.runTactic tacName fun mvar {prop, hyps, goal, ..} => do
    let goal ← instantiateMVars goal
    let some gargs := appArgsOf? ``BIBase.wand goal
      | throwIPMError "the goal must be of the form `l ↦s v -∗ j ⤇ e -∗ G`"
    let L := gargs[gargs.size - 2]!
    let rest := gargs[gargs.size - 1]!
    let some rargs := appArgsOf? ``BIBase.wand rest
      | throwIPMError "the goal must be of the form `l ↦s v -∗ j ⤇ e -∗ G`"
    let A ← whnfR rargs[rargs.size - 2]!
    let G := rargs[rargs.size - 1]!
    let some largs := appArgsOf? ``heapSPointsTo L
      | throwIPMError "expected a source points-to"
    have l : Q(Loc) := largs[largs.size - 3]!
    have q : Q(DFrac) := largs[largs.size - 2]!
    have v : Q(Val) := largs[largs.size - 1]!
    let some aargs := appArgsOf? ``tpoolPointsTo A
      | throwIPMError "expected a source thread"
    have e : Q(Exp) := aargs[aargs.size - 1]!
    let kind ← srcGoalKind G
    let some {K, result := w, mkFill, ..} ← findSrcCtx (α := Lean.Expr) e fun _ e₁ => do
      if load then
        let ~q(Exp.load (Exp.ofVal (Val.lit (BaseLit.loc $l')))) := e₁ | failure
        guard <| ← isDefEq l l'
        return q(())
      else
        let ~q(Exp.store (Exp.ofVal (Val.lit (BaseLit.loc $l'))) (Exp.ofVal $w)) := e₁ | failure
        guard <| ← isDefEq l l'
        return w
      | throwIPMError "cannot find a {if load then "load" else "store"} of {l} in {e}"
    let (L', eNew) ← if load then
        pure (L, ← mkFill q(Exp.ofVal $v))
      else do
        have w : Q(Val) := w
        pure (mkApp L.appFn! w, ← mkFill q(Exp.ofVal (Val.lit .unit)))
    let A' := mkApp A.appFn! eNew
    let G' ← match kind with
      | .upd => srcUpdToWeak G
      | _ => pure G
    have newGoal : Q($prop) := mkApp2 goal.appFn!.appFn! L' (mkApp2 rest.appFn!.appFn! A' G')
    let pf ← addBIGoal hyps newGoal
    let pf' ← if load then
        match kind with
        | .upd => mkAppM ``tac_src_load_upd #[K, l, q, v, pf]
        | .weak => mkAppM ``tac_src_load_weak #[K, l, q, v, pf]
        | .rwp => do
          let et ← rwpTargetExp G
          let he ← mkEqRefl (← mkAppM ``ProgramLogic.ToVal.toVal #[et])
          mkAppM ``tac_src_load_rwp #[K, l, q, v, he, pf]
      else
        match kind with
        | .upd => mkAppM ``tac_src_store_upd #[K, l, w, v, pf]
        | .weak => mkAppM ``tac_src_store_weak #[K, l, w, v, pf]
        | .rwp => do
          let et ← rwpTargetExp G
          let he ← mkEqRefl (← mkAppM ``ProgramLogic.ToVal.toVal #[et])
          mkAppM ``tac_src_store_rwp #[K, l, w, v, he, pf]
    assignChecked mvar pf'

/-- A pure step of the source thread in the goal `j ⤇ e -∗ srcUpd E P`, allocating `k`
stuttering credits. -/
elab "src_pure_cred_core " kStx:term : tactic =>
  ProofModeM.runTactic `src_pure_cred fun mvar {prop, hyps, goal, ..} => do
    let goal ← instantiateMVars goal
    let some gargs := appArgsOf? ``BIBase.wand goal
      | throwIPMError "the goal must be of the form `j ⤇ e -∗ srcUpd E P`"
    let A ← whnfR gargs[gargs.size - 2]!
    let G := gargs[gargs.size - 1]!
    let some aargs := appArgsOf? ``tpoolPointsTo A
      | throwIPMError "the goal must be of the form `j ⤇ e -∗ srcUpd E P`"
    have e : Q(Exp) := aargs[aargs.size - 1]!
    let .upd ← srcGoalKind G
      | throwIPMError "the goal must be a source update"
    let k ← elabTermEnsuringTypeQ kStx q(Nat)
    let some {result := ⟨φ, n, e₂, hexec⟩, K, e' := e₁, mkFill} ←
      findSrcCtx (α := ((_ : Q(Prop)) × (_ : Q(Nat)) × (_ : Q(Exp)) × Lean.Expr)) e
        fun _ e₁ => findSrcPureStep false e₁
      | throwIPMError "cannot find a pure step in the source expression {e}"
    let hφ ← iSolveSidecondition φ
    let e₂f ← mkFill e₂
    let ⟨e₂s, pfeq⟩ ← iWpExprSimp e₂f
    let A' := mkApp A.appFn! e₂s
    let G' ← srcUpdToWeak G
    let stut ← Term.elabTermEnsuringType (← `(Iris.Transfinite.Refinement.stutter $kStx)) prop
    Term.synthesizeSyntheticMVarsNoPostponing
    let stut ← instantiateMVars stut
    let wand := goal.appFn!.appFn!
    have newGoal : Q($prop) := mkApp2 wand A' (mkApp2 wand stut G')
    let pf ← addBIGoal hyps newGoal
    let pfc ← mkAppM ``tac_src_change #[pfeq, pf]
    let pf' ← mkAppM ``tac_src_pure_cred #[k, K, e₁, e₂, hexec, hφ, pfc]
    assignChecked mvar pf'

elab "src_load_core" : tactic => srcHeapCore `src_load true
elab "src_store_core" : tactic => srcHeapCore `src_store false

/-- `src_pure H` takes a pure step of the source thread `H : j ⤇ e`. -/
macro "src_pure " h:ident : tactic =>
  `(tactic| (irevert $h:ident; src_pure_core; iintro $h:ident))

/-- `src_pure_cred k H as Hc` takes a pure step of the source thread `H : j ⤇ e` in a source
update, allocating `k` stuttering credits `Hc`. -/
macro "src_pure_cred " k:term:max ppSpace h:ident " as " hc:ident : tactic =>
  `(tactic| (irevert $h:ident; src_pure_cred_core $k; iintro $h:ident $hc:ident))

/-- `src_rec H` beta-reduces the innermost application of a function (possibly hidden behind a
definition) in the source thread `H : j ⤇ e`. -/
macro "src_rec " h:ident : tactic =>
  `(tactic| (irevert $h:ident; src_rec_core; iintro $h:ident))

/-- `src_pures H` takes all possible pure steps of the source thread `H : j ⤇ e`. -/
macro "src_pures " h:ident : tactic =>
  `(tactic| (src_pure $h; repeat src_pure $h))

/-- `src_bind focus in H` presents the source expression of `H : j ⤇ e` as `fill K focus`. -/
macro "src_bind " focus:hl_exp:10 " in " h:ident : tactic =>
  `(tactic| (irevert $h:ident; src_bind_core $focus; iintro $h:ident))

/-- `src_load H Hl` executes a load of the source thread `H`, using `Hl : l ↦s{q} v`. -/
macro "src_load " h:ident ppSpace hl:ident : tactic =>
  `(tactic| (irevert $h:ident; irevert $hl:ident; src_load_core; iintro $hl:ident $h:ident))

/-- `src_store H Hl` executes a store of the source thread `H`, using `Hl : l ↦s v`. -/
macro "src_store " h:ident ppSpace hl:ident : tactic =>
  `(tactic| (irevert $h:ident; irevert $hl:ident; src_store_core; iintro $hl:ident $h:ident))

end Iris.ProofMode
