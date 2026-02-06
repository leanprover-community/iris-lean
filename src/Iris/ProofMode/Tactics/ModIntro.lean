/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.ProofMode.Tactics.Basic
import Iris.ProofMode.Modalities

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

/-- Reified version of ModalityAction -/
private inductive ModalityActionQ (PROP1 : Q(Type u)) (PROP2 : Q(Type u)) : Type where
| isEmpty
| forall (C : Q($PROP1 → Prop))
| transform (C : Q($PROP2 → $PROP1 → Prop))
| clear
| id

private def ModalityActionQ.parse {prop1 prop2 : Q(Type u)} (act : Q(ModalityAction $prop1 $prop2)) :
  ProofModeM (ModalityActionQ prop1 prop2) := do
  let act ← whnf q($act)
  match_expr act with
  | ModalityAction.isEmpty _ _ => return .isEmpty
  | ModalityAction.forall _ C => return .forall C
  | ModalityAction.transform _ _ C => return .transform C
  | ModalityAction.clear _ _ => return .clear
  | ModalityAction.id _ => return .id
  | _ => throwError "imodintro: unknown modality action {act}"

private theorem modaction_forall [BI PROP] {p P} (M : Modality PROP PROP) {C} (h : M.action p = .forall C) (hC : C P)
  : □?p P ⊢ M.M iprop(□?p P) := by
    have hs := M.spec p
    rw [h] at hs
    apply (hs _ hC)

private theorem modaction_transform [BI PROP1] [BI PROP2] {p P Q} (M : Modality PROP1 PROP2) {C} (h : M.action p = .transform C) (hC : C P Q)
  : □?p P ⊢ M.M iprop(□?p Q) := by
    have hs := M.spec p
    rw [h] at hs
    apply (hs _ _ hC)

private theorem modaction_clear [BI PROP1] [BI PROP2] {p P} (M : Modality PROP1 PROP2) (h : M.action p = .clear)
  : □?p P ⊢ M.M emp :=
  match p, h  with
  | true, _ => affine.trans M.emp
  | false, h => by
    have hs := M.spec false
    simp [h] at hs
    apply Entails.trans (sep_emp.2.trans (sep_mono true_intro M.emp)) absorbing

private theorem modaction_id [BI PROP] {p P} (M : Modality PROP PROP) (h : M.action p = .id)
  : □?p P ⊢ M.M iprop(□?p P) := by
    have hs := M.spec p
    rw [h] at hs
    apply hs


private theorem modaction_sep_emp_l [BI PROP1] [bi2: BI PROP2] {elhs erhs erhs'} {M : Modality PROP1 PROP2}
  (h1 : elhs ⊢ M.M emp) (h2 : erhs ⊢ M.M erhs') : elhs ∗ erhs ⊢ M.M iprop(erhs') := (sep_mono h1 h2).trans $ M.sep.trans (M.mono emp_sep.1)

private theorem modaction_sep_emp_r [BI PROP1] [bi2: BI PROP2] {elhs elhs' erhs} {M : Modality PROP1 PROP2}
  (h1 : elhs ⊢ M.M elhs') (h2 : erhs ⊢ M.M emp) : elhs ∗ erhs ⊢ M.M iprop(elhs') := (sep_mono h1 h2).trans $ M.sep.trans (M.mono sep_emp.1)

private theorem modaction_sep [BI PROP1] [bi2: BI PROP2] {elhs erhs elhs' erhs'} {M : Modality PROP1 PROP2}
  (h1 : elhs ⊢ M.M elhs') (h2 : erhs ⊢ M.M erhs') : elhs ∗ erhs ⊢ M.M iprop(elhs' ∗ erhs') := (sep_mono h1 h2).trans M.sep


/--
Applies modality actions to transform proof mode context.

# Parameters
- `hyps` - Context in `prop2`
- `M` - Modality being introduced (`prop1 → prop2`)
- `act` - Modality action depending on persistence flag

# Returns
A tuple containing:
- Transformed context term
- Transformed context `hyps'` in `prop1`
- Proof of `hyps ⊢ M hyps'`
-/
private def iModAction {prop1 : Q(Type u)} {bi1 : Q(BI $prop1)} {bi2} {e}
  (hyps : @Hyps u prop2 bi2 e) (M : Q(Modality $prop1 $prop2)) (act : Bool → ModalityActionQ prop1 prop2) :
  ProofModeM ((e' : _) × Hyps bi1 e' × Q($e ⊢ $(M).M $e')) :=
  match hyps with
  | .emp _ => return ⟨_, .mkEmp bi1, q($(M).emp)⟩
  | .hyp _ name uniq p ty _ =>
    let p' := isTrue p
    match act p' with
    | .isEmpty => throwError "imodintro: {if p' then "intuitionistic" else "spatial"} context is not empty"
    | .forall C => do
      have : $prop1 =Q $prop2 := ⟨⟩
      have : $bi1 =Q $bi2 := ⟨⟩
      let .some hC ← trySynthInstanceQ q($C $ty)
        | throwError "imodintro: hypothesis {name} : {ty} does not satisfy {C}"
      -- bridge through defeq since `M.action` cannot unify directly with the pattern (same in other cases)
      have heq : Q(@ModalityAction.forall $prop1 $C = .forall $C) := q(Eq.refl (ModalityAction.forall $C))
      have heq : Q($(M).action $p = .forall $C) := heq
      return ⟨_, .mkHyp bi1 name uniq p ty, q(modaction_forall $M $heq $hC)⟩
    | .transform C => do
      let ty' ← mkFreshExprMVarQ q($prop1)
      let .some hC ← trySynthInstanceQ q($C $ty $ty')
        | throwError "imodintro: cannot transform hypothesis {name} : {ty} with {C}"
      have heq : Q(@ModalityAction.transform $prop1 $prop2 $C = .transform $C) := q(Eq.refl (ModalityAction.transform $C))
      have heq : Q($(M).action $p = .transform $C) := heq
      return ⟨_, .mkHyp bi1 name uniq p ty', q(modaction_transform $M $heq $hC)⟩
    | .clear =>
       have heq : Q(@ModalityAction.clear $prop1 $prop2 = .clear) := q(Eq.refl (ModalityAction.clear))
       have heq : Q($(M).action $p = @ModalityAction.clear $prop1 $prop2) := heq
       return ⟨_, .mkEmp bi1, q(modaction_clear $M $heq)⟩
    | .id =>
      have : $prop1 =Q $prop2 := ⟨⟩
      have : $bi1 =Q $bi2 := ⟨⟩
      have heq : Q(@ModalityAction.id $prop1 = .id) := q(Eq.refl (ModalityAction.id))
      have heq : Q($(M).action $p = .id) := heq
      return ⟨_, .mkHyp bi1 name uniq p ty, q(modaction_id $M $heq)⟩
  | .sep _ _ _ _ lhs rhs => do
    let ⟨_, lhs', pflhs⟩ ← iModAction lhs M act
    let ⟨_, rhs', pfrhs⟩ ← iModAction rhs M act
    -- TODO: make pruning emp part of mkSep?
    if let .emp _ := lhs' then
      return ⟨_, rhs', q(modaction_sep_emp_l $pflhs $pfrhs)⟩
    if let .emp _ := rhs' then
      return ⟨_, lhs', q(modaction_sep_emp_r $pflhs $pfrhs)⟩
    return ⟨_, .mkSep lhs' rhs', q(modaction_sep $pflhs $pfrhs)⟩

private theorem modintro [BI PROP1] [BI PROP2] {e e'} {Φ M sel} {P : PROP2} {Q : PROP1} [FromModal Φ M sel P Q]
  (h1 : e ⊢ M.M e') (h2 : e' ⊢ Q) (hΦ : Φ) : e ⊢ P :=
    (h1.trans (M.mono h2)).trans (from_modal sel hΦ)

/-- Introduce a modality by applying modality actions to transform hypotheses.

# Parameters
- `hyps` : Context
- `goal` - Goal
- `sel` - Selector term to match against specific modality patterns
- `k` - Continuation that receives the transformed context `P` and goal `Q`,
  and produces a proof of `P ⊢ Q`

# Returns
Proof term of `hyps ⊢ goal`
-/
def iModIntroCore {e} (hyps : @Hyps u prop bi e) (goal : Q($prop)) (sel : TSyntax `term)
  (k : ∀ {prop' bi' P}, @Hyps u prop' bi' P → ∀ Q : Q($prop'), ProofModeM Q($P ⊢ $Q))
   : ProofModeM (Q($e ⊢ $goal)) := do
    let prop' : Q(Type u) ← mkFreshExprMVarQ q(Type u)
    let bi' ← mkFreshExprMVarQ q(BI $prop')
    let Φ ← mkFreshExprMVarQ q(Prop)
    let M ← mkFreshExprMVarQ q(Modality $prop' $prop)
    let sel ← elabTermEnsuringTypeQ (← `(term | iprop($sel))) prop'
    let Q ← mkFreshExprMVarQ q($prop')
    -- `M Q ⊢ goal`
    let .some _ ← ProofModeM.trySynthInstanceQ q(@FromModal $prop' $prop $bi' $bi $Φ $M $sel $goal $Q)
      | throwError "imodintro: {goal} is not a modality{if sel.isMVar then m!"" else m!" matching {sel}"}"
    -- show the side condition
    let hΦ ← mkFreshExprMVarQ q($Φ)
    iSolveSideconditionAt hΦ.mvarId!
    -- pre-compute the actions
    let iact ← ModalityActionQ.parse q($(M).action true)
    let sact ← ModalityActionQ.parse q($(M).action false)
    -- perform modality actions, get transformed context `hyps'` and `pf : hyps ⊢ M hyps'`
    let ⟨_, hyps', pf⟩ ← iModAction hyps M (λ p => if p then iact else sact)
    -- get proof `hyps' ⊢ Q`
    let pf' ← k hyps' Q
    return q(modintro (sel:=$sel) $pf $pf' $hΦ)

elab "imodintro" colGt sel:term : tactic => do
  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
  let pf ← iModIntroCore hyps goal sel addBIGoal

  mvar.assign pf

macro "imodintro" : tactic => `(tactic | imodintro _)
macro "inext" : tactic => `(tactic | imodintro (▷^[_] _))
