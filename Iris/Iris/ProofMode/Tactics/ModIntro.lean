/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
module

import Iris.ProofMode.Modalities
public import Iris.ProofMode.SolveSideCondition
public meta import Iris.ProofMode.Tactics.Basic

namespace Iris.ProofMode

public section
open Qq BI Std

/-- Reified version of ModalityAction -/
inductive ModalityActionQ (PROP1 : Q(Type u)) (PROP2 : Q(Type u)) : Type where
  | isEmpty
  | forall (C : Q($PROP1 → Prop))
  | transform (C : Q($PROP2 → $PROP1 → Prop))
  | clear
  | id

theorem modaction_forall [BI PROP] {p P} (M : Modality PROP PROP) {C}
    (h : M.action p = .forall C) (hC : C P) : □?p P ⊢ M.M iprop(□?p P) := by
  have hs := M.spec p
  rw [h] at hs
  apply (hs _ hC)

theorem modaction_transform [BI PROP1] [BI PROP2]
    {p P Q} (M : Modality PROP1 PROP2) {C}
    (h : M.action p = .transform C) (hC : C P Q) : □?p P ⊢ M.M iprop(□?p Q) := by
  have hs := M.spec p
  rw [h] at hs
  apply (hs _ _ hC)

theorem modaction_clear [BI PROP1] [BI PROP2] {p P} (M : Modality PROP1 PROP2)
    (h : M.action p = .clear) : □?p P ⊢ M.M emp :=
  match p, h with
  | true, _ => affine.trans M.emp
  | false, h => by
    have hs := M.spec false
    simp [h] at hs
    calc
      _ ⊢ □?false P ∗ emp := sep_emp.mpr
      _ ⊢ True ∗ M.M emp  := sep_mono true_intro M.emp
      _ ⊢ M.M emp         := true_sep.mp

theorem modaction_id [BI PROP] {p P} (M : Modality PROP PROP) (h : M.action p = .id) :
    □?p P ⊢ M.M iprop(□?p P) := by
  have hs := M.spec p
  rw [h] at hs
  apply hs

theorem modaction_sep_emp_left [BI PROP1] [bi2: BI PROP2]
    {elhs erhs erhs'} {M : Modality PROP1 PROP2}
    (h1 : elhs ⊢ M.M emp) (h2 : erhs ⊢ M.M erhs') : elhs ∗ erhs ⊢ M.M iprop(erhs') := calc
  _ ⊢ M.M emp ∗ M.M erhs'    := sep_mono h1 h2
  _ ⊢ M.M iprop(emp ∗ erhs') := M.sep
  _ ⊢ M.M erhs'              := M.mono emp_sep.1

theorem modaction_sep_emp_right [BI PROP1] [bi2: BI PROP2]
    {elhs elhs' erhs} {M : Modality PROP1 PROP2}
    (h1 : elhs ⊢ M.M elhs') (h2 : erhs ⊢ M.M emp) : elhs ∗ erhs ⊢ M.M iprop(elhs') := calc
  _ ⊢ M.M elhs' ∗ M.M emp    := sep_mono h1 h2
  _ ⊢ M.M iprop(elhs' ∗ emp) := M.sep
  _ ⊢ M.M elhs'              := M.mono sep_emp.1

theorem modaction_sep [BI PROP1] [bi2: BI PROP2]
    {elhs erhs elhs' erhs'} {M : Modality PROP1 PROP2}
    (h1 : elhs ⊢ M.M elhs') (h2 : erhs ⊢ M.M erhs') : elhs ∗ erhs ⊢ M.M iprop(elhs' ∗ erhs') :=
  (sep_mono h1 h2).trans M.sep

@[rocq_alias tac_modal_intro]
theorem modintro [BI PROP1] [BI PROP2] {e e'} {α Φ M} {sel : α}
    {P : PROP2} {Q : PROP1}
    [inst : FromModal .out M Φ sel P Q] (h1 : e ⊢ M.M e') (h2 : e' ⊢ Q) (hΦ : Φ) : e ⊢ P := calc
  e ⊢ M.M e' := h1
  _ ⊢ M.M Q  := M.mono h2
  _ ⊢ P      := inst.from_modal hΦ

public meta section
open Lean Elab Tactic Meta

private def parseModalityActionQ {prop1 prop2 : Q(Type u)}
    (act : Q(ModalityAction $prop1 $prop2)) :
    ProofModeM (ModalityActionQ prop1 prop2) := do
  let act ← whnf q($act)
  match_expr act with
  | ModalityAction.isEmpty _ _ => return .isEmpty
  | ModalityAction.forall _ C => return .forall C
  | ModalityAction.transform _ _ C => return .transform C
  | ModalityAction.clear _ _ => return .clear
  | ModalityAction.id _ => return .id
  | _ => throwIPMError "unknown modality action {act}"

/--
Applies modality actions to transform proof mode context.

# Parameters
- `hyps` - Context in `prop2`
- `M` - Modality being introduced (`prop1 → prop2`)

# Returns
A tuple containing:
- Transformed context term
- Transformed context `hyps'` in `prop1`
- Proof of `hyps ⊢ M hyps'`
-/
def iModAction {prop1 prop2 : Q(Type u)} {bi1 : Q(BI $prop1)} {bi2} {e}
  (hyps : @Hyps u prop2 bi2 e) (M : Q(Modality $prop1 $prop2)) :
  ProofModeM ((e' : _) × Hyps bi1 e' × Q($e ⊢ $(M).M $e')) := do
  -- pre-compute the actions
  let iact ← parseModalityActionQ q($(M).action true)
  let sact ← parseModalityActionQ q($(M).action false)
  go iact sact hyps.toArray (hyps.toArray.size - 1) e
where
  go (iact sact : ModalityActionQ prop1 prop2) (hs : Array (Hyp prop2)) (i : Nat)
      (epre : Q($prop2)) :        -- caller guarantees `epre = sepFoldE bi2 hs[0…i]`
      ProofModeM ((e' : Q($prop1)) × Hyps bi1 e' × Q($epre ⊢ $(M).M $e')) := do
    match i, hs[i]? with
    | _, none =>                                            -- empty context
      have eEmp : Q($prop1) := sepFoldE bi1 #[]
      have pf0 : Q((emp : $prop2) ⊢ $(M).M (emp : $prop1)) := q($(M).emp)
      have pf : Q($epre ⊢ $(M).M $eEmp) := pf0
      return ⟨eEmp, Hyps.ofArray bi1 #[] eEmp, pf⟩
    | 0, some h =>                                          -- no `∗` above `hs[0]`
      let ⟨o, pfR⟩ ← step iact sact h
      have eR : Q($prop1) := sepFoldE bi1 o.toArray
      have pf : Q($epre ⊢ $(M).M $eR) := pfR
      return ⟨eR, Hyps.ofArray bi1 o.toArray eR, pf⟩
    | i+1, some h =>
      -- bind every meta-level fold as an opaque atom before any `q(…)`
      have preL : Q($prop2) := sepFoldE bi2 (hs.extract 0 (i+1))
      let ⟨eL, accL, pfL⟩ ← go iact sact hs i preL
      let ⟨o, pfR⟩ ← step iact sact h
      have xe : Q($prop2) := (h.e bi2).1
      have eR : Q($prop1) := sepFoldE bi1 o.toArray
      have pfR : Q($xe ⊢ $(M).M $eR) := pfR
      match accL.toArray.isEmpty, o with
      | true, none =>
        -- `accL` empty ⇒ `eL` is `emp`; `o` cleared ⇒ `eR` is `emp`
        have pfLE : Q($preL ⊢ $(M).M (emp : $prop1)) := pfL
        have pfRE : Q($xe ⊢ $(M).M (emp : $prop1)) := pfR
        have pf0 : Q(iprop($preL ∗ $xe) ⊢ $(M).M (emp : $prop1)) :=
          q(modaction_sep_emp_left $pfLE $pfRE)
        have pf : Q($epre ⊢ $(M).M $eR) := pf0
        return ⟨eR, Hyps.ofArray bi1 o.toArray eR, pf⟩
      | true, some _ =>
        have pfLE : Q($preL ⊢ $(M).M (emp : $prop1)) := pfL
        have pf0 : Q(iprop($preL ∗ $xe) ⊢ $(M).M $eR) :=
          q(modaction_sep_emp_left $pfLE $pfR)
        have pf : Q($epre ⊢ $(M).M $eR) := pf0
        return ⟨eR, Hyps.ofArray bi1 o.toArray eR, pf⟩
      | false, none =>
        have pfRE : Q($xe ⊢ $(M).M (emp : $prop1)) := pfR
        have pf0 : Q(iprop($preL ∗ $xe) ⊢ $(M).M $eL) :=
          q(modaction_sep_emp_right $pfL $pfRE)
        have pf : Q($epre ⊢ $(M).M $eL) := pf0
        return ⟨eL, accL, pf⟩
      | false, some h' =>
        have pf0 : Q(iprop($preL ∗ $xe) ⊢ $(M).M iprop($eL ∗ $eR)) :=
          q(modaction_sep $pfL $pfR)
        have pf : Q($epre ⊢ $(M).M iprop($eL ∗ $eR)) := pf0
        return ⟨q(iprop($eL ∗ $eR)),
                Hyps.ofArray bi1 (accL.toArray.push h') q(iprop($eL ∗ $eR)),
                pf⟩
  /-- Image of one hypothesis under the modality: `none` means it is cleared.
      Returns a proof of `□?p ty ⊢ M.M X` where `X` is `emp` or the image. -/
  step (iact sact : ModalityActionQ prop1 prop2) (h : Hyp prop2) :
      ProofModeM ((o : Option (Hyp prop1)) ×
                  Q($((h.e bi2).1) ⊢ $(M).M $(sepFoldE bi1 o.toArray))) := do
    let p' := h.persistent?
    let p  := h.p; let ty := h.ty; let name := h.name; let ivar := h.ivar
    match if p' then iact else sact with
    | .isEmpty =>
      throwIPMError "{if p' then "intuitionistic" else "spatial"} context is not empty"
    | .forall C => do
      have : $prop1 =Q $prop2 := ⟨⟩
      have : $bi1 =Q $bi2 := ⟨⟩
      let .some hC ← ProofModeM.trySynthInstanceQ q($C $ty)
        | throwIPMError "hypothesis {name}: {ty} does not satisfy {C}"
      -- bridge through defeq since `M.action` cannot unify directly with the pattern
      have heq : Q(@ModalityAction.forall $prop1 $C = .forall $C) :=
        q(Eq.refl (ModalityAction.forall $C))
      have heq : Q($(M).action $p = .forall $C) := heq
      have pf0 : Q(iprop(□?$p $ty) ⊢ $(M).M iprop(□?$p $ty)) :=
        q(modaction_forall $M $heq $hC)
      let h' : Hyp prop1 := { name, ivar, p, ty }
      have pf : Q($((h.e bi2).1) ⊢ $(M).M $(sepFoldE bi1 (some h').toArray)) := pf0
      return ⟨some h', pf⟩
    | .transform C => do
      let ty' ← mkFreshExprMVarQ q($prop1)
      let .some hC ← ProofModeM.trySynthInstanceQ q($C $ty $ty')
        | throwIPMError "cannot transform hypothesis {name}: {ty} with {C}"
      have heq : Q(@ModalityAction.transform $prop1 $prop2 $C = .transform $C) :=
        q(Eq.refl (ModalityAction.transform $C))
      have heq : Q($(M).action $p = .transform $C) := heq
      have pf0 : Q(iprop(□?$p $ty) ⊢ $(M).M iprop(□?$p $ty')) :=
        q(modaction_transform $M $heq $hC)
      let h' : Hyp prop1 := { name, ivar, p, ty := ty' }
      have pf : Q($((h.e bi2).1) ⊢ $(M).M $(sepFoldE bi1 (some h').toArray)) := pf0
      return ⟨some h', pf⟩
    | .clear => do
      have heq : Q(@ModalityAction.clear $prop1 $prop2 = .clear) :=
        q(Eq.refl (ModalityAction.clear))
      have heq : Q($(M).action $p = @ModalityAction.clear $prop1 $prop2) := heq
      have pf0 : Q(iprop(□?$p $ty) ⊢ $(M).M (emp : $prop1)) :=
        q(modaction_clear $M $heq)
      have pf : Q($((h.e bi2).1) ⊢
                  $(M).M $(sepFoldE bi1 (none : Option (Hyp prop1)).toArray)) := pf0
      return ⟨none, pf⟩
    | .id => do
      have : $prop1 =Q $prop2 := ⟨⟩
      have : $bi1 =Q $bi2 := ⟨⟩
      have heq : Q(@ModalityAction.id $prop1 = .id) := q(Eq.refl (ModalityAction.id))
      have heq : Q($(M).action $p = .id) := heq
      have pf0 : Q(iprop(□?$p $ty) ⊢ $(M).M iprop(□?$p $ty)) :=
        q(modaction_id $M $heq)
      let h' : Hyp prop1 := { name, ivar, p, ty }
      have pf : Q($((h.e bi2).1) ⊢ $(M).M $(sepFoldE bi1 (some h').toArray)) := pf0
      return ⟨some h', pf⟩
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
def iModIntroCore {e} (hyps : @Hyps u prop bi e) (goal : Q($prop))
  (sel : TSyntax `term)
  (k : ∀ {prop' bi' P}, @Hyps u prop' bi' P → ∀ Q : Q($prop'), ProofModeM Q($P ⊢ $Q) := addBIGoal)
   : ProofModeM (Q($e ⊢ $goal)) := do
    let prop' : Q(Type u) ← mkFreshExprMVarQ q(Type u)
    let bi' ← mkFreshExprMVarQ q(BI $prop')
    let Φ ← mkFreshExprMVarQ q(Prop)
    let M ← mkFreshExprMVarQ q(Modality $prop' $prop)
    let α : Q(Type u) ← mkFreshExprMVarQ q(Type u)
    let sel ← elabTermEnsuringTypeQ (← `(term | iprop($sel))) α
    let Q ← mkFreshExprMVarQ q($prop')
    -- `M Q ⊢ goal`
    let .some _ ←
      ProofModeM.trySynthInstanceQ q(@FromModal .out $prop' $prop $α $bi' $bi $M $Φ $sel $goal $Q)
      | throwIPMError "{goal} is not a \
          modality{if sel.isMVar then m!"" else m!" matching {sel}"}"
    -- show the side condition
    let hΦ ← iSolveSidecondition q($Φ)
    -- perform modality actions, get transformed context `hyps'` and `pf : hyps ⊢ M hyps'`
    let ⟨_, hyps', pf⟩ ← iModAction hyps M
    -- get proof `hyps' ⊢ Q`
    let pf' ← k hyps' Q
    return q(modintro (sel:=$sel) $pf $pf' $hΦ)

/--
  `imodintro sel` introduces the modality at the top of the goal (e.g., `□`,
  `<pers>`, `▷`, `|==>`), adjusting the context as required by the modality.
  The tactic succeeds only when the selector term `sel` matches the modality.
-/
elab "imodintro " colGt sel:term : tactic => do
  ProofModeM.runTactic `imodintro λ mvar { hyps, goal, .. } => do
    let pf ← iModIntroCore hyps goal sel

    mvar.assign pf

/--
  `imodintro sel` introduces the modality at the top of the goal (e.g., `□`,
  `<pers>`, `▷`, `|==>`), adjusting the context as required by the modality.
-/
macro "imodintro" : tactic => `(tactic | imodintro _)

/--
  `inext` introduces the later modality (`▷`), adjusting the context as
  required by the modality. The tactic is equivalent to `imodintro (▷^[_] _)`.
-/
macro "inext" : tactic => `(tactic | imodintro (▷^[_] _))
