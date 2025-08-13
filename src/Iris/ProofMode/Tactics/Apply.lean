/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Patterns.ProofModeTerm
import Iris.ProofMode.Tactics.Split
import Iris.ProofMode.Tactics.Pose

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem apply [BI PROP] {P Q1 Q2 R : PROP}
    (h : P ⊢ Q1) [inst : IntoWand false false R Q1 Q2] : P ∗ R ⊢ Q2 :=
  (sep_mono h inst.1).trans wand_elim_r

theorem rec_apply [BI PROP] {P Q P' Q' Q1 Q2 R : PROP}
    (h1 : P ⊣⊢ P' ∗ Q') (h2 : Q' ⊢ Q1) (h3 : P' ∗ Q2 ⊢ R)
    [IntoWand false false Q Q1 Q2] : P ∗ Q ⊢ R :=
  (sep_congr h1 .rfl).mp.trans <| sep_assoc.mp.trans <| (sep_mono_r <| apply h2).trans h3

theorem apply_lean [BI PROP] {P Q R : PROP} (pf : ⊢ Q) (res : P ∗ Q ⊢ R) : P ⊢ R :=
  sep_emp.mpr.trans <| (sep_mono_r pf).trans res

variable {prop : Q(Type u)} {bi : Q(BI $prop)} in
def specPatGoal
    (A1 : Q($prop)) (hyps : Hyps bi e) (spats : List SpecPat)
    (addGoal : ∀ {e}, Name → Hyps bi e → (goal : Q($prop)) → MetaM Q($e ⊢ $goal)) :
    MetaM Q($e ⊢ $A1) := do
  return ← if let (some <| .ident _ _, some inst) := (spats.head?,
      ← try? (synthInstanceQ q(FromAssumption false $e $A1))) then
    pure q(($inst).from_assumption)
  else
    addGoal (headName spats) hyps A1

variable {prop : Q(Type u)} {bi : Q(BI $prop)} in
def processSpecPats
    (A1 : Q($prop)) (hypsl : Hyps bi el) (spats : List SpecPat)
    (addGoal : ∀ {e}, Name → Hyps bi e → (goal : Q($prop)) → MetaM Q($e ⊢ $goal)) :
    MetaM ((el' er' : Q($prop)) × Q($er' ⊢ $A1) × Hyps bi el' × Q($el ⊣⊢ $el' ∗ $er')) := do
  let splitPat := fun name _ => match spats.head? with
    | some <| .ident bIdent _ => binderIdentHasName name bIdent
    | some <| .idents bIdents _ => bIdents.any <| binderIdentHasName name
    | _ => false

  let ⟨el', er', hypsl', hypsr', h'⟩ := Hyps.split bi splitPat hypsl
  let m ← specPatGoal A1 hypsr' spats addGoal
  return ⟨el', er', m, hypsl', h'⟩

variable {prop : Q(Type u)} {bi : Q(BI $prop)} in
partial def iApplyCore
    (goal el er : Q($prop)) (hypsl : Hyps bi el) (spats : List SpecPat)
    (addGoal : ∀ {e}, Name → Hyps bi e → (goal : Q($prop)) → MetaM Q($e ⊢ $goal)) :
    MetaM (Q($el ∗ $er ⊢ $goal)) := do
  let A1 ← mkFreshExprMVarQ q($prop)
  let A2 ← mkFreshExprMVarQ q($prop)

  if let (some _, some _) := (← try? <| synthInstanceQ q(FromAssumption false $er $goal),
                              ← try? <| synthInstanceQ q(TCOr (Affine $el) (Absorbing $goal))) then
    -- iexact case
    return q(assumption (p := false) .rfl)
  else if let some _ ← try? <| synthInstanceQ q(IntoWand false false $er $A1 $goal) then
    -- iapply base case
    let m ← specPatGoal A1 hypsl spats addGoal
    return q(apply $m)
  else if let some _ ← try? <| synthInstanceQ q(IntoWand false false $er $A1 $A2) then
    -- iapply recursive case
    let ⟨el', _, m, hypsl', h'⟩ ← processSpecPats A1 hypsl spats addGoal
    let res : Q($el' ∗ $A2 ⊢ $goal) ← iApplyCore goal el' A2 hypsl' spats.tail addGoal
    return q(rec_apply $h' $m $res)
  else
    throwError "iapply: cannot apply {er}"

elab "iapply" colGt pmt:pmTerm : tactic => do
  let pmt ← liftMacroM <| PMTerm.parse pmt
  let mvar ← getMainGoal

  mvar.withContext do
    let g ← instantiateMVars <| ← mvar.getType
    let some { prop, e, hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"
    match pmt.term.raw with
    | .ident _ _ _ _ => do
      let ident : Ident := ⟨pmt.term.raw⟩
      if let some uniq ← try? do pure (← hyps.findWithInfo ident) then
        -- lemma from iris context
        let ⟨e', hyps', out, _, _, _, pf⟩ := hyps.remove false uniq

        let goals ← IO.mkRef #[]
        let res ← iApplyCore goal e' out hyps' pmt.spats <| goalTracker goals
        mvar.assign <| q(($pf).mp.trans $res)
        replaceMainGoal (← goals.get).toList
      else
        -- lemma from lean context
        let f ← getFVarId pmt.term
        let ⟨hyp, pf⟩ ← iPoseCore prop f ident

        let goals ← IO.mkRef #[]
        let res ← iApplyCore goal e hyp hyps pmt.spats <| goalTracker goals
        mvar.assign <| ← mkAppM ``apply_lean #[pf, res]
        replaceMainGoal (← goals.get).toList
    | .node _ _ _ =>
      -- bluntly applies lean lemma
      let mut val ← instantiateMVars (← elabTermForApply pmt.term)
      if val.isMVar then
        Term.synthesizeSyntheticMVarsNoPostponing
        val ← instantiateMVars val
      let mvarIds' ← (·.apply (term? := some m!"`{pmt.term}`")) (← getMainGoal) val
      Term.synthesizeSyntheticMVarsNoPostponing
      replaceMainGoal mvarIds'
    | _ => throwError "iapply: {pmt.term} is neither an identifier nor a node"
