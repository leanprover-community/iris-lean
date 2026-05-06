/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public meta import Iris.ProofMode.Tactics.Assumption
public meta import Iris.ProofMode.Patterns.CasesPattern

namespace Iris.ProofMode

public meta section
open Lean Elab Tactic Meta Qq BI Std

theorem combine [BI PROP] {out1 out2 out e1 e2 goal e : PROP}
  (pf : e2 ∗ □?false out ⊢ goal)
  (pf1 : e ⊣⊢ e1 ∗ out1)
  (pf2 : e1 ⊣⊢ e2 ∗ out2)
  (inst : CombineSepAs out1 out2 out)
  : e ⊢ goal :=
  calc
    e ⊢ e1 ∗ out1          := pf1.mp
    _ ⊢ (e2 ∗ out2) ∗ out1 := sep_mono pf2.mp refl
    _ ⊢ e2 ∗ (out2 ∗ out1) := sep_assoc.mp
    _ ⊢ e2 ∗ (out1 ∗ out2) := sep_mono refl sep_comm.mp
    _ ⊢ e2 ∗ out           := sep_mono refl inst.combine_sep_as
    _ ⊢ goal               := pf

/-- An simplified version of icombine for combining two propositions
    into one using the type class CombineSepAs or, by default, the separating
    conjunction -/
private def iCombineCore (hyp1 hyp2 : Ident) (pat : iCasesPat) : TacticM Unit :=
  match pat with
  | .one name => do
    ProofModeM.runTactic λ mvar { bi, hyps, goal, .. } => do
      let uniq1 ← hyps.findWithInfo hyp1
      let uniq2 ← hyps.findWithInfo hyp2

      -- Remove the original two hypotheses
      let ⟨_, hyps1, out1, _, _, _, pf1⟩ := hyps.remove true uniq1
      let ⟨_, hyps2, out2, _, _, _, pf2⟩ := hyps1.remove true uniq2

      -- Handle the combined proposition based on the type class
      let out ← mkFreshExprMVarQ _
      let some inst ← ProofModeM.trySynthInstanceQ q(CombineSepAs $out1 $out2 $out)
      | throwError "icombine: no type class instance to combine {out1} and {out2}"

      -- Introduce the new hypothesis that combines the two original hypotheses
      let ⟨_, newHyps⟩ ← Hyps.addWithInfo bi name q(false) out hyps2

      -- New proof goal for the tactic user
      let pf ← addBIGoal newHyps goal

      mvar.assign q(combine $pf $pf1 $pf2 $inst)
  | _ => throwUnsupportedSyntax

/-- An simplified version of icombine for combining multiple propositions
    into one using the type class CombineSepsAs -/
private def iCombineCoreList (hs : List Ident) (pat : iCasesPat) : TacticM Unit :=
  match pat with
  | .one name => do
    ProofModeM.runTactic λ mvar { prop, bi, hyps, goal, .. } => do
      let uniqs ← hs.mapM (fun h => hyps.findWithInfo h)
      let ⟨e, e', hyps, hyps', pf1⟩ := hyps.split bi (fun _ uniq => uniq ∈ uniqs)

      let out ← mkFreshExprMVarQ _

      -- Get the list of propositions from hyps'
      let list : List Q($prop) := Hyps.leaves hyps'
      let qlist : Q(List $prop) := list.foldr (fun p acc => q($p :: $acc)) q([])

      let some inst ← ProofModeM.trySynthInstanceQ q(CombineSepsAs $qlist $out)
      | throwError "icombine: no type class instance to combine propositions"

      let ⟨_, newHyps⟩ ← Hyps.addWithInfo bi name q(false) out hyps

      let pf ← addBIGoal newHyps goal
  | _ => throwUnsupportedSyntax

private def iCombineCoreRec (hs : List (TSyntax `ident)) (pat : iCasesPat) : TacticM Unit :=
  match hs with
  | [hyp1, hyp2] => iCombineCore hyp1 hyp2 pat
  | _ => iCombineCoreList hs pat

elab "icombine" hyps:(colGt ident)* "as" colGt pat:icasesPat : tactic => do
  let pat ← liftMacroM <| iCasesPat.parse pat  -- Parse syntax
  iCombineCoreRec hyps.toList pat
