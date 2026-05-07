/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public meta import Iris.ProofMode.Tactics.Assumption
public meta import Iris.ProofMode.Tactics.Cases
public meta import Iris.ProofMode.Patterns.CasesPattern

namespace Iris.ProofMode

public meta section
open Lean Elab Tactic Meta Qq BI Std

theorem bigSep_nil [BI PROP] : ([∗] ([] : List PROP)) = emp := by
  simp [bigSep, bigOp]

theorem bigSep_singleton [BI PROP] (P : PROP) : ([∗] [P]) = P := by
  simp [bigSep, bigOp]

theorem bigSep_append [BI PROP] (l1 l2 : List PROP) :
    [∗] (l1 ++ l2) ⊣⊢ ([∗] l1) ∗ ([∗] l2) := by
  induction l1 with
  | nil => simp [bigSep_nil, emp_sep.symm]
  | cons x xs ih =>
    calc
      [∗] (x :: xs ++ l2) ⊣⊢ x ∗ [∗] (xs ++ l2) := bigOp_sep_cons
      _ ⊣⊢ x ∗ [∗] xs ∗ [∗] l2 := ⟨sep_mono .rfl ih.mp, sep_mono .rfl ih.mpr⟩
      _ ⊣⊢ (x ∗ [∗] xs) ∗ [∗] l2 := sep_assoc.symm
      _ ⊣⊢ [∗] (x :: xs) ∗ [∗] l2 :=
        ⟨sep_mono bigOp_sep_cons.mpr .rfl, sep_mono bigOp_sep_cons.mp .rfl⟩

theorem combine [BI PROP] {out1 out2 out e1 e2 goal e : PROP}
  (pf1 : e ⊣⊢ e1 ∗ out1)
  (pf2 : e1 ⊣⊢ e2 ∗ out2)
  (pf3 : e2 ∗ out ⊢ goal)
  (inst : CombineSepAs out1 out2 out) : e ⊢ goal := by
    calc
      e ⊢ e1 ∗ out1          := pf1.mp
      _ ⊢ (e2 ∗ out2) ∗ out1 := sep_mono pf2.mp refl
      _ ⊢ e2 ∗ (out2 ∗ out1) := sep_assoc.mp
      _ ⊢ e2 ∗ (out1 ∗ out2) := sep_mono refl sep_comm.mp
      _ ⊢ e2 ∗ out           := sep_mono refl inst.combine_sep_as
      _ ⊢ goal               := pf3

theorem combineList [BI PROP] {e el er out goal : PROP} {list : List PROP}
  (pf1 : e ⊣⊢ el ∗ er)
  (pf2 : er ⊣⊢ [∗] list)
  (pf3 : (el ∗ out) ⊢ goal)
  (inst : CombineSepsAs list out) :
  e ⊢ goal := by
    calc
      e ⊢ el ∗ er       := pf1.mp
      _ ⊢ el ∗ [∗] list := sep_mono refl pf2.mp
      _ ⊢ el ∗ out      := sep_mono refl inst.combine_seps_as
      _ ⊢ goal          := pf3

/-- An simplified version of icombine for combining two propositions
    into one using the type class CombineSepAs or, by default, the separating
    conjunction -/
private def iCombineCore (hyp1 hyp2 : Ident) (pat : iCasesPat) : TacticM Unit :=
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
    -- New proof goal for the tactic user
    let pf3 ← iCasesCore bi hyps2 goal pat q(false) out (fun hyps goal => addBIGoal hyps goal)

    mvar.assign q(combine $pf1 $pf2 $pf3 $inst)

/-- An version of icombine for combining multiple propositions into one using
    the type class CombineSepsAs -/
private def iCombineCoreList (hs : List Ident) (pat : iCasesPat) : TacticM Unit :=
  ProofModeM.runTactic λ mvar { prop, bi, e, hyps, goal, .. } => do
    let uniqs ← hs.mapM (fun h => hyps.findWithInfo h)
    let ⟨e', e'', hyps', hyps'', pf1⟩ := hyps.split _ (fun _ uniq => uniq ∈ uniqs)

    -- Get the list of propositions from hyps'
    let list : Q(List $prop) := Hyps.leaves hyps''
    have pf2 : Q($e'' ⊣⊢ [∗] $list) := sorry

    -- Handle the combined proposition based on the type class
    let out ← mkFreshExprMVarQ _
    let some inst ← ProofModeM.trySynthInstanceQ q(CombineSepsAs $list $out)
    | throwError "icombine: no type class instance to combine propositions"

    let pf3 ← iCasesCore bi hyps' goal pat q(false) out (fun hyps goal => addBIGoal hyps goal)

    -- mvar.assign q(combineList $pf1 $pf2 $pf3 $inst)

elab "icombine" hyps:(colGt ident)* "as" colGt pat:icasesPat : tactic => do
  let pat ← liftMacroM <| iCasesPat.parse pat  -- Parse syntax
  match hyps.toList with
  | [hyp1, hyp2] => iCombineCore hyp1 hyp2 pat
  | _            => iCombineCoreList hyps.toList pat
