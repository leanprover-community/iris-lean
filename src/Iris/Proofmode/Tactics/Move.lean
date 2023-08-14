/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.Proofmode.Expr
import Iris.Proofmode.Classes

namespace Iris.Proofmode
open Lean Elab Tactic Meta Qq BI Std

def Replaces [BI PROP] (K A B : PROP) := (B -∗ K) ⊢ (A -∗ K)

theorem replaces_r [BI PROP] {K P Q Q' : PROP} (h : Replaces K Q Q') :
    Replaces K iprop(P ∗ Q) iprop(P ∗ Q') :=
  wand_intro <| sep_assoc.2.trans <| wand_elim <|
  (wand_intro <| sep_assoc.1.trans wand_elim_l).trans h

theorem replaces_l [BI PROP] {K P P' Q : PROP} (h : Replaces K P P') :
    Replaces K iprop(P ∗ Q) iprop(P' ∗ Q) :=
  (wand_mono_l sep_comm.1).trans <| (replaces_r h).trans (wand_mono_l sep_comm.1)

theorem Replaces.apply [BI PROP] {P P' Q : PROP}
    (h : Replaces Q P P') (h_entails : P' ⊢ Q) : P ⊢ Q :=
  wand_entails <| (entails_wand h_entails).trans h

inductive ReplaceHyp (prop : Q(Type)) (bi : Q(BI $prop)) (Q : Q($prop)) where
  | none
  | unchanged (hyps' : Hyps prop)
  | main (hyps' : Hyps prop) (e e' : Q($prop)) (pf : Q(Replaces $Q $e $e'))

variable [Monad m] {prop : Q(Type)} (bi : Q(BI $prop)) (Q : Q($prop))
  (name : Name) (repl : HypothesisKind → Q($prop) → MetaM (ReplaceHyp prop bi Q)) in
def Hyps.replace : Hyps prop → MetaM (ReplaceHyp prop bi Q)
  | .emp _ => pure .none
  | .hyp _ _ kind name' ty => do
    if name == name' then
      let res ← repl kind ty
      if let .main hyps' e e' _ := res then
        let e' ← instantiateMVarsQ e'
        if e == e' then
          return .unchanged hyps'
      return res
    else return .none
  | .sep _ _ lhs rhs => do
    match ← rhs.replace with
    | .unchanged rhs' => return .unchanged (.mkSep bi lhs rhs')
    | .main rhs' erhs' e' pf =>
      have elhs := lhs.strip
      let hyps' := .mkSep bi lhs rhs'
      return .main hyps' q(iprop($elhs ∗ $erhs')) q(iprop($elhs ∗ $e')) q(replaces_r $pf)
    | .none => match ← lhs.replace with
      | .unchanged lhs' => return .unchanged (.mkSep bi lhs' rhs)
      | .main lhs' elhs' e' pf =>
        have erhs := rhs.strip
        let hyps' := .mkSep bi lhs' rhs
        return .main hyps' q(iprop($elhs' ∗ $erhs)) q(iprop($e' ∗ $erhs)) q(replaces_l $pf)
      | .none => pure .none

theorem to_persistent_spatial [BI PROP] {P P' Q : PROP}
    [hP : IntoPersistently false P P'] [or : TCOr (Affine P) (Absorbing Q)] :
    Replaces Q P iprop(□ P') :=
  match or with
  | TCOr.l => wand_mono_l <| (affine_affinely P).2.trans (affinely_mono hP.1)
  | TCOr.r =>
    wand_intro <| (sep_mono_r <| hP.1.trans absorbingly_intuitionistically.2).trans <|
    absorbingly_sep_r.1.trans <| (absorbingly_mono wand_elim_l).trans absorbing

theorem to_persistent_intuitionistic [BI PROP] {P P' Q : PROP}
    [hP : IntoPersistently true P P'] : Replaces Q iprop(□ P) iprop(□ P') :=
  wand_mono_l <| affinely_mono hP.1

elab "iintuitionistic" colGt hyp:ident : tactic => do
  -- parse syntax
  let name := hyp.getId
  if name.isAnonymous then
    throwUnsupportedSyntax

  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { prop, bi, hyps, goal } := parseIrisGoal? g | throwError "not in proof mode"

  match ← hyps.replace bi goal name fun kind ty => do
    let P' ← mkFreshExprMVarQ prop
    match kind with
    | .intuitionistic =>
      let _ ← synthInstanceQ q(IntoPersistently true $ty $P')
      return .main (.mkHyp bi .intuitionistic name P')
        q(iprop(□ $ty)) q(iprop(□ $P')) q(to_persistent_intuitionistic)
    | .spatial =>
      let _ ← synthInstanceQ q(IntoPersistently false $ty $P')
      let _ ← synthInstanceQ q(TCOr (Affine $ty) (Absorbing $goal))
      return .main (.mkHyp bi .intuitionistic name P') ty q(iprop(□ $P')) q(to_persistent_spatial)
  with
  | .none => throwError "unknown hypothesis"
  | .unchanged hyps' =>
    mvar.setType <| IrisGoal.toExpr { prop, bi, hyps := hyps', goal }
  | .main hyps' _e e' pf =>
    let m : Q($e' ⊢ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
      IrisGoal.toExpr { prop, bi, hyps := hyps', goal }
    mvar.assign q(Replaces.apply $pf $m)
    replaceMainGoal [m.mvarId!]

theorem from_affine [BI PROP] {p : Bool} {P P' Q : PROP} [hP : FromAffinely P' P p] :
    Replaces Q iprop(□?p P) P' :=
  wand_mono_l <| affinelyIf_of_intuitionisticallyIf.trans hP.1

elab "ispatial" colGt hyp:ident : tactic => do
  -- parse syntax
  let name := hyp.getId
  if name.isAnonymous then
    throwUnsupportedSyntax

  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { prop, bi, hyps, goal } := parseIrisGoal? g | throwError "not in proof mode"

  match ← hyps.replace bi goal name fun kind ty => do
    let P' ← mkFreshExprMVarQ prop
    match kind with
    | .intuitionistic =>
      let _ ← synthInstanceQ q(FromAffinely $P' $ty true)
      return .main (.mkHyp bi .spatial name P') q(iprop(□ $ty)) P' q(from_affine (p := true))
    | .spatial =>
      let _ ← synthInstanceQ q(FromAffinely $P' $ty false)
      return .main (.mkHyp bi .spatial name P') ty P' q(from_affine (p := false))
  with
  | .none => throwError "unknown hypothesis"
  | .unchanged hyps' =>
    mvar.setType <| IrisGoal.toExpr { prop, bi, hyps := hyps', goal }
  | .main hyps' _e e' pf =>
    let m : Q($e' ⊢ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
      IrisGoal.toExpr { prop, bi, hyps := hyps', goal }
    mvar.assign q(Replaces.apply $pf $m)
    replaceMainGoal [m.mvarId!]
