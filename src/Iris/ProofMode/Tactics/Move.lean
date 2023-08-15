/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.ProofMode.Expr
import Iris.ProofMode.Classes

namespace Iris.ProofMode
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

inductive ReplaceHyp {prop : Q(Type)} (bi : Q(BI $prop)) (Q : Q($prop)) where
  | none
  | unchanged (ehyps') (hyps' : Hyps bi ehyps')
  | main (e e' : Q($prop)) (hyps' : Hyps bi e') (pf : Q(Replaces $Q $e $e'))

variable [Monad m] {prop : Q(Type)} (bi : Q(BI $prop)) (Q : Q($prop))
  (name : Name) (repl : Name → Q(Bool) → Q($prop) → MetaM (ReplaceHyp bi Q)) in
def Hyps.replace : ∀ {e}, Hyps bi e → MetaM (ReplaceHyp bi Q)
  | _, .emp _ => pure .none
  | _, .hyp _ name' uniq p ty _ => do
    if name == name' then
      let res ← repl uniq p ty
      if let .main e e' hyps' _ := res then
        let e' ← instantiateMVarsQ e'
        if e == e' then
          return .unchanged _ hyps'
      return res
    else return .none
  | _, .sep _ elhs erhs _ lhs rhs => do
    match ← rhs.replace with
    | .unchanged _ rhs' => return .unchanged _ (.mkSep lhs rhs')
    | .main erhs₀ _ rhs' pf =>
      let hyps' := .mkSep lhs rhs'
      return .main q(iprop($elhs ∗ $erhs₀)) _ hyps' q(replaces_r $pf)
    | .none => match ← lhs.replace with
      | .unchanged _ lhs' => return .unchanged _ (.mkSep lhs' rhs)
      | .main elhs₀ _ lhs' pf =>
        let hyps' := .mkSep lhs' rhs
        return .main q(iprop($elhs₀ ∗ $erhs)) _ hyps' q(replaces_l $pf)
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

  match ← hyps.replace bi goal name fun uniq p ty => do
    let P' ← mkFreshExprMVarQ prop
    let _ ← synthInstanceQ q(IntoPersistently $p $ty $P')
    match matchBool p with
    | .inl _ =>
      return .main q(iprop(□ $ty)) q(iprop(□ $P')) (.mkHyp bi name uniq p P' _)
        q(to_persistent_intuitionistic)
    | .inr _ =>
      let _ ← synthInstanceQ q(TCOr (Affine $ty) (Absorbing $goal))
      return .main ty q(iprop(□ $P')) (.mkHyp bi name uniq q(true) P' _) q(to_persistent_spatial)
  with
  | .none => throwError "unknown hypothesis"
  | .unchanged _ hyps' =>
    mvar.setType <| IrisGoal.toExpr { prop, bi, hyps := hyps', goal }
  | .main _e e' hyps' pf =>
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

  match ← hyps.replace bi goal name fun uniq p ty => do
    let P' ← mkFreshExprMVarQ prop
    match matchBool p with
    | .inl _ =>
      let _ ← synthInstanceQ q(FromAffinely $P' $ty true)
      return .main q(iprop(□ $ty)) P' (.mkHyp bi name uniq q(false) P' _) q(from_affine (p := true))
    | .inr _ =>
      let _ ← synthInstanceQ q(FromAffinely $P' $ty false)
      return .main ty P' (.mkHyp bi name uniq p P' _) q(from_affine (p := false))
  with
  | .none => throwError "unknown hypothesis"
  | .unchanged _ hyps' =>
    mvar.setType <| IrisGoal.toExpr { prop, bi, hyps := hyps', goal }
  | .main _e e' hyps' pf =>
    let m : Q($e' ⊢ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
      IrisGoal.toExpr { prop, bi, hyps := hyps', goal }
    mvar.assign q(Replaces.apply $pf $m)
    replaceMainGoal [m.mvarId!]
