/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Patterns.SpecPattern
import Iris.ProofMode.Tactics.Basic
import Iris.ProofMode.Tactics.Remove

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem apply [BI PROP] {P P' Q O A1 A2 : PROP} {p : Bool}
    (h1 : P ⊢ P' ∗ □?p O) (h2 : P' ⊢ A1) [h3 : IntoWand' p false O A1 A2]
    [h4 : FromAssumption false A2 Q] : P ⊢ Q :=
  h1.trans <| (sep_mono_l h2).trans <| (sep_mono_r h3.1).trans <| wand_elim_r.trans h4.1

-- todo: combine apply and apply'
theorem apply' [BI PROP] {P P' P'' A1 A2 hyp out : PROP} {p : Bool}
    (h1 : P ⊢ P' ∗ □?p hyp) (h2 : P' ⊢ P'' ∗ out)
    [h3 : IntoWand' p false hyp A1 A2] [h4 : FromAssumption false out A1]
    : P ⊢ P'' ∗ A2 :=
  h1.trans <| (sep_mono_l h2).trans <| sep_assoc.mp.trans <| sep_mono_r <|
  (sep_mono_l h4.1).trans <| sep_comm.mp.trans <| wand_elim h3.1

-- in progress
theorem general_apply [BI PROP] {P P' P'' Q R O A1 A2 : PROP} {p : Bool}
    (h1 : P ⊢ P' ∗ □?p O) (h2 : P' ⊢ P'' ∗ R) [h3 : IntoWand' p false O A1 A2]
    [h4 : FromAssumption false R A1] [h5 : FromAssumption false A2 Q] : P ⊢ P'' ∗ Q :=
  h1.trans <| (sep_mono_l h2).trans <| sep_assoc.mp.trans <| sep_mono_r <|
  (sep_mono_l h4.1).trans <| sep_comm.mp.trans <| wand_elim <| h3.1.trans <| wand_mono_r h5.1

theorem assumption' [BI PROP] {p : Bool} {P P' A Q : PROP} [inst : FromAssumption p A Q]
    [TCOr (Affine P') (Absorbing Q)] (h : P ⊢ P' ∗ □?p A) : P ⊢ Q :=
  h.trans <| (sep_mono_r inst.1).trans sep_elim_r

theorem temp [BI PROP] {P Q R Q' R' : PROP} (h1 : P ⊢ Q ∗ R) (h2 : Q ⊢ Q' ∗ R') : P ⊢ Q' ∗ (R' ∗ R) :=
  h1.trans <| (sep_mono_l (Q := R) h2).trans sep_assoc_l

-- todo: additional outputs
variable {prop : Q(Type u)} {bi : Q(BI $prop)} in
partial def removeHyps (hyps : Hyps bi P) (hyps' : Hyps bi e) (uniqs : List Name) (out : Q($prop) := q(emp))
    (h : Q($P ⊢ $e ∗ $out)) : MetaM (Σ e' out : Q($prop), Hyps bi e' × Q($P ⊢ $e' ∗ $out)) := match uniqs with
  | [] => Pure.pure ⟨_, _, hyps', h⟩
  | uniq :: rest =>
    let ⟨e', hyps', out', _, p, eq, h'⟩ := hyps'.remove true uniq
    removeHyps hyps hyps' rest q(sep $out' $out) q(temp $h ($h').mp) -- todo: update out and h

-- todo: complex spec patterns
variable {prop : Q(Type u)} (bi : Q(BI $prop)) in
partial def iApplyCore
    {P P'} (p : Q(Bool)) (hyps : Hyps bi P) (hyps' : Hyps bi P') (Q hyp : Q($prop))
    (pf : Q($P ⊢ $P' ∗ □?$p $hyp)) (pat? : Option SpecPat)
    (k : ∀ {P}, Hyps bi P → (Q : Q($prop)) → MetaM Q($P ⊢ $Q)) :
    MetaM (Q($P ⊢ $Q)) := do
  let A1 ← mkFreshExprMVarQ q($prop)
  let A2 ← mkFreshExprMVarQ q($prop)

  let intoWand' ← try? do
    synthInstanceQ q(IntoWand' $p false $hyp $A1 $A2)

  if let some _ := intoWand' then
    let A1' ← mkFreshExprMVarQ q($prop)
    let A2' ← mkFreshExprMVarQ q($prop)

    let intoWand' ← try? do
      synthInstanceQ q(IntoWand' $p false $A2 $A1' $A2')

    if let some _ := intoWand' then
      -- todo: empty list case instead of option
      if let some pat := pat? then
        -- todo: combine these into one case
        if let .one x := pat then
          let ident ← match x with
            | `(binderIdent| $name:ident) => pure name
            | _ => throwError "invalid identifier"

          let uniq ← hyps.findWithInfo ident
          let ⟨_, hyps', out, out', p', _, h⟩ := hyps'.remove true uniq
          let _ ← k (.mkHyp bi ident.getId uniq p' out') A1
          let _ ← synthInstanceQ q(FromAssumption false $out $A1)
          let pf' := q(apply' $pf ($h).mp)
          return ← iApplyCore p hyps hyps' Q A2 pf' none k
        else
          let .idents l := pat | throwError "unknown spec pattern"

          let idents ← l.mapM fun x : TSyntax ``binderIdent => match x with
            | `(binderIdent| $name:ident) => pure name
            | _ => throwError "invalid identifier"

          let uniqs ← idents.mapM hyps.findWithInfo

          let ⟨e', out, hyps', h⟩ ← removeHyps hyps' hyps' uniqs q(emp) q(sep_emp.mpr)
          let _ ← synthInstanceQ q(FromAssumption false $out $A1)
          let pf' := q(apply' $pf $h)
          return ← iApplyCore p hyps hyps' Q A2 pf' none k
      else
        let _ ← k (.mkEmp bi) A1
        return ← iApplyCore p hyps hyps' Q A2 pf none k
    else
      let m ← k hyps' A1
      let _ ← synthInstanceQ q(FromAssumption false $A2 $Q)
      return q(apply $pf $m)
  else
    let _ ← synthInstanceQ q(FromAssumption $p $hyp $Q)
    let _ ← synthInstanceQ q(TCOr (Affine $P') (Absorbing $Q))

    return q(assumption' $pf)

-- todo: case when hyp is a lean lemma (later)
-- todo: macro for when no pat is supplied
elab "iapply" colGt hyp:ident pat:specPat : tactic => do
  let pat ← liftMacroM <| SpecPat.parse pat
  let mvar ← getMainGoal

  mvar.withContext do
    let g ← instantiateMVars <| ← mvar.getType
    let some { u, prop, e, bi, hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"

    let uniq ← hyps.findWithInfo hyp
    let ⟨e', hyps', out, _, p, _, pf⟩ := hyps.remove true uniq

    let pf' : Q($e ⊢ $e' ∗ $out) := q(($pf).mp)

    let goals ← IO.mkRef #[]
    let pf ← iApplyCore bi p hyps hyps' goal out pf' pat fun {P} hyps goal => do
      let m : Q($P ⊢ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
        IrisGoal.toExpr { prop, bi, hyps, goal, .. }
      goals.modify (·.push m.mvarId!)
      pure m

    mvar.assign pf
    replaceMainGoal (← goals.get).toList
