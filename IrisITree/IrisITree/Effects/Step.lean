/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunsong Yang, Michael Sammler
-/

module

import Iris.ProofMode
public import IrisITree.Core.Wpi
public import ITree.Effects.Step
public import Iris.Instances.Lib.FUpd

public section

namespace IrisITree

open Iris Iris.BI ITree ITree.Effects

section handler

variable {PROP : Type _} [BI PROP]

/-- A logical modality used to interpret operational `step` events. -/
class StepMod (PROP : Type _) [BI PROP] where
  apply : PROP → PROP
  mono (P Q : PROP) : (P -∗ Q) -∗ apply P -∗ apply Q

instance : CoeFun (StepMod PROP) (fun _ => PROP → PROP) where
  coe m := @StepMod.apply PROP _ m

namespace StepMod

theorem map (m : StepMod PROP) (P Q : PROP) :
    m P -∗ (P -∗ Q) -∗ m Q := by
  iintro HP Hwand
  iapply m.mono $$ Hwand HP

/-- Interpret a step with the identity modality, giving the *total* logic. -/
@[reducible] def id : StepMod PROP where
  apply := fun P => P
  mono _ _ := by iintro $

/-- Interpret a step as one later modality, giving the *partial* logic. -/
@[reducible] def later : StepMod PROP where
  apply P := iprop(▷ P)
  mono _ _ := by
    iintro Hwand HP
    inext; iapply Hwand $$ [$]

theorem wand (m : StepMod PROP) (P Q : PROP) :
    m iprop(P -∗ Q) -∗ P -∗ m Q := by
  iintro Hwand HP
  iapply m.map $$ Hwand
  iintro HPQ
  iapply HPQ $$ HP

end StepMod

/-- Interpret an operational step using `m`. -/
def stepH (m : StepMod PROP) : IHandler PROP stepE where
  ihandle := fun _ Φ _ => m (Φ ⟨⟩)
  ihandle_mono := by
    iintro %_ %Φ %Φ' %_ %_ HΦwand _ HΦ
    ispecialize HΦwand $$ %⟨⟩
    iapply m.map $$ HΦ HΦwand

instance stepH_sequential (m : StepMod PROP) : Sequential (stepH m) := by
  constructor
  iintro %_ %_ %_ H
  simp only [stepH]
  iexact H

/-- An identity step interpretation implies a later step interpretation. -/
instance stepH_ident_later :
    WandH (stepH .id (PROP := PROP)) (stepH .later) := by
  constructor
  intro _ _ _
  exact entails_wand later_intro

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
  {E : Effect} {H : IHandler PROP E}
  {m : StepMod PROP}
  [sub : stepE -< E] [Hin : InH (stepH m) H]

theorem wpi_step M (Φ : PUnit → PROP) :
    m iprop(|={M}=> Φ ⟨⟩) -∗
    WPi step @> H; M {{ Φ }} := by
  unfold step
  iintro HΦ; iapply wpi_trigger
  iapply fupd_mask_intro (by simp)
  iintro Hclose; simp only [stepH]
  iapply m.map $$ HΦ
  iintro HΦ; imod Hclose; imod HΦ
  imodintro; iframe

end wpi_rules

section exec

open ITree.Exec

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

/-- Executing an identity-interpreted step requires no later credits. -/
instance stepEH_id_adequate :
    SEHandlerAdequate (stepH (.id (PROP := PROP))) (stepEH (fun _ => 0)) where
  inv _ := iprop(emp)
  adequate := by
    intro i ⟨st, sl⟩ C Φ₁ Φ₂ Hhandle
    simp only [stepH, stepEH] at *
    simp only [Nat.zero_le, true_and, Nat.sub_zero] at Hhandle
    iintro HΦ _ !>
    iexists ⟨⟩, (ULift.up (st.down + 1), ULift.up sl.down)
    iframe; itrivial

variable [BILaterCredits PROP] [BIFUpdLaterCredits PROP]

/-- Executing a later-interpreted step consumes one later credit. -/
instance stepEH_later_adequate :
    SEHandlerAdequate (stepH (.later (PROP := PROP))) (stepEH (fun _ => 1)) where
  inv s := £ s.2.down
  adequate := by
    intro i ⟨st, sl⟩ C Φ₁ Φ₂ ⟨Hcredit, HC⟩
    simp only [stepH] at *
    iintro HΦ Hlc
    ihave Hparts : £ 1 ∗ £ (sl.down - 1) $$ [Hlc]
    · iapply lc_split.mp
      rw [Nat.add_sub_of_le Hcredit]
      iexact Hlc
    icases Hparts with ⟨Hone, Hrest⟩
    imod lc_fupd_elim_later $$ Hone HΦ with HΦ
    imodintro
    iexists ⟨⟩, (ULift.up (st.down + 1), ULift.up (sl.down - 1))
    iframe; itrivial

end exec

end IrisITree
