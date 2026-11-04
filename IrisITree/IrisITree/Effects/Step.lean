/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunsong Yang, Michael Sammler
-/

module

import Iris.ProofMode
public import IrisITree.Core.Wpi
public import ITree.Effects.Step

public section

namespace IrisITree

open Iris Iris.BI ITree ITree.Effects

variable {PROP : Type _} [BI PROP]

/-- A logical modality used to interpret operational `step` events. -/
class StepMod (m : PROP → PROP) : Prop where
  mono (P Q : PROP) : (P -∗ Q) -∗ m P -∗ m Q

namespace StepMod

variable {m : PROP → PROP} [StepMod m]

theorem map (P Q : PROP) : m P -∗ (P -∗ Q) -∗ m Q := by
  iintro HP Hwand
  iapply StepMod.mono $$ Hwand HP

theorem wand (P Q : PROP) : m iprop(P -∗ Q) -∗ P -∗ m Q := by
  iintro Hwand HP
  iapply StepMod.map $$ Hwand
  iintro HPQ
  iapply HPQ $$ HP

/-- Interpret a step with the identity modality, giving the *total* logic. -/
instance stepMod_id : StepMod (PROP := PROP) id where
  mono _ _ := by
    simp only [id]
    iintro Hwand HP
    iapply Hwand $$ [$]

/-- Interpret a step as one later modality, giving the *partial* logic. -/
instance stepMod_later : StepMod (PROP := PROP) BIBase.later where
  mono _ _ := by
    iintro Hwand HP
    inext; iapply Hwand $$ [$]

end StepMod

/-- A step modality bundled with its monotonicity law, used as the mode of `WP`. -/
structure StepMode (PROP : Type _) [BI PROP] where
  m : PROP → PROP
  [step_mod : StepMod m]

/-- Bundle a step modality and its inferred law for use in `WP e @ step[m]`. -/
notation "step[" m "]" => StepMode.mk m

section handler

/-- Interpret an operational step using the step modality `m`. -/
def stepH (m : PROP → PROP) [StepMod m] : IHandler PROP stepE where
  ihandle := fun _ Φ _ => m (Φ ⟨⟩)
  ihandle_mono := by
    iintro %_ %Φ %Φ' %_ %_ HΦwand _ HΦ
    ispecialize HΦwand $$ %⟨⟩
    iapply StepMod.map $$ HΦ HΦwand

instance stepH_sequential {m : PROP → PROP} [StepMod m] : Sequential (stepH m):= by
  constructor
  iintro %_ %_ %_ H
  simp only [stepH]
  iexact H

/-- An identity step interpretation implies a later step interpretation. -/
instance stepH_ident_later :
    WandH (stepH (PROP := PROP) id) (stepH BIBase.later) := by
  constructor
  intro _ _ _
  exact entails_wand later_intro

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
  {E : Effect} {H : IHandler PROP E}
  {m : PROP → PROP} [StepMod m]
  [sub : stepE -< E] [Hin : InH (stepH m) H]

theorem wpi_step Ms Me (Φ : PUnit → PROP) :
    m iprop(|={Ms, Me}=> Φ ()) -∗
    WPi step @> H; Ms,Me {{ Φ }} := by
  unfold step
  iintro HΦ; iapply wpi_trigger
  iapply fupd_mask_intro (by simp)
  iintro Hclose; simp only [stepH]
  iapply StepMod.map $$ HΦ
  iintro HΦ; imod Hclose; imod HΦ
  imodintro; iframe

end wpi_rules

section exec

open ITree.Exec

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

/-- Executing an identity-interpreted step requires no later credits. -/
instance stepEH_id_adequate :
    SEHandlerAdequate (stepH (PROP := PROP) id) (stepEH (fun _ => 0)) where
  inv _ := iprop(emp)
  adequate := by
    intro i ⟨st, sl⟩ C Φ₁ Φ₂ Hhandle
    simp only [stepH, stepEH, id] at *
    simp only [Nat.zero_le, true_and, Nat.sub_zero] at Hhandle
    iintro HΦ _ !>
    iexists ⟨⟩, (ULift.up (st.down + 1), ULift.up sl.down)
    iframe; itrivial

variable [BILaterCredits PROP] [BIFUpdLaterCredits PROP]

/-- Executing a later-interpreted step consumes one later credit. -/
instance stepEH_later_adequate :
    SEHandlerAdequate (stepH (PROP := PROP) BIBase.later) (stepEH (fun _ => 1)) where
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
