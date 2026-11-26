/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunsong Yang, Michael Sammler
-/

module

import Iris.ProofMode
public import ITree.Effects.Demonic
public import IrisITree.Core.Wpi

public section
namespace IrisITree

open Iris Iris.BI ITree ITree.Effects
variable {PROP : Type _} [BI PROP]

def demonicH (α : Type _) : IHandler PROP (demonicE α) where
  ihandle _ Φ _ := iprop% ∀ a, Φ a
  ihandle_mono i Φ Φ' s s':= by
    iintro HΦwand #Hswand H %a
    iapply HΦwand
    iapply H

instance demonicH_sequential {α : Type _} :
    Sequential (PROP := PROP) (demonicH (PROP := PROP) α) := by
  constructor
  unfold demonicH
  iintro %i %Φ %s $

section wpi_rules

variable [BIFUpdate PROP] {E : Effect}
  {H : IHandler PROP E} {α : Type _}
  [sub : demonicE α -< E] [Hin : InH (demonicH (PROP := PROP) α) H]

theorem wpi_demonic (M : CoPset) (Φ : α → Prop) [Hdec : DecidablePred Φ]
    [Inhabited {a // Φ a}] (Ψ : {a // Φ a} → PROP) :
    (∀ a, Ψ a) ⊢ WPi choose Φ @> H;M {{ Ψ }} := by
  iintro HΨ
  unfold choose
  iapply wpi_trigger
  iapply fupd_mask_intro (by simp)
  iintro Hclose
  simp only [demonicH]
  iintro %a
  imod Hclose
  imodintro
  iapply HΨ

end wpi_rules

section exec

open ITree.Exec

instance demonicEH_adequate [BIFUpdate PROP] {α : Type _} :
    SEHandlerAdequate (demonicH (PROP := PROP) α) (demonicEH α) where
  inv _ := iprop% emp
  adequate i s C Φ1 Φ2 Hhandle := by
    simp only [demonicH, demonicEH] at Hhandle ⊢
    rcases Hhandle with ⟨a, s', HC⟩
    iintro HΦ1 Hinv !>
    iframe %HC Hinv
    iexists s
    iapply HΦ1

end exec
end IrisITree
