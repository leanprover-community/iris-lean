module

import Iris.ProofMode
public import ITree.Effects.Demonic
public import IrisITree.Core.Wpi

public section

namespace IrisITree

open Iris Iris.BI ITree ITree.Effects

section handler

variable {PROP : Type _} [BI PROP]

def demonicH (α : Type _) : IHandler PROP (demonicE α) where
  ihandle := fun _ Φ _ => iprop(∀ a, Φ a)
  ihandle_mono := by
    iintro %i %Φ %Φ' %s %s' HΦwand #Hswand H %a
    iapply HΦwand; iapply H

instance demonicH_sequential {α : Type _} :
    Sequential (PROP := PROP) (demonicH (PROP := PROP) α) := by
  constructor
  unfold demonicH
  iintro %i %Φ %s H
  iexact H

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] {E : Effect}
  {H : IHandler PROP E} {α : Type _}
  [sub : demonicE α -< E] [Hin : InH (demonicH (PROP := PROP) α) H]

theorem wpi_demonic (M : CoPset) (Φ : α → Prop) [Hdec : DecidablePred Φ]
    [Hi : Inhabited {a // Φ a}] (Ψ : {a // Φ a} → PROP) :
    (∀ a, Ψ a) ⊢ WPi choose Φ @> H;M {{ Ψ }} := by
  iintro HΨ; unfold choose
  set_option pp.all true in
  iapply wpi_trigger
  iapply fupd_mask_intro
  · simp
  iintro Hclose; simp [demonicH]; iintro %a
  imod Hclose; imodintro; iapply HΨ

end wpi_rules

section exec

open ITree.Exec

abbrev demonicEH := ITree.Effects.demonicEH
instance demonicEH_adequate {PROP : Type _} [BI PROP] [BIFUpdate PROP] {α : Type _} :
    SEHandlerAdequate (demonicH (PROP := PROP) α) (demonicEH α) where
  inv _ := iprop(emp)
  adequate := by
    intro i s C Φ1 Φ2 Hhandle
    simp [demonicH, demonicEH] at Hhandle ⊢
    rcases Hhandle with ⟨a, s', HC⟩
    iintro HΦ1 Hinv; imodintro
    iexists ⟨a, s'⟩; iexists s; iframe
    isplitr; itrivial
    iapply HΦ1

end exec

end IrisITree
