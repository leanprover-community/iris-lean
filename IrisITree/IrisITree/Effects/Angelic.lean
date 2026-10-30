/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunsong Yang, Michael Sammler
-/

module

import Iris.ProofMode
public import ITree.Effects.Angelic
public import IrisITree.Core.Wpi

public section

namespace IrisITree

open Iris Iris.BI ITree.Effects

section handler

variable {PROP : Type _} [BI PROP]

def angelicH (α : Type _) : IHandler PROP (angelicE α) where
  ihandle := fun _ Φ _ => iprop(∃ a, Φ a)
  ihandle_mono := by
    iintro %p %Φ %Φ' %s %s' HΦwand #Hswand H
    icases H with ⟨%a, HΦ⟩
    iexists a; iapply HΦwand $$ HΦ

instance angelicH_sequential {α : Type _} :
    Sequential (angelicH (PROP := PROP) α) := by
  constructor
  unfold angelicH
  iintro %p %Φ %s H
  iexact H

end handler

section wpi_rules

open ITree

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] {E : Effect}
  {H : IHandler PROP E} {α : Type _}
  [sub : angelicE α -< E] [Hin : InH (angelicH (PROP := PROP) α) H]

theorem wpi_angelic (M : CoPset) (p : α → Prop) (a : {x // p x}) (Ψ : {x // p x} → PROP) :
    Ψ a ⊢ WPi (choose_angelic p) @> H; M {{ Ψ }} := by
  iintro HΨ; unfold choose_angelic
  iapply wpi_trigger
  iapply fupd_mask_intro
  · simp
  iintro Hfalse; simp [angelicH]; iexists a
  imod Hfalse; imodintro; iexact HΨ

end wpi_rules

section exec

open ITree.Exec

instance angelicEH_adequate {PROP : Type _} [BI PROP] [BIFUpdate PROP] {α : Type _} :
    SEHandlerAdequate (angelicH (PROP := PROP) α) (angelicEH α) where
  inv _ := iprop(emp)
  adequate := by
    intro i s C Φ1 Φ2 Hhandle
    simp [angelicH, angelicEH] at Hhandle ⊢
    iintro ⟨%a, HΦ⟩ Hinv !>; iexists a, s; iframe; itrivial

end exec

end IrisITree
