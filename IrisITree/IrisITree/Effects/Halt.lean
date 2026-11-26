/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunsong Yang, Michael Sammler
-/

module

import Iris.ProofMode
public import ITree.Effects.Halt
public import IrisITree.Core.Wpi

public section
namespace IrisITree

open Iris Iris.BI ITree ITree.Effects
variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

def haltH : IHandler PROP haltE where
  ihandle _ _ _ := iprop% |={∅, ⊤}=> True
  ihandle_mono _ _ _ _ _ := by
    iintro _ _ HH
    iexact HH

instance haltH_sequential : Sequential (PROP := PROP) haltH := by
  constructor
  unfold haltH
  iintro %i %Φ %s $

section wpi_rules

variable {E : Effect} {H : IHandler PROP E} [Hsub : haltE -< E] [Hin : InH haltH H]

theorem wpi_halt {R} (Φ : R → PROP) :
    ⊢ WPi HaltE.halt @> H; ⊤ {{ Φ }} := by
  unfold HaltE.halt
  iapply wpi_bind
  iapply wpi_trigger
  iapply fupd_mask_intro (by simp)
  iintro Hclose
  simp only [haltH]
  imod Hclose
  itrivial

theorem wpi_assume [BIAffine PROP] (P : Prop) [Decidable P] (Φ : { _x // P } → PROP) :
    (∀ HP, Φ HP) ⊢ WPi HaltE.assume P @> H; ⊤ {{ Φ }} := by
  unfold HaltE.assume
  by_cases HP : P <;> (simp only [HP, ↓reduceDIte]; iintro HΦ)
  · iapply wpi_pure
    iapply HΦ
  · iapply wpi_halt

end wpi_rules

section exec

open ITree.Exec ITree.Effects

instance haltEH_adequate :
    SEHandlerAdequate (haltH (PROP := PROP)) haltEH where
  inv _ := iprop% True
  adequate _ _ _ _ _ := by rintro ⟨⟩

end exec
end IrisITree
