/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunsong Yang, Michael Sammler
-/

module

import Iris.ProofMode
public import ITree.Effects.Fail
public import IrisITree.Core.Wpi

public section
namespace IrisITree

open Iris Iris.BI ITree ITree.Effects
variable {PROP : Type _} [BI PROP]

def failH : IHandler PROP failE where
  ihandle := fun _ _ _ => iprop% False
  ihandle_mono := by iintro %_ %_ %_ %_ %_ _ _ ⟨⟩

instance failH_sequential : Sequential (PROP := PROP) failH := by
  constructor
  iintro %i %Φ %s ⟨⟩

variable [BIFUpdate PROP]

section wpi_rules
variable {E : Effect} {H : IHandler PROP E} [sub : failE -< E]

theorem wpi_fail [Hin : InH failH H] {R} (M : CoPset) (Φ : R → PROP) (s : String) :
    WPi fail s @> H; M {{ Φ }} ={M}=∗ False := by
  iintro Hwp
  simp only [fail, Effect.trigger, vis_bind, pure_bind]
  icases wpi_vis $$ Hwp with >Hwp
  iapply ((Hin.is_inH _ (fun _ => iprop% False) (fun _ => iprop% False)).mpr.trans false_elim)
  unfold Subeffect.map
  iapply H.ihandle_mono $$ [] [] Hwp
  · iintro %a _; cases (sub.map _).snd a
  · iintro !> %a _; cases (sub.map _).snd a

theorem wpi_assert {M} (P : Prop) [Decidable P] (Φ : PUnit → PROP) :
    P →
    Φ ⟨⟩ -∗
    WPi FailE.assert P @> H;M {{ Φ }} := by
  iintro %hP HΦ
  simp only [FailE.assert, hP, ↓reduceIte]
  iapply wpi_pure $$ [$]

end wpi_rules

section exec
open ITree.Exec

instance failEH_adequate :
    SEHandlerAdequate (failH (PROP := PROP)) failEH where
  inv _ := iprop% True
  adequate := by
    iintro %_ %_ %_ %_ %_ %_ ⟨⟩

end exec
end IrisITree
