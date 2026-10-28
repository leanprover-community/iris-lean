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

section handler

variable {PROP : Type _} [BI PROP]

def failH : IHandler PROP failE where
  ihandle := fun _ _ _ => iprop(False)
  ihandle_mono := by
    iintro %_ %_ %_ %_ %_ _ _ ⟨⟩

instance failH_sequential : Sequential (PROP := PROP) failH := by
  constructor
  iintro %i %Φ %s ⟨⟩

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] {E : Effect}
  {H : IHandler PROP E} [sub : failE -< E] [Hin : InH failH H]

theorem wpi_fail {R} (M : CoPset) (Φ : R → PROP) (s : String) :
    WPi fail s @> H; M {{ Φ }} ={M}=∗ False := by
  iintro Hwp; simp [fail, Effect.trigger]
  let e := @Subeffect.map failE E sub ({ down := s } : failE.I)
  ihave >Hwp := wpi_vis $$ Hwp
  have Hfalse : H.ihandle e.fst (fun _ => iprop(False)) (fun _ => iprop(False)) ⊢ iprop(False) :=
    (Hin.is_inH ({ down := s } : failE.I) (fun _ => iprop(False))
      (fun _ => iprop(False))).mpr.trans false_elim
  iapply false_elim
  iapply Hfalse
  iapply H.ihandle_mono e.fst $$ [] [] Hwp
  · iintro %a _; cases e.snd a
  · iintro !> %a _; cases e.snd a

omit Hin in
theorem wpi_assert {M} (P : Prop) [Decidable P] (Φ : PUnit → PROP) :
    P →
    Φ ⟨⟩ -∗
    WPi FailE.assert P @> H;M {{ Φ }} := by
  intro hP; unfold FailE.assert; simp [hP]
  iintro HΦ; iapply wpi_pure $$ [$]

end wpi_rules

section exec

open ITree.Exec

instance failEH_adequate {PROP : Type _} [BI PROP] [BIFUpdate PROP] :
    SEHandlerAdequate (failH (PROP := PROP)) failEH where
  inv _ := iprop(True)
  adequate := by
    intro i s C Φ1 Φ2 Hhandle; simp [failH]
    iintro ⟨⟩

end exec

end IrisITree
