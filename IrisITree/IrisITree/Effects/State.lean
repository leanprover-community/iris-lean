module

import Iris.ProofMode
public import ITree.Effects.State
public import IrisITree.Core.Wpi

public section

namespace IrisITree

open Iris Iris.BI ITree ITree.Effects

section handler

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

def stateH {S : Type _} (stateInterp : S → PROP) : IHandler PROP (stateE S) where
  ihandle i Φ _ :=
    iprop(∀ s, stateInterp s ={∅}=∗ stateInterp (i s) ∗ Φ s)
  ihandle_mono := by
    iintro %i %Φ %Φ' %s %s' HΦwand #Hswand HH %st Hst
    imod HH $$ Hst with ⟨$, _⟩
    imodintro; iapply HΦwand $$ [$]

instance {S : Type _} (stateInterp : S → PROP) :
    Sequential (stateH stateInterp) := by
  constructor
  unfold stateH
  iintro %i %Φ %s HH
  iexact HH

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] {S : Type _}
  (stateInterp : S → PROP)
  {E : Effect} {H : IHandler PROP E}
  [stateE S -< E] [Hin : InH (stateH stateInterp) H]

/-- Allow a mask-changing fancy update from `Ms` to `Me` while handling `get`. -/
theorem wpi_stateE_get Ms Me (Φ : S → PROP) :
    (∀ s, stateInterp s ={Ms, Me}=∗ stateInterp s ∗ Φ s) -∗
    WPi StateE.get @> H; Ms, Me {{Φ}} := by
  iintro Hw; unfold StateE.get StateE.modify
  iapply wpi_trigger
  iapply fupd_mask_intro (by simp); iintro Hm
  simp [stateH]; iintro %s Hs; imod Hm
  imod Hw $$ [$] with ⟨$, $⟩
  iapply fupd_mask_intro (by simp); iintro $

theorem wpi_get Ms Me (Φ : S → PROP) :
    (∀ s, stateInterp s ={Ms, Me}=∗ stateInterp s ∗ Φ s) -∗
    WPi get @> H; Ms, Me {{Φ}} := wpi_stateE_get _ _ _ _

/-- Allow a mask-changing fancy update from `Ms` to `Me` while handling `get`. -/
theorem wpi_stateE_set Ms Me s' (Φ : PUnit → PROP) :
    (∀ s, stateInterp s ={Ms, Me}=∗ stateInterp s' ∗ Φ ⟨⟩) -∗
    WPi StateE.set s' @> H; Ms, Me {{Φ}} := by
  iintro Hw; unfold StateE.set StateE.modify
  iapply wpi_trigger_bind
  iapply fupd_mask_intro (by simp); iintro Hm
  simp [stateH]; iintro %s Hs; imod Hm
  imod Hw $$ [$] with ⟨$, HΦ⟩
  iapply fupd_mask_intro (by simp); iintro >_
  iapply wpi_pure; iexact HΦ

theorem wpi_set Ms Me s' (Φ : PUnit → PROP) :
    (∀ s, stateInterp s ={Ms, Me}=∗ stateInterp s' ∗ Φ ⟨⟩) -∗
    WPi set s' @> H; Ms, Me {{Φ}} := wpi_stateE_set _ _ _ _ _

end wpi_rules

section exec

open ITree.Exec

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
  {S : Type _} (stateInterp : S → PROP)

instance stateEH_adequate :
    SEHandlerAdequate (stateH stateInterp) (stateEH S) where
  inv s := stateInterp s
  adequate := by
    intro i s C Φ1 Φ2 Hhandle
    simp [stateH, stateEH] at Hhandle ⊢
    iintro Hs Hinv; imod Hs $$ [$] with ⟨_, _⟩
    iintro !>; iexists _, _; iframe
    itrivial

end exec

end IrisITree
