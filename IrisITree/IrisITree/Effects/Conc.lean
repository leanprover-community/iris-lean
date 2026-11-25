/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunsong Yang, Michael Sammler
-/

module

import Iris.ProofMode
public import ITree.Effects.Conc
public import IrisITree.Core.Wpi

public section

namespace IrisITree

open Iris Iris.BI ITree ITree.Effects

section handler

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

def concH : IHandler PROP concE where
  ihandle
    | .fork, Φ, Φs => iprop(Φ .parent ∗ |={⊤, ∅}=> Φs .child)
    | .yield, Φ, _ => iprop(|={∅, ⊤}=> |={⊤, ∅}=> Φ ⟨⟩)
    | .kill, _, _ => iprop(|={∅, ⊤}=> True)
  ihandle_mono := by
    iintro %i %Φ %Φ' %Φs %Φs' HΦwand #Hswand HH
    cases i <;> dsimp only
    · icases HH with ⟨HΦ, HΦs⟩
      isplitl [HΦwand HΦ]
      · iapply HΦwand $$ HΦ
      · imod HΦs
        imodintro
        iapply Hswand $$ HΦs
    · imod HH; itrivial
    · imod HH; imodintro; imod HH; imodintro; iapply HΦwand $$ [$]

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
  {E : Effect} {H : IHandler PROP E}
  [concE -< E] [Hin : InH concH H]

theorem wpi_kill M (Φ : PUnit → PROP) :
    True -∗ WPi kill @> H; ⊤, M {{Φ}} := by
  iintro Ht; unfold kill
  iapply wpi_trigger_bind
  simp [concH]
  iapply fupd_mask_intro_subseteq (by simp) $$ [$]

theorem wpi_fork t M (Φ : PUnit → PROP) :
    Φ ⟨⟩ -∗
    WPi t @> H; ⊤ {{ _v, True }} -∗
    WPi fork t @> H; M {{Φ}} := by
  iintro HΦ Ht; unfold fork
  iapply wpi_trigger_bind
  iapply fupd_mask_intro (by simp); iintro Hm
  simp [concH]; isplitr [Ht]
  · imod Hm; iapply wpi_pure; iexact HΦ
  · imod Ht; imodintro; iapply wpi_bind_strong
    iapply wpi_wand $$ [$]; iintro %_ _
    iapply wpi_kill $$ [$]

theorem wpi_yield (Φ : PUnit → PROP) :
    Φ ⟨⟩ -∗
    WPi yield @> H; ⊤ {{ Φ }} := by
  iintro HΦ; unfold yield
  iapply wpi_trigger; simp [concH]
  iapply fupd_mask_intro_subseteq (by simp)
  iapply fupd_mask_intro_subseteq (by simp) $$ [$]

end wpi_rules

section exec

open ITree.Exec Iris.Std

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] [BIAffine PROP]

instance concEH_adequate {GE GR} :
    EHandlerAdequate (PROP:=PROP) concH (concEH (GE:=GE) (GR:=GR)) where
  inv s Ms := iprop% <affine> ⌜Ms = ListPerm.ofList (s.pool.filterMap fun t =>
      (fun t P => iprop% |={⊤, ∅}=> P t) <$> t)⌝
  adequate := by
    intro G i s Ms C k Hhandle
    let f (t : ITree GE GR) (P : ITree GE GR → PROP) := iprop(|={⊤, ∅}=> P t)
    let pending (s : ConcState (ITree GE GR)) := ListPerm.ofList (s.pool.filterMap (Option.map f))
    have pool_set_perm (xs : List (Option (ITree GE GR))) (i : Nat) (old new : Option (ITree GE GR))
        (hi : i < xs.length) (hx : xs[i] = old) :
        ((old :: xs.set i new).filterMap (Option.map f)).Perm
          ((new :: xs).filterMap (Option.map f)) := by
      suffices h : List.Perm (xs[i] :: xs.set i new) (new :: xs) from hx ▸ h.filterMap _
      exact List.set_set_perm («as» := new :: xs) (i := 0) (j := i + 1) (by grind) (by grind)
    cases i <;> simp [concEH, concH] at Hhandle ⊢
    · -- Fork case
      iintro ⟨_, _⟩ %h !>
      iexists _, _, fun P => P (k .parent), Ms ⊎ {f (k .child)},
        {fun P => P (k .parent)} ⊎ {f (k .child)}
      isplit; · itrivial
      isplit; · ipureintro; grind
      simp only [BigSepMS.bigSepMS_disjUnion.to_eq, BigSepMS.bigSepMS_singleton.to_eq]
      iframe
      isplitr
      · ipureintro
        simp [h, f, ConcState.add, ListPerm.singleton_eq, ListPerm.disjUnion_ofList]
      · iintro %_ $
    · -- Kill case
      iintro Ht %rfl
      rcases Hhandle with ⟨i, t', hi, Hget, HC⟩
      imodintro
      iexists t', .yield s.pool i hi, f t', pending (.yield s.pool i hi), ∅
      simp only [BigSepMS.bigSepMS_empty.to_eq, emp_sep.to_eq]
      iframe %HC
      isplit
      · ipureintro; rw [disjUnion_empty_left]
        -- TODO: can we prove this without unfolding the definitions using Quotient.sound?
        exact Quotient.sound (pool_set_perm s.pool i (some t') none hi Hget)
      isplit; · ipureintro; rfl
      imod Ht; iintro %P $
    · -- Yield case
      iintro >Ht %rfl
      rcases Hhandle with ⟨i, t', hi, Hget, HC⟩
      iapply fupd_mask_intro (by simp)
      iintro Hemp
      let tp' := s.pool.set s.curr (some (k ⟨⟩))
      let hi' : i < tp'.length := by grind
      iexists t', .yield tp' i hi', f t', pending (.yield tp' i hi'), {f (k ⟨⟩)}
      rw [BigSepMS.bigSepMS_singleton.to_eq]
      iframe %HC ∗
      isplit
      · ipureintro
        -- TODO: can we prove this without unfolding the definitions using Quotient.sound?
        exact Quotient.sound ((pool_set_perm tp' i (some t') none hi' Hget).trans
          (pool_set_perm s.pool s.curr none (some (k ⟨⟩)) s.curr_in_pool s.curr_is_none))
      isplit; · ipureintro; rfl
      imod Hemp; iintro %x $

end exec

end IrisITree
