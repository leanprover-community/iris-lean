/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/

module

public import Iris.BI
public import Iris.ProofMode

@[expose] public section

namespace Iris

section Core
open BI OFE

@[rocq_alias coreP]
def coreP [Sbi PROP] (P : PROP) : PROP :=
  iprop(∀ Q, <affine> ■ (Q -∗ <pers> Q) -∗ <affine> ■ (P -∗ Q) -∗ Q)

variable [Sbi PROP]

@[rocq_alias coreP_intro]
theorem coreP_intro {P : PROP} : P -∗ coreP P := by
  unfold coreP
  iintro HP %Q HQ HPQ
  iapply affinely_plainly_elim $$ HPQ HP

@[rocq_alias coreP_persistent]
instance coreP_persistent [BIPersistentlyForall PROP] (P : PROP) : Persistent (coreP P) where
  persistent := by
    unfold coreP
    iintro HC %Q
    iapply persistently_wand_affinely_plainly
    iintro #HQ
    iapply persistently_wand_affinely_plainly
    iintro #HPQ
    ispecialize HC $$ %Q HQ
    iapply HQ
    iapply HC
    iapply HPQ

@[rocq_alias coreP_affine]
instance coreP_affine (P : PROP) [Affine P] : Affine (coreP P) where
  affine := by
    unfold coreP
    iintro HC
    iapply HC <;> iintro !> !> _ //

@[rocq_alias coreP_ne]
instance coreP_ne : NonExpansive (coreP (PROP := PROP)) where
  ne n P Q H := by
    sorry

@[rocq_alias coreP_wand]
theorem coreP_wand (P Q : PROP) : <affine> ■ (P -∗ Q) -∗ coreP P -∗ coreP Q := by
  unfold coreP
  iintro #HPQ HP %R #HR #HQR
  iapply HP $$ HR
  iintro !> !> HP
  iapply HQR
  iapply HPQ $$ HP

@[rocq_alias coreP_elim]
theorem coreP_elim (P : PROP) [inst : Persistent P] : coreP P -∗ P := by
  unfold coreP
  iintro HCP
  iapply HCP
  · iintro !> !> #HP //
  · iintro !> !> HP //

@[rocq_alias coreP_entails]
theorem coreP_entails [inst : BIPersistentlyForall PROP] {P Q : PROP} :
    (<affine> coreP P ⊢ Q) ↔ (P ⊢ <pers> Q) := by
  constructor <;> intro h
  · iintro HP
    ihave HP := coreP_intro $$ HP
    unfold coreP
    iapply HP
    · iintro !> !> #HQ //
    · iintro !> !> HP
      ihave #H := h
      imodintro
      iapply H
      unfold coreP
      iintro !> %A HH AA
      sorry
  · iintro HP
    have b := inst.persistently_sForall_2
    have a : Persistent P := sorry
    ihave #HP := coreP_elim $$ HP
    iapply h $$ HP

@[rocq_alias coreP_entails']
theorem coreP_entails' [BIPersistentlyForall PROP] {P Q : PROP} [inst : Affine P] :
    (coreP P ⊢ Q) ↔ (P ⊢ □ Q) := by
  constructor <;> intro h
  · iintro HP
    ihave a := inst.affine $$ HP
    unfold coreP at h
    ihave H := h
    sorry
  · unfold coreP
    iintro HP
    iapply HP
    · iintro !> !>
      sorry
    · sorry

end Core
