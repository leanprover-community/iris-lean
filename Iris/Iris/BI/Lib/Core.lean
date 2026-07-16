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
    unfold coreP
    refine forall_ne ?_
    intro R
    apply wand_ne.ne
    · rfl
    · apply wand_ne.ne
      · apply affinely_ne.ne
        apply instPlainly_ne.ne
        apply wand_ne.ne
        assumption
        rfl
      · rfl

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
theorem coreP_entails [inst : BIPersistentlyForall PROP] (P Q : PROP) :
    (<affine> coreP P ⊢ Q) ↔ (P ⊢ <pers> Q) := by
  constructor <;> intro h
  · iintro HP
    ihave #HPQ := coreP_intro $$ HP
    imodintro
    iapply h
    iassumption
  · have a : <affine> coreP P ⊢ <affine> coreP iprop(<pers> Q) := by
      iintro #HP
      imodintro
      unfold coreP
      iintro %R H1 H2
      ispecialize HP $$ %R H1
      iapply HP
      iintuitionistic H2
      imodintro
      iapply plainly_mono
      · apply wand_mono
        apply h
        apply BIBase.Entails.rfl
      · iexact H2
    iapply a.trans
    iintro #HcQ
    iapply coreP_elim $$ HcQ

theorem coreP_entails'_aux {P Q : PROP} [Affine P] :
    (P ⊢ <pers> Q) ↔ (P ⊢ □ Q) := by
  constructor
  · have a := affine_affinely (PROP := PROP) P
    intro h
    iintro H
    have a := a.mpr
    ihave H := a $$ H
    iintuitionistic h
    ihave a := affinely_mono h
    ispecialize a $$ H
    iexact a
  · intro h
    iintro HP
    ihave #HQ := h $$ HP
    iexact HQ

@[rocq_alias coreP_entails']
theorem coreP_entails' [BIPersistentlyForall PROP] {P Q : PROP} [inst : Affine P] :
    (coreP P ⊢ Q) ↔ (P ⊢ □ Q) := by
  have h1 := affine_affinely (coreP P)
  have h2 := coreP_entails P Q
  constructor
  · intro h
    apply coreP_entails'_aux.mp
    apply h2.mp
    iintro HP
    ihave a := h $$ HP
    iexact a
  · intro h
    have hh := affinely_intro .rfl (P := coreP P)
    have hhh := h.trans affinely_elim
    have hhhh : <affine> coreP P ⊢ Q := h2.mpr hhh
    apply h1.mpr.trans
    apply hhhh

#rocq_ignore coreP_proper "No Proper type class in Lean"
#rocq_ignore coreP_mono "No Proper type class in Lean"
#rocq_ignore coreP_flip_mono "No Proper type class in Lean"

end Core
