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
    iapply HQ
    iapply HC
    iapply HQ
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
    apply forall_ne
    intro R
    apply wand_ne.ne; rfl
    apply wand_ne.ne
    · apply affinely_ne.ne
      apply instPlainly_ne.ne
      apply wand_ne.ne H; rfl
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
theorem coreP_elim (P : PROP) [Persistent P] : coreP P -∗ P := by
  unfold coreP
  iintro HCP
  iapply HCP
  · iintro !> !> #HP //
  · iintro !> !> HP //

/- This is an instance of `Proper` in the Rocq version. -/
@[rw_mono_rule, rocq_alias coreP_mono]
theorem coreP_mono {P Q : PROP} (h : P ⊢ Q) : coreP P ⊢ coreP Q := by
  unfold coreP
  iintro HPQ %R HR HQR
  iapply HPQ $$ HR
  imodintro
  iapply plainly_mono <| wand_mono h .rfl
  iassumption

/- This is an instance of `Proper` in the Rocq version. -/
@[rocq_alias coreP_proper]
theorem coreP_proper {P Q : PROP} (h : P ⊣⊢ Q) : coreP P ⊣⊢ coreP Q :=
  BIBase.BiEntails.ofMono coreP_mono h

@[rocq_alias coreP_entails]
theorem coreP_entails [BIPersistentlyForall PROP] (P Q : PROP) :
    (<affine> coreP P ⊢ Q) ↔ (P ⊢ <pers> Q) := by
  constructor <;> intro h
  · iintro HP
    ihave #HPQ := coreP_intro $$ HP
    imodintro
    iapply h
    iassumption
  · rw' [h] -- Same as `iapply (affinely_mono <| coreP_mono h).trans`
    iintro #HcQ
    iapply coreP_elim $$ HcQ

@[rocq_alias coreP_entails']
theorem coreP_entails' [BIPersistentlyForall PROP] {P Q : PROP} [Affine P] :
    (coreP P ⊢ Q) ↔ (P ⊢ □ Q) := by
  constructor <;> intro h
  · apply affinely_intro
    apply (coreP_entails P Q).mp
    exact affinely_elim.trans h
  · rw' [h]
    apply (wand_entails <| coreP_elim iprop(□ Q)).trans intuitionistically_elim

#rocq_ignore coreP_flip_mono "No `Proper` type class in Lean, `rw'` works both ways"

end Core
