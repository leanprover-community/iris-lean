/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public import Iris.BI
public import Iris.BI.Extensions
public import Iris.BI.Sbi
public import Iris.ProofMode
public import Iris.ProofMode.Classes
public meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris

open Iris.Std BI ProofMode

namespace AffineEM

variable {PROP : Type _} [BI PROP]
variable (em : ∀ P : PROP, ⊢ P ∨ ¬P)
variable (P Q : PROP)
include em

@[rocq_alias affine_em.sep_dup]
theorem sep_dup [Affine P] : P ⊢ P ∗ P := by
  iintro HP
  icases (em P) with (HP' | HnotP)
  · iframe HP HP'
  · iexfalso
    iapply HnotP $$ HP

@[rocq_alias affine_em.and_sep]
theorem and_sep [BIAffine PROP] : P ∧ Q ⊢ P ∗ Q := by
  iintro HPQ
  icases sep_dup $$ HPQ with ⟨HPQ, HPQ'⟩
  · assumption
  · isplitl [HPQ]
    · icases HPQ with ⟨HP, -⟩
      iassumption
    · icases HPQ' with ⟨-, HQ⟩
      iassumption

end AffineEM

namespace LoebEM

@[rocq_alias löb_em.later_anything]
theorem later_anything [BI PROP] (em : ∀ P : PROP, ⊢ P ∨ ¬P) [BILoeb PROP] :
    ⊢@{PROP} ▷ P := by
  icases (em iprop(▷ False)) with #(HP | HnotP)
  · inext
    iexfalso
    iassumption
  · iexfalso
    iloeb as IH
    ispecialize HnotP $$ IH
    iassumption

@[rocq_alias löb_em.later_inconsistent]
theorem later_inconsistent [Sbi PROP] (em : ∀ P : PROP, ⊢ P ∨ ¬P) : ⊢@{PROP} False := by
  apply later_soundness (PROP := PROP) (P := iprop(False))
  apply later_anything
  assumption

end LoebEM

namespace SavedProp

variable [BI PROP] [instAffine : BIAffine PROP] {P Q : PROP}
variable (bupd : PROP → PROP)
variable (bupd_intro : ∀ {P : PROP}, P ⊢ bupd P)
variable (bupd_mono : ∀ {P Q : PROP}, (P ⊢ Q) → bupd P ⊢ bupd Q)
variable (bupd_trans : ∀ {P : PROP}, bupd (bupd P) ⊢ bupd P)
variable (bupd_frame_right : ∀ {P R : PROP}, bupd P ∗ R ⊢ bupd iprop(P ∗ R))
variable (ident : Type _) (saved : ident → PROP → PROP)
variable [instPers : ∀ (i : ident) (P : PROP), Persistent (saved i P)]
variable (sprop_alloc_dep : ∀ {P : ident → PROP}, ⊢ bupd (∃ i, saved i (P i)))
variable (sprop_agree : ∀ (i : ident) (P Q : PROP), saved i P ∧ saved i Q ⊢ □ (P ↔ Q))
variable (consistency : ¬(⊢ bupd iprop(False)))

include bupd_mono in
omit instAffine in
@[rw_mono_rule, rocq_alias savedprop.bupd_mono']
theorem bupd_mono' (h : P ⊢ Q) : bupd P ⊢ bupd Q := bupd_mono h

include bupd_frame_right bupd_trans bupd_mono in
omit instAffine in
@[rocq_alias savedprop.elim_modal_bupd]
theorem elim_modal_bupd (p : Bool) : ElimModal True p io false (bupd P) P (bupd Q) (bupd Q) where
  elim_modal _ := calc
    _ ⊢ bupd P ∗ (P -∗ bupd Q) := sep_mono_left intuitionisticallyIf_elim
    _ ⊢ bupd iprop(P ∗ (P -∗ bupd Q)) := bupd_frame_right
    _ ⊢ bupd (bupd Q) := bupd_mono wand_elim_right
    _ ⊢ bupd Q := bupd_trans

@[reducible, rocq_alias savedprop.A]
def A (i : ident) : PROP := iprop(∃ P, □ (¬P ∗ saved i P))

include sprop_alloc_dep in
omit instAffine instPers in
@[rocq_alias savedprop.A_alloc]
theorem A_alloc : ⊢ bupd (∃ i, saved i (A ident saved i)) := sprop_alloc_dep

include sprop_agree in
@[rocq_alias savedprop.saved_NA]
theorem saved_NA (i : ident) : saved i (A ident saved i) ⊢ ¬A ident saved i := by
  iintro #Hs #HA
  ihave ⟨%P, HNP, HsP⟩ := HA
  iapply HNP
  icases sprop_agree i P (A ident saved i) $$ [] with #⟨_, HP⟩
  · isplit <;> iassumption
  · iapply HP; iassumption

include sprop_agree in
@[rocq_alias savedprop.saved_A]
theorem saved_A (i : ident) : saved i (A ident saved i) ⊢ A ident saved i := by
  iintro #Hs
  iexists A ident saved i
  iframe Hs
  iintro !>
  iapply saved_NA
  · exact sprop_agree
  · iassumption

include consistency bupd_frame_right bupd_intro bupd_trans bupd_mono sprop_alloc_dep sprop_agree in
@[rocq_alias savedprop.contradiction]
theorem contradiction : False := by
  haveI {p : Bool} {P Q : PROP} : ElimModal True p .out false (bupd P) P (bupd Q) (bupd Q) :=
    elim_modal_bupd (io := .out) bupd bupd_mono bupd_trans bupd_frame_right p
  apply consistency
  imod A_alloc bupd ident saved sprop_alloc_dep with ⟨%i, #H⟩
  iapply bupd_intro
  iapply saved_NA _ $$ H
  · exact sprop_agree
  · iapply saved_A
    · exact sprop_agree
    · iassumption

end SavedProp
