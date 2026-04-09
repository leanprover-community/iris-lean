/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Yunsong Yang
-/
module

public import Iris.BI
public import Iris.ProofMode.Classes
public import Iris.Std.TC

@[expose] public section

namespace Iris.ProofMode

open Iris.BI Iris.Std

section BIBasicUpdate

variable {PROP} [BI PROP] [BIUpdate PROP]

instance fromAssumption_bupd p ioP (P Q : PROP)
    [h : FromAssumption p ioP P Q] : FromAssumption p ioP P iprop(|==> Q) where
  from_assumption := h.1.trans BIUpdate.intro

instance fromPure_bupd (a : Bool) (P : PROP) (φ : Prop)
    [h : FromPure a P φ] : FromPure a iprop(|==> P) φ where
  from_pure := h.1.trans BIUpdate.intro

instance intoWand_bupd (p q : Bool) ioP ioQ (R P Q : PROP)
    [h : IntoWand false false R ioP P ioQ Q] :
    IntoWand p q iprop(|==> R) ioP iprop(|==> P) ioQ iprop(|==> Q) where
  into_wand := intuitionisticallyIf_elim.trans <|
    wand_intro <| (sep_mono (BIUpdate.mono h.1) intuitionisticallyIf_elim).trans <|
    bupd_sep.trans <| BIUpdate.mono wand_elim_l

instance intoWand_bupd_persistent (p q : Bool) ioP ioQ (R P Q : PROP)
    [h : IntoWand false q R ioP P ioQ Q] :
    IntoWand p q iprop(|==> R) ioP P ioQ iprop(|==> Q) where
  into_wand := intuitionisticallyIf_elim.trans <|
    wand_intro <| (sep_mono (BIUpdate.mono h.1) .rfl).trans <|
    bupd_frame_r.trans <| BIUpdate.mono wand_elim_l

instance fromSep_bupd (P Q1 Q2 : PROP)
    [h : FromSep P Q1 Q2] : FromSep iprop(|==> P) iprop(|==> Q1) iprop(|==> Q2) where
  from_sep := bupd_sep.trans (BIUpdate.mono h.1)

instance fromOr_bupd (P Q1 Q2 : PROP)
    [h : FromOr P Q1 Q2] : FromOr iprop(|==> P) iprop(|==> Q1) iprop(|==> Q2) where
  from_or := bupd_or.trans (BIUpdate.mono h.1)

instance intoAnd_bupd (P Q1 Q2 : PROP)
    [h : IntoAnd false P Q1 Q2] : IntoAnd false iprop(|==> P) iprop(|==> Q1) iprop(|==> Q2) where
  into_and := (BIUpdate.mono h.1).trans bupd_and

instance fromExists_bupd (P : PROP) (Φ : α → PROP)
    [h : FromExists P Φ] : FromExists iprop(|==> P) (fun a => iprop(|==> Φ a)) where
  from_exists := bupd_exist.trans (BIUpdate.mono h.1)

instance intoForall_bupd (P : PROP) (Φ : α → PROP)
    [h : IntoForall P Φ] : IntoForall iprop(|==> P) (fun a => iprop(|==> Φ a)) where
  into_forall := (BIUpdate.mono h.1).trans bupd_forall

instance isExcept0_bupd (P : PROP)
    [h : IsExcept0 P] : IsExcept0 iprop(|==> P) where
  is_except0 := bupd_except0.trans <| BIUpdate.mono h.1

instance fromModal_bupd (P : PROP) :
    FromModal True modality_id iprop(|==> P) iprop(|==> P) P where
  from_modal := by simp [modality_id]; exact BIUpdate.intro

instance elimModal_bupd p (P Q : PROP) :
    ElimModal True p false iprop(|==> P) P iprop(|==> Q) iprop(|==> Q) where
  elim_modal _ := (sep_mono_l intuitionisticallyIf_elim).trans <|
    bupd_frame_r.trans <| (BIUpdate.mono wand_elim_r).trans BIUpdate.trans

end BIBasicUpdate

section SBIBasicUpdate

variable {PROP} [Sbi PROP] [BIUpdate PROP] [BIBUpdatePlainly PROP]

@[ipm_backtrack]
instance elimModal_bupd_plain_goal p (P Q : PROP) [Plain Q] :
    ElimModal True p false iprop(|==> P) P Q Q where
  elim_modal _ := (sep_mono_l intuitionisticallyIf_elim).trans <|
    bupd_frame_r.trans <| (BIUpdate.mono wand_elim_r).trans bupd_elim

@[ipm_backtrack]
instance elimModal_bupd_plain p (P Q : PROP) [Plain P] :
    ElimModal True p p iprop(|==> P) P Q Q where
  elim_modal _ := (sep_mono_l (intuitionisticallyIf_mono bupd_elim)).trans wand_elim_r

end SBIBasicUpdate

section BIFancyUpdate

variable {PROP} [BI PROP] [BIUpdate PROP] [BIFUpdate PROP] [BIUpdateFUpdate PROP]

instance fromAssumption_fupd E p ioP (P Q : PROP)
    [h : FromAssumption p ioP P iprop(|==> Q)] : FromAssumption p ioP P iprop(|={E}=> Q) where
  from_assumption := h.from_assumption.trans BIUpdateFUpdate.fupd_of_bupd

instance fromPure_fupd E a (P : PROP) (φ : Prop)
    [h : FromPure a P φ] : FromPure a iprop(|={E}=> P) φ where
  from_pure := h.from_pure.trans <| fupd_intro

instance intoWand_fupd E (p q : Bool) ioP ioQ (R P Q : PROP)
    [h : IntoWand false false R ioP P ioQ Q] :
    IntoWand p q iprop(|={E}=> R) ioP iprop(|={E}=> P) ioQ iprop(|={E}=> Q) where
  into_wand := intuitionisticallyIf_elim.trans <|
    wand_intro <| (sep_mono (BIFUpdate.mono h.into_wand) intuitionisticallyIf_elim).trans <|
    fupd_sep.trans <| BIFUpdate.mono wand_elim_l

instance intoWand_fupd_persistent E1 E2 (p q : Bool) ioP ioQ (R P Q : PROP)
    [h : IntoWand false q R ioP P ioQ Q] :
    IntoWand p q iprop(|={E1,E2}=> R) ioP P ioQ iprop(|={E1,E2}=> Q) where
  into_wand := intuitionisticallyIf_elim.trans <|
    wand_intro <| (sep_mono (BIFUpdate.mono h.into_wand) .rfl).trans <|
    fupd_frame_r.trans <| BIFUpdate.mono wand_elim_l

instance fromSep_fupd E (P Q1 Q2 : PROP)
    [h : FromSep P Q1 Q2] : FromSep iprop(|={E}=> P) iprop(|={E}=> Q1) iprop(|={E}=> Q2) where
  from_sep := fupd_sep.trans <| BIFUpdate.mono h.from_sep

instance fromOr_fupd E1 E2 (P Q1 Q2 : PROP)
    [h : FromOr P Q1 Q2] : FromOr iprop(|={E1,E2}=> P) iprop(|={E1,E2}=> Q1) iprop(|={E1,E2}=> Q2) where
  from_or := fupd_or.trans <| BIFUpdate.mono h.from_or

instance intoAnd_fupd E1 E2 (P Q1 Q2 : PROP)
    [h : IntoAnd false P Q1 Q2] : IntoAnd false iprop(|={E1,E2}=> P) iprop(|={E1,E2}=> Q1) iprop(|={E1,E2}=> Q2) where
  into_and := (BIFUpdate.mono h.into_and).trans fupd_and

instance fromExists_fupd E1 E2 (P : PROP) (Φ : α → PROP)
    [h : FromExists P Φ] : FromExists iprop(|={E1,E2}=> P) (fun a => iprop(|={E1,E2}=> Φ a)) where
  from_exists := fupd_exist.trans <| (BIFUpdate.mono h.from_exists)

instance intoForall_fupd E1 E2 (P : PROP) (Φ : α → PROP)
    [h : IntoForall P Φ] : IntoForall iprop(|={E1,E2}=> P) (fun a => iprop(|={E1,E2}=> Φ a)) where
  into_forall := (BIFUpdate.mono h.into_forall).trans fupd_forall

instance isExcept0_fupd E1 E2 (P : PROP) : IsExcept0 iprop(|={E1,E2}=> P) where
  is_except0 := BIFUpdate.except0

instance fromModal_fupd E (P : PROP) :
    FromModal True modality_id iprop(|={E}=> P) iprop(|={E}=> P) P where
  from_modal := by simp [modality_id]; exact fupd_intro

instance (priority := low) fromModal_fupd_wrongMask E1 E2 (P : PROP) :
    FromModal (PMError "Only non-mask-changing update modalities can be introduced directly.
      Use `iapply (fupd_mask_intro ...)` to introduce a mask-changing fancy update.")
      modality_id iprop(|={E1,E2}=> P) iprop(|={E1,E2}=> P) P where
  from_modal h := by cases h

instance elimModal_bupd_fupd p E1 E2 (P Q : PROP) :
    ElimModal True p false iprop(|==> P) P iprop(|={E1,E2}=> Q) iprop(|={E1,E2}=> Q) where
  elim_modal _ := (sep_mono_l intuitionisticallyIf_elim).trans <|
    (sep_mono_l BIUpdateFUpdate.fupd_of_bupd).trans <|
    fupd_frame_r.trans <| (BIFUpdate.mono wand_elim_r).trans BIFUpdate.trans

instance (priority := low) elimModal_fupd_fupd_wrongMask p E0 E1 E2 E3 (P Q : PROP) :
    ElimModal (PMError "Goal and eliminated modality must have the same mask.
      Use `BIFUpdate.subset` to adjust the goal mask before using `imod`.")
      p false iprop(|={E1,E2}=> P) iprop(False) iprop(|={E0,E3}=> Q) iprop(False) where
  elim_modal h := by cases h

instance (priority := high) elimModal_fupd_fupd p E1 E2 E3 (P Q : PROP) :
    ElimModal True p false iprop(|={E1,E2}=> P) P iprop(|={E1,E3}=> Q) iprop(|={E2,E3}=> Q) where
  elim_modal _ := (sep_mono_l intuitionisticallyIf_elim).trans <|
    fupd_frame_r.trans <| (BIFUpdate.mono wand_elim_r).trans BIFUpdate.trans

end BIFancyUpdate

section SBIFancyUpdate

variable {PROP} [Sbi PROP] [BIFUpdate PROP] [BIFUpdatePlainly PROP] [BIAffine PROP]

-- TODO:
-- `fromForall_fupd` needs a derived plain/fupd/forall lemma.
-- `fromForall_stepFupd` additionally needs a step-fupd/forall theorem in `BI/Updates.lean`.
-- instance fromForall_fupd E1 E2 (P : PROP) {α : Type _} (Φ : α → PROP)
--     [hmask : TCOr (E1 = E2) (TCOr (E1 = ⊤) (E2 = ∅))]
--     [h : FromForall P Φ] [∀ a, Plain (Φ a)] :
--     FromForall iprop(|={E1,E2}=> P) (fun a => iprop(|={E1,E2}=> Φ a)) where
--   from_forall := sorry

-- instance fromForall_stepFupd E (P : PROP) (Φ : α → PROP)
--     [h : FromForall P Φ] [∀ a, Plain (Φ a)] :
--     FromForall iprop(|={E}▷=> P) (fun a => iprop(|={E}▷=> Φ a)) where
--   from_forall := sorry

end SBIFancyUpdate
