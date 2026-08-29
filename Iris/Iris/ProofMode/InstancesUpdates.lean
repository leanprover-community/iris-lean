/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Yunsong Yang, Alvin Tang
-/
module

public import Iris.BI
public import Iris.ProofMode.Classes
public import Iris.ProofMode.Instances
public import Iris.Std.TC
public import Iris.ProofMode.Tactics
public import Iris.ProofMode.Display

@[expose] public section

namespace Iris.ProofMode

open Iris.BI Iris.Std BIFUpdate

section BIBasicUpdate

variable {PROP} [BI PROP] [BIUpdate PROP]

@[rocq_alias from_assumption_bupd]
instance fromAssumption_bupd p ioP (P Q : PROP)
    [h : FromAssumption p ioP P Q] : FromAssumption p ioP P iprop(|==> Q) where
  from_assumption := h.1.trans BIUpdate.intro

@[rocq_alias from_pure_bupd]
instance fromPure_bupd (a : Bool) (P : PROP) (φ : Prop)
    [h : FromPure a P io φ] : FromPure a iprop(|==> P) io φ where
  from_pure := h.1.trans BIUpdate.intro

@[rocq_alias into_wand_bupd]
instance intoWand_bupd (p q : Bool) m (R P Q : PROP)
    [h : IntoWand false false R m P Q] :
    IntoWand p q iprop(|==> R) m iprop(|==> P) iprop(|==> Q) where
  into_wand := by
    refine intuitionisticallyIf_elim.trans <| wand_intro ?_
    calc
      _ ⊢ |==> (P -∗ Q) ∗ |==> P := sep_mono (BIUpdate.mono h.into_wand) intuitionisticallyIf_elim
      _ ⊢ |==> ((P -∗ Q) ∗ P) := bupd_sep
      _ ⊢ |==> Q := BIUpdate.mono wand_elim_left

@[rocq_alias into_wand_bupd_args]
instance (priority := low) intoWand_bupd_args (p q : Bool) (s : WandMode.Side) (R P Q : PROP)
    [h : IntoWand p false R (.matching s) P Q] :
    IntoWand p q R (.matching s) iprop(|==> P) iprop(|==> Q) where
  into_wand := wand_intro_left <|
    (sep_mono intuitionisticallyIf_elim h.into_wand).trans bupd_wand_right

@[rocq_alias into_wand_bupd_persistent]
instance intoWand_bupd_persistent (p q : Bool) m (R P Q : PROP)
    [h : IntoWand false q R m P Q] :
    IntoWand p q iprop(|==> R) m P iprop(|==> Q) where
  into_wand := by
    refine intuitionisticallyIf_elim.trans <| wand_intro ?_
    calc
      _ ⊢ |==> (□?q P -∗ Q) ∗ □?q P   := sep_mono_left <| BIUpdate.mono h.1
      _ ⊢ |==> ((□?q P -∗ Q) ∗ □?q P) := bupd_frame_right
      _ ⊢ |==> Q                      := BIUpdate.mono wand_elim_left

@[rocq_alias from_sep_bupd]
instance fromSep_bupd (P Q1 Q2 : PROP)
    [h : FromSep P Q1 Q2] : FromSep iprop(|==> P) iprop(|==> Q1) iprop(|==> Q2) where
  from_sep := bupd_sep.trans (BIUpdate.mono h.1)

@[rocq_alias from_or_bupd]
instance fromOr_bupd (P Q1 Q2 : PROP)
    [h : FromOr P Q1 Q2] : FromOr iprop(|==> P) iprop(|==> Q1) iprop(|==> Q2) where
  from_or := bupd_or.trans (BIUpdate.mono h.1)

@[rocq_alias into_and_bupd]
instance intoAnd_bupd (P Q1 Q2 : PROP)
    [h : IntoAnd false P Q1 Q2] : IntoAnd false iprop(|==> P) iprop(|==> Q1) iprop(|==> Q2) where
  into_and := (BIUpdate.mono h.1).trans bupd_and

@[rocq_alias from_exist_bupd]
instance fromExists_bupd (P : PROP) (Φ : α → PROP)
    [h : FromExists P Φ] : FromExists iprop(|==> P) (fun a => iprop(|==> Φ a)) where
  from_exists := bupd_exist.trans (BIUpdate.mono h.1)

@[rocq_alias into_forall_bupd]
instance intoForall_bupd (P : PROP) (Φ : α → PROP)
    [h : IntoForall P Φ] : IntoForall iprop(|==> P) (fun a => iprop(|==> Φ a)) where
  into_forall := (BIUpdate.mono h.1).trans bupd_forall

@[rocq_alias is_except_0_bupd]
instance isExcept0_bupd (P : PROP)
    [h : IsExcept0 P] : IsExcept0 iprop(|==> P) where
  is_except0 := except0_bupd.trans <| BIUpdate.mono h.1

@[rocq_alias from_modal_bupd]
instance fromModal_bupd io (P : PROP) :
    FromModal io modality_id True iprop(|==> P) iprop(|==> P) P where
  from_modal := by simp [modality_id]; exact BIUpdate.intro

@[rocq_alias elim_modal_bupd]
instance elimModal_bupd p io (P Q : PROP) :
    ElimModal True p io false iprop(|==> P) P iprop(|==> Q) iprop(|==> Q) where
  elim_modal _ := calc
    _ ⊢ |==> P ∗ (P ==∗ Q)   := sep_mono_left intuitionisticallyIf_elim
    _ ⊢ |==> (P ∗ (P ==∗ Q)) := bupd_frame_right
    _ ⊢ |==> |==> Q          := BIUpdate.mono wand_elim_right
    _ ⊢ |==> Q               := BIUpdate.trans

@[rocq_alias add_modal_bupd]
instance addModal_bupd (P Q : PROP) :
    AddModal iprop(|==> P) P iprop(|==> Q) where
  add_modal := bupd_wand_right.trans bupd_trans

end BIBasicUpdate

section SBIBasicUpdate

variable {PROP} [Sbi PROP] [BIUpdate PROP] [BIBUpdateSbi PROP]

@[ipm_backtrack, rocq_alias elim_modal_bupd_plain_goal]
instance elimModal_bupd_plain_goal [BIAffine PROP] p io (P Q : PROP) [Plain Q] :
    ElimModal True p io false iprop(|==> P) P Q Q where
  elim_modal _ := calc
    _ ⊢ |==> P ∗ (P -∗ Q)   := sep_mono_left intuitionisticallyIf_elim
    _ ⊢ |==> (P ∗ (P -∗ Q)) := bupd_frame_right
    _ ⊢ |==> Q              := BIUpdate.mono wand_elim_right
    _ ⊢ Q                   := bupd_elim

@[ipm_backtrack, rocq_alias elim_modal_bupd_plain]
instance elimModal_bupd_plain [BIAffine PROP] p io (P Q : PROP) [Plain P] :
    ElimModal True p io p iprop(|==> P) P Q Q where
  elim_modal _ := (sep_mono_left (intuitionisticallyIf_mono bupd_elim)).trans wand_elim_right

end SBIBasicUpdate

section BIFancyUpdate

variable {PROP} [BI PROP] [BIUpdate PROP] [BIFUpdate PROP] [BIUpdateFUpdate PROP]

@[rocq_alias from_assumption_fupd]
instance fromAssumption_fupd E p ioP (P Q : PROP)
    [h : FromAssumption p ioP P iprop(|==> Q)] : FromAssumption p ioP P iprop(|={E}=> Q) where
  from_assumption := h.from_assumption.trans BIUpdateFUpdate.fupd_of_bupd

@[rocq_alias from_pure_fupd]
instance fromPure_fupd E a (P : PROP) (φ : Prop)
    [h : FromPure a P io φ] : FromPure a iprop(|={E}=> P) io φ where
  from_pure := h.from_pure.trans <| fupd_intro

@[rocq_alias into_wand_fupd]
instance intoWand_fupd E (p q : Bool) m (R P Q : PROP)
    [h : IntoWand false false R m P Q] :
    IntoWand p q iprop(|={E}=> R) m iprop(|={E}=> P) iprop(|={E}=> Q) where
  into_wand := by
    refine intuitionisticallyIf_elim.trans <| wand_intro ?_
    calc
      _ ⊢ (|={E}=> P -∗ Q) ∗ |={E}=> P := sep_mono (mono h.into_wand) intuitionisticallyIf_elim
      _ ⊢ |={E}=> (P -∗ Q) ∗ P         := fupd_sep
      _ ⊢ |={E}=> Q                    := mono wand_elim_left

@[rocq_alias into_wand_fupd_persistent]
instance intoWand_fupd_persistent E1 E2 (p q : Bool) m (R P Q : PROP)
    [h : IntoWand false q R m P Q] :
    IntoWand p q iprop(|={E1,E2}=> R) m P iprop(|={E1,E2}=> Q) where
  into_wand := by
    refine intuitionisticallyIf_elim.trans <| wand_intro ?_
    calc
      _ ⊢ (|={E1, E2}=> □?q P -∗ Q) ∗ □?q P := sep_mono_left <| mono h.into_wand
      _ ⊢ |={E1, E2}=> (□?q P -∗ Q) ∗ □?q P := fupd_frame_right
      _ ⊢ |={E1, E2}=> Q                    := mono wand_elim_left

-- The `set_option` is needed because the masks `E1`/`E2` are not determined by the argument
-- and result slots.
set_option synthInstance.checkSynthOrder false in
@[rocq_alias into_wand_fupd_args]
instance (priority := low) intoWand_fupd_args E1 E2 (p q : Bool) (s : WandMode.Side)
    (R P Q : PROP) [h : IntoWand p false R (.matching s) P Q] :
    IntoWand p q R (.matching s) iprop(|={E1,E2}=> P) iprop(|={E1,E2}=> Q) where
  into_wand := wand_intro_left <|
    (sep_mono intuitionisticallyIf_elim h.into_wand).trans fupd_wand_right

@[rocq_alias from_sep_fupd]
instance fromSep_fupd E (P Q1 Q2 : PROP)
    [h : FromSep P Q1 Q2] : FromSep iprop(|={E}=> P) iprop(|={E}=> Q1) iprop(|={E}=> Q2) where
  from_sep := fupd_sep.trans <| mono h.from_sep

@[rocq_alias from_or_fupd]
instance fromOr_fupd E1 E2 (P Q1 Q2 : PROP)
    [h : FromOr P Q1 Q2] : FromOr iprop(|={E1,E2}=> P) iprop(|={E1,E2}=> Q1) iprop(|={E1,E2}=> Q2) where
  from_or := fupd_or.trans <| mono h.from_or

@[rocq_alias into_and_fupd]
instance intoAnd_fupd E1 E2 (P Q1 Q2 : PROP)
    [h : IntoAnd false P Q1 Q2] : IntoAnd false iprop(|={E1,E2}=> P) iprop(|={E1,E2}=> Q1) iprop(|={E1,E2}=> Q2) where
  into_and := (mono h.into_and).trans fupd_and

@[rocq_alias from_exist_fupd]
instance fromExists_fupd E1 E2 (P : PROP) (Φ : α → PROP)
    [h : FromExists P Φ] : FromExists iprop(|={E1,E2}=> P) (fun a => iprop(|={E1,E2}=> Φ a)) where
  from_exists := fupd_exist.trans <| (mono h.from_exists)

@[rocq_alias into_forall_fupd]
instance intoForall_fupd E1 E2 (P : PROP) (Φ : α → PROP)
    [h : IntoForall P Φ] : IntoForall iprop(|={E1,E2}=> P) (fun a => iprop(|={E1,E2}=> Φ a)) where
  into_forall := (mono h.into_forall).trans fupd_forall

@[rocq_alias is_except_0_fupd]
instance isExcept0_fupd E1 E2 (P : PROP) : IsExcept0 iprop(|={E1,E2}=> P) where
  is_except0 := except0

@[rocq_alias from_modal_fupd]
instance fromModal_fupd E io (P : PROP) :
    FromModal io modality_id True iprop(|={E}=> P) iprop(|={E}=> P) P where
  from_modal := by simp [modality_id]; exact fupd_intro

@[rocq_alias from_modal_fupd_wrong_mask]
instance (priority := low) fromModal_fupd_wrongMask E1 E2 io (P : PROP) :
    FromModal io modality_id (PMError "Only non-mask-changing update modalities can be introduced directly.
      Use `iapply (fupd_mask_intro ...)` to introduce a mask-changing fancy update.")
      iprop(|={E1,E2}=> P) iprop(|={E1,E2}=> P) P where
  from_modal h := by cases h

@[rocq_alias elim_modal_bupd_fupd]
instance elimModal_bupd_fupd p io E1 E2 (P Q : PROP) :
    ElimModal True p io false iprop(|==> P) P iprop(|={E1,E2}=> Q) iprop(|={E1,E2}=> Q) where
  elim_modal _ := calc
    _ ⊢ |==> P ∗ (P ={E1,E2}=∗ Q)       := sep_mono_left intuitionisticallyIf_elim
    _ ⊢ (|={E1}=> P) ∗ (P ={E1,E2}=∗ Q) := sep_mono_left BIUpdateFUpdate.fupd_of_bupd
    _ ⊢ |={E1}=> P ∗ (P ={E1,E2}=∗ Q)   := fupd_frame_right
    _ ⊢ |={E1}=> |={E1,E2}=> Q          := mono wand_elim_right
    _ ⊢ |={E1,E2}=> Q                   := trans

@[rocq_alias elim_modal_fupd_fupd]
instance (priority := high) elimModal_fupd_fupd p io E1 E2 E3 (P Q : PROP) :
    ElimModal True p io false iprop(|={E1,E2}=> P) P iprop(|={E1,E3}=> Q) iprop(|={E2,E3}=> Q) where
  elim_modal _ := calc
    _ ⊢ (|={E1,E2}=> P) ∗ (P ={E2,E3}=∗ Q) := sep_mono_left intuitionisticallyIf_elim
    _ ⊢ |={E1,E2}=> P ∗ (P ={E2,E3}=∗ Q)   := fupd_frame_right
    _ ⊢ |={E1,E2}=> |={E2,E3}=> Q          := mono wand_elim_right
    _ ⊢ |={E1,E3}=> Q                      := trans

@[rocq_alias elim_modal_fupd_fupd_wrong_mask]
instance (priority := low) elimModal_fupd_fupd_wrongMask p io E0 E1 E2 E3 (P Q : PROP) :
    ElimModal (PMError "Goal and eliminated modality must have the same mask.
      Use `BIFUpdate.subset` to adjust the goal mask before using `imod`.")
      p io false iprop(|={E1,E2}=> P) iprop(False) iprop(|={E0,E3}=> Q) iprop(False) where
  elim_modal h := by cases h

@[rocq_alias add_modal_fupd]
instance addModal_fupd E1 E2 (P Q : PROP) :
    AddModal iprop(|={E1}=> P) P iprop(|={E1,E2}=> Q) where
  add_modal := by
    calc
      _ ⊢ (P ={E1, E2}=∗ Q) ∗ (|={E1}=> P)    := sep_comm.mp
      _ ⊢ |={E1}=> ((P -∗ |={E1,E2}=> Q) ∗ P) := fupd_frame_left
      _ ⊢ |={E1}=> (|={E1,E2}=> Q)            := mono wand_elim_left
      _ ⊢ |={E1, E2}=> Q                      := trans

@[rocq_alias elim_acc_bupd]
instance elimAcc_bupd {X} (α β : X → PROP) mγ (Q : PROP) :
    ElimAcc True bupd bupd α β mγ
    iprop(|==> Q)
    iprop(fun x => (|==> β x ∗ (mγ x -∗? |==> Q))) where
  elim_acc := by
    simp only [accessor, BIBase.wandM]
    iintro %_ Hinner >⟨%x, Hα, Hclose⟩
    ispecialize Hinner $$ %x Hα
    cases (mγ x) with simp_all
    | none =>
      icases Hinner with ⟨Hβ, Hfin⟩
      imod Hβ
      ispecialize Hclose $$ Hβ
      imod Hclose
      iexact Hfin
    | some P =>
      icases Hinner with ⟨Hβ, Hfin⟩
      imod Hβ
      imod Hclose $$ Hβ
      iapply Hfin
      iexact Hclose

@[rocq_alias elim_acc_fupd]
instance elimAcc_fupd {X} E1 E2 E (α β : X → PROP) mγ (Q : PROP) :
    ElimAcc True (fupd E1 E2) (fupd E2 E1) α β mγ
    iprop(|={E1,E}=> Q)
    (fun x => iprop(|={E2}=> β x ∗ (mγ x -∗? |={E1,E}=> Q))) where
  elim_acc := by
    simp only [accessor, BIBase.wandM]
    iintro %_ Hinner >⟨%x, Hα, Hclose⟩
    ispecialize Hinner $$ %x Hα
    cases (mγ x) with simp_all
    | none =>
      imod Hinner with ⟨Hβ, Hfin⟩
      ispecialize Hclose $$ Hβ
      imod Hclose
      iexact Hfin
    | some p =>
      imod Hinner with ⟨Hβ, Hfin⟩
      ispecialize Hclose $$ Hβ
      imod Hclose
      iapply Hfin $$ Hclose

end BIFancyUpdate

section SBIFancyUpdate

variable {PROP} [Sbi PROP] [BIFUpdate PROP] [BIFUpdateSbi PROP] [BIAffine PROP]

@[ipm_backtrack, rocq_alias from_forall_fupd]
instance fromForall_fupd E1 E2 (P : PROP) {α : Type _} (Φ : α → PROP)
    [inst : TCSideCondition (E2 ⊆ E1)]
    [h : FromForall P Φ] [∀ a, Plain (Φ a)] :
    FromForall iprop(|={E1,E2}=> P) (fun a => iprop(|={E1,E2}=> Φ a)) where
  from_forall := (fupd_plain_forall inst.sidecondition).mpr.trans (mono h.from_forall)

@[ipm_backtrack, rocq_alias from_forall_step_fupd]
instance fromForall_stepFupd E1 E2 (P : PROP) (Φ : α → PROP)
    [inst : TCSideCondition (E2 ⊆ E1)]
    [h : FromForall P Φ] [∀ a, Plain (Φ a)] :
    FromForall iprop(|={E1}[E2]▷=> P) (fun a => iprop(|={E1}[E2]▷=> Φ a)) where
  from_forall := (step_fupd_plain_forall inst.sidecondition).mpr.trans (step_fupd_mono h.from_forall)

end SBIFancyUpdate
