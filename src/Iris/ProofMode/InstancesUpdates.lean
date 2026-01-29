/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.BI
import Iris.ProofMode.Classes
import Iris.Std.TC

namespace Iris.ProofMode
open Iris.BI Iris.Std

variable {PROP} [BI PROP]

instance fromAssumption_bupd [BIUpdate PROP] p ioP (P Q : PROP)
    [h : FromAssumption p ioP P Q] : FromAssumption p ioP P iprop(|==> Q) where
  from_assumption := h.1.trans BIUpdate.intro

instance fromPure_bupd [BIUpdate PROP] (a : Bool) (P : PROP) (φ : Prop)
    [h : FromPure a P φ] : FromPure a iprop(|==> P) φ where
  from_pure := h.1.trans BIUpdate.intro

instance intoWand_bupd [BIUpdate PROP] (p q : Bool) ioP ioQ (R P Q : PROP)
    [h : IntoWand false false R ioP P ioQ Q] :
    IntoWand p q iprop(|==> R) ioP iprop(|==> P) ioQ iprop(|==> Q) where
  into_wand := intuitionisticallyIf_elim.trans <|
    wand_intro <| (sep_mono (BIUpdate.mono h.1) intuitionisticallyIf_elim).trans <|
    bupd_sep.trans <| BIUpdate.mono wand_elim_l

instance intoWand_bupd_persistent [BIUpdate PROP] (p q : Bool) ioP ioQ (R P Q : PROP)
    [h : IntoWand false q R ioP P ioQ Q] :
    IntoWand p q iprop(|==> R) ioP P ioQ iprop(|==> Q) where
  into_wand := intuitionisticallyIf_elim.trans <|
    wand_intro <| (sep_mono (BIUpdate.mono h.1) .rfl).trans <|
    bupd_frame_r.trans <| BIUpdate.mono wand_elim_l

instance fromSep_bupd [BIUpdate PROP] (P Q1 Q2 : PROP)
    [h : FromSep P Q1 Q2] : FromSep iprop(|==> P) iprop(|==> Q1) iprop(|==> Q2) where
  from_sep := bupd_sep.trans (BIUpdate.mono h.1)

instance fromOr_bupd [BIUpdate PROP] (P Q1 Q2 : PROP)
    [h : FromOr P Q1 Q2] : FromOr iprop(|==> P) iprop(|==> Q1) iprop(|==> Q2) where
  from_or := bupd_or.trans (BIUpdate.mono h.1)

instance intoAnd_bupd [BIUpdate PROP] (P Q1 Q2 : PROP)
    [h : IntoAnd false P Q1 Q2] : IntoAnd false iprop(|==> P) iprop(|==> Q1) iprop(|==> Q2) where
  into_and := (BIUpdate.mono h.1).trans bupd_and

instance fromExists_bupd [BIUpdate PROP] (P : PROP) (Φ : α → PROP)
    [h : FromExists P Φ] : FromExists iprop(|==> P) (fun a => iprop(|==> Φ a)) where
  from_exists := bupd_exist.trans (BIUpdate.mono h.1)

instance intoForall_bupd [BIUpdate PROP] (P : PROP) (Φ : α → PROP)
    [h : IntoForall P Φ] : IntoForall iprop(|==> P) (fun a => iprop(|==> Φ a)) where
  into_forall := (BIUpdate.mono h.1).trans bupd_forall

instance isExcept0_bupd [BIUpdate PROP] (P : PROP)
    [h : IsExcept0 P] : IsExcept0 iprop(|==> P) where
  is_except0 := bupd_except0.trans <| BIUpdate.mono h.1

instance fromModal_bupd [BIUpdate PROP] (P : PROP) :
    FromModal True modality_id iprop(|==> P) iprop(|==> P) P where
  from_modal := by simp [modality_id]; exact BIUpdate.intro
