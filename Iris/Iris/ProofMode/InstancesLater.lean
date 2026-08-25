/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Alvin Tang
-/
module

public import Iris.BI
public import Iris.ProofMode.Classes
public import Iris.ProofMode.ClassesMake
public import Iris.ProofMode.ModalityInstances
public import Iris.ProofMode.NatCancel

@[expose] public section

namespace Iris.ProofMode
open Iris.BI Iris.Std

/-! ### FromAssumption -/

@[rocq_alias from_assumption_later]
instance fromAssumption_later [BI PROP] (p : Bool) (P Q : PROP)
    [h : FromAssumption p ioP P Q] : FromAssumption p ioP P iprop(▷ Q) where
  from_assumption := h.1.trans later_intro

@[rocq_alias from_assumption_laterN]
instance fromAssumption_laterN [BI PROP] n (p : Bool) (P Q : PROP)
    [h : FromAssumption p ioP P Q] : FromAssumption p ioP P iprop(▷^[n] Q) where
  from_assumption := h.1.trans (laterN_intro n)

@[rocq_alias from_assumption_except_0]
instance fromAssumption_except0 [BI PROP] (p : Bool) (P Q : PROP)
    [h : FromAssumption p ioP P Q] : FromAssumption p ioP P iprop(◇ Q) where
  from_assumption := h.1.trans except0_intro

/-
  `fromAssumption_later_laterN` must have a higher priority than fromAssumption_later.
  Rocq does not need this instance since there `▷^[n + 1]` is convertible to `▷ ▷^[n]`
  TODO: This instance is currently quite specific. Should it be generalized?
-/
instance (priority := default + 10) fromAssumption_later_laterN [BI PROP] n (p : Bool) (P Q : PROP)
    [h : FromAssumption p .in iprop(▷^[n] P) Q] :
    FromAssumption p .in iprop(▷^[n + 1] P) iprop(▷ Q) where
  from_assumption := later_intuitionisticallyIf_2.trans (later_mono h.from_assumption)

/-! ### FromPure -/

@[rocq_alias from_pure_later]
instance fromPure_later [BI PROP] (a : Bool) (P : PROP) (φ : Prop)
    [h : FromPure a P io φ] : FromPure a iprop(▷ P) io φ where
  from_pure := h.1.trans later_intro

@[rocq_alias from_pure_laterN]
instance fromPure_laterN [BI PROP] (a : Bool) (n : Nat) (P : PROP) (φ : Prop)
    [h : FromPure a P io φ] : FromPure a iprop(▷^[n] P) io φ where
  from_pure := h.1.trans (laterN_intro n)

@[rocq_alias from_pure_except_0]
instance fromPure_except0 [BI PROP] (a : Bool) (P : PROP) (φ : Prop)
    [h : FromPure a P io φ] : FromPure a iprop(◇ P) io φ where
  from_pure := h.1.trans except0_intro

/-! ### IntoWand -/

@[rocq_alias into_wand_later]
instance intoWand_later [BI PROP] (p q : Bool) (R P Q : PROP)
    [h : IntoWand p q R m P Q] : IntoWand p q iprop(▷ R) m iprop(▷ P) iprop(▷ Q) where
  into_wand := calc
    _ ⊢ ▷ □?p R         := later_intuitionisticallyIf_2
    _ ⊢ ▷ (□?q P -∗ Q)  := later_mono h.into_wand
    _ ⊢ ▷ □?q P -∗ ▷ Q := later_wand
    _ ⊢ □?q ▷ P -∗ ▷ Q := wand_mono_left later_intuitionisticallyIf_2

@[rocq_alias into_wand_later_args]
instance (priority := low) intoWand_later_args [BI PROP] (p q : Bool) (s : WandMode.Side)
    (R P Q : PROP) [h : IntoWand p q R (.matching s) P Q] :
    IntoWand p q R (.matching s) iprop(▷ P) iprop(▷ Q) where
  into_wand := calc
    _ ⊢ □?p ▷ R         := intuitionisticallyIf_mono later_intro
    _ ⊢ ▷ □?p R         := later_intuitionisticallyIf_2
    _ ⊢ ▷ (□?q P -∗ Q)  := later_mono h.into_wand
    _ ⊢ ▷ □?q P -∗ ▷ Q := later_wand
    _ ⊢ □?q ▷ P -∗ ▷ Q := wand_mono_left later_intuitionisticallyIf_2

@[rocq_alias into_wand_laterN]
instance intoWand_laterN [BI PROP] (n : Nat) (p q : Bool) (R P Q : PROP)
    [h : IntoWand p q R m P Q] :
    IntoWand p q iprop(▷^[n] R) m iprop(▷^[n] P) iprop(▷^[n] Q) where
  into_wand := calc
    _ ⊢ ▷^[n]□?p R            := laterN_intuitionisticallyIf n
    _ ⊢ ▷^[n](□?q P -∗ Q)     := laterN_mono n h.into_wand
    _ ⊢ ▷^[n]□?q P -∗ ▷^[n]Q := laterN_wand n
    _ ⊢ □?q ▷^[n]P -∗ ▷^[n]Q := wand_mono_left <| laterN_intuitionisticallyIf n

set_option synthInstance.checkSynthOrder false in
@[rocq_alias into_wand_laterN_args]
instance (priority := low) intoWand_laterN_args [BI PROP] (n : Nat) (p q : Bool)
    (s : WandMode.Side) (R P Q : PROP) [h : IntoWand p q R (.matching s) P Q] :
    IntoWand p q R (.matching s) iprop(▷^[n] P) iprop(▷^[n] Q) where
  into_wand := calc
    _ ⊢ □?p ▷^[n]R            := intuitionisticallyIf_mono <| laterN_intro n
    _ ⊢ ▷^[n]□?p R            := laterN_intuitionisticallyIf n
    _ ⊢ ▷^[n](□?q P -∗ Q)     := laterN_mono n h.into_wand
    _ ⊢ ▷^[n]□?q P -∗ ▷^[n]Q := laterN_wand n
    _ ⊢ □?q ▷^[n]P -∗ ▷^[n]Q := wand_mono_left <| laterN_intuitionisticallyIf n

/-! ### FromAnd -/

@[rocq_alias from_and_later]
instance fromAnd_later [BI PROP] (P Q1 Q2 : PROP)
    [h : FromAnd P Q1 Q2] : FromAnd iprop(▷ P) iprop(▷ Q1) iprop(▷ Q2) where
  from_and := later_and.2.trans (later_mono h.1)

@[rocq_alias from_and_laterN]
instance fromAnd_laterN [BI PROP] (n : Nat) (P Q1 Q2 : PROP)
    [h : FromAnd P Q1 Q2] : FromAnd iprop(▷^[n] P) iprop(▷^[n] Q1) iprop(▷^[n] Q2) where
  from_and := (laterN_and n).2.trans (laterN_mono n h.1)

@[rocq_alias from_and_except_0]
instance fromAnd_except0 [BI PROP] (P Q1 Q2 : PROP)
    [h : FromAnd P Q1 Q2] : FromAnd iprop(◇ P) iprop(◇ Q1) iprop(◇ Q2) where
  from_and := except0_and.2.trans (except0_mono h.1)

/-! ### FromSep -/

@[rocq_alias from_sep_later]
instance fromSep_later [BI PROP] (P Q1 Q2 : PROP)
    [h : FromSep P Q1 Q2] : FromSep iprop(▷ P) iprop(▷ Q1) iprop(▷ Q2) where
  from_sep := later_sep.2.trans (later_mono h.1)

@[rocq_alias from_sep_laterN]
instance fromSep_laterN [BI PROP] (n : Nat) (P Q1 Q2 : PROP)
    [h : FromSep P Q1 Q2] : FromSep iprop(▷^[n] P) iprop(▷^[n] Q1) iprop(▷^[n] Q2) where
  from_sep := (laterN_sep n).2.trans (laterN_mono n h.1)

@[rocq_alias from_sep_except_0]
instance fromSep_except0 [BI PROP] (P Q1 Q2 : PROP)
    [h : FromSep P Q1 Q2] : FromSep iprop(◇ P) iprop(◇ Q1) iprop(◇ Q2) where
  from_sep := except0_sep.2.trans (except0_mono h.1)

/-! ### IntoAnd -/

@[rocq_alias into_and_later]
instance intoAnd_later [BI PROP] (p : Bool) (P Q1 Q2 : PROP)
    [h : IntoAnd p P Q1 Q2] : IntoAnd p iprop(▷ P) iprop(▷ Q1) iprop(▷ Q2) where
  into_and := intuitionisticallyIf_intro_intuitionisticallyIf <| calc
    _ ⊢ ▷ □?p P      := later_intuitionisticallyIf_2
    _ ⊢ ▷ (Q1 ∧ Q2)  := later_mono <| h.into_and.trans intuitionisticallyIf_elim
    _ ⊢ ▷ Q1 ∧ ▷ Q2 := later_and.mp

@[rocq_alias into_and_laterN]
instance intoAnd_laterN [BI PROP] (n : Nat) (p : Bool) (P Q1 Q2 : PROP)
    [h : IntoAnd p P Q1 Q2] : IntoAnd p iprop(▷^[n] P) iprop(▷^[n] Q1) iprop(▷^[n] Q2) where
  into_and := intuitionisticallyIf_intro_intuitionisticallyIf <| calc
    _ ⊢ ▷^[n]□?p P         := laterN_intuitionisticallyIf n
    _ ⊢ ▷^[n](Q1 ∧ Q2)     := laterN_mono n <| h.into_and.trans intuitionisticallyIf_elim
    _ ⊢ ▷^[n]Q1 ∧ ▷^[n]Q2 := (laterN_and n).mp

@[rocq_alias into_and_except_0]
instance intoAnd_except0 [BI PROP] (p : Bool) (P Q1 Q2 : PROP)
    [h : IntoAnd p P Q1 Q2] : IntoAnd p iprop(◇ P) iprop(◇ Q1) iprop(◇ Q2) where
  into_and := intuitionisticallyIf_intro_intuitionisticallyIf <| calc
    _ ⊢ ◇ □?p P      := except0_intuitionisticallyIf
    _ ⊢ ◇ (Q1 ∧ Q2)  := except0_mono <| h.into_and.trans intuitionisticallyIf_elim
    _ ⊢ ◇ Q1 ∧ ◇ Q2 := except0_and.mp

/-! ### IntoSep -/

@[rocq_alias into_sep_later]
instance intoSep_later [BI PROP] (P Q1 Q2 : PROP)
    [h : IntoSep P Q1 Q2] : IntoSep iprop(▷ P) iprop(▷ Q1) iprop(▷ Q2) where
  into_sep := (later_mono h.1).trans later_sep.1

@[rocq_alias into_sep_laterN]
instance intoSep_laterN [BI PROP] (n : Nat) (P Q1 Q2 : PROP)
    [h : IntoSep P Q1 Q2] : IntoSep iprop(▷^[n] P) iprop(▷^[n] Q1) iprop(▷^[n] Q2) where
  into_sep := (laterN_mono n h.1).trans (laterN_sep n).1

@[rocq_alias into_sep_except_0]
instance intoSep_except0 [BI PROP] (P Q1 Q2 : PROP)
    [h : IntoSep P Q1 Q2] : IntoSep iprop(◇ P) iprop(◇ Q1) iprop(◇ Q2) where
  into_sep := (except0_mono h.1).trans except0_sep.1

/- FIXME: This instance is overly specific, generalize it. -/
@[rocq_alias into_sep_affinely_later]
instance intoSep_affinely_later [BI PROP] [Timeless (emp : PROP)]
    (P Q1 Q2 : PROP) [inst : IntoSep P Q1 Q2] [Affine Q1] [Affine Q2] :
    IntoSep iprop(<affine> ▷ P) iprop(<affine> ▷ Q1) iprop(<affine> ▷ Q2) where
  into_sep := by
    have step (Q : PROP) [Affine Q] : iprop(▷ Q) ⊢ iprop(◇ <affine> ▷ Q) :=
      (later_mono (affine_affinely Q).mpr).trans later_affinely_mp
    calc
      _ ⊢ <affine> ▷ (Q1 ∗ Q2)    := affinely_mono <| later_mono inst.into_sep
      _ ⊢ <affine> (▷ Q1 ∗ ▷ Q2) := affinely_mono later_sep.mp
      _ ⊢ <affine> (◇ <affine> ▷ Q1 ∗ ◇ <affine> ▷ Q2) :=
          affinely_mono <| sep_mono (step Q1) (step Q2)
      _ ⊢ <affine> ◇ (<affine> ▷ Q1 ∗ <affine> ▷ Q2) := affinely_mono except0_sep.mpr
      _ ⊢ <affine> ▷ False ∨ <affine> (<affine> ▷ Q1 ∗ <affine> ▷ Q2) := affinely_or.mp
      _ ⊢ <affine> ▷ Q1 ∗ <affine> ▷ Q2 := or_elim ?_ affinely_elim
    calc iprop(<affine> ▷ False)
      _ ⊢ <affine> ▷ False ∧ <affine> ▷ False := and_intro .rfl .rfl
      _ ⊢ <affine> ▷ False ∗ <affine> ▷ False := persistent_and_sep_mp
      _ ⊢ <affine> ▷ Q1 ∗ <affine> ▷ Q2       :=
          sep_mono (affinely_mono <| later_mono false_elim) (affinely_mono <| later_mono false_elim)

/-! ### FromOr -/

@[rocq_alias from_or_later]
instance fromOr_later [BI PROP] (P Q1 Q2 : PROP)
    [h : FromOr P Q1 Q2] : FromOr iprop(▷ P) iprop(▷ Q1) iprop(▷ Q2) where
  from_or := later_or.2.trans (later_mono h.1)

@[rocq_alias from_or_laterN]
instance fromOr_laterN [BI PROP] (n : Nat) (P Q1 Q2 : PROP)
    [h : FromOr P Q1 Q2] : FromOr iprop(▷^[n] P) iprop(▷^[n] Q1) iprop(▷^[n] Q2) where
  from_or := (laterN_or n).2.trans (laterN_mono n h.1)

@[rocq_alias from_or_except_0]
instance fromOr_except0 [BI PROP] (P Q1 Q2 : PROP)
    [h : FromOr P Q1 Q2] : FromOr iprop(◇ P) iprop(◇ Q1) iprop(◇ Q2) where
  from_or := except0_or.2.trans (except0_mono h.1)

/-! ### IntoOr -/

@[rocq_alias into_or_later]
instance intoOr_later [BI PROP] (P Q1 Q2 : PROP)
    [h : IntoOr P Q1 Q2] : IntoOr iprop(▷ P) iprop(▷ Q1) iprop(▷ Q2) where
  into_or := (later_mono h.1).trans later_or.1

@[rocq_alias into_or_laterN]
instance intoOr_laterN [BI PROP] (n : Nat) (P Q1 Q2 : PROP)
    [h : IntoOr P Q1 Q2] : IntoOr iprop(▷^[n] P) iprop(▷^[n] Q1) iprop(▷^[n] Q2) where
  into_or := (laterN_mono n h.1).trans (laterN_or n).1

@[rocq_alias into_or_except_0]
instance intoOr_except0 [BI PROP] (P Q1 Q2 : PROP)
    [h : IntoOr P Q1 Q2] : IntoOr iprop(◇ P) iprop(◇ Q1) iprop(◇ Q2) where
  into_or := (except0_mono h.1).trans except0_or.1

/-! ### FromExists -/

@[rocq_alias from_exist_later]
instance fromExists_later [BI PROP] (P : PROP) (Φ : α → PROP)
    [h : FromExists P Φ] : FromExists iprop(▷ P) (fun a => iprop(▷ Φ a)) where
  from_exists := (exists_elim fun x => (later_mono (exists_intro x))).trans (later_mono h.1)

@[rocq_alias from_exist_laterN]
instance fromExists_laterN [BI PROP] (n : Nat) (P : PROP) (Φ : α → PROP)
    [h : FromExists P Φ] : FromExists iprop(▷^[n] P) (fun a => iprop(▷^[n] Φ a)) where
  from_exists := (exists_elim fun x => (laterN_mono n (exists_intro x))).trans (laterN_mono n h.1)

@[rocq_alias from_exist_except_0]
instance fromExists_except0 [BI PROP] (P : PROP) (Φ : α → PROP)
    [h : FromExists P Φ] : FromExists iprop(◇ P) (fun a => iprop(◇ Φ a)) where
  from_exists := except0_exists_mpr.trans (except0_mono h.1)

/-! ### IntoExists -/

@[rocq_alias into_exist_later]
instance intoExists_later [BI PROP] [Inhabited α] (P : PROP) (Φ : α → PROP)
    [h : IntoExists P Φ] : IntoExists iprop(▷ P) (fun a => iprop(▷ Φ a)) where
  into_exists := (later_mono h.1).trans later_exists.2

@[rocq_alias into_exist_laterN]
instance intoExists_laterN [BI PROP] [Inhabited α] (n : Nat) (P : PROP) (Φ : α → PROP)
    [h : IntoExists P Φ] : IntoExists iprop(▷^[n] P) (fun a => iprop(▷^[n] Φ a)) where
  into_exists := (laterN_mono n h.1).trans (laterN_exists n).1

@[rocq_alias into_exist_except_0]
instance intoExists_except0 [BI PROP] [Inhabited α] (P : PROP) (Φ : α → PROP)
    [h : IntoExists P Φ] : IntoExists iprop(◇ P) (fun a => iprop(◇ Φ a)) where
  into_exists := (except0_mono h.1).trans (except0_exists.1)

/-! ### IntoForall -/

@[rocq_alias into_forall_later]
instance intoForall_later [BI PROP] (P : PROP) (Φ : α → PROP)
    [h : IntoForall P Φ] : IntoForall iprop(▷ P) (fun a => iprop(▷ Φ a)) where
  into_forall := (later_mono h.1).trans later_forall.1

@[rocq_alias into_forall_laterN]
instance intoForall_laterN [BI PROP] (n : Nat) (P : PROP) (Φ : α → PROP)
    [h : IntoForall P Φ] : IntoForall iprop(▷^[n] P) (fun a => iprop(▷^[n] Φ a)) where
  into_forall := (laterN_mono n h.1).trans (laterN_forall n).1

@[rocq_alias into_forall_except_0]
instance intoForall_except0 [BI PROP] (P : PROP) (Φ : α → PROP)
    [h : IntoForall P Φ] : IntoForall iprop(◇ P) (fun a => iprop(◇ Φ a)) where
  into_forall := (except0_mono h.1).trans except0_forall.1

/-! ### FromForall -/

@[rocq_alias from_forall_later]
instance fromForall_later [BI PROP] (P : PROP) (Φ : α → PROP)
    [h : FromForall P Φ] : FromForall iprop(▷ P) (fun a => iprop(▷ Φ a)) where
  from_forall := later_forall.2.trans (later_mono h.1)

@[rocq_alias from_forall_laterN]
instance fromForall_laterN [BI PROP] (n : Nat) (P : PROP) (Φ : α → PROP)
    [h : FromForall P Φ] : FromForall iprop(▷^[n] P) (fun a => iprop(▷^[n] Φ a)) where
  from_forall := (laterN_forall n).2.trans (laterN_mono n h.1)

@[rocq_alias from_forall_except_0]
instance fromForall_except0 [BI PROP] (P : PROP) (Φ : α → PROP)
    [h : FromForall P Φ] : FromForall iprop(◇ P) (fun a => iprop(◇ Φ a)) where
  from_forall := except0_forall.2.trans (except0_mono h.1)

/-! ### IsExcept0 -/

@[rocq_alias is_except_0_except_0]
instance isExcept0_except0 [BI PROP] (P : PROP) : IsExcept0 iprop(◇ P) where
  is_except0 := (except0_idem.1)

@[rocq_alias is_except_0_later]
instance isExcept0_later [BI PROP] (P : PROP) : IsExcept0 iprop(▷ P) where
  is_except0 := except0_later

/-! ### FromModal -/

@[rocq_alias from_modal_later]
instance fromModal_later [BI PROP] io (P : PROP) :
  FromModal io (modality_laterN 1) True iprop(▷^[1] P) iprop(▷ P) P where
  from_modal _ := .rfl

@[rocq_alias from_modal_laterN]
instance fromModal_laterN [BI PROP] io (P : PROP) n :
  FromModal io (modality_laterN n) True iprop(▷^[n] P) iprop(▷^[n] P) P where
  from_modal _ := .rfl

@[rocq_alias from_modal_except_0]
instance fromModal_except0 [BI PROP] io (P : PROP) :
  FromModal io modality_id True iprop(◇ P) iprop(◇ P) P where
  from_modal _ := except0_intro

/-! ### IntoExcept0 -/

@[rocq_alias into_except_0_except_0]
instance intoExcept0_except0 [BI PROP] (P : PROP) :
    IntoExcept0 iprop(◇ P) P where
  into_except0 := .rfl

@[ipm_backtrack, rocq_alias into_except_0_later]
instance intoExcept0_later [BI PROP] (P : PROP) [Timeless P] :
    IntoExcept0 iprop(▷ P) P where
  into_except0 := Timeless.timeless

@[ipm_backtrack, rocq_alias into_except_0_later_if]
instance intoExcept0_laterIf [BI PROP] p (P : PROP) [Timeless P] :
    IntoExcept0 iprop(▷?p P) P where
  into_except0 := match p with
                  | true => Timeless.timeless (P := P)
                  | false => except0_intro

@[rocq_alias into_except_0_affinely]
instance intoExcept0_affinely [BI PROP] (P Q : PROP)
    [h : IntoExcept0 P Q] : IntoExcept0 iprop(<affine> P) iprop(<affine> Q) where
  into_except0 := (affinely_mono h.1).trans except0_affinely

@[rocq_alias into_except_0_intuitionistically]
instance intoExcept0_intuitionistically [BI PROP] (P Q : PROP)
    [h : IntoExcept0 P Q] : IntoExcept0 iprop(□ P) iprop(□ Q) where
  into_except0 := (intuitionistically_mono h.1).trans except0_intuitionistically

@[rocq_alias into_except_0_absorbingly]
instance intoExcept0_absorbingly [BI PROP] (P Q : PROP)
    [h : IntoExcept0 P Q] : IntoExcept0 iprop(<absorb> P) iprop(<absorb> Q) where
  into_except0 := (absorbingly_mono h.1).trans except0_absorbingly.2

@[rocq_alias into_except_0_persistently]
instance intoExcept0_persistently [BI PROP] (P Q : PROP)
    [h : IntoExcept0 P Q] : IntoExcept0 iprop(<pers> P) iprop(<pers> Q) where
  into_except0 := (persistently_mono h.1).trans except0_persistently.2

/-! ### ElimModal -/

@[ipm_backtrack, rocq_alias elim_modal_timeless]
instance (priority := default - 10) elimModal_timeless [BI PROP] p io
    (P P' Q : PROP) [inst : IntoExcept0 P P'] [IsExcept0 Q] :
    ElimModal True p io p P P' Q Q where
  elim_modal _ := calc
    _ ⊢ ◇ □?p P' ∗ (□?p P' -∗ Q)    := sep_mono_left <|
        (intuitionisticallyIf_mono inst.into_except0).trans except0_intuitionisticallyIf
    _ ⊢ ◇ □?p P' ∗ ◇ (□?p P' -∗ Q) := sep_mono_right except0_intro
    _ ⊢ ◇ (□?p P' ∗ (□?p P' -∗ Q))  := except0_sep.mpr
    _ ⊢ ◇ Q                         := except0_mono wand_elim_right
    _ ⊢ Q                            := is_except0

/-! ### AddModal -/

@[ipm_backtrack, rocq_alias add_modal_later_except_0]
instance (priority := default + 10) addModal_later_except_0 [BI PROP]
    (P Q : PROP) [h : Timeless P] :
    AddModal iprop(▷ P) P iprop(◇ Q) where
  add_modal := calc
    _ ⊢ ◇ P ∗ (P -∗ ◇ Q)   := sep_mono_left h.timeless
    _ ⊢ ◇ (P ∗ (P -∗ ◇ Q)) := except0_frame_right
    _ ⊢ ◇ (◇ Q)            := except0_mono wand_elim_right
    _ ⊢ ◇ Q                 := except0_idem.mp

@[ipm_backtrack, rocq_alias add_modal_later]
instance (priority := default + 10) addModal_later [BI PROP] (P Q : PROP) [h : Timeless P] :
    AddModal iprop(▷ P) P iprop(▷ Q) where
  add_modal := calc
    _ ⊢ ◇ P ∗ (P -∗ ▷ Q)   := sep_mono_left h.timeless
    _ ⊢ ◇ (P ∗ (P -∗ ▷ Q)) := except0_frame_right
    _ ⊢ ◇ (▷ Q)            := except0_mono wand_elim_right
    _ ⊢ ▷ Q                 := except0_later

@[rocq_alias add_modal_except_0]
instance addModal_except_0 [BI PROP] (P Q : PROP) :
    AddModal iprop(◇ P) P iprop(◇ Q) where
  add_modal :=
    calc
    _ ⊢ ◇ (P ∗ (P -∗ ◇ Q)) := except0_frame_right
    _ ⊢ ◇ (◇ Q)            := except0_mono wand_elim_right
    _ ⊢ ◇ Q                 := except0_idem.mp

@[rocq_alias add_modal_except_0_later]
instance addModal_except_0_later [BI PROP] (P Q : PROP) :
    AddModal iprop(◇ P) P iprop(▷ Q) where
  add_modal := calc
    _ ⊢ ◇ (P ∗ (P -∗ ▷ Q)) := except0_frame_right
    _ ⊢ ◇ (▷ Q)            := except0_mono wand_elim_right
    _ ⊢ ▷ Q                 := except0_later

/-! ### IntoLaterN -/

@[rocq_alias into_laterN_0, rocq_alias maybe_into_laterN_default_0]
instance (priority := high) intoLaterN_0 [BI PROP] progress only_head (P : PROP) :
    IntoLaterN progress only_head 0 P P where
  into_laterN := laterN_intro 0

-- the identity: only when no progress is required
@[rocq_alias maybe_into_laterN_default]
instance (priority := low) intoLaterN_default [BI PROP] only_head n (P : PROP) :
    IntoLaterN (progress := false) only_head n P P where
  into_laterN := laterN_intro n

@[ipm_backtrack, rocq_alias into_laterN_later]
instance (priority := default - 200) intoLaterN_later [BI PROP] stuck only_head n n' m' (P Q lQ : PROP)
    [h1 : NatCancel n 1 n' m' stuck]
    [h2 : IntoLaterN stuck only_head n' P Q]
    [h3 : MakeLaterN m' Q lQ] : IntoLaterN progress only_head n iprop(▷ P) lQ where
  into_laterN := calc
    _ ⊢ ▷▷^[n']Q      := later_mono h2.into_laterN
    _ ⊢ ▷^[n' + 1]Q    := (later_laterN _).mpr
    _ ⊢ ▷^[n] ▷^[m']Q := by rw [h1.1]; exact (laterN_add _ _).mp
    _ ⊢ ▷^[n]lQ        := laterN_mono _ h3.make_laterN.mp

@[ipm_backtrack, rocq_alias into_laterN_laterN]
instance (priority := default - 100) intoLaterN_laterN [BI PROP] progress stuck only_head n m n' m' (P Q lQ : PROP)
    [h1 : NatCancel n m n' m' stuck]
    [h2 : IntoLaterN stuck only_head n' P Q]
    [h3 : MakeLaterN m' Q lQ] : IntoLaterN progress only_head n iprop(▷^[m] P) lQ where
  into_laterN := calc
    _ ⊢ ▷^[m] ▷^[n']Q := laterN_mono _ h2.into_laterN
    _ ⊢ ▷^[m + n']Q    := (laterN_add _ _).mpr
    _ ⊢ ▷^[n] ▷^[m']Q := by rw [Nat.add_comm, h1.nat_cancel]; exact (laterN_add _ _).mp
    _ ⊢ ▷^[n]lQ        := laterN_mono _ h3.make_laterN.mp

@[ipm_backtrack, rocq_alias into_laterN_laterN_bool]
instance (priority := default - 300) intoLaterN_laterN_bool [BI PROP] progress stuck only_head n (p : Bool) n' m' (P Q lQ : PROP)
    [h1 : NatCancel n 1 n' m' stuck]
    [h2 : IntoLaterN stuck only_head n' P Q]
    [h3 : MakeLaterN m' Q lQ] : IntoLaterN progress only_head n iprop(▷?p P) lQ where
  into_laterN := calc
    _ ⊢ ▷ P            := by cases p; exact later_intro; exact BIBase.Entails.rfl
    _ ⊢ ▷ ▷^[n']Q     := later_mono h2.into_laterN
    _ ⊢ ▷^[n' + 1]Q    := (later_laterN _).mpr
    _ ⊢ ▷^[n] ▷^[m']Q := h1.nat_cancel.symm ▸ (laterN_add _ _).mp
    _ ⊢ ▷^[n]lQ        := laterN_mono _ h3.make_laterN.mp

@[ipm_backtrack, rocq_alias into_laterN_and_l]
instance (priority := default - 10) intoLaterN_and_left [BI PROP]
    progress n (P1 P2 Q1 Q2 : PROP)
    [h1 : IntoLaterN (progress := true) (only_head := false) n P1 Q1]
    [h2 : IntoLaterN (progress := false) (only_head := false) n P2 Q2] :
    IntoLaterN progress (only_head := false) n iprop(P1 ∧ P2) iprop(Q1 ∧ Q2) where
  into_laterN := (and_mono h1.1 h2.1).trans (laterN_and n).2

@[ipm_backtrack, rocq_alias into_laterN_and_r]
instance (priority := default - 11) intoLaterN_and_right [BI PROP]
    progress n (P P2 Q2 : PROP)
    [h : IntoLaterN (progress := true) (only_head := false) n P2 Q2] :
    IntoLaterN progress (only_head := false) n iprop(P ∧ P2) iprop(P ∧ Q2) where
  into_laterN := (and_mono (laterN_intro n) h.1).trans (laterN_and n).2

@[ipm_backtrack, rocq_alias into_laterN_forall]
instance intoLaterN_forall [BI PROP] {α} n (Φ Ψ : α → PROP) progress
    [h : ∀ x, IntoLaterN (progress := true) (only_head := false) n (Φ x) (Ψ x)] :
    IntoLaterN progress (only_head := false) n iprop(∀ x, Φ x) iprop(∀ x, Ψ x) where
  into_laterN := (forall_mono fun x => (h x).1).trans (laterN_forall n).2

@[ipm_backtrack, rocq_alias into_laterN_exist]
instance intoLaterN_exists [BI PROP] {α} n (Φ Ψ : α → PROP) progress
    [h : ∀ x, IntoLaterN (progress := true) (only_head := false) n (Φ x) (Ψ x)] :
    IntoLaterN progress (only_head := false) n iprop(∃ x, Φ x) iprop(∃ x, Ψ x) where
  into_laterN := (exists_mono fun x => (h x).1).trans (laterN_exists_mpr n)

@[ipm_backtrack, rocq_alias into_laterN_or_l]
instance (priority := default - 10) intoLaterN_or_left [BI PROP]
    progress n (P1 P2 Q1 Q2 : PROP)
    [h1 : IntoLaterN (progress := true) (only_head := false) n P1 Q1]
    [h2 : IntoLaterN (progress := false) (only_head := false) n P2 Q2] :
    IntoLaterN progress (only_head := false) n iprop(P1 ∨ P2) iprop(Q1 ∨ Q2) where
  into_laterN := (or_mono h1.1 h2.1).trans (laterN_or n).2

@[ipm_backtrack, rocq_alias into_laterN_or_r]
instance (priority := default - 11) intoLaterN_or_right [BI PROP]
    progress n (P P2 Q2 : PROP)
    [h : IntoLaterN (progress := true) (only_head := false) n P2 Q2] :
    IntoLaterN progress (only_head := false) n iprop(P ∨ P2) iprop(P ∨ Q2) where
  into_laterN := (or_mono (laterN_intro n) h.1).trans (laterN_or n).2

@[ipm_backtrack, rocq_alias into_later_affinely]
instance intoLaterN_affinely [BI PROP] n (P Q : PROP) progress
    [h : IntoLaterN (progress := true) (only_head := false) n P Q] :
    IntoLaterN progress (only_head := false) n iprop(<affine> P) iprop(<affine> Q) where
  into_laterN := (affinely_mono h.1).trans (laterN_affinely n)

@[ipm_backtrack, rocq_alias into_later_intuitionistically]
instance intoLaterN_intuitionistically [BI PROP] n (P Q : PROP)
    [h : IntoLaterN (progress := true) (only_head := false) n P Q] :
    IntoLaterN progress (only_head := false) n iprop(□ P) iprop(□ Q) where
  into_laterN := (intuitionistically_mono h.1).trans (laterN_intuitionistically n)

@[ipm_backtrack, rocq_alias into_later_absorbingly]
instance intoLaterN_absorbingly [BI PROP] n (P Q : PROP) progress
    [h : IntoLaterN (progress := true) (only_head := false) n P Q] :
    IntoLaterN progress (only_head := false) n iprop(<absorb> P) iprop(<absorb> Q) where
  into_laterN := (absorbingly_mono h.1).trans (laterN_absorbingly n).2

@[ipm_backtrack, rocq_alias into_later_persistently]
instance intoLaterN_persistently [BI PROP] n (P Q : PROP) progress
    [h : IntoLaterN (progress := true) (only_head := false) n P Q] :
    IntoLaterN progress (only_head := false) n iprop(<pers> P) iprop(<pers> Q) where
  into_laterN := (persistently_mono h.1).trans (laterN_persistently n).2

@[ipm_backtrack, rocq_alias into_laterN_sep_l]
instance (priority := default - 10) intoLaterN_sep_left [BI PROP]
    n (P1 P2 Q1 Q2 : PROP) progress
    [h1 : IntoLaterN (progress := true) (only_head := false) n P1 Q1]
    [h2 : IntoLaterN (progress := false) (only_head := false) n P2 Q2] :
    IntoLaterN progress (only_head := false) n iprop(P1 ∗ P2) iprop(Q1 ∗ Q2) where
  into_laterN := (sep_mono h1.1 h2.1).trans (laterN_sep n).2

@[ipm_backtrack, rocq_alias into_laterN_sep_r]
instance (priority := default - 11) intoLaterN_sep_right [BI PROP]
    n (P P2 Q2 : PROP) progress
    [h : IntoLaterN (progress := true) (only_head := false) n P2 Q2] :
    IntoLaterN progress (only_head := false) n iprop(P ∗ P2) iprop(P ∗ Q2) where
  into_laterN := (sep_mono (laterN_intro n) h.into_laterN).trans (laterN_sep n).mpr

/-- IntoLaterN, big operators -/

@[ipm_backtrack, rocq_alias into_laterN_big_sepL]
instance intoLaterN_bigSepL [BI PROP] {A} progress n
    (Φ Ψ : Nat → A → PROP) (l : List A)
    [h : ∀ k x, IntoLaterN (progress := true) (only_head := false) n (Φ k x) (Ψ k x)] :
    IntoLaterN progress (only_head := false) n
      iprop([∗list] k ↦ x ∈ l, Φ k x) iprop([∗list] k ↦ x ∈ l, Ψ k x) where
  into_laterN :=
    (BigSepL.bigSepL_mono_of_forall fun {k x} => (h k x).into_laterN).trans
    BigSepL.bigSepL_laterN_2

@[ipm_backtrack, rocq_alias into_laterN_big_sepL2]
instance intoLaterN_bigSepL2 [BI PROP] {A B} progress n
    (Φ Ψ : Nat → A → B → PROP) (l1 : List A) (l2 : List B)
    [h : ∀ k x1 x2,
      IntoLaterN (progress := true) (only_head := false) n (Φ k x1 x2) (Ψ k x1 x2)] :
    IntoLaterN progress (only_head := false) n
      iprop([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2)
      iprop([∗list] k ↦ y1;y2 ∈ l1;l2, Ψ k y1 y2) where
  into_laterN :=
    (BigSepL2.bigSepL2_mono_of_forall fun {k x1 x2} => (h k x1 x2).into_laterN).trans
    BigSepL2.bigSepL2_laterN_2

@[ipm_backtrack, rocq_alias into_laterN_big_sepM]
instance intoLaterN_bigSepM [BI PROP] {K V M}
    [LawfulFiniteMap M K] progress n (Φ Ψ : K → V → PROP) (m : M V)
    [h : ∀ k x, IntoLaterN (progress := true) (only_head := false) n (Φ k x) (Ψ k x)] :
    IntoLaterN progress (only_head := false) n
      iprop([∗map] k ↦ x ∈ m, Φ k x) iprop([∗map] k ↦ x ∈ m, Ψ k x) where
  into_laterN :=
    (BigSepM.bigSepM_mono_of_forall fun {k x} => (h k x).into_laterN).trans
    BigSepM.bigSepM_laterN_2

@[ipm_backtrack, rocq_alias into_laterN_big_sepS]
instance intoLaterN_bigSepS [BI PROP] {S A} [LawfulFiniteSet S A]
    progress n (Φ Ψ : A → PROP) (X : S)
    [h : ∀ x, IntoLaterN (progress := true) (only_head := false) n (Φ x) (Ψ x)] :
    IntoLaterN progress (only_head := false) n
      iprop([∗set] x ∈ X, Φ x) iprop([∗set] x ∈ X, Ψ x) where
  into_laterN :=
    (BigSepS.bigSepS_mono_of_forall fun x => (h x).into_laterN).trans
    BigSepS.bigSepS_laterN_2

@[ipm_backtrack, rocq_alias into_laterN_big_sepMS]
instance intoLaterN_bigSepMS [BI PROP] {MS A} [LawfulFiniteMultiSet MS A]
    progress n (Φ Ψ : A → PROP) (X : MS)
    [h : ∀ x, IntoLaterN (progress := true) (only_head := false) n (Φ x) (Ψ x)] :
    IntoLaterN progress (only_head := false) n
      iprop([∗mset] x ∈ X, Φ x) iprop([∗mset] x ∈ X, Ψ x) where
  into_laterN :=
    (BigSepMS.bigSepMS_mono_of_forall fun x => (h x).into_laterN).trans
    BigSepMS.bigSepMS_laterN_2

@[ipm_backtrack, rocq_alias into_laterN_big_sepM2]
instance intoLaterN_bigSepM2 [BI PROP] {K A B M} [LawfulFiniteMap M K]
    progress n (Φ Ψ : K → A → B → PROP) (m1 : M A) (m2 : M B)
    [h : ∀ k x1 x2, IntoLaterN (progress := true) (only_head := false) n (Φ k x1 x2) (Ψ k x1 x2)] :
    IntoLaterN progress (only_head := false) n
      iprop([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2)
      iprop([∗map] k ↦ x1;x2 ∈ m1;m2, Ψ k x1 x2) where
  into_laterN := calc
    _ ⊢ [∗map] k ↦ x1;x2 ∈ m1;m2, ▷^[n] Ψ k x1 x2 :=
      BigSepM2.bigSepM2_mono_of_forall Φ (fun k x1 x2 => iprop(▷^[n] Ψ k x1 x2)) m1 m2
        (fun {k x1 x2} => (h k x1 x2).into_laterN)
    _ ⊢ ▷^[n] [∗map] k ↦ x1;x2 ∈ m1;m2, Ψ k x1 x2 := BigSepM2.bigSepM2_laterN_2 n

/-! ### CombineSepAs -/

@[rocq_alias maybe_combine_sep_as_later]
instance combineSepAs_later [BI PROP] (Q1 Q2 P : PROP)
    [h : CombineSepAs Q1 Q2 P] :
    CombineSepAs iprop(▷ Q1) iprop(▷ Q2) iprop(▷ P) where
  combine_sep_as := later_sep.mpr.trans (later_mono h.combine_sep_as)

@[rocq_alias maybe_combine_sep_as_laterN]
instance combineSepAs_laterN [BI PROP] (Q1 Q2 P : PROP)
    [h : CombineSepAs Q1 Q2 P] :
    CombineSepAs iprop(▷^[n] Q1) iprop(▷^[n] Q2) iprop(▷^[n] P) where
  combine_sep_as := (laterN_sep n).mpr.trans (laterN_mono n h.combine_sep_as)

@[rocq_alias maybe_combine_sep_as_except_0]
instance combineSepAs_except0 [BI PROP] (Q1 Q2 P : PROP)
    [h : CombineSepAs Q1 Q2 P] :
    CombineSepAs iprop(◇ Q1) iprop(◇ Q2) iprop(◇ P) where
  combine_sep_as := except0_sep.mpr.trans (except0_mono h.combine_sep_as)

/-! ### CombineSepGives -/

@[rocq_alias maybe_combine_sep_gives_later]
instance combineSepGives_later [BI PROP] (Q1 Q2 P : PROP)
    [h : CombineSepGives Q1 Q2 P] :
    CombineSepGives iprop(▷ Q1) iprop(▷ Q2) iprop(▷ P) where
  combine_sep_gives := by calc
    ▷ Q1 ∗ ▷ Q2 ⊢ ▷ (Q1 ∗ Q2) := later_sep.mpr
    _             ⊢ ▷ <pers> P  := later_mono h.combine_sep_gives
    _             ⊢ <pers> ▷ P  := later_persistently.mp

@[rocq_alias maybe_combine_sep_gives_laterN]
instance combineSepGives_laterN [BI PROP] (Q1 Q2 P : PROP)
    [h : CombineSepGives Q1 Q2 P] :
    CombineSepGives iprop(▷^[n] Q1) iprop(▷^[n] Q2) iprop(▷^[n] P) where
  combine_sep_gives := by calc
    ▷^[n] Q1 ∗ ▷^[n] Q2 ⊢ ▷^[n] (Q1 ∗ Q2) := (laterN_sep n).mpr
    _                     ⊢ ▷^[n] <pers> P  := laterN_mono n h.combine_sep_gives
    _                     ⊢ <pers> ▷^[n] P  := (laterN_persistently n).mp

@[rocq_alias maybe_combine_sep_gives_except_0]
instance combineSepGives_except0 [BI PROP] (Q1 Q2 P : PROP)
    [h : CombineSepGives Q1 Q2 P] :
    CombineSepGives iprop(◇ Q1) iprop(◇ Q2) iprop(◇ P) where
  combine_sep_gives := by calc
    ◇ Q1 ∗ ◇ Q2 ⊢ ◇ (Q1 ∗ Q2) := except0_sep.mpr
    _             ⊢ ◇ <pers> P  := except0_mono h.combine_sep_gives
    _             ⊢ <pers> ◇ P  := except0_persistently.mp

end Iris.ProofMode
