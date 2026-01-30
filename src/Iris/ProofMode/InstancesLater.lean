/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.BI
import Iris.ProofMode.Classes
import Iris.ProofMode.ClassesMake
import Iris.ProofMode.ModalityInstances
import Iris.Std.TC

namespace Iris.ProofMode
open Iris.BI Iris.Std

/-- FromAssumption -/

instance fromAssumption_later [BI PROP] (p : Bool) ioP (P Q : PROP)
    [h : FromAssumption p ioP P Q] : FromAssumption p ioP P iprop(▷ Q) where
  from_assumption := h.1.trans later_intro

instance fromAssumption_laterN [BI PROP] n (p : Bool) ioP (P Q : PROP)
    [h : FromAssumption p ioP P Q] : FromAssumption p ioP P iprop(▷^[n] Q) where
  from_assumption := h.1.trans (laterN_intro n)

instance fromAssumption_except0 [BI PROP] (p : Bool) ioP (P Q : PROP)
    [h : FromAssumption p ioP P Q] : FromAssumption p ioP P iprop(◇ Q) where
  from_assumption := h.1.trans except0_intro


/-- FromPure -/

instance fromPure_later [BI PROP] (a : Bool) (P : PROP) (φ : Prop)
    [h : FromPure a P φ] : FromPure a iprop(▷ P) φ where
  from_pure := h.1.trans later_intro

instance fromPure_laterN [BI PROP] (a : Bool) (n : Nat) (P : PROP) (φ : Prop)
    [h : FromPure a P φ] : FromPure a iprop(▷^[n] P) φ where
  from_pure := h.1.trans (laterN_intro n)

instance fromPure_except0 [BI PROP] (a : Bool) (P : PROP) (φ : Prop)
    [h : FromPure a P φ] : FromPure a iprop(◇ P) φ where
  from_pure := h.1.trans except0_intro

/-- IntoWand -/

instance intoWand_later [BI PROP] (p q : Bool) ioP ioQ (R P Q : PROP)
    [h : IntoWand p q R ioP P ioQ Q] : IntoWand p q iprop(▷ R) ioP iprop(▷ P) ioQ iprop(▷ Q) where
  into_wand := later_intuitionisticallyIf_2.trans <|
    (later_mono h.1).trans <| later_wand.trans <| wand_mono later_intuitionisticallyIf_2 .rfl

-- TODO: see if this is necessary. It is an instance for IntoWand' in Rocq
-- instance intoWand_later_args [BI PROP] (p q : Bool) ioP ioQ (R P Q : PROP)
--     [h : IntoWand p q R ioP P ioQ Q] : IntoWand p q R ioP iprop(▷ P) ioQ iprop(▷ Q) where
--   into_wand := (intuitionisticallyIf_mono later_intro).trans <| later_intuitionisticallyIf_2.trans <|
--     (later_mono h.1).trans <| later_wand.trans <| wand_mono later_intuitionisticallyIf_2 .rfl

instance intoWand_laterN [BI PROP] (n : Nat) (p q : Bool) ioP ioQ (R P Q : PROP)
    [h : IntoWand p q R ioP P ioQ Q] : IntoWand p q iprop(▷^[n] R) ioP iprop(▷^[n] P) ioQ iprop(▷^[n] Q) where
  into_wand := (laterN_intuitionisticallyIf_2 n).trans <|
    (laterN_mono n h.1).trans <| (laterN_wand n).trans <| wand_mono (laterN_intuitionisticallyIf_2 n) .rfl

-- TODO: see if this is necessary. It is an instance for IntoWand' in Rocq
-- instance intoWand_laterN_args [BI PROP] (n : Nat) (p q : Bool) ioP ioQ (R P Q : PROP)
--     [h : IntoWand p q R ioP P ioQ Q] : IntoWand p q R ioP iprop(▷^[n] P) ioQ iprop(▷^[n] Q) where
--   into_wand := (intuitionisticallyIf_mono (laterN_intro n)).trans <| (laterN_intuitionisticallyIf_2 n).trans <|
--     (laterN_mono n h.1).trans <| (laterN_wand n).trans <| wand_mono (laterN_intuitionisticallyIf_2 n) .rfl

/-- FromAnd -/

instance fromAnd_later [BI PROP] (P Q1 Q2 : PROP)
    [h : FromAnd P Q1 Q2] : FromAnd iprop(▷ P) iprop(▷ Q1) iprop(▷ Q2) where
  from_and := later_and.2.trans (later_mono h.1)

instance fromAnd_laterN [BI PROP] (n : Nat) (P Q1 Q2 : PROP)
    [h : FromAnd P Q1 Q2] : FromAnd iprop(▷^[n] P) iprop(▷^[n] Q1) iprop(▷^[n] Q2) where
  from_and := (laterN_and n).2.trans (laterN_mono n h.1)

instance fromAnd_except0 [BI PROP] (P Q1 Q2 : PROP)
    [h : FromAnd P Q1 Q2] : FromAnd iprop(◇ P) iprop(◇ Q1) iprop(◇ Q2) where
  from_and := except0_and.2.trans (except0_mono h.1)

/-- FromSep -/

instance fromSep_later [BI PROP] (P Q1 Q2 : PROP)
    [h : FromSep P Q1 Q2] : FromSep iprop(▷ P) iprop(▷ Q1) iprop(▷ Q2) where
  from_sep := later_sep.2.trans (later_mono h.1)

instance fromSep_laterN [BI PROP] (n : Nat) (P Q1 Q2 : PROP)
    [h : FromSep P Q1 Q2] : FromSep iprop(▷^[n] P) iprop(▷^[n] Q1) iprop(▷^[n] Q2) where
  from_sep := (laterN_sep n).2.trans (laterN_mono n h.1)

instance fromSep_except0 [BI PROP] (P Q1 Q2 : PROP)
    [h : FromSep P Q1 Q2] : FromSep iprop(◇ P) iprop(◇ Q1) iprop(◇ Q2) where
  from_sep := except0_sep.2.trans (except0_mono h.1)

/-- IntoAnd -/

instance intoAnd_later [BI PROP] (p : Bool) (P Q1 Q2 : PROP)
    [h : IntoAnd p P Q1 Q2] : IntoAnd p iprop(▷ P) iprop(▷ Q1) iprop(▷ Q2) where
  into_and := intuitionisticallyIf_intro' <|
    later_intuitionisticallyIf_2.trans <| (later_mono <| h.1.trans intuitionisticallyIf_elim).trans later_and.1

instance intoAnd_laterN [BI PROP] (n : Nat) (p : Bool) (P Q1 Q2 : PROP)
    [h : IntoAnd p P Q1 Q2] : IntoAnd p iprop(▷^[n] P) iprop(▷^[n] Q1) iprop(▷^[n] Q2) where
  into_and := intuitionisticallyIf_intro' <|
    (laterN_intuitionisticallyIf_2 n).trans <| (laterN_mono n <| h.1.trans intuitionisticallyIf_elim).trans (laterN_and n).1

instance intoAnd_except0 [BI PROP] (p : Bool) (P Q1 Q2 : PROP)
    [h : IntoAnd p P Q1 Q2] : IntoAnd p iprop(◇ P) iprop(◇ Q1) iprop(◇ Q2) where
  into_and := intuitionisticallyIf_intro' <|
    except0_intuitionisticallyIf_2.trans <| (except0_mono <| h.1.trans intuitionisticallyIf_elim).trans except0_and.1

/-- IntoSep -/

instance intoSep_later [BI PROP] (P Q1 Q2 : PROP)
    [h : IntoSep P Q1 Q2] : IntoSep iprop(▷ P) iprop(▷ Q1) iprop(▷ Q2) where
  into_sep := (later_mono h.1).trans later_sep.1

instance intoSep_laterN [BI PROP] (n : Nat) (P Q1 Q2 : PROP)
    [h : IntoSep P Q1 Q2] : IntoSep iprop(▷^[n] P) iprop(▷^[n] Q1) iprop(▷^[n] Q2) where
  into_sep := (laterN_mono n h.1).trans (laterN_sep n).1

instance intoSep_except0 [BI PROP] (P Q1 Q2 : PROP)
    [h : IntoSep P Q1 Q2] : IntoSep iprop(◇ P) iprop(◇ Q1) iprop(◇ Q2) where
  into_sep := (except0_mono h.1).trans except0_sep.1

/-- FromOr -/

instance fromOr_later [BI PROP] (P Q1 Q2 : PROP)
    [h : FromOr P Q1 Q2] : FromOr iprop(▷ P) iprop(▷ Q1) iprop(▷ Q2) where
  from_or := later_or.2.trans (later_mono h.1)

instance fromOr_laterN [BI PROP] (n : Nat) (P Q1 Q2 : PROP)
    [h : FromOr P Q1 Q2] : FromOr iprop(▷^[n] P) iprop(▷^[n] Q1) iprop(▷^[n] Q2) where
  from_or := (laterN_or n).2.trans (laterN_mono n h.1)

instance fromOr_except0 [BI PROP] (P Q1 Q2 : PROP)
    [h : FromOr P Q1 Q2] : FromOr iprop(◇ P) iprop(◇ Q1) iprop(◇ Q2) where
  from_or := except0_or.2.trans (except0_mono h.1)

/-- IntoOr -/

instance intoOr_later [BI PROP] (P Q1 Q2 : PROP)
    [h : IntoOr P Q1 Q2] : IntoOr iprop(▷ P) iprop(▷ Q1) iprop(▷ Q2) where
  into_or := (later_mono h.1).trans later_or.1

instance intoOr_laterN [BI PROP] (n : Nat) (P Q1 Q2 : PROP)
    [h : IntoOr P Q1 Q2] : IntoOr iprop(▷^[n] P) iprop(▷^[n] Q1) iprop(▷^[n] Q2) where
  into_or := (laterN_mono n h.1).trans (laterN_or n).1

instance intoOr_except0 [BI PROP] (P Q1 Q2 : PROP)
    [h : IntoOr P Q1 Q2] : IntoOr iprop(◇ P) iprop(◇ Q1) iprop(◇ Q2) where
  into_or := (except0_mono h.1).trans except0_or.1

/-- FromExists -/

instance fromExists_later [BI PROP] (P : PROP) (Φ : α → PROP)
    [h : FromExists P Φ] : FromExists iprop(▷ P) (fun a => iprop(▷ Φ a)) where
  from_exists := (exists_elim fun x => (later_mono (exists_intro x))).trans (later_mono h.1)

instance fromExists_laterN [BI PROP] (n : Nat) (P : PROP) (Φ : α → PROP)
    [h : FromExists P Φ] : FromExists iprop(▷^[n] P) (fun a => iprop(▷^[n] Φ a)) where
  from_exists := (exists_elim fun x => (laterN_mono n (exists_intro x))).trans (laterN_mono n h.1)

instance fromExists_except0 [BI PROP] (P : PROP) (Φ : α → PROP)
    [h : FromExists P Φ] : FromExists iprop(◇ P) (fun a => iprop(◇ Φ a)) where
  from_exists := except0_exists_2.trans (except0_mono h.1)

/-- IntoExists -/

instance intoExists_later [BI PROP] [Inhabited α] (P : PROP) (Φ : α → PROP)
    [h : IntoExists P Φ] : IntoExists iprop(▷ P) (fun a => iprop(▷ Φ a)) where
  into_exists := (later_mono h.1).trans later_exists.2

instance intoExists_laterN [BI PROP] [Inhabited α] (n : Nat) (P : PROP) (Φ : α → PROP)
    [h : IntoExists P Φ] : IntoExists iprop(▷^[n] P) (fun a => iprop(▷^[n] Φ a)) where
  into_exists := (laterN_mono n h.1).trans (laterN_exists n).1

instance intoExists_except0 [BI PROP] [Inhabited α] (P : PROP) (Φ : α → PROP)
    [h : IntoExists P Φ] : IntoExists iprop(◇ P) (fun a => iprop(◇ Φ a)) where
  into_exists := (except0_mono h.1).trans (except0_exists.1)

/-- IntoForall -/

instance intoForall_later [BI PROP] (P : PROP) (Φ : α → PROP)
    [h : IntoForall P Φ] : IntoForall iprop(▷ P) (fun a => iprop(▷ Φ a)) where
  into_forall := (later_mono h.1).trans later_forall.1

instance intoForall_laterN [BI PROP] (n : Nat) (P : PROP) (Φ : α → PROP)
    [h : IntoForall P Φ] : IntoForall iprop(▷^[n] P) (fun a => iprop(▷^[n] Φ a)) where
  into_forall := (laterN_mono n h.1).trans (laterN_forall n).1

instance intoForall_except0 [BI PROP] (P : PROP) (Φ : α → PROP)
    [h : IntoForall P Φ] : IntoForall iprop(◇ P) (fun a => iprop(◇ Φ a)) where
  into_forall := (except0_mono h.1).trans except0_forall.1

/-- FromForall -/

instance fromForall_later [BI PROP] (P : PROP) (Φ : α → PROP)
    [h : FromForall P Φ] : FromForall iprop(▷ P) (fun a => iprop(▷ Φ a)) where
  from_forall := later_forall.2.trans (later_mono h.1)

instance fromForall_laterN [BI PROP] (n : Nat) (P : PROP) (Φ : α → PROP)
    [h : FromForall P Φ] : FromForall iprop(▷^[n] P) (fun a => iprop(▷^[n] Φ a)) where
  from_forall := (laterN_forall n).2.trans (laterN_mono n h.1)

instance fromForall_except0 [BI PROP] (P : PROP) (Φ : α → PROP)
    [h : FromForall P Φ] : FromForall iprop(◇ P) (fun a => iprop(◇ Φ a)) where
  from_forall := except0_forall.2.trans (except0_mono h.1)

/-- IsExcept0 -/

instance isExcept0_except0 [BI PROP] (P : PROP) : IsExcept0 iprop(◇ P) where
  is_except0 := (except0_idemp.1)

instance isExcept0_later [BI PROP] (P : PROP) : IsExcept0 iprop(▷ P) where
  is_except0 := except0_later

/-- FromModal -/

instance fromModal_later [BI PROP] (P : PROP) :
  FromModal True (modality_laterN 1) iprop(▷^[1] P) iprop(▷ P) P where
  from_modal _ := .rfl

instance fromModal_laterN [BI PROP] (P : PROP) n :
  FromModal True (modality_laterN n) iprop(▷^[n] P) iprop(▷^[n] P) P where
  from_modal _ := .rfl

instance fromModal_except0 [BI PROP] (P : PROP) :
  FromModal True modality_id iprop(◇ P) iprop(◇ P) P where
  from_modal _ := except0_intro

/-- IntoExcept0 -/

instance intoExcept0_except0 [BI PROP] (P : PROP) : IntoExcept0 iprop(◇ P) P where
  into_except0 := .rfl

instance intoExcept0_later [BI PROP] (P : PROP) [Timeless P] : IntoExcept0 iprop(▷ P) P where
  into_except0 := Timeless.timeless

instance intoExcept0_laterIf [BI PROP] p (P : PROP) [Timeless P] : IntoExcept0 iprop(▷?p P) P where
  into_except0 := match p with
                  | true => Timeless.timeless
                  | false => except0_intro

instance intoExcept0_affinely [BI PROP] (P Q : PROP)
    [h : IntoExcept0 P Q] : IntoExcept0 iprop(<affine> P) iprop(<affine> Q) where
  into_except0 := (affinely_mono h.1).trans except0_affinely_2

instance intoExcept0_intuitionistically [BI PROP] (P Q : PROP)
    [h : IntoExcept0 P Q] : IntoExcept0 iprop(□ P) iprop(□ Q) where
  into_except0 := (intuitionistically_mono h.1).trans except0_intuitionistically_2

instance intoExcept0_absorbingly [BI PROP] (P Q : PROP)
    [h : IntoExcept0 P Q] : IntoExcept0 iprop(<absorb> P) iprop(<absorb> Q) where
  into_except0 := (absorbingly_mono h.1).trans except0_absorbingly.2

instance intoExcept0_persistently [BI PROP] (P Q : PROP)
    [h : IntoExcept0 P Q] : IntoExcept0 iprop(<pers> P) iprop(<pers> Q) where
  into_except0 := (persistently_mono h.1).trans except0_persistently.2

/-- ElimModal -/
@[ipm_backtrack]
instance (priority := default - 10) elimModal_timeless [BI PROP] p (P P' Q : PROP) [IntoExcept0 P P'] [IsExcept0 Q] :
  ElimModal True p p P P' Q Q where
  elim_modal _ := ((sep_mono ((intuitionisticallyIf_mono into_except0).trans except0_intuitionisticallyIf_2) except0_intro).trans $ except0_sep.2.trans (except0_mono wand_elim_r)).trans is_except0

/-- IntoLaterN -/
instance (priority := low) intoLaterN_default [BI PROP] only_head n (P : PROP) :
  IntoLaterN only_head n P P where
  into_laterN := laterN_intro n

instance (priority := high) intoLaterN_default_0 [BI PROP] only_head (P : PROP) :
  IntoLaterN only_head 0 P P where
  into_laterN := laterN_intro 0

instance intoLaterN_later [BI PROP] only_head n n' m' (P Q lQ : PROP)
    [h1 : NatCancel n 1 n' m']
    [h2 : IntoLaterN only_head n' P Q]
    [h3 : MakeLaterN m' Q lQ] : IntoLaterN only_head n iprop(▷ P) lQ where
  into_laterN := (later_mono h2.1).trans $ (later_laterN _).2.trans $ by
    rw [h1.1]
    apply (laterN_add _ _).1.trans (laterN_mono _ h3.1.1)

instance intoLaterN_laterN [BI PROP] only_head n m n' m' (P Q lQ : PROP)
    [h1 : NatCancel n m n' m']
    [h2 : IntoLaterN only_head n' P Q]
    [h3 : MakeLaterN m' Q lQ] : IntoLaterN only_head n iprop(▷^[m] P) lQ where
  into_laterN := (laterN_mono _ h2.1).trans $ (laterN_add _ _).2.trans $ by
    rw [Nat.add_comm, h1.1]
    apply (laterN_add _ _).1.trans (laterN_mono _ h3.1.1)

instance intoLaterN_and [BI PROP] n (P1 P2 Q1 Q2 : PROP)
    [h1 : IntoLaterN false n P1 Q1] [h2 : IntoLaterN false n P2 Q2] :
    IntoLaterN false n iprop(P1 ∧ P2) iprop(Q1 ∧ Q2) where
  into_laterN := (and_mono h1.1 h2.1).trans (laterN_and n).2

instance intoLaterN_forall [BI PROP] n (Φ Ψ : α → PROP)
    [h : ∀ x, IntoLaterN false n (Φ x) (Ψ x)] : IntoLaterN false n iprop(∀ x, Φ x) iprop(∀ x, Ψ x) where
  into_laterN := (forall_mono fun x => (h x).1).trans (laterN_forall n).2

instance intoLaterN_exists [BI PROP] n (Φ Ψ : α → PROP)
    [h : ∀ x, IntoLaterN false n (Φ x) (Ψ x)] : IntoLaterN false n iprop(∃ x, Φ x) iprop(∃ x, Ψ x) where
  into_laterN := (exists_mono fun x => (h x).1).trans (laterN_exists_2 n)

instance intoLaterN_or [BI PROP] n (P1 P2 Q1 Q2 : PROP)
    [h1 : IntoLaterN false n P1 Q1] [h2 : IntoLaterN false n P2 Q2] :
    IntoLaterN false n iprop(P1 ∨ P2) iprop(Q1 ∨ Q2) where
  into_laterN := (or_mono h1.1 h2.1).trans (laterN_or n).2

instance intoLaterN_affinely [BI PROP] n (P Q : PROP)
    [h : IntoLaterN false n P Q] : IntoLaterN false n iprop(<affine> P) iprop(<affine> Q) where
  into_laterN := (affinely_mono h.1).trans (laterN_affinely_2 n)

instance intoLaterN_intuitionistically [BI PROP] n (P Q : PROP)
    [h : IntoLaterN false n P Q] : IntoLaterN false n iprop(□ P) iprop(□ Q) where
  into_laterN := (intuitionistically_mono h.1).trans (laterN_intuitionistically_2 n)

instance intoLaterN_absorbingly [BI PROP] n (P Q : PROP)
    [h : IntoLaterN false n P Q] : IntoLaterN false n iprop(<absorb> P) iprop(<absorb> Q) where
  into_laterN := (absorbingly_mono h.1).trans (laterN_absorbingly n).2

instance intoLaterN_persistently [BI PROP] n (P Q : PROP)
    [h : IntoLaterN false n P Q] : IntoLaterN false n iprop(<pers> P) iprop(<pers> Q) where
  into_laterN := (persistently_mono h.1).trans (laterN_persistently n).2

instance intoLaterN_sep [BI PROP] n (P1 P2 Q1 Q2 : PROP)
    [h1 : IntoLaterN false n P1 Q1] [h2 : IntoLaterN false n P2 Q2] :
    IntoLaterN false n iprop(P1 ∗ P2) iprop(Q1 ∗ Q2) where
  into_laterN := (sep_mono h1.1 h2.1).trans (laterN_sep n).2

end Iris.ProofMode
