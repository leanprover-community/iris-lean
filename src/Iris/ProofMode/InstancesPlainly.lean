/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
module

public import Iris.BI
public import Iris.ProofMode.Classes
public import Iris.ProofMode.ModalityInstances
public import Iris.Std.TC

@[expose] public section

namespace Iris.ProofMode
open Iris.BI Iris.Std

/-- FromAssumption -/

@[rocq_alias from_assumption_plainly_l_true]
instance fromAssumption_plainly_l_true [Sbi PROP] (P Q : PROP)
    [h : FromAssumption true .in P Q] : FromAssumption true .in iprop(■ P) Q where
  from_assumption := intuitionistically_plainly_elim.trans h.1

@[rocq_alias from_assumption_plainly_l_false]
instance fromAssumption_plainly_l_false [Sbi PROP] [BIAffine PROP] (P Q : PROP)
    [h : FromAssumption true .in P Q] : FromAssumption false .in iprop(■ P) Q where
  from_assumption := plainly_elim_persistently.trans <|
    intuitionistically_iff_persistently.2.trans h.1

/-- FromPure -/

@[rocq_alias from_pure_plainly]
instance fromPure_plainly [Sbi PROP] (P : PROP) (φ : Prop)
    [h : FromPure false P φ] : FromPure false iprop(■ P) φ where
  from_pure := plainly_pure.2.trans (plainly_mono h.1)

/-- IntoPure -/

@[rocq_alias into_pure_plainly]
instance intoPure_plainly [Sbi PROP] (P : PROP) (φ : Prop)
    [h : IntoPure P φ] : IntoPure iprop(■ P) φ where
  into_pure := (plainly_mono h.1).trans plainly_elim

/-- IntoWand -/

@[rocq_alias into_wand_plainly_true]
instance intoWand_plainly_true [Sbi PROP] (q : Bool) ioP ioQ (R P Q : PROP)
    [h : IntoWand true q R ioP P ioQ Q] : IntoWand true q iprop(■ R) ioP P ioQ Q where
  into_wand := intuitionistically_plainly_elim.trans h.1

@[rocq_alias into_wand_plainly_false]
instance intoWand_plainly_false [Sbi PROP] (q : Bool) ioP ioQ (R P Q : PROP)
    [Absorbing R] [h : IntoWand false q R ioP P ioQ Q] :
    IntoWand false q iprop(■ R) ioP P ioQ Q where
  into_wand := plainly_elim.trans h.1

/-- FromAnd -/

@[rocq_alias from_and_plainly]
instance fromAnd_plainly [Sbi PROP] (P Q1 Q2 : PROP)
    [h : FromAnd P Q1 Q2] : FromAnd iprop(■ P) iprop(■ Q1) iprop(■ Q2) where
  from_and := plainly_and.2.trans (plainly_mono h.1)

/-- FromSep -/

@[rocq_alias from_sep_plainly]
instance fromSep_plainly [Sbi PROP] (P Q1 Q2 : PROP)
    [h : FromSep P Q1 Q2] : FromSep iprop(■ P) iprop(■ Q1) iprop(■ Q2) where
  from_sep := plainly_sep_2.trans (plainly_mono h.1)

/-- IntoAnd -/

@[rocq_alias into_and_plainly]
instance intoAnd_plainly [Sbi PROP] (p : Bool) (P Q1 Q2 : PROP)
    [h : IntoAnd p P Q1 Q2] : IntoAnd p iprop(■ P) iprop(■ Q1) iprop(■ Q2) where
  into_and := by
    cases p <;> simp only [intuitionisticallyIf, Bool.false_eq_true, ↓reduceIte]
    · exact (plainly_mono h.1).trans plainly_and.1
    · apply (intuitionistically_idem).2.trans (intuitionistically_mono _)
      apply (intuitionistically_plainly.trans (plainly_mono h.1)).trans _
      apply Entails.trans _ (plainly_and.1)
      apply plainly_mono
      apply intuitionistically_elim

/-- IntoSep -/

@[rocq_alias into_sep_plainly]
instance intoSep_plainly [Sbi PROP] [BIPositive PROP] (P Q1 Q2 : PROP)
    [h : IntoSep P Q1 Q2] : IntoSep iprop(■ P) iprop(■ Q1) iprop(■ Q2) where
  into_sep := (plainly_mono h.1).trans plainly_sep.1

@[rocq_alias into_sep_plainly_affine]
instance intoSep_plainly_affine [Sbi PROP] (P Q1 Q2 : PROP)
    [h : IntoSep P Q1 Q2]
    [TCOr (Affine Q1) (Absorbing Q2)] [TCOr (Affine Q2) (Absorbing Q1)] :
    IntoSep iprop(■ P) iprop(■ Q1) iprop(■ Q2) where
  into_sep := (plainly_mono (h.1.trans sep_and)).trans <|
    plainly_and.1.trans and_sep_plainly.1

/-- FromOr -/

@[rocq_alias from_or_plainly]
instance fromOr_plainly [Sbi PROP] (P Q1 Q2 : PROP)
    [h : FromOr P Q1 Q2] : FromOr iprop(■ P) iprop(■ Q1) iprop(■ Q2) where
  from_or := plainly_or_2.trans (plainly_mono h.1)

/-- IntoOr -/

@[rocq_alias into_or_plainly]
instance intoOr_plainly [Sbi PROP] [SbiEmpValidExist PROP] (P Q1 Q2 : PROP)
    [h : IntoOr P Q1 Q2] : IntoOr iprop(■ P) iprop(■ Q1) iprop(■ Q2) where
  into_or := (plainly_mono h.1).trans plainly_or.1

/-- FromExists -/

@[rocq_alias from_exist_plainly]
instance fromExists_plainly [Sbi PROP] (P : PROP) (Φ : α → PROP)
    [h : FromExists P Φ] : FromExists iprop(■ P) (fun a => iprop(■ Φ a)) where
  from_exists := plainly_exists_2.trans (plainly_mono h.1)

/-- IntoExists -/

@[rocq_alias into_exist_plainly]
instance intoExists_plainly [Sbi PROP] [SbiEmpValidExist PROP] (P : PROP)
    {α : Type _} (Φ : α → PROP) [h : IntoExists P Φ] :
    IntoExists iprop(■ P) (fun a => iprop(■ Φ a)) where
  into_exists := (plainly_mono h.1).trans plainly_exists_1

/-- IntoForall -/

@[rocq_alias into_forall_plainly]
instance intoForall_plainly [Sbi PROP] (P : PROP) {α : Type _} (Φ : α → PROP)
    [h : IntoForall P Φ] : IntoForall iprop(■ P) (fun a => iprop(■ Φ a)) where
  into_forall := (plainly_mono h.1).trans plainly_forall.1

/-- FromForall -/

@[rocq_alias from_forall_plainly]
instance fromForall_plainly [Sbi PROP] (P : PROP) {α : Type _} (Φ : α → PROP)
    [h : FromForall P Φ] : FromForall iprop(■ P) (fun a => iprop(■ Φ a)) where
  from_forall := plainly_forall.2.trans (plainly_mono h.1)

/-- FromModal -/

@[rocq_alias from_modal_plainly]
instance fromModal_plainly [Sbi PROP] (P : PROP) :
  FromModal True modality_plainly iprop(■ P) iprop(■ P) P where
  from_modal := by simp [modality_plainly]

/- IntoExcept0 -/

@[rocq_alias into_except_0_plainly]
instance intoExcept0_plainly [Sbi PROP] (P Q : PROP)
    [h : IntoExcept0 P Q] : IntoExcept0 iprop(■ P) iprop(■ Q) where
  into_except0 := (plainly_mono h.1).trans except0_plainly.2

/- IntoLaterN -/

@[rocq_alias into_later_plainly]
instance intoLaterN_plainly [Sbi PROP] (n : Nat) (P Q : PROP)
    [h : IntoLaterN false n P Q] : IntoLaterN false n iprop(■ P) iprop(■ Q) where
  into_laterN := (plainly_mono h.1).trans (laterN_plainly n).2

end Iris.ProofMode
