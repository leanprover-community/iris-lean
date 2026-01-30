/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.BI
import Iris.ProofMode.Classes
import Iris.ProofMode.ModalityInstances
import Iris.Std.TC

namespace Iris.ProofMode
open Iris.BI Iris.Std

/-- FromAssumption -/

instance fromAssumption_plainly_l_true [BI PROP] [BIPlainly PROP] (P Q : PROP)
    [h : FromAssumption true .in P Q] : FromAssumption true .in iprop(■ P) Q where
  from_assumption := intuitionistically_plainly_elim.trans h.1

instance fromAssumption_plainly_l_false [BI PROP] [BIPlainly PROP] [BIAffine PROP] (P Q : PROP)
    [h : FromAssumption true .in P Q] : FromAssumption false .in iprop(■ P) Q where
  from_assumption := BIPlainly.elim_persistently.trans <|
    intuitionistically_iff_persistently.2.trans h.1

/-- FromPure -/

instance fromPure_plainly [BI PROP] [BIPlainly PROP] (P : PROP) (φ : Prop)
    [h : FromPure false P φ] : FromPure false iprop(■ P) φ where
  from_pure := plainly_pure.2.trans (BIPlainly.mono h.1)

/-- IntoPure -/

instance intoPure_plainly [BI PROP] [BIPlainly PROP] (P : PROP) (φ : Prop)
    [h : IntoPure P φ] : IntoPure iprop(■ P) φ where
  into_pure := (BIPlainly.mono h.1).trans plainly_elim

/-- IntoWand -/

instance intoWand_plainly_true [BI PROP] [BIPlainly PROP] (q : Bool) ioP ioQ (R P Q : PROP)
    [h : IntoWand true q R ioP P ioQ Q] : IntoWand true q iprop(■ R) ioP P ioQ Q where
  into_wand := intuitionistically_plainly_elim.trans h.1

instance intoWand_plainly_false [BI PROP] [BIPlainly PROP] (q : Bool) ioP ioQ (R P Q : PROP)
    [Absorbing R] [h : IntoWand false q R ioP P ioQ Q] :
    IntoWand false q iprop(■ R) ioP P ioQ Q where
  into_wand := plainly_elim.trans h.1

/-- FromAnd -/

instance fromAnd_plainly [BI PROP] [BIPlainly PROP] (P Q1 Q2 : PROP)
    [h : FromAnd P Q1 Q2] : FromAnd iprop(■ P) iprop(■ Q1) iprop(■ Q2) where
  from_and := plainly_and.2.trans (BIPlainly.mono h.1)

/-- FromSep -/

instance fromSep_plainly [BI PROP] [BIPlainly PROP] (P Q1 Q2 : PROP)
    [h : FromSep P Q1 Q2] : FromSep iprop(■ P) iprop(■ Q1) iprop(■ Q2) where
  from_sep := plainly_sep_2.trans (BIPlainly.mono h.1)

/-- IntoAnd -/

instance intoAnd_plainly [BI PROP] [BIPlainly PROP] (p : Bool) (P Q1 Q2 : PROP)
    [h : IntoAnd p P Q1 Q2] : IntoAnd p iprop(■ P) iprop(■ Q1) iprop(■ Q2) where
  into_and := by
    cases p <;> simp only [intuitionisticallyIf, Bool.false_eq_true, ↓reduceIte]
    · exact (BIPlainly.mono h.1).trans plainly_and.1
    · apply (intuitionistically_idem).2.trans (intuitionistically_mono _)
      apply (intuitionistically_plainly.trans (BIPlainly.mono h.1)).trans _
      apply Entails.trans _ (plainly_and.1)
      apply BIPlainly.mono
      apply intuitionistically_elim

/-- IntoSep -/

instance intoSep_plainly [BI PROP] [BIPlainly PROP] [BIPositive PROP] (P Q1 Q2 : PROP)
    [h : IntoSep P Q1 Q2] : IntoSep iprop(■ P) iprop(■ Q1) iprop(■ Q2) where
  into_sep := (BIPlainly.mono h.1).trans plainly_sep.1

instance intoSep_plainly_affine [BI PROP] [BIPlainly PROP] (P Q1 Q2 : PROP)
    [h : IntoSep P Q1 Q2]
    [TCOr (Affine Q1) (Absorbing Q2)] [TCOr (Affine Q2) (Absorbing Q1)] :
    IntoSep iprop(■ P) iprop(■ Q1) iprop(■ Q2) where
  into_sep := (BIPlainly.mono (h.1.trans sep_and)).trans <|
    plainly_and.1.trans and_sep_plainly.1

/-- FromOr -/

instance fromOr_plainly [BI PROP] [BIPlainly PROP] (P Q1 Q2 : PROP)
    [h : FromOr P Q1 Q2] : FromOr iprop(■ P) iprop(■ Q1) iprop(■ Q2) where
  from_or := plainly_or_2.trans (BIPlainly.mono h.1)

/-- IntoOr -/

instance intoOr_plainly [BI PROP] [BIPlainly PROP] [BIPlainlyExists PROP] (P Q1 Q2 : PROP)
    [h : IntoOr P Q1 Q2] : IntoOr iprop(■ P) iprop(■ Q1) iprop(■ Q2) where
  into_or := (BIPlainly.mono h.1).trans plainly_or.1

/-- FromExists -/

instance fromExists_plainly [BI PROP] [BIPlainly PROP] (P : PROP) (Φ : α → PROP)
    [h : FromExists P Φ] : FromExists iprop(■ P) (fun a => iprop(■ Φ a)) where
  from_exists := plainly_exists_2.trans (BIPlainly.mono h.1)

/-- IntoExists -/

instance intoExists_plainly [BI PROP] [BIPlainly PROP] [BIPlainlyExists PROP] (P : PROP)
    (Φ : α → PROP) [h : IntoExists P Φ] :
    IntoExists iprop(■ P) (fun a => iprop(■ Φ a)) where
  into_exists := (BIPlainly.mono h.1).trans plainly_exists_1

/-- IntoForall -/

instance intoForall_plainly [BI PROP] [BIPlainly PROP] (P : PROP) (Φ : α → PROP)
    [h : IntoForall P Φ] : IntoForall iprop(■ P) (fun a => iprop(■ Φ a)) where
  into_forall := (BIPlainly.mono h.1).trans plainly_forall.1

/-- FromForall -/

instance fromForall_plainly [BI PROP] [BIPlainly PROP] (P : PROP) (Φ : α → PROP)
    [h : FromForall P Φ] : FromForall iprop(■ P) (fun a => iprop(■ Φ a)) where
  from_forall := plainly_forall.2.trans (BIPlainly.mono h.1)

/-- FromModal -/

instance fromModal_plainly [BI PROP] [BIPlainly PROP] (P : PROP) :
  FromModal True modality_plainly iprop(■ P) iprop(■ P) P where
  from_modal := by simp [modality_plainly]

/- IntoExcept0 -/

/- TODO
instance intoExcept0_plainly [BI PROP] [BIPlainly PROP] [BIPlainlyExists PROP] (P Q : PROP)
    [h : IntoExcept0 P Q] : IntoExcept0 iprop(■ P) iprop(■ Q) where
  into_except0 := (BIPlainly.mono h.1).trans except0_plainly.2
-/

/- IntoLaterN -/

/- TODO
instance intoLaterN_plainly [BI PROP] [BIPlainly PROP] (n : Nat) (P Q : PROP)
    [h : IntoLaterN false n P Q] : IntoLaterN false n iprop(■ P) iprop(■ Q) where
  into_laterN := (BIPlainly.mono h.1).trans (laterN_plainly n).2
-/

end Iris.ProofMode
