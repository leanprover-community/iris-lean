/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.BI
import Iris.Proofmode.Classes
import Iris.Std.TC

namespace Iris.Proofmode
open Iris.BI Iris.Std

-- AsEmpValid
instance (priority := default - 10) asEmpValidEmpValid1
    [BI PROP] (P : PROP) : AsEmpValid1 (⊢ P) P := ⟨by simp⟩
instance (priority := default + 10) asEmpValidEmpValid2
    [BI PROP] (P : PROP) : AsEmpValid2 (⊢ P) P := AsEmpValid1.to2

instance asEmpValidEntails1 [bi : BI PROP] (P Q : PROP) :
  AsEmpValid1 (P ⊢ Q) iprop(P -∗ Q)
where
  as_emp_valid := by
    constructor
    · exact entails_wand
    · exact wand_entails
instance asEmpValidEntails2 [BI PROP] (P Q : PROP) :
  AsEmpValid2 (P ⊢ Q) iprop(P -∗ Q) := AsEmpValid1.to2
example [BI PROP] (Q : PROP) :=
  have : AsEmpValid2 (Q ⊢ Q) _ := inferInstance
  trivial

instance asEmpValidEquiv1 [BI PROP] (P Q : PROP) :
  AsEmpValid1 (P ⊣⊢ Q) iprop(P ∗-∗ Q)
where
  as_emp_valid := by
    constructor
    · exact equiv_wandIff
    · exact wandIff_equiv
instance asEmpValidEquiv2 [BI PROP] (P Q : PROP) :
  AsEmpValid2 (P ⊣⊢ Q) iprop(P ∗-∗ Q) := AsEmpValid1.to2

-- FromImp
instance fromImplImp [BI PROP] (P1 P2 : PROP) :
  FromImp iprop(P1 → P2) P1 P2
where
  from_imp := by
    simp

-- FromWand
instance fromWandWand [BI PROP] (P1 P2 : PROP) :
  FromWand iprop(P1 -∗ P2) P1 P2
where
  from_wand := by
    simp

-- IntoWand
instance intoWandWand (p q : Bool) [BI PROP] (P Q P' : PROP) :
  [FromAssumption q P P'] →
  IntoWand p q iprop(P' -∗ Q) P Q
where
  into_wand := by
    rw' [(FromAssumption.from_assumption : □?q P ⊢ P'), intuitionisticallyIf_elim]

instance intoWandImplFalseFalse [BI PROP] (P Q P' : PROP) :
  [Absorbing P'] →
  [Absorbing iprop(P' → Q)] →
  [FromAssumption false P P'] →
  IntoWand false false iprop(P' → Q) P Q
where
  into_wand := by
    rw' [← (FromAssumption.from_assumption : □?false P ⊢ P')]
    simp only [intuitionisticallyIf, ite_false]
    apply BI.wand_intro
    rw' [sep_and, imp_elim_l]

instance intoWandImplFalseTrue [BI PROP] (P Q P' : PROP) :
  [Absorbing P'] →
  [FromAssumption true P P'] →
  IntoWand false true iprop(P' → Q) P Q
where
  into_wand := by
    simp only [intuitionisticallyIf, ite_true, ite_false]
    apply wand_intro'
    rw' [
      ← intuitionistically_idem,
      (FromAssumption.from_assumption : □?true P ⊢ P'),
      ← persistently_and_intuitionistically_sep_l,
      persistently_elim,
      imp_elim_r]

instance intoWandImplTrueFalse [BI PROP] (P Q P' : PROP) :
  [Affine P'] →
  [FromAssumption false P P'] →
  IntoWand true false iprop(P' → Q) P Q
where
  into_wand := by
    simp only [intuitionisticallyIf, ite_true, ite_false]
    rw' [← (FromAssumption.from_assumption : □?false P ⊢ P')]
    apply BI.wand_intro
    rw' [sep_and, intuitionistically_elim, imp_elim_l]

instance intoWandImplTrueTrue [BI PROP] (P Q P' : PROP) :
  [FromAssumption true P P'] →
  IntoWand true true iprop(P' → Q) P Q
where
  into_wand := by
    rw' [(FromAssumption.from_assumption : □?true P ⊢ P')]
    simp only [intuitionisticallyIf, ite_true, ite_false]
    apply wand_intro'
    rw' [
      sep_and,
      (intuitionistically_elim : □ (□ P → _) ⊢ _),
      imp_elim_r]

instance intoWandAndL (p q : Bool) [BI PROP] (R1 R2 P' Q' : PROP) :
  [IntoWand p q R1 P' Q'] →
  IntoWand p q iprop(R1 ∧ R2) P' Q'
where
  into_wand := by
    rw' [BI.and_elim_l]
    exact IntoWand.into_wand

instance intoWandAndR (p q : Bool) [BI PROP] (R1 R2 P' Q' : PROP) :
  [IntoWand p q R2 Q' P'] →
  IntoWand p q iprop(R1 ∧ R2) Q' P'
where
  into_wand := by
    rw' [BI.and_elim_r]
    exact IntoWand.into_wand

set_option synthInstance.checkSynthOrder false in
instance intoWandForall (p q : Bool) [BI PROP] (Φ : α → PROP) (P Q : PROP) (x : α)
  [inst : IntoWand p q (Φ x) P Q] :
  IntoWand p q iprop(∀ x, Φ x) P Q
where
  into_wand := by
    rw' [← (IntoWand.into_wand : □?p Φ x ⊢ □?q P -∗ Q), BI.forall_elim x]

instance intoWandAffine (p q : Bool) [BI  PROP] (R P Q : PROP) :
  [IntoWand p q R P Q] →
  IntoWand p q iprop(<affine> R) iprop(<affine> P) iprop(<affine> Q)
where
  into_wand := by
    apply BI.wand_intro ?_
    cases p
    case false =>
      cases q
      case false =>
        rw' [(IntoWand.into_wand : □?false R ⊢ □?false P -∗ Q)]
        simp only [intuitionisticallyIf, ite_false]
        rw' [affinely_sep_2, wand_elim_l]
      case true =>
        rw' [
          (affinely_elim : _ ⊢ P),
          (IntoWand.into_wand : □?false R ⊢ □?true P -∗ Q)]
        simp only [intuitionisticallyIf, ite_true, ite_false]
        conv =>
          lhs
          rhs
          rw [← affine_affinely iprop(□ P)]
        rw' [affinely_sep_2, wand_elim_l]
    case true =>
      rw' [
        (affinely_elim : <affine> R ⊢ _),
        ← intuitionisticallyIf_intro_true,
        ← affine_affinely iprop(□ R)]
      cases q
      case false =>
        rw' [
          (IntoWand.into_wand : □?true R ⊢ □?false P -∗ Q),
          affinely_sep_2,
          wand_elim_l]
      case true =>
        simp only [intuitionisticallyIf, ite_true]
        rw' [
          (affinely_elim : <affine> P ⊢ _),
          ← affine_affinely iprop(□ P),
          (IntoWand.into_wand : □?true R ⊢ □?true P -∗ Q),
          affinely_sep_2,
          wand_elim_l]

instance intoWandIntuitionistically (p q : Bool) [BI PROP] (R P Q : PROP) :
  [IntoWand true q R P Q] →
  IntoWand p q iprop(□ R) P Q
where
  into_wand := by
    rw' [(IntoWand.into_wand : □?true R ⊢ □?q P -∗ Q), intuitionisticallyIf_elim]

instance intoWandPersistentlyTrue (q : Bool) [BI PROP] (R P Q : PROP) :
  [IntoWand true q R P Q] →
  IntoWand true q iprop(<pers> R) P Q
where
  into_wand := by
    rw' [
      ← intuitionisticallyIf_intro_true,
      intuitionistically_persistently,
      (IntoWand.into_wand : □?true R ⊢ □?q P -∗ Q)]

instance intoWandPersistentlyFalse (q : Bool) [BI PROP] (R P Q : PROP) :
  [Absorbing R] →
  [IntoWand false q R P Q] →
  IntoWand false q iprop(<pers> R) P Q
where
  into_wand := by
    rw' [persistently_elim, (IntoWand.into_wand : □?false R ⊢ □?q P -∗ Q)]

-- FromForall
instance fromForallForall [BI PROP] (Φ : α → PROP) :
  FromForall (BIBase.forall Φ) Φ
where
  from_forall := by
    simp

-- IntoForall
instance intoForallForall [BI PROP] (Φ : α → PROP) :
  IntoForall iprop(∀ a, Φ a) Φ
where
  into_forall := by
    simp

instance intoForallAffinely [BI PROP] (P : PROP) (Φ : α → PROP) :
  [IntoForall P Φ] →
  IntoForall iprop(<affine> P) (fun a => iprop(<affine> (Φ a)))
where
  into_forall := by
    rw' [IntoForall.into_forall, affinely_forall]

instance intoForallIntuitionistically [BI PROP] (P : PROP) (Φ : α → PROP) :
  [IntoForall P Φ] →
  IntoForall iprop(□ P) (fun a => iprop(□ (Φ a)))
where
  into_forall := by
    rw' [IntoForall.into_forall, intuitionistically_forall]

-- FromExists
instance (priority := default + 10) fromExistsExists [BI PROP] (Φ : α → PROP) :
  FromExists iprop(∃ a, Φ a) Φ
where
  from_exists := by
    simp

instance fromExistsPure (φ : α → Prop) [BI PROP] :
  FromExists (PROP := PROP) iprop(⌜∃ x, φ x⌝) (fun a => iprop(⌜φ a⌝))
where
  from_exists := by
    rw' [pure_exists]

instance fromExistsAffinely [BI PROP] (P : PROP) (Φ : α → PROP) :
  [FromExists P Φ] →
  FromExists iprop(<affine> P) (fun a => iprop(<affine> (Φ a)))
where
  from_exists := by
    rw' [← FromExists.from_exists, ← affinely_exists]

instance fromExistsIntuitionistically [BI PROP] (P : PROP) (Φ : α → PROP) :
  [FromExists P Φ] →
  FromExists iprop(□ P) (fun a => iprop(□ (Φ a)))
where
  from_exists := by
    rw' [← FromExists.from_exists, ← intuitionistically_exists]

instance fromExistsAbsorbingly [BI PROP] (P : PROP) (Φ : α → PROP) :
  [FromExists P Φ] →
  FromExists iprop(<absorb> P) (fun a => iprop(<absorb> (Φ a)))
where
  from_exists := by
    rw' [← FromExists.from_exists, ← absorbingly_exists]

instance from_exists_persistently [BI PROP] (P : PROP) (Φ : α → PROP) :
  [FromExists P Φ] →
  FromExists iprop(<pers> P) (fun a => iprop(<pers> (Φ a)))
where
  from_exists := by
    rw' [← FromExists.from_exists, ← persistently_exists]

-- IntoExists
instance into_exists_exists [BI PROP] (Φ : α → PROP) :
  IntoExists (BIBase.exists Φ) Φ
where
  into_exists := by
    simp

instance into_exists_pure (φ : α → Prop) [BI PROP] :
  IntoExists (PROP := PROP) iprop(⌜∃ x, φ x⌝) (fun a => iprop(⌜φ a⌝))
where
  into_exists := by
    rw' [pure_exists]

instance into_exists_affinely [BI PROP] (P : PROP) (Φ : α → PROP) :
  [IntoExists P Φ] →
  IntoExists iprop(<affine> P) (fun a => iprop(<affine> (Φ a)))
where
  into_exists := by
    rw' [← affinely_exists, into_exists]

instance into_exists_intuitionistically [BI PROP] (P : PROP) (Φ : α → PROP) :
  [IntoExists P Φ] →
  IntoExists iprop(□ P) (fun a => iprop(□ (Φ a)))
where
  into_exists := by
    rw' [← intuitionistically_exists, into_exists]

instance into_exists_absorbingly [BI PROP] (P : PROP) (Φ : α → PROP) :
  [IntoExists P Φ] →
  IntoExists iprop(<absorb> P) (fun a => iprop(<absorb> (Φ a)))
where
  into_exists := by
    rw' [← absorbingly_exists, into_exists]

instance into_exists_persistently [BI PROP] {P : PROP} (Φ : α → PROP) :
  [IntoExists P Φ] →
  IntoExists iprop(<pers> P) (fun a => iprop(<pers> (Φ a)))
where
  into_exists := by
    rw' [← persistently_exists, into_exists]

-- FromAnd
instance (priority := default - 10) fromAndAnd [BI PROP] (P1 P2 : PROP) :
  FromAnd iprop(P1 ∧ P2) P1 P2
where
  from_and := by
    simp

instance (priority := default + 30) fromAndSepPersistentL [BI PROP] (P1 P1' P2 : PROP) :
  [Persistent P1] →
  [IntoAbsorbingly P1' P1] →
  FromAnd iprop(P1 ∗ P2) P1' P2
where
  from_and := by
    rw' [
      (IntoAbsorbingly.into_absorbingly : _ ⊢ <absorb> P1),
      persistent_and_affinely_sep_l,
      (persistent : P1 ⊢ _),
      absorbingly_persistently,
      intuitionistically_elim]

instance (priority := default + 20) fromAndSepPersistentR [BI PROP] (P1 P2 P2' : PROP) :
  [Persistent P2] →
  [IntoAbsorbingly P2' P2] →
  FromAnd iprop(P1 ∗ P2) P1 P2'
where
  from_and := by
    rw' [
      (IntoAbsorbingly.into_absorbingly : _ ⊢ <absorb> P2),
      persistent_and_affinely_sep_r,
      (persistent : P2 ⊢ _),
      absorbingly_persistently,
      intuitionistically_elim]

instance (priority := default + 50) fromAndPure (φ ψ : Prop) [BI PROP] :
  FromAnd (PROP := PROP) iprop(⌜φ ∧ ψ⌝) iprop(⌜φ⌝) iprop(⌜ψ⌝)
where
  from_and := by
    rw' [pure_and]

instance (priority := default + 40) fromAndPersistently [BI PROP] (P Q1 Q2 : PROP) :
  [FromAnd P Q1 Q2] →
  FromAnd iprop(<pers> P) iprop(<pers> Q1) iprop(<pers> Q2)
where
  from_and := by
    rw' [← FromAnd.from_and, persistently_and]

instance (priority := default + 10) fromAndPersistentlySep [BI PROP] (P Q1 Q2 : PROP) :
  [FromSep P Q1 Q2] →
  FromAnd iprop(<pers> P) iprop(<pers> Q1) iprop(<pers> Q2)
where
  from_and := by
    rw' [
      ← FromSep.from_sep,
      ← persistently_and,
      persistently_and_sep]

-- IntoAnd
instance (priority := default - 10) intoAndAnd (p : Bool) [BI PROP] (P Q : PROP) :
  IntoAnd p iprop(P ∧ Q) P Q
where
  into_and := by
    rw' [intuitionisticallyIf_and]

instance intoAndAndAffineL [BI PROP] (P Q Q' : PROP) :
  [Affine P] →
  [FromAffinely Q' Q] →
  IntoAnd false iprop(P ∧ Q) P Q'
where
  into_and := by
    rw' [
      ← affine_affinely P,
      affinely_and_l,
      affinely_and,
      ← (FromAffinely.from_affinely : <affine>?true Q ⊢ _)]

instance intoAndAndAffineR [BI PROP] (P P' Q : PROP) :
  [Affine Q] →
  [FromAffinely P' P] →
  IntoAnd false iprop(P ∧ Q) P' Q
where
  into_and := by
    rw' [
      ← affine_affinely Q,
      affinely_and_r,
      affinely_and,
      ← (FromAffinely.from_affinely : <affine>?true P ⊢ _)]

instance intoAndSepAffine (p : Bool) [BI PROP] (P Q : PROP) :
  [TCOr (Affine P) (Absorbing Q)] →
  [TCOr (Absorbing P) (Affine Q)] →
  IntoAnd p iprop(P ∗ Q) P Q
where
  into_and := by
    cases p
    <;> rw' [sep_and]

instance intoAndPure (p : Bool) (φ ψ : Prop) [BI PROP] :
  IntoAnd (PROP := PROP) p iprop(⌜φ ∧ ψ⌝) iprop(⌜φ⌝) iprop(⌜ψ⌝)
where
  into_and := by
    rw' [pure_and]

instance intoAndAffinely (p : Bool) [BI PROP] (P Q1 Q2 : PROP) :
  [IntoAnd p P Q1 Q2] →
  IntoAnd p iprop(<affine> P) iprop(<affine> Q1) iprop(<affine> Q2)
where
  into_and := by
    cases p
    case false =>
      rw' [
        ← affinely_and,
        (IntoAnd.into_and : □?false P ⊢ _)]
    case true =>
      simp only [intuitionisticallyIf]
      rw' [
        ← affinely_and,
        !intuitionistically_affinely,
        (IntoAnd.into_and : □?true P ⊢ _)]

instance intoAndIntuitionistically (p : Bool) [BI PROP] (P Q1 Q2 : PROP) :
  [IntoAnd p P Q1 Q2] →
  IntoAnd p iprop(□ P) iprop(□ Q1) iprop(□ Q2)
where
  into_and := by
    cases p
    case false =>
      rw' [
        ← intuitionistically_and,
        (IntoAnd.into_and : □?false P ⊢ _)]
    case true =>
      simp only [intuitionisticallyIf]
      rw' [
        intuitionistically_and,
        !intuitionistically_idem,
        ← intuitionistically_and,
        (IntoAnd.into_and : □?true P ⊢ _)]

instance intoAndPersistently (p : Bool) [BI PROP] (P Q1 Q2 : PROP) :
  [IntoAnd p P Q1 Q2] →
  IntoAnd p iprop(<pers> P) iprop(<pers> Q1) iprop(<pers> Q2)
where
  into_and := by
    cases p
    case false =>
      rw' [
        ← persistently_and,
        (IntoAnd.into_and : □?false P ⊢ _)]
    case true =>
      simp only [intuitionisticallyIf]
      rw' [
        ← persistently_and,
        !intuitionistically_persistently,
        (IntoAnd.into_and : □?true P ⊢ _)]

-- FromSep
instance (priority := default - 10) fromSepSep [BI PROP] (P1 P2 : PROP) :
  FromSep iprop(P1 ∗ P2) P1 P2
where
  from_sep := by
    simp

instance (priority := default - 20) fromSepAnd [BI PROP] (P1 P2 : PROP) :
  [TCOr (Affine P1) (Absorbing P2)] →
  [TCOr (Absorbing P1) (Affine P2)] →
  FromSep iprop(P1 ∧ P2) P1 P2
where
  from_sep := sep_and

instance (priority := default + 20) fromSepPure (φ ψ : Prop) [BI PROP] :
  FromSep (PROP := PROP) iprop(⌜φ ∧ ψ⌝) iprop(⌜φ⌝) iprop(⌜ψ⌝)
where
  from_sep := by
    rw' [pure_and, sep_and]

instance (priority := default + 10) fromSepAffinely [BI PROP] (P Q1 Q2 : PROP) :
  [FromSep P Q1 Q2] →
  FromSep iprop(<affine> P) iprop(<affine> Q1) iprop(<affine> Q2)
where
  from_sep := by
    rw' [← FromSep.from_sep, affinely_sep_2]

instance (priority := default + 10) fromSepIntuitionistically [BI PROP] (P Q1 Q2 : PROP) :
  [FromSep P Q1 Q2] →
  FromSep iprop(□ P) iprop(□ Q1) iprop(□ Q2)
where
  from_sep := by
    rw' [← FromSep.from_sep, intuitionistically_sep_2]

instance (priority := default + 10) fromSepAbsorbingly [BI PROP] (P Q1 Q2 : PROP) :
  [FromSep P Q1 Q2] →
  FromSep iprop(<absorb> P) iprop(<absorb> Q1) iprop(<absorb> Q2)
where
  from_sep := by
    rw' [← FromSep.from_sep, absorbingly_sep]

instance (priority := default + 10) fromSepPersistently [BI PROP] (P Q1 Q2 : PROP) :
  [FromSep P Q1 Q2] →
  FromSep iprop(<pers> P) iprop(<pers> Q1) iprop(<pers> Q2)
where
  from_sep := by
    rw' [← FromSep.from_sep, persistently_sep_2]

-- AndIntoSep
inductive AndIntoSep [BI PROP] : PROP → PROP → PROP → PROP → Prop
  | and_into_sep_affine (P Q Q' : PROP) : Affine P → FromAffinely Q' Q → AndIntoSep P P Q Q'
  | and_into_sep (P Q : PROP) : AndIntoSep P iprop(<affine> P) Q Q

attribute [class] AndIntoSep
attribute [instance] AndIntoSep.and_into_sep_affine
attribute [instance] AndIntoSep.and_into_sep

-- IntoSep
instance intoSepSep [BI PROP] (P Q : PROP) :
  IntoSep iprop(P ∗ Q) P Q
where
  into_sep := by
    simp

set_option synthInstance.checkSynthOrder false in
instance intoSepAndPersistentL [BI PROP] (P Q P' Q' : PROP)
  [Persistent P]
  [inst : AndIntoSep P P' Q Q'] :
  IntoSep iprop(P ∧ Q) P' Q'
where
  into_sep := by
    cases inst
    case and_into_sep_affine =>
      rw' [
        ← (FromAffinely.from_affinely : <affine>?true Q ⊢ _),
        ← affine_affinely P,
        affinely_and_lr,
        persistent_and_affinely_sep_l_1]
    case and_into_sep =>
      rw' [persistent_and_affinely_sep_l_1]

set_option synthInstance.checkSynthOrder false in
instance intoSepAndPersistentR [BI PROP] (P Q P' Q' : PROP)
  [Persistent Q]
  [inst : AndIntoSep Q Q' P P'] :
  IntoSep iprop(P ∧ Q) P' Q'
where
  into_sep := by
    cases inst
    case and_into_sep_affine =>
      rw' [
        ← (FromAffinely.from_affinely : <affine>?true P ⊢ _),
        ← affine_affinely Q,
        ← affinely_and_lr,
        persistent_and_affinely_sep_r_1]
    case and_into_sep =>
      rw' [persistent_and_affinely_sep_r_1]

instance intoSepPure (φ ψ : Prop) [BI PROP] :
  IntoSep (PROP := PROP) iprop(⌜φ ∧ ψ⌝) iprop(⌜φ⌝) iprop(⌜ψ⌝)
where
  into_sep := by
    rw' [pure_and, persistent_and_sep_1]

-- Coq: This instance is kind of strange, it just gets rid of the affinely.
instance (priority := default - 10) intoSepAffinelyTrim [BI PROP] (P Q1 Q2 : PROP) :
  [IntoSep P Q1 Q2] →
  IntoSep iprop(<affine> P) Q1 Q2
where
  into_sep := by
    rw' [IntoSep.into_sep, affinely_elim]

instance intoSepPersistentlyAffine [BI PROP] (P Q1 Q2 : PROP) :
  [IntoSep P Q1 Q2] →
  [TCOr (Affine Q1) (Absorbing Q2)] →
  [TCOr (Absorbing Q1) (Affine Q2)] →
  IntoSep iprop(<pers> P) iprop(<pers> Q1) iprop(<pers> Q2)
where
  into_sep := by
    rw' [IntoSep.into_sep, sep_and, persistently_and, persistently_and_imp_sep]

instance intoSepIntuitionisticallyAffine [BI PROP] (P Q1 Q2 : PROP) :
  [IntoSep P Q1 Q2] →
  [TCOr (Affine Q1) (Absorbing Q2)] →
  [TCOr (Absorbing Q1) (Affine Q2)] →
  IntoSep iprop(□ P) iprop(□ Q1) iprop(□ Q2)
where
  into_sep := by
    rw' [
      IntoSep.into_sep,
      sep_and,
      intuitionistically_and,
      and_sep_intuitionistically]

-- FromOr
instance fromOrOr [BI PROP] (P1 P2 : PROP) :
  FromOr iprop(P1 ∨ P2) P1 P2
where
  from_or := by
    simp

instance fromOrPure (φ ψ : Prop) [BI PROP] :
  FromOr (PROP := PROP) iprop(⌜φ ∨ ψ⌝) iprop(⌜φ⌝) iprop(⌜ψ⌝)
where
  from_or := by
    rw' [pure_or]

instance fromOrAffinely [BI PROP] (P Q1 Q2 : PROP) :
  [FromOr P Q1 Q2] →
  FromOr iprop(<affine> P) iprop(<affine> Q1) iprop(<affine> Q2)
where
  from_or := by
    rw' [← FromOr.from_or, ← affinely_or]

instance fromOrIntuitionistically [BI PROP] (P Q1 Q2 : PROP) :
  [FromOr P Q1 Q2] →
  FromOr iprop(□ P) iprop(□ Q1) iprop(□ Q2)
where
  from_or := by
    rw' [← FromOr.from_or, ← intuitionistically_or]

instance fromOrAbsorbingly [BI PROP] (P Q1 Q2 : PROP) :
  [FromOr P Q1 Q2] →
  FromOr iprop(<absorb> P) iprop(<absorb> Q1) iprop(<absorb> Q2)
where
  from_or := by
    rw' [← FromOr.from_or, ← absorbingly_or]

instance fromOrPersistently [BI PROP] (P Q1 Q2 : PROP) :
  [FromOr P Q1 Q2] →
  FromOr iprop(<pers> P) iprop(<pers> Q1) iprop(<pers> Q2)
where
  from_or := by
    rw' [← FromOr.from_or, ← persistently_or]

-- IntoOr
instance intoOrOr [BI PROP] (P Q : PROP) :
  IntoOr iprop(P ∨ Q) P Q
where
  into_or := by
    simp

instance intoOrPure (φ ψ : Prop) [BI PROP] :
  IntoOr (PROP := PROP) iprop(⌜φ ∨ ψ⌝) iprop(⌜φ⌝) iprop(⌜ψ⌝)
where
  into_or := by
    rw' [pure_or]

instance intoOrAffinely [BI PROP] (P Q1 Q2 : PROP) :
  [IntoOr P Q1 Q2] →
  IntoOr iprop(<affine> P) iprop(<affine> Q1) iprop(<affine> Q2)
where
  into_or := by
    rw' [IntoOr.into_or, ← affinely_or]

instance intoOrIntuitionistically [BI PROP] (P Q1 Q2 : PROP) :
  [IntoOr P Q1 Q2] →
  IntoOr iprop(□ P) iprop(□ Q1) iprop(□ Q2)
where
  into_or := by
    rw' [IntoOr.into_or, ← intuitionistically_or]

instance intoOrAbsorbingly [BI PROP] (P Q1 Q2 : PROP) :
  [IntoOr P Q1 Q2] →
  IntoOr iprop(<absorb> P) iprop(<absorb> Q1) iprop(<absorb> Q2)
where
  into_or := by
    rw' [IntoOr.into_or, ← absorbingly_or]

instance intoOrPersistently [BI PROP] (P Q1 Q2 : PROP) :
  [IntoOr P Q1 Q2] →
  IntoOr iprop(<pers> P) iprop(<pers> Q1) iprop(<pers> Q2)
where
  into_or := by
    rw' [IntoOr.into_or, ← persistently_or]

-- IntoPersistent
instance (priority := default + 20) intoPersistentPersistently (p : Bool) [BI PROP] (P Q : PROP) :
  [IntoPersistent true P Q] →
  IntoPersistent p iprop(<pers> P) Q
where
  into_persistent := by
    cases p
    case false =>
      exact (IntoPersistent.into_persistent : <pers>?true P ⊢ _)
    case true =>
      rw' [(IntoPersistent.into_persistent : <pers>?true P ⊢ _)]
      simp only [persistentlyIf]
      rw' [persistently_idem]

instance (priority := default + 20) intoPersistentAffinely (p : Bool) [BI PROP] (P Q : PROP) :
  [IntoPersistent p P Q] →
  IntoPersistent p iprop(<affine> P) Q
where
  into_persistent := by
    rw' [
      ← (IntoPersistent.into_persistent : <pers>?p P ⊢ _),
      affinely_elim]

instance (priority := default + 20) intoPersistentIntuitionistically (p : Bool) [BI PROP] (P Q : PROP) :
  [IntoPersistent true P Q] →
  IntoPersistent p iprop(□ P) Q
where
  into_persistent := by
    rw' [← (IntoPersistent.into_persistent : <pers>?true P ⊢ _)]
    cases p
    case false =>
      exact persistently_of_intuitionistically
    case true =>
      apply persistentlyIf_mono
      exact intuitionistically_elim

instance (priority := default + 10) intoPersistentHere [BI PROP] (P : PROP) :
  IntoPersistent true P P
where
  into_persistent := by
    simp [persistentlyIf]

instance (priority := default - 10) intoPersistentPersistent [BI PROP] (P : PROP) :
  [Persistent P] →
  IntoPersistent false P P
where
  into_persistent := by
    rw' [persistent]

-- FromAffinely
instance fromAffinelyAffine [BI PROP] (P : PROP) :
  [Affine P] →
  FromAffinely P P true
where
  from_affinely := by
    rw' [affinely_elim]

instance (priority := default - 50) fromAffinelyDefault [BI PROP] (P : PROP) :
  FromAffinely iprop(<affine> P) P true
where
  from_affinely := by
    simp [affinelyIf]

instance (priority := default - 10) fromAffinelyIntuitionistically [BI PROP] (P : PROP) :
  FromAffinely iprop(□ P) iprop(<pers> P) true
where
  from_affinely := by
    simp [affinelyIf, intuitionistically]

instance fromAffinelyId [BI PROP] (P : PROP) :
  FromAffinely P P false
where
  from_affinely := by
    simp [affinelyIf]

-- IntoAbsorbingly
instance (priority := default + 30) intoAbsorbinglyTrue [BI PROP] :
  IntoAbsorbingly (PROP := PROP) iprop(True) iprop(emp)
where
  into_absorbingly := by
    rw' [← absorbingly_true_emp, absorbingly_pure]

instance (priority := default + 20) intoAbsorbinglyAbsorbing [BI PROP] (P : PROP) :
  [Absorbing P] →
  IntoAbsorbingly P P
where
  into_absorbingly := by
    rw' [absorbing_absorbingly]

instance (priority := default + 10) intoAbsorbinglyIntuitionistically [BI PROP] (P : PROP) :
  IntoAbsorbingly iprop(<pers> P) iprop(□ P)
where
  into_absorbingly := by
    rw' [← absorbingly_intuitionistically]

instance (priority := default - 10) intoAbsorbinglyDefault [BI PROP] (P : PROP) :
  IntoAbsorbingly iprop(<absorb> P) P
where
  into_absorbingly := by
    simp

-- FromAssumption
instance (priority := default + 100) fromAssumptionExact (p : Bool) [BI PROP] (P : PROP) :
  FromAssumption p P P
where
  from_assumption := by
    cases p
    <;> simp [intuitionisticallyIf, intuitionistically_elim]

instance (priority := default + 30) fromAssumptionPersistentlyR [BI PROP] (P Q : PROP) :
  [FromAssumption true P Q] →
  FromAssumption true P iprop(<pers> Q)
where
  from_assumption := by
    rw' [← (FromAssumption.from_assumption : □?true P ⊢ Q)]
    simp [intuitionisticallyIf, persistent]

instance (priority := default + 30) fromAssumptionAffinelyR [BI PROP] (P Q : PROP) :
  [FromAssumption true P Q] →
  FromAssumption true P iprop(<affine> Q)
where
  from_assumption := by
    rw' [← (FromAssumption.from_assumption : □?true P ⊢ Q)]
    simp only [intuitionisticallyIf, ite_true, intuitionistically]
    rw' [affinely_idem]

instance (priority := default + 30) fromAssumptionIntuitionisticallyR [BI PROP] (P Q : PROP) :
  [FromAssumption true P Q] →
  FromAssumption true P iprop(□ Q)
where
  from_assumption := by
    rw' [← (FromAssumption.from_assumption : □?true P ⊢ Q)]
    simp only [intuitionisticallyIf, ite_true]
    rw' [intuitionistically_idem]

instance (priority := default + 20) fromAssumptionAbsorbinglyR (p : Bool) [BI PROP] (P Q : PROP) :
  [FromAssumption p P Q] →
  FromAssumption p P iprop(<absorb> Q)
where
  from_assumption := by
    rw' [← (FromAssumption.from_assumption : □?p P ⊢ Q)]
    exact absorbingly_intro

instance (priority := default + 20) fromAssumptionIntuitionisticallyL (p : Bool) [BI PROP] (P Q : PROP) :
  [FromAssumption true P Q] →
  FromAssumption p iprop(□ P) Q
where
  from_assumption := by
    rw' [
      ← (FromAssumption.from_assumption : □?true P ⊢ Q),
      intuitionisticallyIf_elim]

instance (priority := default + 20) fromAssumptionIntuitionisticallyLTrue (p : Bool) [BI PROP] (P Q : PROP) :
  [FromAssumption p P Q] →
  FromAssumption p iprop(□ P) Q
where
  from_assumption := by
    rw' [
      ← (FromAssumption.from_assumption : □?p P ⊢ Q),
      intuitionistically_elim]

instance (priority := default + 30) FromAssumptionPersistentlyLTrue [BI PROP] (P Q : PROP) :
  [FromAssumption true P Q] →
  FromAssumption true iprop(<pers> P) Q
where
  from_assumption := by
    simp only [intuitionisticallyIf]
    rw' [
      ← (FromAssumption.from_assumption : □?true P ⊢ Q),
      intuitionistically_persistently]

instance (priority := default + 30) fromAssumptionPersistentlyLFalse [BIAffine PROP] (P Q : PROP) :
  [FromAssumption true P Q] →
  FromAssumption false iprop(<pers> P) Q
where
  from_assumption := by
    rw' [← (FromAssumption.from_assumption : □?true P ⊢ Q)]
    simp only [intuitionisticallyIf, ite_true, ite_false]
    rw' [intuitionistically_iff_persistently]

instance (priority := default + 20) fromAssumptionAffinelyL (p : Bool) [BI PROP] (P Q : PROP) :
  [FromAssumption p P Q] →
  FromAssumption p iprop(<affine> P) Q
where
  from_assumption := by
    rw' [
      ← (FromAssumption.from_assumption : □?p P ⊢ Q),
      affinely_elim]

set_option synthInstance.checkSynthOrder false in
instance (priority := default + 10) fromAssumptionForall (p : Bool) [BI PROP] (Φ : α → PROP) (x : α) (Q : PROP) :
  [FromAssumption p (Φ x) Q] →
  FromAssumption p iprop(∀ x, Φ x) Q
where
  from_assumption := by
    rw' [
      ← (FromAssumption.from_assumption : □?p (Φ x) ⊢ Q),
      BI.forall_elim x]

-- IntoPure
instance intoPurePure (φ : Prop) [BI PROP] :
  IntoPure (PROP := PROP) iprop(⌜φ⌝) φ
where
  into_pure := by
    simp

instance intoPurePureAnd (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [IntoPure P1 φ1] →
  [IntoPure P2 φ2] →
  IntoPure iprop(P1 ∧ P2) (φ1 ∧ φ2)
where
  into_pure := by
    rw' [
      pure_and,
      (IntoPure.into_pure : P1 ⊢ _),
      (IntoPure.into_pure : P2 ⊢ _)]

instance intoPurePureOr (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [IntoPure P1 φ1] →
  [IntoPure P2 φ2] →
  IntoPure iprop(P1 ∨ P2) (φ1 ∨ φ2)
where
  into_pure := by
    rw' [
      pure_or,
      (IntoPure.into_pure : P1 ⊢ _),
      (IntoPure.into_pure : P2 ⊢ _)]

instance intoPureExists [BI PROP] (Φ : α → PROP) (φ : α → Prop) :
  [∀ x, IntoPure (Φ x) (φ x)] →
  IntoPure iprop(∃ x, Φ x) (∃ x, φ x)
where
  into_pure := by
    rw' [IntoPure.into_pure, pure_exists]

instance intoPurePureSep (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [IntoPure P1 φ1] →
  [IntoPure P2 φ2] →
  IntoPure iprop(P1 ∗ P2) (φ1 ∧ φ2)
where
  into_pure := by
    rw' [
      (IntoPure.into_pure : P1 ⊢ _),
      (IntoPure.into_pure : P2 ⊢ _),
      sep_and,
      pure_and]

instance intoPureAffinely [BI PROP] (P : PROP) (φ : Prop) :
  [IntoPure P φ] →
  IntoPure iprop(<affine> P) φ
where
  into_pure := by
    rw' [IntoPure.into_pure, affinely_elim]

instance intoPureIntuitionistically [BI PROP] (P : PROP) (φ : Prop) :
  [IntoPure P φ] →
  IntoPure iprop(□ P) φ
where
  into_pure := by
    rw' [IntoPure.into_pure, intuitionistically_elim]

instance intoPureAbsorbingly [BI PROP] (P : PROP) (φ : Prop) :
  [IntoPure P φ] →
  IntoPure iprop(<absorb> P) φ
where
  into_pure := by
    rw' [(IntoPure.into_pure : P ⊢ _), absorbingly_pure]

instance intoPurePersistently [BI PROP] (P : PROP) (φ : Prop) :
  [IntoPure P φ] →
  IntoPure iprop(<pers> P) φ
where
  into_pure := by
    rw' [IntoPure.into_pure, persistently_elim]

-- FromPure
instance fromPureEmp [BI PROP] :
  FromPure (PROP := PROP) true iprop(emp) True
where
  from_pure := by
    simp only [affinelyIf, ite_true]
    rw' [affine]

instance fromPurePure [BI PROP] (φ : Prop) :
  FromPure (PROP := PROP) false iprop(⌜φ⌝) φ
where
  from_pure := by
    simp [affinelyIf]

instance fromPurePureAnd (a1 a2 : Bool) (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [FromPure a1 P1 φ1] →
  [FromPure a2 P2 φ2] →
  FromPure (a1 || a2) iprop(P1 ∧ P2) (φ1 ∧ φ2)
where
  from_pure := by
    rw' [
      pure_and,
      ← (FromPure.from_pure : _ ⊢ P1),
      ← (FromPure.from_pure : _ ⊢ P2),
      affinelyIf_and]
    apply and_mono
    <;> apply affinelyIf_flag_mono
    <;> simp_all

instance fromPurePureOr (a1 a2 : Bool) (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [FromPure a1 P1 φ1] →
  [FromPure a2 P2 φ2] →
  FromPure (a1 || a2) iprop(P1 ∨ P2) (φ1 ∨ φ2)
where
  from_pure := by
    rw' [
      pure_or,
      ← (FromPure.from_pure : _ ⊢ P1),
      ← (FromPure.from_pure : _ ⊢ P2),
      affinelyIf_or]
    apply or_mono
    <;> apply affinelyIf_flag_mono
    <;> simp_all

instance fromPurePureImp (a : Bool) (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [IntoPure P1 φ1] →
  [FromPure a P2 φ2] →
  FromPure a iprop(P1 → P2) (φ1 → φ2)
where
  from_pure := by
    rw' [
      ← IntoPure.into_pure,
      ← FromPure.from_pure,
      pure_imp_2]
    cases a
    <;> simp [affinelyIf]
    apply BI.imp_intro'
    rw' [affinely_and_r, BI.imp_elim_r]

instance fromPureExists (a : Bool) [BI PROP] (Φ : α → PROP) (φ : α → Prop) :
  [∀ x, FromPure a iprop(Φ x) (φ x)] →
  FromPure a iprop(∃ x, Φ x) (∃ x, φ x)
where
  from_pure := by
    rw' [← FromPure.from_pure, pure_exists, affinelyIf_exists]

instance fromPureForall (a : Bool) [BI PROP] (Φ : α → PROP) (φ : α → Prop) :
  [∀ x, FromPure a iprop(Φ x) (φ x)] →
  FromPure a iprop(∀ x, Φ x) (∀ x, φ x)
where
  from_pure := by
    rw' [← FromPure.from_pure, pure_forall_2]
    cases a
    <;> simp [affinelyIf, affinely_forall]

instance fromPurePureSepTrue (a1 a2 : Bool) (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [FromPure a1 P1 φ1] →
  [FromPure a2 P2 φ2] →
  FromPure (a1 && a2) iprop(P1 ∗ P2) (φ1 ∧ φ2)
where
  from_pure := by
    rw' [
      ← (FromPure.from_pure : _ ⊢ P1),
      ← (FromPure.from_pure : _ ⊢ P2)]
    cases a1
    <;> cases a2
    <;> simp only [affinelyIf]
    <;> rw' [pure_and]
    · rw' [persistent_and_sep_1]
    · rw' [persistent_and_affinely_sep_r]
    · rw' [persistent_and_affinely_sep_l]
    · rw' [affinely_and, persistent_and_sep_1]

instance fromPurePureWand (a : Bool) (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP)
  [IntoPure P1 φ1]
  [FromPure a P2 φ2]
  [inst : TCIte a (Affine P1) TCTrue] :
  FromPure a iprop(P1 -∗ P2) (φ1 → φ2)
where
  from_pure := by
    rw' [← FromPure.from_pure]
    apply BI.wand_intro'
    cases a
    <;> simp only [affinelyIf, ite_true, ite_false]
    <;> cases inst
    case a.false.e =>
      rw' [IntoPure.into_pure, pure_and, pure_imp_2, imp_elim_r]
    case a.true.t =>
      rw' [
        ← persistent_and_affinely_sep_r,
        ← affine_affinely P1,
        (IntoPure.into_pure : P1 ⊢ _),
        affinely_and_l,
        pure_imp_2,
        imp_elim_r]

set_option synthInstance.checkSynthOrder false in
instance fromPurePersistently [BI PROP] (P : PROP) (a : Bool) (φ : Prop) :
  [FromPure true P φ] →
  FromPure a iprop(<pers> P) φ
where
  from_pure := by
    rw' [← FromPure.from_pure]
    conv =>
      rhs
      simp only [affinelyIf, ite_true]
    rw' [
      persistently_affinely_elim,
      affinelyIf_elim,
      persistently_pure]

instance fromPureAffinelyTrue (a : Bool) [BI PROP] (P : PROP) (φ : Prop) :
  [FromPure a P φ] →
  FromPure true iprop(<affine> P) φ
where
  from_pure := by
    rw' [
      ← (FromPure.from_pure : _ ⊢ P),
      ← affinely_affinelyIf,
      affinely_idem]

instance fromPureIntuitionisticallyTrue (a : Bool) [BI PROP] (P : PROP) (φ : Prop) :
  [FromPure a P φ] →
  FromPure true iprop(□ P) φ
where
  from_pure := by
    rw' [
      ← (FromPure.from_pure : _ ⊢ P),
      ← intuitionistically_affinely,
      ← affinely_affinelyIf,
      affinely_idem,
      intuitionistically_of_intuitionistic]

instance fromPureAbsorbingly (a : Bool) [BI PROP] (P : PROP) (φ : Prop) :
  [FromPure a P φ] →
  FromPure false iprop(<absorb> P) φ
where
  from_pure := by
    rw' [
      ← (FromPure.from_pure : _ ⊢ P),
      ← affinely_affinelyIf,
      ← absorbingly_affinely_intro_of_persistent]

end Iris.Proofmode
