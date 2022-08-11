import Iris.BI
import Iris.Proofmode.Classes
import Iris.Std.TC

namespace Iris.Proofmode
open Iris.BI Iris.Std

-- AsEmpValid
instance (priority := default + 10) asEmpValidEmpValid [bi : BI PROP] (P : PROP) :
  AsEmpValid (⊢ P) P
where
  bi := bi
  as_emp_valid := by
    simp

instance asEmpValidEntails [bi : BI PROP] (P Q : PROP) :
  AsEmpValid (P ⊢ Q) `[iprop| P -∗ Q]
where
  bi := bi
  as_emp_valid := by
    constructor
    · exact entails_wand
    · exact wand_entails

instance asEmpValidEquiv [bi : BI PROP] (P Q : PROP) :
  AsEmpValid (P ⊣⊢ Q) `[iprop| P ∗-∗ Q]
where
  bi := bi
  as_emp_valid := by
    constructor
    · exact equiv_wand_iff
    · exact wand_iff_equiv

-- FromImpl
instance fromImplImpl [BI PROP] (P1 P2 : PROP) :
  FromImpl `[iprop| P1 → P2] P1 P2
where
  from_impl := by
    simp

-- FromWand
instance fromWandWand [BI PROP] (P1 P2 : PROP) :
  FromWand `[iprop| P1 -∗ P2] P1 P2
where
  from_wand := by
    simp

-- FromForall
instance fromForallForall [BI PROP] (Φ : α → PROP) :
  FromForall (BIBase.forall Φ) Φ
where
  from_forall := by
    simp

-- FromExist
instance (priority := default + 10) fromExistExist [BI PROP] (Φ : α → PROP) :
  FromExist `[iprop| ∃ a, Φ a] Φ
where
  from_exist := by
    simp

instance fromExistPure (φ : α → Prop) [BI PROP] :
  FromExist (PROP := PROP) `[iprop| ⌜∃ x, φ x⌝] (fun a => `[iprop| ⌜φ a⌝])
where
  from_exist := by
    rw' [pure_exist]

instance fromExistAffinely [BI PROP] (P : PROP) (Φ : α → PROP) :
  [FromExist P Φ] →
  FromExist `[iprop| <affine> P] (fun a => `[iprop| <affine> (Φ a)])
where
  from_exist := by
    rw' [← FromExist.from_exist, ← affinely_exist]

instance fromExistIntuitionistically [BI PROP] (P : PROP) (Φ : α → PROP) :
  [FromExist P Φ] →
  FromExist `[iprop| □ P] (fun a => `[iprop| □ (Φ a)])
where
  from_exist := by
    rw' [← FromExist.from_exist, ← intuitionistically_exist]

instance fromExistAbsorbingly [BI PROP] (P : PROP) (Φ : α → PROP) :
  [FromExist P Φ] →
  FromExist `[iprop| <absorb> P] (fun a => `[iprop| <absorb> (Φ a)])
where
  from_exist := by
    rw' [← FromExist.from_exist, ← absorbingly_exist]

instance from_exist_persistently [BI PROP] (P : PROP) (Φ : α → PROP) :
  [FromExist P Φ] →
  FromExist `[iprop| <pers> P] (fun a => `[iprop| <pers> (Φ a)])
where
  from_exist := by
    rw' [← FromExist.from_exist, ← persistently_exist]

-- IntoExist
instance into_exist_exist [BI PROP] (Φ : α → PROP) :
  IntoExist (BIBase.exists Φ) Φ
where
  into_exist := by
    simp

instance into_exist_pure (φ : α → Prop) [BI PROP] :
  IntoExist (PROP := PROP) `[iprop| ⌜∃ x, φ x⌝] (fun a => `[iprop| ⌜φ a⌝])
where
  into_exist := by
    rw' [pure_exist]

instance into_exist_affinely [BI PROP] (P : PROP) (Φ : α → PROP) :
  [IntoExist P Φ] →
  IntoExist `[iprop| <affine> P] (fun a => `[iprop| <affine> (Φ a)])
where
  into_exist := by
    rw' [← affinely_exist, into_exist]

instance into_exist_intuitionistically [BI PROP] (P : PROP) (Φ : α → PROP) :
  [IntoExist P Φ] →
  IntoExist `[iprop| □ P] (fun a => `[iprop| □ (Φ a)])
where
  into_exist := by
    rw' [← intuitionistically_exist, into_exist]

instance into_exist_absorbingly [BI PROP] (P : PROP) (Φ : α → PROP) :
  [IntoExist P Φ] →
  IntoExist `[iprop| <absorb> P] (fun a => `[iprop| <absorb> (Φ a)])
where
  into_exist := by
    rw' [← absorbingly_exist, into_exist]

instance into_exist_persistently [BI PROP] {P : PROP} (Φ : α → PROP) :
  [IntoExist P Φ] →
  IntoExist `[iprop| <pers> P] (fun a => `[iprop| <pers> (Φ a)])
where
  into_exist := by
    rw' [← persistently_exist, into_exist]

-- FromAnd
instance (priority := default - 10) fromAndAnd [BI PROP] (P1 P2 : PROP) :
  FromAnd `[iprop| P1 ∧ P2] P1 P2
where
  from_and := by
    simp

instance (priority := default + 30) fromAndSepPersistentL [BI PROP] (P1 P1' P2 : PROP) :
  [Persistent P1] →
  [IntoAbsorbingly P1' P1] →
  FromAnd `[iprop| P1 ∗ P2] P1' P2
where
  from_and := by
    rw' [
      (IntoAbsorbingly.into_absorbingly : _ ⊢ <absorb> P1),
      persistent_and_affinely_sep_l,
      (persistent : P1 ⊢ _),
      absorbingly_elim_persistently,
      intuitionistically_elim]

instance (priority := default + 20) fromAndSepPersistentR [BI PROP] (P1 P2 P2' : PROP) :
  [Persistent P2] →
  [IntoAbsorbingly P2' P2] →
  FromAnd `[iprop| P1 ∗ P2] P1 P2'
where
  from_and := by
    rw' [
      (IntoAbsorbingly.into_absorbingly : _ ⊢ <absorb> P2),
      persistent_and_affinely_sep_r,
      (persistent : P2 ⊢ _),
      absorbingly_elim_persistently,
      intuitionistically_elim]

instance (priority := default + 50) fromAndPure (φ ψ : Prop) [BI PROP] :
  FromAnd (PROP := PROP) `[iprop| ⌜φ ∧ ψ⌝] `[iprop| ⌜φ⌝] `[iprop| ⌜ψ⌝]
where
  from_and := by
    rw' [pure_and]

instance (priority := default + 40) fromAndPersistently [BI PROP] (P Q1 Q2 : PROP) :
  [FromAnd P Q1 Q2] →
  FromAnd `[iprop| <pers> P] `[iprop| <pers> Q1] `[iprop| <pers> Q2]
where
  from_and := by
    rw' [← FromAnd.from_and, persistently_and]

instance (priority := default + 10) fromAndPersistentlySep [BI PROP] (P Q1 Q2 : PROP) :
  [FromSep P Q1 Q2] →
  FromAnd `[iprop| <pers> P] `[iprop| <pers> Q1] `[iprop| <pers> Q2]
where
  from_and := by
    rw' [
      ← FromSep.from_sep,
      ← persistently_and,
      persistently_and_sep]

-- IntoAnd
instance (priority := default - 10) intoAndAnd (p : Bool) [BI PROP] (P Q : PROP) :
  IntoAnd p `[iprop| P ∧ Q] P Q
where
  into_and := by
    rw' [intuitionistically_if_and]

instance intoAndAndAffineL [BI PROP] (P Q Q' : PROP) :
  [Affine P] →
  [FromAffinely Q' Q] →
  IntoAnd false `[iprop| P ∧ Q] P Q'
where
  into_and := by
    rw' [
      ← (affine_affinely : _ ⊣⊢ P),
      affinely_and_l,
      affinely_and,
      ← (FromAffinely.from_affinely : <affine>?true Q ⊢ _)]

instance intoAndAndAffineR [BI PROP] (P P' Q : PROP) :
  [Affine Q] →
  [FromAffinely P' P] →
  IntoAnd false `[iprop| P ∧ Q] P' Q
where
  into_and := by
    rw' [
      ← (affine_affinely : _ ⊣⊢ Q),
      affinely_and_r,
      affinely_and,
      ← (FromAffinely.from_affinely : <affine>?true P ⊢ _)]

instance intoAndSepAffine (p : Bool) [BI PROP] (P Q : PROP) :
  [TCOr (Affine P) (Absorbing Q)] →
  [TCOr (Absorbing P) (Affine Q)] →
  IntoAnd p `[iprop| P ∗ Q] P Q
where
  into_and := by
    cases p
    <;> rw' [sep_and]

instance intoAndPure (p : Bool) (φ ψ : Prop) [BI PROP] :
  IntoAnd (PROP := PROP) p `[iprop| ⌜φ ∧ ψ⌝] `[iprop| ⌜φ⌝] `[iprop| ⌜ψ⌝]
where
  into_and := by
    rw' [pure_and]

instance intoAndAffinely (p : Bool) [BI PROP] (P Q1 Q2 : PROP) :
  [IntoAnd p P Q1 Q2] →
  IntoAnd p `[iprop| <affine> P] `[iprop| <affine> Q1] `[iprop| <affine> Q2]
where
  into_and := by
    cases p
    case false =>
      rw' [
        ← affinely_and,
        (IntoAnd.into_and : □?false P ⊢ _)]
    case true =>
      simp only [bi_intuitionistically_if]
      rw' [
        ← affinely_and,
        !intuitionistically_affinely_elim,
        (IntoAnd.into_and : □?true P ⊢ _)]

instance intoAndIntuitionistically (p : Bool) [BI PROP] (P Q1 Q2 : PROP) :
  [IntoAnd p P Q1 Q2] →
  IntoAnd p `[iprop| □ P] `[iprop| □ Q1] `[iprop| □ Q2]
where
  into_and := by
    cases p
    case false =>
      rw' [
        ← intuitionistically_and,
        (IntoAnd.into_and : □?false P ⊢ _)]
    case true =>
      simp only [bi_intuitionistically_if]
      rw' [
        intuitionistically_and,
        !intuitionistically_idemp,
        ← intuitionistically_and,
        (IntoAnd.into_and : □?true P ⊢ _)]

instance intoAndPersistently (p : Bool) [BI PROP] (P Q1 Q2 : PROP) :
  [IntoAnd p P Q1 Q2] →
  IntoAnd p `[iprop| <pers> P] `[iprop| <pers> Q1] `[iprop| <pers> Q2]
where
  into_and := by
    cases p
    case false =>
      rw' [
        ← persistently_and,
        (IntoAnd.into_and : □?false P ⊢ _)]
    case true =>
      simp only [bi_intuitionistically_if]
      rw' [
        ← persistently_and,
        !intuitionistically_persistently_elim,
        (IntoAnd.into_and : □?true P ⊢ _)]

-- FromSep
instance (priority := default - 10) fromSepSep [BI PROP] (P1 P2 : PROP) :
  FromSep `[iprop| P1 ∗ P2] P1 P2
where
  from_sep := by
    simp

instance (priority := default - 20) fromSepAnd [BI PROP] (P1 P2 : PROP) :
  [TCOr (Affine P1) (Absorbing P2)] →
  [TCOr (Absorbing P1) (Affine P2)] →
  FromSep `[iprop| P1 ∧ P2] P1 P2
where
  from_sep := sep_and

instance (priority := default + 20) fromSepPure (φ ψ : Prop) [BI PROP] :
  FromSep (PROP := PROP) `[iprop| ⌜φ ∧ ψ⌝] `[iprop| ⌜φ⌝] `[iprop| ⌜ψ⌝]
where
  from_sep := by
    rw' [pure_and, sep_and]

instance (priority := default + 10) fromSepAffinely [BI PROP] (P Q1 Q2 : PROP) :
  [FromSep P Q1 Q2] →
  FromSep `[iprop| <affine> P] `[iprop| <affine> Q1] `[iprop| <affine> Q2]
where
  from_sep := by
    rw' [← FromSep.from_sep, affinely_sep_2]

instance (priority := default + 10) fromSepIntuitionistically [BI PROP] (P Q1 Q2 : PROP) :
  [FromSep P Q1 Q2] →
  FromSep `[iprop| □ P] `[iprop| □ Q1] `[iprop| □ Q2]
where
  from_sep := by
    rw' [← FromSep.from_sep, intuitionistically_sep_2]

instance (priority := default + 10) fromSepAbsorbingly [BI PROP] (P Q1 Q2 : PROP) :
  [FromSep P Q1 Q2] →
  FromSep `[iprop| <absorb> P] `[iprop| <absorb> Q1] `[iprop| <absorb> Q2]
where
  from_sep := by
    rw' [← FromSep.from_sep, absorbingly_sep]

instance (priority := default + 10) fromSepPersistently [BI PROP] (P Q1 Q2 : PROP) :
  [FromSep P Q1 Q2] →
  FromSep `[iprop| <pers> P] `[iprop| <pers> Q1] `[iprop| <pers> Q2]
where
  from_sep := by
    rw' [← FromSep.from_sep, persistently_sep_2]

-- AndIntoSep
inductive AndIntoSep [BI PROP] : PROP → PROP → PROP → PROP → Prop
  | and_into_sep_affine (P Q Q' : PROP) : Affine P → FromAffinely Q' Q → AndIntoSep P P Q Q'
  | and_into_sep (P Q : PROP) : AndIntoSep P `[iprop| <affine> P] Q Q

attribute [class] AndIntoSep
attribute [instance] AndIntoSep.and_into_sep_affine
attribute [instance] AndIntoSep.and_into_sep

-- IntoSep
instance intoSepSep [BI PROP] (P Q : PROP) :
  IntoSep `[iprop| P ∗ Q] P Q
where
  into_sep := by
    simp

instance intoSepAndPersistentL [BI PROP] (P Q P' Q' : PROP)
  [Persistent P]
  [inst : AndIntoSep P P' Q Q'] :
  IntoSep `[iprop| P ∧ Q] P' Q'
where
  into_sep := by
    cases inst
    case and_into_sep_affine =>
      rw' [
        ← (FromAffinely.from_affinely : <affine>?true Q ⊢ _),
        ← (affine_affinely : _ ⊣⊢ P),
        affinely_and_lr,
        persistent_and_affinely_sep_l_1]
    case and_into_sep =>
      rw' [persistent_and_affinely_sep_l_1]

instance intoSepAndPersistentR [BI PROP] (P Q P' Q' : PROP)
  [Persistent Q]
  [inst : AndIntoSep Q Q' P P'] :
  IntoSep `[iprop| P ∧ Q] P' Q'
where
  into_sep := by
    cases inst
    case and_into_sep_affine =>
      rw' [
        ← (FromAffinely.from_affinely : <affine>?true P ⊢ _),
        ← (affine_affinely : _ ⊣⊢ Q),
        ← affinely_and_lr,
        persistent_and_affinely_sep_r_1]
    case and_into_sep =>
      rw' [persistent_and_affinely_sep_r_1]

instance intoSepPure (φ ψ : Prop) [BI PROP] :
  IntoSep (PROP := PROP) `[iprop| ⌜φ ∧ ψ⌝] `[iprop| ⌜φ⌝] `[iprop| ⌜ψ⌝]
where
  into_sep := by
    rw' [pure_and, persistent_and_sep_1]

-- Coq: This instance is kind of strange, it just gets rid of the bi_affinely.
instance (priority := default - 10) intoSepAffinelyTrim [BI PROP] (P Q1 Q2 : PROP) :
  [IntoSep P Q1 Q2] →
  IntoSep `[iprop| <affine> P] Q1 Q2
where
  into_sep := by
    rw' [IntoSep.into_sep, affinely_elim]

instance intoSepPersistentlyAffine [BI PROP] (P Q1 Q2 : PROP) :
  [IntoSep P Q1 Q2] →
  [TCOr (Affine Q1) (Absorbing Q2)] →
  [TCOr (Absorbing Q1) (Affine Q2)] →
  IntoSep `[iprop| <pers> P] `[iprop| <pers> Q1] `[iprop| <pers> Q2]
where
  into_sep := by
    rw' [IntoSep.into_sep, sep_and, persistently_and, persistently_and_sep_l_1]

instance intoSepIntuitionisticallyAffine [BI PROP] (P Q1 Q2 : PROP) :
  [IntoSep P Q1 Q2] →
  [TCOr (Affine Q1) (Absorbing Q2)] →
  [TCOr (Absorbing Q1) (Affine Q2)] →
  IntoSep `[iprop| □ P] `[iprop| □ Q1] `[iprop| □ Q2]
where
  into_sep := by
    rw' [
      IntoSep.into_sep,
      sep_and,
      intuitionistically_and,
      and_sep_intuitionistically]

-- FromOr
instance fromOrOr [BI PROP] (P1 P2 : PROP) :
  FromOr `[iprop| P1 ∨ P2] P1 P2
where
  from_or := by
    simp

instance fromOrPure (φ ψ : Prop) [BI PROP] :
  FromOr (PROP := PROP) `[iprop| ⌜φ ∨ ψ⌝] `[iprop| ⌜φ⌝] `[iprop| ⌜ψ⌝]
where
  from_or := by
    rw' [pure_or]

instance fromOrAffinely [BI PROP] (P Q1 Q2 : PROP) :
  [FromOr P Q1 Q2] →
  FromOr `[iprop| <affine> P] `[iprop| <affine> Q1] `[iprop| <affine> Q2]
where
  from_or := by
    rw' [← FromOr.from_or, ← affinely_or]

instance fromOrIntuitionistically [BI PROP] (P Q1 Q2 : PROP) :
  [FromOr P Q1 Q2] →
  FromOr `[iprop| □ P] `[iprop| □ Q1] `[iprop| □ Q2]
where
  from_or := by
    rw' [← FromOr.from_or, ← intuitionistically_or]

instance fromOrAbsorbingly [BI PROP] (P Q1 Q2 : PROP) :
  [FromOr P Q1 Q2] →
  FromOr `[iprop| <absorb> P] `[iprop| <absorb> Q1] `[iprop| <absorb> Q2]
where
  from_or := by
    rw' [← FromOr.from_or, ← absorbingly_or]

instance fromOrPersistently [BI PROP] (P Q1 Q2 : PROP) :
  [FromOr P Q1 Q2] →
  FromOr `[iprop| <pers> P] `[iprop| <pers> Q1] `[iprop| <pers> Q2]
where
  from_or := by
    rw' [← FromOr.from_or, ← persistently_or]

-- IntoOr
instance intoOrOr [BI PROP] (P Q : PROP) :
  IntoOr `[iprop| P ∨ Q] P Q
where
  into_or := by
    simp

instance intoOrPure (φ ψ : Prop) [BI PROP] :
  IntoOr (PROP := PROP) `[iprop| ⌜φ ∨ ψ⌝] `[iprop| ⌜φ⌝] `[iprop| ⌜ψ⌝]
where
  into_or := by
    rw' [pure_or]

instance intoOrAffinely [BI PROP] (P Q1 Q2 : PROP) :
  [IntoOr P Q1 Q2] →
  IntoOr `[iprop| <affine> P] `[iprop| <affine> Q1] `[iprop| <affine> Q2]
where
  into_or := by
    rw' [IntoOr.into_or, ← affinely_or]

instance intoOrIntuitionistically [BI PROP] (P Q1 Q2 : PROP) :
  [IntoOr P Q1 Q2] →
  IntoOr `[iprop| □ P] `[iprop| □ Q1] `[iprop| □ Q2]
where
  into_or := by
    rw' [IntoOr.into_or, ← intuitionistically_or]

instance intoOrAbsorbingly [BI PROP] (P Q1 Q2 : PROP) :
  [IntoOr P Q1 Q2] →
  IntoOr `[iprop| <absorb> P] `[iprop| <absorb> Q1] `[iprop| <absorb> Q2]
where
  into_or := by
    rw' [IntoOr.into_or, ← absorbingly_or]

instance intoOrPersistently [BI PROP] (P Q1 Q2 : PROP) :
  [IntoOr P Q1 Q2] →
  IntoOr `[iprop| <pers> P] `[iprop| <pers> Q1] `[iprop| <pers> Q2]
where
  into_or := by
    rw' [IntoOr.into_or, ← persistently_or]

-- IntoPersistent
instance (priority := default + 20) intoPersistentPersistently (p : Bool) [BI PROP] (P Q : PROP) :
  [IntoPersistent true P Q] →
  IntoPersistent p `[iprop| <pers> P] Q
where
  into_persistent := by
    cases p
    case false =>
      exact (IntoPersistent.into_persistent : <pers>?true P ⊢ _)
    case true =>
      rw' [(IntoPersistent.into_persistent : <pers>?true P ⊢ _)]
      simp only [bi_persistently_if]
      rw' [persistently_idemp]

instance (priority := default + 20) intoPersistentAffinely (p : Bool) [BI PROP] (P Q : PROP) :
  [IntoPersistent p P Q] →
  IntoPersistent p `[iprop| <affine> P] Q
where
  into_persistent := by
    rw' [
      ← (IntoPersistent.into_persistent : <pers>?p P ⊢ _),
      affinely_elim]

instance (priority := default + 20) intoPersistentIntuitionistically (p : Bool) [BI PROP] (P Q : PROP) :
  [IntoPersistent true P Q] →
  IntoPersistent p `[iprop| □ P] Q
where
  into_persistent := by
    rw' [← (IntoPersistent.into_persistent : <pers>?true P ⊢ _)]
    cases p
    case false =>
      exact intuitionistically_into_persistently_1
    case true =>
      apply persistently_if_mono
      exact intuitionistically_elim

instance (priority := default + 10) intoPersistentHere [BI PROP] (P : PROP) :
  IntoPersistent true P P
where
  into_persistent := by
    simp [bi_persistently_if]

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

instance (priority := default - 10) fromAffinelyDefault [BI PROP] (P : PROP) :
  FromAffinely `[iprop| <affine> P] P true
where
  from_affinely := by
    simp [bi_affinely_if]

instance (priority := default - 10) fromAffinelyIntuitionistically [BI PROP] (P : PROP) :
  FromAffinely `[iprop| □ P] `[iprop| <pers> P] true
where
  from_affinely := by
    simp [bi_affinely_if, bi_intuitionistically]

instance fromAffinelyId [BI PROP] (P : PROP) :
  FromAffinely P P false
where
  from_affinely := by
    simp [bi_affinely_if]

-- IntoAbsorbingly
instance (priority := default + 30) intoAbsorbinglyTrue [BI PROP] :
  IntoAbsorbingly (PROP := PROP) `[iprop| True] `[iprop| emp]
where
  into_absorbingly := by
    rw' [← absorbingly_True_emp, absorbingly_pure]

instance (priority := default + 20) intoAbsorbinglyAbsorbing [BI PROP] (P : PROP) :
  [Absorbing P] →
  IntoAbsorbingly P P
where
  into_absorbingly := by
    rw' [absorbing_absorbingly]

instance (priority := default + 10) intoAbsorbinglyIntuitionistically [BI PROP] (P : PROP) :
  IntoAbsorbingly `[iprop| <pers> P] `[iprop| □ P]
where
  into_absorbingly := by
    rw' [← absorbingly_intuitionistically_into_persistently]

instance (priority := default - 10) intoAbsorbinglyDefault [BI PROP] (P : PROP) :
  IntoAbsorbingly `[iprop| <absorb> P] P
where
  into_absorbingly := by
    simp

-- FromAssumption
instance (priority := default + 100) fromAssumptionExact (p : Bool) [BI PROP] (P : PROP) :
  FromAssumption p P P
where
  from_assumption := by
    cases p
    <;> simp [bi_intuitionistically_if, intuitionistically_elim]

instance (priority := default + 30) fromAssumptionPersistentlyR [BI PROP] (P Q : PROP) :
  [FromAssumption true P Q] →
  FromAssumption true P `[iprop| <pers> Q]
where
  from_assumption := by
    rw' [← (FromAssumption.from_assumption : □?true P ⊢ Q)]
    simp [bi_intuitionistically_if, persistent]

instance (priority := default + 30) fromAssumptionAffinelyR [BI PROP] (P Q : PROP) :
  [FromAssumption true P Q] →
  FromAssumption true P `[iprop| <affine> Q]
where
  from_assumption := by
    rw' [← (FromAssumption.from_assumption : □?true P ⊢ Q)]
    simp only [bi_intuitionistically_if, ite_true, bi_intuitionistically]
    rw' [affinely_idemp]

instance (priority := default + 30) fromAssumptionIntuitionisticallyR [BI PROP] (P Q : PROP) :
  [FromAssumption true P Q] →
  FromAssumption true P `[iprop| □ Q]
where
  from_assumption := by
    rw' [← (FromAssumption.from_assumption : □?true P ⊢ Q)]
    simp only [bi_intuitionistically_if, ite_true]
    rw' [intuitionistically_idemp]

instance (priority := default + 20) fromAssumptionAbsorbinglyR (p : Bool) [BI PROP] (P Q : PROP) :
  [FromAssumption p P Q] →
  FromAssumption p P `[iprop| <absorb> Q]
where
  from_assumption := by
    rw' [← (FromAssumption.from_assumption : □?p P ⊢ Q)]
    exact absorbingly_intro

instance (priority := default + 20) fromAssumptionIntuitionisticallyL (p : Bool) [BI PROP] (P Q : PROP) :
  [FromAssumption true P Q] →
  FromAssumption p `[iprop| □ P] Q
where
  from_assumption := by
    rw' [
      ← (FromAssumption.from_assumption : □?true P ⊢ Q),
      intuitionistically_if_elim]

instance (priority := default + 20) fromAssumptionIntuitionisticallyLTrue (p : Bool) [BI PROP] (P Q : PROP) :
  [FromAssumption p P Q] →
  FromAssumption p `[iprop| □ P] Q
where
  from_assumption := by
    rw' [
      ← (FromAssumption.from_assumption : □?p P ⊢ Q),
      intuitionistically_elim]

instance (priority := default + 30) FromAssumptionPersistentlyLTrue [BI PROP] (P Q : PROP) :
  [FromAssumption true P Q] →
  FromAssumption true `[iprop| <pers> P] Q
where
  from_assumption := by
    simp only [bi_intuitionistically_if]
    rw' [
      ← (FromAssumption.from_assumption : □?true P ⊢ Q),
      intuitionistically_persistently_elim]

instance (priority := default + 30) fromAssumptionPersistentlyLFalse [BIAffine PROP] (P Q : PROP) :
  [FromAssumption true P Q] →
  FromAssumption false `[iprop| <pers> P] Q
where
  from_assumption := by
    rw' [← (FromAssumption.from_assumption : □?true P ⊢ Q)]
    simp only [bi_intuitionistically_if, ite_true, ite_false]
    rw' [intuitionistically_into_persistently]

instance (priority := default + 20) fromAssumptionAffinelyL (p : Bool) [BI PROP] (P Q : PROP) :
  [FromAssumption p P Q] →
  FromAssumption p `[iprop| <affine> P] Q
where
  from_assumption := by
    rw' [
      ← (FromAssumption.from_assumption : □?p P ⊢ Q),
      affinely_elim]

instance (priority := default + 10) fromAssumptionForall (p : Bool) [BI PROP] (Φ : α → PROP) (x : α) (Q : PROP) :
  [FromAssumption p (Φ x) Q] →
  FromAssumption p `[iprop| ∀ x, Φ x] Q
where
  from_assumption := by
    rw' [
      ← (FromAssumption.from_assumption : □?p (Φ x) ⊢ Q),
      BI.forall_elim x]

-- IntoPure
instance intoPurePure (φ : Prop) [BI PROP] :
  IntoPure (PROP := PROP) `[iprop| ⌜φ⌝] φ
where
  into_pure := by
    simp

instance intoPurePureAnd (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [IntoPure P1 φ1] →
  [IntoPure P2 φ2] →
  IntoPure `[iprop| P1 ∧ P2] (φ1 ∧ φ2)
where
  into_pure := by
    rw' [
      pure_and,
      (IntoPure.into_pure : P1 ⊢ _),
      (IntoPure.into_pure : P2 ⊢ _)]

instance intoPurePureOr (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [IntoPure P1 φ1] →
  [IntoPure P2 φ2] →
  IntoPure `[iprop| P1 ∨ P2] (φ1 ∨ φ2)
where
  into_pure := by
    rw' [
      pure_or,
      (IntoPure.into_pure : P1 ⊢ _),
      (IntoPure.into_pure : P2 ⊢ _)]

instance intoPureExist [BI PROP] (Φ : α → PROP) (φ : α → Prop) :
  [∀ x, IntoPure (Φ x) (φ x)] →
  IntoPure `[iprop| ∃ x, Φ x] (∃ x, φ x)
where
  into_pure := by
    rw' [IntoPure.into_pure, pure_exist]

instance intoPurePureSep (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [IntoPure P1 φ1] →
  [IntoPure P2 φ2] →
  IntoPure `[iprop| P1 ∗ P2] (φ1 ∧ φ2)
where
  into_pure := by
    rw' [
      (IntoPure.into_pure : P1 ⊢ _),
      (IntoPure.into_pure : P2 ⊢ _),
      sep_and,
      pure_and]

instance intoPureAffinely [BI PROP] (P : PROP) (φ : Prop) :
  [IntoPure P φ] →
  IntoPure `[iprop| <affine> P] φ
where
  into_pure := by
    rw' [IntoPure.into_pure, affinely_elim]

instance intoPureIntuitionistically [BI PROP] (P : PROP) (φ : Prop) :
  [IntoPure P φ] →
  IntoPure `[iprop| □ P] φ
where
  into_pure := by
    rw' [IntoPure.into_pure, intuitionistically_elim]

instance intoPureAbsorbingly [BI PROP] (P : PROP) (φ : Prop) :
  [IntoPure P φ] →
  IntoPure `[iprop| <absorb> P] φ
where
  into_pure := by
    rw' [(IntoPure.into_pure : P ⊢ _), absorbingly_pure]

instance intoPurePersistently [BI PROP] (P : PROP) (φ : Prop) :
  [IntoPure P φ] →
  IntoPure `[iprop| <pers> P] φ
where
  into_pure := by
    rw' [IntoPure.into_pure, persistently_elim]

-- FromPure
instance fromPureEmp [BI PROP] :
  FromPure (PROP := PROP) true `[iprop| emp] True
where
  from_pure := by
    simp only [bi_affinely_if, ite_true]
    rw' [affine]

instance fromPurePure [BI PROP] (φ : Prop) :
  FromPure (PROP := PROP) false `[iprop| ⌜φ⌝] φ
where
  from_pure := by
    simp [bi_affinely_if]

instance fromPurePureAnd (a1 a2 : Bool) (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [FromPure a1 P1 φ1] →
  [FromPure a2 P2 φ2] →
  FromPure (a1 || a2) `[iprop| P1 ∧ P2] (φ1 ∧ φ2)
where
  from_pure := by
    rw' [
      pure_and,
      ← (FromPure.from_pure : _ ⊢ P1),
      ← (FromPure.from_pure : _ ⊢ P2),
      affinely_if_and]
    apply and_mono
    <;> apply affinely_if_flag_mono
    <;> simp_all

instance fromPurePureOr (a1 a2 : Bool) (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [FromPure a1 P1 φ1] →
  [FromPure a2 P2 φ2] →
  FromPure (a1 || a2) `[iprop| P1 ∨ P2] (φ1 ∨ φ2)
where
  from_pure := by
    rw' [
      pure_or,
      ← (FromPure.from_pure : _ ⊢ P1),
      ← (FromPure.from_pure : _ ⊢ P2),
      affinely_if_or]
    apply or_mono
    <;> apply affinely_if_flag_mono
    <;> simp_all

instance fromPurePureImpl (a : Bool) (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [IntoPure P1 φ1] →
  [FromPure a P2 φ2] →
  FromPure a `[iprop| P1 → P2] (φ1 → φ2)
where
  from_pure := by
    rw' [
      ← IntoPure.into_pure,
      ← FromPure.from_pure,
      pure_impl_1]
    cases a
    <;> simp [bi_affinely_if]
    apply BI.impl_intro_l
    rw' [affinely_and_r, BI.impl_elim_r]

instance fromPureExist (a : Bool) [BI PROP] (Φ : α → PROP) (φ : α → Prop) :
  [∀ x, FromPure a `[iprop| Φ x] (φ x)] →
  FromPure a `[iprop| ∃ x, Φ x] (∃ x, φ x)
where
  from_pure := by
    rw' [← FromPure.from_pure, pure_exist, affinely_if_exist]

instance fromPureForall (a : Bool) [BI PROP] (Φ : α → PROP) (φ : α → Prop) :
  [∀ x, FromPure a `[iprop| Φ x] (φ x)] →
  FromPure a `[iprop| ∀ x, Φ x] (∀ x, φ x)
where
  from_pure := by
    rw' [← FromPure.from_pure, pure_forall_1]
    cases a
    <;> simp [bi_affinely_if, affinely_forall]

instance fromPurePureSepTrue (a1 a2 : Bool) (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP) :
  [FromPure a1 P1 φ1] →
  [FromPure a2 P2 φ2] →
  FromPure (a1 && a2) `[iprop| P1 ∗ P2] (φ1 ∧ φ2)
where
  from_pure := by
    rw' [
      ← (FromPure.from_pure : _ ⊢ P1),
      ← (FromPure.from_pure : _ ⊢ P2)]
    cases a1
    <;> cases a2
    <;> simp only [bi_affinely_if]
    <;> rw' [pure_and]
    · rw' [persistent_and_sep_1]
    · rw' [persistent_and_affinely_sep_r]
    · rw' [persistent_and_affinely_sep_l]
    · rw' [affinely_and, persistent_and_sep_1]

instance fromPurePureWand (a : Bool) (φ1 φ2 : Prop) [BI PROP] (P1 P2 : PROP)
  [IntoPure P1 φ1]
  [FromPure a P2 φ2]
  [inst : TCIte a (Affine P1) TCTrue] :
  FromPure a `[iprop| P1 -∗ P2] (φ1 → φ2)
where
  from_pure := by
    rw' [← FromPure.from_pure]
    apply BI.wand_intro_l
    cases a
    <;> simp only [bi_affinely_if, ite_true, ite_false]
    <;> cases inst
    case a.false.e =>
      rw' [IntoPure.into_pure, pure_and, pure_impl_1, impl_elim_r]
    case a.true.t =>
      rw' [
        ← persistent_and_affinely_sep_r,
        ← (affine_affinely : _ ⊣⊢ P1),
        (IntoPure.into_pure : P1 ⊢ _),
        affinely_and_l,
        pure_impl_1,
        impl_elim_r]

instance fromPurePersistently [BI PROP] (P : PROP) (a : Bool) (φ : Prop) :
  [FromPure true P φ] →
  FromPure a `[iprop| <pers> P] φ
where
  from_pure := by
    rw' [← FromPure.from_pure]
    conv =>
      rhs
      simp only [bi_affinely_if, ite_true]
    rw' [
      persistently_affinely_elim,
      affinely_if_elim,
      persistently_pure]

instance fromPureAffinelyTrue (a : Bool) [BI PROP] (P : PROP) (φ : Prop) :
  [FromPure a P φ] →
  FromPure true `[iprop| <affine> P] φ
where
  from_pure := by
    rw' [
      ← (FromPure.from_pure : _ ⊢ P),
      ← affinely_affinely_if,
      affinely_idemp]

instance fromPureIntuitionisticallyTrue (a : Bool) [BI PROP] (P : PROP) (φ : Prop) :
  [FromPure a P φ] →
  FromPure true `[iprop| □ P] φ
where
  from_pure := by
    rw' [
      ← (FromPure.from_pure : _ ⊢ P),
      ← intuitionistically_affinely_elim,
      ← affinely_affinely_if,
      affinely_idemp,
      intuitionistic_intuitionistically]

instance fromPureAbsorbingly (a : Bool) [BI PROP] (P : PROP) (φ : Prop) :
  [FromPure a P φ] →
  FromPure false `[iprop| <absorb> P] φ
where
  from_pure := by
    rw' [
      ← (FromPure.from_pure : _ ⊢ P),
      ← affinely_affinely_if,
      ← persistent_absorbingly_affinely_2]

end Iris.Proofmode
