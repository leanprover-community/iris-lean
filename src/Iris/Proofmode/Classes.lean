import Iris.BI

namespace Iris.Proofmode
open Iris.BI

class AsEmpValid1 (φ : outParam Prop) {PROP : Type} (P : PROP) where
  [bi : BI PROP]
  as_emp_valid : φ ↔ ⊢ P

class AsEmpValid2 (φ : Prop) {PROP : outParam Type} (P : outParam PROP) where
  [bi : BI PROP]
  as_emp_valid : φ ↔ ⊢ P

instance (priority := default - 100) [inst : @AsEmpValid1 φ PROP P] : BI PROP := inst.bi
instance (priority := default - 100) [inst : @AsEmpValid2 φ PROP P] : BI PROP := inst.bi

class AsEmpValid (φ : Prop) {PROP : Type} (P : PROP) extends
  AsEmpValid1 φ P,
  AsEmpValid2 φ P

theorem as_emp_valid_1 [BI PROP] (P : PROP) [AsEmpValid1 φ P] : φ → ⊢ P := sorry
theorem as_emp_valid_2 (φ : Prop) [AsEmpValid2 φ P] : (⊢ P) → φ := sorry


class FromImpl [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_impl : (Q1 → Q2) ⊢ P

class FromWand [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_wand : (Q1 -∗ Q2) ⊢ P

class FromAnd [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_and : Q1 ∧ Q2 ⊢ P

class IntoAnd (p : Bool) [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  into_and : □?p P ⊢ □?p (Q1 ∧ Q2)

class FromSep [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_sep : Q1 ∗ Q2 ⊢ P

class IntoSep [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) :=
  into_sep : P ⊢ Q1 ∗ Q2

class FromOr [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_or : Q1 ∨ Q2 ⊢ P

class IntoOr [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  into_or : P ⊢ Q1 ∨ Q2


class IntoPersistent (p : Bool) [BI PROP] (P : PROP) (Q : outParam PROP) where
  into_persistent : <pers>?p P ⊢ <pers> Q

class FromAffinely [BI PROP] (P : outParam PROP) (Q : PROP) (p : Bool := true) where
  from_affinely : <affine>?p Q ⊢ P

class IntoAbsorbingly [BI PROP] (P : outParam PROP) (Q : PROP) where
  into_absorbingly : P ⊢ <absorb> Q


class FromAssumption (p : Bool) [BI PROP] (P Q : PROP) where
  from_assumption : □?p P ⊢ Q

class IntoPure [BI PROP] (P : PROP) (φ : outParam Prop) where
  into_pure : P ⊢ ⌜φ⌝

end Iris.Proofmode
