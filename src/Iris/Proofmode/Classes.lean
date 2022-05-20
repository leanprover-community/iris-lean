import Iris.BI

namespace Iris.Proofmode
open Iris.BI

class AsEmpValid1 (φ : outParam Prop) {PROP : Type} (P : PROP) where
  [bi : BI PROP]
  as_emp_valid : φ ↔ ⊢ P

class AsEmpValid2 (φ : Prop) {PROP : outParam Type} (P : outParam PROP) where
  [bi : BI PROP]
  as_emp_valid : φ ↔ ⊢ P

instance [inst : @AsEmpValid1 φ PROP P] : BI PROP := inst.bi
instance [inst : @AsEmpValid2 φ PROP P] : BI PROP := inst.bi

class AsEmpValid (φ : Prop) {PROP : Type} (P : PROP) extends
  AsEmpValid1 φ P,
  AsEmpValid2 φ P

theorem as_emp_valid_1 [BI PROP] (P : PROP) [AsEmpValid1 φ P] : φ → ⊢ P := sorry
theorem as_emp_valid_2 (φ : Prop) [AsEmpValid2 φ P] : (⊢ P) → φ := sorry


class FromImpl [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_impl : (Q1 → Q2) ⊢ P

class FromWand [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_wand : (Q1 -∗ Q2) ⊢ P


class IntoPersistent (p : Bool) [BI PROP] (P : PROP) (Q : outParam PROP) where
  into_persistent : <pers>?p P ⊢ <pers> Q

class FromAffinely [BI PROP] (P : outParam PROP) (Q : PROP) where
  from_affinely : <affine> Q ⊢ P


class FromAssumption (p : Bool) [BI PROP] (P Q : PROP) where
  from_assumption : □?p P ⊢ Q

end Iris.Proofmode
