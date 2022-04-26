import Iris.BI

namespace Iris.Proofmode
open Iris.BI

class AsEmpValid1 (φ : outParam Prop) {PROP : Type} (P : PROP) where
  [bi : BI PROP]
  as_emp_valid : φ ↔ ⊢ P

class AsEmpValid2 (φ : Prop) {PROP : outParam Type} (P : outParam PROP) where
  [bi : BI PROP]
  as_emp_valid : φ ↔ ⊢ P

instance [as : @AsEmpValid1 φ PROP P] : BI PROP := as.bi
instance [as : @AsEmpValid2 φ PROP P] : BI PROP := as.bi

class AsEmpValid (φ : Prop) {PROP : Type} (P : PROP) extends
  AsEmpValid1 φ P,
  AsEmpValid2 φ P

theorem as_emp_valid_1 [BI PROP] (P : PROP) [AsEmpValid1 φ P] : φ → ⊢ P := sorry
theorem as_emp_valid_2 (φ : Prop) [AsEmpValid2 φ P] : (⊢ P) → φ := sorry

end Iris.Proofmode
