import Iris.BI

namespace Iris.Proofmode
open Iris.BI

class AsEmpValid1 (φ : outParam Prop) {PROP : Type} (P : PROP) where
  [bi : BI PROP]
  as_emp_valid : φ ↔ ⊢ P

class AsEmpValid2 (φ : Prop) {PROP : outParam Type} (P : outParam PROP) where
  [bi : BI PROP]
  as_emp_valid : φ ↔ ⊢ P

attribute [instance (default - 100)] AsEmpValid1.bi
attribute [instance (default - 100)] AsEmpValid2.bi

class AsEmpValid (φ : Prop) {PROP : Type} (P : PROP) extends
  AsEmpValid1 φ P,
  AsEmpValid2 φ P

theorem as_emp_valid_1 (P : PROP) [AsEmpValid1 φ P] : φ → ⊢ P :=
  AsEmpValid1.as_emp_valid.mp
theorem as_emp_valid_2 (φ : Prop) [AsEmpValid2 φ P] : (⊢ P) → φ :=
  AsEmpValid2.as_emp_valid.mpr


class FromImpl [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_impl : (Q1 → Q2) ⊢ P
export FromImpl (from_impl)

class FromWand [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_wand : (Q1 -∗ Q2) ⊢ P
export FromWand (from_wand)

class IntoWand [BI PROP] (p q : Bool) (R P : PROP) (Q : outParam PROP) where
  into_wand : □?p R ⊢ □?q P -∗ Q
export IntoWand (into_wand)

class FromForall [BI PROP] (P : PROP) {α : outParam Type} (Ψ : outParam <| α → PROP) where
  from_forall : (∀ x, Ψ x) ⊢ P
export FromForall (from_forall)

class IntoForall [BI PROP] (P : PROP) {α : outParam Type} (Φ : outParam <| α → PROP) where
  into_forall : P ⊢ ∀ x, Φ x
export IntoForall (into_forall)

class FromExist [BI PROP] (P : PROP) {α : outParam Type} (Φ : outParam <| α → PROP) where
  from_exist : (∃ x, Φ x) ⊢ P
export FromExist (from_exist)

class IntoExist [BI PROP] (P : PROP) {α : outParam Type} (Φ : outParam <| α → PROP) where
  into_exist : P ⊢ ∃ x, Φ x
export IntoExist (into_exist)

class FromAnd [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_and : Q1 ∧ Q2 ⊢ P
export FromAnd (from_and)

class IntoAnd (p : Bool) [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  into_and : □?p P ⊢ □?p (Q1 ∧ Q2)
export IntoAnd (into_and)

class FromSep [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_sep : Q1 ∗ Q2 ⊢ P
export FromSep (from_sep)

class IntoSep [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) :=
  into_sep : P ⊢ Q1 ∗ Q2
export IntoSep (into_sep)

class FromOr [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_or : Q1 ∨ Q2 ⊢ P
export FromOr (from_or)

class IntoOr [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  into_or : P ⊢ Q1 ∨ Q2
export IntoOr (into_or)


class IntoPersistent (p : Bool) [BI PROP] (P : PROP) (Q : outParam PROP) where
  into_persistent : <pers>?p P ⊢ <pers> Q
export IntoPersistent (into_persistent)

class FromAffinely [BI PROP] (P : outParam PROP) (Q : PROP) (p : Bool := true) where
  from_affinely : <affine>?p Q ⊢ P
export FromAffinely (from_affinely)

class IntoAbsorbingly [BI PROP] (P : outParam PROP) (Q : PROP) where
  into_absorbingly : P ⊢ <absorb> Q
export IntoAbsorbingly (into_absorbingly)


class FromAssumption (p : Bool) [BI PROP] (P Q : PROP) where
  from_assumption : □?p P ⊢ Q
export FromAssumption (from_assumption)

class IntoPure [BI PROP] (P : PROP) (φ : outParam Prop) where
  into_pure : P ⊢ ⌜φ⌝
export IntoPure (into_pure)

class FromPure [BI PROP] (a : outParam Bool) (P : PROP) (φ : outParam Prop) where
  from_pure : <affine>?a ⌜φ⌝ ⊢ P
export FromPure (from_pure)

end Iris.Proofmode
