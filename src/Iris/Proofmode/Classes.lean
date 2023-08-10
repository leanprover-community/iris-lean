/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.BI

namespace Iris.Proofmode
open Iris.BI

/- The two type classes `AsEmpValid1` and `AsEmpValid2` are necessary since type class instance
search is used in both directions in `as_emp_valid_1` and `as_emp_valid_2`. When type class
instance search is supposed to generate `φ` based on `P`, `AsEmpValid1` is used, since `φ` is declared as an
`outParam`. Consequently, if type class instance search is supposed to generate `P`, `AsEmpValid2`
is used. -/

class AsEmpValid1 (φ : outParam Prop) {PROP : Type} (P : PROP) [BI PROP] : Prop where
  as_emp_valid : φ ↔ ⊢ P

class AsEmpValid2 (φ : Prop) {PROP : outParam Type} (P : outParam PROP) [BI PROP] : Prop where
  as_emp_valid : φ ↔ ⊢ P

def AsEmpValid1.to2 {φ : Prop} {PROP : Type} {P : PROP} [BI PROP]
    [AsEmpValid1 φ P] : AsEmpValid2 φ P := ⟨AsEmpValid1.as_emp_valid⟩

def AsEmpValid2.to1 {φ : Prop} {PROP : Type} {P : PROP} [BI PROP]
    [AsEmpValid2 φ P] : AsEmpValid1 φ P := ⟨AsEmpValid2.as_emp_valid⟩

theorem as_emp_valid_1 [BI PROP] (P : PROP) [AsEmpValid1 φ P] : φ → ⊢ P :=
  AsEmpValid1.as_emp_valid.mp
theorem as_emp_valid_2 [BI PROP] (φ : Prop) [AsEmpValid2 φ (P : PROP)] : (⊢ P) → φ :=
  AsEmpValid2.as_emp_valid.mpr


/- Depending on the use case, type classes with the prefix `From` or `Into` are used. Type classes
with the prefix `From` are used to generate one or more propositions *from* which the original
proposition can be derived. Type classes with the prefix `Into` are used to generate propositions
*into* which the original proposition can be turned by derivation. Additional boolean flags are
used to indicate that certain propositions should be intuitionistic. -/

class FromImp [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) : Prop where
  from_imp : (Q1 → Q2) ⊢ P
export FromImp (from_imp)

class FromWand [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) : Prop where
  from_wand : (Q1 -∗ Q2) ⊢ P
export FromWand (from_wand)

class IntoWand [BI PROP] (p q : Bool) (R P : PROP) (Q : outParam PROP) : Prop where
  into_wand : □?p R ⊢ □?q P -∗ Q
export IntoWand (into_wand)

class FromForall [BI PROP] (P : PROP) {α : outParam Type} (Ψ : outParam <| α → PROP) : Prop where
  from_forall : (∀ x, Ψ x) ⊢ P
export FromForall (from_forall)

class IntoForall [BI PROP] (P : PROP) {α : outParam Type} (Φ : outParam <| α → PROP) : Prop where
  into_forall : P ⊢ ∀ x, Φ x
export IntoForall (into_forall)

class FromExists [BI PROP] (P : PROP) {α : outParam Type} (Φ : outParam <| α → PROP) : Prop where
  from_exists : (∃ x, Φ x) ⊢ P
export FromExists (from_exists)

class IntoExists [BI PROP] (P : PROP) {α : outParam Type} (Φ : outParam <| α → PROP) : Prop where
  into_exists : P ⊢ ∃ x, Φ x
export IntoExists (into_exists)

class FromAnd [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) : Prop where
  from_and : Q1 ∧ Q2 ⊢ P
export FromAnd (from_and)

class IntoAnd (p : Bool) [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) : Prop where
  into_and : □?p P ⊢ □?p (Q1 ∧ Q2)
export IntoAnd (into_and)

class FromSep [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) : Prop where
  from_sep : Q1 ∗ Q2 ⊢ P
export FromSep (from_sep)

class IntoSep [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) : Prop where
  into_sep : P ⊢ Q1 ∗ Q2
export IntoSep (into_sep)

class FromOr [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) : Prop where
  from_or : Q1 ∨ Q2 ⊢ P
export FromOr (from_or)

class IntoOr [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) : Prop where
  into_or : P ⊢ Q1 ∨ Q2
export IntoOr (into_or)


class IntoPersistent (p : Bool) [BI PROP] (P : PROP) (Q : outParam PROP) : Prop where
  into_persistent : <pers>?p P ⊢ <pers> Q
export IntoPersistent (into_persistent)

class FromAffinely [BI PROP] (P : outParam PROP) (Q : PROP) (p : Bool := true) : Prop where
  from_affinely : <affine>?p Q ⊢ P
export FromAffinely (from_affinely)

class IntoAbsorbingly [BI PROP] (P : outParam PROP) (Q : PROP) : Prop where
  into_absorbingly : P ⊢ <absorb> Q
export IntoAbsorbingly (into_absorbingly)


class FromAssumption (p : Bool) [BI PROP] (P Q : PROP) : Prop where
  from_assumption : □?p P ⊢ Q
export FromAssumption (from_assumption)

class IntoPure [BI PROP] (P : PROP) (φ : outParam Prop) : Prop where
  into_pure : P ⊢ ⌜φ⌝
export IntoPure (into_pure)

class FromPure [BI PROP] (a : outParam Bool) (P : PROP) (φ : outParam Prop) : Prop where
  from_pure : <affine>?a ⌜φ⌝ ⊢ P
export FromPure (from_pure)

end Iris.Proofmode
