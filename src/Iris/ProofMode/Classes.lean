/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.BI
import Iris.ProofMode.SynthInstance

namespace Iris.ProofMode
open Iris.BI

/-- [InOut] is used to dynamically determine whether a type class
parameter is an input or an output. This is important for classes that
are used with multiple modings, e.g., IntoWand. Instances can match on
the InOut parameter to avoid accidentially instantiating outputs if
matching on an input was intended. -/
inductive InOut where
  | in
  | out

inductive AsEmpValid.Direction where
  | into
  | from

@[ipm_class]
class AsEmpValid (d : AsEmpValid.Direction) (φ : Prop) {PROP : outParam (Type _)} (P : outParam PROP) [BI PROP] where
  as_emp_valid : (d = .into → φ → ⊢ P) ∧ (d = .from → (⊢ P) → φ)

theorem asEmpValid_1 [BI PROP] (P : PROP) [AsEmpValid .into φ P] : φ → ⊢ P :=
  AsEmpValid.as_emp_valid.1 rfl
theorem asEmpValid_2 [BI PROP] (φ : Prop) [AsEmpValid .from φ (P : PROP)] : (⊢ P) → φ :=
  AsEmpValid.as_emp_valid.2 rfl


/- Depending on the use case, type classes with the prefix `From` or `Into` are used. Type classes
with the prefix `From` are used to generate one or more propositions *from* which the original
proposition can be derived. Type classes with the prefix `Into` are used to generate propositions
*into* which the original proposition can be turned by derivation. Additional boolean flags are
used to indicate that certain propositions should be intuitionistic. -/

@[ipm_class]
class FromImp [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_imp : (Q1 → Q2) ⊢ P
export FromImp (from_imp)

@[ipm_class]
class FromWand [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_wand : (Q1 -∗ Q2) ⊢ P
export FromWand (from_wand)

@[ipm_class]
class IntoWand [BI PROP] (p q : Bool) (R : PROP)
  (ioP : InOut) (P : semiOutParam PROP)
  (ioQ : InOut) (Q : semiOutParam PROP) where
  into_wand : □?p R ⊢ □?q P -∗ Q
export IntoWand (into_wand)

@[ipm_class]
class FromForall [BI PROP] (P : PROP) {α : outParam (Sort _)} (Ψ : outParam <| α → PROP) where
  from_forall : (∀ x, Ψ x) ⊢ P
export FromForall (from_forall)

@[ipm_class]
class IntoForall [BI PROP] (P : PROP) {α : outParam (Sort _)} (Φ : outParam <| α → PROP) where
  into_forall : P ⊢ ∀ x, Φ x
export IntoForall (into_forall)

@[ipm_class]
class FromExists [BI PROP] (P : PROP) {α : outParam (Sort _)} (Φ : outParam <| α → PROP) where
  from_exists : (∃ x, Φ x) ⊢ P
export FromExists (from_exists)

@[ipm_class]
class IntoExists [BI PROP] (P : PROP) {α : outParam (Sort _)} (Φ : outParam <| α → PROP) where
  into_exists : P ⊢ ∃ x, Φ x
export IntoExists (into_exists)

@[ipm_class]
class FromAnd [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_and : Q1 ∧ Q2 ⊢ P
export FromAnd (from_and)

@[ipm_class]
class IntoAnd (p : Bool) [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  into_and : □?p P ⊢ □?p (Q1 ∧ Q2)
export IntoAnd (into_and)

@[ipm_class]
class FromSep [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_sep : Q1 ∗ Q2 ⊢ P
export FromSep (from_sep)

@[ipm_class]
class IntoSep [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  into_sep : P ⊢ Q1 ∗ Q2
export IntoSep (into_sep)

@[ipm_class]
class FromOr [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_or : Q1 ∨ Q2 ⊢ P
export FromOr (from_or)

@[ipm_class]
class IntoOr [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  into_or : P ⊢ Q1 ∨ Q2
export IntoOr (into_or)


@[ipm_class]
class IntoPersistently (p : Bool) [BI PROP] (P : PROP) (Q : outParam PROP) where
  into_persistently : <pers>?p P ⊢ <pers> Q
export IntoPersistently (into_persistently)

@[ipm_class]
class FromAffinely [BI PROP] (P : outParam PROP) (Q : PROP) (p : Bool := true) where
  from_affinely : <affine>?p Q ⊢ P
export FromAffinely (from_affinely)

@[ipm_class]
class IntoAbsorbingly [BI PROP] (P : outParam PROP) (Q : PROP) where
  into_absorbingly : P ⊢ <absorb> Q
export IntoAbsorbingly (into_absorbingly)


@[ipm_class]
class FromAssumption (p : Bool) [BI PROP] (ioP : InOut) (P : semiOutParam PROP) (Q : PROP) where
  from_assumption : □?p P ⊢ Q
export FromAssumption (from_assumption)

@[ipm_class]
class IntoPure [BI PROP] (P : PROP) (φ : outParam Prop) where
  into_pure : P ⊢ ⌜φ⌝
export IntoPure (into_pure)

@[ipm_class]
class FromPure [BI PROP] (a : outParam Bool) (P : PROP) (φ : outParam Prop) where
  from_pure : <affine>?a ⌜φ⌝ ⊢ P
export FromPure (from_pure)

@[ipm_class]
class IsExcept0 [BI PROP] (Q : PROP) where
  is_except0 : ◇ Q ⊢ Q
export IsExcept0 (is_except0)

@[ipm_class]
class IntoExcept0 [BI PROP] (P : PROP) (Q : outParam PROP) where
  into_except0 : P ⊢ ◇ Q
export IntoExcept0 (into_except0)

end Iris.ProofMode
