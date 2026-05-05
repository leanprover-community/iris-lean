/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Michael Sammler
-/
module

public import Iris.BI
public meta import Iris.ProofMode.SynthInstance
public import Iris.ProofMode.Modalities

@[expose] public section

namespace Iris.ProofMode
open Iris.BI

/-- [PMError] is used as precondition on "failing" instances of typeclasses
  that have pure preconditions (such as [ElimModal]) -/
inductive PMError (msg : String) : Prop

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
class AsEmpValid (d : AsEmpValid.Direction) (φ : Prop) {PROP : semiOutParam (Type _)} (P : outParam PROP) [semiOutParam (BI PROP)] where
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

/-- `FromModal` turns a goal `P : PROP2` into a modality `M : PROP1 → PROP2` applied to `Q : PROP1` under condition `φ`. -/
@[ipm_class]
class FromModal {PROP1 PROP2} [BI PROP1] [BI PROP2] (φ : outParam $ Prop) (M : outParam $ Modality PROP1 PROP2) (sel : semiOutParam PROP1) (P : PROP2) (Q : outParam $ PROP1) where
  from_modal : φ → M.M Q ⊢ P
export FromModal (from_modal)

/-- `ElimModal` turns `□?p P` into `□?p' P'` and `Q` into `Q'` under condition `φ`. -/
@[ipm_class]
class ElimModal {PROP} [BI PROP] (φ : outParam $ Prop) (p : Bool) (p' : outParam Bool) (P : PROP) (P' : outParam PROP) (Q : PROP) (Q' : outParam PROP) where
  elim_modal : φ → □?p P ∗ (□?p' P' -∗ Q') ⊢ Q
export ElimModal (elim_modal)


/-- `IntoLaterN` turns `P` into `▷^[n] Q`.
The Boolean [only_head] indicates whether laters should only be stripped in
head position or also below other logical connectives. For [inext] it should
strip laters below other logical connectives, but this should not happen while
framing.

The Rocq version uses an `MaybeIntoLaterN` typeclass that avoids unfolding definitions
for searches that do not make progress. But this is not necessary in Lean since Lean
TC synthesis does not unfold definitions by default.

This classes is deliberately not an `ipm_class` to use the more efficient TC synthesis.
-/
class IntoLaterN [BI PROP] (only_head : Bool) (n : Nat) (P : PROP) (Q : outParam PROP) where
  into_laterN : P ⊢ ▷^[n] Q
export IntoLaterN (into_laterN)

/-- `CombineSepAs` combines two propositions `P` and `Q` into `R` -/
@[ipm_class]
class CombineSepAs [BI PROP] (P Q : PROP) (R : outParam PROP) where
  combine_sep_as : P ∗ Q ⊢ R
export CombineSepAs (combine_sep_as)

end Iris.ProofMode
