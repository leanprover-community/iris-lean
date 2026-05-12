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

/--
[PMError] is used as precondition on "failing" instances of typeclasses that
have pure preconditions (such as [ElimModal])
-/
@[rocq_alias pm_error]
inductive PMError (msg : String) : Prop

@[rocq_alias as_emp_valid_direction]
inductive AsEmpValid.Direction where
  | into
  | from

@[ipm_class, rocq_alias AsEmpValid]
class AsEmpValid (d : AsEmpValid.Direction) (φ : Prop) (_ : InOut) (PROP : semiOutParam $ Type _)
(_ : InOut) (bi : semiOutParam $ BI PROP) (P : outParam $ PROP) where
  as_emp_valid : (d = .into → φ → ⊢ P) ∧ (d = .from → (⊢ P) → φ)

@[rocq_alias as_emp_valid_1]
theorem asEmpValid_1 {PROP} [bi : BI PROP] {φ : Prop} (P : PROP) [AsEmpValid .into φ .in PROP .in bi P]
: φ → ⊢ P := (AsEmpValid.as_emp_valid .in .in).1 rfl
@[rocq_alias as_emp_valid_2]
theorem asEmpValid_2 {PROP} [bi : BI PROP] {P: PROP} (φ : Prop) [AsEmpValid .from φ .out PROP .out bi P]
: (⊢ P) → φ := (AsEmpValid.as_emp_valid .out .out).2 rfl

/- Depending on the use case, type classes with the prefix `From` or `Into` are used. Type classes
with the prefix `From` are used to generate one or more propositions *from* which the original
proposition can be derived. Type classes with the prefix `Into` are used to generate propositions
*into* which the original proposition can be turned by derivation. Additional boolean flags are
used to indicate that certain propositions should be intuitionistic. -/

@[ipm_class, rocq_alias FromImpl]
class FromImp {PROP} [BI PROP] (P : PROP) (Q1 Q2 : outParam $ PROP) where
  from_imp : (Q1 → Q2) ⊢ P
export FromImp (from_imp)

@[ipm_class, rocq_alias FromWand]
class FromWand {PROP} [BI PROP] (P : PROP) (_ : InOut) (Q1 : semiOutParam PROP) (Q2 : outParam $ PROP) where
  from_wand : (Q1 -∗ Q2) ⊢ P
export FromWand (from_wand)

#rocq_ignore IntoWand' "not used in Lean"

@[ipm_class, rocq_alias IntoWand]
class IntoWand {PROP} [BI PROP] (p q : Bool) (R : PROP)
  (ioP : InOut) (P : semiOutParam PROP)
  (ioQ : InOut) (Q : semiOutParam PROP) where
  into_wand : □?p R ⊢ □?q P -∗ Q
export IntoWand (into_wand)

@[ipm_class, rocq_alias FromForall]
class FromForall {PROP} [BI PROP] (P : PROP) {α : outParam (Sort _)} (Ψ : outParam <| α → PROP) where
  from_forall : (∀ x, Ψ x) ⊢ P
export FromForall (from_forall)

@[ipm_class, rocq_alias IntoForall]
class IntoForall {PROP} [BI PROP] (P : PROP) {α : outParam (Sort _)} (Φ : outParam <| α → PROP) where
  into_forall : P ⊢ ∀ x, Φ x
export IntoForall (into_forall)

@[ipm_class, rocq_alias FromExist]
class FromExists {PROP} [BI PROP] (P : PROP) {α : outParam (Sort _)} (Φ : outParam <| α → PROP) where
  from_exists : (∃ x, Φ x) ⊢ P
export FromExists (from_exists)

@[ipm_class, rocq_alias IntoExist]
class IntoExists {PROP} [BI PROP] (P : PROP) {α : outParam (Sort _)} (Φ : outParam <| α → PROP) where
  into_exists : P ⊢ ∃ x, Φ x
export IntoExists (into_exists)

@[ipm_class, rocq_alias FromAnd]
class FromAnd {PROP} [BI PROP] (P : PROP) (Q1 Q2 : outParam $ PROP) where
  from_and : Q1 ∧ Q2 ⊢ P
export FromAnd (from_and)

@[ipm_class, rocq_alias IntoAnd]
class IntoAnd {PROP} [BI PROP] (p : Bool) (P : PROP) (Q1 Q2 : outParam $ PROP) where
  into_and : □?p P ⊢ □?p (Q1 ∧ Q2)
export IntoAnd (into_and)

@[ipm_class, rocq_alias FromSep]
class FromSep {PROP} [BI PROP] (P : PROP) (Q1 Q2 : outParam $ PROP) where
  from_sep : Q1 ∗ Q2 ⊢ P
export FromSep (from_sep)

@[ipm_class, rocq_alias IntoSep]
class IntoSep {PROP} [BI PROP] (P : PROP) (Q1 Q2 : outParam $ PROP) where
  into_sep : P ⊢ Q1 ∗ Q2
export IntoSep (into_sep)

@[ipm_class, rocq_alias FromOr]
class FromOr {PROP} [BI PROP] (P : PROP) (Q1 Q2 : outParam $ PROP) where
  from_or : Q1 ∨ Q2 ⊢ P
export FromOr (from_or)

@[ipm_class, rocq_alias IntoOr]
class IntoOr {PROP} [BI PROP] (P : PROP) (Q1 Q2 : outParam $ PROP) where
  into_or : P ⊢ Q1 ∨ Q2
export IntoOr (into_or)

@[ipm_class, rocq_alias IntoPersistent]
class IntoPersistently {PROP} [BI PROP] (p : Bool) (P : PROP) (Q : outParam $ PROP) where
  into_persistently : <pers>?p P ⊢ <pers> Q
export IntoPersistently (into_persistently)

@[ipm_class, rocq_alias FromAffinely]
class FromAffinely {PROP} [BI PROP] (P : outParam $ PROP) (Q : PROP) (p : Bool := true) where
  from_affinely : <affine>?p Q ⊢ P
export FromAffinely (from_affinely)

@[ipm_class, rocq_alias IntoAbsorbingly]
class IntoAbsorbingly {PROP} [BI PROP] (P : outParam $ PROP) (Q : PROP) where
  into_absorbingly : P ⊢ <absorb> Q
export IntoAbsorbingly (into_absorbingly)

@[ipm_class, rocq_alias FromAssumption, rocq_alias KnownLFromAssumption, rocq_alias KnownRFromAssumption]
class FromAssumption {PROP} [BI PROP] (p : Bool) (ioP : InOut) (P : semiOutParam $ PROP) (Q : PROP) where
  from_assumption : □?p P ⊢ Q
export FromAssumption (from_assumption)

@[ipm_class, rocq_alias IntoPure, rocq_alias IntoPureT]
class IntoPure {PROP} [BI PROP] (P : PROP) (φ : outParam Prop) where
  into_pure : P ⊢ ⌜φ⌝
export IntoPure (into_pure)

#rocq_ignore into_pureT_hint "IntoPureT is not necessary in Lean"

@[ipm_class, rocq_alias FromPure, rocq_alias FromPureT]
class FromPure {PROP} [BI PROP] (a : outParam $ Bool) (P : PROP) (ioφ : InOut) (φ : semiOutParam $ Prop) where
  from_pure : <affine>?a ⌜φ⌝ ⊢ P
export FromPure (from_pure)

#rocq_ignore from_pureT_hint "FromPureT is not necessary in Lean"

@[ipm_class, rocq_alias IsExcept0]
class IsExcept0 {PROP} [BI PROP] (Q : PROP) where
  is_except0 : ◇ Q ⊢ Q
export IsExcept0 (is_except0)

@[ipm_class, rocq_alias IntoExcept0]
class IntoExcept0 {PROP} [BI PROP] (P : PROP) (Q : outParam $ PROP) where
  into_except0 : P ⊢ ◇ Q
export IntoExcept0 (into_except0)

/--
`FromModal` turns a goal `P : PROP2` into a modality `M : PROP1 → PROP2` applied to `Q : PROP1`
under condition `φ`.

`sel` is an input that can be provided by the user to match on the desired modality to introduce.
It needs to be an `outParam` to make Lean happy since `PROP1` is an `outParam`.
For the IPM TC synthesis, it needs to be an `uncheckedInParam` since it should match all modalities
if the user provides an mvar.
-/
@[ipm_class, rocq_alias FromModal]
class FromModal {PROP1 : outParam $ Type _} {PROP2} [outParam $ BI PROP1] [BI PROP2] (φ : outParam $ Prop)
    (M : outParam $ Modality PROP1 PROP2) (sel : outParam <| uncheckedInParam $ PROP1) (P : PROP2)
    (Q : outParam $ PROP1) where
  from_modal : φ → M.M Q ⊢ P
export FromModal (from_modal)

/-- `ElimModal` turns `□?p P` into `□?p' P'` and `Q` into `Q'` under condition `φ`. -/
@[ipm_class, rocq_alias ElimModal]
class ElimModal {PROP} [BI PROP] (φ : outParam $ Prop) (p : Bool) (p' : outParam $ Bool) (P : PROP)
    (P' : outParam $ PROP) (Q : PROP) (Q' : outParam $ PROP) where
  elim_modal : φ → □?p P ∗ (□?p' P' -∗ Q') ⊢ Q
export ElimModal (elim_modal)

@[ipm_class, rocq_alias Frame]
class Frame {PROP} [BI PROP] (p : Bool) (R P : PROP) (Q : outParam $ PROP) where
  frame : □?p R ∗ Q ⊢ P
export Frame (frame)

/--
`IntoLaterN` turns `P` into `▷^[n] Q`.
The Boolean [only_head] indicates whether laters should only be stripped in head position or also below
other logical connectives. For [inext] it should strip laters below other logical connectives,
but this should not happen while framing.

The Rocq version uses an `MaybeIntoLaterN` typeclass that avoids unfolding definitions for searches
that do not make progress. But this is not necessary in Lean since Lean TC synthesis does not unfold
definitions by default.

This classes is deliberately not an `ipm_class` to use the more efficient TC synthesis.
-/
@[rocq_alias IntoLaterN, rocq_alias MaybeIntoLaterN]
class IntoLaterN {PROP} [BI PROP] (only_head : Bool) (n : Nat) (P : PROP) (Q : outParam $ PROP) where
  into_laterN : P ⊢ ▷^[n] Q
export IntoLaterN (into_laterN)

#rocq_ignore elim_inv_tc_opaque "No tc_opaque in Lean"
#rocq_ignore elim_modal_tc_opaque "No tc_opaque in Lean"
#rocq_ignore from_and_tc_opaque "No tc_opaque in Lean"
#rocq_ignore from_exist_tc_opaque "No tc_opaque in Lean"
#rocq_ignore from_forall_tc_opaque "No tc_opaque in Lean"
#rocq_ignore from_modal_tc_opaque "No tc_opaque in Lean"
#rocq_ignore from_or_tc_opaque "No tc_opaque in Lean"
#rocq_ignore from_pure_tc_opaque "No tc_opaque in Lean"
#rocq_ignore from_sep_tc_opaque "No tc_opaque in Lean"
#rocq_ignore from_wand_tc_opaque "No tc_opaque in Lean"
#rocq_ignore into_and_tc_opaque "No tc_opaque in Lean"
#rocq_ignore into_exist_tc_opaque "No tc_opaque in Lean"
#rocq_ignore into_forall_tc_opaque "No tc_opaque in Lean"
#rocq_ignore into_inv_tc_opaque "No tc_opaque in Lean"
#rocq_ignore into_or_tc_opaque "No tc_opaque in Lean"
#rocq_ignore into_pure_tc_opaque "No tc_opaque in Lean"
#rocq_ignore into_sep_tc_opaque "No tc_opaque in Lean"
#rocq_ignore into_wand_tc_opaque "No tc_opaque in Lean"

end Iris.ProofMode
