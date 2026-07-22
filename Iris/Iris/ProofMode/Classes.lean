/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Michael Sammler, Yunsong Yang, Alvin Tang
-/
module

public import Iris.BI
public meta import Iris.ProofMode.SynthInstance
public import Iris.ProofMode.Modalities
public import Iris.Std.Namespaces

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

meta section

@[reducible]
def AsEmpValid.Direction.toInOut : AsEmpValid.Direction → InOut
  | .into => .in
  | .from => .out

end

@[ipm_class, rocq_alias AsEmpValid]
class AsEmpValid (d : AsEmpValid.Direction) (φ : Prop) io
    (PROP : semiOutParamIPM io (Type _))
    (bi : semiOutParamIPM d.toInOut (BI PROP))
    (P : outParam $ PROP) where
  as_emp_valid : (d = .into → φ → ⊢ P) ∧ (d = .from → (⊢ P) → φ)

@[rocq_alias as_emp_valid_1]
theorem asEmpValid_1 {PROP} [bi : BI PROP] {φ : Prop} (P : PROP) {io}
    (inst : AsEmpValid .into φ io PROP bi P) : φ → ⊢ P :=
  inst.as_emp_valid.left rfl

@[rocq_alias as_emp_valid_2]
theorem asEmpValid_2 {PROP} [bi : BI PROP] {P: PROP} (φ : Prop) {io}
    (inst : AsEmpValid .from φ io PROP bi P) : (⊢ P) → φ :=
  inst.as_emp_valid.right rfl

@[ipm_class, rocq_alias AsEmpValid0]
class AsEmpValid0 (d : AsEmpValid.Direction) (φ : Prop) (io : InOut := d.toInOut)
    (PROP : semiOutParamIPM io (Type _))
    (bi : semiOutParamIPM d.toInOut (BI PROP)) (P : outParam PROP) where
  as_emp_valid_0 : AsEmpValid d φ io PROP bi P

attribute [ipm_backtrack,instance] AsEmpValid0.as_emp_valid_0

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
class FromWand {PROP} [BI PROP] (P : PROP) (io : InOut)
    (Q1 : semiOutParamIPM io PROP) (Q2 : outParam $ PROP) where
  from_wand : (Q1 -∗ Q2) ⊢ P
export FromWand (from_wand)

#rocq_ignore IntoWand' "not used in Lean"

@[ipm_class, rocq_alias IntoWand]
class IntoWand {PROP} [BI PROP] (p q : Bool) (R : PROP)
  (ioP : InOut) (P : semiOutParamIPM ioP PROP)
  (ioQ : InOut) (Q : semiOutParamIPM ioQ PROP) where
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

@[ipm_class, rocq_alias IntoInternalEq]
class IntoInternalEq {PROP} [BI PROP] [Sbi PROP] {A : outParam $ Type _} [ofe : outParam $ OFE A] (P : PROP) (x y : outParam A) where
  into_internal_eq : P ⊢@{PROP} x ≡ y
export IntoInternalEq (into_internal_eq)

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
class FromAssumption {PROP} [BI PROP] (p : Bool) (ioP : InOut)
    (P : semiOutParamIPM ioP PROP) (Q : PROP) where
  from_assumption : □?p P ⊢ Q
export FromAssumption (from_assumption)

@[ipm_class, rocq_alias IntoPure, rocq_alias IntoPureT]
class IntoPure {PROP} [BI PROP] (P : PROP) (φ : outParam Prop) where
  into_pure : P ⊢ ⌜φ⌝
export IntoPure (into_pure)

#rocq_ignore into_pureT_hint "IntoPureT is not necessary in Lean"

@[ipm_class, rocq_alias FromPure, rocq_alias FromPureT]
class FromPure {PROP} [BI PROP] (a : outParam $ Bool) (P : PROP) (ioφ : InOut)
    (φ : semiOutParamIPM ioφ Prop) where
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
class ElimModal {PROP} [BI PROP] (φ : outParam $ Prop) (p : Bool)
    (p' : outParam $ uncheckedInParam Bool) (P : PROP)
    (P' : outParam $ uncheckedInParam PROP) (Q : PROP) (Q' : outParam $ PROP) where
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

/-- `CombineSepAs` combines two propositions `P` and `Q` into `R` -/
@[ipm_class, rocq_alias CombineSepAs]
class CombineSepAs [BI PROP] (P Q : PROP) (R : outParam PROP) where
  combine_sep_as : P ∗ Q ⊢ R
export CombineSepAs (combine_sep_as)

#rocq_ignore MaybeCombineSepAs "No need for progress_indicator"
#rocq_ignore progress_indicator "No longer required as it is only used by the type class MaybeCombineSepAs"
#rocq_ignore maybe_combine_sep_as_combine_sep_as "No longer required along with MaybeCombineSepAs"

/-- `CombineSepGives` combines two propositions `P` and `Q` for a proposition
    with the `<pers>` modality -/
@[ipm_class, rocq_alias CombineSepGives]
class CombineSepGives [BI PROP] (P Q : PROP) (R : outParam PROP) where
  combine_sep_gives : P ∗ Q ⊢ <pers> R
export CombineSepGives (combine_sep_gives)

@[ipm_class, rocq_alias IntoInv]
class IntoInv [BI PROP] (P : PROP) (N : Namespace)

@[rocq_alias accessor]
def accessor [BI PROP] {X : Type} (M1 M2 : PROP → PROP) (α β : X → PROP)
    (mγ : X → Option  PROP) : PROP :=
  M1 iprop(∃ x, α x ∗ (β x -∗ M2 (mγ x |>.getD emp)))

@[ipm_class, rocq_alias ElimAcc]
class ElimAcc [BI PROP] {X : Type} (ϕ : outParam Prop) (M1 M2 : PROP → PROP)
    (α β : X → PROP) (mγ : X → Option PROP) (Q : PROP) (Q' : outParam <| X → PROP) where
  elim_acc : ϕ → ((∀ x, α x -∗ Q' x) -∗ accessor M1 M2 α β mγ -∗ Q)

@[ipm_class, rocq_alias IntoAcc]
class IntoAcc [BI PROP] {X : outParam Type} (Pacc : PROP)
    (ϕ : outParam Prop) (Pin : outParam <| PROP)
    (M1 M2 : outParam <| PROP → PROP) (α β : outParam <| X → PROP)
    (mγ : outParam <| X → Option PROP) where
  into_acc : ϕ → Pacc -∗ Pin -∗ accessor M1 M2 α β mγ

set_option synthInstance.checkSynthOrder false in
/-- The type class used for the `iinv` tactic. -/
@[ipm_class, rocq_alias ElimInv]
class ElimInv [BI PROP] (φ : outParam Prop) (X : outParam Type)
    (Pinv : PROP) (Pin : outParam PROP) (Pout : outParam <| X → PROP)
    (close : Bool) (mPclose : outParam <| Option <| X → PROP)
    (Q : PROP) (Q' : outParam <| X → PROP) where
  elim_inv : φ → Pinv ∗ Pin ∗ (∀ x, (match mPclose with
    | some Pclose => iprop(Pout x ∗ Pclose x -∗ Q' x)
    | none => iprop(Pout x -∗ Q' x))) ⊢ Q
export ElimInv (elim_inv)

/-
  `IntoIH φ P Q` describes how to turn a pure induction hypothesis `φ` into a proofmode
  hypothesis `Q` under an intuitionistic BI context `□ P`.
-/
@[ipm_class, rocq_alias IntoIH]
class IntoIH [BI PROP] (φ : Prop) (P : PROP) (Q : outParam PROP) where
  into_ih : φ → □ P ⊢ Q
export IntoIH (into_ih)

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
