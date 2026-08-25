/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Michael Sammler, Yunsong Yang, Alvin Tang
-/
module

public import Iris.BI
public import Iris.ProofMode.Modalities

@[expose] public section

namespace Iris.ProofMode
open Iris.BI Std

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
    (bi : semiOutParamIPM io (BI PROP))
    (P : outParam PROP) where
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
class AsEmpValid0 (d : AsEmpValid.Direction) (φ : Prop) (io : InOut)
    (PROP : semiOutParamIPM io (Type _))
    (bi : semiOutParamIPM io (BI PROP))
    ioP (P : semiOutParamIPM ioP PROP) where
  as_emp_valid_0 : AsEmpValid d φ io PROP bi P

@[ipm_backtrack]
instance asEmpValid_of_asEmpValid0 (d : AsEmpValid.Direction) (φ : Prop) io
    (PROP : Type _) (bi : BI PROP) (P : PROP)
    [inst : AsEmpValid0 d φ io PROP bi .out P] :
    AsEmpValid d φ io PROP bi P := inst.as_emp_valid_0

/- Depending on the use case, type classes with the prefix `From` or `Into` are used. Type classes
with the prefix `From` are used to generate one or more propositions *from* which the original
proposition can be derived. Type classes with the prefix `Into` are used to generate propositions
*into* which the original proposition can be turned by derivation. Additional boolean flags are
used to indicate that certain propositions should be intuitionistic. -/

@[ipm_class, rocq_alias FromImpl]
class FromImp {PROP} [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_imp : (Q1 → Q2) ⊢ P
export FromImp (from_imp)

@[ipm_class, rocq_alias FromWand]
class FromWand {PROP} [BI PROP] (P : PROP) (io : InOut)
    (Q1 : semiOutParamIPM io PROP) (Q2 : outParam PROP) where
  from_wand : (Q1 -∗ Q2) ⊢ P
export FromWand (from_wand)

inductive WandMode.Side where
  | argument
  | result

/--
[WandMode] describes the modings of a two-sided class `IntoWand`, by recording whether each of the
argument and result slots is an input or an output.

`unknown` leaves both slots as outputs, and corresponds to Rocq's `IntoWand` (Hint Mode `- -`).
`matching s` makes the slot `s` an input, and corresponds to Rocq's `IntoWand'`
(Hint Modes `! -` and `- !`).

The priority of `matching` mode instances (such as `intoWand_bupd_args`) must stay below that of
every instance with `unknown` (such as `intoWand_bupd`). This mirrors the priority `100` on
Rocq's `into_wand_wand'`.
-/
inductive WandMode where
  | unknown
  | matching (s : WandMode.Side)

meta section

/-- Whether the argument slot of a class at mode `m` is an input or an output. -/
@[reducible]
def WandMode.argIO : WandMode → InOut
  | .unknown => .out
  | .matching .argument => .in
  | .matching .result => .out


/-- Whether the result slot of a class at mode `m` is an input or an output. -/
@[reducible]
def WandMode.resIO : WandMode → InOut
  | .unknown => .out
  | .matching .argument => .out
  | .matching .result => .in

end

#rocq_ignore IntoWand' "the `matching` mode of `IntoWand` subsumes it"

@[ipm_class, rocq_alias IntoWand]
class IntoWand {PROP} [BI PROP] (p q : Bool) (R : PROP) (m : WandMode)
    (P : semiOutParamIPM m.argIO PROP)
    (Q : semiOutParamIPM m.resIO PROP) where
  into_wand : □?p R ⊢ □?q P -∗ Q
export IntoWand (into_wand)

@[ipm_class, rocq_alias FromForall]
class FromForall {PROP} [BI PROP] (P : PROP)
    {α : outParam (Sort _)} (Ψ : outParam <| α → PROP) where
  from_forall : (∀ x, Ψ x) ⊢ P
export FromForall (from_forall)

@[ipm_class, rocq_alias IntoForall]
class IntoForall {PROP} [BI PROP] (P : PROP)
    {α : outParam (Sort _)} (Φ : outParam <| α → PROP) where
  into_forall : P ⊢ ∀ x, Φ x
export IntoForall (into_forall)

@[ipm_class, rocq_alias FromExist]
class FromExists {PROP} [BI PROP] (P : PROP)
    {α : outParam (Sort _)} (Φ : outParam <| α → PROP) where
  from_exists : (∃ x, Φ x) ⊢ P
export FromExists (from_exists)

@[ipm_class, rocq_alias IntoExist]
class IntoExists {PROP} [BI PROP] (P : PROP)
    {α : outParam (Sort _)} (Φ : outParam <| α → PROP) where
  into_exists : P ⊢ ∃ x, Φ x
export IntoExists (into_exists)

@[ipm_class, rocq_alias FromAnd]
class FromAnd {PROP} [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_and : Q1 ∧ Q2 ⊢ P
export FromAnd (from_and)

@[ipm_class, rocq_alias IntoAnd]
class IntoAnd {PROP} [BI PROP] (p : Bool) (P : PROP) (Q1 Q2 : outParam PROP) where
  into_and : □?p P ⊢ □?p (Q1 ∧ Q2)
export IntoAnd (into_and)

@[ipm_class, rocq_alias FromSep]
class FromSep {PROP} [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_sep : Q1 ∗ Q2 ⊢ P
export FromSep (from_sep)

@[ipm_class, rocq_alias IntoSep]
class IntoSep {PROP} [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  into_sep : P ⊢ Q1 ∗ Q2
export IntoSep (into_sep)

@[ipm_class, rocq_alias FromOr]
class FromOr {PROP} [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_or : Q1 ∨ Q2 ⊢ P
export FromOr (from_or)

@[ipm_class, rocq_alias IntoOr]
class IntoOr {PROP} [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  into_or : P ⊢ Q1 ∨ Q2
export IntoOr (into_or)

@[ipm_class, rocq_alias IntoInternalEq]
class IntoInternalEq {PROP} [BI PROP] [Sbi PROP] {A : outParam $ Type _}
    [ofe : outParam $ OFE A] (P : PROP) (x y : outParam A) where
  into_internal_eq : P ⊢@{PROP} x ≡ y
export IntoInternalEq (into_internal_eq)

@[ipm_class, rocq_alias IntoPersistent]
class IntoPersistently {PROP} [BI PROP] (p : Bool) (P : PROP) (Q : outParam PROP) where
  into_persistently : <pers>?p P ⊢ <pers> Q
export IntoPersistently (into_persistently)

@[ipm_class, rocq_alias FromAffinely]
class FromAffinely {PROP} [BI PROP] (P : outParam PROP) (Q : PROP) (p : Bool := true) where
  from_affinely : <affine>?p Q ⊢ P
export FromAffinely (from_affinely)

@[ipm_class, rocq_alias IntoAbsorbingly]
class IntoAbsorbingly {PROP} [BI PROP] (P : outParam PROP) (Q : PROP) where
  into_absorbingly : P ⊢ <absorb> Q
export IntoAbsorbingly (into_absorbingly)

@[ipm_class, rocq_alias FromAssumption,
  rocq_alias KnownLFromAssumption, rocq_alias KnownRFromAssumption]
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
class IntoExcept0 {PROP} [BI PROP] (P : PROP) (Q : outParam PROP) where
  into_except0 : P ⊢ ◇ Q
export IntoExcept0 (into_except0)

/--
`FromModal` turns a goal `P : PROP2` into a modality `M : PROP1 → PROP2` applied
to `Q : PROP1` under condition `φ`. The modality `M` is usually an output, except
for specific recursive instances for embedding.

The selector `sel` is an input that can be provided by the user to match on the
desired modality to introduce. This is unique in a sense that the metavariable
is supplied as an input (e.g. when the user writes `imodintro _`).
This is why `uncheckedInParam` is used so that all modalities can be matched by
IPM type class synthesis.
It also needs to be an `outParam` as `PROP1` can be an output parameter.
-/
@[ipm_class, rocq_alias FromModal]
class FromModal (io : InOut)
    {PROP1 : semiOutParamIPM io (Type _)}
    {PROP2} {α : outParam <| uncheckedInParam <| Type _}
    [semiOutParamIPM io (BI PROP1)] [BI PROP2]
    (M : semiOutParamIPM io (Modality PROP1 PROP2))
    (φ : outParam Prop)
    (sel : outParam <| uncheckedInParam α) (P : PROP2) (Q : outParam PROP1) where
  from_modal : φ → M.M Q ⊢ P
export FromModal (from_modal)

/-- `ElimModal` turns `□?p P` into `□?p' P'` and `Q` into `Q'` under condition `φ`. -/
@[ipm_class, rocq_alias ElimModal]
class ElimModal {PROP} [BI PROP] (φ : outParam Prop) (p : Bool) (io : InOut)
    (p' : semiOutParamIPM io Bool) (P : PROP)
    (P' : semiOutParamIPM io PROP) (Q : PROP) (Q' : outParam PROP) where
  elim_modal : φ → □?p P ∗ (□?p' P' -∗ Q') ⊢ Q
export ElimModal (elim_modal)

/--
`AddModal` is used by `ispecialize` and `ihave _ : _` to add a modality to the
goal corresponding to the premise/asserted proposition.
-/
@[ipm_class, rocq_alias AddModal]
class AddModal {PROP} [BI PROP] (P : outParam PROP) (P' Q : PROP) where
  add_modal : P ∗ (P' -∗ Q) ⊢ Q
export AddModal (add_modal)

@[rocq_alias add_modal_id]
theorem addModal_id {PROP} [BI PROP] (P Q : PROP) : AddModal P P Q where
  add_modal := wand_elim_right

@[ipm_class, rocq_alias IsCons]
class IsCons {α} (l : List α) (x : outParam α) (xs : outParam <| List α) where
  is_cons : l = x :: xs
export IsCons (is_cons)

@[ipm_class, rocq_alias IsApp]
class IsApp {α} (l : List α) (l1 l2 : outParam (List α)) where
  is_app : l = l1 ++ l2
export IsApp (is_app)

@[rocq_alias is_cons_cons]
instance isCons_cons {α} (x : α) (xs : List α) : IsCons (x :: xs) x xs where
  is_cons := rfl

@[rocq_alias is_app_app]
instance isApp_app {α} (l1 l2 : List α) : IsApp (l1 ++ l2) l1 l2 where
  is_app := rfl

@[ipm_class, rocq_alias IsDisjUnion]
class IsDisjUnion {MS A : Type _} [FiniteMultiSet MS A]
    (X : MS) (X₁ X₂ : outParam MS) : Prop where
  is_disj_union : X = X₁ ⊎ X₂
export IsDisjUnion (is_disj_union)

@[rocq_alias is_disj_union_disj_union]
instance isDisjUnion_disjUnion {MS A : Type _} [FiniteMultiSet MS A] (X₁ X₂ : MS) :
    IsDisjUnion (A := A) (X₁ ⊎ X₂) X₁ X₂ where
  is_disj_union := rfl

@[ipm_class, rocq_alias Frame]
class Frame {PROP} [BI PROP] (p : Bool) (R P : PROP) (Q : outParam PROP) where
  frame : □?p R ∗ Q ⊢ P
export Frame (frame)

@[ipm_class, rocq_alias FrameInstantiateExistDisabled]
class FrameInstantiateExistDisabled {PROP} [BI PROP] (p : Bool)
    (R P : PROP) (Q : outParam PROP) where
  frame_instantiatiate_exist_disabled : Frame p R P Q
export FrameInstantiateExistDisabled (frame_instantiatiate_exist_disabled)

/--
`IntoLaterN` turns `P` into `▷^[n] Q`.
The Boolean [only_head] indicates whether laters should only be stripped in head position or
also below other logical connectives. For [inext] it should strip laters below other logical
connectives, but this should not happen while framing.

Instead of implementing `MaybeIntoLaterN` as in Rocq, we introduce `progress`
as an additional parameter of `IntoLaterN` to indicate the instance must strip at least one
later modality. Recursive instances should set `progress` to `true` in the call to
`IntoLaterN` for the subexpression such that the recursive instance only applies when something
changes in the subexpression. Otherwise, the default instance `intoLaterN_default` applies.
-/
@[ipm_class, rocq_alias MaybeIntoLaterN, rocq_alias IntoLaterN]
class IntoLaterN {PROP} [BI PROP] (progress only_head : Bool) (n : Nat)
    (P : PROP) (Q : outParam PROP) where
  into_laterN : P ⊢ ▷^[n] Q
export IntoLaterN (into_laterN)

/-- `CombineSepAs` combines two propositions `P` and `Q` into `R` -/
@[ipm_class, rocq_alias CombineSepAs]
class CombineSepAs [BI PROP] (P Q : PROP) (R : outParam PROP) where
  combine_sep_as : P ∗ Q ⊢ R
export CombineSepAs (combine_sep_as)

#rocq_ignore MaybeCombineSepAs "No need for progress_indicator"
#rocq_ignore progress_indicator
  "No longer required as it is only used by the type class MaybeCombineSepAs"
#rocq_ignore maybe_combine_sep_as_combine_sep_as
  "No longer required along with MaybeCombineSepAs"

/-- `CombineSepGives` combines two propositions `P` and `Q` for a proposition
    with the `<pers>` modality -/
@[ipm_class, rocq_alias CombineSepGives]
class CombineSepGives [BI PROP] (P Q : PROP) (R : outParam PROP) where
  combine_sep_gives : P ∗ Q ⊢ <pers> R
export CombineSepGives (combine_sep_gives)

#rocq_ignore CombineSepsAs "Iteration is done directly within the metaprogram in Lean"
#rocq_ignore CombineSepsAsGives "Iteration is done directly within the metaprogram in Lean"

@[ipm_class, rocq_alias IntoInv]
class IntoInv [BI PROP] (P : PROP) (N : Namespace)

@[rocq_alias accessor]
def accessor [BI PROP] {X : Type} (M1 M2 : PROP → PROP) (α β : X → PROP)
    (mγ : X → Option  PROP) : PROP :=
  M1 iprop(∃ x, α x ∗ (β x -∗ M2 (mγ x |>.getD emp)))

@[ipm_class, rocq_alias ElimAcc]
class ElimAcc [BI PROP] {X : Type} (φ : outParam Prop) (M1 M2 : PROP → PROP)
    (α β : X → PROP) (mγ : X → Option PROP) (Q : PROP) (Q' : outParam <| X → PROP) where
  elim_acc : φ → ((∀ x, α x -∗ Q' x) -∗ accessor M1 M2 α β mγ -∗ Q)

@[ipm_class, rocq_alias IntoAcc]
class IntoAcc [BI PROP] {X : outParam Type} (Pacc : PROP)
    (φ : outParam Prop) (Pin : outParam PROP)
    (M1 M2 : outParam <| PROP → PROP) (α β : outParam <| X → PROP)
    (mγ : outParam <| X → Option PROP) where
  into_acc : φ → Pacc -∗ Pin -∗ accessor M1 M2 α β mγ

set_option synthInstance.checkSynthOrder false in
/-- The type class used for the `iinv` tactic. -/
@[ipm_class, rocq_alias ElimInv]
class ElimInv [BI PROP] (φ : outParam Prop) (X : outParam Type)
    (Pinv : PROP) (Pin : outParam PROP) (Pout : outParam <| X → PROP)
    (close : Bool) (mPclose : outParam <| Option <| X → PROP)
    (Q : PROP) (Q' : outParam <| X → PROP) where
  elim_inv : φ → Pinv ∗ Pin ∗ (∀ x, Pout x ∗ mPclose.getD (λ _ => emp) x -∗ Q' x) ⊢ Q
export ElimInv (elim_inv)

/-
  `IntoIH φ P Q` describes how to turn a pure induction hypothesis `φ` into a proofmode
  hypothesis `Q` under an intuitionistic BI context `□ P`.
-/
@[ipm_class, rocq_alias IntoIH]
class IntoIH [BI PROP] (φ : Prop) (P : PROP) (Q : outParam PROP) where
  into_ih : φ → □ P ⊢ Q
export IntoIH (into_ih)

@[ipm_class, rocq_alias IntoEmbed]
class IntoEmbed [BI PROP1] [BI PROP2] [BiEmbed PROP1 PROP2]
    (P : PROP2) (Q : outParam PROP1) where
  into_embed : P ⊢ ⎡Q⎤
export IntoEmbed (into_embed)

#rocq_ignore IntoEmpValid "Not needed as recursion is handled directly by metaprogramming"

#rocq_ignore AffineEnv
  "Environment-related type classes are not needed as Expr.lean (Hyps) provides the infrastructure"
#rocq_ignore IntoModalIntuitionisticEnv
  "Environment-related definitions are not needed as Expr.lean (Hyps) provides the infrastructure"
#rocq_ignore IntoModalSpatialEnv
  "Environment-related definitions are not needed as Expr.lean (Hyps) provides the infrastructure"
#rocq_ignore MaybeIntoLaterNEnvs
  "Environment-related type classes are not needed as Expr.lean (Hyps) provides the infrastructure"
#rocq_ignore TransformIntuitionisticEnv
  "Environment-related type classes are not needed as Expr.lean (Hyps) provides the infrastructure"
#rocq_ignore TransformSpatialEnv
  "Environment-related type classes are not needed as Expr.lean (Hyps) provides the infrastructure"

#rocq_ignore transform_intuitionistic_env_nil
  "Type class IntoModalIntuitionisticEnv is not needed in Lean"
#rocq_ignore transform_intuitionistic_env_snoc
  "Type class IntoModalIntuitionisticEnv is not needed in Lean"
#rocq_ignore transform_intuitionistic_env_snoc_not
  "Type IntoModalIntuitionisticEnv class is not needed in Lean"
#rocq_ignore transform_spatial_env_nil "Type class TransformSpatialEnv is not needed in Lean"
#rocq_ignore transform_spatial_env_snoc "Type class TransformSpatialEnv is not needed in Lean"
#rocq_ignore transform_spatial_env_snoc_not "Type class TransformSpatialEnv is not needed in Lean"
#rocq_ignore affine_env_bi "Type class AffineEnv is not needed in Lean"
#rocq_ignore affine_env_nil "Type class AffineEnv is not needed in Lean"
#rocq_ignore affine_env_snoc "Type class AffineEnv is not needed in Lean"
#rocq_ignore affine_env_spatial "Type class AffineEnv is not needed in Lean"
#rocq_ignore into_laterN_env_sound "Environment-related theorem not relevant in Lean"
#rocq_ignore into_laterN_envs "Environment-related type class instance not relevant in Lean"

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
