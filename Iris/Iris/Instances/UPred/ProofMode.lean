/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra.IsOp
public import Iris.Instances.UPred.Instance
public import Iris.ProofMode.Classes

@[expose] public section


variable {SI : Iris.stepindex (Type _)} [Iris.SIdx SI]

open Iris BI ORA ProofMode Std

namespace UPred

variable [URA M] [UORA SI M] [UPred.OrdExtend0 SI M]

@[rocq_alias from_sep_ownM]
instance fromSep_ownM {a b1 b2 : M} [h : IsOp .split a b1 b2] :
    FromSep (ownM SI a) (ownM _ b1) (ownM _ b2) where
  from_sep := by rw [h.is_op]; exact (ownM_op ..).mpr

@[rocq_alias combine_sep_as_ownM]
instance (priority := default - 15) combineSepAs_ownM {a b1 b2 : M} [h : IsOp .merge a b1 b2] :
    CombineSepAs (ownM _ b1) (ownM _ b2) (ownM SI a) where
  combine_sep_as := by rw [h.is_op]; exact (ownM_op ..).mpr

@[rocq_alias combine_sep_gives_ownM]
instance combineSepGives_ownM {b1 b2 : M} :
    CombineSepGives (ownM SI b1) (ownM _ b2) iprop(✓[SI] b1 • b2) where
  combine_sep_gives := (ownM_op ..).mpr.trans (ownM_valid _)

@[rocq_alias from_sep_ownM_core_id]
instance fromAnd_ownM_coreId {a b1 b2 : M} [h : IsOp .split a b1 b2]
    [TCOr (CoreId b1) (CoreId b2)] : FromAnd (ownM SI a) (ownM _ b1) (ownM _ b2) where
  from_and := by
    rw [h.is_op]
    refine .trans ?_ (ownM_op ..).mpr
    cases (inferInstance : TCOr (CoreId b1) (CoreId b2)) <;> exact persistent_and_sep_mp

@[rocq_alias into_and_ownM]
instance intoAnd_ownM (p : Bool) {a b1 b2 : M} [h : IsOp .split a b1 b2] [Increasing SI b1]
    [Increasing SI b2] : IntoAnd p (ownM SI a) (ownM _ b1) (ownM _ b2) where
  into_and := intuitionisticallyIf_mono <| by
    rw [h.is_op]
    exact fun _ _ hx => ⟨(ordN_op_left _ b1 b2).trans hx, (ordN_op_right _ b1 b2).trans hx⟩

@[rocq_alias into_sep_ownM]
instance intoSep_ownM {a b1 b2 : M} [h : IsOp .split a b1 b2] :
    IntoSep (ownM SI a) (ownM _ b1) (ownM _ b2) where
  into_sep := by rw [h.is_op]; exact (ownM_op ..).mp

end UPred

end
