/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.Algebra.IsOp
public import Iris.Instances.UPred.Instance
public import Iris.ProofMode.Classes

@[expose] public section

open Iris BI CMRA ProofMode Std

namespace UPred

variable [UCMRA M]

set_option synthInstance.checkSynthOrder false in
@[rocq_alias from_sep_ownM]
instance fromSep_ownM {a b1 b2 : M} [h : IsOp .split a b1 b2] :
    FromSep (ownM a) (ownM b1) (ownM b2) where
  from_sep := by rw [h.is_op]; exact (ownM_op ..).mpr

set_option synthInstance.checkSynthOrder false in
@[rocq_alias combine_sep_as_ownM]
instance (priority := default - 15) combineSepAs_ownM {a b1 b2 : M} [h : IsOp .merge a b1 b2] :
    CombineSepAs (ownM b1) (ownM b2) (ownM a) where
  combine_sep_as := by rw [h.is_op]; exact (ownM_op ..).mpr

@[rocq_alias combine_sep_gives_ownM]
instance combineSepGives_ownM {b1 b2 : M} :
    CombineSepGives (ownM b1) (ownM b2) iprop(✓ b1 • b2) where
  combine_sep_gives := (ownM_op ..).mpr.trans (ownM_valid _)

set_option synthInstance.checkSynthOrder false in
@[rocq_alias from_sep_ownM_core_id]
instance fromAnd_ownM_coreId {a b1 b2 : M} [h : IsOp .split a b1 b2]
    [TCOr (CoreId b1) (CoreId b2)] : FromAnd (ownM a) (ownM b1) (ownM b2) where
  from_and := by
    rw [h.is_op]
    refine .trans ?_ (ownM_op ..).mpr
    cases (inferInstance : TCOr (CoreId b1) (CoreId b2)) <;> exact persistent_and_sep.mp

set_option synthInstance.checkSynthOrder false in
@[rocq_alias into_and_ownM]
instance intoAnd_ownM (p : Bool) {a b1 b2 : M} [h : IsOp .split a b1 b2] :
    IntoAnd p (ownM a) (ownM b1) (ownM b2) where
  into_and := intuitionisticallyIf_mono <| by rw [h.is_op]; exact (ownM_op ..).mp.trans sep_and

set_option synthInstance.checkSynthOrder false in
@[rocq_alias into_sep_ownM]
instance intoSep_ownM {a b1 b2 : M} [h : IsOp .split a b1 b2] :
    IntoSep (ownM a) (ownM b1) (ownM b2) where
  into_sep := by rw [h.is_op]; exact (ownM_op ..).mp

end UPred

end
