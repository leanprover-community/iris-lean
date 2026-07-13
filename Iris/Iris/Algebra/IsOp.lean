/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Alvin Tang
-/
module

public import Iris.Algebra.CMRA
public import Iris.ProofMode.SynthInstanceAttr
meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris

open CMRA ProofMode

section IsOp

/--
  A type class that allows merging `b1` and `b2` into `a` as well as
  to split `a` into `b1` and `b2`.
-/
@[ipm_class, rocq_alias IsOp, rocq_alias IsOp', rocq_alias IsOp'LR]
class IsOp [CMRA α]
    (io : InOut) (a : semiOutParamPos io α)
    (b1 : semiOutParamNeg io α)
    (b2 : semiOutParamNeg io α) where
  is_op : a ≡ b1 • b2

/--
  Syntactic sugar for specifying whether `IsOp` is used for merging or splitting.
-/
abbrev IsOpMerge [CMRA α] (a b1 b2 : α) := IsOp .out a b1 b2
abbrev IsOpSplit [CMRA α] (a b1 b2 : α) := IsOp .in a b1 b2

set_option synthInstance.checkSynthOrder false in
/--
  Merging with `•` should have the lowest priority.
-/
@[rocq_alias is_op_op]
instance (priority := default - 100) isOpMerge_op [CMRA α] (a b : α) :
    IsOpMerge (a • b) a b where
  is_op := .rfl

set_option synthInstance.checkSynthOrder false in
/--
  Splitting with `•` should have the highest priority.
-/
@[rocq_alias is_op_lr_op]
instance (priority := default + 100) isOpSplit_op [CMRA α] (a b : α) :
    IsOpSplit (a • b) a b where
  is_op := .rfl

/-
  The following type class instances were originally defined in terms of
  both `IsOp` and `IsOp'` in Rocq. The distinction between `IsOp` and `IsOp'` is no
  longer relevant in Lean, and we use `InOut` instead.
-/

@[rocq_alias is_op_pair]
instance isOp_pair [CMRA α] {io : InOut}
    (a b1 b2 : α) (a' b1' b2' : α)
    [h1 : IsOp io a b1 b2] [h2 : IsOp io a' b1' b2'] :
    IsOp io (a, a') (b1, b1') (b2, b2') where
  is_op := OFE.equiv_prod_ext h1.is_op h2.is_op

set_option synthInstance.checkSynthOrder false in
@[rocq_alias is_op_pair_core_id_l]
instance isOp_pair_core_id_l [CMRA α] [CMRA β] {io : InOut}
    (a : α) (a' b1' b2' : β) [h1 : CoreId a] [h2 : IsOp io a' b1' b2'] :
    IsOp io (a, a') (a, b1') (a, b2') where
  is_op := OFE.equiv_prod_ext (op_self a).symm h2.is_op

set_option synthInstance.checkSynthOrder false in
@[rocq_alias is_op_pair_core_id_r]
instance isOpMerge_pair_core_id_r [CMRA α] [CMRA β] {io : InOut}
    (a b1 b2 : α) (a' : β)
    [h1 : CoreId a'] [h2 : IsOp io a b1 b2] :
    IsOp io (a, a') (b1, a') (b2, a') where
  is_op := OFE.equiv_prod_ext h2.is_op (op_self a').symm

@[rocq_alias is_op_Some]
instance isOp_some [CMRA α] (a b1 b2 : α) {io : InOut}
    [h : IsOp io a b1 b2] :
    IsOp io (some a) (some b1) (some b2) where
  is_op := h.is_op

end IsOp

end Iris
