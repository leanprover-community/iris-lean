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

inductive IsOp.Direction
| merge
| split

meta section

@[reducible]
def IsOp.Direction.mapToInOut (d : IsOp.Direction) : InOut :=
  match d with | merge => .out | split => .in

end

/--
  A type class that allows merging `b1` and `b2` into `a` as well as
  to split `a` into `b1` and `b2`.
-/
@[ipm_class, rocq_alias IsOp, rocq_alias IsOp', rocq_alias IsOp'LR]
class IsOp [CMRA α]
    (d : IsOp.Direction) (a : semiOutParam <| inOutParam d.mapToInOut α)
    (b1 : semiOutParam <| inOutParam d.mapToInOut.negate α)
    (b2 : semiOutParam <| inOutParam d.mapToInOut.negate α) where
  is_op : a ≡ b1 • b2

set_option synthInstance.checkSynthOrder false in
/-- Merging with `•` should have the lowest priority. -/
@[rocq_alias is_op_op]
instance (priority := default - 100) isOpMerge_op [CMRA α] (a b : α) :
    IsOp .merge (a • b) a b where
  is_op := .rfl

set_option synthInstance.checkSynthOrder false in
/-- Splitting with `•` should have the highest priority. -/
@[rocq_alias is_op_lr_op]
instance (priority := default + 100) isOpSplit_op [CMRA α] (a b : α) :
    IsOp .split (a • b) a b where
  is_op := .rfl

/-
  The following type class instances were originally defined in terms of
  both `IsOp` and `IsOp'` in Rocq. The distinction between `IsOp` and `IsOp'` is no
  longer relevant in Lean, and we use `InOut` instead.
-/

@[rocq_alias is_op_pair]
instance isOp_pair [CMRA α] {d : IsOp.Direction} (a b1 b2 : α) (a' b1' b2' : α)
    [h1 : IsOp d a b1 b2] [h2 : IsOp d a' b1' b2'] :
    IsOp d (a, a') (b1, b1') (b2, b2') where
  is_op := OFE.equiv_prod_ext h1.is_op h2.is_op

set_option synthInstance.checkSynthOrder false in
@[rocq_alias is_op_pair_core_id_l]
instance isOp_pair_core_id_l [CMRA α] [CMRA β] {d : IsOp.Direction}
    (a : α) (a' b1' b2' : β) [h1 : CoreId a] [h2 : IsOp d a' b1' b2'] :
    IsOp d (a, a') (a, b1') (a, b2') where
  is_op := OFE.equiv_prod_ext (op_self a).symm h2.is_op

set_option synthInstance.checkSynthOrder false in
@[rocq_alias is_op_pair_core_id_r]
instance isOpMerge_pair_core_id_r [CMRA α] [CMRA β] {d : IsOp.Direction}
    (a b1 b2 : α) (a' : β) [h1 : CoreId a'] [h2 : IsOp d a b1 b2] :
    IsOp d (a, a') (b1, a') (b2, a') where
  is_op := OFE.equiv_prod_ext h2.is_op (op_self a').symm

@[rocq_alias is_op_Some]
instance isOp_some [CMRA α] (a b1 b2 : α) {d : IsOp.Direction}
    [h : IsOp d a b1 b2] : IsOp d (some a) (some b1) (some b2) where
  is_op := h.is_op

end IsOp

end Iris
