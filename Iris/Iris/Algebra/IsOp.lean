/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Alvin Tang
-/
module

public import Iris.Algebra.CMRA
meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris

open CMRA

section IsOp


/--
  A type class for splitting `a` into `b1` and `b2`, as well as to merge `b1`
  and `b2` into `a`.
-/
@[rocq_alias IsOp]
class IsOp [CMRA α] (a : outParam α) (b1 b2 : α) where
  is_op : a ≡ b1 • b2

@[rocq_alias is_op_op]
instance (priority := default + 100) isOp_op [CMRA α] (a b : α) : IsOp (a • b) a b where
  is_op := .rfl

#rocq_ignore IsOp' "separate type class is no longer necessary"

-- @[rocq_alias IsOp']
-- class IsOp' [CMRA α] (a b1 b2 : α) where
--   is_op' : IsOp a b1 b2

#rocq_ignore IsOp'LR "seperate type class is no longer necessary"

-- @[rocq_alias IsOp'LR]
-- class IsOp'LR [CMRA α] (a b1 b2 : α) where
--   is_op_lr : IsOp a b1 b2

#rocq_ignore is_op_lr_op "no longer necessary as IsOp'LR is not relevant"

-- @[rocq_alias is_op_lr_op]
-- instance isOp_lr_op [CMRA α] (a b : α) : IsOp'LR (a • b) a b where
--   is_op_lr := ⟨.rfl⟩

/- The following type class instances were originally defined for `IsOp'`. -/

@[rocq_alias is_op_pair]
instance isOp_pair [CMRA α] (a b1 b2 : α) (a' b1' b2' : α)
    [h1 : IsOp a b1 b2] [h2 : IsOp a' b1' b2'] : IsOp (a, a') (b1, b1') (b2, b2') where
  is_op := ⟨h1.is_op, h2.is_op⟩

@[rocq_alias is_op_pair_core_id_l]
instance isOp_pair_core_id_l [CMRA α] [CMRA β] (a : α) (a' b1' b2' : β)
    [h1 : CoreId a] [h2 : IsOp a' b1' b2'] : IsOp (a, a') (a, b1') (a, b2') where
  is_op := ⟨(op_self a).symm, h2.is_op⟩

@[rocq_alias is_op_pair_core_id_r]
instance isOp_pair_core_id_r [CMRA α] [CMRA β] (a b1 b2 : α) (a' : β)
    [h1 : CoreId a'] [h2 : IsOp a b1 b2] : IsOp (a, a') (b1, a') (b2, a') where
  is_op := ⟨h2.is_op, (op_self a').symm⟩

@[rocq_alias is_op_Some]
instance isOp_some [CMRA α] (a b1 b2 : α)
    [h : IsOp a b1 b2] : IsOp (some a) (some b1) (some b2) where
  is_op := h.is_op

end IsOp

end Iris
