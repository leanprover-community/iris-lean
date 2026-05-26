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

set_option synthInstance.checkSynthOrder false

/--
  A type class that allows merging `b1` and `b2` into `a` as well as
  to split `a` into `b1` and `b2`.
-/
@[ipm_class, rocq_alias IsOp, rocq_alias IsOp', rocq_alias IsOp'LR]
class IsOp [CMRA α]
    (_ : InOut) (a : semiOutParam $ α)
    (_ : InOut) (b1 : semiOutParam α)
    (_ : InOut) (b2 : semiOutParam α) where
  is_op : a ≡ b1 • b2

/--
  Syntactic sugar for specifying whether `IsOp` is used for merging or splitting.
-/
macro_rules
  | `(IsOp merge $a $b1 $b2) => `(IsOp .out $a .in $b1 .in $b2)
  | `(IsOp split $a $b1 $b2) => `(IsOp .in $a .out $b1 .out $b2)

/--
  Merging with `•` should have the lowest priority.
-/
@[rocq_alias is_op_op]
instance (priority := default - 100) isOp_op [CMRA α] (a b : α) :
    IsOp merge (a • b) a b where
  is_op := .rfl

/--
  Splitting with `•` should have the highest priority.
-/
@[rocq_alias is_op_lr_op]
instance (priority := default + 100) isOpSplit_op [CMRA α] (a b : α) :
    IsOp split (a • b) a b where
  is_op := .rfl

/-
  The following type class instances were originally defined in terms of
  both `IsOp` and `IsOp'`. The distinction between `IsOp` and `IsOp'` is no
  longer relevant in Lean, and we use `InOut` instead.

  Note that in the Rocq formulation, the assumptions use `IsOp` while
  the conclusion use `IsOp'`. We therefore use `merge` for the assumptions
  but allow any `InOut` value for the conclusion.
-/

@[rocq_alias is_op_pair]
instance isOpMerge_pair [CMRA α]
    (a b1 b2 : α) (a' b1' b2' : α)
    [h1 : IsOp merge a b1 b2] [h2 : IsOp merge a' b1' b2'] :
    IsOp ioa (a, a') iob1 (b1, b1') iob2 (b2, b2') where
  is_op := ⟨h1.is_op, h2.is_op⟩

@[rocq_alias is_op_pair_core_id_l]
instance isOpMerge_pair_core_id_l [CMRA α] [CMRA β] {ioa iob1 iob2 : InOut}
    (a : α) (a' b1' b2' : β) [h1 : CoreId a] [h2 : IsOp merge a' b1' b2'] :
    IsOp ioa (a, a') iob1 (a, b1') iob2 (a, b2') where
  is_op := ⟨(op_self a).symm, h2.is_op⟩

@[rocq_alias is_op_pair_core_id_r]
instance isOpMerge_pair_core_id_r [CMRA α] [CMRA β] {ioa iob1 iob2 : InOut}
    (a b1 b2 : α) (a' : β)
    [h1 : CoreId a'] [h2 : IsOp merge a b1 b2] :
    IsOp ioa (a, a') iob1 (b1, a') iob2 (b2, a') where
  is_op := ⟨h2.is_op, (op_self a').symm⟩

@[rocq_alias is_op_Some]
instance isOpMerge_some [CMRA α] (a b1 b2 : α) {ioa iob1 iob2 : InOut}
    [h : IsOp merge a b1 b2] :
    IsOp ioa (some a) iob1 (some b1) iob2 (some b2) where
  is_op := h.is_op

end IsOp

end Iris
