/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/

namespace Iris.Std

/-- Fold a binary operator `f` over a list of `PROP`s. If the list is empty, `unit` is returned. -/
def bigOp (f : PROP → PROP → PROP) (unit : PROP) : List PROP → PROP
  | []      => unit
  | [P]     => P
  | P :: Ps => f P (bigOp f unit Ps)
