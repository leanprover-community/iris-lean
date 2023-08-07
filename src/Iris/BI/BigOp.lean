/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.BI.Interface
import Iris.BI.Notation

namespace Iris.BI

/-- Fold a binary operator `f` over a list of `PROP`s. If the list is empty, `unit` is returned. -/
def big_op [BIBase PROP] (f : PROP → PROP → PROP) (unit : PROP) : List PROP → PROP
  | []      => unit
  | [P]     => P
  | P :: Ps => f P (big_op f unit Ps)

/-- Fold the conjunction `∧` over a list of separation logic propositions. -/
syntax:40 "[∧] " term:max : term
/-- Fold the disjunction `∨` over a list of separation logic propositions. -/
syntax:40 "[∨] " term:max : term
/-- Fold the separating conjunction `∗` over a list of separation logic propositions. -/
syntax:40 "[∗] " term:max : term

macro_rules
  | `(`[iprop| [∧] $Ps]) => ``(big_op BIBase.and `[iprop| True] `[iprop| $Ps])
  | `(`[iprop| [∨] $Ps]) => ``(big_op BIBase.or `[iprop| False] `[iprop| $Ps])
  | `(`[iprop| [∗] $Ps]) => ``(big_op BIBase.sep `[iprop| emp] `[iprop| $Ps])

delab_rule big_op
  | `($_ BIBase.and `[iprop| True]  $Ps) => do ``(`[iprop| [∧] $(← unpackIprop Ps)])
  | `($_ BIBase.or  `[iprop| False] $Ps) => do ``(`[iprop| [∨] $(← unpackIprop Ps)])
  | `($_ BIBase.sep `[iprop| emp]   $Ps) => do ``(`[iprop| [∗] $(← unpackIprop Ps)])

end Iris.BI
