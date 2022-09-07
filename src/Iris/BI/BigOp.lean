import Iris.BI.Interface
import Iris.BI.Notation

namespace Iris.BI

def big_op [BIBase PROP] (f : PROP → PROP → PROP) (unit : PROP) : List PROP → PROP
  | []      => unit
  | [P]     => P
  | P :: Ps => f P (big_op f unit Ps)

syntax:40 "[∧] " term:max : term
syntax:40 "[∨] " term:max : term
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
