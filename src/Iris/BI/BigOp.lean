import Iris.BI.Interface
import Iris.BI.Notation
import Iris.Std.List

namespace Iris.BI

def big_op [BIBase PROP] (ps : List PROP) (f : PROP → PROP → PROP) (unit : PROP) : PROP :=
  ps.foldr1 f (fun _ => unit)

syntax:40 "[∧] " term:max : term
syntax:40 "[∨] " term:max : term
syntax:40 "[∗] " term:max : term

macro_rules
  | `(`[iprop| [∧] $Ps]) => `(big_op `[iprop| $Ps] BIBase.and `[iprop| True])
  | `(`[iprop| [∨] $Ps]) => `(big_op `[iprop| $Ps] BIBase.or `[iprop| False])
  | `(`[iprop| [∗] $Ps]) => `(big_op `[iprop| $Ps] BIBase.sep `[iprop| emp])

delab_rule big_op
  | `(big_op $Ps BIBase.and `[iprop| True])  => do `(`[iprop| [∧] $(← unpackIprop Ps)])
  | `(big_op $Ps BIBase.or  `[iprop| False]) => do `(`[iprop| [∨] $(← unpackIprop Ps)])
  | `(big_op $Ps BIBase.sep `[iprop| emp])   => do `(`[iprop| [∗] $(← unpackIprop Ps)])

end Iris.BI
