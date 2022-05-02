import Iris.BI.Interface
import Iris.Std.List

namespace Iris.BI

def bigOp [BIBase PROP] (ps : List PROP) (f : PROP → PROP → PROP) (unit : PROP) : PROP :=
  ps.foldr1 f (fun _ => unit)

syntax:37 "[∧] " term:max : term
syntax:37 "[∨] " term:max : term
syntax:37 "[∗] " term:max : term

macro_rules
  | `(`[iprop| [∧] $Ps]) => `(bigOp `[iprop| $Ps] BIBase.and `[iprop| True])
  | `(`[iprop| [∨] $Ps]) => `(bigOp `[iprop| $Ps] BIBase.or `[iprop| False])
  | `(`[iprop| [∗] $Ps]) => `(bigOp `[iprop| $Ps] BIBase.sep `[iprop| emp])

end Iris.BI
