import Iris.Instances.Classical.Instance

namespace Iris.Instances.Classical
open Iris.Instances.Data

def maps_to (l : Nat) (v : Val) : HeapProp Val :=
  fun state => state l = result v

syntax:52 term:53 " ↦ " term:53 : term

macro_rules
  | `(`[iprop| $l ↦ $v]) => `(maps_to $l $v)

delab_rule maps_to
  | `($_ $l $v) => `(`[iprop| $l ↦ $v])

end Iris.Instances.Classical
