/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public import Iris.Algebra.StepIndex
public import Iris.Algebra.OFE
public import Iris.Std.Classes
public meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris

namespace OFE

theorem Dist.leNat [OFE α] {m n} {x y : α} (h : x ≡{n}≡ y) (h' : m ≤ n) : x ≡{m}≡ y :=
  if hm : m = n then hm ▸ h else h.lt <| Nat.lt_of_le_of_ne h' hm

theorem Contractive.succNat [OFE α] [OFE β] (f : α → β) [Contractive f] {n x y}
    (h : x ≡{n}≡ y) : f x ≡{n.succ}≡ f y :=
  Contractive.distLater_dist <| distLater_succ.mpr h


end OFE
