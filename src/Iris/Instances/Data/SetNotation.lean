/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/

namespace Iris.Instances.Data

class Disjoint (α : Type u) where
  disjoint : α → α → Prop
infix:60 " || " => Disjoint.disjoint

end Iris.Instances.Data
