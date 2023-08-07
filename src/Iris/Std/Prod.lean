/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
namespace Prod

/-- Apply `f` to all elements of a tuple. All elements of the tuple must have the same type `α`. -/
def mapAllM [Monad M] (f : α → M β) : α × α → M (β × β)
  | (x, y) => do return (← f x, ← f y)

end Prod
