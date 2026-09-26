/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Iris.Init

@[expose] public section

namespace Iris.ProofMode

def try? [Monad m] [MonadExcept ε m] (x : m α) : m (Option α) :=
  try pure (some (← x)) catch _ => pure none

end Iris.ProofMode
