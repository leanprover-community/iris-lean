/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

def try? [Monad m] [MonadExcept ε m] (x : m α) : m (Option α) :=
  try pure (some (← x)) catch _ => pure none
