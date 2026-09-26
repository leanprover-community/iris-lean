/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Iris.Init

@[expose] public section

theorem equivalence_eq : Equivalence (@Eq α) := ⟨.refl, .symm, .trans⟩
