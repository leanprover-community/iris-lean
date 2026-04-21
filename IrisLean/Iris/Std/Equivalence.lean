/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

@[expose] public section

theorem equivalence_eq : Equivalence (@Eq α) := ⟨.refl, .symm, .trans⟩
