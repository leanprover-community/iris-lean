/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/


namespace Set

def Disjoint {X : Type _} (S1 S2 : X → Prop) : Prop :=
  ∀ x : X, ¬(S1 x ∧ S2 x)

def Union {X : Type _} (S1 S2 : X → Prop) : X → Prop :=
  fun x => S1 x ∨ S2 x

def Included {X : Type _} (S1 S2 : X → Prop) : Prop :=
  ∀ x, S1 x → S2 x

end Set
