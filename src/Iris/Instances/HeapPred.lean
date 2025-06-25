/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Instances.UPred
import Iris.Algebra.HeapView
import Iris.Algebra.Agree
import Iris.Algebra.OFE

/-
# Iris 0.5: a step-indexed separation logic with a heap

- Paramaterized by a type of indices `K`, values `V`, and heap type `H`
- Fixes the global CMRA as contain a single ghost map, with values `Auth (Leibniz V)`
- Derived points-to connective
- Should be sufficient to define a weakest precondition in the usual Iris style
-/

open Iris

section heProp

variable (F K V : Type _) (H : Type _ → Type _) [DFractional F] [∀ T, Heap (H T) K T]

abbrev heProp := UPred (HeapView F K /- (Auth (LeibnizO V)) -/ Unit  H)



end heProp
