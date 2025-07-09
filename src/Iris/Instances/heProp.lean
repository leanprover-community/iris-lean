/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Instances.UPred
import Iris.Instances.UPred.Instance
import Iris.Algebra.HeapView
import Iris.Algebra.Heap
import Iris.Algebra.Agree
import Iris.Algebra.OFE

/-
# Iris 0.5: a step-indexed separation logic with a heap

- Paramaterized by a type of indices `K`, values `V`, and heap type `H`
- Fixes the global CMRA as contain a single ghost map, with values `Agree (Leibniz V)`
- Derived points-to connective
- Should be sufficient to define a weakest precondition in the usual Iris style
-/

abbrev Option.lift (f : A → B) : Option A → Option B
| .some a => .some <| f a
| .none => .none

open Iris

section heProp

variable (F K V : Type _) (H : Type _ → Type _) [UFraction F] [∀ T, Heap (H T) K T]

abbrev heProp := UPred (HeapView F K (Agree (LeibnizO V)) H)

def heProp_auth (m : H V) : heProp F K V H :=
  UPred.ownM <| ●V StoreO.map (.lift <| toAgree ∘ .mk) ⟨m⟩

def heProp_frag (m : H V) : heProp F K V H :=
  UPred.ownM <| ◯V StoreO.map (.lift fun v => (.own One.one, toAgree <| .mk v)) ⟨m⟩

def heProp_elem (k : K) (v : V) : heProp F K V H :=
  heProp_frag F K V H (WithPoints.point k (.some v))

notation k " ↦ " v => heProp_elem k v

end heProp
