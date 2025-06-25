/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.Heap
import Iris.Algebra.View
import Iris.Algebra.DFrac

open Iris

namespace heap_view

variable (F K V : Type _) (H : Type _ → Type _) [DFractional F] [∀ T, Heap (H T) K T] [CMRA V]

abbrev heapR (n : Nat) (m : StoreO (H V)) (f : StoreO (H ((DFrac F) × V))) : Prop :=
  let P (k : K) (fv : DFrac F × V) : Prop :=
    ∃ (v : V) (dq : DFrac F), StoreO.get k m = .some v ∧ ✓{n} (dq, v) ∧ (some fv ≼{n} some (dq, v))
  StoreO.all (lift_dom P) f

instance : ViewRel (heapR F K V H) where
  mono := sorry
  rel_validN := sorry
  rel_unit := sorry

abbrev HeapView := View F (heapR F K V H)

-- #synth CMRA (HeapView F K V H)

def heap_view_auth (dq : DFrac F) (m : H V) : HeapView F K V H :=
  ●V{dq} .mk m

def heap_view_frag (k : K) (dq : DFrac F) (v : V) : HeapView F K V H :=
  ◯V .singleton k <| .some (dq, v)


end heap_view
