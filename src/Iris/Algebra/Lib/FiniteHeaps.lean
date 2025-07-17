/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.Heap
import Iris.Algebra.Lib.ClassicalHeaps

/-- Heaps with intrinsically finite domain, represented as an association list.
Keys taken to be Nat for the sake of example. -/

inductive FiniteDomFunction (V : Type _)
| empty : FiniteDomFunction V
| set : Nat → V → FiniteDomFunction V → FiniteDomFunction V
| remove : Nat → FiniteDomFunction V → FiniteDomFunction V

def FiniteDomFunction.lookup (f : FiniteDomFunction V) (k : Nat) : Option V :=
  match f with
  | .empty => none
  | .set n v' rest => if n = k then some v' else rest.lookup k
  | .remove n rest => if n = k then none else rest.lookup k

def FiniteDomFunction.update (f : FiniteDomFunction V) (k : Nat) (v : Option V) : FiniteDomFunction V :=
  match v with
  | some v' => f.set k v'
  | none => f.remove k

instance instFiniteDomStore : Store (FiniteDomFunction V) Nat (Option V) where
  get := FiniteDomFunction.lookup
  set := FiniteDomFunction.update
  merge := sorry
  get_set_eq := sorry
  get_set_ne := sorry
  get_merge := sorry

instance instFiniteDomHeap : Heap (fun V => FiniteDomFunction V) Nat where
  hmap h f := sorry
  hmap_alloc := sorry
  hmap_unalloc := sorry
  empty _ := sorry
  get_empty := sorry

instance instFinitDomAllocHeap : AllocHeap (fun V => FiniteDomFunction V) Nat  where
  notFull f := sorry
  fresh HC := sorry
  get_fresh {_ _ HC} := sorry

instance : UnboundedHeap (fun V => FiniteDomFunction V) Nat where
  notFull_empty := by sorry
  notFull_set_fresh {V t v H} := by sorry
