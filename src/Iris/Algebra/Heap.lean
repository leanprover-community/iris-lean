/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE

open Iris

/- # Datatype and CMRA for a generic heap-like structure.

Like FunLike in Mathlib, but not exactly the same, since the type must also be able to be updated. -/

open Classical in
noncomputable def fset {K V : Type _} (f : K → V) (k : K) (v : V) : K → V :=
  fun k' => if (k = k') then v else f k'

/-- `T` can store and retrieve keys and values. -/
class StoreLike (T : Type _) (K V : outParam (Type _)) where
  get : T → K → V
  set : T → K → V → T
  of_fun : (K → V) → T
export StoreLike (get set)

/-- `T`'s store and retrieve operations behave like a classical store. -/
class Store (T : Type _) (K V : outParam (Type _)) extends StoreLike T K V where
  get_set {t k v} : get (set t k v) = fset (get t : K → V) k v
  /-- One-sided inverse between get and of_fun. The other direction does not need to hold. -/
  of_fun_get {f} : get (of_fun f) = f

class Alloc (T : Type _) (K : outParam (Type _)) where
  fresh : T → K

/-- A type is HeapLike when it behaves like store for Optional values -/
class Heap (T : Type _) (K V : outParam (Type _)) extends StoreLike T K (Option V), Alloc T K where
  fresh_get {t} : get t (fresh t) = none


namespace Store
variable {T K V : Type _} [Store T K V]

theorem get_set_ne {m : T} (H : k ≠ k') : get (set m k v) k' = get m k' := by
  rw [get_set]; unfold fset; rw [if_neg H]

theorem get_set_eq {m : T} (H : k = k') : get (set m k v) k' = v := by
  rw [get_set]; unfold fset; rw [if_pos H]

end Store


/-- Wrapper type for functions with the Store OFE -/
structure StoreO (T : Type _) where car : T

section algebra

open OFE

/-- The OFE on StoreO is the discrete function OFE on it's .get function. -/
instance StoreO_OFE {T K V : Type _} [StoreLike T K V] [OFE V] : OFE (StoreO T) where
  Equiv s0 s1  := StoreLike.get s0.1 ≡ StoreLike.get s1.1
  Dist n s0 s1 := StoreLike.get s0.1 ≡{n}≡ StoreLike.get s1.1
  dist_eqv     := ⟨fun _ => .of_eq rfl, (·.symm), (·.trans ·)⟩
  equiv_dist   := equiv_dist
  dist_lt      := dist_lt

def StoreO.toMap {T K V : Type _} [StoreLike T K V] [OFE V] : (StoreO T) -n> (K → V) where
  f x := StoreLike.get <| StoreO.car x
  ne.1 {_ _ _} H k := H k

def StoreO.ofMap {T K V : Type _} [Store T K V] [OFE V] : (K → V) -n> (StoreO T) where
  f x := StoreO.mk <| StoreLike.of_fun x
  ne.1 {_ _ _} H k := by rw [Store.of_fun_get, Store.of_fun_get]; exact H k

instance StoreO_COFE {T K V : Type _} [Store T K V] [COFE V] : COFE (StoreO T) where
  compl c := ⟨StoreLike.of_fun <| COFE.compl <| c.map StoreO.toMap⟩
  conv_compl {n c} k := by
    rw [Store.of_fun_get]
    exact COFE.conv_compl (c := Chain.map StoreO.toMap c) k

end algebra
