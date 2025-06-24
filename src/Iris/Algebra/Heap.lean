/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE

/- # Datatype and CMRA for a generic heap-like structure -/

open Classical in
noncomputable def fset {K V : Type _} (f : K → V) (k : K) (v : V) : K → V :=
  fun k' => if (k = k') then v else f k'

/-- `T` can store and retrieve keys and values. -/
class StoreLike (T K V : Type _) where
  get : T → K → V
  set : T → K → V → T
export StoreLike (get set)

/-- `T`'s store and retrieve operations behave like a classical store. -/
class Store (T K V : Type _) extends StoreLike T K V where
  get_set {t k v} : get (set t k v) = fset (get t : K → V) k v

/-- A type is HeapLike when it behaves like store for Optional values -/
class abbrev HeapLike (T K V : Type _) := StoreLike T K (Option V)
