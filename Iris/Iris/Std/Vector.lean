/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Init

/-! # Vector Lemmas -/

@[expose] public section

namespace Vector

/-- Build a vector from a list of the right length. -/
def ofList (l : List α) (h : l.length = n) : Vector α n := ⟨l.toArray, by simp [h]⟩

@[simp] theorem toList_ofList {l : List α} {h : l.length = n} : (ofList l h).toList = l := by
  simp [ofList]

/-- Prepend an element to a vector. -/
def cons (x : α) (v : Vector α n) : Vector α (n + 1) := v.insertIdx 0 x

@[simp] theorem toList_cons {x : α} {v : Vector α n} : (cons x v).toList = x :: v.toList := by
  simp [cons, Vector.insertIdx, Vector.toList]

end Vector
