/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
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
def cons (x : α) (v : Vector α n) : Vector α (n + 1) := ofList (x :: v.toList) (by simp)

@[simp] theorem toList_cons {x : α} {v : Vector α n} : (cons x v).toList = x :: v.toList := by
  simp [cons]

end Vector
