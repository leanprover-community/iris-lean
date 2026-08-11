/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.Auth
public import Iris.Algebra.LeibnizMultiSet
meta import Iris.Std.RocqPorting

@[expose] public section

/-!
# Authoritative multisets

The authority owns a multiset and each fragment owns some of its elements: adding an element to
the authority hands out the matching singleton fragment, and returning it removes the element.
-/

open Iris Std CMRA

namespace LeibnizMultiSet

variable {MS : Type _} [LawfulMultiSet MS A]

@[rocq_alias heap_lang.auth_valid_gmultiset_singleton]
theorem auth_valid_singleton {dq : DFrac} {v : A} {g : MS}
    (h : ✓ ((●{dq} .ofSet g : Auth (LeibnizMultiSet MS)) • ◯ LeibnizMultiSet.ofSet {v})) : v ∈ g :=
  singleton_subset_iff.mp (included_iff_subset.mp (Auth.both_dfrac_valid_discrete.mp h).2.1)

theorem auth_alloc_singleton {v : A} {g : MS} :
    (● .ofSet g : Auth (LeibnizMultiSet MS)) ~~>
      (● LeibnizMultiSet.ofSet (g ⊎ {v})) • ◯ LeibnizMultiSet.ofSet {v} := by
  refine Auth.auth_update_alloc ?_
  have h := localUpdate_alloc (X := g) (Y := (∅ : MS)) (X' := {v})
  rwa [disjUnion_empty_left] at h

theorem auth_dealloc_singleton {v : A} {g : MS} :
    ((● .ofSet g : Auth (LeibnizMultiSet MS)) • ◯ LeibnizMultiSet.ofSet {v}) ~~>
      ● LeibnizMultiSet.ofSet (g \ {v}) := by
  refine Auth.auth_update_dealloc ?_
  have h := localUpdate_dealloc (X := g) (Y := ({v} : MS)) (X' := {v}) subset_refl
  rwa [difference_self] at h

end LeibnizMultiSet
