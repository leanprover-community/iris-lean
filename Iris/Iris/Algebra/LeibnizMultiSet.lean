/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.BigOp
public import Iris.Algebra.CMRA
public import Iris.Algebra.LocalUpdates
public import Iris.Algebra.Updates
public import Iris.Std.GenMultiSets
meta import Iris.Std.RocqPorting

@[expose] public section

/-! ## The multiset union CMRA -/

open Iris Std CMRA OFE

@[grind!, rocq_alias gmultisetO, rocq_alias gmultisetR, rocq_alias gmultisetUR]
inductive LeibnizMultiSet (MS : Type _) where
  | ofSet (X : MS)

#rocq_ignore gmultiset_valid_instance "Provided by the `CMRA (LeibnizMultiSet MS)` instance."
#rocq_ignore gmultiset_validN_instance "Provided by the `CMRA (LeibnizMultiSet MS)` instance."
#rocq_ignore gmultiset_unit_instance "Provided by the `UCMRA (LeibnizMultiSet MS)` instance."
#rocq_ignore gmultiset_op_instance "Provided by the `CMRA (LeibnizMultiSet MS)` instance."
#rocq_ignore gmultiset_pcore_instance "Provided by the `CMRA (LeibnizMultiSet MS)` instance."
#rocq_ignore gmultiset_ra_mixin "Provided by the `CMRA (LeibnizMultiSet MS)` instance."
#rocq_ignore gmultiset_ucmra_mixin "Provided by the `UCMRA (LeibnizMultiSet MS)` instance."

instance : COFE (LeibnizMultiSet MS) := COFE.ofDiscrete _

namespace LeibnizMultiSet

variable {MS : Type _} [LawfulMultiSet MS A]

open MultiSet

instance : CMRA (LeibnizMultiSet MS) where
  pcore _ := some (ofSet ∅)
  op | ofSet X, ofSet  Y => ofSet (X ⊎ Y)
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne _ _ _ H := by rw [(H : _ = _)]
  pcore_ne {_ _ _ cx} _ H := ⟨cx, H, .rfl⟩
  validN_ne _ _ := trivial
  valid_iff_validN := by simp
  validN_succ _ := trivial
  validN_op_left _ := trivial
  assoc := by grind
  comm := by grind
  pcore_op_left {_ X} := by cases X; rintro ⟨rfl⟩; exact congrArg ofSet disjUnion_empty_left
  pcore_idem := id
  pcore_op_mono {_ X} := by
    rintro ⟨rfl⟩ _
    exists .ofSet ∅
    grind
  extend {_ _ _ _} _ h := ⟨_, _, h, .rfl, .rfl⟩

instance : UCMRA (LeibnizMultiSet MS) where
  unit := .ofSet ∅
  unit_valid := trivial
  unit_left_id {X} := by cases X; exact congrArg ofSet disjUnion_empty_left
  pcore_unit := rfl

@[rocq_alias gmultiset_cmra_discrete]
instance : CMRA.Discrete (LeibnizMultiSet MS) where
  discrete_0 h := h
  discrete_valid := id

instance : CMRA.IsTotal (LeibnizMultiSet MS) where
  total _ := ⟨.ofSet ∅, rfl⟩

@[rocq_alias gmultiset_op]
theorem op_disjUnion (X Y : MS) : (ofSet X) • (ofSet Y) = ofSet (X ⊎ Y) := rfl

@[rocq_alias gmultiset_core]
theorem core_eq_empty (X : LeibnizMultiSet MS) : core X = ofSet ∅ := rfl

@[rocq_alias gmultiset_opM]
theorem opM_disjUnion (X : LeibnizMultiSet MS) (mY : Option (LeibnizMultiSet MS)) :
    X •? mY = X • mY.getD (ofSet ∅) := by
  cases X; cases mY <;> simp [op?, op, disjUnion_empty_right]

@[rocq_alias gmultiset_included]
theorem included_iff_subset {X Y : MS} : ofSet X ≼ ofSet Y ↔ X ⊆ Y where
  mp | ⟨.ofSet _, h⟩ => ofSet.inj h ▸ disjUnion_subset_left
  mpr h := ⟨ofSet (Y \ X), congrArg ofSet (disjUnion_difference_of_subseteq h)⟩

@[rocq_alias gmultiset_cancelable]
instance (X : LeibnizMultiSet MS) : CMRA.Cancelable X :=
  discrete_cancelable fun {Y Z} _ h => by
    cases X; cases Y; cases Z
    exact congrArg ofSet (disjUnion_left_inj (ofSet.inj h))

@[rocq_alias gmultiset_update]
theorem update (X Y : MS) : ofSet X ~~> ofSet Y := fun _ _ _ => trivial

@[rocq_alias gmultiset_local_update]
theorem localUpdate {X Y X' Y' : MS} (h : X ⊎ Y' = X' ⊎ Y) :
    (ofSet X, ofSet Y) ~l~> (ofSet X', ofSet Y') := by
  refine (local_update_unital_discrete ..).mpr fun ⟨Z⟩ _ e => ⟨trivial, ?_⟩
  refine congrArg ofSet (LawfulMultiSet.ext fun a => ?_)
  have : multiplicity a X + multiplicity a Y' = multiplicity a X' + multiplicity a Y := by
    simp [← multiplicity_disjUnion, congrArg (multiplicity a) h]
  have : multiplicity a X = multiplicity a Y + multiplicity a Z := by
    simp [← multiplicity_disjUnion, congrArg (multiplicity a) (ofSet.inj e)]
  suffices H : multiplicity a X' = multiplicity a Y' + multiplicity a Z  by
    simp [← multiplicity_disjUnion, H]
  omega

@[rocq_alias gmultiset_local_update_alloc]
theorem localUpdate_alloc {X Y X' : MS} :
    (ofSet X, ofSet Y) ~l~> (ofSet (X ⊎ X'), ofSet (Y ⊎ X')) :=
  localUpdate <| LawfulMultiSet.ext fun _ => by simp only [multiplicity_disjUnion]; omega

@[rocq_alias gmultiset_local_update_dealloc]
theorem localUpdate_dealloc {X Y X' : MS} (h : X' ⊆ Y) :
    (ofSet X, ofSet Y) ~l~> (ofSet (X \ X'), ofSet (Y \ X')) := by
  refine LocalUpdate.total_valid fun _ _ inc => localUpdate (LawfulMultiSet.ext fun a => ?_)
  simp only [multiplicity_disjUnion, multiplicity_difference]
  have _ : multiplicity a Y ≤ multiplicity a X  := subset_iff.mp (included_iff_subset.mp inc) a
  have _ : multiplicity a X' ≤ multiplicity a Y := subset_iff.mp h a
  omega

end LeibnizMultiSet

namespace LeibnizMultiSet
open Algebra

variable {MS : Type _} [LawfulFiniteMultiSet MS A]

@[rocq_alias big_opMS_singletons]
theorem bigOpMS_singletons (X : MS) :
    ([^ CMRA.op mset] x ∈ X, (ofSet {x} : LeibnizMultiSet MS)) = ofSet X := by
  induction X using multiset_ind with
  | empty => exact BigOpMS.bigOpMS_empty
  | disjUnion_singleton a X ih => rw [BigOpMS.bigOpMS_insert, ih, op_disjUnion]

end LeibnizMultiSet
