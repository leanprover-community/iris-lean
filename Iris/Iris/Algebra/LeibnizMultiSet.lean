/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.BigOp
public import Iris.Algebra.CMRA
public import Iris.Algebra.LocalUpdates
public import Iris.Algebra.Updates
public import Iris.Std.GenMultiSets

@[expose] public section

variable {SI : Type _} [instSI : Iris.SIdx SI]

/-! ## The multiset union ORA -/

open Iris Std ORA OFE

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

instance : COFE SI (LeibnizMultiSet MS) := COFE.ofDiscrete _

namespace LeibnizMultiSet

variable {MS : Type _} [LawfulMultiSet MS A]

open MultiSet

/-- The operation and core as step-index-free data instances (Mathlib-style). -/
instance : Op (LeibnizMultiSet MS) where
  op | ofSet X, ofSet Y => ofSet (X ⊎ Y)
  assoc := by grind
  comm := by grind

instance : PCore (LeibnizMultiSet MS) where
  pcore _ := some (ofSet ∅)
  pcore_idem := id

instance instRA : RA (LeibnizMultiSet MS) where
  pcore_op_left {_ X} := by cases X; rintro ⟨rfl⟩; exact congrArg ofSet disjUnion_empty_left

instance instURA : URA (LeibnizMultiSet MS) where
  unit := .ofSet ∅
  unit_left_id {X} := by cases X; exact congrArg ofSet disjUnion_empty_left
  pcore_unit := rfl
  total _ := ⟨.ofSet ∅, rfl⟩

@[reducible] def cmraData : CMRAData SI (LeibnizMultiSet MS) where
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne _ _ _ H := by rw [(H : _ = _)] <;> exact .rfl
  pcore_ne {_ _ _ cx} _ H := ⟨cx, H, .rfl⟩
  validN_ne _ _ := trivial
  valid_iff_validN := by simp
  validN_le _ _ := trivial
  validN_op_left _ := trivial
  extend {_ _ _ _} _ h := ⟨_, _, h, .rfl, .rfl⟩
  pcore_op_mono h _ :=
    ⟨.ofSet ∅, by cases h; exact congrArg (some ∘ ofSet) disjUnion_empty_left.symm⟩

instance : CMRA SI (LeibnizMultiSet MS) := ofCMRAData LeibnizMultiSet.cmraData

theorem ucmraData : UCMRAData SI (LeibnizMultiSet MS) where
  unit_valid := trivial

instance instUnital : UCMRA SI (LeibnizMultiSet MS) := UORA.ofUCMRAData LeibnizMultiSet.ucmraData

@[rocq_alias gmultiset_cmra_discrete]
instance : ORA.Discrete SI (LeibnizMultiSet MS) where
  discrete_0 h := h
  discrete_valid := id
  discrete_ord | ⟨z, hz⟩ => ⟨z, hz⟩

@[rocq_alias gmultiset_op]
theorem op_disjUnion (X Y : MS) : (ofSet X) • (ofSet Y) = ofSet (X ⊎ Y) := rfl
attribute [local grind =] op_disjUnion

@[rocq_alias gmultiset_core]
theorem core_eq_empty (X : LeibnizMultiSet MS) : core X = ofSet ∅ := rfl

@[rocq_alias gmultiset_opM]
theorem opM_disjUnion (X : LeibnizMultiSet MS) (mY : Option (LeibnizMultiSet MS)) :
    X •? mY = X • mY.getD (ofSet ∅) := by
  cases X; cases mY <;> simp [op?, op, disjUnion_empty_right]

@[rocq_alias gmultiset_included]
theorem included_iff_subset {X Y : MS} : ofSet X ≼ ofSet Y ↔ X ⊆ Y where
  mp | ⟨_, h⟩ => ofSet.inj h ▸ disjUnion_subset_left
  mpr h := ⟨ofSet (Y \ X), congrArg ofSet (disjUnion_difference_of_subseteq h)⟩

theorem ord_iff_subset {X Y : MS} : ofSet X ≼ₒ[SI] ofSet Y ↔ X ⊆ Y :=
  inc_iff_ord.symm.trans included_iff_subset

@[rocq_alias gmultiset_cancelable]
instance (X : LeibnizMultiSet MS) : Cancelable SI X := discrete_cancelable fun {Y Z} _ h => by grind

@[rocq_alias gmultiset_update]
theorem update (X Y : MS) : ofSet X ~~>[SI] ofSet Y := fun _ _ _ => trivial

@[rocq_alias gmultiset_local_update]
theorem localUpdate {X Y X' Y' : MS} (h : X ⊎ Y' = X' ⊎ Y) :
    (ofSet X, ofSet Y) ~l~>[SI] (ofSet X', ofSet Y') := by
  refine (local_update_unital_discrete ..).mpr fun ⟨Z⟩ _ e => ⟨trivial, ?_⟩
  refine congrArg ofSet (LawfulMultiSet.ext fun a => ?_)
  grind [multiplicity_disjUnion]

@[rocq_alias gmultiset_local_update_alloc]
theorem localUpdate_alloc {X Y X' : MS} :
    (ofSet X, ofSet Y) ~l~>[SI] (ofSet (X ⊎ X'), ofSet (Y ⊎ X')) :=
  localUpdate <| LawfulMultiSet.ext fun _ => by simp only [multiplicity_disjUnion]; omega

@[rocq_alias gmultiset_local_update_dealloc]
theorem localUpdate_dealloc {X Y X' : MS} (h : X' ⊆ Y) :
    (ofSet X, ofSet Y) ~l~>[SI] (ofSet (X \ X'), ofSet (Y \ X')) := by
  refine LocalUpdate.total_valid fun _ _ le => localUpdate (LawfulMultiSet.ext fun a => ?_)
  simp only [multiplicity_disjUnion, multiplicity_difference]
  grind [subset_iff, (ord_iff_subset (SI := SI)).mp le]

end LeibnizMultiSet

namespace LeibnizMultiSet
open Algebra

variable {MS : Type _} [LawfulFiniteMultiSet MS A]

@[rocq_alias big_opMS_singletons]
theorem bigOpMS_singletons (X : MS) :
    ([^ op mset] x ∈ X, (ofSet {x} : LeibnizMultiSet MS)) = ofSet X := by
  induction X using multiset_ind with
  | empty => exact BigOpMS.bigOpMS_empty
  | disjUnion_singleton a X ih => rw [BigOpMS.bigOpMS_insert, ih, op_disjUnion]

end LeibnizMultiSet
