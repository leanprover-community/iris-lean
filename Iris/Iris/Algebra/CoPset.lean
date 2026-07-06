/-
Copyright (c) 2026 TODO: fill in author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TODO: fill in author
-/
module

public import Iris.Algebra.LeibnizSet
public import Iris.Std.CoPset
meta import Iris.Std.RocqPorting

@[expose] public section

/-! ## The coPset CMRAs

Two resource algebras over sets of positives (`CoPset`), each obtained as an instance of the
generic set-CMRA construction in `Iris/Algebra/LeibnizSet.lean`:

* the *union* CMRA `LeibnizSet CoPset`, in which every element is valid and composition is set
  union;
* the *disjoint union* CMRA `DisjointLeibnizSet CoPset`, in which composition of two sets is only
  valid when they are disjoint.
-/

open Iris Std CMRA OFE LawfulSet

namespace Iris

/-! ### The union CMRA -/

/-- The union CMRA over `CoPset` -/
@[rocq_alias coPsetO, rocq_alias coPsetR, rocq_alias coPsetUR]
abbrev CoPsetL := LeibnizSet CoPset

#rocq_ignore coPset_valid_instance "Provided by the `CMRA (LeibnizSet S)` instance."
#rocq_ignore coPset_unit_instance "Provided by the `UCMRA (LeibnizSet S)` instance."
#rocq_ignore coPset_op_instance "Provided by the `CMRA (LeibnizSet S)` instance."
#rocq_ignore coPset_pcore_instance "Provided by the `CMRA (LeibnizSet S)` instance."
#rocq_ignore coPset_ra_mixin "Provided by the `CMRA (LeibnizSet S)` instance."
#rocq_ignore coPset_cmra_discrete "Provided by the generic `CMRA.Discrete (LeibnizSet S)` instance."
#rocq_ignore coPset_ucmra_mixin "Provided by the `UCMRA (LeibnizSet S)` instance."

@[rocq_alias coPset_opM]
theorem CoPsetL.opM_union (X : LeibnizSet CoPset) (mY : Option (LeibnizSet CoPset)) :
    X •? mY = X • mY.getD (LeibnizSet.valid ∅) := by
  cases mY <;> simp [op?, op, union_empty_right]

@[rocq_alias coPset_update]
theorem CoPsetL.update (X Y : CoPset) : LeibnizSet.valid X ~~> LeibnizSet.valid Y :=
  fun _ _ _ => trivial

@[rocq_alias coPset_local_update]
theorem CoPsetL.local_update (X Y X' : CoPset) (H : X ⊆ X') :
    (LeibnizSet.valid X, LeibnizSet.valid Y) ~l~> (LeibnizSet.valid X', LeibnizSet.valid X') := by
  refine (LocalUpdate.discrete ..).mpr fun mz _ e => ⟨trivial, ?_⟩
  match mz with
  | none => rfl
  | some (.valid Z) =>
    simp only [op?, op, leibniz, LeibnizSet.valid.injEq] at e ⊢
    have hZ : Z ⊆ X' := subset_trans union_subset_right (e ▸ H)
    rw [union_comm, union_subset_absorption hZ]

/-! ### The disjoint union CMRA -/

/-- The disjoint union CMRA over `CoPset` -/
@[rocq_alias coPset_disj, rocq_alias coPset_disjO, rocq_alias coPset_disjR, rocq_alias coPset_disjUR]
abbrev CoPsetDisjL := DisjointLeibnizSet CoPset

#rocq_ignore coPset_disj_valid_instance "Provided by the `CMRA (DisjointLeibnizSet S)` instance."
#rocq_ignore coPset_disj_unit_instance "Provided by the `UCMRA (DisjointLeibnizSet S)` instance."
#rocq_ignore coPset_disj_op_instance "Provided by the `CMRA (DisjointLeibnizSet S)` instance."
#rocq_ignore coPset_disj_pcore_instance "Provided by the `CMRA (DisjointLeibnizSet S)` instance."
#rocq_ignore coPset_disj_ra_mixin "Provided by the `CMRA (DisjointLeibnizSet S)` instance."
#rocq_ignore coPset_disj_cmra_discrete "Provided by `CMRA.Discrete (DisjointLeibnizSet S)`."
#rocq_ignore coPset_disj_ucmra_mixin "Provided by the `UCMRA (DisjointLeibnizSet S)` instance."

end Iris
