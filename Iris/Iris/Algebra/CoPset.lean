/-
Copyright (c) 2026 Сухарик. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Сухарик (@suhr)
-/

module

public import Iris.Std.CoPset
public import Iris.Std.GenSets
public import Iris.Algebra.OFE
public import Iris.Algebra.CMRA
public import Iris.Algebra.Updates
public import Iris.Algebra.LocalUpdates

namespace Iris

@[expose] public section

open Iris Std CoPset LawfulSet

instance : COFE CoPset := COFE.ofDiscrete _ Eq_Equivalence

instance : OFE.Discrete CoPset where
  discrete_0 := id

instance : OFE.Leibniz CoPset where
  eq_of_eqv := id

instance : CMRA CoPset where
  pcore := some
  Valid _ := True
  ValidN _ _ := True
  op := union
  op_ne {x} := { ne := fun ⦃n⦄ ⦃x₁ x₂⦄ => congrArg x.union }
  pcore_ne {n x y cx} e pe := ⟨y, rfl, by grind⟩
  validN_ne _ := id
  valid_iff_validN := { mp _ := fun _ => ⟨⟩, mpr h := h 0 }
  validN_succ := id
  validN_op_left := id
  assoc := union_assoc
  comm := union_comm
  pcore_op_left {x cx} h := by cases h;  exact union_idem
  pcore_idem h := by cases h; rfl
  pcore_op_mono h y := ⟨y, by cases h; rfl⟩
  extend {n x y₁ y₂} _ exy := ⟨y₁, y₂, exy, rfl, rfl⟩

instance : CMRA.Discrete CoPset where
  discrete_valid _ := ⟨⟩

instance : UCMRA CoPset where
  unit := ∅
  unit_valid := ⟨⟩
  unit_left_id := union_empty_left
  pcore_unit := rfl

instance : CMRA.IsTotal CoPset where
  total _ := Option.isSome_iff_exists.mp rfl

theorem CoPset.valid (x : CoPset) : ✓ x := ⟨⟩
theorem CoPset.validN (x : CoPset) : ✓{n} x := ⟨⟩

@[rocq_alias coPset_op]
theorem CoPset.op_eq_union (x y : CoPset) : x • y = x ∪ y := rfl

@[rocq_alias coPset_core]
theorem CoPset.core_eq_self (x : CoPset) : CMRA.core x = x := rfl

@[rocq_alias coPset_included]
theorem CoPset.inc_iff_subset {x y : CoPset} : x ≼ y ↔ x ⊆ y where
  mp := fun ⟨z, (hz : y = x ∪ z)⟩ => by simp [hz, union_subset_left]
  mpr h := ⟨y \ x, show y = x ∪ y \ x from (subset_union_diff h).symm⟩

@[rocq_alias coPset_opM]
theorem CoPset.opM_eq_union (x : CoPset) (my : Option CoPset) : x •? my = x ∪ my.getD ∅ :=
  match my with
  | none => union_empty_right.symm
  | some _ => rfl

@[rocq_alias coPset_update]
theorem CoPset.update (x y : CoPset) : x ~~> y := fun _ _ _ => ⟨⟩

@[rocq_alias coPset_local_update]
theorem CoPset.local_update (x y x' : CoPset) (h : x ⊆ x') : (x, y) ~l~> (x', x') := by
  refine fun n mz _ e => ⟨⟨⟩, CoPset.ext_iff.mpr fun p => ?_⟩
  grind [opM_eq_union, mem_union, h p, CoPset.ext_iff.mp e p]


-- The disjoint union CMRA

public inductive CoPsetDisj where
| set     : CoPset → CoPsetDisj
| invalid : CoPsetDisj

namespace CoPsetDisj

instance : EmptyCollection CoPsetDisj where
  emptyCollection := .set ∅

instance : Membership Pos CoPsetDisj where
  mem s x :=
    match s with
    | .set s   => x ∈ s
    | .invalid => False

theorem mem_empty (p : Pos) : ¬p ∈ (∅ : CoPsetDisj) := CoPset.mem_empty
theorem exist_set_of_mem {x : CoPsetDisj} (h : p ∈ x) : ∃x', x = .set x' :=
  match x with
  | invalid => by simp [Membership.mem] at h
  | set x' => ⟨x', rfl⟩

instance : COFE CoPsetDisj := COFE.ofDiscrete _ Eq_Equivalence

instance : OFE.Discrete CoPsetDisj where
  discrete_0 := id

instance : OFE.Leibniz CoPsetDisj where
  eq_of_eqv := id

theorem mem_of_eqv {a b : CoPsetDisj} (eqv : a ≡ b) (mx : x ∈ a) : x ∈ b :=
  match a, b with
  | .invalid, _ => False.elim mx
  | .set a, .invalid => by simp at eqv
  | .set a, .set b => by simpa [← show _ = _ from eqv]

def Valid : CoPsetDisj → Prop
| .set _ => True
| .invalid => False

def op : CoPsetDisj → CoPsetDisj → CoPsetDisj
| .set x, .set y => if x ## y then .set (x ∪ y) else .invalid
| _, _ => .invalid

theorem op_invalid_right (x : CoPsetDisj) : x.op .invalid = invalid :=
  by cases x <;> rfl

theorem op_invalid_left (x : CoPsetDisj) : (CoPsetDisj.invalid).op x = .invalid :=
  by cases x <;> rfl

theorem op_empty_left (x : CoPsetDisj) : (CoPsetDisj.set ∅).op x = x :=
  match x with
  | .set x => by simp [CoPsetDisj.op, disjoint_empty_left]
  | .invalid => rfl

theorem op_assoc (x y z : CoPsetDisj) : x.op (y.op z) = (x.op y).op z :=
  match x, y, z with
  | .invalid, _ ,_ => by simp [op_invalid_left]
  | _, .invalid ,_ => by simp [op_invalid_left, op_invalid_right]
  | _, _ , .invalid => by simp [op_invalid_right]
  | .set x, .set y, .set z => by
    unfold CoPsetDisj.op
    grind [disjoint_union_left, disjoint_union_right, union_assoc]

theorem op_comm (x y : CoPsetDisj) : x.op y = y.op x :=
  match x, y with
  | .invalid, _ => by simp [op_invalid_left, op_invalid_right]
  | _, .invalid => by simp [op_invalid_left, op_invalid_right]
  | .set x, .set y => by
    unfold CoPsetDisj.op
    if h: x ## y then simp [h, disjoint_comm, union_comm]
    else simp [h, disjoint_comm]

instance : CMRA CoPsetDisj where
  pcore _ := some (.set ∅)
  Valid := Valid
  ValidN _ := Valid
  op := CoPsetDisj.op
  op_ne {x} := { ne ⦃n⦄ ⦃x₁ x₂⦄ h := OFE.Dist.of_eq (congrArg x.op h) }
  pcore_ne {n x y cx} e pe := ⟨.set ∅, rfl, by rw [Option.some_inj.mp pe]⟩
  validN_ne h := h ▸ id
  valid_iff_validN := { mp h := fun _ => h, mpr h := h 0 }
  validN_succ := id
  validN_op_left {n x y} :=
    match x, y with
    | .set x, _ => fun _ => ⟨⟩
    | .invalid, _ => by simp [op_invalid_left]
  assoc {x y z} := op_assoc _ _ _
  comm {x y} := op_comm _ _
  pcore_op_left {x cx} h := by cases h; simp [op_empty_left]
  pcore_idem h := by cases h; rfl
  pcore_op_mono h y := ⟨.set ∅, by cases h; simp only [OFE.leibniz, op_empty_left]⟩
  extend {n x y₁ y₂} _ exy := ⟨y₁, y₂, exy, rfl, rfl⟩

@[rocq_alias coPset_disjR]
instance : CMRA.Discrete CoPsetDisj where
  discrete_valid := id

instance : UCMRA CoPsetDisj where
  unit := ∅
  unit_valid := ⟨⟩
  unit_left_id := CMRA.pcore_op_left' rfl
  pcore_unit := rfl

instance : CMRA.IsTotal CoPsetDisj where
  total _ := Option.isSome_iff_exists.mp rfl

theorem core_empty (x : CoPsetDisj) : CMRA.core x = ∅ := rfl

theorem valid_set : ✓ set s := ⟨⟩
theorem validN_set : ✓{n} set s := ⟨⟩

theorem not_valid_invalid : ¬ ✓ invalid := False.elim
theorem not_validN_invalid : ¬ ✓{n} invalid := False.elim

@[rocq_alias coPset_disj_union]
theorem set_op_eq_union {x y : CoPset} (disj : x ## y)
    : set x • set y = set (x ∪ y) := by simp [CMRA.op, CoPsetDisj.op, disj]

theorem set_op_eq_op {x y : CoPset} (disj : x ## y) : set x • set y = set (x • y) :=
  set_op_eq_union disj

@[rocq_alias coPset_disj_included]
theorem inc_iff_subset {x y : CoPset} : set x ≼ set y ↔ x ⊆ y where
  mp := fun ⟨z, (hz : set y = set x • z)⟩ => by
    cases z with
    | set z =>
      if h : x ## z then
        simp [CMRA.op, CoPsetDisj.op, h] at hz
        simp [hz, union_subset_left]
      else
        simp [CMRA.op, CoPsetDisj.op, h] at hz
    | invalid => simp [CMRA.op, CoPsetDisj.op] at hz
  mpr h :=
    ⟨set (y \ x), set_op_eq_op disjoint_diff_right ▸ congrArg set (subset_union_diff h).symm⟩

theorem mem_iff_of_valid_union {x y : CoPsetDisj} (v : ✓ x • y) (a : Pos)
    : a ∈ x • y ↔ a ∈ x ∨ a ∈ y := by
  match x, y with
  | .invalid, _ => simp [CMRA.op, op_invalid_left] at v; exact v.elim
  | _, .invalid => simp [CMRA.op, op_invalid_right] at v; exact v.elim
  | .set x, .set y =>
    if h : x ## y then
      simp [CMRA.op, CoPsetDisj.op, h]
      exact in_union
    else
      simp [CMRA.op, CoPsetDisj.op, h] at v; exact v.elim

theorem mem_iff_of_validN_union {n : Nat} {x y : CoPsetDisj} (v : ✓{n} x • y) (a : Pos)
    : a ∈ x • y ↔ a ∈ x ∨ a ∈ y := mem_iff_of_valid_union v a

@[rocq_alias coPset_disj_valid_op]
theorem disj_iff_valid_set_op_set {x y : CoPset} : ✓ set x • set y ↔ x ## y := by
  simp [CMRA.Valid, Valid, CMRA.op, op]
  grind

theorem not_mem_of_mem_and_valid_op_left {x y : CoPsetDisj} (v : ✓ x • y) {p : Pos} (m : p ∈ x)
    : ¬ p ∈ y := by
  intro h
  have ⟨x', hx⟩ := exist_set_of_mem m
  have ⟨y', hy⟩ := exist_set_of_mem h
  have : ¬ x' ## y' := fun hh =>
    hh p ⟨show p ∈ set x' from hx ▸ m, show p ∈ set y' from hy ▸ h⟩
  exact absurd (disj_iff_valid_set_op_set.mp (hx ▸ hy ▸ v)) this

theorem not_mem_of_mem_and_valid_op_right {x y : CoPsetDisj} (v : ✓ x • y) {p : Pos} (m : p ∈ y)
    : ¬ p ∈ x := not_mem_of_mem_and_valid_op_left ((OFE.Equiv.valid CMRA.comm).mp v) m
