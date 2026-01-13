/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.BI.BigOp.BigOp
import Iris.BI.BigOp.BigSepList
import Iris.BI.BigOp.BigSepSet
import Iris.BI.Instances
import Iris.Std.FiniteMapDom
import Iris.Std.List
import Iris.Std.TC

namespace Iris.BI

open Iris.Algebra
open Iris.Std
open Iris.Std (domSet ofSet)
open BIBase

/-! # Big Separating Conjunction over Maps

Rocq Iris: `iris/bi/big_op.v`, Section `sep_map` -/

variable {PROP : Type _} [BI PROP]
variable {K : Type u} {M : Type u' → Type _}  {V : Type _}
variable [DecidableEq K] [DecidableEq V] [FiniteMap K M] [FiniteMapLaws K M]

namespace BigSepM

/-! ## Basic Structural Lemmas -/

/-- Corresponds to `big_sepM_empty` in Rocq Iris. -/
@[simp]
theorem empty {Φ : K → V → PROP} :
    ([∗map] k ↦ x ∈ (∅ : M V), Φ k x) ⊣⊢ emp := by
  simp only [bigSepM, FiniteMapLaws.map_to_list_empty, bigOpL]
  exact .rfl

/-- Corresponds to `big_sepM_empty'` in Rocq Iris. -/
theorem empty' {P : PROP} [Affine P] {Φ : K → V → PROP} :
    P ⊢ [∗map] k ↦ x ∈ (∅ : M V), Φ k x :=
  Affine.affine.trans empty.2

/-- Corresponds to `big_sepM_singleton` in Rocq Iris. -/
theorem singleton {Φ : K → V → PROP} {k : K} {v : V} :
    ([∗map] k' ↦ x ∈ ({[k := v]} : M V), Φ k' x) ⊣⊢ Φ k v := by
  simp only [bigSepM, FiniteMap.singleton]
  -- bigOpM Φ (insert ∅ k v) ≡ Φ k v ∗ emp (by insert) ≡ Φ k v (by op_right_id)
  -- But BigOpM.singleton gives us: bigOpM Φ (insert ∅ k v) ≡ Φ k v directly
  have heq : BigOpM.bigOpM (op := sep) (unit := emp) Φ (FiniteMap.insert (∅ : M V) k v) ≡ Φ k v :=
    BigOpM.singleton (op := sep) (unit := emp) Φ k v
  exact equiv_iff.mp heq

/-- Corresponds to `big_sepM_insert` in Rocq Iris. -/
theorem insert {Φ : K → V → PROP} {m : M V} {k : K} {v : V}
    (h : get? m k = none) :
    ([∗map] k' ↦ x ∈ FiniteMap.insert m k v, Φ k' x) ⊣⊢
      Φ k v ∗ [∗map] k' ↦ x ∈ m, Φ k' x := by
  simp only [bigSepM]
  exact equiv_iff.mp (BigOpM.insert (op := sep) (unit := emp) Φ m k v h)

/-- Corresponds to `big_sepM_insert_delete` in Rocq Iris. -/
theorem insert_delete {Φ : K → V → PROP} {m : M V} {k : K} {v : V} :
    ([∗map] k' ↦ x ∈ FiniteMap.insert m k v, Φ k' x) ⊣⊢
      Φ k v ∗ [∗map] k' ↦ x ∈ Std.delete m k, Φ k' x := by
  have heq := FiniteMapLaws.insert_delete_eq m k v
  simp only [bigSepM, ← heq]
  have herase : get? (Std.delete m k) k = none := lookup_delete_eq m k
  have hins := insert (Φ := Φ) (m := Std.delete m k) (k := k) (v := v) herase
  exact hins

/-- Corresponds to `big_sepM_delete` in Rocq Iris. -/
theorem delete {Φ : K → V → PROP} {m : M V} {k : K} {v : V}
    (h : get? m k = some v) :
    ([∗map] k' ↦ x ∈ m, Φ k' x) ⊣⊢ Φ k v ∗ [∗map] k' ↦ x ∈ Std.delete m k, Φ k' x := by
  simp only [bigSepM]
  exact equiv_iff.mp (BigOpM.delete (op := sep) (unit := emp) Φ m k v h)

/-! ## Monotonicity and Congruence -/

omit [DecidableEq K] in
/-- Helper: mono on lists directly. -/
private theorem mono_list {Φ Ψ : K × V → PROP} {l : List (K × V)}
    (h : ∀ kv, kv ∈ l → Φ kv ⊢ Ψ kv) :
    bigOpL sep emp (fun _ kv => Φ kv) l ⊢ bigOpL sep emp (fun _ kv => Ψ kv) l := by
  induction l with
  | nil => exact Entails.rfl
  | cons kv kvs ih =>
    simp only [bigOpL]
    apply sep_mono
    · exact h kv List.mem_cons_self
    · exact ih (fun kv' hmem => h kv' (List.mem_cons_of_mem _ hmem))

/-- Corresponds to `big_sepM_mono` in Rocq Iris. -/
theorem mono {Φ Ψ : K → V → PROP} {m : M V}
    (h : ∀ k v, get? m k = some v → Φ k v ⊢ Ψ k v) :
    ([∗map] k ↦ x ∈ m, Φ k x) ⊢ [∗map] k ↦ x ∈ m, Ψ k x := by
  simp only [bigSepM]
  apply mono_list
  intro kv hmem
  have hkv : get? m kv.1 = some kv.2 := (FiniteMapLaws.elem_of_map_to_list m kv.1 kv.2).mp hmem
  exact h kv.1 kv.2 hkv

/-- Corresponds to `big_sepM_proper` in Rocq Iris. -/
theorem proper {Φ Ψ : K → V → PROP} {m : M V}
    (h : ∀ k v, get? m k = some v → Φ k v ≡ Ψ k v) :
    ([∗map] k ↦ x ∈ m, Φ k x) ≡ [∗map] k ↦ x ∈ m, Ψ k x := by
  simp only [bigSepM]
  exact BigOpM.proper (op := sep) (unit := emp) Φ Ψ m h

/-- Unconditional version of `proper`. No direct Rocq equivalent. -/
theorem congr {Φ Ψ : K → V → PROP} {m : M V}
    (h : ∀ k v, Φ k v ≡ Ψ k v) :
    ([∗map] k ↦ x ∈ m, Φ k x) ≡ [∗map] k ↦ x ∈ m, Ψ k x :=
  proper (fun k v _ => h k v)

/-- Corresponds to `big_sepM_ne` in Rocq Iris. -/
theorem ne {Φ Ψ : K → V → PROP} {m : M V} {n : Nat}
    (h : ∀ k v, get? m k = some v → Φ k v ≡{n}≡ Ψ k v) :
    ([∗map] k ↦ x ∈ m, Φ k x) ≡{n}≡ [∗map] k ↦ x ∈ m, Ψ k x := by
  simp only [bigSepM]
  exact BigOpM.ne (op := sep) (unit := emp) Φ Ψ m n h

/-- Corresponds to `big_sepM_mono'` in Rocq Iris. -/
theorem mono' {Φ Ψ : K → V → PROP} {m : M V}
    (h : ∀ k v, Φ k v ⊢ Ψ k v) :
    ([∗map] k ↦ x ∈ m, Φ k x) ⊢ [∗map] k ↦ x ∈ m, Ψ k x :=
  mono (fun k v _ => h k v)

/-- Corresponds to `big_sepM_flip_mono'` in Rocq Iris. -/
theorem flip_mono' {Φ Ψ : K → V → PROP} {m : M V}
    (h : ∀ k v, Ψ k v ⊢ Φ k v) :
    ([∗map] k ↦ x ∈ m, Ψ k x) ⊢ [∗map] k ↦ x ∈ m, Φ k x :=
  mono' h

/-! ## Typeclass Instances -/

/-- Corresponds to `big_sepM_empty_persistent` in Rocq Iris. -/
instance empty_persistent {Φ : K → V → PROP} :
    Persistent ([∗map] k ↦ x ∈ (∅ : M V), Φ k x) where
  persistent := by
    simp only [bigSepM, FiniteMapLaws.map_to_list_empty, bigOpL]
    exact persistently_emp_2

/-- Corresponds to `big_sepM_persistent` in Rocq Iris (conditional version). -/
theorem persistent_cond {Φ : K → V → PROP} {m : M V}
    (h : ∀ k v, get? m k = some v → Persistent (Φ k v)) :
    Persistent ([∗map] k ↦ x ∈ m, Φ k x) where
  persistent := by
    simp only [bigSepM]
    apply BigOpL.closed (fun P => P ⊢ <pers> P) (fun _ kv => Φ kv.1 kv.2) (toList m)
      persistently_emp_2
      (fun _ _ h1 h2 => (sep_mono h1 h2).trans persistently_sep_2)
    intro i kv hget
    have hi : i < (toList m).length := List.getElem?_eq_some_iff.mp hget |>.1
    have heq : (toList m)[i] = kv := List.getElem?_eq_some_iff.mp hget |>.2
    have hmem : kv ∈ toList m := heq ▸ List.getElem_mem hi
    have hkv : get? m kv.1 = some kv.2 := (FiniteMapLaws.elem_of_map_to_list m kv.1 kv.2).mp hmem
    exact (h kv.1 kv.2 hkv).persistent

/-- Corresponds to `big_sepM_persistent'` in Rocq Iris. -/
instance persistent {Φ : K → V → PROP} {m : M V} [∀ k v, Persistent (Φ k v)] :
    Persistent ([∗map] k ↦ x ∈ m, Φ k x) :=
  persistent_cond fun _ _ _ => inferInstance

/-- Corresponds to `big_sepM_empty_affine` in Rocq Iris. -/
instance empty_affine {Φ : K → V → PROP} :
    Affine ([∗map] k ↦ x ∈ (∅ : M V), Φ k x) where
  affine := by
    simp only [bigSepM, FiniteMapLaws.map_to_list_empty, bigOpL]
    exact Entails.rfl

/-- Corresponds to `big_sepM_affine` in Rocq Iris (conditional version). -/
theorem affine_cond {Φ : K → V → PROP} {m : M V}
    (h : ∀ k v, get? m k = some v → Affine (Φ k v)) :
    Affine ([∗map] k ↦ x ∈ m, Φ k x) where
  affine := by
    simp only [bigSepM]
    apply BigOpL.closed (fun P => P ⊢ emp) (fun _ kv => Φ kv.1 kv.2) (toList m)
      Entails.rfl
      (fun _ _ h1 h2 => (sep_mono h1 h2).trans sep_emp.1)
    intro i kv hget
    have hi : i < (toList m).length := List.getElem?_eq_some_iff.mp hget |>.1
    have heq : (toList m)[i] = kv := List.getElem?_eq_some_iff.mp hget |>.2
    have hmem : kv ∈ toList m := heq ▸ List.getElem_mem hi
    have hkv : get? m kv.1 = some kv.2 := (FiniteMapLaws.elem_of_map_to_list m kv.1 kv.2).mp hmem
    exact (h kv.1 kv.2 hkv).affine

/-- Corresponds to `big_sepM_affine'` in Rocq Iris. -/
instance affine {Φ : K → V → PROP} {m : M V} [∀ k v, Affine (Φ k v)] :
    Affine ([∗map] k ↦ x ∈ m, Φ k x) :=
  affine_cond fun _ _ _ => inferInstance

/-! ## Logical Operations -/

omit [DecidableEq K] [FiniteMapLaws K M] in
/-- Corresponds to `big_sepM_sep` in Rocq Iris. -/
theorem sep' {Φ Ψ : K → V → PROP} {m : M V} :
    ([∗map] k ↦ x ∈ m, Φ k x ∗ Ψ k x) ⊣⊢
      ([∗map] k ↦ x ∈ m, Φ k x) ∗ [∗map] k ↦ x ∈ m, Ψ k x := by
  simp only [bigSepM]
  exact equiv_iff.mp (BigOpM.op_distr (op := sep) (unit := emp) Φ Ψ m)

omit [DecidableEq K] [FiniteMapLaws K M] in
/-- Corresponds to `big_sepM_sep_2` in Rocq Iris. -/
theorem sep_2 {Φ Ψ : K → V → PROP} {m : M V} :
    ([∗map] k ↦ x ∈ m, Φ k x) ∗ ([∗map] k ↦ x ∈ m, Ψ k x) ⊣⊢
      [∗map] k ↦ x ∈ m, Φ k x ∗ Ψ k x :=
  sep'.symm

/-- Corresponds to `big_sepM_and` in Rocq Iris (one direction only). -/
theorem and' {Φ Ψ : K → V → PROP} {m : M V} :
    ([∗map] k ↦ x ∈ m, Φ k x ∧ Ψ k x) ⊢
      ([∗map] k ↦ x ∈ m, Φ k x) ∧ [∗map] k ↦ x ∈ m, Ψ k x :=
  and_intro (mono' fun _ _ => and_elim_l) (mono' fun _ _ => and_elim_r)

/-- Corresponds to `big_sepM_wand` in Rocq Iris. -/
theorem wand {Φ Ψ : K → V → PROP} {m : M V} :
    ([∗map] k ↦ x ∈ m, Φ k x) ⊢
      ([∗map] k ↦ x ∈ m, Φ k x -∗ Ψ k x) -∗ [∗map] k ↦ x ∈ m, Ψ k x :=
  wand_intro <| sep_2.1.trans (mono' fun _ _ => wand_elim_r)

/-! ## Lookup Lemmas -/

/-- Corresponds to `big_sepM_lookup_acc` in Rocq Iris. -/
theorem lookup_acc {Φ : K → V → PROP} {m : M V} {k : K} {v : V}
    (h : get? m k = some v) :
    ([∗map] k' ↦ x ∈ m, Φ k' x) ⊢
      Φ k v ∗ (Φ k v -∗ [∗map] k' ↦ x ∈ m, Φ k' x) :=
  (delete h).1.trans (sep_mono_r (wand_intro' (delete h).2))

/-- Corresponds to `big_sepM_lookup` in Rocq Iris. -/
theorem lookup {Φ : K → V → PROP} {m : M V} {k : K} {v : V}
    (h : get? m k = some v) :
    [TCOr (∀ j w, Affine (Φ j w)) (Absorbing (Φ k v))] →
    ([∗map] k' ↦ x ∈ m, Φ k' x) ⊢ Φ k v
  | TCOr.l => (delete h).1.trans sep_elim_l
  | TCOr.r => (lookup_acc h).trans (sep_elim_l (P := Φ k v) (Q := iprop(Φ k v -∗ bigSepM Φ m)))

/-- Corresponds to `big_sepM_lookup_dom` in Rocq Iris. -/
theorem lookup_dom {Φ : K → PROP} {m : M V} {k : K}
    (h : (get? m k).isSome) :
    [TCOr (∀ j, Affine (Φ j)) (Absorbing (Φ k))] →
    bigSepM (fun k' _ => Φ k') m ⊢ Φ k := by
  have ⟨v, hv⟩ : ∃ v, get? m k = some v := Option.isSome_iff_exists.mp h
  intro htc
  exact match htc with
  | TCOr.l => lookup (Φ := fun k' _ => Φ k') hv
  | TCOr.r => lookup (Φ := fun k' _ => Φ k') hv

/-- Corresponds to `big_sepM_insert_acc` in Rocq Iris. -/
theorem insert_acc {Φ : K → V → PROP} {m : M V} {k : K} {v : V}
    (h : get? m k = some v) :
    ([∗map] k' ↦ x ∈ m, Φ k' x) ⊢
      Φ k v ∗ (∀ v', Φ k v' -∗ [∗map] k' ↦ x ∈ FiniteMap.insert m k v', Φ k' x) := by
  have hdel := delete (Φ := Φ) (m := m) h
  refine hdel.1.trans (sep_mono_r ?_)
  apply forall_intro
  intro v'
  have hmap_eq := FiniteMapLaws.insert_delete_eq m k v'
  have hprop_eq : bigSepM Φ (FiniteMap.insert m k v') ⊣⊢ bigSepM Φ (FiniteMap.insert (Std.delete m k) k v') := by
    unfold bigSepM; rw [hmap_eq]; exact .rfl
  have hins := insert (Φ := Φ) (m := Std.delete m k) (k := k) (v := v') (lookup_delete_eq m k)
  exact wand_intro' (hins.2.trans hprop_eq.2)

/-- Corresponds to `big_sepM_insert_2` in Rocq Iris. -/
theorem insert_2 {Φ : K → V → PROP} {m : M V} {k : K} {v : V} :
    [TCOr (∀ w, Affine (Φ k w)) (Absorbing (Φ k v))] →
    Φ k v ⊢ ([∗map] k' ↦ x ∈ m, Φ k' x) -∗ [∗map] k' ↦ x ∈ FiniteMap.insert m k v, Φ k' x
  | TCOr.l => by
    apply wand_intro
    cases hm : get? m k with
    | none =>
      exact (insert hm).2
    | some y =>
      have hdel := delete (Φ := Φ) (m := m) hm
      refine (sep_mono_r hdel.1).trans ?_
      refine (sep_assoc (P := Φ k v) (Q := Φ k y) (R := bigSepM (fun k' x => Φ k' x) (Std.delete m k))).2.trans ?_
      refine (sep_mono_l sep_elim_l).trans ?_
      have hins := insert (Φ := Φ) (m := Std.delete m k) (k := k) (v := v) (lookup_delete_eq m k)
      have hmap_eq := FiniteMapLaws.insert_delete_eq m k v
      have hprop_eq : bigSepM Φ (FiniteMap.insert m k v) ⊣⊢ bigSepM Φ (FiniteMap.insert (Std.delete m k) k v) := by
        unfold bigSepM; rw [hmap_eq]; exact .rfl
      exact hins.2.trans hprop_eq.2
  | TCOr.r => by
    apply wand_intro
    cases hm : get? m k with
    | none => exact (insert hm).2
    | some y =>
      have hdel := delete (Φ := Φ) (m := m) hm
      refine (sep_mono_r hdel.1).trans ?_
      refine (sep_assoc (P := Φ k v) (Q := Φ k y) (R := bigSepM (fun k' x => Φ k' x) (Std.delete m k))).2.trans ?_
      refine (sep_mono_l (sep_elim_l (P := Φ k v) (Q := Φ k y))).trans ?_
      have hins := insert (Φ := Φ) (m := Std.delete m k) (k := k) (v := v) (lookup_delete_eq m k)
      have hmap_eq := FiniteMapLaws.insert_delete_eq m k v
      have hprop_eq : bigSepM Φ (FiniteMap.insert m k v) ⊣⊢ bigSepM Φ (FiniteMap.insert (Std.delete m k) k v) := by
        unfold bigSepM; rw [hmap_eq]; exact .rfl
      exact hins.2.trans hprop_eq.2

/-- Corresponds to `big_sepM_insert_override` in Rocq Iris. -/
theorem insert_override {Φ : K → V → PROP} {m : M V} {k : K} {v v' : V}
    (hm : get? m k = some v)
    (heqv : Φ k v ⊣⊢ Φ k v') :
    ([∗map] k' ↦ x ∈ FiniteMap.insert m k v', Φ k' x) ⊣⊢ [∗map] k' ↦ x ∈ m, Φ k' x := by
  constructor
  · have hins := insert_delete (Φ := Φ) (m := m) (k := k) (v := v')
    refine hins.1.trans ?_
    refine (sep_mono_l heqv.2).trans ?_
    exact (delete hm).2
  · have hdel := delete (Φ := Φ) (m := m) hm
    refine hdel.1.trans ?_
    refine (sep_mono_l heqv.1).trans ?_
    exact insert_delete.2

/-- Corresponds to `big_sepM_insert_override_1` in Rocq Iris. -/
theorem insert_override_1 {Φ : K → V → PROP} {m : M V} {k : K} {v v' : V}
    (hm : get? m k = some v) :
    ([∗map] k' ↦ x ∈ FiniteMap.insert m k v', Φ k' x) ⊢
      (Φ k v' -∗ Φ k v) -∗ [∗map] k' ↦ x ∈ m, Φ k' x := by
  apply wand_intro'
  refine sep_comm.1.trans ?_
  have hins := insert_delete (Φ := Φ) (m := m) (k := k) (v := v')
  refine (sep_mono_l hins.1).trans ?_
  refine (sep_assoc (P := Φ k v') (Q := bigSepM (fun k' x => Φ k' x) (Std.delete m k)) (R := iprop(Φ k v' -∗ Φ k v))).1.trans ?_
  refine (sep_mono_r sep_comm.1).trans ?_
  refine (sep_assoc (P := Φ k v') (Q := iprop(Φ k v' -∗ Φ k v)) (R := bigSepM (fun k' x => Φ k' x) (Std.delete m k))).2.trans ?_
  refine (sep_mono_l (sep_comm.1.trans (wand_elim_l (P := Φ k v') (Q := Φ k v)))).trans ?_
  exact (delete hm).2

/-- Corresponds to `big_sepM_insert_override_2` in Rocq Iris. -/
theorem insert_override_2 {Φ : K → V → PROP} {m : M V} {k : K} {v v' : V}
    (hm : get? m k = some v) :
    ([∗map] k' ↦ x ∈ m, Φ k' x) ⊢
      (Φ k v -∗ Φ k v') -∗ [∗map] k' ↦ x ∈ FiniteMap.insert m k v', Φ k' x := by
  apply wand_intro'
  refine sep_comm.1.trans ?_
  have hdel := delete (Φ := Φ) (m := m) hm
  refine (sep_mono_l hdel.1).trans ?_
  refine (sep_assoc (P := Φ k v) (Q := bigSepM (fun k' x => Φ k' x) (Std.delete m k)) (R := iprop(Φ k v -∗ Φ k v'))).1.trans ?_
  refine (sep_mono_r sep_comm.1).trans ?_
  refine (sep_assoc (P := Φ k v) (Q := iprop(Φ k v -∗ Φ k v')) (R := bigSepM (fun k' x => Φ k' x) (Std.delete m k))).2.trans ?_
  refine (sep_mono_l (sep_comm.1.trans (wand_elim_l (P := Φ k v) (Q := Φ k v')))).trans ?_
  exact insert_delete.2

/-! ## Map Conversion -/

omit [DecidableEq K] [FiniteMapLaws K M] in
/-- Corresponds to `big_sepM_map_to_list` in Rocq Iris. -/
theorem map_to_list {Φ : K → V → PROP} {m : M V} :
    ([∗map] k ↦ x ∈ m, Φ k x) ⊣⊢ ([∗list] kv ∈ toList m, Φ kv.1 kv.2) := by
  simp only [bigSepM]
  exact .rfl

/-! ## Persistently and Later -/

omit [DecidableEq K] [FiniteMapLaws K M] in
/-- Helper for persistently: induction on list. -/
private theorem persistently_list {Φ : K × V → PROP} {l : List (K × V)} [BIAffine PROP] :
    iprop(<pers> bigOpL sep emp (fun _ kv => Φ kv) l) ⊣⊢
      bigOpL sep emp (fun _ kv => iprop(<pers> Φ kv)) l := by
  induction l with
  | nil => simp only [bigOpL]; exact persistently_emp' (PROP := PROP)
  | cons kv kvs ih =>
    simp only [bigOpL]
    exact persistently_sep.trans ⟨sep_mono_r ih.1, sep_mono_r ih.2⟩

omit [DecidableEq K] [FiniteMapLaws K M] in
/-- Corresponds to `big_sepM_persistently` in Rocq Iris. -/
theorem persistently {Φ : K → V → PROP} {m : M V} [BIAffine PROP] :
    iprop(<pers> [∗map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∗map] k ↦ x ∈ m, <pers> Φ k x := by
  simp only [bigSepM]
  exact persistently_list

omit [DecidableEq K] [FiniteMapLaws K M] in
/-- Helper for later: induction on list. -/
private theorem later_list {Φ : K × V → PROP} {l : List (K × V)} [BIAffine PROP] :
    iprop(▷ bigOpL sep emp (fun _ kv => Φ kv) l) ⊣⊢
      bigOpL sep emp (fun _ kv => iprop(▷ Φ kv)) l := by
  induction l with
  | nil => simp only [bigOpL]; exact later_emp
  | cons kv kvs ih =>
    simp only [bigOpL]
    exact later_sep.trans ⟨sep_mono_r ih.1, sep_mono_r ih.2⟩

omit [DecidableEq K] [FiniteMapLaws K M] in
/-- Corresponds to `big_sepM_later` in Rocq Iris. -/
theorem later [BIAffine PROP] {Φ : K → V → PROP} {m : M V} :
    iprop(▷ [∗map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∗map] k ↦ x ∈ m, ▷ Φ k x := by
  simp only [bigSepM]
  exact later_list

omit [DecidableEq K] [FiniteMapLaws K M] in
/-- Helper for later_2: induction on list. -/
private theorem later_2_list {Φ : K × V → PROP} {l : List (K × V)} :
    bigOpL sep emp (fun _ kv => iprop(▷ Φ kv)) l ⊢
      iprop(▷ bigOpL sep emp (fun _ kv => Φ kv) l) := by
  induction l with
  | nil => simp only [bigOpL]; exact later_intro
  | cons kv kvs ih =>
    simp only [bigOpL]
    exact (sep_mono_r ih).trans later_sep.2

omit [DecidableEq K] [FiniteMapLaws K M] in
/-- Corresponds to `big_sepM_later_2` in Rocq Iris. -/
theorem later_2 {Φ : K → V → PROP} {m : M V} :
    ([∗map] k ↦ x ∈ m, ▷ Φ k x) ⊢ iprop(▷ [∗map] k ↦ x ∈ m, Φ k x) := by
  simp only [bigSepM]
  exact later_2_list

omit [DecidableEq K] [FiniteMapLaws K M] in
/-- Corresponds to `big_sepM_laterN` in Rocq Iris. -/
theorem laterN [BIAffine PROP] {Φ : K → V → PROP} {m : M V} {n : Nat} :
    iprop(▷^[n] [∗map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∗map] k ↦ x ∈ m, ▷^[n] Φ k x := by
  induction n with
  | zero => exact .rfl
  | succ k ih => exact (later_congr ih).trans later

omit [DecidableEq K] [FiniteMapLaws K M] in
/-- Corresponds to `big_sepM_laterN_2` in Rocq Iris. -/
theorem laterN_2 {Φ : K → V → PROP} {m : M V} {n : Nat} :
    ([∗map] k ↦ x ∈ m, ▷^[n] Φ k x) ⊢ iprop(▷^[n] [∗map] k ↦ x ∈ m, Φ k x) := by
  induction n with
  | zero => exact .rfl
  | succ k ih => exact later_2.trans (later_mono ih)

/-! ## Map Transformations -/

section MapTransformations

variable {V' : Type _}
variable [DecidableEq V']

/-- Corresponds to `big_sepM_fmap` in Rocq Iris. -/
theorem fmap {Φ : K → V' → PROP} {m : M V} (f : V → V') :
    ([∗map] k ↦ y ∈ FiniteMap.map f m, Φ k y) ⊣⊢
      [∗map] k ↦ y ∈ m, Φ k (f y) := by
  simp only [bigSepM]
  exact equiv_iff.mp (BigOpM.fmap (op := sep) (unit := emp) f Φ m)

end MapTransformations

section FilterMapTransformations

omit [DecidableEq K] [FiniteMapLaws K M] in
/-- Helper lemma for omap: bigOpL over filterMapped list. -/
private theorem omap_list_aux {Φ : K → V → PROP} (f : V → Option V) (l : List (K × V)) :
    bigOpL sep emp (fun _ kv => Φ kv.1 kv.2)
      (l.filterMap (fun kv => (f kv.2).map (kv.1, ·))) ⊣⊢
    bigOpL sep emp (fun _ kv => match f kv.2 with | some y' => Φ kv.1 y' | none => emp) l := by
  induction l with
  | nil => simp only [List.filterMap, bigOpL]; exact .rfl
  | cons kv kvs ih =>
    simp only [List.filterMap, Option.map]
    cases hf : f kv.2 with
    | none =>
      simp only [bigOpL, hf]
      exact ih.trans emp_sep.symm
    | some y' =>
      simp only [bigOpL, hf]
      exact ⟨sep_mono_r ih.1, sep_mono_r ih.2⟩

/-- Corresponds to `big_sepM_omap` in Rocq Iris. -/
theorem omap [FiniteMapLawsSelf K M] {Φ : K → V → PROP} {m : M V} (f : V → Option V) :
    ([∗map] k ↦ y ∈ FiniteMap.filterMap (M := M) f m, Φ k y) ⊣⊢
      [∗map] k ↦ y ∈ m, match f y with | some y' => Φ k y' | none => emp := by
  simp only [bigSepM]
  have hperm := toList_filterMap (K := K) m f
  have heq : bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) (toList (FiniteMap.filterMap (M := M) f m)) ≡
             bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) ((toList m).filterMap (fun kv => (f kv.2).map (kv.1, ·))) :=
    BigOpL.perm _ hperm
  exact equiv_iff.mp heq |>.trans (omap_list_aux f (toList m))

/-- Corresponds to `big_sepM_union` in Rocq Iris. -/
theorem union [FiniteMapLawsSelf K M] {Φ : K → V → PROP} {m₁ m₂ : M V}
    (hdisj : m₁ ##ₘ m₂) :
    ([∗map] k ↦ y ∈ m₁ ∪ m₂, Φ k y) ⊣⊢
      ([∗map] k ↦ y ∈ m₁, Φ k y) ∗ [∗map] k ↦ y ∈ m₂, Φ k y := by
  simp only [bigSepM]
  exact equiv_iff.mp (BigOpM.union (op := sep) (unit := emp) Φ m₁ m₂ hdisj)

/-- Corresponds to `big_sepM_subseteq` in Rocq Iris. -/
theorem subseteq {Φ : K → V → PROP} {m₁ m₂ : M V} [FiniteMapLawsSelf K M] [∀ k v, Affine (Φ k v)]
    (h : m₂ ⊆ m₁) :
    ([∗map] k ↦ x ∈ m₁, Φ k x) ⊢ [∗map] k ↦ x ∈ m₂, Φ k x := by
  have heq : m₂ ∪ (m₁ \ m₂) = m₁ := FiniteMap.map_difference_union m₁ m₂ h
  have hdisj : FiniteMap.Disjoint m₂ (m₁ \ m₂) := FiniteMap.disjoint_difference_r m₁ m₂
  suffices hsuff : ([∗map] k ↦ x ∈ m₂ ∪ (m₁ \ m₂), Φ k x) ⊢ [∗map] k ↦ x ∈ m₂, Φ k x by
    have : ([∗map] k ↦ x ∈ m₁, Φ k x) ≡ ([∗map] k ↦ x ∈ m₂ ∪ (m₁ \ m₂), Φ k x) := by rw [heq]
    exact (equiv_iff.mp this).1.trans hsuff
  refine (union hdisj).1.trans ?_
  have : Affine ([∗map] k ↦ x ∈ m₁ \ m₂, Φ k x) := inferInstance
  exact sep_elim_l

end FilterMapTransformations

/-! ## List-Map Conversions -/

/-- Corresponds to `big_sepM_list_to_map` in Rocq Iris. -/
theorem list_to_map {Φ : K → V → PROP} {l : List (K × V)}
    (hnodup : (l.map Prod.fst).Nodup) :
    ([∗map] k ↦ x ∈ (ofList l : M V), Φ k x) ⊣⊢ [∗list] kv ∈ l, Φ kv.1 kv.2 := by
  simp only [bigSepM, bigSepL]
  exact equiv_iff.mp (BigOpM.list_to_map (op := sep) (unit := emp) Φ l hnodup)

/-! ## Intro and Forall Lemmas -/

/-- Corresponds to `big_sepM_intro` in Rocq Iris.
    -/
theorem intro {Φ : K → V → PROP} {m : M V} :
    iprop(□ (∀ k v, ⌜get? m k = some v⌝ → Φ k v)) ⊢ [∗map] k ↦ x ∈ m, Φ k x := by
  simp only [bigSepM]
  generalize hl : toList m = l
  induction l generalizing m with
  | nil =>
    exact affinely_elim_emp
  | cons kv kvs ih =>
    simp only [bigOpL]
    have hmem_kv : kv ∈ toList m := hl ▸ List.mem_cons_self
    have hget_kv := (FiniteMapLaws.elem_of_map_to_list m kv.1 kv.2).mp hmem_kv
    refine intuitionistically_sep_idem.2.trans <| sep_mono ?_ ?_
    · refine intuitionistically_elim.trans ?_
      exact (forall_elim kv.1).trans ((forall_elim kv.2).trans
        ((imp_mono_l (pure_mono fun _ => hget_kv)).trans true_imp.1))
    · have htail : ∀ kv', kv' ∈ kvs → get? m kv'.1 = some kv'.2 := fun kv' hmem =>
        (FiniteMapLaws.elem_of_map_to_list m kv'.1 kv'.2).mp (hl.symm ▸ List.mem_cons_of_mem _ hmem)
      clear ih hmem_kv hget_kv hl
      induction kvs with
      | nil => exact affinely_elim_emp
      | cons kv' kvs' ih' =>
        simp only [bigOpL]
        refine intuitionistically_sep_idem.2.trans <| sep_mono ?_ ?_
        · refine intuitionistically_elim.trans ?_
          exact (forall_elim kv'.1).trans ((forall_elim kv'.2).trans
            ((imp_mono_l (pure_mono fun _ => htail kv' List.mem_cons_self)).trans true_imp.1))
        · exact ih' fun kv'' hmem => htail kv'' (List.mem_cons_of_mem _ hmem)

/-- Forward direction of `big_sepM_forall` in Rocq Iris. -/
theorem forall_1' {Φ : K → V → PROP} {m : M V} [BIAffine PROP]
    [∀ k v, Persistent (Φ k v)] :
    ([∗map] k ↦ x ∈ m, Φ k x) ⊢ ∀ k, ∀ v, iprop(⌜get? m k = some v⌝ → Φ k v) := by
  refine forall_intro fun k => forall_intro fun v => imp_intro' <| pure_elim_l fun hget => ?_
  have hdel := delete (Φ := Φ) hget
  exact hdel.1.trans <| (sep_mono_l Persistent.persistent).trans <|
    sep_comm.1.trans <| persistently_absorb_r.trans persistently_elim

/-- Backward direction of `big_sepM_forall` in Rocq Iris. -/
theorem forall_2' {Φ : K → V → PROP} {m : M V} [BIAffine PROP]
    [∀ k v, Persistent (Φ k v)] :
    (∀ k v, iprop(⌜get? m k = some v⌝ → Φ k v)) ⊢ [∗map] k ↦ x ∈ m, Φ k x := by
  simp only [bigSepM]
  generalize hl : toList m = l
  induction l generalizing m with
  | nil => exact Affine.affine
  | cons kv kvs ih =>
    simp only [bigOpL]
    have hmem_kv : kv ∈ toList m := hl ▸ List.mem_cons_self
    have hget_kv := (FiniteMapLaws.elem_of_map_to_list m kv.1 kv.2).mp hmem_kv
    have head_step : iprop(∀ k v, ⌜get? m k = some v⌝ → Φ k v) ⊢ Φ kv.1 kv.2 :=
      (forall_elim kv.1).trans (forall_elim kv.2) |>.trans <|
        (and_intro (pure_intro hget_kv) .rfl).trans imp_elim_r
    have htail : ∀ kv', kv' ∈ kvs → get? m kv'.1 = some kv'.2 := fun kv' hmem =>
      (FiniteMapLaws.elem_of_map_to_list m kv'.1 kv'.2).mp (hl.symm ▸ List.mem_cons_of_mem _ hmem)
    refine and_self.2.trans (and_mono_l head_step) |>.trans persistent_and_sep_1 |>.trans <|
      sep_mono_r ?_
    clear ih head_step hmem_kv hget_kv hl
    induction kvs with
    | nil => exact Affine.affine
    | cons kv' kvs' ih' =>
      simp only [bigOpL]
      have hget_kv' := htail kv' List.mem_cons_self
      have head_step' : iprop(∀ k v, ⌜get? m k = some v⌝ → Φ k v) ⊢ Φ kv'.1 kv'.2 :=
        (forall_elim kv'.1).trans (forall_elim kv'.2) |>.trans <|
          (and_intro (pure_intro hget_kv') .rfl).trans imp_elim_r
      refine and_self.2.trans (and_mono_l head_step') |>.trans persistent_and_sep_1 |>.trans <|
        sep_mono_r (ih' fun kv'' hmem => htail kv'' (List.mem_cons_of_mem _ hmem))

/-- Corresponds to `big_sepM_forall` in Rocq Iris. -/
theorem forall' {Φ : K → V → PROP} {m : M V} [BIAffine PROP]
    [∀ k v, Persistent (Φ k v)] :
    ([∗map] k ↦ x ∈ m, Φ k x) ⊣⊢ ∀ k, ∀ v, iprop(⌜get? m k = some v⌝ → Φ k v) :=
  ⟨forall_1', forall_2'⟩

/-- Corresponds to `big_sepM_impl` in Rocq Iris. -/
theorem impl {Φ Ψ : K → V → PROP} {m : M V} :
    ([∗map] k ↦ x ∈ m, Φ k x) ⊢
      □ (∀ k v, iprop(⌜get? m k = some v⌝ → Φ k v -∗ Ψ k v)) -∗ [∗map] k ↦ x ∈ m, Ψ k x := by
  apply wand_intro
  have h1 : iprop(□ (∀ k v, ⌜get? m k = some v⌝ → Φ k v -∗ Ψ k v)) ⊢ bigSepM (fun k v => iprop(Φ k v -∗ Ψ k v)) m :=
    intro
  refine (sep_mono_r h1).trans ?_
  exact sep_2.1.trans (mono' fun _ _ => wand_elim_r)

omit [DecidableEq K] [FiniteMapLaws K M] in
/-- Corresponds to `big_sepM_dup` in Rocq Iris. -/
theorem dup {P : PROP} [Affine P] {m : M V} :
    □ (P -∗ P ∗ P) ⊢ P -∗ [∗map] _k ↦ _x ∈ m, P := by
  simp only [bigSepM]
  apply wand_intro
  generalize toList m = l
  induction l with
  | nil =>
    simp only [bigOpL]
    exact sep_elim_r.trans Affine.affine
  | cons kv kvs ih =>
    simp only [bigOpL]
    refine (sep_mono_l intuitionistically_sep_idem.2).trans <| sep_assoc.1.trans <|
      (sep_mono_r <| (sep_mono_l intuitionistically_elim).trans wand_elim_l).trans <|
      sep_assoc.2.trans <| (sep_mono_l ih).trans sep_comm.1

/-- Corresponds to `big_sepM_lookup_acc_impl` in Rocq Iris. -/
theorem lookup_acc_impl {Φ : K → V → PROP} {m : M V} {k : K} {v : V}
    (hget : get? m k = some v) :
    ([∗map] k' ↦ x ∈ m, Φ k' x) ⊢
      Φ k v ∗ ∀ (Ψ: K → V → PROP), □ (∀ k' v', iprop(⌜get? m k' = some v'⌝ → ⌜k' ≠ k⌝ → Φ k' v' -∗ Ψ k' v')) -∗
        Ψ k v -∗ [∗map] k' ↦ x ∈ m, Ψ k' x := by
  have hdel := delete (Φ := Φ) (m := m) hget
  refine hdel.1.trans (sep_mono_r ?_)
  apply forall_intro
  intro Ψ
  apply wand_intro
  apply wand_intro
  have hdelΨ := delete (Φ := Ψ) (m := m) hget
  refine sep_comm.1.trans <| (sep_mono_r sep_comm.1).trans ?_
  refine (sep_mono_r sep_comm.1).trans ?_
  refine (sep_mono_r ?_).trans hdelΨ.2
  have himpl : iprop(□ (∀ k' v', ⌜get? m k' = some v'⌝ → ⌜k' ≠ k⌝ → Φ k' v' -∗ Ψ k' v'))
      ⊢ bigSepM (fun k' v' => iprop(Φ k' v' -∗ Ψ k' v')) (Std.delete m k) := by
    have htrans : iprop(□ (∀ k' v', ⌜get? m k' = some v'⌝ → ⌜k' ≠ k⌝ → Φ k' v' -∗ Ψ k' v'))
        ⊢ iprop(□ (∀ k' v', ⌜get? (Std.delete m k) k' = some v'⌝ → Φ k' v' -∗ Ψ k' v')) := by
      apply intuitionistically_mono
      apply forall_mono; intro k'
      apply forall_mono; intro v'
      apply imp_intro'
      apply pure_elim_l; intro hget_erase
      have hne : k' ≠ k := by
        intro heq
        rw [heq, lookup_delete_eq] at hget_erase
        exact Option.noConfusion hget_erase
      have hget_m : get? m k' = some v' := by
        rw [lookup_delete_ne m k k' hne.symm] at hget_erase
        exact hget_erase
      exact (and_intro (pure_intro hget_m) .rfl).trans imp_elim_r |>.trans <|
        (and_intro (pure_intro hne) .rfl).trans imp_elim_r
    exact htrans.trans intro
  refine (sep_mono_r himpl).trans ?_
  exact sep_2.1.trans (mono' fun _ _ => wand_elim_r)

/-! ## Pure Lemmas -/

/-- Corresponds to `big_sepM_pure_1` in Rocq Iris. -/
theorem pure_1 {φ : K → V → Prop} {m : M V} :
    ([∗map] k ↦ x ∈ m, ⌜φ k x⌝) ⊢ (⌜FiniteMap.map_Forall φ m⌝ : PROP) := by
  simp only [bigSepM]
  suffices h : ∀ l : List (K × V),
      bigOpL sep emp (fun _ (kv : K × V) => iprop(⌜φ kv.1 kv.2⌝)) l ⊢
        iprop(⌜∀ kv, kv ∈ l → φ kv.1 kv.2⌝) by
    refine (h (toList m)).trans <| pure_mono fun hlist => ?_
    exact (FiniteMapLaws.map_Forall_to_list φ m).mpr hlist
  intro l
  induction l with
  | nil =>
    simp only [bigOpL]
    exact pure_intro fun _ h => nomatch h
  | cons kv kvs ih =>
    simp only [bigOpL]
    refine (sep_mono_r ih).trans <| sep_and.trans <| pure_and.1.trans <| pure_mono ?_
    intro ⟨hkv, hkvs⟩ kv' hmem
    cases hmem with
    | head => exact hkv
    | tail _ htail => exact hkvs kv' htail

/-- Corresponds to `big_sepM_affinely_pure_2` in Rocq Iris. -/
theorem affinely_pure_2 {φ : K → V → Prop} {m : M V} :
    iprop(<affine> ⌜FiniteMap.map_Forall φ m⌝) ⊢ ([∗map] k ↦ x ∈ m, <affine> ⌜φ k x⌝ : PROP) := by
  simp only [bigSepM]
  suffices h : ∀ l : List (K × V),
      iprop(<affine> ⌜∀ kv, kv ∈ l → φ kv.1 kv.2⌝) ⊢
        bigOpL sep emp (fun _ (kv : K × V) => iprop(<affine> ⌜φ kv.1 kv.2⌝)) l by
    refine (affinely_mono <| pure_mono fun hmap => ?_).trans (h (toList m))
    exact (FiniteMapLaws.map_Forall_to_list φ m).mp hmap
  intro l
  induction l with
  | nil =>
    simp only [bigOpL]
    exact affinely_elim_emp
  | cons kv kvs ih =>
    simp only [bigOpL]
    refine (affinely_mono <| pure_mono fun h =>
      ⟨h kv List.mem_cons_self, fun kv' hmem => h kv' (List.mem_cons_of_mem _ hmem)⟩).trans <|
      (affinely_mono pure_and.2).trans <| affinely_and.1.trans <|
      persistent_and_sep_1.trans (sep_mono_r ih)

/-- Corresponds to `big_sepM_pure` in Rocq Iris. -/
theorem pure' [BIAffine PROP] {φ : K → V → Prop} {m : M V} :
    ([∗map] k ↦ x ∈ m, ⌜φ k x⌝) ⊣⊢ (⌜FiniteMap.map_Forall φ m⌝ : PROP) :=
  ⟨pure_1, (affine_affinely _).2.trans <| affinely_pure_2.trans (mono' fun _ _ => affinely_elim)⟩

/-! ## Filter Lemmas -/

variable [FiniteMapLawsSelf K M]

omit [DecidableEq K] in
/-- Helper: bigOpL over filtered list. -/
private theorem filter_list_aux (Φ : K × V → PROP) (φ : K × V → Prop) [∀ kv, Decidable (φ kv)]
    (l : List (K × V)) :
    bigOpL sep emp (fun _ kv => Φ kv) (l.filter (fun kv => decide (φ kv))) ⊣⊢
    bigOpL sep emp (fun _ kv => if decide (φ kv) then Φ kv else emp) l := by
  induction l with
  | nil => simp only [List.filter, bigOpL]; exact .rfl
  | cons kv kvs ih =>
    simp only [List.filter]
    cases hp : decide (φ kv) with
    | false =>
      simp only [bigOpL, hp]
      exact ih.trans emp_sep.symm
    | true =>
      simp only [bigOpL, hp, ↓reduceIte]
      exact ⟨sep_mono_r ih.1, sep_mono_r ih.2⟩

/-- Corresponds to `big_sepM_filter'` in Rocq Iris. -/
theorem filter' {Φ : K → V → PROP} {m : M V}
    (φ : K × V → Prop) [∀ kv, Decidable (φ kv)] :
    ([∗map] k ↦ x ∈ FiniteMap.filter (fun k v => decide (φ (k, v))) m, Φ k x) ⊣⊢
      [∗map] k ↦ x ∈ m, if decide (φ (k, x)) then Φ k x else emp := by
  simp only [bigSepM]
  exact equiv_iff.mp (BigOpM.filter' (op := sep) (unit := emp) (fun k v => decide (φ (k, v))) Φ m)

/-- Corresponds to `big_sepM_filter` in Rocq Iris. -/
theorem filter [BIAffine PROP] {Φ : K → V → PROP} {m : M V}
    (φ : K × V → Prop) [∀ kv, Decidable (φ kv)] :
    ([∗map] k ↦ x ∈ FiniteMap.filter (fun k v => decide (φ (k, v))) m, Φ k x) ⊣⊢
      [∗map] k ↦ x ∈ m, iprop(⌜φ (k, x)⌝ → Φ k x) := by
  have heq : ([∗map] k ↦ x ∈ m, if decide (φ (k, x)) then Φ k x else emp) ⊣⊢
      [∗map] k ↦ x ∈ m, iprop(⌜φ (k, x)⌝ → Φ k x) := by
    apply equiv_iff.mp
    apply proper
    intro k v _
    cases hp : decide (φ (k, v)) with
    | false =>
      have hφ : ¬φ (k, v) := of_decide_eq_false hp
      refine equiv_iff.mpr ⟨?_, Affine.affine⟩
      refine imp_intro' <| pure_elim_l fun h => ?_
      exact absurd h hφ
    | true =>
      have hφ : φ (k, v) := of_decide_eq_true hp
      simp only [↓reduceIte]
      refine equiv_iff.mpr ⟨?_, ?_⟩
      · exact imp_intro' <| pure_elim_l fun _ => Entails.rfl
      · exact (and_intro (pure_intro hφ) .rfl).trans imp_elim_r
  exact (filter' φ).trans heq

/-! ## Function Insertion Lemmas -/

/-- Function update: returns `b` if `k = i`, otherwise `f k`. -/
def fnInsert {K B : Type _} [DecidableEq K] (f : K → B) (i : K) (b : B) (k : K) : B :=
  if k = i then b else f k

theorem fnInsert_same {K B : Type _} [DecidableEq K] (f : K → B) (i : K) (b : B) :
    fnInsert f i b i = b := by simp [fnInsert]

theorem fnInsert_ne {K B : Type _} [DecidableEq K] (f : K → B) (i : K) (b : B) (k : K) (h : k ≠ i) :
    fnInsert f i b k = f k := by simp [fnInsert, h]

omit [FiniteMapLawsSelf K M] in
/-- Corresponds to `big_sepM_fn_insert` in Rocq Iris. -/
theorem fn_insert {B : Type _} {Ψ : K → V → B → PROP} {f : K → B} {m : M V} {i : K} {x : V} {b : B}
    (h : get? m i = none) :
    ([∗map] k ↦ y ∈ FiniteMap.insert m i x, Ψ k y (fnInsert f i b k)) ⊣⊢
      Ψ i x b ∗ [∗map] k ↦ y ∈ m, Ψ k y (f k) := by
  have hins := insert (Φ := fun k y => Ψ k y (fnInsert f i b k)) (v := x) h
  have hhead : Ψ i x (fnInsert f i b i) ⊣⊢ Ψ i x b := by
    simp only [fnInsert_same]
    exact .rfl
  have htail : ([∗map] k ↦ y ∈ m, Ψ k y (fnInsert f i b k)) ⊣⊢
      [∗map] k ↦ y ∈ m, Ψ k y (f k) := by
    apply equiv_iff.mp
    apply proper
    intro k y hget
    have hne : k ≠ i := by
      intro heq
      rw [heq, h] at hget
      exact Option.noConfusion hget
    simp only [fnInsert_ne f i b k hne]
    exact OFE.Equiv.rfl
  exact hins.trans ⟨(sep_mono hhead.1 htail.1), (sep_mono hhead.2 htail.2)⟩

/-- Corresponds to `big_sepM_fn_insert'` in Rocq Iris. -/
theorem fn_insert' {Φ : K → PROP} {m : M V} {i : K} {x : V} {P : PROP}
    (h : get? m i = none) :
    ([∗map] k ↦ _y ∈ FiniteMap.insert m i x, fnInsert Φ i P k) ⊣⊢
      P ∗ [∗map] k ↦ _y ∈ m, Φ k :=
  fn_insert (Ψ := fun _ _ P => P) (f := Φ) (b := P) h

/-! ## Map Zip Lemmas -/

section MapZip

variable {M₁ : Type _ → Type _} {M₂ : Type _ → Type _} {V₁ : Type _} {V₂ : Type _}
variable [FiniteMap K M₁] [FiniteMapLaws K M₁]
variable [FiniteMap K M₂] [FiniteMapLaws K M₂]

omit [FiniteMapLaws K M₁] [FiniteMapLaws K M₂] in
/-- Corresponds to `big_sepM_sep_zip_with` in Rocq Iris. -/
theorem sep_zip_with {C : Type _} {MZ : Type _ → Type _} [FiniteMap K MZ] [FiniteMapLaws K MZ]
    {Φ₁ : K → V₁ → PROP} {Φ₂ : K → V₂ → PROP}
    {f : V₁ → V₂ → C} {g₁ : C → V₁} {g₂ : C → V₂}
    {m₁ : M₁ V₁} {m₂ : M₂ V₂} {mz : MZ C}
    (_hg₁ : ∀ x y, g₁ (f x y) = x)
    (_hg₂ : ∀ x y, g₂ (f x y) = y)
    (_hdom : ∀ k, (get? m₁ k).isSome ↔ (get? m₂ k).isSome)
    (_hperm : (toList mz).Perm
               ((toList m₁).filterMap (fun kv =>
                  match get? m₂ kv.1 with
                  | some v₂ => some (kv.1, f kv.2 v₂)
                  | none => none)))
    (hfmap₁ : (toList m₁).Perm ((toList mz).map (fun kv => (kv.1, g₁ kv.2))))
    (hfmap₂ : (toList m₂).Perm ((toList mz).map (fun kv => (kv.1, g₂ kv.2)))) :
    ([∗map] k ↦ xy ∈ mz, Φ₁ k (g₁ xy) ∗ Φ₂ k (g₂ xy)) ⊣⊢
      ([∗map] k ↦ x ∈ m₁, Φ₁ k x) ∗ [∗map] k ↦ y ∈ m₂, Φ₂ k y := by
  simp only [bigSepM]
  have hsep : bigOpL sep emp (fun _ kv => iprop(Φ₁ kv.1 (g₁ kv.2) ∗ Φ₂ kv.1 (g₂ kv.2))) (toList mz) ≡
              sep (bigOpL sep emp (fun _ kv => Φ₁ kv.1 (g₁ kv.2)) (toList mz))
                  (bigOpL sep emp (fun _ kv => Φ₂ kv.1 (g₂ kv.2)) (toList mz)) :=
    BigOpL.op_distr _ _ _
  refine equiv_iff.mp hsep |>.trans ?_
  have heq₁ : bigOpL sep emp (fun _ kv => Φ₁ kv.1 kv.2) (toList m₁) ≡
              bigOpL sep emp (fun _ kv => Φ₁ kv.1 kv.2) ((toList mz).map (fun kv => (kv.1, g₁ kv.2))) :=
    BigOpL.perm _ hfmap₁
  have heq₂ : bigOpL sep emp (fun _ kv => Φ₂ kv.1 kv.2) (toList m₂) ≡
              bigOpL sep emp (fun _ kv => Φ₂ kv.1 kv.2) ((toList mz).map (fun kv => (kv.1, g₂ kv.2))) :=
    BigOpL.perm _ hfmap₂
  have hmap₁ : bigOpL sep emp (fun _ kv => Φ₁ kv.1 (g₁ kv.2)) (toList mz) ≡
               bigOpL sep emp (fun _ kv => Φ₁ kv.1 kv.2) ((toList mz).map (fun kv => (kv.1, g₁ kv.2))) := by
    induction (toList mz) with
    | nil => exact OFE.Equiv.rfl
    | cons kv kvs ih =>
      simp only [List.map, bigOpL]
      exact Monoid.op_proper OFE.Equiv.rfl ih
  have hmap₂ : bigOpL sep emp (fun _ kv => Φ₂ kv.1 (g₂ kv.2)) (toList mz) ≡
               bigOpL sep emp (fun _ kv => Φ₂ kv.1 kv.2) ((toList mz).map (fun kv => (kv.1, g₂ kv.2))) := by
    induction (toList mz) with
    | nil => exact OFE.Equiv.rfl
    | cons kv kvs ih =>
      simp only [List.map, bigOpL]
      exact Monoid.op_proper OFE.Equiv.rfl ih
  have h₁ : bigOpL sep emp (fun _ kv => Φ₁ kv.1 (g₁ kv.2)) (toList mz) ≡
            bigOpL sep emp (fun _ kv => Φ₁ kv.1 kv.2) (toList m₁) :=
    hmap₁.trans heq₁.symm
  have h₂ : bigOpL sep emp (fun _ kv => Φ₂ kv.1 (g₂ kv.2)) (toList mz) ≡
            bigOpL sep emp (fun _ kv => Φ₂ kv.1 kv.2) (toList m₂) :=
    hmap₂.trans heq₂.symm
  exact equiv_iff.mp (Monoid.op_proper h₁ h₂)

omit [FiniteMapLaws K M₂] in
/-- Corresponds to `big_sepM_sep_zip` in Rocq Iris. -/
theorem sep_zip {Φ₁ : K → V₁ → PROP} {Φ₂ : K → V₂ → PROP}
    {m₁ : M₁ V₁} {m₂ : M₂ V₂} {mz : M₁ (V₁ × V₂)}
    (hdom : ∀ k, (get? m₁ k).isSome ↔ (get? m₂ k).isSome)
    (hperm : (toList mz).Perm
               ((toList m₁).filterMap (fun kv =>
                  match get? m₂ kv.1 with
                  | some v₂ => some (kv.1, (kv.2, v₂))
                  | none => none)))
    (hfmap₁ : (toList m₁).Perm ((toList mz).map
                (fun kv => (kv.1, kv.2.1))))
    (hfmap₂ : (toList m₂).Perm ((toList mz).map
                (fun kv => (kv.1, kv.2.2)))) :
    ([∗map] k ↦ xy ∈ mz, Φ₁ k xy.1 ∗ Φ₂ k xy.2) ⊣⊢
      ([∗map] k ↦ x ∈ m₁, Φ₁ k x) ∗ [∗map] k ↦ y ∈ m₂, Φ₂ k y :=
  sep_zip_with (f := Prod.mk) (g₁ := Prod.fst) (g₂ := Prod.snd)
    (fun _ _ => rfl) (fun _ _ => rfl) hdom hperm hfmap₁ hfmap₂

end MapZip

/-! ## Advanced Impl Lemmas -/

/-- Corresponds to `big_sepM_impl_strong` in Rocq Iris.
    Strong version of impl that tracks which keys are in m₂ vs only in m₁. -/
theorem impl_strong {M₂ : Type _ → Type _} {V₂ : Type _}
    [FiniteMap K M₂] [FiniteMapLaws K M₂] [DecidableEq V₂]
    {Φ : K → V → PROP} {Ψ : K → V₂ → PROP} {m₁ : M V} {m₂ : M₂ V₂} :
    ([∗map] k ↦ x ∈ m₁, Φ k x) ⊢
      □ (∀ k, ∀ y, (match get? m₁ k with | some x => Φ k x | none => emp) -∗
         iprop(⌜get? m₂ k = some y⌝ → Ψ k y)) -∗
      ([∗map] k ↦ y ∈ m₂, Ψ k y) ∗
        [∗map] k ↦ x ∈ FiniteMap.filter (fun k _ => decide ((get? m₂ k).isNone)) m₁, Φ k x := by
  apply wand_intro
  revert m₁
  apply FiniteMapLaws.map_ind (M := M₂) (K := K) (V := V₂) (P := fun m₂ =>
    ∀ (m₁ : M V), ([∗map] k ↦ x ∈ m₁, Φ k x) ∗
      □ (∀ k y, (match get? m₁ k with | some x => Φ k x | none => emp) -∗
         iprop(⌜get? m₂ k = some y⌝ → Ψ k y))
      ⊢ ([∗map] k ↦ y ∈ m₂, Ψ k y) ∗
          [∗map] k ↦ x ∈ FiniteMap.filter (fun k _ => decide ((get? m₂ k).isNone)) m₁, Φ k x)
  · intro m₁
    have hfilter_perm : (toList (FiniteMap.filter (fun k _ => decide ((get? (∅ : M₂ V₂) k).isNone)) m₁)).Perm
        (toList m₁) := by
      have hperm := toList_filter m₁ (fun k _ => decide ((get? (∅ : M₂ V₂) k).isNone))
      rw [List.filter_eq_self.mpr (fun kv _ => by simp [lookup_empty])] at hperm
      exact hperm
    have hfilter_equiv : ([∗map] k ↦ x ∈ FiniteMap.filter (fun k _ => decide ((get? (∅ : M₂ V₂) k).isNone)) m₁, Φ k x) ⊣⊢
        ([∗map] k ↦ x ∈ m₁, Φ k x) := by
      simp only [bigSepM]
      exact equiv_iff.mp (BigOpL.perm (fun kv => Φ kv.1 kv.2) hfilter_perm)
    exact (sep_mono_r (Affine.affine (P := iprop(□ _)))).trans <| sep_emp.1.trans <|
      hfilter_equiv.2.trans <| sep_emp.2.trans <| sep_comm.1.trans (sep_mono_l empty.2)
  · intro i y m hi IH m₁
    have hinsert_goal := insert (Φ := Ψ) (v := y) hi
    refine (sep_mono_r intuitionistically_sep_dup.1).trans <| sep_assoc.2.trans ?_
    cases hm₁i : get? m₁ i with
    | none =>
      have hlookup_insert : get? (Std.insert m i y) i = some y := lookup_insert_eq m i y
      have hΨ_from_hyp : iprop(□ (∀ k y', (match get? m₁ k with | some x => Φ k x | none => emp) -∗
           iprop(⌜get? (Std.insert m i y) k = some y'⌝ → Ψ k y'))) ⊢ Ψ i y := by
        refine intuitionistically_elim.trans <| (forall_elim (a := i)).trans <| (forall_elim (a := y)).trans ?_
        simp only [hm₁i, hlookup_insert]
        exact (wand_mono_r true_imp.1).trans <| emp_sep.2.trans (sep_comm.1.trans wand_elim_l)
      have hweaken : iprop(□ (∀ k y', (match get? m₁ k with | some x => Φ k x | none => emp) -∗
           iprop(⌜get? (Std.insert m i y) k = some y'⌝ → Ψ k y'))) ⊢
          iprop(□ (∀ k y', (match get? m₁ k with | some x => Φ k x | none => emp) -∗
           iprop(⌜get? m k = some y'⌝ → Ψ k y'))) := by
        apply intuitionistically_mono; apply forall_mono; intro k; apply forall_mono; intro y'
        apply wand_mono_r; apply imp_intro'; apply pure_elim_l; intro hget_m
        have hne : k ≠ i := by intro heq; rw [heq] at hget_m; exact Option.noConfusion (hi ▸ hget_m)
        rw [lookup_insert_ne m i k y hne.symm] at *
        exact (and_intro (pure_intro hget_m) .rfl).trans imp_elim_r
      have hfilter_eq : FiniteMap.filter (fun k _ => decide ((get? (Std.insert m i y) k).isNone)) m₁ =
          FiniteMap.filter (fun k _ => decide ((get? m k).isNone)) m₁ := by
        simp only [FiniteMap.filter]; congr 1
        apply List.filter_congr; intro ⟨j, v⟩ hjv
        have hget : get? m₁ j = some v := (FiniteMapLaws.elem_of_map_to_list m₁ j v).mp hjv
        have hne : j ≠ i := by intro heq; rw [heq] at hget; exact Option.noConfusion (hm₁i ▸ hget)
        rw [lookup_insert_ne _ _ _ _ hne.symm]
      rw [hfilter_eq]
      exact (sep_mono_r hΨ_from_hyp).trans <| (sep_mono_l (sep_mono_r hweaken)).trans <|
        (sep_mono_l (IH m₁)).trans <| sep_assoc.1.trans <| (sep_mono_r sep_comm.1).trans <|
        sep_assoc.2.trans (sep_mono_l (sep_comm.1.trans hinsert_goal.2))
    | some x =>
      have hdel := delete (Φ := Φ) (m := m₁) hm₁i
      have hΨ_from_hyp : Φ i x ∗ iprop(□ (∀ k y', (match get? m₁ k with | some x' => Φ k x' | none => emp) -∗
           iprop(⌜get? (Std.insert m i y) k = some y'⌝ → Ψ k y'))) ⊢ Ψ i y := by
        have hlookup_insert : get? (Std.insert m i y) i = some y := lookup_insert_eq m i y
        refine (sep_mono_r intuitionistically_elim).trans <| (sep_mono_r (forall_elim (a := i))).trans <|
          (sep_mono_r (forall_elim (a := y))).trans ?_
        simp only [hm₁i, hlookup_insert]
        exact (sep_mono_r (wand_mono_r true_imp.1)).trans wand_elim_r
      have hweaken : iprop(□ (∀ k y', (match get? m₁ k with | some x' => Φ k x' | none => emp) -∗
           iprop(⌜get? (Std.insert m i y) k = some y'⌝ → Ψ k y'))) ⊢
          iprop(□ (∀ k y', (match get? (Std.delete m₁ i) k with | some x' => Φ k x' | none => emp) -∗
           iprop(⌜get? m k = some y'⌝ → Ψ k y'))) := by
        apply intuitionistically_mono; apply forall_mono; intro k; apply forall_mono; intro y'
        apply wand_intro; apply imp_intro'; apply pure_elim_l; intro hget_m
        have hne : k ≠ i := by intro heq; rw [heq] at hget_m; exact Option.noConfusion (hi ▸ hget_m)
        have hlookup_insert_ne : get? (Std.insert m i y) k = some y' := by
          rw [lookup_insert_ne m i k y hne.symm]; exact hget_m
        rw [lookup_delete_ne m₁ i k hne.symm]
        simp only [hlookup_insert_ne]
        exact (sep_mono_l (wand_mono_r true_imp.1)).trans wand_elim_l
      have hfilter_equiv : bigSepM (fun k x => Φ k x)
          (FiniteMap.filter (fun k _ => decide ((get? (Std.insert m i y) k).isNone)) m₁) ⊣⊢
          bigSepM (fun k x => Φ k x)
          (FiniteMap.filter (fun k _ => decide ((get? m k).isNone)) (Std.delete m₁ i)) := by
        simp only [bigSepM]
        have hperm1 := toList_filter m₁ (fun k _ => decide ((get? (Std.insert m i y) k).isNone))
        have hperm2 := toList_filter (Std.delete m₁ i) (fun k _ => decide ((get? m k).isNone))
        have hdel_perm := FiniteMapLaws.map_to_list_delete m₁ i x hm₁i
        have hpred1_i_false : decide ((get? (Std.insert m i y) i).isNone = true) = false := by
          simp only [lookup_insert_eq, Option.isNone_some, decide_eq_false_iff_not]; exact fun h => nomatch h
        have hpred_eq : ∀ k, k ≠ i →
            decide ((get? (Std.insert m i y) k).isNone = true) = decide ((get? m k).isNone = true) := by
          intro k hne; rw [lookup_insert_ne _ _ _ _ hne.symm]
        have hfilter_perm1 : ((toList m₁).filter (fun kv => decide ((get? (Std.insert m i y) kv.fst).isNone))).Perm
            ((toList (Std.delete m₁ i)).filter (fun kv => decide ((get? (Std.insert m i y) kv.fst).isNone))) := by
          have h1 := hdel_perm.filter (fun kv => decide ((get? (Std.insert m i y) kv.fst).isNone))
          rw [List.filter_cons_of_neg (by simp only [hpred1_i_false]; exact Bool.false_ne_true)] at h1
          exact h1
        have hfilter_eq : ((toList (Std.delete m₁ i)).filter (fun kv => decide ((get? (Std.insert m i y) kv.fst).isNone))) =
            ((toList (Std.delete m₁ i)).filter (fun kv => decide ((get? m kv.fst).isNone))) := by
          apply List.filter_congr; intro ⟨k, v⟩ hkv
          have hne : k ≠ i := by
            intro heq; have hlookup := (FiniteMapLaws.elem_of_map_to_list (Std.delete m₁ i) k v).mp hkv
            rw [heq, lookup_delete_eq] at hlookup; exact Option.noConfusion hlookup
          exact hpred_eq k hne
        exact equiv_iff.mp (BigOpL.perm (Φ := fun (kv : K × V) => Φ kv.1 kv.2)
          (hperm1.trans ((hfilter_eq ▸ hfilter_perm1).trans hperm2.symm)))
      refine (sep_mono_l (sep_mono_l hdel.1)).trans <| (sep_mono_l sep_assoc.1).trans <|
        sep_assoc.1.trans <| (sep_mono_r (sep_mono_l sep_comm.1)).trans <|
        (sep_mono_r sep_assoc.1).trans <| sep_assoc.2.trans <| (sep_mono_l hΨ_from_hyp).trans <|
        (sep_mono_r (sep_mono_r hweaken)).trans <| (sep_mono_r (IH (Std.delete m₁ i))).trans <|
        (sep_mono_r (sep_mono_r hfilter_equiv.2)).trans <| sep_assoc.2.trans (sep_mono_l hinsert_goal.2)

/-- Corresponds to `big_sepM_impl_dom_subseteq` in Rocq Iris.
    Specialized version when the domain of m₂ is a subset of the domain of m₁. -/
theorem impl_dom_subseteq {M₂ : Type _ → Type _} {V₂ : Type _}
    [FiniteMap K M₂] [FiniteMapLaws K M₂] [DecidableEq V₂]
    {Φ : K → V → PROP} {Ψ : K → V₂ → PROP} {m₁ : M V} {m₂ : M₂ V₂}
    (_hdom : ∀ k, (get? m₂ k).isSome → (get? m₁ k).isSome) :
    ([∗map] k ↦ x ∈ m₁, Φ k x) ⊢
      □ (∀ k x y, iprop(⌜get? m₁ k = some x⌝ → ⌜get? m₂ k = some y⌝ → Φ k x -∗ Ψ k y)) -∗
      ([∗map] k ↦ y ∈ m₂, Ψ k y) ∗
        [∗map] k ↦ x ∈ FiniteMap.filter (fun k _ => decide ((get? m₂ k).isNone)) m₁, Φ k x := by
  refine (impl_strong (Φ := Φ) (Ψ := Ψ) (m₁ := m₁) (m₂ := m₂)).trans ?_
  apply wand_mono_l; apply intuitionistically_mono
  apply forall_mono; intro k; apply forall_intro; intro y'
  apply wand_intro; apply imp_intro'; apply pure_elim_l; intro hget_m₂
  cases hget_m₁ : get? m₁ k with
  | none =>
    exfalso
    have hm₁_some := _hdom k (by simp only [hget_m₂, Option.isSome_some])
    rw [hget_m₁] at hm₁_some; exact Bool.false_ne_true hm₁_some
  | some x =>
    simp only
    have h1 : (iprop(⌜some x = some x⌝) → ⌜get? m₂ k = some y'⌝ → Φ k x -∗ Ψ k y') ⊢
              (iprop(⌜get? m₂ k = some y'⌝) → Φ k x -∗ Ψ k y') :=
      (imp_mono_l (pure_true rfl).2).trans true_imp.1
    have h2 : (iprop(⌜get? m₂ k = some y'⌝) → Φ k x -∗ Ψ k y') ⊢ (Φ k x -∗ Ψ k y') :=
      (imp_mono_l (pure_true hget_m₂).2).trans true_imp.1
    exact sep_comm.1.trans <| (sep_mono_r (forall_elim (PROP := PROP) x)).trans <|
      (sep_mono_r (forall_elim (PROP := PROP) y')).trans <|
      (sep_mono_r h1).trans <| (sep_mono_r h2).trans (sep_comm.1.trans wand_elim_l)

/-! ## Key Mapping Lemmas -/

section Kmap

variable {K₂ : Type _} {M₂ : Type _ → Type _}
variable [DecidableEq K₂]

omit [DecidableEq V] [FiniteMapLawsSelf K M] [DecidableEq K₂] in
/-- Corresponds to `big_sepM_kmap` in Rocq Iris.
    Note: The Rocq proof uses `map_to_list_kmap` (which we encode as `hperm`) and `big_opL_fmap`.
    The `hinj` (injectivity) is needed in Rocq for `kmap` to be well-defined; here we take
    an explicit permutation witness instead. -/
theorem kmap [DecidableEq K₂] [FiniteMap K₂ M₂] [FiniteMapLaws K₂ M₂] [FiniteMapKmapLaws K K₂ M M₂]
    {Φ : K₂ → V → PROP} {m : M V}
    (f : K → K₂)
    (hinj : ∀ {x y}, f x = f y → x = y):
    ([∗map] k₂ ↦ y ∈ (FiniteMap.kmap f m : M₂ V), Φ k₂ y) ⊣⊢
      [∗map] k₁ ↦ y ∈ m, Φ (f k₁) y := by
  exact equiv_iff.mp (@BigOpM.kmap PROP _ sep emp _ M K V _ _ _ M₂ K₂ _ _ _ _ f @hinj Φ m)

end Kmap

/-! ## List to Map Conversion Lemmas -/

section ListToMap

variable [FiniteMap Nat M]
variable [FiniteMapLaws Nat M]
variable [FiniteMapSeqLaws M]

omit [DecidableEq V] in
/-- Corresponds to `big_sepM_map_seq` in Rocq Iris. -/
theorem map_seq {Φ : Nat → V → PROP} (start : Nat) (l : List V) :
    ([∗map] k ↦ x ∈ (FiniteMap.map_seq start l : M V), Φ k x) ⊣⊢
      ([∗list] i ↦ x ∈ l, Φ (start + i) x) := by
  simp only [bigSepM, bigSepL]
  exact equiv_iff.mp (BigOpM.map_seq (op := sep) (unit := emp) Φ start l)

end ListToMap

/-! ## Domain and Set Conversion Lemmas -/

section DomainSet

variable {S : Type _} [FiniteSet K S] [FiniteSetLaws K S]

omit [FiniteMapLawsSelf K M] in
/-- Corresponds to `big_sepM_dom` in Rocq Iris. -/
theorem dom {Φ : K → PROP} (m : M V) :
    ([∗map] k ↦ _v ∈ m, Φ k) ⊣⊢ ([∗set] k ∈ (domSet m : S), Φ k) := by
  induction m using @FiniteMapLaws.map_ind K M _ _ _ with
  | hemp =>
    rw [domSet_empty]
    exact ⟨empty.1.trans BigSepS.empty.2, BigSepS.empty.1.trans empty.2⟩
  | hins k v m hk_not_in IH =>
    have hk_not_in_dom : FiniteSet.mem k (domSet m : S) = false := by
      cases h : FiniteSet.mem k (domSet m : S)
      · rfl
      · have ⟨v', hv⟩ := elem_of_domSet m k |>.mpr h
        rw [hk_not_in] at hv
        cases hv
    have hinsert_eq : FiniteSet.insert k (domSet m : S) ≡ FiniteSet.singleton k ∪ (domSet m : S) := by
      intro x
      constructor
      · intro h
        by_cases hx : x = k
        · apply FiniteSet.mem_union _ _ _ |>.mpr
          left
          exact FiniteSet.mem_singleton _ _ |>.mpr hx
        · have hmem := (FiniteSet.mem_insert_ne _ _ _ hx).mp h
          apply FiniteSet.mem_union _ _ _ |>.mpr
          right
          exact hmem
      · intro h
        have hmem := FiniteSet.mem_union _ _ _ |>.mp h
        cases hmem with
        | inl hsing =>
          have : x = k := FiniteSet.mem_singleton _ _ |>.mp hsing
          exact FiniteSet.mem_insert_eq _ _ _ this
        | inr hdom =>
          by_cases hx : x = k
          · exact FiniteSet.mem_insert_eq _ _ _ hx
          · exact (FiniteSet.mem_insert_ne _ _ _ hx).mpr hdom
    have hdom_eq : ∀ x, FiniteSet.mem x (FiniteSet.singleton k ∪ (domSet m : S)) =
                        FiniteSet.mem x (domSet (FiniteMap.insert m k v) : S) := by
      intro x
      by_cases hx : x = k
      · rw [hx]
        have h1 : FiniteSet.mem k (FiniteSet.singleton k ∪ (domSet m : S)) = true := by
          apply FiniteSet.mem_union _ _ _ |>.mpr
          left
          exact FiniteSet.mem_singleton _ _ |>.mpr rfl
        have h2 : FiniteSet.mem k (domSet (FiniteMap.insert m k v) : S) = true :=
          elem_of_domSet (FiniteMap.insert m k v) k |>.mp ⟨v, lookup_insert_eq m k v⟩
        rw [h1, h2]
      · by_cases hm : FiniteSet.mem x (domSet m : S) = true
        · have h1 : FiniteSet.mem x (FiniteSet.singleton k ∪ (domSet m : S)) = true := by
            apply FiniteSet.mem_union _ _ _ |>.mpr
            right
            exact hm
          have h2 : FiniteSet.mem x (domSet (FiniteMap.insert m k v) : S) = true := by
            have ⟨v', hv⟩ := elem_of_domSet m x |>.mpr hm
            have hne : k ≠ x := fun h => hx h.symm
            have : get? (FiniteMap.insert m k v) x = some v' :=
              (lookup_insert_ne m k x v hne).symm ▸ hv
            exact elem_of_domSet (FiniteMap.insert m k v) x |>.mp ⟨v', this⟩
          rw [h1, h2]
        · have hs : FiniteSet.mem x (FiniteSet.singleton k : S) = false := by
            cases h : FiniteSet.mem x (FiniteSet.singleton k : S)
            · rfl
            · have : x = k := FiniteSet.mem_singleton _ _ |>.mp h
              exact absurd this hx
          have h1 : FiniteSet.mem x (FiniteSet.singleton k ∪ (domSet m : S)) = false := by
            cases h : FiniteSet.mem x (FiniteSet.singleton k ∪ (domSet m : S))
            · rfl
            · have : FiniteSet.mem x (FiniteSet.singleton k : S) = true ∨ FiniteSet.mem x (domSet m : S) = true :=
                FiniteSet.mem_union _ _ _ |>.mp h
              cases this with
              | inl h' => rw [h'] at hs; cases hs
              | inr h' => exact absurd h' hm
          have h2 : FiniteSet.mem x (domSet (FiniteMap.insert m k v) : S) = false := by
            cases h : FiniteSet.mem x (domSet (FiniteMap.insert m k v) : S)
            · rfl
            · have ⟨v', hv'⟩ := elem_of_domSet (FiniteMap.insert m k v) x |>.mpr h
              have hne : k ≠ x := fun h => hx h.symm
              rw [lookup_insert_ne m k x v hne] at hv'
              have : FiniteSet.mem x (domSet m : S) = true :=
                elem_of_domSet m x |>.mp ⟨v', hv'⟩
              exact absurd this hm
          rw [h1, h2]
    calc ([∗map] k' ↦ _v ∈ FiniteMap.insert m k v, Φ k')
        ⊣⊢ Φ k ∗ ([∗map] k' ↦ _v ∈ m, Φ k') := insert hk_not_in
      _ ⊣⊢ Φ k ∗ ([∗set] k' ∈ (domSet m : S), Φ k') := ⟨sep_mono_r IH.1, sep_mono_r IH.2⟩
      _ ⊣⊢ ([∗set] k' ∈ FiniteSet.singleton k ∪ (domSet m : S), Φ k') := (BigSepS.insert hk_not_in_dom).symm
      _ ⊣⊢ ([∗set] k' ∈ (domSet (FiniteMap.insert m k v) : S), Φ k') := by
        -- Use membership equality to show the two bigSepS are equivalent
        have hsub1 : (FiniteSet.singleton k ∪ (domSet m : S)) ⊆ (domSet (FiniteMap.insert m k v) : S) := by
          intro z hz
          rw [mem_iff_mem] at hz ⊢
          rw [← hdom_eq z]; exact hz
        have hsub2 : (domSet (FiniteMap.insert m k v) : S) ⊆ (FiniteSet.singleton k ∪ (domSet m : S)) := by
          intro z hz
          rw [mem_iff_mem] at hz ⊢
          rw [hdom_eq z]; exact hz
        have ⟨l₁, hperm1⟩ := FiniteSet.toList_subset (domSet (FiniteMap.insert m k v) : S) _ hsub1
        have ⟨l₂, hperm2⟩ := FiniteSet.toList_subset (FiniteSet.singleton k ∪ (domSet m : S)) _ hsub2
        have hl1_nil : l₁ = [] := by
          have h1 := hperm1.length_eq
          have h2 := hperm2.length_eq
          simp only [List.length_append] at h1 h2
          have : l₁.length = 0 := by omega
          match l₁ with
          | [] => rfl
          | _ :: _ => simp at this
        rw [hl1_nil, List.append_nil] at hperm1
        unfold bigSepS
        exact equiv_iff.mp (@BigOpL.perm PROP _ _ sep emp _ Φ _ _ hperm1)

/-- Corresponds to `big_sepM_gset_to_gmap` in Rocq Iris. -/
theorem ofSet' {Φ : K → V → PROP} (X : S) (c : V) :
    ([∗map] k ↦ a ∈ (ofSet c X : M V), Φ k a) ⊣⊢ ([∗set] k ∈ X, Φ k c) := by
  have hlookup : ∀ k v, get? (ofSet c X : M V) k = some v → v = c := by
    intro k v hv
    -- Use elem_of_list_to_map_2 to get membership from lookup
    have hmem : (k, v) ∈ (FiniteSet.toList X).map (fun x => (x, c)) := by
      simp only [ofSet] at hv
      exact FiniteMapLaws.elem_of_list_to_map_2 _ _ _ hv
    rw [List.mem_map] at hmem
    obtain ⟨x, _, heq⟩ := hmem
    simp at heq
    exact heq.2.symm

  have h1 : ([∗map] k ↦ a ∈ (ofSet c X : M V), Φ k a) ≡
            ([∗map] k ↦ a ∈ (ofSet c X : M V), Φ k c) := by
    apply proper
    intro k v hv
    have : v = c := hlookup k v hv
    rw [this]
  have h2 : ([∗map] k ↦ a ∈ (ofSet c X : M V), Φ k c) ⊣⊢
            ([∗set] k ∈ (domSet (ofSet c X : M V) : S), Φ k c) := dom _
  -- domSet_ofSet gives us set equivalence, convert to bigSepS equivalence
  have h3 : ([∗set] k ∈ (domSet (ofSet c X : M V) : S), Φ k c) ⊣⊢
            ([∗set] k ∈ X, Φ k c) := by
    have hequiv := @domSet_ofSet K M _ _ _ S _ _ V c X
    -- Use membership equality to show the two bigSepS are equivalent
    have hmem_eq : ∀ z, FiniteSet.mem z (domSet (ofSet c X : M V) : S) = FiniteSet.mem z X := by
      intro z
      cases h : FiniteSet.mem z (domSet (ofSet c X : M V) : S) <;>
        cases h' : FiniteSet.mem z X
      · rfl
      · -- h says mem z (domSet ...) = false, h' says mem z X = true
        -- But hequiv z says z ∈ domSet ... ↔ z ∈ X, so this is a contradiction
        have hz_in_X : z ∈ X := h'
        have hz_in_dom : z ∈ (domSet (ofSet c X : M V) : S) := (hequiv z).mpr hz_in_X
        have : FiniteSet.mem z (domSet (ofSet c X : M V) : S) = true := hz_in_dom
        rw [h] at this
        cases this
      · -- h says mem z (domSet ...) = true, h' says mem z X = false
        have hz_in_dom : z ∈ (domSet (ofSet c X : M V) : S) := h
        have hz_in_X : z ∈ X := (hequiv z).mp hz_in_dom
        have : FiniteSet.mem z X = true := hz_in_X
        rw [h'] at this
        cases this
      · rfl
    have hsub1 : (domSet (ofSet c X : M V) : S) ⊆ X := by
      intro z hz
      have : FiniteSet.mem z (domSet (ofSet c X : M V) : S) = true := hz
      rw [hmem_eq z] at this
      exact this
    have hsub2 : X ⊆ (domSet (ofSet c X : M V) : S) := by
      intro z hz
      have : FiniteSet.mem z X = true := hz
      rw [← hmem_eq z] at this
      exact this
    have ⟨l₁, hperm1⟩ := FiniteSet.toList_subset X _ hsub1
    have ⟨l₂, hperm2⟩ := FiniteSet.toList_subset (domSet (ofSet c X : M V) : S) _ hsub2
    have hl1_nil : l₁ = [] := by
      have h1 := hperm1.length_eq
      have h2 := hperm2.length_eq
      simp only [List.length_append] at h1 h2
      have : l₁.length = 0 := by omega
      match l₁ with
      | [] => rfl
      | _ :: _ => simp at this
    rw [hl1_nil, List.append_nil] at hperm1
    unfold bigSepS
    exact equiv_iff.mp (@BigOpL.perm PROP _ _ sep emp _ (Φ · c) _ _ hperm1)
  have h1' : ([∗map] k ↦ a ∈ (ofSet c X : M V), Φ k a) ⊣⊢
             ([∗map] k ↦ a ∈ (ofSet c X : M V), Φ k c) := BI.equiv_iff.mp h1
  exact BiEntails.trans h1' (BiEntails.trans h2 h3)

end DomainSet

/-! ## Commuting Lemmas -/

omit [DecidableEq K] [FiniteMapLaws K M] [FiniteMapLawsSelf K M] [DecidableEq V] in
/-- Corresponds to `big_sepM_sepL` in Rocq Iris. -/
theorem sepL {B : Type _} (Φ : K → V → Nat → B → PROP) (m : M V) (l : List B) :
    ([∗map] k↦x ∈ m, [∗list] k'↦y ∈ l, Φ k x k' y) ⊣⊢
      ([∗list] k'↦y ∈ l, [∗map] k↦x ∈ m, Φ k x k' y) := by
  calc [∗map] k↦x ∈ m, [∗list] k'↦y ∈ l, Φ k x k' y
      _ ⊣⊢ [∗list] kv ∈ toList m, [∗list] k'↦y ∈ l, Φ kv.1 kv.2 k' y :=
          equiv_iff.mp <| BigSepL.congr fun _ kv => .rfl
      _ ⊣⊢ [∗list] k'↦y ∈ l, [∗list] kv ∈ toList m, Φ kv.1 kv.2 k' y :=
          @BigSepL.sepL PROP _ (K × V) B (fun _ kv k' y => Φ kv.1 kv.2 k' y) (toList m) l
      _ ⊣⊢ [∗list] k'↦y ∈ l, [∗map] k↦x ∈ m, Φ k x k' y :=
          equiv_iff.mp <| BigSepL.congr fun k' y => .rfl

omit [DecidableEq K] [FiniteMapLaws K M] [FiniteMapLawsSelf K M] [DecidableEq V] in
/-- Corresponds to `big_sepM_sepM` in Rocq Iris. -/
theorem sepM {M₂ : Type _ → Type _} {K₂ : Type _} {V₂ : Type _}
    [DecidableEq K₂] [FiniteMap K₂ M₂] [FiniteMapLaws K₂ M₂]
    (Φ : K → V → K₂ → V₂ → PROP) (m₁ : M V) (m₂ : M₂ V₂) :
    ([∗map] k₁↦x₁ ∈ m₁, [∗map] k₂↦x₂ ∈ m₂, Φ k₁ x₁ k₂ x₂) ⊣⊢
      ([∗map] k₂↦x₂ ∈ m₂, [∗map] k₁↦x₁ ∈ m₁, Φ k₁ x₁ k₂ x₂) := by
  calc [∗map] k₁↦x₁ ∈ m₁, [∗map] k₂↦x₂ ∈ m₂, Φ k₁ x₁ k₂ x₂
      _ ⊣⊢ [∗list] kv₁ ∈ toList m₁, [∗map] k₂↦x₂ ∈ m₂, Φ kv₁.1 kv₁.2 k₂ x₂ :=
          equiv_iff.mp <| BigSepL.congr fun _ kv₁ => .rfl
      _ ⊣⊢ [∗list] kv₁ ∈ toList m₁, [∗list] kv₂ ∈ toList m₂, Φ kv₁.1 kv₁.2 kv₂.1 kv₂.2 :=
          equiv_iff.mp <| BigSepL.congr fun _ kv₁ => .rfl
      _ ⊣⊢ [∗list] kv₂ ∈ toList m₂, [∗list] kv₁ ∈ toList m₁, Φ kv₁.1 kv₁.2 kv₂.1 kv₂.2 :=
          @BigSepL.sepL PROP _ (K × V) (K₂ × V₂) (fun _ kv₁ _ kv₂ => Φ kv₁.1 kv₁.2 kv₂.1 kv₂.2)
            (toList m₁) (toList m₂)
      _ ⊣⊢ [∗list] kv₂ ∈ toList m₂, [∗map] k₁↦x₁ ∈ m₁, Φ k₁ x₁ kv₂.1 kv₂.2 :=
          equiv_iff.mp <| BigSepL.congr fun _ kv₂ => .rfl
      _ ⊣⊢ [∗map] k₂↦x₂ ∈ m₂, [∗map] k₁↦x₁ ∈ m₁, Φ k₁ x₁ k₂ x₂ :=
          equiv_iff.mp <| BigSepL.congr fun _ kv₂ => .rfl

omit [DecidableEq K] [FiniteMapLaws K M] [FiniteMapLawsSelf K M] [DecidableEq V] in
/-- Corresponds to `big_sepM_sepS` in Rocq Iris. -/
theorem sepS {B : Type _} {S : Type _}
    [DecidableEq B] [FiniteSet B S] [FiniteSetLaws B S]
    (Φ : K → V → B → PROP) (m : M V) (X : S) :
    ([∗map] k↦x ∈ m, [∗set] y ∈ X, Φ k x y) ⊣⊢
      ([∗set] y ∈ X, [∗map] k↦x ∈ m, Φ k x y) := by
  calc [∗map] k↦x ∈ m, [∗set] y ∈ X, Φ k x y
      _ ⊣⊢ [∗list] kv ∈ toList m, [∗set] y ∈ X, Φ kv.1 kv.2 y :=
          equiv_iff.mp <| BigSepL.congr fun _ kv => .rfl
      _ ⊣⊢ [∗list] kv ∈ toList m, [∗list] y ∈ toList X, Φ kv.1 kv.2 y :=
          equiv_iff.mp <| BigSepL.congr fun _ kv => .rfl
      _ ⊣⊢ [∗list] y ∈ toList X, [∗list] kv ∈ toList m, Φ kv.1 kv.2 y :=
          @BigSepL.sepL PROP _ (K × V) B (fun _ kv _ y => Φ kv.1 kv.2 y) (toList m) (toList X)
      _ ⊣⊢ [∗list] y ∈ toList X, [∗map] k↦x ∈ m, Φ k x y :=
          equiv_iff.mp <| BigSepL.congr fun _ y => .rfl
      _ ⊣⊢ [∗set] y ∈ X, [∗map] k↦x ∈ m, Φ k x y :=
          equiv_iff.mp <| BigSepL.congr fun _ y => .rfl

end BigSepM

end Iris.BI
