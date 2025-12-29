/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.BI.BigOp
import Iris.BI.BigOpMap
import Iris.BI.Instances
import Iris.Std.TC

namespace Iris.BI

open Iris.Algebra
open Iris.Std
open BIBase

/-! # Big Separating Conjunction over Maps

This file provides theorems for big separating conjunction over finite maps.

## References

- Rocq Iris: `iris/bi/big_op.v`, Section `sep_map` (lines 1388-1735)
-/

variable {PROP : Type _} [BI PROP]
variable {M : Type _} {K : Type _} {V : Type _}
variable [DecidableEq K] [FiniteMap M K V] [FiniteMapLaws M K V]

namespace BigSepM

/-! ## Basic Structural Lemmas -/

/-- Corresponds to `big_sepM_empty` in Rocq Iris. -/
@[simp]
theorem empty {Φ : K → V → PROP} :
    ([∗ map] k ↦ x ∈ (∅ : M), Φ k x) ⊣⊢ emp := by
  simp only [bigSepM, map_to_list_empty, bigOpL]
  exact .rfl

/-- Corresponds to `big_sepM_empty'` in Rocq Iris. -/
theorem empty' {P : PROP} [Affine P] {Φ : K → V → PROP} :
    P ⊢ [∗ map] k ↦ x ∈ (∅ : M), Φ k x :=
  Affine.affine.trans empty.2

/-- Corresponds to `big_sepM_singleton` in Rocq Iris. -/
theorem singleton {Φ : K → V → PROP} {k : K} {v : V} :
    ([∗ map] k' ↦ x ∈ ({[k := v]} : M), Φ k' x) ⊣⊢ Φ k v := by
  have hget : get? (∅ : M) k = none := lookup_empty k
  have hperm : (toList (FiniteMap.insert (∅ : M) k v)).Perm ((k, v) :: toList (∅ : M)) :=
    map_to_list_insert (∅ : M) k v hget
  simp only [map_to_list_empty] at hperm
  simp only [bigSepM, FiniteMap.singleton]
  -- Use that permutation preserves big sep
  have heq : bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) (toList (FiniteMap.insert (∅ : M) k v)) ≡
             bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) [(k, v)] :=
    BigOpL.perm (fun kv => Φ kv.1 kv.2) hperm
  simp only [bigOpL] at heq
  exact (equiv_iff.mp heq).trans ⟨sep_emp.1, sep_emp.2⟩

/-- Corresponds to `big_sepM_insert` in Rocq Iris. -/
theorem insert {Φ : K → V → PROP} {m : M} {k : K} {v : V}
    (h : get? m k = none) :
    ([∗ map] k' ↦ x ∈ FiniteMap.insert m k v, Φ k' x) ⊣⊢
      Φ k v ∗ [∗ map] k' ↦ x ∈ m, Φ k' x := by
  simp only [bigSepM]
  have hperm := map_to_list_insert m k v h
  -- bigOpL over permuted list equals bigOpL over original
  have hperm_eq : bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) (toList (FiniteMap.insert m k v)) ≡
                  bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) ((k, v) :: toList m) :=
    BigOpL.perm _ hperm
  simp only [bigOpL] at hperm_eq
  exact equiv_iff.mp hperm_eq

/-- Corresponds to `big_sepM_insert_delete` in Rocq Iris. -/
theorem insert_delete {Φ : K → V → PROP} {m : M} {k : K} {v : V} :
    ([∗ map] k' ↦ x ∈ FiniteMap.insert m k v, Φ k' x) ⊣⊢
      Φ k v ∗ [∗ map] k' ↦ x ∈ Std.delete m k, Φ k' x := by
  -- Use permutation between insert m k v and insert (Std.delete m k) k v
  have hperm := FiniteMapLaws.toList_insert_delete_perm m k v
  have heq : bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) (toList (FiniteMap.insert m k v)) ≡
             bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) (toList (FiniteMap.insert (Std.delete m k) k v)) :=
    BigOpL.perm _ hperm
  simp only [bigSepM]
  have herase : get? (Std.delete m k) k = none := lookup_delete_eq m k
  have hins := @insert PROP _ M K V _ _ _ Φ (Std.delete m k) k v herase
  exact (equiv_iff.mp heq).trans hins

/-- Corresponds to `big_sepM_delete` in Rocq Iris.
    Splits a big sep over a map into the element at key `k` and the rest. -/
theorem delete {Φ : K → V → PROP} {m : M} {k : K} {v : V}
    (h : get? m k = some v) :
    ([∗ map] k' ↦ x ∈ m, Φ k' x) ⊣⊢ Φ k v ∗ [∗ map] k' ↦ x ∈ Std.delete m k, Φ k' x := by
  simp only [bigSepM]
  have hperm := map_to_list_delete m k v h
  have heq : bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) (toList m) ≡
             bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) ((k, v) :: toList (Std.delete m k)) :=
    BigOpL.perm _ hperm
  simp only [bigOpL] at heq
  exact equiv_iff.mp heq

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
theorem mono {Φ Ψ : K → V → PROP} {m : M}
    (h : ∀ k v, get? m k = some v → Φ k v ⊢ Ψ k v) :
    ([∗ map] k ↦ x ∈ m, Φ k x) ⊢ [∗ map] k ↦ x ∈ m, Ψ k x := by
  simp only [bigSepM]
  apply mono_list
  intro kv hmem
  have hkv : get? m kv.1 = some kv.2 := (elem_of_map_to_list m kv.1 kv.2).mpr hmem
  exact h kv.1 kv.2 hkv

/-- Corresponds to `big_sepM_proper` in Rocq Iris. -/
theorem proper {Φ Ψ : K → V → PROP} {m : M}
    (h : ∀ k v, get? m k = some v → Φ k v ≡ Ψ k v) :
    ([∗ map] k ↦ x ∈ m, Φ k x) ≡ [∗ map] k ↦ x ∈ m, Ψ k x := by
  simp only [bigSepM]
  apply BigOpL.congr
  intro i kv hget
  have hi : i < (toList m).length := List.getElem?_eq_some_iff.mp hget |>.1
  have heq : (toList m)[i] = kv := List.getElem?_eq_some_iff.mp hget |>.2
  have hmem : kv ∈ toList m := heq ▸ List.getElem_mem hi
  have hkv : get? m kv.1 = some kv.2 := (elem_of_map_to_list m kv.1 kv.2).mpr hmem
  exact h kv.1 kv.2 hkv

/-- Unconditional version of `proper`. No direct Rocq equivalent. -/
theorem congr {Φ Ψ : K → V → PROP} {m : M}
    (h : ∀ k v, Φ k v ≡ Ψ k v) :
    ([∗ map] k ↦ x ∈ m, Φ k x) ≡ [∗ map] k ↦ x ∈ m, Ψ k x :=
  proper (fun k v _ => h k v)

/-- Corresponds to `big_sepM_ne` in Rocq Iris. -/
theorem ne {Φ Ψ : K → V → PROP} {m : M} {n : Nat}
    (h : ∀ k v, get? m k = some v → Φ k v ≡{n}≡ Ψ k v) :
    ([∗ map] k ↦ x ∈ m, Φ k x) ≡{n}≡ [∗ map] k ↦ x ∈ m, Ψ k x := by
  simp only [bigSepM]
  apply BigOpL.congr_ne
  intro i kv hget
  have hi : i < (toList m).length := List.getElem?_eq_some_iff.mp hget |>.1
  have heq : (toList m)[i] = kv := List.getElem?_eq_some_iff.mp hget |>.2
  have hmem : kv ∈ toList m := heq ▸ List.getElem_mem hi
  have hkv : get? m kv.1 = some kv.2 := (elem_of_map_to_list m kv.1 kv.2).mpr hmem
  exact h kv.1 kv.2 hkv

/-- Corresponds to `big_sepM_mono'` in Rocq Iris.
    Unconditional mono: we don't need to know that `k ↦ v ∈ m`. -/
theorem mono' {Φ Ψ : K → V → PROP} {m : M}
    (h : ∀ k v, Φ k v ⊢ Ψ k v) :
    ([∗ map] k ↦ x ∈ m, Φ k x) ⊢ [∗ map] k ↦ x ∈ m, Ψ k x :=
  mono (fun k v _ => h k v)

/-- Corresponds to `big_sepM_flip_mono'` in Rocq Iris. -/
theorem flip_mono' {Φ Ψ : K → V → PROP} {m : M}
    (h : ∀ k v, Ψ k v ⊢ Φ k v) :
    ([∗ map] k ↦ x ∈ m, Ψ k x) ⊢ [∗ map] k ↦ x ∈ m, Φ k x :=
  mono' h

/-- Corresponds to `big_sepM_subseteq` in Rocq Iris.
    If `m₂ ⊆ m₁`, we can extract the bigSepM over the smaller map.

    The proof uses the identity `m₂ ∪ (m₁ \ m₂) = m₁` when `m₂ ⊆ m₁`,
    combined with `big_sepM_union` for disjoint maps. -/
theorem subseteq {Φ : K → V → PROP} {m₁ m₂ : M} [FiniteMapLawsSelf M K V] [∀ k v, Affine (Φ k v)]
    (h : m₂ ⊆ m₁) :
    ([∗ map] k ↦ x ∈ m₁, Φ k x) ⊢ [∗ map] k ↦ x ∈ m₂, Φ k x := by
  -- Step 1: m₁ ~ m₂ ∪ (m₁ \ m₂) (as permutation of toLists)
  have hperm := Iris.Std.FiniteMap.toList_difference_union m₁ m₂ h
  -- Step 2: m₂ and (m₁ \ m₂) are disjoint
  have hdisj := Iris.Std.FiniteMap.disjoint_difference_r m₁ m₂
  -- Step 3: toList (m₂ ∪ (m₁ \ m₂)) ~ toList m₂ ++ toList (m₁ \ m₂)
  have hunion_perm := toList_union_disjoint m₂ (m₁ \ m₂) hdisj
  -- Now bigSepM m₁ ≡ bigSepM (m₂ ∪ (m₁ \ m₂)) by permutation
  simp only [bigSepM]
  have heq_m1 : bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) (toList m₁) ≡
               bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) (toList (m₂ ∪ (m₁ \ m₂))) :=
    BigOpL.perm _ hperm.symm
  refine (equiv_iff.mp heq_m1).1.trans ?_
  -- bigSepM (m₂ ∪ (m₁ \ m₂)) ≡ bigSepM m₂ ∗ bigSepM (m₁ \ m₂)
  have heq_union : bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) (toList (m₂ ∪ (m₁ \ m₂))) ≡
                  bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) (toList m₂ ++ toList (m₁ \ m₂)) :=
    BigOpL.perm _ hunion_perm
  refine (equiv_iff.mp heq_union).1.trans ?_
  -- bigOpL over append = sep of two bigOpLs
  have happ := BigOpL.append (op := sep (PROP := PROP)) (unit := emp)
    (fun _ (kv : K × V) => Φ kv.1 kv.2) (toList m₂) (toList (m₁ \ m₂))
  refine (equiv_iff.mp happ).1.trans ?_
  -- Now we have: bigSepM m₂ ∗ bigSepM (m₁ \ m₂) ⊢ bigSepM m₂
  -- Since bigSepM (m₁ \ m₂) is Affine (all Φ k v are Affine), we can drop it
  -- Need to provide the Affine instance for the right side
  haveI : Affine (bigOpL sep emp (fun n (kv : K × V) => Φ kv.1 kv.2) (toList (m₁ \ m₂))) :=
    ⟨BigOpL.closed (fun P => P ⊢ emp) (fun _ kv => Φ kv.1 kv.2) (toList (m₁ \ m₂))
      Entails.rfl
      (fun _ _ h1 h2 => (sep_mono h1 h2).trans sep_emp.1)
      (fun _ _ _ => Affine.affine)⟩
  exact sep_elim_l

/-! ## Typeclass Instances -/

/-- Corresponds to `big_sepM_empty_persistent` in Rocq Iris. -/
instance empty_persistent {Φ : K → V → PROP} :
    Persistent ([∗ map] k ↦ x ∈ (∅ : M), Φ k x) where
  persistent := by
    simp only [bigSepM, map_to_list_empty, bigOpL]
    exact persistently_emp_2

/-- Corresponds to `big_sepM_persistent` in Rocq Iris (conditional version). -/
theorem persistent_cond {Φ : K → V → PROP} {m : M}
    (h : ∀ k v, get? m k = some v → Persistent (Φ k v)) :
    Persistent ([∗ map] k ↦ x ∈ m, Φ k x) where
  persistent := by
    simp only [bigSepM]
    apply BigOpL.closed (fun P => P ⊢ <pers> P) (fun _ kv => Φ kv.1 kv.2) (toList m)
      persistently_emp_2
      (fun _ _ h1 h2 => (sep_mono h1 h2).trans persistently_sep_2)
    intro i kv hget
    have hi : i < (toList m).length := List.getElem?_eq_some_iff.mp hget |>.1
    have heq : (toList m)[i] = kv := List.getElem?_eq_some_iff.mp hget |>.2
    have hmem : kv ∈ toList m := heq ▸ List.getElem_mem hi
    have hkv : get? m kv.1 = some kv.2 := (elem_of_map_to_list m kv.1 kv.2).mpr hmem
    exact (h kv.1 kv.2 hkv).persistent

/-- Corresponds to `big_sepM_persistent'` in Rocq Iris. -/
instance persistent {Φ : K → V → PROP} {m : M} [∀ k v, Persistent (Φ k v)] :
    Persistent ([∗ map] k ↦ x ∈ m, Φ k x) :=
  persistent_cond fun _ _ _ => inferInstance

/-- Corresponds to `big_sepM_empty_affine` in Rocq Iris. -/
instance empty_affine {Φ : K → V → PROP} :
    Affine ([∗ map] k ↦ x ∈ (∅ : M), Φ k x) where
  affine := by
    simp only [bigSepM, map_to_list_empty, bigOpL]
    exact Entails.rfl

/-- Corresponds to `big_sepM_affine` in Rocq Iris (conditional version). -/
theorem affine_cond {Φ : K → V → PROP} {m : M}
    (h : ∀ k v, get? m k = some v → Affine (Φ k v)) :
    Affine ([∗ map] k ↦ x ∈ m, Φ k x) where
  affine := by
    simp only [bigSepM]
    apply BigOpL.closed (fun P => P ⊢ emp) (fun _ kv => Φ kv.1 kv.2) (toList m)
      Entails.rfl
      (fun _ _ h1 h2 => (sep_mono h1 h2).trans sep_emp.1)
    intro i kv hget
    have hi : i < (toList m).length := List.getElem?_eq_some_iff.mp hget |>.1
    have heq : (toList m)[i] = kv := List.getElem?_eq_some_iff.mp hget |>.2
    have hmem : kv ∈ toList m := heq ▸ List.getElem_mem hi
    have hkv : get? m kv.1 = some kv.2 := (elem_of_map_to_list m kv.1 kv.2).mpr hmem
    exact (h kv.1 kv.2 hkv).affine

/-- Corresponds to `big_sepM_affine'` in Rocq Iris. -/
instance affine {Φ : K → V → PROP} {m : M} [∀ k v, Affine (Φ k v)] :
    Affine ([∗ map] k ↦ x ∈ m, Φ k x) :=
  affine_cond fun _ _ _ => inferInstance

/-! ## Logical Operations -/

omit [DecidableEq K] [FiniteMapLaws M K V] in
/-- Corresponds to `big_sepM_sep` in Rocq Iris. -/
theorem sep' {Φ Ψ : K → V → PROP} {m : M} :
    ([∗ map] k ↦ x ∈ m, Φ k x ∗ Ψ k x) ⊣⊢
      ([∗ map] k ↦ x ∈ m, Φ k x) ∗ [∗ map] k ↦ x ∈ m, Ψ k x := by
  simp only [bigSepM]
  exact equiv_iff.mp (BigOpL.op_distr _ _ _)

omit [DecidableEq K] [FiniteMapLaws M K V] in
/-- Corresponds to `big_sepM_sep_2` in Rocq Iris. -/
theorem sep_2 {Φ Ψ : K → V → PROP} {m : M} :
    ([∗ map] k ↦ x ∈ m, Φ k x) ∗ ([∗ map] k ↦ x ∈ m, Ψ k x) ⊣⊢
      [∗ map] k ↦ x ∈ m, Φ k x ∗ Ψ k x :=
  sep'.symm

/-- Corresponds to `big_sepM_and` in Rocq Iris (one direction only). -/
theorem and' {Φ Ψ : K → V → PROP} {m : M} :
    ([∗ map] k ↦ x ∈ m, Φ k x ∧ Ψ k x) ⊢
      ([∗ map] k ↦ x ∈ m, Φ k x) ∧ [∗ map] k ↦ x ∈ m, Ψ k x :=
  and_intro (mono' fun _ _ => and_elim_l) (mono' fun _ _ => and_elim_r)

/-- Corresponds to `big_sepM_wand` in Rocq Iris. -/
theorem wand {Φ Ψ : K → V → PROP} {m : M} :
    ([∗ map] k ↦ x ∈ m, Φ k x) ⊢
      ([∗ map] k ↦ x ∈ m, Φ k x -∗ Ψ k x) -∗ [∗ map] k ↦ x ∈ m, Ψ k x :=
  wand_intro <| sep_2.1.trans (mono' fun _ _ => wand_elim_r)

/-! ## Lookup Lemmas -/

/-- Corresponds to `big_sepM_lookup_acc` in Rocq Iris.
    Access a specific element from the big sep while keeping a wand to restore it. -/
theorem lookup_acc {Φ : K → V → PROP} {m : M} {k : K} {v : V}
    (h : get? m k = some v) :
    ([∗ map] k' ↦ x ∈ m, Φ k' x) ⊢
      Φ k v ∗ (Φ k v -∗ [∗ map] k' ↦ x ∈ m, Φ k' x) :=
  -- delete h : bigSepM m ⊣⊢ Φ k v ∗ bigSepM (Std.delete m k)
  -- We need: bigSepM m ⊢ Φ k v ∗ (Φ k v -∗ bigSepM m)
  (delete h).1.trans (sep_mono_r (wand_intro' (delete h).2))

/-- Corresponds to `big_sepM_lookup` in Rocq Iris.
    Extract a specific element from the big sep, discarding the rest.
    Uses TCOr to handle both the Affine case (all predicates are Affine)
    and the Absorbing case (the specific element is Absorbing). -/
theorem lookup {Φ : K → V → PROP} {m : M} {k : K} {v : V}
    (h : get? m k = some v) :
    [TCOr (∀ j w, Affine (Φ j w)) (Absorbing (Φ k v))] →
    ([∗ map] k' ↦ x ∈ m, Φ k' x) ⊢ Φ k v
  | TCOr.l => (delete h).1.trans sep_elim_l
  | TCOr.r => (lookup_acc h).trans (sep_elim_l (P := Φ k v) (Q := iprop(Φ k v -∗ bigSepM Φ m)))

/-- Corresponds to `big_sepM_lookup_dom` in Rocq Iris.
    Lookup when the predicate doesn't depend on the value.
    Uses TCOr to handle both Affine and Absorbing cases.

    Rocq: `is_Some (m !! i) → ([∗ map] k↦_ ∈ m, Φ k) ⊢ Φ i` -/
theorem lookup_dom {Φ : K → PROP} {m : M} {k : K}
    (h : (get? m k).isSome) :
    [TCOr (∀ j, Affine (Φ j)) (Absorbing (Φ k))] →
    bigSepM (fun k' _ => Φ k') m ⊢ Φ k := by
  -- Extract the value from isSome
  have ⟨v, hv⟩ : ∃ v, get? m k = some v := Option.isSome_iff_exists.mp h
  intro htc
  exact match htc with
  | TCOr.l => lookup (Φ := fun k' _ => Φ k') hv
  | TCOr.r => lookup (Φ := fun k' _ => Φ k') hv

/-- Corresponds to `big_sepM_insert_acc` in Rocq Iris.
    Access element at key `k` with ability to update it to any new value. -/
theorem insert_acc {Φ : K → V → PROP} {m : M} {k : K} {v : V}
    (h : get? m k = some v) :
    ([∗ map] k' ↦ x ∈ m, Φ k' x) ⊢
      Φ k v ∗ (∀ v', Φ k v' -∗ [∗ map] k' ↦ x ∈ FiniteMap.insert m k v', Φ k' x) := by
  -- First extract using delete
  have hdel := delete (Φ := Φ) (m := m) h
  refine hdel.1.trans (sep_mono_r ?_)
  -- Now prove: bigSepM (Std.delete m k) ⊢ ∀ v', Φ k v' -∗ bigSepM (insert m k v')
  apply forall_intro
  intro v'
  -- insert m k v' has the same lookup as insert (Std.delete m k) k v'
  have heq : ∀ k', get? (FiniteMap.insert m k v') k' = get? (FiniteMap.insert (Std.delete m k) k v') k' := by
    intro k'
    rw [FiniteMapLaws.lookup_insert, FiniteMapLaws.lookup_insert, FiniteMapLaws.lookup_delete]
    split <;> simp_all
  have hperm := FiniteMapLaws.toList_perm_eq_of_get?_eq heq
  have hperm_eq : bigSepM Φ (FiniteMap.insert m k v') ⊣⊢ bigSepM Φ (FiniteMap.insert (Std.delete m k) k v') := by
    simp only [bigSepM]
    exact equiv_iff.mp (BigOpL.perm _ hperm)
  -- Now use insert on erased map
  have hins := insert (Φ := Φ) (m := Std.delete m k) (k := k) (v := v') (lookup_delete_eq m k)
  -- Need: bigSepM (Std.delete m k) ⊢ Φ k v' -∗ bigSepM (insert m k v')
  -- hins: bigSepM (insert (Std.delete m k) k v') ⊣⊢ Φ k v' ∗ bigSepM (Std.delete m k)
  -- So: Φ k v' ∗ bigSepM (Std.delete m k) ⊢ bigSepM (insert m k v')
  exact wand_intro' (hins.2.trans hperm_eq.2)

/-- Corresponds to `big_sepM_insert_2` in Rocq Iris (Affine version).
    Insert a new element when the predicate at key `k` is affine. -/
theorem insert_2 {Φ : K → V → PROP} {m : M} {k : K} {v : V} [∀ w, Affine (Φ k w)] :
    Φ k v ⊢ ([∗ map] k' ↦ x ∈ m, Φ k' x) -∗ [∗ map] k' ↦ x ∈ FiniteMap.insert m k v, Φ k' x := by
  apply wand_intro
  -- Goal: Φ k v ∗ bigSepM m ⊢ bigSepM (insert m k v)
  cases hm : get? m k with
  | none =>
    -- insert preserves: bigSepM (insert m k v) ⊣⊢ Φ k v ∗ bigSepM m
    exact (insert hm).2
  | some y =>
    -- m has key k with value y, need to replace it
    have hdel := delete (Φ := Φ) (m := m) hm
    -- hdel: bigSepM m ⊣⊢ Φ k y ∗ bigSepM (Std.delete m k)
    -- Goal: Φ k v ∗ bigSepM m ⊢ bigSepM (insert m k v)
    -- Expand bigSepM m: Φ k v ∗ (Φ k y ∗ bigSepM (Std.delete m k))
    refine (sep_mono_r hdel.1).trans ?_
    -- Reassociate: (Φ k v ∗ Φ k y) ∗ bigSepM (Std.delete m k)
    refine (sep_assoc (P := Φ k v) (Q := Φ k y) (R := bigSepM (fun k' x => Φ k' x) (Std.delete m k))).2.trans ?_
    -- Drop Φ k y (affine): Φ k v ∗ bigSepM (Std.delete m k)
    refine (sep_mono_l sep_elim_l).trans ?_
    -- Use insert on erased map
    have hins := insert (Φ := Φ) (m := Std.delete m k) (k := k) (v := v) (lookup_delete_eq m k)
    have heq : ∀ k', get? (FiniteMap.insert m k v) k' = get? (FiniteMap.insert (Std.delete m k) k v) k' := by
      intro k'
      rw [FiniteMapLaws.lookup_insert, FiniteMapLaws.lookup_insert, FiniteMapLaws.lookup_delete]
      split <;> simp_all
    have hperm := FiniteMapLaws.toList_perm_eq_of_get?_eq heq
    have hperm_eq : bigSepM Φ (FiniteMap.insert m k v) ⊣⊢ bigSepM Φ (FiniteMap.insert (Std.delete m k) k v) := by
      simp only [bigSepM]
      exact equiv_iff.mp (BigOpL.perm _ hperm)
    exact hins.2.trans hperm_eq.2

/-- Corresponds to `big_sepM_insert_2` in Rocq Iris (Absorbing version).
    Insert a new element when `Φ k v` is absorbing. -/
theorem insert_2_absorbing {Φ : K → V → PROP} {m : M} {k : K} {v : V} [Absorbing (Φ k v)] :
    Φ k v ⊢ ([∗ map] k' ↦ x ∈ m, Φ k' x) -∗ [∗ map] k' ↦ x ∈ FiniteMap.insert m k v, Φ k' x := by
  apply wand_intro
  cases hm : get? m k with
  | none => exact (insert hm).2
  | some y =>
    have hdel := delete (Φ := Φ) (m := m) hm
    refine (sep_mono_r hdel.1).trans ?_
    refine (sep_assoc (P := Φ k v) (Q := Φ k y) (R := bigSepM (fun k' x => Φ k' x) (Std.delete m k))).2.trans ?_
    -- Use sep_elim_l with Absorbing instance
    refine (sep_mono_l (sep_elim_l (P := Φ k v) (Q := Φ k y))).trans ?_
    have hins := insert (Φ := Φ) (m := Std.delete m k) (k := k) (v := v) (lookup_delete_eq m k)
    have heq : ∀ k', get? (FiniteMap.insert m k v) k' = get? (FiniteMap.insert (Std.delete m k) k v) k' := by
      intro k'
      rw [FiniteMapLaws.lookup_insert, FiniteMapLaws.lookup_insert, FiniteMapLaws.lookup_delete]
      split <;> simp_all
    have hperm := FiniteMapLaws.toList_perm_eq_of_get?_eq heq
    have hperm_eq : bigSepM Φ (FiniteMap.insert m k v) ⊣⊢ bigSepM Φ (FiniteMap.insert (Std.delete m k) k v) := by
      simp only [bigSepM]
      exact equiv_iff.mp (BigOpL.perm _ hperm)
    exact hins.2.trans hperm_eq.2

/-- Corresponds to `big_sepM_insert_override` in Rocq Iris.
    Replacing a value with an equivalent predicate gives equivalent bigSepM. -/
theorem insert_override {Φ : K → V → PROP} {m : M} {k : K} {v v' : V}
    (hm : get? m k = some v)
    (heqv : Φ k v ⊣⊢ Φ k v') :
    ([∗ map] k' ↦ x ∈ FiniteMap.insert m k v', Φ k' x) ⊣⊢ [∗ map] k' ↦ x ∈ m, Φ k' x := by
  constructor
  · -- insert m k v' ⊢ m
    have hins := insert_delete (Φ := Φ) (m := m) (k := k) (v := v')
    refine hins.1.trans ?_
    refine (sep_mono_l heqv.2).trans ?_
    exact (delete hm).2
  · -- m ⊢ insert m k v'
    have hdel := delete (Φ := Φ) (m := m) hm
    refine hdel.1.trans ?_
    refine (sep_mono_l heqv.1).trans ?_
    exact insert_delete.2

/-- Corresponds to `big_sepM_insert_override_1` in Rocq Iris.
    From inserted map, recover original via wand. -/
theorem insert_override_1 {Φ : K → V → PROP} {m : M} {k : K} {v v' : V}
    (hm : get? m k = some v) :
    ([∗ map] k' ↦ x ∈ FiniteMap.insert m k v', Φ k' x) ⊢
      (Φ k v' -∗ Φ k v) -∗ [∗ map] k' ↦ x ∈ m, Φ k' x := by
  -- wand_intro: P ∗ Q ⊢ R  implies  P ⊢ Q -∗ R
  -- So we need: bigSepM (insert m k v') ∗ (Φ k v' -∗ Φ k v) ⊢ bigSepM m
  apply wand_intro'
  -- Swap order: (Φ k v' -∗ Φ k v) ∗ bigSepM (insert m k v')
  refine sep_comm.1.trans ?_
  have hins := insert_delete (Φ := Φ) (m := m) (k := k) (v := v')
  -- Now: bigSepM (insert m k v') ∗ (Φ k v' -∗ Φ k v) ⊢ bigSepM m
  -- hins: bigSepM (insert m k v') ⊣⊢ Φ k v' ∗ bigSepM (Std.delete m k)
  refine (sep_mono_l hins.1).trans ?_
  -- Now: (Φ k v' ∗ bigSepM (Std.delete m k)) ∗ (Φ k v' -∗ Φ k v) ⊢ bigSepM m
  refine (sep_assoc (P := Φ k v') (Q := bigSepM (fun k' x => Φ k' x) (Std.delete m k)) (R := iprop(Φ k v' -∗ Φ k v))).1.trans ?_
  -- Now: Φ k v' ∗ (bigSepM (Std.delete m k) ∗ (Φ k v' -∗ Φ k v)) ⊢ bigSepM m
  refine (sep_mono_r sep_comm.1).trans ?_
  -- Now: Φ k v' ∗ ((Φ k v' -∗ Φ k v) ∗ bigSepM (Std.delete m k)) ⊢ bigSepM m
  refine (sep_assoc (P := Φ k v') (Q := iprop(Φ k v' -∗ Φ k v)) (R := bigSepM (fun k' x => Φ k' x) (Std.delete m k))).2.trans ?_
  -- Now: (Φ k v' ∗ (Φ k v' -∗ Φ k v)) ∗ bigSepM (Std.delete m k) ⊢ bigSepM m
  -- wand_elim_l expects (P -∗ Q) ∗ P, so swap first
  refine (sep_mono_l (sep_comm.1.trans (wand_elim_l (P := Φ k v') (Q := Φ k v)))).trans ?_
  -- Now: Φ k v ∗ bigSepM (Std.delete m k) ⊢ bigSepM m
  exact (delete hm).2

/-- Corresponds to `big_sepM_insert_override_2` in Rocq Iris.
    From original map, get inserted via wand. -/
theorem insert_override_2 {Φ : K → V → PROP} {m : M} {k : K} {v v' : V}
    (hm : get? m k = some v) :
    ([∗ map] k' ↦ x ∈ m, Φ k' x) ⊢
      (Φ k v -∗ Φ k v') -∗ [∗ map] k' ↦ x ∈ FiniteMap.insert m k v', Φ k' x := by
  apply wand_intro'
  refine sep_comm.1.trans ?_
  have hdel := delete (Φ := Φ) (m := m) hm
  -- Now: bigSepM m ∗ (Φ k v -∗ Φ k v') ⊢ bigSepM (insert m k v')
  -- hdel: bigSepM m ⊣⊢ Φ k v ∗ bigSepM (Std.delete m k)
  refine (sep_mono_l hdel.1).trans ?_
  -- Now: (Φ k v ∗ bigSepM (Std.delete m k)) ∗ (Φ k v -∗ Φ k v') ⊢ bigSepM (insert m k v')
  refine (sep_assoc (P := Φ k v) (Q := bigSepM (fun k' x => Φ k' x) (Std.delete m k)) (R := iprop(Φ k v -∗ Φ k v'))).1.trans ?_
  -- Now: Φ k v ∗ (bigSepM (Std.delete m k) ∗ (Φ k v -∗ Φ k v')) ⊢ bigSepM (insert m k v')
  refine (sep_mono_r sep_comm.1).trans ?_
  -- Now: Φ k v ∗ ((Φ k v -∗ Φ k v') ∗ bigSepM (Std.delete m k)) ⊢ bigSepM (insert m k v')
  refine (sep_assoc (P := Φ k v) (Q := iprop(Φ k v -∗ Φ k v')) (R := bigSepM (fun k' x => Φ k' x) (Std.delete m k))).2.trans ?_
  -- Now: (Φ k v ∗ (Φ k v -∗ Φ k v')) ∗ bigSepM (Std.delete m k) ⊢ bigSepM (insert m k v')
  refine (sep_mono_l (sep_comm.1.trans (wand_elim_l (P := Φ k v) (Q := Φ k v')))).trans ?_
  -- Now: Φ k v' ∗ bigSepM (Std.delete m k) ⊢ bigSepM (insert m k v')
  exact insert_delete.2

/-! ## Map Conversion -/

omit [DecidableEq K] [FiniteMapLaws M K V] in
/-- Corresponds to `big_sepM_map_to_list` in Rocq Iris. -/
theorem map_to_list {Φ : K → V → PROP} {m : M} :
    ([∗ map] k ↦ x ∈ m, Φ k x) ⊣⊢ ([∗ list] kv ∈ toList m, Φ kv.1 kv.2) := by
  simp only [bigSepM]
  exact .rfl

/-! ## Persistently and Later -/

omit [DecidableEq K] [FiniteMapLaws M K V] in
/-- Helper for persistently: induction on list. -/
private theorem persistently_list {Φ : K × V → PROP} {l : List (K × V)} [BIAffine PROP] :
    iprop(<pers> bigOpL sep emp (fun _ kv => Φ kv) l) ⊣⊢
      bigOpL sep emp (fun _ kv => iprop(<pers> Φ kv)) l := by
  induction l with
  | nil => simp only [bigOpL]; exact persistently_emp' (PROP := PROP)
  | cons kv kvs ih =>
    simp only [bigOpL]
    exact persistently_sep.trans ⟨sep_mono_r ih.1, sep_mono_r ih.2⟩

omit [DecidableEq K] [FiniteMapLaws M K V] in
/-- Corresponds to `big_sepM_persistently` in Rocq Iris. Requires `BIAffine`. -/
theorem persistently {Φ : K → V → PROP} {m : M} [BIAffine PROP] :
    iprop(<pers> [∗ map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∗ map] k ↦ x ∈ m, <pers> Φ k x := by
  simp only [bigSepM]
  exact persistently_list

omit [DecidableEq K] [FiniteMapLaws M K V] in
/-- Helper for later: induction on list. -/
private theorem later_list {Φ : K × V → PROP} {l : List (K × V)} [BIAffine PROP] :
    iprop(▷ bigOpL sep emp (fun _ kv => Φ kv) l) ⊣⊢
      bigOpL sep emp (fun _ kv => iprop(▷ Φ kv)) l := by
  induction l with
  | nil => simp only [bigOpL]; exact later_emp
  | cons kv kvs ih =>
    simp only [bigOpL]
    exact later_sep.trans ⟨sep_mono_r ih.1, sep_mono_r ih.2⟩

omit [DecidableEq K] [FiniteMapLaws M K V] in
/-- Corresponds to `big_sepM_later` in Rocq Iris. -/
theorem later [BIAffine PROP] {Φ : K → V → PROP} {m : M} :
    iprop(▷ [∗ map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∗ map] k ↦ x ∈ m, ▷ Φ k x := by
  simp only [bigSepM]
  exact later_list

omit [DecidableEq K] [FiniteMapLaws M K V] in
/-- Helper for later_2: induction on list. -/
private theorem later_2_list {Φ : K × V → PROP} {l : List (K × V)} :
    bigOpL sep emp (fun _ kv => iprop(▷ Φ kv)) l ⊢
      iprop(▷ bigOpL sep emp (fun _ kv => Φ kv) l) := by
  induction l with
  | nil => simp only [bigOpL]; exact later_intro
  | cons kv kvs ih =>
    simp only [bigOpL]
    exact (sep_mono_r ih).trans later_sep.2

omit [DecidableEq K] [FiniteMapLaws M K V] in
/-- Corresponds to `big_sepM_later_2` in Rocq Iris. -/
theorem later_2 {Φ : K → V → PROP} {m : M} :
    ([∗ map] k ↦ x ∈ m, ▷ Φ k x) ⊢ iprop(▷ [∗ map] k ↦ x ∈ m, Φ k x) := by
  simp only [bigSepM]
  exact later_2_list

omit [DecidableEq K] [FiniteMapLaws M K V] in
/-- Corresponds to `big_sepM_laterN` in Rocq Iris. -/
theorem laterN [BIAffine PROP] {Φ : K → V → PROP} {m : M} {n : Nat} :
    iprop(▷^[n] [∗ map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∗ map] k ↦ x ∈ m, ▷^[n] Φ k x := by
  induction n with
  | zero => exact .rfl
  | succ k ih => exact (later_congr ih).trans later

omit [DecidableEq K] [FiniteMapLaws M K V] in
/-- Corresponds to `big_sepM_laterN_2` in Rocq Iris. -/
theorem laterN_2 {Φ : K → V → PROP} {m : M} {n : Nat} :
    ([∗ map] k ↦ x ∈ m, ▷^[n] Φ k x) ⊢ iprop(▷^[n] [∗ map] k ↦ x ∈ m, Φ k x) := by
  induction n with
  | zero => exact .rfl
  | succ k ih => exact later_2.trans (later_mono ih)

/-! ## Map Transformations -/

section MapTransformations

variable {M' : Type _} {V' : Type _}
variable [FiniteMap M' K V']

omit [DecidableEq K] [FiniteMapLaws M K V] in
/-- Corresponds to `big_sepM_fmap` in Rocq Iris.
    Big sep over a mapped (fmapped) map is equivalent to composing the predicate with the function.

    Note: Requires `FiniteMapLawsExt M M' K V V'` instance for the specific map types. -/
theorem fmap {Φ : K → V' → PROP} {m : M} (f : V → V')
    (hperm : (toList (FiniteMap.map (M := M) (M' := M') f m)).Perm
              ((toList m).map (fun kv => (kv.1, f kv.2)))) :
    ([∗ map] k ↦ y ∈ FiniteMap.map (M' := M') f m, Φ k y) ⊣⊢
      [∗ map] k ↦ y ∈ m, Φ k (f y) := by
  simp only [bigSepM]
  have heq : bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) (toList (FiniteMap.map (M' := M') f m)) ≡
             bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) ((toList m).map (fun kv => (kv.1, f kv.2))) :=
    BigOpL.perm _ hperm
  refine equiv_iff.mp heq |>.trans ?_
  -- Now show that bigOpL over mapped list equals bigOpL with composed function
  clear heq hperm
  induction (toList m) with
  | nil => exact .rfl
  | cons kv kvs ih =>
    simp only [List.map, bigOpL]
    exact ⟨sep_mono_r ih.1, sep_mono_r ih.2⟩

end MapTransformations

section FilterMapTransformations

omit [DecidableEq K] [FiniteMapLaws M K V] in
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
      -- Goal: bigOpL ... (filterMap ...) ⊣⊢ emp ∗ bigOpL ... kvs
      -- ih: bigOpL ... (filterMap ...) ⊣⊢ bigOpL ... kvs
      -- emp_sep: emp ∗ P ⊣⊢ P, so emp_sep.symm: P ⊣⊢ emp ∗ P
      exact ih.trans emp_sep.symm
    | some y' =>
      simp only [bigOpL, hf]
      -- Goal: Φ kv.1 y' ∗ bigOpL ... (filterMap ...) ⊣⊢ Φ kv.1 y' ∗ bigOpL ... kvs
      exact ⟨sep_mono_r ih.1, sep_mono_r ih.2⟩

omit [DecidableEq K] [FiniteMapLaws M K V] in
/-- Corresponds to `big_sepM_omap` in Rocq Iris.
    Big sep over a filterMapped (omapped) map.

    Note: Requires the permutation proof for the specific map implementation. -/
theorem omap {Φ : K → V → PROP} {m : M} (f : V → Option V)
    (hperm : (toList (FiniteMap.filterMap (M := M) f m)).Perm
              ((toList m).filterMap (fun kv => (f kv.2).map (kv.1, ·)))) :
    ([∗ map] k ↦ y ∈ FiniteMap.filterMap (M := M) f m, Φ k y) ⊣⊢
      [∗ map] k ↦ y ∈ m, match f y with | some y' => Φ k y' | none => emp := by
  simp only [bigSepM]
  have heq : bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) (toList (FiniteMap.filterMap (M := M) f m)) ≡
             bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) ((toList m).filterMap (fun kv => (f kv.2).map (kv.1, ·))) :=
    BigOpL.perm _ hperm
  exact equiv_iff.mp heq |>.trans (omap_list_aux f (toList m))

/-- Corresponds to `big_sepM_union` in Rocq Iris.
    Big sep over a disjoint union splits into a separating conjunction.

    Rocq: `m1 ##ₘ m2 → ([∗ map] k↦y ∈ m1 ∪ m2, Φ k y) ⊣⊢ ([∗ map] k↦y ∈ m1, Φ k y) ∗ ([∗ map] k↦y ∈ m2, Φ k y)` -/
theorem union [FiniteMapLawsSelf M K V] {Φ : K → V → PROP} {m₁ m₂ : M}
    (hdisj : FiniteMap.Disjoint m₁ m₂) :
    ([∗ map] k ↦ y ∈ m₁ ∪ m₂, Φ k y) ⊣⊢
      ([∗ map] k ↦ y ∈ m₁, Φ k y) ∗ [∗ map] k ↦ y ∈ m₂, Φ k y := by
  simp only [bigSepM]
  have hperm := toList_union_disjoint m₁ m₂ hdisj
  have heq : bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) (toList (m₁ ∪ m₂)) ≡
             bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) (toList m₁ ++ toList m₂) :=
    BigOpL.perm _ hperm
  refine equiv_iff.mp heq |>.trans ?_
  exact equiv_iff.mp (BigOpL.append _ (toList m₁) (toList m₂))

end FilterMapTransformations

/-! ## List-Map Conversions -/

/-- Corresponds to `big_sepM_list_to_map` in Rocq Iris.
    Big sep over a map constructed from a list (with no duplicate keys).
    Aligned with Rocq: requires `NoDup l.*1` (no duplicate keys). -/
theorem list_to_map {Φ : K → V → PROP} {l : List (K × V)}
    (hnodup : (l.map Prod.fst).Nodup) :
    ([∗ map] k ↦ x ∈ (ofList l : M), Φ k x) ⊣⊢ [∗ list] kv ∈ l, Φ kv.1 kv.2 := by
  simp only [bigSepM]
  exact equiv_iff.mp (BigOpL.perm _ (map_to_list_to_map l hnodup))

/-! ## Intro and Forall Lemmas -/

/-- Corresponds to `big_sepM_intro` in Rocq Iris.

    Rocq: `□ (∀ k x, ⌜m !! k = Some x⌝ → Φ k x) ⊢ [∗ map] k↦x ∈ m, Φ k x` -/
theorem intro {Φ : K → V → PROP} {m : M} :
    iprop(□ (∀ k v, ⌜get? m k = some v⌝ → Φ k v)) ⊢ [∗ map] k ↦ x ∈ m, Φ k x := by
  simp only [bigSepM]
  generalize hl : toList m = l
  induction l generalizing m with
  | nil =>
    -- □ P ⊢ emp (via affinely_elim_emp)
    exact affinely_elim_emp
  | cons kv kvs ih =>
    simp only [bigOpL]
    -- □ (∀ k v, ⌜...⌝ → Φ k v) ⊢ Φ kv.1 kv.2 ∗ bigOpL ... kvs
    have hmem_kv : kv ∈ toList m := hl ▸ List.mem_cons_self
    have hget_kv := (elem_of_map_to_list m kv.1 kv.2).mpr hmem_kv
    -- Use intuitionistically_sep_idem to duplicate □ P
    refine intuitionistically_sep_idem.2.trans <| sep_mono ?_ ?_
    · -- □ (∀ k v, ...) ⊢ Φ kv.1 kv.2
      refine intuitionistically_elim.trans ?_
      exact (forall_elim kv.1).trans ((forall_elim kv.2).trans
        ((imp_mono_l (pure_mono fun _ => hget_kv)).trans true_imp.1))
    · -- □ (∀ k v, ...) ⊢ bigOpL ... kvs
      have htail : ∀ kv', kv' ∈ kvs → get? m kv'.1 = some kv'.2 := fun kv' hmem =>
        (elem_of_map_to_list m kv'.1 kv'.2).mpr (hl ▸ List.mem_cons_of_mem _ hmem)
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
theorem forall_1' {Φ : K → V → PROP} {m : M} [BIAffine PROP]
    [∀ k v, Persistent (Φ k v)] :
    ([∗ map] k ↦ x ∈ m, Φ k x) ⊢ ∀ k, ∀ v, iprop(⌜get? m k = some v⌝ → Φ k v) := by
  refine forall_intro fun k => forall_intro fun v => imp_intro' <| pure_elim_l fun hget => ?_
  -- Use delete to extract Φ k v, then use persistence to duplicate and drop the rest
  have hdel := delete (Φ := Φ) hget
  exact hdel.1.trans <| (sep_mono_l Persistent.persistent).trans <|
    sep_comm.1.trans <| persistently_absorb_r.trans persistently_elim

/-- Backward direction of `big_sepM_forall` in Rocq Iris. -/
theorem forall_2' {Φ : K → V → PROP} {m : M} [BIAffine PROP]
    [∀ k v, Persistent (Φ k v)] :
    (∀ k v, iprop(⌜get? m k = some v⌝ → Φ k v)) ⊢ [∗ map] k ↦ x ∈ m, Φ k x := by
  simp only [bigSepM]
  generalize hl : toList m = l
  induction l generalizing m with
  | nil => exact Affine.affine
  | cons kv kvs ih =>
    simp only [bigOpL]
    have hmem_kv : kv ∈ toList m := hl ▸ List.mem_cons_self
    have hget_kv := (elem_of_map_to_list m kv.1 kv.2).mpr hmem_kv
    have head_step : iprop(∀ k v, ⌜get? m k = some v⌝ → Φ k v) ⊢ Φ kv.1 kv.2 :=
      (forall_elim kv.1).trans (forall_elim kv.2) |>.trans <|
        (and_intro (pure_intro hget_kv) .rfl).trans imp_elim_r
    have htail : ∀ kv', kv' ∈ kvs → get? m kv'.1 = some kv'.2 := fun kv' hmem =>
      (elem_of_map_to_list m kv'.1 kv'.2).mpr (hl ▸ List.mem_cons_of_mem _ hmem)
    -- Clear ih and prove tail directly
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
theorem forall' {Φ : K → V → PROP} {m : M} [BIAffine PROP]
    [∀ k v, Persistent (Φ k v)] :
    ([∗ map] k ↦ x ∈ m, Φ k x) ⊣⊢ ∀ k, ∀ v, iprop(⌜get? m k = some v⌝ → Φ k v) :=
  ⟨forall_1', forall_2'⟩

/-- Corresponds to `big_sepM_impl` in Rocq Iris. -/
theorem impl {Φ Ψ : K → V → PROP} {m : M} :
    ([∗ map] k ↦ x ∈ m, Φ k x) ⊢
      □ (∀ k v, iprop(⌜get? m k = some v⌝ → Φ k v -∗ Ψ k v)) -∗ [∗ map] k ↦ x ∈ m, Ψ k x := by
  apply wand_intro
  -- First derive: □ (∀ k v, ⌜get? m k = some v⌝ → Φ k v -∗ Ψ k v) ⊢ bigSepM (Φ -∗ Ψ) m
  have h1 : iprop(□ (∀ k v, ⌜get? m k = some v⌝ → Φ k v -∗ Ψ k v)) ⊢ bigSepM (fun k v => iprop(Φ k v -∗ Ψ k v)) m :=
    intro
  -- Now combine: bigSepM Φ ∗ bigSepM (Φ -∗ Ψ) ⊢ bigSepM Ψ
  refine (sep_mono_r h1).trans ?_
  exact sep_2.1.trans (mono' fun _ _ => wand_elim_r)

omit [DecidableEq K] [FiniteMapLaws M K V] in
/-- Corresponds to `big_sepM_dup` in Rocq Iris. -/
theorem dup {P : PROP} [Affine P] {m : M} :
    □ (P -∗ P ∗ P) ⊢ P -∗ [∗ map] _k ↦ _x ∈ m, P := by
  simp only [bigSepM]
  apply wand_intro
  generalize toList m = l
  induction l with
  | nil =>
    simp only [bigOpL]
    exact sep_elim_r.trans Affine.affine
  | cons kv kvs ih =>
    simp only [bigOpL]
    -- Goal: □ (P -∗ P ∗ P) ∗ P ⊢ P ∗ bigOpL sep emp (fun _ _ => P) kvs
    -- Duplicate the box: □ (P -∗ P ∗ P) → □ (P -∗ P ∗ P) ∗ □ (P -∗ P ∗ P)
    refine (sep_mono_l intuitionistically_sep_idem.2).trans <| sep_assoc.1.trans <|
      -- Now: □ (P -∗ P ∗ P) ∗ (□ (P -∗ P ∗ P) ∗ P)
      -- Apply wand_elim on the right: □ (P -∗ P ∗ P) ∗ P → P ∗ P
      (sep_mono_r <| (sep_mono_l intuitionistically_elim).trans wand_elim_l).trans <|
      -- Now: □ (P -∗ P ∗ P) ∗ (P ∗ P)
      -- Reassociate to get (□ (P -∗ P ∗ P) ∗ P) ∗ P for the IH
      sep_assoc.2.trans <| (sep_mono_l ih).trans sep_comm.1

/-- Corresponds to `big_sepM_lookup_acc_impl` in Rocq Iris.
    Access a specific element with ability to restore with a different predicate.

    Note: This lemma is complex due to the universal quantification over Ψ.
    For most use cases, `lookup_acc` or `insert_acc` are simpler alternatives. -/
theorem lookup_acc_impl {Φ : K → V → PROP} {m : M} {k : K} {v : V}
    (hget : get? m k = some v) :
    ([∗ map] k' ↦ x ∈ m, Φ k' x) ⊢
      Φ k v ∗ ∀ (Ψ: K → V → PROP), □ (∀ k' v', iprop(⌜get? m k' = some v'⌝ → ⌜k' ≠ k⌝ → Φ k' v' -∗ Ψ k' v')) -∗
        Ψ k v -∗ [∗ map] k' ↦ x ∈ m, Ψ k' x := by
  -- First extract Φ k v using delete
  have hdel := delete (Φ := Φ) (m := m) hget
  refine hdel.1.trans (sep_mono_r ?_)
  -- Now we need: bigSepM (Std.delete m k) ⊢ ∀ Ψ, □ (...) -∗ Ψ k v -∗ bigSepM m Ψ
  apply forall_intro
  intro Ψ
  apply wand_intro
  apply wand_intro
  -- We have: (bigSepM Φ (Std.delete m k) ∗ □ (...)) ∗ Ψ k v
  -- Goal: bigSepM Ψ m
  -- Use delete on Ψ: bigSepM Ψ m ⊣⊢ Ψ k v ∗ bigSepM Ψ (Std.delete m k)
  have hdelΨ := delete (Φ := Ψ) (m := m) hget
  -- Rearrange to get: Ψ k v ∗ (bigSepM Φ (Std.delete m k) ∗ □ (...))
  refine sep_comm.1.trans <| (sep_mono_r sep_comm.1).trans ?_
  -- Now: Ψ k v ∗ (□ (...) ∗ bigSepM Φ (Std.delete m k))
  refine (sep_mono_r sep_comm.1).trans ?_
  -- Now: Ψ k v ∗ (bigSepM Φ (Std.delete m k) ∗ □ (...))
  -- Use hdelΨ.2: Ψ k v ∗ bigSepM Ψ (Std.delete m k) ⊢ bigSepM Ψ m
  refine (sep_mono_r ?_).trans hdelΨ.2
  -- Need: bigSepM Φ (Std.delete m k) ∗ □ (...) ⊢ bigSepM Ψ (Std.delete m k)
  -- Use impl with the condition that k' ≠ k (since we're on Std.delete m k)
  have himpl : iprop(□ (∀ k' v', ⌜get? m k' = some v'⌝ → ⌜k' ≠ k⌝ → Φ k' v' -∗ Ψ k' v'))
      ⊢ bigSepM (fun k' v' => iprop(Φ k' v' -∗ Ψ k' v')) (Std.delete m k) := by
    -- Transform the □ (∀ k' v', ⌜get? m k' = some v'⌝ → ⌜k' ≠ k⌝ → Φ k' v' -∗ Ψ k' v')
    -- into □ (∀ k' v', ⌜get? (Std.delete m k) k' = some v'⌝ → Φ k' v' -∗ Ψ k' v')
    have htrans : iprop(□ (∀ k' v', ⌜get? m k' = some v'⌝ → ⌜k' ≠ k⌝ → Φ k' v' -∗ Ψ k' v'))
        ⊢ iprop(□ (∀ k' v', ⌜get? (Std.delete m k) k' = some v'⌝ → Φ k' v' -∗ Ψ k' v')) := by
      apply intuitionistically_mono
      apply forall_mono; intro k'
      apply forall_mono; intro v'
      apply imp_intro'
      -- From ⌜get? (Std.delete m k) k' = some v'⌝, derive ⌜get? m k' = some v'⌝ and ⌜k' ≠ k⌝
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

/-- `mapForall φ m` means `φ k v` holds for all key-value pairs in `m`.
    This is equivalent to Rocq Iris's `map_Forall`. -/
def mapForall (φ : K → V → Prop) (m : M) : Prop :=
  ∀ k v, get? m k = some v → φ k v

/-- Corresponds to `big_sepM_pure_1` in Rocq Iris.
    Big sep of pure propositions implies a pure proposition about all entries. -/
theorem pure_1 {φ : K → V → Prop} {m : M} :
    ([∗ map] k ↦ x ∈ m, ⌜φ k x⌝) ⊢ (⌜mapForall φ m⌝ : PROP) := by
  simp only [bigSepM, mapForall]
  -- First prove the list version, then connect to map
  suffices h : ∀ l : List (K × V),
      bigOpL sep emp (fun _ (kv : K × V) => iprop(⌜φ kv.1 kv.2⌝)) l ⊢
        iprop(⌜∀ kv, kv ∈ l → φ kv.1 kv.2⌝) by
    refine (h (toList m)).trans <| pure_mono fun hlist k v hget => ?_
    have hmem : (k, v) ∈ toList m := (elem_of_map_to_list m k v).mp hget
    exact hlist (k, v) hmem
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

/-- Corresponds to `big_sepM_affinely_pure_2` in Rocq Iris.
    An affinely pure proposition about all entries gives big sep of affinely pure propositions. -/
theorem affinely_pure_2 {φ : K → V → Prop} {m : M} :
    iprop(<affine> ⌜mapForall φ m⌝) ⊢ ([∗ map] k ↦ x ∈ m, <affine> ⌜φ k x⌝ : PROP) := by
  simp only [bigSepM, mapForall]
  -- First prove the list version, then connect to map
  suffices h : ∀ l : List (K × V),
      iprop(<affine> ⌜∀ kv, kv ∈ l → φ kv.1 kv.2⌝) ⊢
        bigOpL sep emp (fun _ (kv : K × V) => iprop(<affine> ⌜φ kv.1 kv.2⌝)) l by
    refine (affinely_mono <| pure_mono fun hmap kv hmem => ?_).trans (h (toList m))
    have hget : get? m kv.1 = some kv.2 := (elem_of_map_to_list m kv.1 kv.2).mpr hmem
    exact hmap kv.1 kv.2 hget
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

/-- Corresponds to `big_sepM_pure` in Rocq Iris. Requires `BIAffine`.
    Big sep of pure propositions is equivalent to a pure proposition about all entries. -/
theorem pure' [BIAffine PROP] {φ : K → V → Prop} {m : M} :
    ([∗ map] k ↦ x ∈ m, ⌜φ k x⌝) ⊣⊢ (⌜mapForall φ m⌝ : PROP) :=
  ⟨pure_1, (affine_affinely _).2.trans <| affinely_pure_2.trans (mono' fun _ _ => affinely_elim)⟩

/-! ## Filter Lemmas -/

variable [FiniteMapLawsSelf M K V]

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

/-- Corresponds to `big_sepM_filter'` in Rocq Iris.
    Big sep over a filtered map is equivalent to big sep with conditional predicate.

    Rocq: `Lemma big_sepM_filter' (φ : K * A → Prop) `{∀ kx, Decision (φ kx)} Φ m :
            ([∗ map] k ↦ x ∈ filter φ m, Φ k x) ⊣⊢
            ([∗ map] k ↦ x ∈ m, if decide (φ (k, x)) then Φ k x else emp).` -/
theorem filter' {Φ : K → V → PROP} {m : M}
    (φ : K × V → Prop) [∀ kv, Decidable (φ kv)] :
    ([∗ map] k ↦ x ∈ FiniteMap.filter (fun k v => decide (φ (k, v))) m, Φ k x) ⊣⊢
      [∗ map] k ↦ x ∈ m, if decide (φ (k, x)) then Φ k x else emp := by
  simp only [bigSepM]
  have hperm := toList_filter m (fun k v => decide (φ (k, v)))
  have heq : bigOpL sep emp (fun _ kv => Φ kv.1 kv.2)
               (toList (FiniteMap.filter (fun k v => decide (φ (k, v))) m)) ≡
             bigOpL sep emp (fun _ kv => Φ kv.1 kv.2)
               ((toList m).filter (fun kv => decide (φ kv))) :=
    BigOpL.perm _ hperm
  refine equiv_iff.mp heq |>.trans ?_
  exact filter_list_aux (fun kv => Φ kv.1 kv.2) φ (toList m)

/-- Corresponds to `big_sepM_filter` in Rocq Iris. Requires `BIAffine`.
    Big sep over a filtered map is equivalent to big sep with implication guard.

    Rocq: `Lemma big_sepM_filter `{!BiAffine PROP}
            (φ : K * A → Prop) `{∀ kx, Decision (φ kx)} Φ m :
            ([∗ map] k ↦ x ∈ filter φ m, Φ k x) ⊣⊢
            ([∗ map] k ↦ x ∈ m, ⌜φ (k, x)⌝ → Φ k x).` -/
theorem filter [BIAffine PROP] {Φ : K → V → PROP} {m : M}
    (φ : K × V → Prop) [∀ kv, Decidable (φ kv)] :
    ([∗ map] k ↦ x ∈ FiniteMap.filter (fun k v => decide (φ (k, v))) m, Φ k x) ⊣⊢
      [∗ map] k ↦ x ∈ m, iprop(⌜φ (k, x)⌝ → Φ k x) := by
  -- The proof follows Rocq: `setoid_rewrite <-decide_emp. apply big_sepM_filter'.`
  -- We rewrite using the equivalence: (⌜φ kx⌝ → P) ⊣⊢ (if decide (φ kx) then P else emp)
  have heq : ([∗ map] k ↦ x ∈ m, if decide (φ (k, x)) then Φ k x else emp) ⊣⊢
      [∗ map] k ↦ x ∈ m, iprop(⌜φ (k, x)⌝ → Φ k x) := by
    apply equiv_iff.mp
    apply proper
    intro k v _
    cases hp : decide (φ (k, v)) with
    | false =>
      have hφ : ¬φ (k, v) := of_decide_eq_false hp
      -- emp ≡ (⌜φ (k, v)⌝ → Φ k v) when ¬φ (k, v)
      -- Forward: emp ⊢ ⌜φ (k, v)⌝ → Φ k v (vacuously true since ⌜φ (k, v)⌝ is absurd)
      -- Backward: (⌜φ (k, v)⌝ → Φ k v) ⊢ emp (affine)
      refine equiv_iff.mpr ⟨?_, Affine.affine⟩
      refine imp_intro' <| pure_elim_l fun h => ?_
      exact absurd h hφ
    | true =>
      have hφ : φ (k, v) := of_decide_eq_true hp
      -- Φ k v ≡ (⌜φ (k, v)⌝ → Φ k v) when φ (k, v) holds
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

omit [FiniteMapLawsSelf M K V] in
/-- Corresponds to `big_sepM_fn_insert` in Rocq Iris.
    Big sep over an inserted map where the predicate also depends on a function that is updated.

    Rocq: `m !! i = None →
           ([∗ map] k↦y ∈ <[i:=x]> m, Ψ k y (<[i:=b]> f k))
         ⊣⊢ (Ψ i x b ∗ [∗ map] k↦y ∈ m, Ψ k y (f k))` -/
theorem fn_insert {B : Type _} {Ψ : K → V → B → PROP} {f : K → B} {m : M} {i : K} {x : V} {b : B}
    (h : get? m i = none) :
    ([∗ map] k ↦ y ∈ FiniteMap.insert m i x, Ψ k y (fnInsert f i b k)) ⊣⊢
      Ψ i x b ∗ [∗ map] k ↦ y ∈ m, Ψ k y (f k) := by
  -- Use insert lemma, then show the predicates match
  have hins := insert (Φ := fun k y => Ψ k y (fnInsert f i b k)) (v := x) h
  -- hins: bigSepM (insert m i x) ⊣⊢ Ψ i x (fnInsert f i b i) ∗ bigSepM m
  -- Note: fnInsert f i b i = b
  have hhead : Ψ i x (fnInsert f i b i) ⊣⊢ Ψ i x b := by
    simp only [fnInsert_same]
    exact .rfl
  -- For the tail, we need: for k in m, fnInsert f i b k = f k
  -- Since k ≠ i (because m !! k = some y but m !! i = none)
  have htail : ([∗ map] k ↦ y ∈ m, Ψ k y (fnInsert f i b k)) ⊣⊢
      [∗ map] k ↦ y ∈ m, Ψ k y (f k) := by
    apply equiv_iff.mp
    apply proper
    intro k y hget
    -- k ≠ i since m !! k = some y but m !! i = none
    have hne : k ≠ i := by
      intro heq
      rw [heq, h] at hget
      exact Option.noConfusion hget
    simp only [fnInsert_ne f i b k hne]
    exact OFE.Equiv.rfl
  exact hins.trans ⟨(sep_mono hhead.1 htail.1), (sep_mono hhead.2 htail.2)⟩

omit [FiniteMapLawsSelf M K V] in
/-- Corresponds to `big_sepM_fn_insert'` in Rocq Iris.
    Simpler version where the predicate is just a function of the key.

    Rocq: `m !! i = None →
           ([∗ map] k↦y ∈ <[i:=x]> m, <[i:=P]> Φ k) ⊣⊢ (P ∗ [∗ map] k↦y ∈ m, Φ k)` -/
theorem fn_insert' {Φ : K → PROP} {m : M} {i : K} {x : V} {P : PROP}
    (h : get? m i = none) :
    ([∗ map] k ↦ _y ∈ FiniteMap.insert m i x, fnInsert Φ i P k) ⊣⊢
      P ∗ [∗ map] k ↦ _y ∈ m, Φ k :=
  fn_insert (Ψ := fun _ _ P => P) (f := Φ) (b := P) h

/-! ## Map Zip Lemmas -/

section MapZip

variable {M₁ : Type _} {M₂ : Type _} {V₁ : Type _} {V₂ : Type _}
variable [FiniteMap M₁ K V₁] [FiniteMapLaws M₁ K V₁]
variable [FiniteMap M₂ K V₂] [FiniteMapLaws M₂ K V₂]

omit [FiniteMapLaws M₁ K V₁] [FiniteMapLaws M₂ K V₂] in
/-- Corresponds to `big_sepM_sep_zip_with` in Rocq Iris.
    Big sep over a zipped map with a combining function.

    Rocq proof:
    ```
    intros Hdom Hg1 Hg2. rewrite big_opM_op.
    rewrite -(big_opM_fmap g1) -(big_opM_fmap g2).
    rewrite map_fmap_zip_with_r; [|naive_solver..].
    by rewrite map_fmap_zip_with_l; [|naive_solver..].
    ```

    Note: The Rocq proof uses `hg₁`, `hg₂`, `hdom` through `map_fmap_zip_with_l/r` lemmas.
    In Lean, we pass explicit permutation witnesses `hfmap₁`, `hfmap₂` instead.

    Rocq: `(∀ x y, g1 (f x y) = x) → (∀ x y, g2 (f x y) = y) →
           (∀ k, is_Some (m1 !! k) ↔ is_Some (m2 !! k)) →
           ([∗ map] k↦xy ∈ map_zip_with f m1 m2, Φ1 k (g1 xy) ∗ Φ2 k (g2 xy)) ⊣⊢
           ([∗ map] k↦x ∈ m1, Φ1 k x) ∗ ([∗ map] k↦y ∈ m2, Φ2 k y)` -/
theorem sep_zip_with {C : Type _} {MZ : Type _} [FiniteMap MZ K C] [FiniteMapLaws MZ K C]
    {Φ₁ : K → V₁ → PROP} {Φ₂ : K → V₂ → PROP}
    {f : V₁ → V₂ → C} {g₁ : C → V₁} {g₂ : C → V₂}
    {m₁ : M₁} {m₂ : M₂} {mz : MZ}
    -- These hypotheses are needed for the Rocq proof but replaced by permutation witnesses here
    (_hg₁ : ∀ x y, g₁ (f x y) = x)
    (_hg₂ : ∀ x y, g₂ (f x y) = y)
    (_hdom : ∀ k, (get? m₁ k).isSome ↔ (get? m₂ k).isSome)
    -- Permutation witness for the zipped map (encodes the result of map_zip_with)
    (_hperm : (toList mz).Perm
               ((toList m₁).filterMap (fun kv =>
                  match get? m₂ kv.1 with
                  | some v₂ => some (kv.1, f kv.2 v₂)
                  | none => none)))
    -- Permutation witnesses for fmap laws: g₁ <$> mz ≈ m₁ and g₂ <$> mz ≈ m₂
    (hfmap₁ : (toList m₁).Perm ((toList mz).map (fun kv => (kv.1, g₁ kv.2))))
    (hfmap₂ : (toList m₂).Perm ((toList mz).map (fun kv => (kv.1, g₂ kv.2)))) :
    ([∗ map] k ↦ xy ∈ mz, Φ₁ k (g₁ xy) ∗ Φ₂ k (g₂ xy)) ⊣⊢
      ([∗ map] k ↦ x ∈ m₁, Φ₁ k x) ∗ [∗ map] k ↦ y ∈ m₂, Φ₂ k y := by
  -- Following Rocq: rewrite big_opM_op (our sep')
  -- First unfold bigSepM and use BigOpL.op_distr
  simp only [bigSepM]
  have hsep : bigOpL sep emp (fun _ kv => iprop(Φ₁ kv.1 (g₁ kv.2) ∗ Φ₂ kv.1 (g₂ kv.2))) (toList mz) ≡
              sep (bigOpL sep emp (fun _ kv => Φ₁ kv.1 (g₁ kv.2)) (toList mz))
                  (bigOpL sep emp (fun _ kv => Φ₂ kv.1 (g₂ kv.2)) (toList mz)) :=
    BigOpL.op_distr _ _ _
  refine equiv_iff.mp hsep |>.trans ?_
  -- Now use permutation to show each component equals the original maps
  have heq₁ : bigOpL sep emp (fun _ kv => Φ₁ kv.1 kv.2) (toList m₁) ≡
              bigOpL sep emp (fun _ kv => Φ₁ kv.1 kv.2) ((toList mz).map (fun kv => (kv.1, g₁ kv.2))) :=
    BigOpL.perm _ hfmap₁
  have heq₂ : bigOpL sep emp (fun _ kv => Φ₂ kv.1 kv.2) (toList m₂) ≡
              bigOpL sep emp (fun _ kv => Φ₂ kv.1 kv.2) ((toList mz).map (fun kv => (kv.1, g₂ kv.2))) :=
    BigOpL.perm _ hfmap₂
  -- Show bigOpL over mapped list equals bigOpL with composed function
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
  -- Combine using transitivity
  have h₁ : bigOpL sep emp (fun _ kv => Φ₁ kv.1 (g₁ kv.2)) (toList mz) ≡
            bigOpL sep emp (fun _ kv => Φ₁ kv.1 kv.2) (toList m₁) :=
    hmap₁.trans heq₁.symm
  have h₂ : bigOpL sep emp (fun _ kv => Φ₂ kv.1 (g₂ kv.2)) (toList mz) ≡
            bigOpL sep emp (fun _ kv => Φ₂ kv.1 kv.2) (toList m₂) :=
    hmap₂.trans heq₂.symm
  exact equiv_iff.mp (Monoid.op_proper h₁ h₂)

omit [FiniteMapLaws M₁ K V₁] [FiniteMapLaws M₂ K V₂] in
/-- Corresponds to `big_sepM_sep_zip` in Rocq Iris.
    Big sep over a zipped map is equivalent to sep of big seps over component maps.

    Rocq proof: `intros. by apply big_opM_sep_zip_with.`

    Rocq: `(∀ k, is_Some (m1 !! k) ↔ is_Some (m2 !! k)) →
           ([∗ map] k↦xy ∈ map_zip m1 m2, Φ1 k xy.1 ∗ Φ2 k xy.2) ⊣⊢
           ([∗ map] k↦x ∈ m1, Φ1 k x) ∗ ([∗ map] k↦y ∈ m2, Φ2 k y)` -/
theorem sep_zip {MZ : Type _} [FiniteMap MZ K (V₁ × V₂)] [FiniteMapLaws MZ K (V₁ × V₂)]
    {Φ₁ : K → V₁ → PROP} {Φ₂ : K → V₂ → PROP}
    {m₁ : M₁} {m₂ : M₂}
    (hdom : ∀ k, (get? m₁ k).isSome ↔ (get? m₂ k).isSome)
    -- Permutation witness for the zipped map
    (hperm : (toList (FiniteMap.zip (M := M₁) (M' := M₂) (M'' := MZ) m₁ m₂)).Perm
               ((toList m₁).filterMap (fun kv =>
                  match get? m₂ kv.1 with
                  | some v₂ => some (kv.1, (kv.2, v₂))
                  | none => none)))
    -- Permutation witnesses for projection laws
    (hfmap₁ : (toList m₁).Perm ((toList (FiniteMap.zip (M := M₁) (M' := M₂) (M'' := MZ) m₁ m₂)).map
                (fun kv => (kv.1, kv.2.1))))
    (hfmap₂ : (toList m₂).Perm ((toList (FiniteMap.zip (M := M₁) (M' := M₂) (M'' := MZ) m₁ m₂)).map
                (fun kv => (kv.1, kv.2.2)))) :
    ([∗ map] k ↦ xy ∈ FiniteMap.zip (M := M₁) (M' := M₂) (M'' := MZ) m₁ m₂,
       Φ₁ k xy.1 ∗ Φ₂ k xy.2) ⊣⊢
      ([∗ map] k ↦ x ∈ m₁, Φ₁ k x) ∗ [∗ map] k ↦ y ∈ m₂, Φ₂ k y :=
  -- Following Rocq: just apply sep_zip_with with f = Prod.mk, g₁ = Prod.fst, g₂ = Prod.snd
  sep_zip_with (f := Prod.mk) (g₁ := Prod.fst) (g₂ := Prod.snd)
    (fun _ _ => rfl) (fun _ _ => rfl) hdom hperm hfmap₁ hfmap₂

end MapZip

/-! ## Advanced Impl Lemmas -/

/-- Corresponds to `big_sepM_impl_strong` in Rocq Iris.
    Strong version of impl that tracks which keys are in m₂ vs only in m₁.

    Rocq proof:
    ```
    apply wand_intro_r.
    revert m1. induction m2 as [|i y m ? IH] using map_ind=> m1.
    { rewrite big_sepM_empty left_id sep_elim_l.
      rewrite map_filter_id //. }
    rewrite big_sepM_insert; last done.
    rewrite intuitionistically_sep_dup.
    rewrite assoc. rewrite (comm _ _ (□ _))%I.
    rewrite {1}intuitionistically_elim {1}(forall_elim i) {1}(forall_elim y).
    rewrite lookup_insert_eq pure_True // left_id.
    destruct (m1 !! i) as [x|] eqn:Hx.
    - rewrite big_sepM_delete; last done.
      rewrite assoc assoc wand_elim_l -2!assoc. apply sep_mono_r.
      assert (filter ... = filter ... (delete i m1)) as ->.
      { apply map_filter_strong_ext_1=> k z. ... }
      rewrite -IH. ...
    - rewrite left_id -assoc. apply sep_mono_r.
      assert (filter ... = filter ... m1) as ->.
      { apply map_filter_strong_ext_1=> k z. ... }
      rewrite -IH. ...
    ```

    Rocq: `([∗ map] k↦x ∈ m1, Φ k x) ⊢
           □ (∀ (k : K) (y : B),
             (if m1 !! k is Some x then Φ k x else emp) -∗
             ⌜m2 !! k = Some y⌝ → Ψ k y) -∗
           ([∗ map] k↦y ∈ m2, Ψ k y) ∗
           ([∗ map] k↦x ∈ filter (λ '(k, _), m2 !! k = None) m1, Φ k x)` -/
theorem impl_strong [FiniteMapLawsSelf M K V] {M₂ : Type _} {V₂ : Type _}
    [FiniteMap M₂ K V₂] [FiniteMapLaws M₂ K V₂]
    {Φ : K → V → PROP} {Ψ : K → V₂ → PROP} {m₁ : M} {m₂ : M₂} :
    ([∗ map] k ↦ x ∈ m₁, Φ k x) ⊢
      □ (∀ k, ∀ y, (match get? m₁ k with | some x => Φ k x | none => emp) -∗
         iprop(⌜get? m₂ k = some y⌝ → Ψ k y)) -∗
      ([∗ map] k ↦ y ∈ m₂, Ψ k y) ∗
        [∗ map] k ↦ x ∈ FiniteMap.filter (fun k _ => decide ((get? m₂ k).isNone)) m₁, Φ k x := by
  -- Use wand_intro to move the □(...) to the left
  apply wand_intro
  -- Swap to get □(...) on the left
  refine sep_comm.1.trans ?_
  -- Goal: □(...) ∗ bigSepM Φ m₁ ⊢ bigSepM Ψ m₂ ∗ bigSepM Φ (filter ...)
  -- We work with lists directly
  simp only [bigSepM]
  -- Use list induction on toList m₂
  generalize hl₂ : toList m₂ = l₂
  induction l₂ generalizing m₂ with
  | nil =>
    -- m₂ has empty toList, so bigOpL over it is emp
    simp only [bigOpL]
    -- Goal: □(...) ∗ bigOpL ... m₁ ⊢ emp ∗ bigOpL ... (filter ...)
    refine (sep_mono_l (affinely_elim_emp (PROP := PROP))).trans ?_
    -- Goal: emp ∗ bigOpL ... m₁ ⊢ emp ∗ bigOpL ... (filter ...)
    refine sep_mono_r ?_
    -- Goal: bigOpL ... m₁ ⊢ bigOpL ... (filter ...)
    -- When m₂ is empty (toList m₂ = []), all keys have get? m₂ k = none
    -- So the filter condition is always true, and filter m₁ ≈ m₁
    have hfilter_all : ∀ k v, (k, v) ∈ toList m₁ →
        decide ((get? m₂ k).isNone) = true := by
      intro k v _hmem
      -- Since toList m₂ = [], get? m₂ k = none for all k
      have hempty : toList m₂ = [] := hl₂
      simp only [decide_eq_true_eq]
      cases hget : get? m₂ k with
      | none => rfl
      | some y =>
        have hmem : (k, y) ∈ toList m₂ := (elem_of_map_to_list m₂ k y).mp hget
        rw [hempty] at hmem
        exact False.elim (List.not_mem_nil hmem)
    -- The filter keeps everything, so toList (filter ...) ~ toList m₁
    have hperm := @toList_filter M K V _ _ _ _ m₁ (fun k _ => decide ((get? m₂ k).isNone))
    have hfilter_eq : (toList m₁).filter (fun kv => decide ((get? m₂ kv.1).isNone)) = toList m₁ := by
      apply List.filter_eq_self.mpr
      intro kv hmem
      exact hfilter_all kv.1 kv.2 hmem
    rw [hfilter_eq] at hperm
    exact equiv_iff.mp (BigOpL.perm _ hperm.symm) |>.1
  | cons kv l₂' _ih =>
    /-
    Inductive case: toList m₂ = kv :: l₂'

    BLOCKING ISSUE: List induction on toList m₂ is insufficient.

    The challenge is that l₂' (the tail) might not be the toList of any map m₂'
    such that `get? m₂' = get? m₂` except for kv.1. In other words, we cannot
    easily construct a "smaller map" from the list tail.

    The Rocq proof uses `map_ind` which provides:
    - A smaller map `m` where `m !! kv.1 = None`
    - The relationship `m₂ = <[kv.1 := kv.2]> m`
    - This allows applying `big_sepM_insert` and the IH properly

    To complete this proof, we need one of:
    1. A `map_ind` principle in FiniteMapLaws that provides proper induction on map structure
    2. An `erase` operation that provably gives `toList (erase m₂ kv.1) ~ l₂'`
       (we have `map_to_list_delete` but it requires `get? m₂ kv.1 = some kv.2`)
    3. A way to construct a map from a list and prove properties about it

    For now, this case remains incomplete pending map induction infrastructure.
    -/
    sorry

/-- Corresponds to `big_sepM_impl_dom_subseteq` in Rocq Iris.
    Specialized version when the domain of m₂ is a subset of the domain of m₁.

    Rocq proof:
    ```
    intros. apply entails_wand. rewrite big_sepM_impl_strong.
    apply wand_mono; last done. f_equiv. f_equiv=> k. apply forall_intro=> y.
    apply wand_intro_r, impl_intro_l, pure_elim_l=> Hlm2.
    destruct (m1 !! k) as [x|] eqn:Hlm1.
    - rewrite (forall_elim x) (forall_elim y).
      do 2 rewrite pure_True // left_id //. apply wand_elim_l.
    - apply elem_of_dom_2 in Hlm2. apply not_elem_of_dom in Hlm1.
      set_solver.
    ```

    Rocq: `(∀ k, is_Some (m2 !! k) → is_Some (m1 !! k)) →
           ([∗ map] k↦x ∈ m1, Φ k x) ⊢
           □ (∀ k x y, ⌜m1 !! k = Some x⌝ → ⌜m2 !! k = Some y⌝ → Φ k x -∗ Ψ k y) -∗
           ([∗ map] k↦y ∈ m2, Ψ k y) ∗
           ([∗ map] k↦x ∈ filter (λ '(k, _), m2 !! k = None) m1, Φ k x)` -/
theorem impl_dom_subseteq [FiniteMapLawsSelf M K V] {M₂ : Type _} {V₂ : Type _}
    [FiniteMap M₂ K V₂] [FiniteMapLaws M₂ K V₂]
    {Φ : K → V → PROP} {Ψ : K → V₂ → PROP} {m₁ : M} {m₂ : M₂}
    (_hdom : ∀ k, (get? m₂ k).isSome → (get? m₁ k).isSome) :
    ([∗ map] k ↦ x ∈ m₁, Φ k x) ⊢
      □ (∀ k x y, iprop(⌜get? m₁ k = some x⌝ → ⌜get? m₂ k = some y⌝ → Φ k x -∗ Ψ k y)) -∗
      ([∗ map] k ↦ y ∈ m₂, Ψ k y) ∗
        [∗ map] k ↦ x ∈ FiniteMap.filter (fun k _ => decide ((get? m₂ k).isNone)) m₁, Φ k x := by
  /-
  Following Rocq proof structure:
  1. apply entails_wand, rewrite big_sepM_impl_strong
  2. apply wand_mono (the conclusion is the same, just need to show hypothesis is weaker)
  3. For each k, show that the dom_subseteq hypothesis implies the impl_strong hypothesis
  4. Use hdom to show that when m₂ !! k = some y, we have m₁ !! k = some x for some x

  This proof depends on impl_strong which requires map induction.
  -/
  sorry

/-! ## Key Mapping Lemmas -/

section Kmap

variable {K₂ : Type _} {M₂ : Type _}
variable [DecidableEq K₂]
variable [FiniteMap M₂ K₂ V] [FiniteMapLaws M₂ K₂ V]

/-- Key map: apply a function to all keys in a map.
    `kmap h m` has entries `(h k, v)` for each `(k, v)` in `m`.
    Requires `h` to be injective to preserve map semantics. -/
def kmap (h : K → K₂) (m : M) : M₂ :=
  ofList ((toList m).map (fun kv => (h kv.1, kv.2)))

omit [DecidableEq K] [FiniteMapLaws M K V] [FiniteMapLawsSelf M K V]
      [DecidableEq K₂] [FiniteMapLaws M₂ K₂ V] in
/-- Corresponds to `big_sepM_kmap` in Rocq Iris.
    Big sep over a key-mapped map is equivalent to composing the predicate with the key function.

    Rocq proof:
    ```
    rewrite big_op.big_opM_unseal /big_op.big_opM_def map_to_list_kmap big_opL_fmap.
    by apply big_opL_proper=> ? [??].
    ```

    Note: The Rocq proof uses `map_to_list_kmap` (which we encode as `hperm`) and `big_opL_fmap`.
    The `hinj` (injectivity) is needed in Rocq for `kmap` to be well-defined; here we take
    an explicit permutation witness instead.

    Rocq: `Inj (=) (=) h →
           ([∗ map] k2 ↦ y ∈ kmap h m, Φ k2 y) ⊣⊢ ([∗ map] k1 ↦ y ∈ m, Φ (h k1) y)` -/
theorem kmap' {Φ : K₂ → V → PROP} {m : M}
    (h : K → K₂) (_hinj : Function.Injective h)
    (hperm : (toList (kmap (M₂ := M₂) h m)).Perm
               ((toList m).map (fun kv => (h kv.1, kv.2)))) :
    ([∗ map] k₂ ↦ y ∈ kmap (M₂ := M₂) h m, Φ k₂ y) ⊣⊢
      [∗ map] k₁ ↦ y ∈ m, Φ (h k₁) y := by
  -- Following Rocq: use map_to_list_kmap (our hperm) and big_opL_fmap
  simp only [bigSepM]
  -- Use permutation to relate kmap's toList to mapped list (corresponds to map_to_list_kmap)
  have heq : bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) (toList (kmap (M₂ := M₂) h m)) ≡
             bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) ((toList m).map (fun kv => (h kv.1, kv.2))) :=
    BigOpL.perm _ hperm
  refine equiv_iff.mp heq |>.trans ?_
  -- Now show bigOpL over mapped list equals bigOpL with composed predicate (corresponds to big_opL_fmap)
  clear heq hperm
  induction (toList m) with
  | nil => exact .rfl
  | cons kv kvs ih =>
    simp only [List.map, bigOpL]
    exact ⟨sep_mono_r ih.1, sep_mono_r ih.2⟩

end Kmap

/-! ## Missing Lemmas from Rocq Iris

The following lemmas from Rocq Iris are not yet fully ported:
- `big_sepM_subseteq`: Uses sorry (needs map difference/union laws)
- `big_sepM_timeless*`: Requires sep_timeless infrastructure

Recently ported:
- `big_sepM_delete`: Added `map_to_list_delete` law to FiniteMapLaws
- `big_sepM_lookup_acc`, `big_sepM_lookup`, `big_sepM_lookup_dom`: Using delete
- `big_sepM_insert_acc`: Uses delete + forall wand
- `big_sepM_insert_2`: Split into Affine/Absorbing versions
- `big_sepM_insert_override*`: All three variants ported
- `big_sepM_fmap`: Added FiniteMapLawsExt for map laws
- `big_sepM_omap`: Added FiniteMapLawsSelf for filterMap laws
- `big_sepM_union`: Added FiniteMapLawsSelf for union laws
- `big_sepM_list_to_map`: Uses get?_ofList and nodup
- Lean-only `lookup_absorbing`, `insert_2_absorbing`: Absorbing versions
- `big_sepM_intro`, `big_sepM_forall`, `big_sepM_impl`: Intro and forall lemmas
- `big_sepM_dup`: Duplication lemma for Affine propositions
- `big_sepM_lookup_acc_impl`: Access with predicate change
- `big_sepM_pure_1`, `big_sepM_affinely_pure_2`, `big_sepM_pure`: Pure lemmas with mapForall
- `big_sepM_filter'`, `big_sepM_filter`: Filter lemmas using FiniteMapLawsSelf
- `big_sepM_fn_insert`, `big_sepM_fn_insert'`: Function insertion lemmas
- `big_sepM_sep_zip_with`, `big_sepM_sep_zip`: Map zip lemmas (require zip infrastructure)
- `big_sepM_impl_strong`, `big_sepM_impl_dom_subseteq`: Advanced impl lemmas
- `big_sepM_kmap`: Key mapping lemma
-/

end BigSepM

end Iris.BI
