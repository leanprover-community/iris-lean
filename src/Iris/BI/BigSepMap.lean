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
  simp only [bigSepM, toList_empty, bigOpL]
  exact .rfl

/-- Corresponds to `big_sepM_empty'` in Rocq Iris. -/
theorem empty' {P : PROP} [Affine P] {Φ : K → V → PROP} :
    P ⊢ [∗ map] k ↦ x ∈ (∅ : M), Φ k x :=
  Affine.affine.trans empty.2

/-- Corresponds to `big_sepM_singleton` in Rocq Iris. -/
theorem singleton {Φ : K → V → PROP} {k : K} {v : V} :
    ([∗ map] k' ↦ x ∈ ({[k := v]} : M), Φ k' x) ⊣⊢ Φ k v := by
  have hget : get? (∅ : M) k = none := get?_empty k
  have hperm : (toList (FiniteMap.insert (∅ : M) k v)).Perm ((k, v) :: toList (∅ : M)) :=
    toList_insert (∅ : M) k v hget
  simp only [toList_empty] at hperm
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
  have hperm := toList_insert m k v h
  -- bigOpL over permuted list equals bigOpL over original
  have hperm_eq : bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) (toList (FiniteMap.insert m k v)) ≡
                  bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) ((k, v) :: toList m) :=
    BigOpL.perm _ hperm
  simp only [bigOpL] at hperm_eq
  exact equiv_iff.mp hperm_eq

/-- Corresponds to `big_sepM_insert_delete` in Rocq Iris. -/
theorem insert_delete {Φ : K → V → PROP} {m : M} {k : K} {v : V} :
    ([∗ map] k' ↦ x ∈ FiniteMap.insert m k v, Φ k' x) ⊣⊢
      Φ k v ∗ [∗ map] k' ↦ x ∈ erase m k, Φ k' x := by
  -- Use permutation between insert m k v and insert (erase m k) k v
  have hperm := FiniteMapLaws.toList_insert_erase_perm m k v
  have heq : bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) (toList (FiniteMap.insert m k v)) ≡
             bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) (toList (FiniteMap.insert (erase m k) k v)) :=
    BigOpL.perm _ hperm
  simp only [bigSepM]
  have herase : get? (erase m k) k = none := get?_erase_eq m k
  have hins := @insert PROP _ M K V _ _ _ Φ (erase m k) k v herase
  exact (equiv_iff.mp heq).trans hins

/-- Corresponds to `big_sepM_delete` in Rocq Iris.
    Splits a big sep over a map into the element at key `k` and the rest. -/
theorem delete {Φ : K → V → PROP} {m : M} {k : K} {v : V}
    (h : get? m k = some v) :
    ([∗ map] k' ↦ x ∈ m, Φ k' x) ⊣⊢ Φ k v ∗ [∗ map] k' ↦ x ∈ erase m k, Φ k' x := by
  simp only [bigSepM]
  have hperm := toList_erase m k v h
  have heq : bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) (toList m) ≡
             bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) ((k, v) :: toList (erase m k)) :=
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
  have hkv : get? m kv.1 = some kv.2 := (toList_get? m kv.1 kv.2).mpr hmem
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
  have hkv : get? m kv.1 = some kv.2 := (toList_get? m kv.1 kv.2).mpr hmem
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
  have hkv : get? m kv.1 = some kv.2 := (toList_get? m kv.1 kv.2).mpr hmem
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
    simp only [bigSepM, toList_empty, bigOpL]
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
    have hkv : get? m kv.1 = some kv.2 := (toList_get? m kv.1 kv.2).mpr hmem
    exact (h kv.1 kv.2 hkv).persistent

/-- Corresponds to `big_sepM_persistent'` in Rocq Iris. -/
instance persistent {Φ : K → V → PROP} {m : M} [∀ k v, Persistent (Φ k v)] :
    Persistent ([∗ map] k ↦ x ∈ m, Φ k x) :=
  persistent_cond fun _ _ _ => inferInstance

/-- Corresponds to `big_sepM_empty_affine` in Rocq Iris. -/
instance empty_affine {Φ : K → V → PROP} :
    Affine ([∗ map] k ↦ x ∈ (∅ : M), Φ k x) where
  affine := by
    simp only [bigSepM, toList_empty, bigOpL]
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
    have hkv : get? m kv.1 = some kv.2 := (toList_get? m kv.1 kv.2).mpr hmem
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
  -- delete h : bigSepM m ⊣⊢ Φ k v ∗ bigSepM (erase m k)
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
    Note: Rocq uses `is_Some (m !! i)`, here we require an explicit value `v`. -/
theorem lookup_dom {Φ : K → PROP} {m : M} {k : K} {v : V}
    (h : get? m k = some v) :
    [TCOr (∀ j, Affine (Φ j)) (Absorbing (Φ k))] →
    bigSepM (fun k' _ => Φ k') m ⊢ Φ k
  | TCOr.l => lookup (Φ := fun k' _ => Φ k') h
  | TCOr.r => lookup (Φ := fun k' _ => Φ k') h

/-- Corresponds to `big_sepM_insert_acc` in Rocq Iris.
    Access element at key `k` with ability to update it to any new value. -/
theorem insert_acc {Φ : K → V → PROP} {m : M} {k : K} {v : V}
    (h : get? m k = some v) :
    ([∗ map] k' ↦ x ∈ m, Φ k' x) ⊢
      Φ k v ∗ (∀ v', Φ k v' -∗ [∗ map] k' ↦ x ∈ FiniteMap.insert m k v', Φ k' x) := by
  -- First extract using delete
  have hdel := delete (Φ := Φ) (m := m) h
  refine hdel.1.trans (sep_mono_r ?_)
  -- Now prove: bigSepM (erase m k) ⊢ ∀ v', Φ k v' -∗ bigSepM (insert m k v')
  apply forall_intro
  intro v'
  -- insert m k v' has the same lookup as insert (erase m k) k v'
  have heq : ∀ k', get? (FiniteMap.insert m k v') k' = get? (FiniteMap.insert (erase m k) k v') k' := by
    intro k'
    rw [FiniteMapLaws.get?_insert, FiniteMapLaws.get?_insert, FiniteMapLaws.get?_erase]
    split <;> simp_all
  have hperm := FiniteMapLaws.toList_perm_eq_of_get?_eq heq
  have hperm_eq : bigSepM Φ (FiniteMap.insert m k v') ⊣⊢ bigSepM Φ (FiniteMap.insert (erase m k) k v') := by
    simp only [bigSepM]
    exact equiv_iff.mp (BigOpL.perm _ hperm)
  -- Now use insert on erased map
  have hins := insert (Φ := Φ) (m := erase m k) (k := k) (v := v') (get?_erase_eq m k)
  -- Need: bigSepM (erase m k) ⊢ Φ k v' -∗ bigSepM (insert m k v')
  -- hins: bigSepM (insert (erase m k) k v') ⊣⊢ Φ k v' ∗ bigSepM (erase m k)
  -- So: Φ k v' ∗ bigSepM (erase m k) ⊢ bigSepM (insert m k v')
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
    -- hdel: bigSepM m ⊣⊢ Φ k y ∗ bigSepM (erase m k)
    -- Goal: Φ k v ∗ bigSepM m ⊢ bigSepM (insert m k v)
    -- Expand bigSepM m: Φ k v ∗ (Φ k y ∗ bigSepM (erase m k))
    refine (sep_mono_r hdel.1).trans ?_
    -- Reassociate: (Φ k v ∗ Φ k y) ∗ bigSepM (erase m k)
    refine (sep_assoc (P := Φ k v) (Q := Φ k y) (R := bigSepM (fun k' x => Φ k' x) (erase m k))).2.trans ?_
    -- Drop Φ k y (affine): Φ k v ∗ bigSepM (erase m k)
    refine (sep_mono_l sep_elim_l).trans ?_
    -- Use insert on erased map
    have hins := insert (Φ := Φ) (m := erase m k) (k := k) (v := v) (get?_erase_eq m k)
    have heq : ∀ k', get? (FiniteMap.insert m k v) k' = get? (FiniteMap.insert (erase m k) k v) k' := by
      intro k'
      rw [FiniteMapLaws.get?_insert, FiniteMapLaws.get?_insert, FiniteMapLaws.get?_erase]
      split <;> simp_all
    have hperm := FiniteMapLaws.toList_perm_eq_of_get?_eq heq
    have hperm_eq : bigSepM Φ (FiniteMap.insert m k v) ⊣⊢ bigSepM Φ (FiniteMap.insert (erase m k) k v) := by
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
    refine (sep_assoc (P := Φ k v) (Q := Φ k y) (R := bigSepM (fun k' x => Φ k' x) (erase m k))).2.trans ?_
    -- Use sep_elim_l with Absorbing instance
    refine (sep_mono_l (sep_elim_l (P := Φ k v) (Q := Φ k y))).trans ?_
    have hins := insert (Φ := Φ) (m := erase m k) (k := k) (v := v) (get?_erase_eq m k)
    have heq : ∀ k', get? (FiniteMap.insert m k v) k' = get? (FiniteMap.insert (erase m k) k v) k' := by
      intro k'
      rw [FiniteMapLaws.get?_insert, FiniteMapLaws.get?_insert, FiniteMapLaws.get?_erase]
      split <;> simp_all
    have hperm := FiniteMapLaws.toList_perm_eq_of_get?_eq heq
    have hperm_eq : bigSepM Φ (FiniteMap.insert m k v) ⊣⊢ bigSepM Φ (FiniteMap.insert (erase m k) k v) := by
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
  -- hins: bigSepM (insert m k v') ⊣⊢ Φ k v' ∗ bigSepM (erase m k)
  refine (sep_mono_l hins.1).trans ?_
  -- Now: (Φ k v' ∗ bigSepM (erase m k)) ∗ (Φ k v' -∗ Φ k v) ⊢ bigSepM m
  refine (sep_assoc (P := Φ k v') (Q := bigSepM (fun k' x => Φ k' x) (erase m k)) (R := iprop(Φ k v' -∗ Φ k v))).1.trans ?_
  -- Now: Φ k v' ∗ (bigSepM (erase m k) ∗ (Φ k v' -∗ Φ k v)) ⊢ bigSepM m
  refine (sep_mono_r sep_comm.1).trans ?_
  -- Now: Φ k v' ∗ ((Φ k v' -∗ Φ k v) ∗ bigSepM (erase m k)) ⊢ bigSepM m
  refine (sep_assoc (P := Φ k v') (Q := iprop(Φ k v' -∗ Φ k v)) (R := bigSepM (fun k' x => Φ k' x) (erase m k))).2.trans ?_
  -- Now: (Φ k v' ∗ (Φ k v' -∗ Φ k v)) ∗ bigSepM (erase m k) ⊢ bigSepM m
  -- wand_elim_l expects (P -∗ Q) ∗ P, so swap first
  refine (sep_mono_l (sep_comm.1.trans (wand_elim_l (P := Φ k v') (Q := Φ k v)))).trans ?_
  -- Now: Φ k v ∗ bigSepM (erase m k) ⊢ bigSepM m
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
  -- hdel: bigSepM m ⊣⊢ Φ k v ∗ bigSepM (erase m k)
  refine (sep_mono_l hdel.1).trans ?_
  -- Now: (Φ k v ∗ bigSepM (erase m k)) ∗ (Φ k v -∗ Φ k v') ⊢ bigSepM (insert m k v')
  refine (sep_assoc (P := Φ k v) (Q := bigSepM (fun k' x => Φ k' x) (erase m k)) (R := iprop(Φ k v -∗ Φ k v'))).1.trans ?_
  -- Now: Φ k v ∗ (bigSepM (erase m k) ∗ (Φ k v -∗ Φ k v')) ⊢ bigSepM (insert m k v')
  refine (sep_mono_r sep_comm.1).trans ?_
  -- Now: Φ k v ∗ ((Φ k v -∗ Φ k v') ∗ bigSepM (erase m k)) ⊢ bigSepM (insert m k v')
  refine (sep_assoc (P := Φ k v) (Q := iprop(Φ k v -∗ Φ k v')) (R := bigSepM (fun k' x => Φ k' x) (erase m k))).2.trans ?_
  -- Now: (Φ k v ∗ (Φ k v -∗ Φ k v')) ∗ bigSepM (erase m k) ⊢ bigSepM (insert m k v')
  refine (sep_mono_l (sep_comm.1.trans (wand_elim_l (P := Φ k v) (Q := Φ k v')))).trans ?_
  -- Now: Φ k v' ∗ bigSepM (erase m k) ⊢ bigSepM (insert m k v')
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

omit [DecidableEq K] [FiniteMapLaws M K V] in
/-- Corresponds to `big_sepM_union` in Rocq Iris.
    Big sep over a disjoint union splits into a separating conjunction.

    Note: Requires the permutation proof for the specific map implementation. -/
theorem union {Φ : K → V → PROP} {m₁ m₂ : M}
    (hperm : (toList (m₁ ∪ m₂)).Perm (toList m₁ ++ toList m₂)) :
    ([∗ map] k ↦ y ∈ m₁ ∪ m₂, Φ k y) ⊣⊢
      ([∗ map] k ↦ y ∈ m₁, Φ k y) ∗ [∗ map] k ↦ y ∈ m₂, Φ k y := by
  simp only [bigSepM]
  have heq : bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) (toList (m₁ ∪ m₂)) ≡
             bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) (toList m₁ ++ toList m₂) :=
    BigOpL.perm _ hperm
  refine equiv_iff.mp heq |>.trans ?_
  -- bigOpL over appended list equals sep of two bigOpLs
  exact equiv_iff.mp (BigOpL.append _ (toList m₁) (toList m₂))

end FilterMapTransformations

/-! ## List-Map Conversions -/

omit [DecidableEq K] [FiniteMapLaws M K V] in
/-- Corresponds to `big_sepM_list_to_map` in Rocq Iris.
    Big sep over a map constructed from a list (with no duplicate keys).

    Note: Requires the permutation proof showing `toList (ofList l)` is a permutation of `l`. -/
theorem list_to_map {Φ : K → V → PROP} {l : List (K × V)}
    (hperm : (toList (ofList l : M)).Perm l) :
    ([∗ map] k ↦ x ∈ (ofList l : M), Φ k x) ⊣⊢ [∗ list] kv ∈ l, Φ kv.1 kv.2 := by
  simp only [bigSepM]
  exact equiv_iff.mp (BigOpL.perm _ hperm)

/-! ## Intro and Forall Lemmas -/

/-- Corresponds to `big_sepM_intro` in Rocq Iris.
    This is the direct translation using `□` modality in the proposition.

    Rocq: `□ (∀ k x, ⌜m !! k = Some x⌝ → Φ k x) ⊢ [∗ map] k↦x ∈ m, Φ k x` -/
theorem intro' {Φ : K → V → PROP} {m : M} :
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
    have hget_kv := (toList_get? m kv.1 kv.2).mpr hmem_kv
    -- Use intuitionistically_sep_idem to duplicate □ P
    refine intuitionistically_sep_idem.2.trans <| sep_mono ?_ ?_
    · -- □ (∀ k v, ...) ⊢ Φ kv.1 kv.2
      refine intuitionistically_elim.trans ?_
      exact (forall_elim kv.1).trans ((forall_elim kv.2).trans
        ((imp_mono_l (pure_mono fun _ => hget_kv)).trans true_imp.1))
    · -- □ (∀ k v, ...) ⊢ bigOpL ... kvs
      have htail : ∀ kv', kv' ∈ kvs → get? m kv'.1 = some kv'.2 := fun kv' hmem =>
        (toList_get? m kv'.1 kv'.2).mpr (hl ▸ List.mem_cons_of_mem _ hmem)
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

/-- Alternative form of `big_sepM_intro` using `[Intuitionistic P]` typeclass.
    This is more convenient when P is known to be intuitionistic at the type level. -/
theorem intro {P : PROP} {Φ : K → V → PROP} {m : M} [Intuitionistic P]
    (h : ∀ k v, get? m k = some v → P ⊢ Φ k v) :
    P ⊢ [∗ map] k ↦ x ∈ m, Φ k x := by
  simp only [bigSepM]
  generalize hl : toList m = l
  induction l generalizing m with
  | nil => exact Intuitionistic.intuitionistic.trans affinely_elim_emp
  | cons kv kvs ih =>
    simp only [bigOpL]
    have hmem_kv : kv ∈ toList m := hl ▸ List.mem_cons_self
    have hget_kv := (toList_get? m kv.1 kv.2).mpr hmem_kv
    refine Intuitionistic.intuitionistic.trans <| intuitionistically_sep_idem.2.trans <|
      sep_mono (intuitionistically_elim.trans (h kv.1 kv.2 hget_kv)) ?_
    refine intuitionistically_elim.trans ?_
    -- For the tail, we need to provide a proof for each element in kvs
    -- Since kvs is a subset of toList m, any kv' in kvs is also in toList m
    have htail : ∀ kv', kv' ∈ kvs → get? m kv'.1 = some kv'.2 := fun kv' hmem =>
      (toList_get? m kv'.1 kv'.2).mpr (hl ▸ List.mem_cons_of_mem _ hmem)
    -- Now we need to show P ⊢ bigOpL sep emp ... kvs
    clear ih hmem_kv hget_kv hl
    induction kvs with
    | nil => exact Intuitionistic.intuitionistic.trans affinely_elim_emp
    | cons kv' kvs' ih' =>
      simp only [bigOpL]
      refine Intuitionistic.intuitionistic.trans <| intuitionistically_sep_idem.2.trans <|
        sep_mono (intuitionistically_elim.trans (h kv'.1 kv'.2 (htail kv' List.mem_cons_self))) ?_
      exact intuitionistically_elim.trans (ih' fun kv'' hmem => htail kv'' (List.mem_cons_of_mem _ hmem))

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
    have hget_kv := (toList_get? m kv.1 kv.2).mpr hmem_kv
    have head_step : iprop(∀ k v, ⌜get? m k = some v⌝ → Φ k v) ⊢ Φ kv.1 kv.2 :=
      (forall_elim kv.1).trans (forall_elim kv.2) |>.trans <|
        (and_intro (pure_intro hget_kv) .rfl).trans imp_elim_r
    have htail : ∀ kv', kv' ∈ kvs → get? m kv'.1 = some kv'.2 := fun kv' hmem =>
      (toList_get? m kv'.1 kv'.2).mpr (hl ▸ List.mem_cons_of_mem _ hmem)
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
  have h1 : iprop(□ (∀ k v, ⌜get? m k = some v⌝ → Φ k v -∗ Ψ k v)) ⊢ bigSepM (fun k v => iprop(Φ k v -∗ Ψ k v)) m := by
    haveI : Intuitionistic iprop(□ (∀ k v, ⌜get? m k = some v⌝ → Φ k v -∗ Ψ k v)) :=
      intuitionistically_intuitionistic _
    exact intro fun k v hget => intuitionistically_elim.trans <|
      (forall_elim k).trans (forall_elim v) |>.trans <|
      (imp_mono_l (pure_mono fun _ => hget)).trans true_imp.1
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
  -- Now we need: bigSepM (erase m k) ⊢ ∀ Ψ, □ (...) -∗ Ψ k v -∗ bigSepM m Ψ
  apply forall_intro
  intro Ψ
  apply wand_intro
  apply wand_intro
  -- We have: (bigSepM Φ (erase m k) ∗ □ (...)) ∗ Ψ k v
  -- Goal: bigSepM Ψ m
  -- Use delete on Ψ: bigSepM Ψ m ⊣⊢ Ψ k v ∗ bigSepM Ψ (erase m k)
  have hdelΨ := delete (Φ := Ψ) (m := m) hget
  -- Rearrange to get: Ψ k v ∗ (bigSepM Φ (erase m k) ∗ □ (...))
  refine sep_comm.1.trans <| (sep_mono_r sep_comm.1).trans ?_
  -- Now: Ψ k v ∗ (□ (...) ∗ bigSepM Φ (erase m k))
  refine (sep_mono_r sep_comm.1).trans ?_
  -- Now: Ψ k v ∗ (bigSepM Φ (erase m k) ∗ □ (...))
  -- Use hdelΨ.2: Ψ k v ∗ bigSepM Ψ (erase m k) ⊢ bigSepM Ψ m
  refine (sep_mono_r ?_).trans hdelΨ.2
  -- Need: bigSepM Φ (erase m k) ∗ □ (...) ⊢ bigSepM Ψ (erase m k)
  -- Use impl with the condition that k' ≠ k (since we're on erase m k)
  have himpl : iprop(□ (∀ k' v', ⌜get? m k' = some v'⌝ → ⌜k' ≠ k⌝ → Φ k' v' -∗ Ψ k' v'))
      ⊢ bigSepM (fun k' v' => iprop(Φ k' v' -∗ Ψ k' v')) (erase m k) := by
    haveI : Intuitionistic iprop(□ (∀ k' v', ⌜get? m k' = some v'⌝ → ⌜k' ≠ k⌝ → Φ k' v' -∗ Ψ k' v')) :=
      intuitionistically_intuitionistic _
    apply intro
    intro k' v' hget'
    have hget_erase : get? (erase m k) k' = some v' := hget'
    have hne : k' ≠ k := by
      intro heq
      rw [heq, get?_erase_eq] at hget_erase
      exact Option.noConfusion hget_erase
    have hget_m : get? m k' = some v' := by
      rw [get?_erase_ne m k k' hne.symm] at hget_erase
      exact hget_erase
    exact intuitionistically_elim.trans <|
      (forall_elim k').trans (forall_elim v') |>.trans <|
      (imp_mono_l (pure_mono fun _ => hget_m)).trans true_imp.1 |>.trans <|
      (imp_mono_l (pure_mono fun _ => hne)).trans true_imp.1
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
    have hmem : (k, v) ∈ toList m := (toList_get? m k v).mp hget
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
    have hget : get? m kv.1 = some kv.2 := (toList_get? m kv.1 kv.2).mpr hmem
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
private theorem filter_list_aux {Φ : K × V → PROP} (p : K × V → Bool) (l : List (K × V)) :
    bigOpL sep emp (fun _ kv => Φ kv) (l.filter p) ⊣⊢
    bigOpL sep emp (fun _ kv => if p kv then Φ kv else emp) l := by
  induction l with
  | nil => simp only [List.filter, bigOpL]; exact .rfl
  | cons kv kvs ih =>
    simp only [List.filter]
    cases hp : p kv with
    | false =>
      simp only [bigOpL, hp]
      exact ih.trans emp_sep.symm
    | true =>
      simp only [bigOpL, hp, ↓reduceIte]
      exact ⟨sep_mono_r ih.1, sep_mono_r ih.2⟩

/-- Corresponds to `big_sepM_filter'` in Rocq Iris.
    Big sep over a filtered map is equivalent to big sep with conditional predicate. -/
theorem filter' {Φ : K → V → PROP} {m : M} (p : K → V → Bool) :
    ([∗ map] k ↦ x ∈ FiniteMap.filter p m, Φ k x) ⊣⊢
      [∗ map] k ↦ x ∈ m, if p k x then Φ k x else emp := by
  simp only [bigSepM]
  have hperm := toList_filter m p
  have heq : bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) (toList (FiniteMap.filter p m)) ≡
             bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) ((toList m).filter (fun kv => p kv.1 kv.2)) :=
    BigOpL.perm _ hperm
  refine equiv_iff.mp heq |>.trans ?_
  exact filter_list_aux (fun kv => p kv.1 kv.2) (toList m)

/-- Corresponds to `big_sepM_filter` in Rocq Iris. Requires `BIAffine`.
    Big sep over a filtered map is equivalent to big sep with implication guard. -/
theorem filter'' [BIAffine PROP] {Φ : K → V → PROP} {m : M} (p : K → V → Bool) :
    ([∗ map] k ↦ x ∈ FiniteMap.filter p m, Φ k x) ⊣⊢
      [∗ map] k ↦ x ∈ m, iprop(⌜p k x = true⌝ → Φ k x) := by
  have heq : ([∗ map] k ↦ x ∈ m, if p k x then Φ k x else emp) ⊣⊢
      [∗ map] k ↦ x ∈ m, iprop(⌜p k x = true⌝ → Φ k x) := by
    apply equiv_iff.mp
    apply proper
    intro k v _
    cases hp : p k v with
    | false =>
      simp only [↓reduceIte, Bool.false_eq_true]
      -- emp ≡ (⌜false⌝ → Φ k v)
      -- Forward: emp ⊢ ⌜false⌝ → Φ k v (vacuously true since ⌜false⌝ is absurd)
      -- Backward: (⌜false⌝ → Φ k v) ⊢ emp (affine)
      refine equiv_iff.mpr ⟨?_, Affine.affine⟩
      refine imp_intro' <| pure_elim_l fun h => ?_
      simp at h
    | true =>
      -- After simp, the goal becomes: Φ k v ≡ (True → Φ k v) since ⌜p k v = true⌝ simplifies to True
      simp only [↓reduceIte]
      -- Now: Φ k v ≡ (True → Φ k v), which is exactly true_imp.symm
      exact equiv_iff.mpr true_imp.symm
  exact (filter' p).trans heq

/-! ## Missing Lemmas from Rocq Iris

The following lemmas from Rocq Iris are not yet fully ported:
- `big_sepM_subseteq`: Uses sorry (needs map difference/union laws)
- `big_sepM_fn_insert*`: Low priority
- `big_sepM_sep_zip*`: Low priority
- `big_sepM_impl_strong`, `big_sepM_impl_dom_subseteq`: Low priority
- `big_sepM_kmap`, `big_sepM_map_seq`: Low priority
- `big_sepM_timeless*`: Requires sep_timeless infrastructure

Recently ported:
- `big_sepM_delete`: Added `toList_erase` law to FiniteMapLaws
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
-/

end BigSepM

end Iris.BI
