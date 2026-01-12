/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.BI.BigOp.BigOp
import Iris.BI.Instances
import Iris.Std.TC

namespace Iris.BI

open Iris.Algebra
open Iris.Std
open BIBase

/-! # Big Conjunction over Maps

Rocq Iris: `iris/bi/big_op.v`, Section `and_map`
-/

variable {PROP : Type _} [BI PROP]
variable {K : Type _} {M : Type _ → Type _} {V : Type _}
variable [DecidableEq K] [DecidableEq V] [FiniteMap K M] [FiniteMapLaws K M]

namespace BigAndM

/-! ## Basic Structural Lemmas -/

/-- Corresponds to `big_andM_empty` in Rocq Iris. -/
@[simp]
theorem empty {Φ : K → V → PROP} :
    ([∧map] k ↦ x ∈ (∅ : M V), Φ k x) ⊣⊢ iprop(True) := by
  simp only [bigAndM, FiniteMapLaws.map_to_list_empty, bigOpL]
  exact .rfl

/-- Corresponds to `big_andM_empty'` in Rocq Iris. -/
theorem empty' {P : PROP} {Φ : K → V → PROP} :
    P ⊢ [∧map] k ↦ x ∈ (∅ : M V), Φ k x :=
  true_intro.trans empty.2

/-- Corresponds to `big_andM_singleton` in Rocq Iris. -/
theorem singleton {Φ : K → V → PROP} {k : K} {v : V} :
    ([∧map] k' ↦ x ∈ ({[k := v]} : M V), Φ k' x) ⊣⊢ Φ k v := by
  have hget : get? (∅ : M V) k = none := lookup_empty k
  have hperm : (toList (FiniteMap.insert (∅ : M V) k v)).Perm ((k, v) :: toList (∅ : M V)) :=
    FiniteMapLaws.map_to_list_insert (∅ : M V) k v hget
  simp only [FiniteMapLaws.map_to_list_empty] at hperm
  simp only [bigAndM, FiniteMap.singleton]
  have heq : bigOpL and iprop(True) (fun _ kv => Φ kv.1 kv.2) (toList (FiniteMap.insert (∅ : M V) k v)) ≡
             bigOpL and iprop(True) (fun _ kv => Φ kv.1 kv.2) [(k, v)] :=
    BigOpL.perm (fun kv => Φ kv.1 kv.2) hperm
  simp only [bigOpL] at heq
  exact (equiv_iff.mp heq).trans ⟨and_elim_l, (and_intro .rfl true_intro)⟩

/-- Corresponds to `big_andM_insert` in Rocq Iris. -/
theorem insert {Φ : K → V → PROP} {m : M V} {k : K} {v : V}
    (h : get? m k = none) :
    ([∧map] k' ↦ x ∈ FiniteMap.insert m k v, Φ k' x) ⊣⊢
      Φ k v ∧ [∧map] k' ↦ x ∈ m, Φ k' x := by
  simp only [bigAndM]
  have hperm := FiniteMapLaws.map_to_list_insert m k v h
  have hperm_eq : bigOpL and iprop(True) (fun _ kv => Φ kv.1 kv.2) (toList (FiniteMap.insert m k v)) ≡
                  bigOpL and iprop(True) (fun _ kv => Φ kv.1 kv.2) ((k, v) :: toList m) :=
    BigOpL.perm _ hperm
  simp only [bigOpL] at hperm_eq
  exact equiv_iff.mp hperm_eq

/-- Corresponds to `big_andM_insert_delete` in Rocq Iris. -/
theorem insert_delete {Φ : K → V → PROP} {m : M V} {k : K} {v : V} :
    ([∧map] k' ↦ x ∈ FiniteMap.insert m k v, Φ k' x) ⊣⊢
      Φ k v ∧ [∧map] k' ↦ x ∈ delete m k, Φ k' x := by
  have hmap_eq := FiniteMapLaws.insert_delete_eq m k v
  simp only [bigAndM, ← hmap_eq]
  have hdelete : get? (delete m k) k = none := lookup_delete_eq m k
  have hins := insert (Φ := Φ) (m := delete m k) (k := k) (v := v) hdelete
  exact hins

/-- Corresponds to `big_andM_delete` in Rocq Iris.
    Splits a big and over a map into the element at key `k` and the rest. -/
theorem delete' {Φ : K → V → PROP} {m : M V} {k : K} {v : V}
    (h : get? m k = some v) :
    ([∧map] k' ↦ x ∈ m, Φ k' x) ⊣⊢ Φ k v ∧ [∧map] k' ↦ x ∈ Std.delete m k, Φ k' x := by
  simp only [bigAndM]
  have hperm := FiniteMapLaws.map_to_list_delete m k v h
  have heq : bigOpL and iprop(True) (fun _ kv => Φ kv.1 kv.2) (toList m) ≡
             bigOpL and iprop(True) (fun _ kv => Φ kv.1 kv.2) ((k, v) :: toList (Std.delete m k)) :=
    BigOpL.perm _ hperm
  simp only [bigOpL] at heq
  exact equiv_iff.mp heq

/-! ## Monotonicity and Congruence -/

omit [DecidableEq K] in
/-- Helper: mono on lists directly. -/
private theorem mono_list {Φ Ψ : K × V → PROP} {l : List (K × V)}
    (h : ∀ kv, kv ∈ l → Φ kv ⊢ Ψ kv) :
    bigOpL and iprop(True) (fun _ kv => Φ kv) l ⊢ bigOpL and iprop(True) (fun _ kv => Ψ kv) l := by
  induction l with
  | nil => exact Entails.rfl
  | cons kv kvs ih =>
    simp only [bigOpL]
    apply and_mono
    · exact h kv List.mem_cons_self
    · exact ih (fun kv' hmem => h kv' (List.mem_cons_of_mem _ hmem))

/-- Corresponds to `big_andM_mono` in Rocq Iris. -/
theorem mono {Φ Ψ : K → V → PROP} {m : M V}
    (h : ∀ k v, get? m k = some v → Φ k v ⊢ Ψ k v) :
    ([∧map] k ↦ x ∈ m, Φ k x) ⊢ [∧map] k ↦ x ∈ m, Ψ k x := by
  simp only [bigAndM]
  apply mono_list
  intro kv hmem
  have hkv : get? m kv.1 = some kv.2 := (FiniteMapLaws.elem_of_map_to_list m kv.1 kv.2).mp hmem
  exact h kv.1 kv.2 hkv

/-- Corresponds to `big_andM_proper` in Rocq Iris. -/
theorem proper {Φ Ψ : K → V → PROP} {m : M V}
    (h : ∀ k v, get? m k = some v → Φ k v ≡ Ψ k v) :
    ([∧map] k ↦ x ∈ m, Φ k x) ≡ [∧map] k ↦ x ∈ m, Ψ k x := by
  simp only [bigAndM]
  apply BigOpL.congr
  intro i kv hget
  have hi : i < (toList m).length := List.getElem?_eq_some_iff.mp hget |>.1
  have heq : (toList m)[i] = kv := List.getElem?_eq_some_iff.mp hget |>.2
  have hmem : kv ∈ toList m := heq ▸ List.getElem_mem hi
  have hkv : get? m kv.1 = some kv.2 := (FiniteMapLaws.elem_of_map_to_list m kv.1 kv.2).mp hmem
  exact h kv.1 kv.2 hkv

/-- Unconditional version of `proper`. No direct Rocq equivalent. -/
theorem congr {Φ Ψ : K → V → PROP} {m : M V}
    (h : ∀ k v, Φ k v ≡ Ψ k v) :
    ([∧map] k ↦ x ∈ m, Φ k x) ≡ [∧map] k ↦ x ∈ m, Ψ k x :=
  proper (fun k v _ => h k v)

/-- Corresponds to `big_andM_ne` in Rocq Iris. -/
theorem ne {Φ Ψ : K → V → PROP} {m : M V} {n : Nat}
    (h : ∀ k v, get? m k = some v → Φ k v ≡{n}≡ Ψ k v) :
    ([∧map] k ↦ x ∈ m, Φ k x) ≡{n}≡ [∧map] k ↦ x ∈ m, Ψ k x := by
  simp only [bigAndM]
  apply BigOpL.congr_ne
  intro i kv hget
  have hi : i < (toList m).length := List.getElem?_eq_some_iff.mp hget |>.1
  have heq : (toList m)[i] = kv := List.getElem?_eq_some_iff.mp hget |>.2
  have hmem : kv ∈ toList m := heq ▸ List.getElem_mem hi
  have hkv : get? m kv.1 = some kv.2 := (FiniteMapLaws.elem_of_map_to_list m kv.1 kv.2).mp hmem
  exact h kv.1 kv.2 hkv

/-- Corresponds to `big_andM_mono'` in Rocq Iris. -/
theorem mono' {Φ Ψ : K → V → PROP} {m : M V}
    (h : ∀ k v, Φ k v ⊢ Ψ k v) :
    ([∧map] k ↦ x ∈ m, Φ k x) ⊢ [∧map] k ↦ x ∈ m, Ψ k x :=
  mono (fun k v _ => h k v)

/-! ## Typeclass Instances -/

/-- Corresponds to `big_andM_empty_persistent` in Rocq Iris. -/
instance empty_persistent {Φ : K → V → PROP} :
    Persistent ([∧map] k ↦ x ∈ (∅ : M V), Φ k x) where
  persistent := by
    simp only [bigAndM, FiniteMapLaws.map_to_list_empty, bigOpL]
    exact persistently_true.2

/-- Corresponds to `big_andM_persistent` in Rocq Iris (conditional version). -/
theorem persistent_cond {Φ : K → V → PROP} {m : M V}
    (h : ∀ k v, get? m k = some v → Persistent (Φ k v)) :
    Persistent ([∧map] k ↦ x ∈ m, Φ k x) where
  persistent := by
    simp only [bigAndM]
    apply BigOpL.closed (fun P => P ⊢ <pers> P) (fun _ kv => Φ kv.1 kv.2) (toList m)
      persistently_true.2
      (fun _ _ h1 h2 => (and_mono h1 h2).trans persistently_and.2)
    intro i kv hget
    have hi : i < (toList m).length := List.getElem?_eq_some_iff.mp hget |>.1
    have heq : (toList m)[i] = kv := List.getElem?_eq_some_iff.mp hget |>.2
    have hmem : kv ∈ toList m := heq ▸ List.getElem_mem hi
    have hkv : get? m kv.1 = some kv.2 := (FiniteMapLaws.elem_of_map_to_list m kv.1 kv.2).mp hmem
    exact (h kv.1 kv.2 hkv).persistent

/-- Corresponds to `big_andM_persistent'` in Rocq Iris. -/
instance persistent {Φ : K → V → PROP} {m : M V} [∀ k v, Persistent (Φ k v)] :
    Persistent ([∧map] k ↦ x ∈ m, Φ k x) :=
  persistent_cond fun _ _ _ => inferInstance

/-- BIAffine instance for bigAndM. -/
instance affine {Φ : K → V → PROP} {m : M V} [BIAffine PROP] :
    Affine ([∧map] k ↦ x ∈ m, Φ k x) where
  affine := by
    simp only [bigAndM]
    induction (toList m) with
    | nil => simp only [bigOpL]; exact true_emp.1
    | cons kv kvs ih => simp only [bigOpL]; exact and_elim_l.trans Affine.affine

/-! ## Lookup Lemmas -/

/-- Corresponds to `big_andM_lookup` in Rocq Iris. -/
theorem lookup {Φ : K → V → PROP} {m : M V} {k : K} {v : V}
    (h : get? m k = some v) :
    ([∧map] k' ↦ x ∈ m, Φ k' x) ⊢ Φ k v :=
  (delete' h).1.trans and_elim_l

/-- Corresponds to `big_andM_lookup_dom` in Rocq Iris. -/
theorem lookup_dom {Φ : K → PROP} {m : M V} {k : K} {v : V}
    (h : get? m k = some v) :
    bigAndM (fun k' _ => Φ k') m ⊢ Φ k :=
  lookup (Φ := fun k' _ => Φ k') h

/-- Corresponds to `big_andM_insert_2` in Rocq Iris. -/
theorem insert_2 {Φ : K → V → PROP} {m : M V} {k : K} {v : V} :
    Φ k v ∧ ([∧map] k' ↦ x ∈ m, Φ k' x) ⊢ [∧map] k' ↦ x ∈ FiniteMap.insert m k v, Φ k' x := by
  cases hm : get? m k with
  | none =>
    exact (insert hm).2
  | some y =>
    have hdel := delete' (Φ := Φ) (m := m) hm
    refine (and_mono_r (hdel.1.trans and_elim_r)).trans insert_delete.2

/-! ## Logical Operations -/

omit [DecidableEq K] [FiniteMapLaws K M] in
/-- Corresponds to `big_andM_and` in Rocq Iris. -/
theorem and' {Φ Ψ : K → V → PROP} {m : M V} :
    ([∧map] k ↦ x ∈ m, Φ k x ∧ Ψ k x) ⊣⊢
      ([∧map] k ↦ x ∈ m, Φ k x) ∧ [∧map] k ↦ x ∈ m, Ψ k x := by
  simp only [bigAndM]
  exact equiv_iff.mp (BigOpL.op_distr _ _ _)

omit [DecidableEq K] [FiniteMapLaws K M] in
/-- Corresponds to `big_andM_persistently` in Rocq Iris. -/
theorem persistently {Φ : K → V → PROP} {m : M V} :
    iprop(<pers> [∧map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∧map] k ↦ x ∈ m, <pers> Φ k x := by
  simp only [bigAndM]
  exact equiv_iff.mp <| BigOpL.commute bi_persistently_and_homomorphism _ (toList m)

/-! ## Map Conversion -/

omit [DecidableEq K] [FiniteMapLaws K M] in
/-- Corresponds to `big_andM_map_to_list` (implicit in Rocq Iris). -/
theorem map_to_list {Φ : K → V → PROP} {m : M V} :
    ([∧map] k ↦ x ∈ m, Φ k x) ⊣⊢ ([∧list] kv ∈ toList m, Φ kv.1 kv.2) := by
  simp only [bigAndM]
  exact .rfl

/-! ## Map Transformations -/

section MapTransformations

variable {V' : Type _}
variable [DecidableEq V']

/-- Corresponds to `big_andM_fmap` in Rocq Iris. -/
theorem fmap {Φ : K → V' → PROP} {m : M V} (f : V → V') :
    ([∧map] k ↦ y ∈ FiniteMap.map f m, Φ k y) ⊣⊢
      [∧map] k ↦ y ∈ m, Φ k (f y) := by
  simp only [bigAndM]
  refine equiv_iff.mp (BigOpL.perm _ (FiniteMapLaws.toList_map (K := K) m f)) |>.trans ?_
  induction (toList m) with
  | nil => exact .rfl
  | cons kv kvs ih =>
    simp only [List.map, bigOpL]
    exact ⟨and_mono_r ih.1, and_mono_r ih.2⟩

end MapTransformations

section FilterMapTransformations

omit [DecidableEq K] [FiniteMapLaws K M] in
/-- Helper lemma for omap: bigOpL over filterMapped list. -/
private theorem omap_list_aux {Φ : K → V → PROP} (f : V → Option V) (l : List (K × V)) :
    bigOpL and iprop(True) (fun _ kv => Φ kv.1 kv.2)
      (l.filterMap (fun kv => (f kv.2).map (kv.1, ·))) ⊣⊢
    bigOpL and iprop(True) (fun _ kv => match f kv.2 with | some y' => Φ kv.1 y' | none => iprop(True)) l := by
  induction l with
  | nil => simp only [List.filterMap, bigOpL]; exact .rfl
  | cons kv kvs ih =>
    simp only [List.filterMap, Option.map]
    cases hf : f kv.2 with
    | none =>
      simp only [bigOpL, hf]
      have true_and : ∀ (X : PROP), iprop(True) ∧ X ⊣⊢ X := fun X =>
        ⟨and_elim_r, and_intro true_intro .rfl⟩
      exact ih.trans (true_and _).symm
    | some y' =>
      simp only [bigOpL, hf]
      exact ⟨and_mono_r ih.1, and_mono_r ih.2⟩

/-- Corresponds to `big_andM_omap` in Rocq Iris. -/
theorem omap [FiniteMapLawsSelf K M] {Φ : K → V → PROP} {m : M V} (f : V → Option V) :
    ([∧map] k ↦ y ∈ FiniteMap.filterMap (M := M) f m, Φ k y) ⊣⊢
      [∧map] k ↦ y ∈ m, match f y with | some y' => Φ k y' | none => iprop(True) := by
  simp only [bigAndM]
  exact equiv_iff.mp (BigOpL.perm _ (toList_filterMap (K := K) m f)) |>.trans
    (omap_list_aux f (toList m))

/-- Corresponds to `big_andM_union` in Rocq Iris. -/
theorem union [FiniteMapLawsSelf K M] {Φ : K → V → PROP} {m₁ m₂ : M V}
    (hdisj : m₁ ##ₘ m₂) :
    ([∧map] k ↦ y ∈ m₁ ∪ m₂, Φ k y) ⊣⊢
      ([∧map] k ↦ y ∈ m₁, Φ k y) ∧ [∧map] k ↦ y ∈ m₂, Φ k y := by
    sorry

end FilterMapTransformations

/-! ## Intro and Forall Lemmas -/

/-- Corresponds to `big_andM_intro` in Rocq Iris. -/
theorem intro {P : PROP} {Φ : K → V → PROP} {m : M V}
    (h : ∀ k v, get? m k = some v → P ⊢ Φ k v) :
    P ⊢ [∧map] k ↦ x ∈ m, Φ k x := by
  simp only [bigAndM]
  generalize hl : toList m = l
  induction l generalizing m with
  | nil => exact true_intro
  | cons kv kvs ih =>
    simp only [bigOpL]
    have hmem_kv : kv ∈ toList m := hl ▸ List.mem_cons_self
    have hget_kv := (FiniteMapLaws.elem_of_map_to_list m kv.1 kv.2).mp hmem_kv
    refine and_intro (h kv.1 kv.2 hget_kv) ?_
    have htail : ∀ kv', kv' ∈ kvs → get? m kv'.1 = some kv'.2 := fun kv' hmem =>
      (FiniteMapLaws.elem_of_map_to_list m kv'.1 kv'.2).mp (hl ▸ List.mem_cons_of_mem _ hmem)
    clear ih hmem_kv hget_kv hl
    induction kvs with
    | nil => exact true_intro
    | cons kv' kvs' ih' =>
      simp only [bigOpL]
      refine and_intro (h kv'.1 kv'.2 (htail kv' List.mem_cons_self)) ?_
      exact ih' fun kv'' hmem => htail kv'' (List.mem_cons_of_mem _ hmem)

/-- Corresponds to `big_andM_forall` in Rocq Iris. -/
theorem forall' {Φ : K → V → PROP} {m : M V} :
    ([∧map] k ↦ x ∈ m, Φ k x) ⊣⊢ ∀ k, ∀ v, iprop(⌜get? m k = some v⌝ → Φ k v) := by
  constructor
  · refine forall_intro fun k => forall_intro fun v => imp_intro' <| pure_elim_l fun hget => ?_
    exact lookup hget
  · exact intro fun k v hget =>
      (forall_elim k).trans (forall_elim v) |>.trans <|
      (and_intro (pure_intro hget) .rfl).trans imp_elim_r

/-- Corresponds to `big_andM_impl` in Rocq Iris. -/
theorem impl {Φ Ψ : K → V → PROP} {m : M V} :
    ([∧map] k ↦ x ∈ m, Φ k x) ∧ (∀ k v, iprop(⌜get? m k = some v⌝ → Φ k v → Ψ k v)) ⊢
      [∧map] k ↦ x ∈ m, Ψ k x := by
  refine intro fun k v hget => ?_
  refine (and_mono (lookup hget) ((forall_elim k).trans (forall_elim v))).trans ?_
  refine (and_mono .rfl ((and_intro (pure_intro hget) .rfl).trans imp_elim_r)).trans imp_elim_r

/-- Corresponds to `big_andM_subseteq` in Rocq Iris. -/
theorem subseteq {Φ : K → V → PROP} {m₁ m₂ : M V}
    (hsub : m₂ ⊆ m₁) :
    ([∧map] k ↦ x ∈ m₁, Φ k x) ⊢ [∧map] k ↦ x ∈ m₂, Φ k x :=
  intro fun k v hget₂ => lookup (hsub k v hget₂)

/-! ## Pure Lemmas -/

/-- Corresponds to `big_andM_pure_1` in Rocq Iris. -/
theorem pure_1 {φ : K → V → Prop} {m : M V} :
    ([∧map] k ↦ x ∈ m, ⌜φ k x⌝) ⊢ (⌜FiniteMap.map_Forall φ m⌝ : PROP) := by
  simp only [bigAndM, FiniteMap.map_Forall]
  suffices h : ∀ l : List (K × V),
      bigOpL and iprop(True) (fun _ (kv : K × V) => iprop(⌜φ kv.1 kv.2⌝)) l ⊢
        iprop(⌜∀ kv, kv ∈ l → φ kv.1 kv.2⌝) by
    refine (h (toList m)).trans <| pure_mono fun hlist k v hget => ?_
    have hmem : (k, v) ∈ toList m := (FiniteMapLaws.elem_of_map_to_list m k v).mpr hget
    exact hlist (k, v) hmem
  intro l
  induction l with
  | nil =>
    simp only [bigOpL]
    exact pure_intro fun _ h => nomatch h
  | cons kv kvs ih =>
    simp only [bigOpL]
    refine (and_mono_r ih).trans <| pure_and.1.trans <| pure_mono ?_
    intro ⟨hkv, hkvs⟩ kv' hmem
    cases hmem with
    | head => exact hkv
    | tail _ htail => exact hkvs kv' htail

/-- Corresponds to `big_andM_pure_2` in Rocq Iris. -/
theorem pure_2 {φ : K → V → Prop} {m : M V} :
    (⌜FiniteMap.map_Forall φ m⌝ : PROP) ⊢ ([∧map] k ↦ x ∈ m, ⌜φ k x⌝) := by
  simp only [bigAndM, FiniteMap.map_Forall]
  suffices h : ∀ l : List (K × V),
      iprop(⌜∀ kv, kv ∈ l → φ kv.1 kv.2⌝) ⊢
        bigOpL and iprop(True) (fun _ (kv : K × V) => iprop(⌜φ kv.1 kv.2⌝)) l by
    refine (pure_mono fun hmap kv hmem => ?_).trans (h (toList m))
    have hget : get? m kv.1 = some kv.2 := (FiniteMapLaws.elem_of_map_to_list m kv.1 kv.2).mp hmem
    exact hmap kv.1 kv.2 hget
  intro l
  induction l with
  | nil =>
    simp only [bigOpL]
    exact true_intro
  | cons kv kvs ih =>
    simp only [bigOpL]
    refine (pure_mono fun h =>
      ⟨h kv List.mem_cons_self, fun kv' hmem => h kv' (List.mem_cons_of_mem _ hmem)⟩).trans <|
      pure_and.2.trans (and_mono_r ih)

/-- Corresponds to `big_andM_pure` in Rocq Iris. -/
theorem pure' {φ : K → V → Prop} {m : M V} :
    ([∧map] k ↦ x ∈ m, ⌜φ k x⌝) ⊣⊢ (⌜FiniteMap.map_Forall φ m⌝ : PROP) :=
  ⟨pure_1, pure_2⟩

/-! ## Later Lemmas -/

omit [DecidableEq K] [FiniteMapLaws K M] in
/-- Corresponds to `big_andM_later` in Rocq Iris. -/
theorem later {Φ : K → V → PROP} {m : M V} :
    iprop(▷ [∧map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∧map] k ↦ x ∈ m, ▷ Φ k x := by
  simp only [bigAndM]
  exact equiv_iff.mp <| BigOpL.commute bi_later_and_homomorphism _ (toList m)

omit [DecidableEq K] [FiniteMapLaws K M] in
/-- Corresponds to `big_andM_laterN` in Rocq Iris. -/
theorem laterN {Φ : K → V → PROP} {m : M V} {n : Nat} :
    iprop(▷^[n] [∧map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∧map] k ↦ x ∈ m, ▷^[n] Φ k x := by
  induction n with
  | zero => exact .rfl
  | succ k ih => exact (later_congr ih).trans later

/-! ## Filter Lemmas -/

variable [FiniteMapLawsSelf K M]

omit [DecidableEq K] in
/-- Helper: bigOpL over filtered list. -/
private theorem filter_list_aux {Φ : K × V → PROP} (p : K × V → Bool) (l : List (K × V)) :
    bigOpL and iprop(True) (fun _ kv => Φ kv) (l.filter p) ⊣⊢
    bigOpL and iprop(True) (fun _ kv => if p kv then Φ kv else iprop(True)) l := by
  induction l with
  | nil => simp only [List.filter, bigOpL]; exact .rfl
  | cons kv kvs ih =>
    simp only [List.filter]
    cases hp : p kv with
    | false =>
      simp only [bigOpL, hp]
      have true_and : ∀ (X : PROP), iprop(True) ∧ X ⊣⊢ X := fun X =>
        ⟨and_elim_r, and_intro true_intro .rfl⟩
      exact ih.trans (true_and _).symm
    | true =>
      simp only [bigOpL, hp, ↓reduceIte]
      exact ⟨and_mono_r ih.1, and_mono_r ih.2⟩

/-- Corresponds to `big_andM_filter'` in Rocq Iris. -/
theorem filter' {Φ : K → V → PROP} {m : M V} (p : K → V → Bool) :
    ([∧map] k ↦ x ∈ FiniteMap.filter p m, Φ k x) ⊣⊢
      [∧map] k ↦ x ∈ m, if p k x then Φ k x else iprop(True) := by
  simp only [bigAndM]
  have hperm := toList_filter m p
  have heq : bigOpL and iprop(True) (fun _ kv => Φ kv.1 kv.2) (toList (FiniteMap.filter p m)) ≡
             bigOpL and iprop(True) (fun _ kv => Φ kv.1 kv.2) ((toList m).filter (fun kv => p kv.1 kv.2)) :=
    BigOpL.perm _ hperm
  refine equiv_iff.mp heq |>.trans ?_
  exact filter_list_aux (fun kv => p kv.1 kv.2) (toList m)

/-- Corresponds to `big_andM_filter` in Rocq Iris. -/
theorem filter'' {Φ : K → V → PROP} {m : M V} (p : K → V → Bool) :
    ([∧map] k ↦ x ∈ FiniteMap.filter p m, Φ k x) ⊣⊢
      [∧map] k ↦ x ∈ m, iprop(⌜p k x = true⌝ → Φ k x) := by
  have heq : ([∧map] k ↦ x ∈ m, if p k x then Φ k x else iprop(True)) ⊣⊢
      [∧map] k ↦ x ∈ m, iprop(⌜p k x = true⌝ → Φ k x) := by
    apply equiv_iff.mp
    apply proper
    intro k v _
    cases hp : p k v with
    | false =>
      simp only [↓reduceIte, Bool.false_eq_true]
      refine equiv_iff.mpr ⟨?_, true_intro⟩
      refine imp_intro' <| pure_elim_l fun h => ?_
      simp at h
    | true =>
      simp only [↓reduceIte]
      exact equiv_iff.mpr true_imp.symm
  exact (filter' p).trans heq

/-! ## Key Transformation Lemmas -/

section KeyTransformations

variable {M' : Type _ → Type _} {K' : Type _}
variable [DecidableEq K']
variable [FiniteMap K' M']
variable [FiniteMapLaws K' M']
variable [FiniteMapKmapLaws K K' M M']

omit [FiniteMapLawsSelf K M] in
/-- Corresponds to `big_andM_kmap` in Rocq Iris. -/
theorem kmap {Φ : K' → V → PROP} {m : M V} (f : K → K') (hinj : ∀ {x y}, f x = f y → x = y) :
    ([∧map] k' ↦ y ∈ FiniteMap.kmap (M' := M') f m, Φ k' y) ⊣⊢
      [∧map] k ↦ y ∈ m, Φ (f k) y := by
  simp only [bigAndM]
  refine equiv_iff.mp (BigOpL.perm _ (toList_kmap f m hinj)) |>.trans ?_
  induction (toList m) with
  | nil => exact .rfl
  | cons kv kvs ih =>
    simp only [List.map, bigOpL]
    exact ⟨and_mono_r ih.1, and_mono_r ih.2⟩

end KeyTransformations

/-! ## List to Map Conversion Lemmas -/

section ListToMap

variable [FiniteMap Nat M]
variable [FiniteMapLaws Nat M]
variable [FiniteMapSeqLaws M]

/-- Corresponds to `big_andM_map_seq` in Rocq Iris. -/
theorem map_seq {Φ : Nat → V → PROP} (start : Nat) (l : List V) :
    ([∧map] k ↦ x ∈ (FiniteMap.map_seq start l : M V), Φ k x) ⊣⊢
      ([∧list] i ↦ x ∈ l, Φ (start + i) x) := by
  simp only [bigAndM, bigAndL]
  have h1 : bigOpL and iprop(True) (fun _ kv => Φ kv.fst kv.snd) (toList (FiniteMap.map_seq start l : M V)) ≡
            bigOpL and iprop(True) (fun _ kv => Φ kv.fst kv.snd) ((List.range' start l.length).zip l) :=
    BigOpL.perm (fun kv => Φ kv.fst kv.snd) (toList_map_seq (M := M) start l)
  have h2 : bigOpL and iprop(True) (fun _ kv => Φ kv.fst kv.snd) ((List.range' start l.length).zip l) ≡
            bigOpL and iprop(True) (fun i x => Φ (start + i) x) l :=
    BigOpL.zip_seq (fun p => Φ p.1 p.2) start l
  exact equiv_iff.mp (h1.trans h2)

end ListToMap

/-! ## Missing Lemmas from Rocq Iris

The following lemmas from Rocq Iris are not yet fully ported:
- `big_andM_fn_insert*`
- `big_andM_timeless*`: Requires and_timeless infrastructure
-/

end BigAndM

end Iris.BI
