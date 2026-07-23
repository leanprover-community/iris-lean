/-
Copyright (c) 2025 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh, Markus de Medeiros
-/
module

public import Iris.Std.PartialMap
public import Iris.Std.Infinite
public import Std.Data.TreeMap
public import Std.Data.ExtTreeMap

/-!
# Heap Instances for Standard Types

This file provides a library of `PartialMap`, `Heap`, and `UnboundedHeap`
instances for types from the Lean standard library.

## Instances
- Plain functions: `PartialMap`, `IsoFunMap`
- Functions into `Option`: `Heap`
- Classical functions into `Option`: `UnboundedHeap`
- Association lists: `UnboundedHeap`
- `TreeMap`: `PartialMap`
- `ExtTreeMap`: `PartialMap`
-/

@[expose] public section

namespace Iris.Std

/-! ## Function PartialMap Instance -/

section FunPartialMap

variable {K V : Type _} [DecidableEq K]

/-- Functions form a partial map. -/
instance instPartialMapFun : PartialMap (K → Option ·) K where
  get? t k := t k
  insert t k v := fun k' => if k = k' then some v else t k'
  delete t k := fun k' => if k = k' then none else t k'
  empty := fun _ => none
  bindAlter f t k := (t k).bind (f k)
  merge f m1 m2 k :=
    match m1 k, m2 k with
    | none, none => none
    | some x, none => some x
    | none, some y => some y
    | some x, some y => some <| f k x y

instance : LawfulPartialMap (K → Option ·) K where
  get?_empty := fun k => rfl
  get?_insert_eq := by simp [get?, insert]; grind
  get?_insert_ne := by simp [get?, insert]; grind
  get?_delete_eq := by simp [get?, delete]
  get?_delete_ne := by simp [get?, delete]; grind
  get?_bindAlter := by simp [get?, bindAlter]
  get?_merge {_ _ _ _ _} := by simp [get?, merge]; split <;> simp_all
  equiv_iff_eq := ⟨funext, congrFun⟩

end FunPartialMap

/-! ## (Noncomputable) Allocation in an infinite function type -/
noncomputable section ClassicalAllocHeap

open Classical

instance instClassicalAllocHeap : Heap (K → Option ·) K where
  notFull f := infinite <| cosupport f
  fresh := choose ∘ coinfinite_exists_next
  get?_fresh {_ _ H} := choose_spec <| coinfinite_exists_next H

instance instClassicalUnboundedHeap [InfiniteType K] : UnboundedHeap (K → Option ·) K where
  notFull_empty := by
    simp [notFull, infinite, cosupport, PartialMap.empty]
    exact ⟨InfiniteType.enum, fun n m a => InfiniteType.enum_inj n m a⟩
  notFull_insert_fresh {_ t v h} := by
    refine cofinite_alter_cofinite (Hs := h) (p' := fresh h) ?_
    simp [PartialMap.insert]
    grind

end ClassicalAllocHeap

end Iris.Std

namespace Std.TreeMap

/-! ## TreeMap Heap Instance -/

section HeapInstance

open Option Std.DTreeMap.Internal.Impl List TransCmp OrientedCmp LawfulEqCmp Ordering
open Iris.Std

variable {K V : Type _} [Ord K] [TransOrd K] [LawfulEqOrd K]
attribute [local instance low] beqOfOrd

@[simp]
theorem getElem?_mergeWith' {t₁ t₂ : TreeMap K V compare} {f : K → V → V → V} {k : K} :
    (t₁.mergeWith f t₂)[k]? = merge (f k) t₁[k]? t₂[k]? := by
  change Const.get? (Const.mergeWith f t₁.inner.inner t₂.inner.inner
    t₁.inner.wf.balanced).impl k =
    merge (f k) (Const.get? t₁.inner.inner k) (Const.get? t₂.inner.inner k)
  have ht₁ : t₁.inner.inner.WF := t₁.inner.wf
  have ht₂ : t₂.inner.inner.WF := t₂.inner.wf
  have hmerge : (Const.mergeWith f t₁.inner.inner t₂.inner.inner
      t₁.inner.wf.balanced).impl.WF := t₁.inner.wf.constMergeWith
  simp_to_model [Const.mergeWith, Const.get?] using
    Std.Internal.List.Const.getValue?_mergeWith

end HeapInstance

end Std.TreeMap

/-! ## ExtTreeMap Heap Instance -/

namespace Std.ExtTreeMap

section HeapInstance

open Option Std.ExtDTreeMap List TransCmp OrientedCmp LawfulEqCmp Ordering Iris.Std

variable {K V : Type _} [Ord K] [TransOrd K] [LawfulEqOrd K]

/-- ExtTreeMap forms a Store with Option values.

Note: This requires that `cmp k k' = .eq` implies `k = k'` (i.e., `LawfulEqCmp`).
-/

instance : PartialMap (ExtTreeMap K · compare) K where
  get? t k := t[k]?
  insert t k v := t.alter k (fun _ => some v)
  delete t k := t.alter k (fun _ => none)
  empty := ∅
  bindAlter f t := t.filterMap f
  merge op t1 t2 := t1.mergeWith op t2

@[simp]
theorem getElem?_mergeWith' {t₁ t₂ : ExtTreeMap K V compare} :
    (t₁.mergeWith f t₂)[k]? = merge (f k) t₁[k]? t₂[k]? := by
  show
    Const.get? (Const.mergeWith f t₁.inner t₂.inner) k =
    merge (f k) (Const.get? t₁.inner k) (Const.get? t₂.inner k)
  obtain ⟨q₁⟩ := t₁.inner
  obtain ⟨q₂⟩ := t₂.inner
  induction q₁ using Quotient.ind with
  | _ m₁ => induction q₂ using Quotient.ind with
    | _ m₂ => exact Std.TreeMap.getElem?_mergeWith'

instance : LawfulPartialMap (ExtTreeMap K · compare) K where
  get?_empty := by simp [Iris.Std.get?]
  get?_insert_eq := by simp [Iris.Std.get?, Iris.Std.insert]; grind
  get?_insert_ne := by simp [Iris.Std.get?, Iris.Std.insert]; grind
  get?_delete_eq := by simp [Iris.Std.get?, Iris.Std.delete]
  get?_delete_ne := by simp [Iris.Std.get?, Iris.Std.delete]; grind
  get?_bindAlter := by simp [Iris.Std.get?, Iris.Std.bindAlter]
  get?_merge := getElem?_mergeWith'
  equiv_iff_eq {V m₁ m₂} := by rw [ExtTreeMap.ext_getElem?_iff]; rfl

instance : FiniteMap (ExtTreeMap K · compare) K where
  toList t := t.toList

instance : LawfulFiniteMap (ExtTreeMap K · compare) K where
  toList_empty := rfl
  toList_noDupKeys {V m} := by
    suffices h : List.Pairwise (fun a b => ¬compare a b = eq) (m.toList.map (·.1)) by
      refine h.imp (· <| LawfulEqOrd.compare_eq_iff_eq.mpr ·)
    exact List.pairwise_map.mpr distinct_keys_toList
  toList_get {_ m _ _} := m.mem_toList_iff_getElem?_eq_some

end HeapInstance

end Std.ExtTreeMap
