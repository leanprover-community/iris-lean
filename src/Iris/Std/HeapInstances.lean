/-
Copyright (c) 2025 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh, Markus de Medeiros
-/

import Iris.Std.Heap
import Std.Data.TreeMap
import Std.Data.ExtTreeMap

/-!
# Heap Instances for Standard Types

This file provides a library of `Store`, `Heap`, `AllocHeap`, and `UnboundedHeap`
instances for types from the Lean standard library.

## Instances
- Plain functions: `Store`, `IsoFunStore`
- Functions into `Option`: `Heap`


## Constraints

The TreeMap/ExtTreeMap instances require `LawfulEqCmp cmp`, which states that
`cmp k k' = .eq → k = k'`. This is necessary because TreeMap only guarantees
key uniqueness up to the comparator—without this constraint, we couldn't prove
`get (set t k v) k = v` since the stored key might differ from `k`.

-/

namespace Iris.Std

/-! ## Function Store Instance -/

section FunStore

variable {K V : Type _} [DecidableEq K]

/-- Functions form a total store. -/
instance instStoreFun : Store (K → V) K V where
  get t k := t k
  set t k v := fun k' => if k = k' then v else t k'
  get_set_eq {t k k' v} h := by grind
  get_set_ne {t k k' v} h := by grind

/-- Functions represent all functions (trivially). -/
instance instRepFunStoreFun : RepFunStore (K → V) K V where
  rep _ := True
  rep_get _ := trivial
  of_fun f := f.val
  get_of_fun := rfl

/-- Functions are isomorphic to themselves. -/
instance instIsoFunStoreFun : IsoFunStore (K → V) K V where
  of_fun_get := rfl

end FunStore

/-! ## Functions into Option Heap Instance -/

section FunHeap

variable {K V : Type _} [DecidableEq K]

/-- Functions to Option form a heap. -/
instance instHeapFun : Heap (K → Option V) K V where
  empty := fun _ => none
  hmap f t k := (t k).bind (f k)
  merge op t1 t2 k := Option.merge op (t1 k) (t2 k)
  get_empty := rfl
  get_hmap := rfl
  get_merge := rfl

end FunHeap

end Iris.Std


/-! ## TreeMap Heap Instance -/

/-- Merge an optional value with an optional key-value pair, using the pair's key in the merge
function. This is an internal helper for TreeMap heap proofs. -/
private def Option.mergeWithPair (f : K → V → V → V) : Option V → Option (K × V) → Option V
  | some v1, some kv2 => some (f kv2.1 v1 kv2.2)
  | some v1, none => some v1
  | none, some kv2 => some kv2.2
  | none, none => none

@[simp] private theorem Option.mergeWithPair_none_right {f : K → V → V → V} {o1 : Option V} :
    Option.mergeWithPair f o1 none = o1 := by cases o1 <;> rfl

@[simp] private theorem Option.mergeWithPair_some_right {f : K → V → V → V} {o1 : Option V}
    {k : K} {v : V} :
    Option.mergeWithPair f o1 (some (k, v)) = Option.merge (f k) o1 (some v) := by cases o1 <;> rfl

/-- Insert a value if none, or merge with existing value. Used in alter operations for maps.
This is `Option.merge f o (some v)` - inserting `v` when empty, or merging with existing. -/
def Option.insertOrMerge (f : V → V → V) (v : V) (o : Option V) : Option V :=
  Option.merge f o (some v)

@[simp] theorem Option.insertOrMerge_none (f : V → V → V) (v : V) :
    Option.insertOrMerge f v none = some v := rfl

@[simp] theorem Option.insertOrMerge_some (f : V → V → V) (v v' : V) :
    Option.insertOrMerge f v (some v') = some (f v' v) := rfl

namespace Std.TreeMap

section HeapInstance

variable {K V : Type _} {cmp : K → K → Ordering} [TransCmp cmp]

/-- TreeMap forms a Store with Option values.

Note: This requires that `cmp k k' = .eq` implies `k = k'` (i.e., `LawfulEqCmp`).
-/
instance instStore [LawfulEqCmp cmp] : Store (TreeMap K V cmp) K (Option V) where
  get t k := t[k]?
  set t k v := t.alter k (fun _ => v)
  get_set_eq {t k k' v} h := by grind
  get_set_ne {t k k' v} h := by simp [getElem?_alter]; grind

open Std.DTreeMap.Internal in
private theorem get?_foldl_alter_impl_sigma [inst : Ord K] [TransOrd K]
    {l : List ((a : K) × (fun _ => V) a)}
    {init : Impl K (fun _ => V)} {f : K → V → V → V} {k : K}
    (hinit : init.WF)
    (hl : l.Pairwise (fun a b => compare a.1 b.1 ≠ .eq)) :
    Impl.Const.get? (l.foldl (fun acc kv =>
        Impl.Const.alter! kv.1 (Option.insertOrMerge (f kv.1) kv.2) acc) init) k =
      Option.mergeWithPair f (Impl.Const.get? init k)
        ((l.find? (fun kv => compare kv.1 k == .eq)).map (fun kv => (kv.1, kv.2))) := by
  induction l generalizing init with
  | nil =>
    simp only [List.foldl_nil, List.find?_nil, Option.map_none]
    cases Impl.Const.get? init k <;> rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    let alterFn := Option.insertOrMerge (f hd.1) hd.2
    have hwf_new : (Impl.Const.alter! hd.1 alterFn init).WF :=
      Impl.WF.constAlter! (f := alterFn) hinit
    rw [ih hwf_new (hl.tail)]
    by_cases heq : compare hd.1 k = .eq
    · rw [Impl.Const.get?_alter! hinit]
      simp only [heq, ↓reduceIte, List.find?_cons, beq_self_eq_true, Option.map_some]
      have htl : tl.find? (fun kv => compare kv.1 k == .eq) = none := List.find?_eq_none.mpr fun kv hkv hkv_eq => by
        simp only [beq_iff_eq] at hkv_eq
        exact List.rel_of_pairwise_cons hl hkv (TransCmp.eq_trans heq (OrientedCmp.eq_symm hkv_eq))
      rw [htl, ← Impl.Const.get?_congr hinit heq]
      cases Impl.Const.get? init hd.1 <;> simp [alterFn, Option.mergeWithPair]
    · rw [Impl.Const.get?_alter! hinit]; simp [heq]

/-- foldl over list with alter gives getElem? in terms of mergeWithPair. -/
private theorem getElem?_foldl_alter {l : List (K × V)} {init : TreeMap K V cmp} {f : K → V → V → V}
    {k : K} (hl : l.Pairwise (fun a b => cmp a.1 b.1 ≠ .eq)) :
    (l.foldl (fun acc kv => acc.alter kv.1 (Option.insertOrMerge (f kv.1) kv.2)) init)[k]? =
      Option.mergeWithPair f init[k]? (l.find? (fun kv => cmp kv.1 k == .eq)) := by
  induction l generalizing init with
  | nil => simp only [List.foldl_nil, List.find?_nil]; cases init[k]? <;> rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih (hl.tail)]
    by_cases heq : cmp hd.1 k = .eq
    · simp only [getElem?_alter, getElem?_congr (OrientedCmp.eq_symm heq), List.find?_cons, heq,
          beq_self_eq_true]
      have htl : tl.find? (fun kv => cmp kv.1 k == .eq) = none := List.find?_eq_none.mpr fun kv hkv h => by
        simp only [beq_iff_eq] at h
        exact List.rel_of_pairwise_cons hl hkv (TransCmp.eq_trans heq (OrientedCmp.eq_symm h))
      simp only [htl, ReflCmp.compare_self, ↓reduceIte]
      cases init[hd.1]? <;> rfl
    · simp [getElem?_alter, heq]

/-- TreeMap.mergeWith equals list foldl with alter at the getElem? level. -/
private theorem getElem?_mergeWith_eq_foldl [LawfulEqCmp cmp] {t₁ t₂ : TreeMap K V cmp}
    {f : K → V → V → V} {k : K} :
    (t₁.mergeWith f t₂)[k]? = (t₂.toList.foldl (fun acc kv =>
        acc.alter kv.1 (Option.insertOrMerge (f kv.1) kv.2)) t₁)[k]? := by
  rw [getElem?_foldl_alter (distinct_keys_toList (t := t₂))]
  letI : Ord K := ⟨cmp⟩
  -- Unfold mergeWith to internal representation
  have h_impl : (t₁.mergeWith f t₂)[k]? =
      Std.DTreeMap.Internal.Impl.Const.get?
        (Std.DTreeMap.Internal.Impl.Const.mergeWith! f t₁.inner.inner t₂.inner.inner) k :=
    congrArg (Std.DTreeMap.Internal.Impl.Const.get? · k)
      (Std.DTreeMap.Internal.Impl.Const.mergeWith_eq_mergeWith! ..)
  -- mergeWith! is definitionally foldl
  have h_foldl : Std.DTreeMap.Internal.Impl.Const.mergeWith! f t₁.inner.inner t₂.inner.inner =
      Std.DTreeMap.Internal.Impl.foldl (fun t a b₂ =>
        Std.DTreeMap.Internal.Impl.Const.alter! a (fun
          | none => some b₂
          | some b₁ => some (f a b₁ b₂)) t) t₁.inner.inner t₂.inner.inner := rfl
  -- Convert internal foldl to list foldl on toListModel
  have h_list : Std.DTreeMap.Internal.Impl.foldl (fun t a b₂ =>
        Std.DTreeMap.Internal.Impl.Const.alter! a (fun
          | none => some b₂
          | some b₁ => some (f a b₁ b₂)) t) t₁.inner.inner t₂.inner.inner =
      t₂.inner.inner.toListModel.foldl (fun acc p =>
        Std.DTreeMap.Internal.Impl.Const.alter! p.1 (Option.insertOrMerge (f p.1) p.2) acc)
        t₁.inner.inner := by
    have heq : (fun t a b₂ => Std.DTreeMap.Internal.Impl.Const.alter! a
        (fun | none => some b₂ | some b₁ => some (f a b₁ b₂)) t) =
        (fun t a b₂ => Std.DTreeMap.Internal.Impl.Const.alter! a (Option.insertOrMerge (f a) b₂) t) := by
      funext t a b₂; congr 1; funext o; cases o <;> rfl
    rw [heq, Std.DTreeMap.Internal.Impl.foldl_eq_foldl]
  -- Keys in toListModel are pairwise distinct
  have hdist : t₂.inner.inner.toListModel.Pairwise (fun a b => compare a.1 b.1 ≠ .eq) :=
    (List.pairwise_map.mp <|
      Std.DTreeMap.Internal.Impl.SameKeys.ordered_iff_pairwise_keys.mp t₂.inner.wf.ordered).imp
      fun hlt heq => nomatch heq ▸ hlt
  -- Connect t₁[k]? with internal get?
  have h_get_eq : t₁[k]? = Std.DTreeMap.Internal.Impl.Const.get? t₁.inner.inner k := rfl
  rw [h_impl, h_foldl, h_list, get?_foldl_alter_impl_sigma t₁.inner.wf hdist, h_get_eq]
  -- Convert sigma-typed toListModel to product-typed toList
  have h_toList : t₂.toList = t₂.inner.inner.toListModel.map (fun e => (e.1, e.2)) :=
    Std.DTreeMap.Internal.Impl.Const.toList_eq_toListModel_map
  have h_find : ∀ l : List ((a : K) × (fun _ => V) a),
      (l.map (fun e => (e.1, e.2))).find? (fun kv => cmp kv.1 k == .eq) =
      (l.find? (fun kv => cmp kv.1 k == .eq)).map (fun e => (e.1, e.2)) := fun l => by
    induction l with
    | nil => rfl
    | cons _ _ ih => simp only [List.map_cons, List.find?_cons]; split <;> grind
  have hfind_eq := h_find t₂.inner.inner.toListModel
  rw [← h_toList] at hfind_eq
  cases hres : t₂.inner.inner.toListModel.find? (fun kv => cmp kv.1 k == .eq) <;>
    simp only [hfind_eq, hres, Option.map_none, Option.map_some]

/-- If `k` is not in the map, `find?` on `toList` returns `none`. -/
private theorem find?_eq_none_of_getElem?_eq_none [LawfulEqCmp cmp] {t : TreeMap K V cmp} {k : K}
    (h : t[k]? = none) : t.toList.find? (fun kv => cmp kv.1 k == .eq) = none := by
  apply List.find?_eq_none.mpr; intro kv hkv heq; simp only [beq_iff_eq] at heq
  exact absurd (getElem?_eq_some_iff_exists_compare_eq_eq_and_mem_toList.mpr
    ⟨kv.1, OrientedCmp.eq_symm heq, hkv⟩) (by simp [h])

/-- If `k` is in the map with value `v`, `find?` returns `some (k', v)` where `k' = k`. -/
private theorem find?_eq_some_of_getElem?_eq_some [LawfulEqCmp cmp] {t : TreeMap K V cmp}
    {k : K} {v : V} (h : t[k]? = some v) :
    ∃ k', t.toList.find? (fun kv => cmp kv.1 k == .eq) = some (k', v) ∧ k' = k := by
  obtain ⟨k', hcmp, hmem⟩ := getElem?_eq_some_iff_exists_compare_eq_eq_and_mem_toList.mp h
  have hpred : (fun kv : K × V => cmp kv.1 k == .eq) (k', v) = true := by
    simp [OrientedCmp.eq_symm hcmp]
  have hisSome := List.find?_isSome (p := fun kv => cmp kv.1 k == .eq) |>.mpr ⟨(k', v), hmem, hpred⟩
  obtain ⟨kv, hfind⟩ := Option.isSome_iff_exists.mp hisSome
  have hkv_cmp : cmp kv.1 k = .eq := by simpa [beq_iff_eq] using List.find?_some hfind
  have hval : kv.2 = v := by
    have := getElem?_eq_some_iff_exists_compare_eq_eq_and_mem_toList.mpr
      ⟨kv.1, OrientedCmp.eq_symm hkv_cmp, List.mem_of_find?_eq_some hfind⟩
    grind
  refine ⟨kv.1, ?_, LawfulEqCmp.eq_of_compare hkv_cmp⟩
  simp only [hfind, ← hval, Prod.eta]

/-- Convert `mergeWithPair` applied to a `find?` result into `Option.merge` with `getElem?`. -/
private theorem mergeWithPair_find?_eq_merge [LawfulEqCmp cmp] {t : TreeMap K V cmp}
    {k : K} {o : Option V} {f : K → V → V → V} :
    Option.mergeWithPair f o (t.toList.find? (fun kv => cmp kv.1 k == .eq)) =
      Option.merge (f k) o t[k]? := by
  cases h : t[k]? with
  | none => simp [find?_eq_none_of_getElem?_eq_none h]
  | some v =>
    obtain ⟨k', hfind, hk'⟩ := find?_eq_some_of_getElem?_eq_some h
    simp [hfind, hk']

/-- `getElem?` of `mergeWith` combines values using `Option.merge`. -/
@[simp] theorem getElem?_mergeWith' [LawfulEqCmp cmp] {t₁ t₂ : TreeMap K V cmp}
    {f : K → V → V → V} {k : K} :
    (t₁.mergeWith f t₂)[k]? = Option.merge (f k) t₁[k]? t₂[k]? := by
  rw [getElem?_mergeWith_eq_foldl, getElem?_foldl_alter (distinct_keys_toList (t := t₂)),
      mergeWithPair_find?_eq_merge]

/-- TreeMap forms a Heap. -/
instance instHeap [LawfulEqCmp cmp] : Heap (TreeMap K V cmp) K V where
  empty := {}
  hmap f t := t.filterMap f
  merge op t1 t2 := t1.mergeWith (fun _ v1 v2 => op v1 v2) t2
  get_empty := rfl
  get_hmap {f t k} := by
    show (filterMap f t)[k]? = t[k]?.bind (f k); simp [getElem?_filterMap, Option.pbind_eq_bind, getKey_eq]
  get_merge := getElem?_mergeWith'

end HeapInstance

end Std.TreeMap

/-! ## ExtTreeMap Heap Instance -/

namespace Std.ExtTreeMap

section HeapInstance

variable {K V : Type _} {cmp : K → K → Ordering}

variable [TransCmp cmp]

/-- ExtTreeMap forms a Store with Option values.

Note: This requires that `cmp k k' = .eq` implies `k = k'` (i.e., `LawfulEqCmp`).
-/
instance instStore [LawfulEqCmp cmp] : Store (ExtTreeMap K V cmp) K (Option V) where
  get t k := t[k]?
  set t k v := t.alter k (fun _ => v)
  get_set_eq {t k k' v} h := by grind
  get_set_ne {t k k' v} h := by simp [getElem?_alter]; grind

/-- getElem? of mergeWith has the expected semantics for ExtTreeMap.

The proof uses quotient induction to reduce to DTreeMap representatives,
then reuses the TreeMap proof since both share the same internal implementation. -/
@[simp] theorem getElem?_mergeWith' [LawfulEqCmp cmp] {t₁ t₂ : ExtTreeMap K V cmp}
    {f : K → V → V → V} {k : K} :
    (t₁.mergeWith f t₂)[k]? = Option.merge (f k) t₁[k]? t₂[k]? := by
  show ExtDTreeMap.Const.get? (ExtDTreeMap.Const.mergeWith f t₁.inner t₂.inner) k =
    Option.merge (f k) (ExtDTreeMap.Const.get? t₁.inner k) (ExtDTreeMap.Const.get? t₂.inner k)
  obtain ⟨q₁⟩ := t₁.inner
  obtain ⟨q₂⟩ := t₂.inner
  induction q₁ using Quotient.ind with
  | _ m₁ => induction q₂ using Quotient.ind with
    | _ m₂ => exact Std.TreeMap.getElem?_mergeWith' (t₁ := ⟨m₁⟩) (t₂ := ⟨m₂⟩) (f := f) (k := k)

/-- ExtTreeMap forms a Heap. -/
instance instHeap [LawfulEqCmp cmp] : Heap (ExtTreeMap K V cmp) K V where
  empty := {}
  hmap f t := t.filterMap f
  merge op t1 t2 := t1.mergeWith (fun _ v1 v2 => op v1 v2) t2
  get_empty := rfl
  get_hmap {f t k} := by
    show (filterMap f t)[k]? = t[k]?.bind (f k); simp [getElem?_filterMap, Option.pbind_eq_bind, getKey_eq]
  get_merge := getElem?_mergeWith'

end HeapInstance

end Std.ExtTreeMap
