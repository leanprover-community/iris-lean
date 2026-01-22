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

section Lemmas

/-- Merge an optional value with an optional key-value pair, using the pair's key in the merge
function. This is an internal helper for TreeMap heap proofs. -/
private def Option.pairMerge (f : K → V → V → V) (o1 : Option V) (o2 : Option (K × V)) : Option V :=
  o2.elim o1 fun ⟨k, v2⟩ => some (o1.elim v2 (f k · v2))

@[simp] private theorem Option.pairMerge_none_right {f : K → V → V → V} {o1 : Option V} :
    Option.pairMerge f o1 none = o1 := by
  cases o1 <;> rfl

@[simp] private theorem Option.pairMerge_some_right :
    Option.pairMerge f o1 (some (k, v)) = Option.merge (f k) o1 (some v) := by
  cases o1 <;> rfl

/-- Insert a value if none, or merge with existing value. Used in alter operations for maps.
This is `Option.merge f o (some v)` - inserting `v` when empty, or merging with existing. -/
def Option.insertOrMerge (f : V → V → V) (v : V) (o : Option V) : Option V :=
  merge f o (some v)

@[simp] theorem Option.insertOrMerge_none (f : V → V → V) (v : V) :
  insertOrMerge f v none = some v := rfl

@[simp] theorem Option.insertOrMerge_some (f : V → V → V) (v v' : V) :
  insertOrMerge f v (some v') = some (f v' v) := rfl

end Lemmas

namespace Std.TreeMap

/-! ## TreeMap Heap Instance -/

section HeapInstance


open Option Std.DTreeMap.Internal.Impl List TransCmp OrientedCmp

variable {K V : Type _} {cmp : K → K → Ordering} [TransCmp cmp]

/-- TreeMap forms a Store with Option values.

Note: This requires that `cmp k k' = .eq` implies `k = k'` (i.e., `LawfulEqCmp`).
-/
instance instStore [LawfulEqCmp cmp] : Store (TreeMap K V cmp) K (Option V) where
  get t k := t[k]?
  set t k v := t.alter k (fun _ => v)
  get_set_eq {t k k' v} h := by grind
  get_set_ne {t k k' v} h := by grind

private theorem get?_foldl_alter_impl_sigma [inst : Ord K] [TransOrd K]
    {l : List ((a : K) × (fun _ => V) a)} (hinit : init.WF)
    (hl : l.Pairwise (compare ·.1 ·.1 ≠ .eq)) :
    Const.get? (l.foldl (fun acc ⟨k, v⟩ => Const.alter! k (insertOrMerge (f k) v) acc) init) k =
    Option.pairMerge f (Const.get? init k) ((l.find? (compare ·.1 k == .eq)).map (fun kv => (kv.1, kv.2))) := by
  induction l generalizing init with
  | nil => simp [foldl_nil]
  | cons hd tl IH =>
    simp only [foldl_cons]
    rw [IH (WF.constAlter! hinit) (hl.tail)]
    by_cases h  : compare hd.1 k = .eq
    · have htl : tl.find? (compare ·.1 k == .eq) = none := by
        refine find?_eq_none.mpr fun _ hkv _ => rel_of_pairwise_cons hl hkv ?_
        exact (eq_trans h (eq_symm (by grind)))
      rw [Const.get?_alter! hinit, ← Const.get?_congr hinit h]
      cases _ : Const.get? init hd.1 <;> simp [htl, h]
    · rw [Const.get?_alter! hinit]; simp [h]

/-- foldl over list with alter gives getElem? in terms of mergeWithPair. -/
private theorem getElem?_foldl_alter {l : List (K × V)} {init : TreeMap K V cmp} {f : K → V → V → V}
    {k : K} (hl : l.Pairwise (fun a b => cmp a.1 b.1 ≠ .eq)) :
    (l.foldl (fun acc kv => acc.alter kv.1 (Option.insertOrMerge (f kv.1) kv.2)) init)[k]? =
      Option.pairMerge f init[k]? (l.find? (fun kv => cmp kv.1 k == .eq)) := by
  induction l generalizing init with
  | nil => simp only [List.foldl_nil, List.find?_nil]; cases init[k]? <;> rfl
  | cons hd tl ih =>
    rw [foldl_cons, ih (hl.tail)]
    by_cases heq : cmp hd.1 k = .eq
    · have htl : tl.find? (fun kv => cmp kv.1 k == .eq) = none := List.find?_eq_none.mpr fun kv hkv h => by
        simp only [beq_iff_eq] at h
        exact rel_of_pairwise_cons hl hkv (eq_trans heq (eq_symm h))
      simp only [getElem?_congr (eq_symm heq), getElem?_alter_self, htl,
                 Option.pairMerge_none_right, heq, BEq.rfl, find?_cons_of_pos]
      cases _ : init[hd.1]? <;> rfl
    · simp [getElem?_alter, heq]

open Std.DTreeMap.Internal.Impl Std.DTreeMap.Internal in
/-- TreeMap.mergeWith equals list foldl with alter at the getElem? level. -/
private theorem getElem?_mergeWith_eq_foldl [LawfulEqCmp cmp] {t₁ t₂ : TreeMap K V cmp}
    {f : K → V → V → V} {k : K} :
    (t₁.mergeWith f t₂)[k]? =
    (t₂.toList.foldl (fun acc kv => acc.alter kv.1 (insertOrMerge (f kv.1) kv.2)) t₁)[k]? := by
  rw [getElem?_foldl_alter (distinct_keys_toList (t := t₂))]
  letI : Ord K := ⟨cmp⟩
  have h_impl : (t₁.mergeWith f t₂)[k]? = Const.get? (Const.mergeWith! f t₁.inner.inner t₂.inner.inner) k :=
    congrArg (Const.get? · k) (Const.mergeWith_eq_mergeWith! ..)
  have h_foldl : Const.mergeWith! f t₁.inner.inner t₂.inner.inner =
      .foldl (fun t a b₂ => Const.alter! a (fun | none => some b₂ | some b₁ => some (f a b₁ b₂)) t) t₁.inner.inner t₂.inner.inner := rfl
  have h_list : Std.DTreeMap.Internal.Impl.foldl (fun t a b₂ =>
     Const.alter! a (fun | none => some b₂ | some b₁ => some (f a b₁ b₂)) t) t₁.inner.inner t₂.inner.inner =
     t₂.inner.inner.toListModel.foldl (fun acc p => Const.alter! p.1 (insertOrMerge (f p.1) p.2) acc) t₁.inner.inner := by
    have heq : (fun t a b₂ => Const.alter! a
        (fun | none => some b₂ | some b₁ => some (f a b₁ b₂)) t) =
        (fun t a b₂ => Std.DTreeMap.Internal.Impl.Const.alter! a (Option.insertOrMerge (f a) b₂) t) := by
      funext t a b₂; congr 1; funext o; cases o <;> rfl
    rw [heq, foldl_eq_foldl]
  have hdist : t₂.inner.inner.toListModel.Pairwise (compare ·.1 ·.1 ≠ .eq) :=
    (pairwise_map.mp <| SameKeys.ordered_iff_pairwise_keys.mp t₂.inner.wf.ordered).imp fun hlt heq => nomatch heq ▸ hlt
  have h_get_eq : t₁[k]? = Std.DTreeMap.Internal.Impl.Const.get? t₁.inner.inner k := rfl
  have h_toList : t₂.toList = t₂.inner.inner.toListModel.map (fun e => (e.1, e.2)) := Const.toList_eq_toListModel_map
  have h_find : ∀ l : List ((a : K) × (fun _ => V) a),
      (l.map (fun e => (e.1, e.2))).find? (fun kv => cmp kv.1 k == .eq) =
      (l.find? (fun kv => cmp kv.1 k == .eq)).map (fun e => (e.1, e.2)) := fun l => by
    induction l with grind
  rw [h_impl, h_foldl, h_list]
  rw [get?_foldl_alter_impl_sigma t₁.inner.wf hdist]
  grind

/-- `getElem?` of `mergeWith` combines values using `Option.merge`. -/
@[simp] theorem getElem?_mergeWith' [LawfulEqCmp cmp] {t₁ t₂ : TreeMap K V cmp}
    {f : K → V → V → V} {k : K} :
    (t₁.mergeWith f t₂)[k]? = Option.merge (f k) t₁[k]? t₂[k]? := by
  have X := getElem?_mergeWith_eq_foldl (t₁ := t₁) (t₂ := t₂) (f := f) (k := k)
  rw [X]
  rw [getElem?_foldl_alter (distinct_keys_toList (t := t₂))]
  cases h : t₂[k]? with
  | none =>
    rw [List.find?_eq_none.mpr]; simp
    refine fun ⟨k', v'⟩ hkv' heq => ?_
    have Y :=
      (@getElem?_eq_some_iff_exists_compare_eq_eq_and_mem_toList _ _ cmp t₂ _ k v').mpr ⟨k', ?G, hkv'⟩
    case G =>
      apply beq_iff_eq.mp
      simp_all
    grind
  | some v =>
    obtain ⟨k', hcmp, hmem⟩ := getElem?_eq_some_iff_exists_compare_eq_eq_and_mem_toList.mp h
    have hpred : (fun kv : K × V => (cmp kv.1 k).isEq) (k', v) = true := by simp [eq_symm hcmp]
    have hisSome := List.find?_isSome (p := fun kv => (cmp kv.1 k).isEq) |>.mpr ⟨(k', v), hmem, hpred⟩
    obtain ⟨kv, hfind⟩ := Option.isSome_iff_exists.mp hisSome
    have hkv_cmp : cmp kv.1 k = .eq := by simpa [beq_iff_eq] using List.find?_some hfind
    have hval : kv.2 = v := by grind
    have hfind : find? (fun kv => (cmp kv.fst k).isEq) t₂.toList = some (kv.fst, v) := by
      simp [← hval, ← hfind]
    have hk' := LawfulEqCmp.eq_of_compare hkv_cmp
    suffices H : Option.pairMerge f t₁[k]? (find? (fun kv => (cmp kv.fst k).isEq) t₂.toList) = Option.merge (f k) t₁[k]? (some v) by
      rw [← H]
      congr 2
      funext
      rw [← Ordering.isEq_eq_beq_eq] -- TODO: Can we move away from using beq everywhere?
    simp [hfind, hk']

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
  get_set_ne {t k k' v} h := by grind

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
  merge op t1 t2 := t1.mergeWith (fun _ => op) t2
  get_empty := rfl
  get_hmap {f t k} := by show (filterMap f t)[k]? = t[k]?.bind (f k); grind
  get_merge := getElem?_mergeWith'

end HeapInstance

end Std.ExtTreeMap
