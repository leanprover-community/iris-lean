/-
Copyright (c) 2025 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh, Markus de Medeiros
-/

import Iris.Std.Heap
import Iris.Std.Infinite
import Std.Data.TreeMap
import Std.Data.ExtTreeMap

/-!
# Heap Instances for Standard Types

This file provides a library of `Store`, `Heap`, `AllocHeap`, and `UnboundedHeap`
instances for types from the Lean standard library.

## Instances
- Plain functions: `Store`, `IsoFunStore`
- Functions into `Option`: `Heap`
- Classical functions into `Option`:  `UnboundedHeap`
- Association lists:  `UnboundedHeap`
- `TreeMap`: `Heap`
- `ExtTreeMap`: `Heap`
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

/-! ## (Noncomputable) Allocation in an infinite function type -/
noncomputable section ClassicalAllocHeap

open Classical

instance instClassicalAllocHeap : AllocHeap (K → Option V) K V where
  notFull f := infinite <| cosupport f
  fresh := choose ∘ coinfinite_exists_next
  get_fresh {_ H} := choose_spec <| coinfinite_exists_next H

instance instClassicalUnboundedHeap [InfiniteType K] : UnboundedHeap (K → Option V) K V where
  notFull_empty := by
    simp [notFull, infinite, cosupport, empty]
    exact ⟨InfiniteType.enum, fun n m a => InfiniteType.enum_inj n m a⟩
  notFull_set_fresh {t v H} := by
    refine cofinite_alter_cofinite (Hs := H) (p' := fresh (T := K → Option V) H) ?_
    simp [Store.set]
    grind

end ClassicalAllocHeap

end Iris.Std

section AssociationLists

inductive AssocList (V : Type _)
| empty : AssocList V
| set : Nat → V → AssocList V → AssocList V
| remove : Nat → AssocList V → AssocList V

open AssocList

@[simp]
def AssocList.lookup (f : AssocList V) (k : Nat) : Option V :=
  match f with
  | .empty => none
  | .set n v' rest => if n = k then some v' else rest.lookup k
  | .remove n rest => if n = k then none else rest.lookup k

@[simp]
def AssocList.update (f : AssocList V) (k : Nat) (v : Option V) : AssocList V :=
  match v with
  | some v' => f.set k v'
  | none => f.remove k

@[simp]
def AssocList.map (f : Nat → V → Option V') (g : AssocList V) : AssocList V' :=
  match g with
  | .empty => .empty
  | .set n v rest =>
      match (f n v) with
      | .some r => .set n r (rest.map f)
      | .none => .remove n (rest.map f)
  | .remove n rest => .remove n (rest.map f)

@[simp]
def AssocList.fresh (f : AssocList V) : Nat :=
  match f with
  | .empty => 0
  | .set n _ rest => max (n + 1) rest.fresh
  | .remove n rest => max (n + 1) rest.fresh

@[simp]
def AssocList.construct (f : Nat → Option V) (N : Nat) : AssocList V :=
  match N with
  | .zero => .empty
  | .succ N' =>
      match (f N') with
      | some v => .set N' v (AssocList.construct f N')
      | none => (AssocList.construct f N')

@[simp]
def AssocList.construct_spec (f : Nat → Option V) (N : Nat) : Nat → (Option V) :=
  fun n => if n < N then f n else none

theorem AssocList.lookup_update (f : AssocList V) :
    (f.update k v).lookup = fset (f.lookup) k v := by
  funext k'
  cases f <;> cases v <;> simp [fset]

theorem AssocList.fresh_lookup_ge (f : AssocList V) n :
    f.fresh ≤ n → f.lookup n = none := by
  induction f <;> simp
  case set => split <;> grind
  case remove => grind

theorem AssocList.construct_get (f : Nat → Option V) (N : Nat) :
    lookup (construct f N) = construct_spec f N := by
  funext k
  rcases Nat.lt_or_ge k N with HL | HG
  · induction N <;> simp
    rename_i N' IH
    split <;> rename_i h
    · simp only [lookup]; split
      · simp_all
      · rw [IH (by omega)]; simp; omega
    · rw [if_pos HL]
      if h : k < N' then
        simp [IH h]; omega
      else
        have : k = N' := by omega
        simp_all
        clear this h
        suffices ∀ N'', N' ≤ N'' → (construct f N').lookup N'' = none by grind
        induction N' <;> simp
        rename_i n' _
        cases f n' <;> simp <;> grind
  · simp; rw [if_neg (by omega)]
    induction N <;> simp
    split
    · simp [lookup]; grind
    · grind

instance AssocList.instStoreAssocList : Store (AssocList V) Nat (Option V) where
  get := lookup
  set := update
  get_set_eq He := by simp only [lookup_update, fset, if_pos He]
  get_set_ne He := by simp only [lookup_update, fset, if_neg He]

abbrev op_lift (op : V → V → V) (v1 v2 : Option V) : Option V :=
  match v1, v2 with
  | some v1, some v2 => some (op v1 v2)
  | some v1, none => some v1
  | none, some v2 => some v2
  | none, none => none

instance AssocList.instHeapAssocList : Heap (AssocList V) Nat V where
  hmap h f := f.map h
  get_hmap := by
    intro f t k
    induction t with
    | empty =>
      simp_all [Store.get, map]
    | set n' v' t' IH =>
      simp_all [Store.get]
      cases h1 : f n' v' <;> simp <;> split <;> rename_i h2 <;> simp_all
    | remove n' t' IH =>
      simp_all [Store.get]
      split <;> simp [Option.bind]
  empty := .empty
  get_empty := by simp [Store.get]
  merge op t1 t2 :=
    construct (fun n => op_lift op (t1.lookup n) (t2.lookup n)) (max t1.fresh t2.fresh)
  get_merge := by
    intro op t1 t2 k
    simp [Store.get, AssocList.construct_get, Option.merge, op_lift]
    split
    · rename_i h
      cases t1.lookup k <;> cases t2.lookup k <;> simp_all
    · rename_i h
      rw [AssocList.fresh_lookup_ge _ _ (by omega : t1.fresh ≤ k)]
      rw [AssocList.fresh_lookup_ge _ _ (by omega : t2.fresh ≤ k)]

instance instAllocHeapAssocList : AllocHeap (AssocList V) Nat V where
  notFull _ := True
  fresh {f} _ := f.fresh
  get_fresh {f _} := fresh_lookup_ge f f.fresh (f.fresh.le_refl)

instance instUnboundedHeapAssocList : UnboundedHeap (AssocList V) Nat V where
  notFull_empty := by simp [notFull]
  notFull_set_fresh {t v H} := by simp [notFull]


end AssociationLists



section Lemmas

/-- Merge an optional value with an optional key-value pair, using the pair's key in the
merge function. This is an internal helper for TreeMap heap proofs. -/
private def Option.pairMerge (f : K → V → V → V) (o1 : Option V)
    (o2 : Option (K × V)) : Option V :=
  o2.elim o1 fun ⟨k, v2⟩ => some (o1.elim v2 (f k · v2))

@[simp]
private theorem Option.pairMerge_none_right : pairMerge f o1 none = o1 := by
  cases o1 <;> rfl

@[simp]
private theorem Option.pairMerge_some_right :
    pairMerge f o1 (some (k, v)) = merge (f k) o1 (some v) := by
  cases o1 <;> rfl

/-- Insert a value if none, or merge with existing value. Used in alter operations for
maps. This is `Option.merge f o (some v)` - inserting `v` when empty, or merging with
existing. -/
@[simp]
def Option.insertOrMerge (f : V → V → V) (v : V) (o : Option V) : Option V :=
  merge f o (some v)

end Lemmas

namespace Std.TreeMap

/-! ## TreeMap Heap Instance -/

section HeapInstance


open Option Std.DTreeMap.Internal.Impl List TransCmp OrientedCmp LawfulEqCmp Ordering

variable {K V : Type _} [Ord K] [TransOrd K] [LawfulEqOrd K]

/-- TreeMap forms a Store with Option values. -/
instance instStoreTreeMap : Store (TreeMap K V compare) K (Option V) where
  get t k := t[k]?
  set t k v := t.alter k (fun _ => v)
  get_set_eq {t k k' v} h := by grind
  get_set_ne {t k k' v} h := by grind

private theorem get?_foldl_alter_impl_sigma {l : List ((_ : K) × V)}
    (hinit : init.WF) (hl : l.Pairwise (fun x y => ¬ (compare x.1 y.1).isEq)) :
    Const.get? (l.foldl (fun acc ⟨k, v⟩ => Const.alter! k (insertOrMerge (f k) v) acc) init) k =
      pairMerge f (Const.get? init k)
        ((l.find? (fun x => (compare x.1 k).isEq)).map (fun kv => (kv.1, kv.2))) := by
  induction l generalizing init with
  | nil =>
    simp [foldl_nil]
  | cons hd tl IH =>
    rw [foldl_cons, IH (WF.constAlter! hinit) (hl.tail), Const.get?_alter! hinit]
    by_cases h : compare hd.1 k = .eq <;> simp [h]
    rw [← Const.get?_congr hinit h]
    have Hhead_none : tl.find? (fun x => (compare x.1 k).isEq) = none := by
      refine find?_eq_none.mpr fun _ hkv He => rel_of_pairwise_cons hl hkv ?_
      refine isEq_iff_eq_eq.mpr <| compare_eq_iff_eq.mpr ?_
      rw [eq_of_compare h, compare_eq_iff_eq.mp <| isEq_iff_eq_eq.mp He]
    rw [Hhead_none, map_none, pairMerge_none_right]

private theorem getElem?_foldl_alter {l : List (K × V)} {init : TreeMap K V compare}
    (hl : l.Pairwise (fun a b => compare a.1 b.1 ≠ .eq)) :
    (l.foldl (fun acc kv => acc.alter kv.1 (insertOrMerge (f kv.1) kv.2)) init)[k]? =
      pairMerge f init[k]? (l.find? (fun kv => (compare kv.1 k).isEq)) := by
  induction l generalizing init with
  | nil =>
    simp
  | cons hd tl ih =>
    rw [foldl_cons, ih (hl.tail)]
    by_cases heq : compare hd.1 k = .eq
    · have htl : tl.find? (fun kv => (compare kv.1 k).isEq) = none := by
        refine find?_eq_none.mpr fun kv hkv h => ?_
        refine rel_of_pairwise_cons hl hkv (eq_trans heq ?_)
        rw [compare_eq_iff_eq.mp <| isEq_iff_eq_eq.mp h]
        exact compare_self
      simp [getElem?_congr (eq_symm heq), htl, heq]
      cases _ : init[hd.1]? <;> rfl
    · simp [getElem?_alter, heq]

private theorem getElem?_mergeWith_eq_foldl {t₁ t₂ : TreeMap K V compare}
    {f : K → V → V → V} {k : K} :
    (t₁.mergeWith f t₂)[k]? =
      (t₂.toList.foldl (fun acc kv => acc.alter kv.1 (insertOrMerge (f kv.1) kv.2)) t₁)[k]? := by
  rw [getElem?_foldl_alter (distinct_keys_toList (t := t₂))]
  rw [show _[_]? = _ from
    congrArg (Const.get? · k) (Const.mergeWith_eq_mergeWith! ..)]
  have h_foldl :
      Const.mergeWith! f t₁.inner.inner t₂.inner.inner =
        .foldl (fun t a b₂ => Const.alter! a (insertOrMerge (f a) b₂) t)
          t₁.inner.inner t₂.inner.inner := by
    unfold Const.mergeWith!
    congr
    funext _ _ _
    congr
    funext o
    cases o <;> rfl
  rw [h_foldl]
  rw [foldl_eq_foldl]
  rw [show t₂.toList = _ from Const.toList_eq_toListModel_map]
  have hfind_map : ∀ l : List ((_ : K) × V),
      (l.map (fun e => (e.1, e.2))).find? (fun kv => (compare kv.1 k).isEq) =
        (l.find? (fun kv => (compare kv.1 k).isEq)).map (fun e => (e.1, e.2)) :=
    fun l => by induction l with grind [isEq]
  rw [hfind_map]
  refine get?_foldl_alter_impl_sigma t₁.inner.wf ?_
  refine (pairwise_map.mp <|
    SameKeys.ordered_iff_pairwise_keys.mp t₂.inner.wf.ordered).imp ?_
  rintro hlt heq H
  simp [H]

@[simp]
theorem getElem?_mergeWith' {t₁ t₂ : TreeMap K V compare} {f : K → V → V → V} {k : K} :
    (t₁.mergeWith f t₂)[k]? = merge (f k) t₁[k]? t₂[k]? := by
  rw [getElem?_mergeWith_eq_foldl (t₁ := t₁) (t₂ := t₂) (f := f) (k := k),
      getElem?_foldl_alter (distinct_keys_toList (t := t₂))]
  cases h : t₂[k]? with
  | none =>
    rw [List.find?_eq_none.mpr, pairMerge_none_right, merge_none_right]
    refine fun ⟨k', v'⟩ hkv' heq => ?_
    have _ :=
      (getElem?_eq_some_iff_exists_compare_eq_eq_and_mem_toList (k := k) (v := v')).mpr
        ⟨k', ?G, hkv'⟩
    case G =>
      replace h := compare_eq_iff_eq.mp <| isEq_iff_eq_eq.mp heq
      simp only [isEq_iff_eq_eq, compare_eq_iff_eq] at heq
      exact heq ▸ compare_self
    grind
  | some v =>
    obtain ⟨k', hcmp, hmem⟩ :=
      getElem?_eq_some_iff_exists_compare_eq_eq_and_mem_toList.mp h
    have hpred : (compare k' k).isEq  = true := by simp [eq_symm hcmp]
    obtain ⟨kv, hfind⟩ := isSome_iff_exists.mp <|
      find?_isSome (p := fun kv => (compare kv.1 k).isEq) |>.mpr ⟨(k', v), hmem, hpred⟩
    have hkv_cmp : compare kv.1 k = .eq := by
      simpa [beq_iff_eq] using List.find?_some hfind
    have hval : kv.2 = v := by grind
    have hfind : find? (fun kv => (compare kv.fst k).isEq) t₂.toList =
        some (kv.fst, v) := by
      simp [← hval, ← hfind]
    simp [← hval, hfind]
    simp [eq_of_compare hkv_cmp]

instance instHeapTreeMap : Heap (TreeMap K V compare) K V where
  empty := {}
  hmap f t := t.filterMap f
  merge op t1 t2 := t1.mergeWith (fun _ v1 v2 => op v1 v2) t2
  get_empty := rfl
  get_hmap {f t k} := by show (filterMap f t)[k]? = t[k]?.bind (f k); simp
  get_merge := getElem?_mergeWith'

end HeapInstance

end Std.TreeMap

/-! ## ExtTreeMap Heap Instance -/

namespace Std.ExtTreeMap

section HeapInstance

open Option Std.ExtDTreeMap List TransCmp OrientedCmp LawfulEqCmp Ordering

variable {K V : Type _} [Ord K] [TransOrd K] [LawfulEqOrd K]

/-- ExtTreeMap forms a Store with Option values.

Note: This requires that `cmp k k' = .eq` implies `k = k'` (i.e., `LawfulEqCmp`).
-/
instance instStoreExtTreeMap : Store (ExtTreeMap K V compare) K (Option V) where
  get t k := t[k]?
  set t k v := t.alter k (fun _ => v)
  get_set_eq {t k k' v} h := by grind
  get_set_ne {t k k' v} h := by grind

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

instance instHeapExtTreeMap : Heap (ExtTreeMap K V compare) K V where
  empty := {}
  hmap f t := t.filterMap f
  merge op t1 t2 := t1.mergeWith (fun _ => op) t2
  get_empty := rfl
  get_hmap {f t k} := by show (filterMap f t)[k]? = t[k]?.bind (f k); grind
  get_merge := getElem?_mergeWith'

end HeapInstance

end Std.ExtTreeMap
