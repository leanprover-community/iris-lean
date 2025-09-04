/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE

open Iris

/-! ## Generic heaps

Note: There are three definitions of equivalence in this file

[1] OFE.Equiv (pointwise equvalence)
[2] StoreO.Equiv (pointwise equality of .get)
[3] Eq (equality of representations)

[3] -> [2] -> [1] always
[1] -> [2] when the value type is Leibniz
[2] -> [3] when the store is an IsoFunStore
-/

-- TODO: Move this to a generic set theory library
def set_disjoint {X : Type _} (S1 S2 : X → Prop) : Prop := ∀ x : X, ¬(S1 x ∧ S2 x)
def set_union {X : Type _} (S1 S2 : X → Prop) : X → Prop := fun x => S1 x ∨ S2 x
def set_included {X : Type _} (S1 S2 : X → Prop) : Prop := ∀ x, S1 x → S2 x

/-- The type `T` can store and retrieve keys of type `K` and obtain values of type `V`. -/
class Store (T : Type _) (K V : outParam (Type _)) where
  get : T → K → V
  set : T → K → V → T
  get_set_eq {t k k' v} : k = k' → get (set t k v) k' = v
  get_set_ne {t k k' v} : k ≠ k' → get (set t k v) k' = get t k'
export Store (get set get_set_eq get_set_ne)

open Classical in
theorem Store.get_set [Store T K V] {t : T} {k k' : K} {v : V} :
    get (set t k v) k' = if k = k' then v else get t k' := by
  split <;> rename_i h
  · exact get_set_eq h
  · exact get_set_ne h

/-- An index-dependent predicate holds at every member of the store. -/
def Store.all [Store T K V] (P : K → V → Prop) : T → Prop :=
  fun t => ∀ k, P k (get t k)

/-- Two Stores are pointwise equivalent. -/
@[simp] def Store.Equiv [Store T K V] (t1 t2 : T) : Prop := get t1 = get t2

instance Store.Equiv_trans [Store T K V] : Trans Equiv (Equiv (T := T)) Equiv := ⟨by simp_all⟩

/-- RepFunStore: The type T can represent all functions that satisfy Rep.
For instance, this holds with `rep _ = True` when `T = K → V`. On the other hand, when
`T = list (K × Option V)` representing a partial function with an association list, this holds
when `rep f` is the predicate that says `f` has finite domain. -/
class RepFunStore (T : Type _) (K V : outParam (Type _)) [Store T K V] where
  rep : (K → V) → Prop
  rep_get (t : T) : rep (get t)
  ofFun : { f : K → V // rep f } → T
  get_ofFun: get (ofFun f) = f
export RepFunStore (rep rep_get ofFun get_ofFun)

/-- IsoFunStore: The type T is isomorphic the type of functions `{f : Rep f}`, or in other words,
equality of T is the same as equality of `{f : Rep f}`. -/
class IsoFunStore (T : Type _) (K V : outParam (Type _)) [Store T K V] extends RepFunStore T K V where
  ofFun_get {t : T} : ofFun ⟨get t, rep_get t⟩ = t
export IsoFunStore (ofFun_get)

theorem IsStoreIso.ext [Store T K V] [IsoFunStore T K V] {t1 t2 : T}
    (H : ∀ k, get t1 k = get t2 k) : t1 = t2 := by
  rw [← ofFun_get (t := t1), ← ofFun_get (t := t2)]
  congr 2; exact funext H

/-- [2] → [3] -/
theorem IsoFunStore.store_eq_of_Equiv [Store T K V] [IsoFunStore T K V] {t1 t2 : T} :
    Store.Equiv t1 t2 → t1 = t2 := (IsStoreIso.ext <| fun k => congrFun · k)

/-- Stores of type T1 can be coerced to stores of type T2. -/
class HasStoreMap (T1 T2 : Type _) (K V1 V2 : outParam (Type _)) [Store T1 K V1] [Store T2 K V2] where
  /-- Map a function that depends on the elemet across the entire structure  -/
  dmap (f : K → V1 → V2) : T1 → T2
  get_dmap : get (dmap f t) k = f k (get t k)
export HasStoreMap (dmap get_dmap)

/-- Map between heaps that preserves non-allocations. -/
class HasHHMap (T1 T2 : Type _) (K V1 V2 : outParam (Type _))
   [Store T1 K (Option V1)] [Store T2 K (Option V2)] where
  hhmap (f : K → V1 → Option V2) : T1 → T2
  hhmap_get (f : K → V1 → Option V2) : get (hhmap f t) k = (get t k).bind (f k)
export HasHHMap (hhmap hhmap_get)

def HasStoreMap.map (f : V1 → V2) [Store T1 K V1] [Store T2 K V2] [HasStoreMap T1 T2 K V1 V2] : T1 → T2 :=
  HasStoreMap.dmap (fun (_ : K) => f)

class Heap (T : Type _) (K V : outParam (Type _)) extends Store T K (Option V) where
  empty : T
  hmap (f : K → V → Option V) : T → T
  merge (op : V → V → V) : T → T → T
  get_empty : get empty k = none
  get_hmap : get (hmap f t) k = (get t k).bind (f k)
  get_merge : get (merge op t1 t2) k = Option.merge op (get t1 k) (get t2 k)
export Heap (empty hmap merge get_empty get_hmap get_merge)

theorem hmap_alloc [Heap T K V] {t : T} (H : get t k = some v) : get (hmap f t) k = f k v := by
  simp [get_hmap, bind, H]

theorem hmap_unalloc [Heap T K V] {t : T} (H : get t k = none) : get (hmap f t) k = none := by
  simp [get_hmap, bind, H]

/-- The heap of a single point -/
def Heap.point [Heap T K V] (k : K) (v : Option V) : T := set empty k v

/-- Delete an element from a heap by setting its value to .none -/
def Heap.delete [Heap T K V] (t : T) (k : K) : T := set t k none

/-- The domain of a heap is the set of keys that map to .some values. -/
def Heap.dom [Heap T K V] (t : T) : K → Prop := fun k => (get t k).isSome

@[simp] def Heap.union [Heap T K V] : T → T → T := merge (fun v _ => v)

theorem Heap.point_get_eq [Heap T K V] (H : k = k') : get (point k v : T) k' = v := by
  rw [point, get_set_eq H]

theorem Heap.point_get_ne [Heap T K V] (H : k ≠ k') : get (point k v : T) k' = none := by
  rw [point, get_set_ne H, get_empty]

open Classical in
theorem Heap.get_point [Heap T K V] {k k' : K} {v : Option V} :
    get (point k v : T) k' = if k = k' then v else .none := by
  split <;> rename_i h
  · exact point_get_eq h
  · exact point_get_ne h

/-- An AllocHeap is a heap which can allocate elements under some condition. -/
class AllocHeap (T : Type _) (K V : outParam (Type _)) extends Heap T K V where
  notFull : T → Prop
  fresh {t : T} : notFull t → K
  get_fresh  {H : notFull t} : get t (fresh H) = none
export AllocHeap (notFull fresh get_fresh)

/-- An UnboundeHeap is a heap which can allocate an unbounded number of elements starting at empty. -/
class UnboundedHeap (T : Type _) (K V : outParam (Type _)) extends AllocHeap T K V where
  notFull_empty : notFull (empty : T)
  notFull_set_fresh {H : notFull t} : notFull (set t (fresh H) v)
export UnboundedHeap (notFull_empty notFull_set_fresh)

section ofe
open OFE

instance Store.instOFE [Store T K V] [OFE V] : OFE T where
  Equiv s0 s1  := get s0 ≡ get s1
  Dist n s0 s1 := get s0 ≡{n}≡ get s1
  dist_eqv     := ⟨fun _ => .of_eq rfl, (·.symm), (·.trans ·)⟩
  equiv_dist   := equiv_dist
  dist_lt      := dist_lt

@[simp] def Store.toMap [Store T K V] [OFE V] : T -n> (K → V) where
  f x := get x
  ne.1 {_ _ _} H k := H k

@[simp] def Store.ofMap [Store T K V] [R : RepFunStore T K V] [OFE V] : {f : K → V // R.rep f} -n> T where
  f x := ofFun x
  ne.1 {_ _ _} H k := by rw [get_ofFun, get_ofFun]; exact H k

instance get_ne [Store T K V] [OFE V] (k : K) : NonExpansive (get · k : T → V) where
  ne {_ _ _} Ht := Ht k

instance [Store T K V] [OFE V] (k : K) : NonExpansive₂ (set · k · : T → V → T) where
  ne {_ _ _} Hv {_ _} Ht k' := by
    if h : k = k'
      then rw [get_set_eq h, get_set_eq h]; exact Ht
      else rw [get_set_ne h, get_set_ne h]; exact Hv k'

theorem Store.eqv_of_Equiv [OFE V] [Store T K V] {t1 t2 : T} (H : Equiv t1 t2) : t1 ≡ t2 :=
  (.of_eq <| congrFun H ·)

instance [Heap T K V] [OFE V] (op : V → V → V) [NonExpansive₂ op] :
    NonExpansive₂ (merge (T := T) op) where
  ne _ {_ _} Ht {_ _} Hs k := by
    simp only [get_merge]
    exact NonExpansive₂.ne (Ht k) (Hs k)

instance [Store T1 K V1] [Store T2 K V2] [OFE V1] [OFE V2] (f : K → V1 → V2)
  [∀ k, NonExpansive (f k)] [HasStoreMap T1 T2 K V1 V2] : NonExpansive (dmap f : T1 → T2) where
  ne _ {_ _} H k := by simp only [get_dmap]; exact NonExpansive.ne (H k)

/-- Project a chain of stores through it's kth coordinate to a chain of values. -/
def Store.chain [Store T K V] [OFE V] (k : K) (c : Chain T) : Chain V where
  chain i := get (c i) k
  cauchy Hni := c.cauchy Hni k

theorem Store.chain_get [Store T K V] [OFE V] (k : K) (c : Chain T) :
    (chain k c) i = get (c i) k := by
  simp [chain]

open Store in
instance Heap.instCOFE [Heap T K V] [COFE V] : COFE T where
  compl c := hmap (fun _ => COFE.compl <| c.map ⟨_, get_ne ·⟩) (c 0)
  conv_compl {_ c} k := by
    rw [get_hmap]
    rcases H : get (c.chain 0) k
    · rw [← chain_get, chain_none_const (c := chain k c) (n := 0) (H▸rfl)]; rfl
    · exact IsCOFE.conv_compl

end ofe

section cmra
open CMRA

/- ## A CMRA on Heaps -/

variable [Heap T K V] [CMRA V]

@[simp] def Store.op (s1 s2 : T) : T := merge (K := K) CMRA.op s1 s2
@[simp] def Store.unit : T := empty
@[simp] def Store.pcore (s : T) : Option T := some <| hmap (fun _ => CMRA.pcore) s
@[simp] def Store.valid (s : T) : Prop := ∀ k, ✓ (get s k : Option V)
@[simp] def Store.validN (n : Nat) (s : T) : Prop := ∀ k, ✓{n} (get s k : Option V)

theorem lookup_incN {n} {m1 m2 : T} :
    (∃ (z : T), m2 ≡{n}≡ Store.op m1 z) ↔
    ∀ i, (∃ z, (get m2 i) ≡{n}≡ (get m1 i) • z) := by
  refine ⟨fun ⟨z, Hz⟩ i => ?_, fun H => ?_⟩
  · refine ⟨get z i, ?_⟩
    refine .trans (get_ne i |>.ne Hz) ?_
    simp only [Store.op, op, optionOp, get_merge]
    cases get m1 i <;> cases get z i <;> simp
  · obtain ⟨f, Hf⟩ := Classical.axiomOfChoice H
    exists hmap (fun k _ => f k) m2
    refine fun i => (Hf i).trans ?_
    specialize Hf i; revert Hf
    simp [CMRA.op, optionOp, get_merge, get_hmap]
    cases get m2 i <;> cases get m1 i <;> cases f i <;> simp

theorem lookup_inc {m1 m2 : T} :
    (∃ (z : T), m2 ≡ Store.op m1 z) ↔
    ∀ i, (∃ z, (Store.get m2 i) ≡ (Store.get m1 i) • z) := by
  refine ⟨fun ⟨z, Hz⟩ i => ?_, fun H => ?_⟩
  · refine ⟨get z i, ?_⟩
    refine .trans (get_ne i |>.eqv Hz) ?_
    simp only [Store.op, op, optionOp, get_merge]
    cases get m1 i <;> cases get z i <;> simp
  · obtain ⟨f, Hf⟩ := Classical.axiomOfChoice H
    exists hmap (fun k _ => f k) m2
    refine fun i => (Hf i).trans ?_
    specialize Hf i; revert Hf
    simp [CMRA.op, optionOp, get_merge, get_hmap]
    cases get m2 i <;> cases get m1 i <;> cases f i <;> simp

open OFE in
instance instStoreCMRA : CMRA T where
  pcore := Store.pcore
  op := Store.op
  ValidN := Store.validN
  Valid := Store.valid
  op_ne.ne _ x1 x2 H i := by
    specialize H i; revert H; rename_i x _
    simp [op, get_merge]
    cases get x1 i <;> cases get x2 i <;> cases get x i <;> simp
    apply op_right_dist
  pcore_ne {n x y _} H := by
    simp only [Store.pcore, Option.some.injEq, exists_eq_left']
    refine (· ▸ fun k => ?_); specialize H k; revert H
    rw [get_hmap, get_hmap]
    cases Store.get x k <;> cases Store.get y k <;> simp
    exact (NonExpansive.ne ·)
  validN_ne Hx H k :=
    validN_ne (NonExpansive.ne (f := (Store.get · k : T → Option V)) Hx) (H k)
  valid_iff_validN :=
    ⟨fun H n k => valid_iff_validN.mp (H k) n,
     fun H k => valid_iff_validN.mpr (H · k)⟩
  validN_succ H k := validN_succ (H k)
  validN_op_left {n x1 x2} H k := by
    refine validN_op_left (y := Store.get x2 k) ?_
    specialize H k; revert H
    simp only [Store.op, get_merge, Option.merge]
    cases get x1 k <;> cases get x2 k <;> simp [optionOp, op]
  assoc {x y z} k := by
    simp only [Store.op, get_merge]
    cases Store.get x k <;> cases Store.get y k <;> cases Store.get z k <;> simp
    exact assoc
  comm {x y} k := by
    simp [Store.op, Heap.get_merge]
    cases Store.get x k <;> cases Store.get y k <;> simp
    exact comm
  pcore_op_left {x cx} H k := by
    simp only [← Option.getD_some (a := cx) (b := cx), Store.op, get_merge]
    cases Hcx : Store.get cx k <;> cases hx : Store.get x k <;> simp <;>
      simp only [Store.pcore, Option.some.injEq] at H
    · rw [← H, hmap_unalloc hx] at Hcx
      cases Hcx
    · apply pcore_op_left
      rw [← Hcx, ← H, hmap_alloc hx]
  pcore_idem {x cx} H := by
    simp only [Store.pcore, Option.some.injEq] at H
    change (Store.pcore cx |>.getD cx) ≡ cx
    intro k
    simp [← H, get_hmap]
    rcases Store.get x k with (_|v) <;> simp
    cases HY : pcore v; simp
    exact pcore_idem HY
  pcore_op_mono := by
    apply pcore_op_mono_of_core_op_mono
    rintro x cx y ⟨z, Hz⟩
    suffices ∃ z, (Store.pcore y |>.getD y) ≡ Store.op (Store.pcore x |>.getD x) z by
      rintro Hx
      simp only [Store.pcore, Option.some.injEq, Store.op, exists_eq_left']
      rcases this with ⟨z', Hz'⟩
      exists z'
      refine .trans Hz' (fun i => ?_)
      cases get z' i <;> cases get x i <;> simp_all
    refine lookup_inc.mpr (fun i => ?_)
    obtain ⟨v', Hv'⟩ : (core (Store.get x i)) ≼ (core (Store.get y i))  := by
      apply core_mono
      exists get z i
      have Hz := Hz i; revert Hz
      simp [CMRA.op, optionOp, get_merge]
      cases get x i <;> cases get z i <;> simp_all
    exists v'
    simp_all [core, pcore, optionCore, get_hmap]
  extend {n x y1 y2} Hm Heq := by
    have Hslice i : Store.get x i ≡{n}≡ Store.get y1 i • Store.get y2 i := by
      refine (get_ne i |>.ne Heq).trans ?_
      simp [CMRA.op, get_merge, optionOp]
      cases get y1 i <;> cases get y2 i <;> simp
    let extendF (i : K) := CMRA.extend (Hm i) (Hslice i)
    exists hmap (fun k (_ : V) => extendF k |>.fst) y1
    exists hmap (fun k (_ : V) => extendF k |>.snd.fst) y2
    simp [Store.op, get_merge]
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
    all_goals rcases hF : extendF i with ⟨z1, z2, Hm, Hz1, Hz2⟩
    · refine Hm.trans ?_
      simp [Store.op, get_merge, hF, CMRA.op, optionOp]
      cases z1 <;> cases z2 <;> cases h1 : get y1 i <;> cases h2 : get y2 i <;> simp [h1, h2] at Hz1 Hz2
      · rw [hmap_unalloc h1, hmap_unalloc h2]; simp
      · rw [hmap_unalloc h1, hmap_alloc h2, hF]; simp
      · rw [hmap_alloc h1, hmap_unalloc h2, hF]; simp
      · rw [hmap_alloc h1, hmap_alloc h2, hF]; simp
    · cases h : Store.get y1 i
      · rw [hmap_unalloc h]
      · rw [hmap_alloc h, ← h, hF]; exact Hz1
    · cases h : Store.get y2 i
      · rw [hmap_unalloc h]
      · rw [hmap_alloc h, ← h, hF]; exact Hz2

instance instStoreUCMRA : UCMRA T where
  unit := Store.unit
  unit_valid := by
    simp [CMRA.Valid, Store.valid, optionValid, Store.unit, get_empty]
  unit_left_id _ := by
    simp [CMRA.op, Heap.get_merge, Store.unit, get_empty]
  pcore_unit _ := by
    simp [Store.unit, hmap_unalloc get_empty, get_empty]

end cmra

namespace Heap

variable {K V : Type _} [Heap T K V] [CMRA V]
open CMRA Store

theorem validN_get_validN {m : T} (Hv : ✓{n} m) (He : get m i ≡{n}≡ some x) : ✓{n} x := by
  specialize Hv i; revert Hv
  rcases h : get m i <;> simp [h] at He
  exact OFE.Dist.validN He |>.mp

theorem valid_get_valid {m : T} (Hv : ✓ m) (He : get m i ≡ some x) : ✓ x :=
  valid_iff_validN.mpr (fun _ => validN_get_validN Hv.validN He.dist)

theorem insert_validN {m : T} (Hx : ✓{n} x) (Hm : ✓{n} m) : ✓{n} (set m i x) := by
  intro k
  rw [get_set]; split; rename_i He
  · exact Hx
  · apply Hm

theorem insert_valid {m : T} (Hx : ✓ x) (Hm : ✓ m) : ✓ (set m i x) :=
  valid_iff_validN.mpr (fun _ => insert_validN Hx.validN Hm.validN)

theorem point_valid_iff : ✓ (point i x : T) ↔ ✓ x := by
  refine ⟨fun H => ?_, fun H k => ?_⟩
  · specialize H i; rw [point_get_eq rfl] at H; trivial
  · rw [get_point]; split <;> trivial

theorem point_validN_iff : ✓{n} (point i x : T) ↔ ✓{n} x := by
  refine ⟨fun H => ?_, fun H k => ?_⟩
  · specialize H i; rw [point_get_eq rfl] at H; trivial
  · rw [get_point]; split <;> trivial

theorem delete_validN {m : T} (Hv : ✓{n} m) : ✓{n} (delete m i) := by
  intro k
  rw [delete, get_set]; split
  · trivial
  · exact Hv k

theorem delete_valid {m : T} (Hv : ✓ m) : ✓ (delete m i) :=
  valid_iff_validN.mpr (fun _ => delete_validN Hv.validN)

theorem set_equiv_point_op_point {m : T} (Hemp : get m i = none) : Equiv (set m i x) (point i x • m) := by
  refine funext (fun k => ?_)
  simp [CMRA.op, Store.op, Equiv, get_merge, Option.merge, get_point, Hemp, get_set]
  split <;> rename_i He
  · rw [← He, Hemp]; cases x <;> rfl
  · cases (Store.get m k) <;> rfl

theorem set_eq_point_op_point [IsoFunStore T K (Option V)] {m : T} (Hemp : get m i = none) :
    set m i x = point i x • m :=
  IsoFunStore.store_eq_of_Equiv (set_equiv_point_op_point Hemp)

theorem core_point_equiv {i : K} {x : V} {cx} (Hpcore : pcore x = some cx) :
    Equiv (T := T) (core <| point i (some x)) (point i (some cx)) := by
  refine funext fun k => ?_
  simp [← Hpcore, core, CMRA.pcore, get_point, get_hmap]
  split <;> rfl

theorem point_core_eq [IsoFunStore T K (Option V)] {i : K} {x : V} {cx} (Hpcore : pcore x = some cx) :
    core (point (T := T) i (some x)) = point i (some cx)  :=
  IsoFunStore.store_eq_of_Equiv (core_point_equiv Hpcore)

theorem point_core_eqv {i : K} {x : V} {cx} (Hpcore : pcore x ≡ some cx) :
    core (point (T := T) i (some x)) ≡ point i (some cx) := by
  intro k
  simp [core, CMRA.pcore, get_point, get_hmap]
  split <;> trivial

theorem point_core_total [IsTotal V] {i : K} {x : V} :
    Equiv (core <| point (T := T) i (some x)) ((point i (some (core x)))) := by
  obtain ⟨_, Hxc⟩ := total x
  apply (core_point_equiv Hxc).trans
  simp [core, Hxc]

theorem point_core_total_eq [IsTotal V] [IsoFunStore T K (Option V)] {i : K} {x : V} :
    core (point (T := T) i (some x)) = point i (some (core x)) :=
  IsoFunStore.store_eq_of_Equiv point_core_total

theorem point_op_point {i : K} {x y : V} :
    Equiv ((point (T := T) i (some x)) • (point i (some y))) ((point i (some (x • y)))) := by
  refine funext fun k => ?_
  simp only [CMRA.op, Store.op, get_merge, get_point]
  split <;> simp [Option.merge]

theorem point_op_point_eq [IsoFunStore T K (Option V)] {i : K} {x y : V} :
    (point (T := T) i (some x)) • (point i (some y)) = (point i (some (x • y))) :=
  IsoFunStore.store_eq_of_Equiv point_op_point

instance {m : T} [∀ x : V, CoreId x] : CoreId m where
  core_id i := by
    rw [get_hmap]
    cases Store.get m i <;> simp
    exact core_id

instance [CoreId (x : V)] : CoreId (point (T := T) i (some x)) where
  core_id k := by
    simp [get_hmap, get_point]
    split <;> simp
    exact  core_id

theorem point_incN_iff {m : T} :
    (point (T := T) i (some x)) ≼{n} m ↔ ∃ y, (get m i ≡{n}≡ some y) ∧ some x ≼{n} some y := by
  refine ⟨fun ⟨z, Hz⟩ => ?_, fun ⟨y, Hy, z, Hz⟩ => ?_⟩
  · specialize Hz i; revert Hz
    simp only [CMRA.op, Store.op, get_merge, point_get_eq rfl]
    rcases get z i with (_|v)
    · intro _
      exists x
    · refine (⟨x • v, ·, ?_⟩)
      exists v
  · exists set m i z
    intro j
    simp [CMRA.op, get_merge, get_point, get_set]
    split <;> rename_i He
    · refine (He ▸ Hy).trans (Hz.trans ?_)
      cases z <;> simp [CMRA.op, optionOp]
    · simp

theorem point_inc_iff {m : T} :
    (point i (T := T) (some x)) ≼ m ↔ ∃ y, (get m i ≡ some y) ∧ some x ≼ some y := by
  refine ⟨fun ⟨z, Hz⟩ => ?_, fun ⟨y, Hy, z, Hz⟩ => ?_⟩
  · specialize Hz i; revert Hz
    simp only [CMRA.op, Store.op, get_merge, point_get_eq rfl]
    rcases get z i with (_|v)
    · intro _
      exists x
    · refine (⟨x • v, ·, ?_⟩)
      exists v
  · exists set m i z
    intro j
    simp [CMRA.op, get_merge, get_point, get_set]
    split <;> rename_i He
    · refine (He ▸ Hy).trans (Hz.trans ?_)
      cases z <;> simp [CMRA.op, optionOp]
    · simp

theorem exclusive_point_inc_iff {m : T} (He : Exclusive x) (Hv : ✓ m) :
    (point i (T := T) (some x)) ≼ m ↔ (get m i ≡ some x) := by
  refine point_inc_iff.trans ⟨fun ⟨y, Hy, Hxy⟩ => ?_, fun _ => ?_⟩
  · suffices x ≡ y by exact Hy.trans <| this.symm
    exact some_inc_exclusive Hxy <| valid_get_valid Hv Hy
  · exists x

theorem point_inc_point_iff : (point i (T := T) (some x)) ≼ (point i (some y)) ↔ some x ≼ some y := by
  refine point_inc_iff.trans ⟨fun ⟨z, Hz, Hxz⟩ => ?_, fun H => ?_⟩
  · refine inc_of_inc_of_eqv Hxz ?_
    refine .trans Hz.symm ?_
    exact .of_eq <| point_get_eq rfl
  · refine ⟨y, ?_, H⟩
    exact .of_eq <| point_get_eq rfl

theorem total_point_inc_point_iff [IsTotal V] : (point i (T := T) (some x)) ≼ (point i (some y)) ↔ x ≼ y :=
  point_inc_point_iff.trans <| some_inc_total.trans <| Eq.to_iff rfl

theorem point_inc_point_mono (Hinc : x ≼ y) : (point (T := T) i (some x)) ≼ (point i (some y)) :=
  point_inc_point_iff.mpr <| some_inc.mpr <| .inr Hinc

instance [H : Cancelable (some x)] : Cancelable (point (T := T) i (some x)) where
  cancelableN {n m1 m2} Hv He j := by
    specialize Hv j; revert Hv
    specialize He j; revert He
    simp only [CMRA.op, Store.op, get_merge, Option.merge, get_point]
    if He : i = j
      then
        simp_all only [↓reduceIte]
        intro Hv He
        cases _ : get m1 j <;> cases _ : get m2 j
        all_goals apply H.cancelableN
        all_goals simp_all [CMRA.op, Store.op, optionOp]
      else
        cases get m1 j <;> cases get m2 j
        all_goals simp_all [CMRA.op, optionOp]

instance {m : T} [Hid : ∀ x : V, IdFree x] [Hc : ∀ x : V, Cancelable x] : Cancelable m where
  cancelableN {n m1 m2} Hv He i := by
    apply cancelableN (x := get m i)
    · specialize Hv i; revert Hv
      simp [CMRA.op, Store.op, Heap.get_merge, optionOp]
      cases _ : get m i <;> cases _ : get m1 i <;> simp_all
    · specialize He i; revert He
      simp [Heap.get_merge, CMRA.op, Store.op, optionOp]
      cases get m i <;> cases get m1 i <;> cases get m2 i <;> simp_all [Heap.get_merge]

theorem insert_op_equiv {m1 m2 : T} :
    Equiv ((set (V := Option V) (m1 • m2) i (x • y))) (set m1 i x • set m2 i y) := by
  refine funext fun j => ?_
  if He : i = j
    then
      simp [CMRA.op, get_set_eq He, get_merge, optionOp]
      cases x <;> cases y <;> simp_all
    else
      simp [CMRA.op, get_set_ne (T := T) He, get_merge]

theorem insert_op_eq [IsoFunStore T K (Option V)] {m1 m2 : T} :
    (set (V := Option V) (m1 • m2) i (x • y)) = (set m1 i x • set m2 i y) :=
  IsoFunStore.store_eq_of_Equiv insert_op_equiv

theorem disjoint_op_equiv_union {m1 m2 : T} (Hd : set_disjoint (dom m1) (dom m2)) :
    Equiv (m1 • m2) (union m1 m2) := by
  refine funext fun j => ?_
  simp [CMRA.op, Store.op, Heap.get_merge]
  rcases _ : get m1 j <;> cases _ : get m2 j <;> simp_all
  refine (Hd j ?_).elim
  simp_all [dom]

theorem disjoint_op_eq_union [IsoFunStore T K (Option V)] {m1 m2 : T} (H : set_disjoint (dom m1) (dom m2)) :
    m1 • m2 = Heap.union m1 m2 :=
  IsoFunStore.store_eq_of_Equiv (disjoint_op_equiv_union H)

theorem valid0_disjoint_dom {m1 m2 : T} (Hv : ✓{0} (m1 • m2)) (H : ∀ {k x}, get m1 k = some x → Exclusive x) :
    set_disjoint (dom m1) (dom m2) := by
  rintro k
  simp only [dom, Option.isSome]
  rcases HX : get m1 k with (_|x) <;> simp
  rcases HY : get m2 k with (_|y) <;> simp
  apply (H HX).1 y
  simp [CMRA.op, CMRA.ValidN] at Hv; specialize Hv k; revert Hv
  simp [Heap.get_merge, optionValidN, HX, HY]

theorem valid_disjoint_dom {m1 m2 : T} (Hv : ✓ (m1 • m2)) (H : ∀ {k x}, get m1 k = some x → Exclusive x) :
    set_disjoint (dom m1) (dom m2) :=
  valid0_disjoint_dom (Valid.validN Hv) H

theorem dom_op_union (m1 m2 : T) : dom (m1 • m2) = set_union (dom m1) (dom m2) := by
  refine funext fun k => ?_
  cases get m1 k <;> cases get m2 k <;> simp_all [CMRA.op, dom, set_union, get_merge]

theorem inc_dom_inc {m1 m2 : T} (Hinc : m1 ≼ m2) : set_included (dom m1) (dom m2) := by
  intro i; unfold Heap.dom
  rcases lookup_inc.mp Hinc i with ⟨z, Hz⟩; revert Hz
  cases get m1 i <;> cases get m2 i <;> cases z <;>
    simp [CMRA.op, optionOp]

nonrec instance [HD : CMRA.Discrete V] [Heap T K V] : Discrete T where
  discrete_0 {_ _} H := (OFE.Discrete.discrete_0 <| H ·)
  discrete_valid {_} := (CMRA.Discrete.discrete_valid <| · ·)

end Heap
