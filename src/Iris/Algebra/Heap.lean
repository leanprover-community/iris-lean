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

section heap_laws

variable {K V : Type _} [Heap T K V] [CMRA V]
open CMRA

theorem lookup_validN_Some {m : T} : ✓{n} m → Store.get m i ≡{n}≡ some x → ✓{n} x := by
  suffices ✓{n} Store.get m i → Store.get m i ≡{n}≡ some x → ✓{n} x by
    exact fun Hv => (this (Hv i) ·)
  simp only [ValidN, optionValidN]
  split <;> rename_i He <;> rw [He]
  · exact fun Hv => (·.validN |>.mp Hv)
  · rintro _ ⟨⟩

theorem lookup_valid_Some {m : T} (Hv : ✓ m) (He : Store.get m i ≡ some x) : ✓ x :=
  valid_iff_validN.mpr (fun _ => lookup_validN_Some Hv.validN He.dist)

theorem insert_validN {m : T} (Hx : ✓{n} x) (Hm : ✓{n} m) : ✓{n} (Store.set m i x) := by
  intro k
  simp [CMRA.ValidN]
  if He : i = k
    then rw [get_set_eq (T := T) He]; exact Hx
    else rw [get_set_ne (T := T) (He ·)]; apply Hm

theorem insert_valid {m : T} (Hx : ✓ x) (Hm : ✓ m) : ✓ (Store.set m i x) :=
  valid_iff_validN.mpr (fun _ => insert_validN Hx.validN Hm.validN)

theorem point_valid : ✓ (Heap.point i x : T) ↔ ✓ x := by
  simp only [Heap.point, Store.get]
  constructor <;> intro H
  · have H' := H i; simp [Heap.point_get_eq rfl] at H'; rw [get_set_eq (T := T) rfl] at H'; exact H'
  · intro k
    if He : i = k
      then rw [get_set_eq (T := T) He]; trivial
      else rw [get_set_ne (T := T) He, Heap.get_empty]; trivial

theorem point_validN : ✓{n} (Heap.point i x : T) ↔ ✓{n} x := by
  simp only [Heap.point, Store.get]
  constructor <;> intro H
  · have H' := H i; simp [Heap.point_get_eq rfl] at H'; rw [get_set_eq (T := T) rfl] at H'; exact H'
  · intro k
    if He : i = k
      then rw [get_set_eq (T := T) He]; trivial
      else rw [get_set_ne (T := T) He, Heap.get_empty]; trivial

theorem delete_validN {m : T} (Hv : ✓{n} m) : ✓{n} (Heap.delete m i) := by
  intro k
  if He : i = k
    then simp only [Heap.delete]; rw [Store.get_set_eq (T := T) He]; trivial
    else simp only [Heap.delete]; rw [Store.get_set_ne (T := T) He]; exact Hv k

theorem delete_valid {m : T} (Hv : ✓ m) : ✓ (Heap.delete m i) :=
  valid_iff_validN.mpr (fun _ => delete_validN Hv.validN)

theorem insert_point_op {m : T} (Hemp : Store.get m i = none) :
    Store.Equiv (Store.set m i x) (Heap.point i x • m) := by
  simp_all [CMRA.op, op, Store.Equiv]
  refine funext (fun k => ?_)
  if He : i = k
    then
      rw [Store.get_set_eq (T := T) He]
      simp only [get_merge]
      rw [Heap.point_get_eq He, He.symm, Hemp]
      unfold Option.merge
      split
      · rfl
      · rfl
      · rename_i Hk; rcases Hk
      · rename_i Hk; rcases Hk
    else
      rw [Store.get_set_ne (T := T) He]
      simp [Store.op, get_merge]
      rw [Heap.point_get_ne He]
      unfold Option.merge
      split <;> trivial

theorem insert_point_op_eq [IsoFunStore (T) K (Option V)] {m : T} (Hemp : Store.get m i = none) :
    Store.set m i x = Heap.point i x • m :=
  IsoFunStore.store_eq_of_Equiv (insert_point_op Hemp)

theorem point_core {i : K} {x : V} {cx} (Hpcore : pcore x = some cx) :
    Store.Equiv (core (Heap.point i (some x) : T)) ((Heap.point i (some cx) : T)) := by
  simp [core, pcore]
  rw [← Hpcore]
  apply funext
  intro k
  if He : i = k
    then simp [Heap.point_get_eq He, hmap_alloc]
    else simp [Heap.point_get_ne He, hmap_unalloc]

theorem point_core_eq [IsoFunStore (T) K (Option V)] {i : K} {x : V} {cx} (Hpcore : pcore x = some cx) :
    core (Heap.point i (some x) : T) = (Heap.point i (some cx) : T) :=
  IsoFunStore.store_eq_of_Equiv (point_core Hpcore)

theorem point_core' {i : K} {x : V} {cx} (Hpcore : pcore x ≡ some cx) :
    core (Heap.point i (some x)) ≡ (Heap.point i (some cx) : T) := by
  simp [core, pcore]
  intro k
  if He : i = k
    then simp [Heap.point_get_eq He, hmap_alloc]; exact Hpcore
    else simp [Heap.point_get_ne He, hmap_unalloc]

theorem point_core_total [IsTotal V] {i : K} {x : V} :
    Store.Equiv (core (Heap.point i (some x) : T)) ((Heap.point i (some (core x)))) := by
  obtain ⟨xc, Hxc⟩ := total x
  apply (point_core Hxc).trans
  simp [core, Hxc]

theorem point_core_total_eq [IsTotal V] [IsoFunStore (T) K (Option V)] {i : K} {x : V} :
    core (Heap.point i (some x) : T) = (Heap.point i (some (core x))) :=
  IsoFunStore.store_eq_of_Equiv point_core_total

theorem point_op {i : K} {x y : V} :
    Store.Equiv ((Heap.point i (some x) : T) • (Heap.point i (some y))) ((Heap.point i (some (x • y)))) := by
  unfold Store.Equiv
  apply funext
  intro k
  simp [op]
  simp [Heap.get_merge]
  if He : i = k
    then
      rw [Heap.point_get_eq He]
      rw [Heap.point_get_eq He]
      simp only [Option.merge]
      rw [Heap.point_get_eq He]
    else
      rw [Heap.point_get_ne He]
      rw [Heap.point_get_ne He]
      simp only [Option.merge]
      rw [Heap.point_get_ne He]

theorem point_op_eq [IsoFunStore (T) K (Option V)] {i : K} {x y : V} :
    (Heap.point i (some x) : T) • (Heap.point i (some y)) = (Heap.point i (some (x • y))) :=
  IsoFunStore.store_eq_of_Equiv point_op

theorem gmap_core_id {m : T} (H : ∀ i (x : V), (Store.get m i = some x) → CoreId x) : CoreId m := by
  constructor
  intro i
  simp [HasStoreMap.get_dmap]
  cases H' : Store.get m i
  · rw [hmap_unalloc H']
  · rw [hmap_alloc H']
    exact (H _ _ H').core_id

instance gmap_core_id' {m : T} (H : ∀ x : V, CoreId x) : CoreId m := by
  constructor
  intro i
  simp [get_dmap]
  cases H' : Store.get m i
  · rw [hmap_unalloc H']
  · rw [hmap_alloc H']
    apply (H _).core_id

instance gmap_point_core_id (H : CoreId (x : V)) : CoreId (Heap.point i (some x) : T) := by
  constructor
  intro k
  simp [get_dmap]
  if He : i = k
    then
      rw [Heap.point_get_eq He]
      rw [hmap_alloc (Heap.point_get_eq He)]
      exact H.core_id
    else
      rw [Heap.point_get_ne He]
      rw [hmap_unalloc (Heap.point_get_ne He)]

theorem point_includedN_l {m : T} :
    (Heap.point i (some x) : T) ≼{n} m ↔ ∃ y, (Store.get m i ≡{n}≡ some y) ∧ some x ≼{n} some y := by
  constructor
  · rintro ⟨z, Hz⟩
    have Hz' := Hz i
    simp [CMRA.op, op] at Hz'
    simp [get_merge,  ] at Hz'
    rw [Heap.point_get_eq rfl] at Hz'
    generalize Hz0 : Store.get z i = z0
    cases z0 <;> simp [Hz0] at Hz'
    · exists x
    · rename_i v
      exists (x • v)
      refine ⟨Hz', ?_⟩
      exists v
  · rintro ⟨y, Hy, z, Hz⟩
    exists Store.set m i z
    intro j
    if He : i = j
      then
        simp [Heap.point]
        simp [Store.get, He] at Hy
        refine Hy.trans (Hz.trans ?_)
        simp [CMRA.op, Heap.get_merge, Heap.point_get_eq He, get_set_eq (T := T) He,  ]
        cases z <;> simp [optionOp]
      else
        simp [CMRA.op]
        simp [get_merge, Heap.point_get_ne He, Store.get_set_ne (T := T) He]

theorem point_included_l {m : T} :
    (Heap.point i (some x) : T) ≼ m ↔ ∃ y, (Store.get m i ≡ some y) ∧ some x ≼ some y := by
  constructor
  · rintro ⟨z, Hz⟩
    have Hz' := Hz i
    simp [CMRA.op, op] at Hz'
    simp [Heap.get_merge] at Hz'
    rw [Heap.point_get_eq rfl] at Hz'
    generalize Hz0 : Store.get z i = z0
    cases z0 <;> simp [Hz0] at Hz'
    · exists x
    · rename_i v
      exists (x • v)
      refine ⟨Hz', ?_⟩
      exists v
  · rintro ⟨y, Hy, z, Hz⟩
    exists Store.set m i z
    intro j
    if He : i = j
      then
        rw [He] at Hy
        refine Hy.trans (Hz.trans ?_)
        simp [CMRA.op, Heap.get_merge, Heap.point_get_eq He, get_set_eq (T := T) He, optionOp]
        cases z <;> simp
      else
        simp [ ]
        simp [CMRA.op, op, Store.op, get_merge, Heap.point_get_ne He, get_set_ne (T := T) He]

theorem point_included_exclusive_l {m : T} (He : Exclusive x) (Hv : ✓ m) :
    (Heap.point i (some x) : T) ≼ m ↔ (Store.get m i ≡ some x) := by
  apply point_included_l.trans
  constructor
  · rintro ⟨y, Hy, Hxy⟩
    suffices x ≡ y by apply Hy.trans this.symm
    exact some_inc_exclusive Hxy <| lookup_valid_Some Hv Hy
  · intro _; exists x

theorem point_included :
    (Heap.point i (some x) : T) ≼ (Heap.point i (some y)) ↔ some x ≼ some y := by
  apply point_included_l.trans
  constructor
  · rintro ⟨z, Hz, Hxz⟩
    rw [Heap.point_get_eq rfl] at Hz
    exact inc_of_inc_of_eqv Hxz Hz.symm
  · intro H
    exists y
    rw [Heap.point_get_eq rfl]
    exact ⟨.rfl, H⟩

theorem point_included_total [IsTotal V] :
    (Heap.point i (some x) : T) ≼ (Heap.point i (some y))  ↔ x ≼ y :=
  point_included.trans <| some_inc_total.trans <| Eq.to_iff rfl

theorem point_included_mono (Hinc : x ≼ y) : (Heap.point i (some x) : T) ≼ (Heap.point i (some y)) :=
  point_included.mpr <| some_inc.mpr <| .inr Hinc

instance point_cancelable (H : Cancelable (some x)) : Cancelable (Heap.point i (some x) : T) := by
  constructor
  intro n m1 m2 Hv He j
  have Hv' := Hv j; clear Hv
  have He' := He j; clear He
  simp_all [CMRA.op, Store.op, get_merge]
  if He : i = j
    then
      rw [Heap.point_get_eq He] at *
      apply H.cancelableN
      · generalize HX : Store.get m1 j = X
        rw [HX] at Hv'
        cases X <;> simp_all [CMRA.op, op, optionOp]
      · generalize HX : (Store.get m1 j) = X
        generalize HY : (Store.get m2 j) = Y
        rw [HX, HY] at He'
        cases X <;> cases Y <;> simp_all [CMRA.op, optionOp]
    else
      rw [Heap.point_get_ne He] at *
      generalize HX : Store.get m1 j =  X
      generalize HY : (Store.get m2 j) = Y
      rw [HX, HY] at He'
      rw [HX] at Hv'
      cases X <;> cases Y <;> simp_all [CMRA.op, optionOp]

instance heap_cancelable {m : T} [Hid : ∀ x : V, IdFree x] [Hc : ∀ x : V, Cancelable x] : Cancelable m := by
  constructor
  intro n m1 m2 Hv He i
  apply CMRA.cancelableN (x := Store.get m i)
  · have Hv' := Hv i
    simp [CMRA.op, op] at Hv'
    simp [Heap.get_merge] at Hv'
    generalize HX : (Store.get m i) = X
    generalize HY : (Store.get m1 i) = Y
    simp_all [CMRA.op, op, optionOp]
    cases X <;> cases Y <;> simp_all
  · have He' := He i
    simp_all [CMRA.op, op, optionOp]
    simp [Heap.get_merge] at He'
    generalize HX : (Store.get m i) = X
    generalize HY : (Store.get m1 i) = Y
    generalize HZ : (Store.get m2 i) = Z
    rw [HX, HY] at He'
    cases X <;> cases Y <;> cases Z <;> simp_all [Heap.get_merge,  ]

theorem insert_op {m1 m2 : T} :
    Store.Equiv ((Store.set (m1 • m2 : T) i (x • y : Option V))) ((Store.set m1 i x) • (Store.set m2 i y) : T) := by
  simp [Store.Equiv, Store.Equiv]
  apply funext
  intro j
  if He : i = j
    then
      simp [CMRA.op, get_set_eq (T := T) He, get_merge]
      simp [optionOp]
      cases x <;> cases y <;> simp_all
    else simp [CMRA.op, get_set_ne (T := T) He, Heap.get_merge]

theorem insert_op_eq [IsoFunStore (T) K (Option V)] {m1 m2 : T} : (Store.set (m1 • m2) i (x • y : Option V)) = (Store.set m1 i x) • (Store.set m2 i y) :=
  IsoFunStore.store_eq_of_Equiv insert_op

theorem gmap_op_union {m1 m2 : T} : set_disjoint (Heap.dom m1) (Heap.dom m2) →
    Store.Equiv (m1 • m2) (Heap.union m1 m2) := by
  intro Hd
  simp [Store.Equiv]
  apply funext
  intro j
  simp [CMRA.op, op, Heap.get_merge,  ]
  generalize HX : Store.get m2 j = X
  generalize HY : Store.get m1 j = Y
  cases X <;> cases Y <;> simp_all
  exfalso
  apply Hd j
  simp [Heap.dom, HX, HY]

theorem gmap_op_union_eq [IsoFunStore (T) K (Option V)] {m1 m2 : T} (H : set_disjoint (Heap.dom m1) (Heap.dom m2)) :
    m1 • m2 = Heap.union m1 m2 :=
  IsoFunStore.store_eq_of_Equiv (gmap_op_union H)

theorem gmap_op_valid0_disjoint {m1 m2 : T} (Hv : ✓{0} (m1 • m2)) (H : ∀ k x, Store.get m1 k = some x → Exclusive x) :
    set_disjoint (Heap.dom m1) (Heap.dom m2) := by
  rintro k
  simp [Heap.dom, Option.isSome]
  generalize HX : Store.get m1 k = X
  cases X <;> simp
  rename_i x
  have H' := H _ _ HX
  generalize HY : Store.get m2 k = Y
  cases Y <;> simp_all
  rcases H' with ⟨Hex⟩
  rename_i xx
  apply Hex xx
  simp [CMRA.op, op, CMRA.ValidN, Store.validN] at Hv
  have Hv' := Hv k
  simp [Heap.get_merge, optionValidN, HX, HY] at Hv'
  exact Hv'

-- TODO: Redundant proof from gmap_op_valid0_disjoint
theorem gmap_op_valid_disjoint {m1 m2 : T} (Hv : ✓ (m1 • m2)) (H : ∀ k x, Store.get m1 k = some x → Exclusive x) :
    set_disjoint (Heap.dom m1) (Heap.dom m2) := by
  rintro k
  simp [Heap.dom, Option.isSome]
  generalize HX : Store.get m1 k = X
  cases X <;> simp
  rename_i x
  have H' := H _ _ HX
  generalize HY : Store.get m2 k = Y
  cases Y <;> simp_all
  rcases H' with ⟨Hex⟩
  rename_i xx
  apply Hex xx
  simp [CMRA.op, op, CMRA.ValidN, Store.validN] at Hv
  have Hv' := Hv k
  simp [Heap.get_merge, optionValidN, HX, HY] at Hv'
  exact Valid.validN Hv'

theorem dom_op (m1 m2 : T) : Heap.dom (m1 • m2) = set_union (Heap.dom m1) (Heap.dom m2) := by
  refine (funext fun k => ?_)
  simp only [CMRA.op, op, Heap.dom, set_union, Heap.get_merge,  ]
  generalize HX : Store.get m1 k = X
  generalize HY : Store.get m2 k = Y
  cases X <;> cases Y <;> simp_all [get_merge]

theorem dom_included {m1 m2 : T} (Hinc : m1 ≼ m2) : set_included (Heap.dom m1) (Heap.dom m2) := by
  intro i
  rcases lookup_inc.mp Hinc i with ⟨z, Hz⟩
  simp [Heap.dom]
  simp [OFE.Equiv, Option.Forall₂] at Hz
  generalize HX : Store.get m1 i = X
  generalize HY : Store.get m2 i = Y
  cases X <;> cases Y <;> simp
  simp [HX, HY, CMRA.op, op, optionOp] at Hz
  cases z <;> simp at Hz

-- theorem StoreO.map_mono [CMRA V'] [Heap T' K V'] {f : Option V → Option V'} {m1 m2 : StoreO T}
--     (H1 : ∀ v1 v2 : V, v1 ≡ v2 → f v1 ≡ f v2)  (H2 : ∀ x y, x ≼ y → f x ≼ f y) (H3 : m1 ≼ m2) :
--     (StoreO.map f m1 : StoreO T') ≼ StoreO.map f m2 := by
--   s orry

nonrec instance [HD : CMRA.Discrete V] [Heap T K V] : Discrete T where
  discrete_0 {m1 m2} H := by
    intro k
    apply OFE.Discrete.discrete_0
    exact H k
  discrete_valid := by
    intro H HH k
    exact CMRA.Discrete.discrete_valid (α := Option V) (HH k)

end heap_laws
