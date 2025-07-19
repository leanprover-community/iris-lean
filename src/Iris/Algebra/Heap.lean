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

-- TODO: Generic set theory library
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
def Store.Equiv [Store T K V] (t1 t2 : T) : Prop := get t1 = get t2

instance Equiv_trans [Store T K V] : Trans (Store.Equiv) (Store.Equiv (T := T)) (Store.Equiv) where
  trans := by simp_all [Store.Equiv]

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
  get_dmap : Store.get (dmap f t) k = f k (Store.get t k)
export HasStoreMap (dmap get_dmap)

/-- Map between heaps that preserves non-allocations.
Constructions like gmap_view need (HasHHMap T1 T2 K (DFrac F × V) V), but no maps between other types.
TODO: Simplify this somehow -/
class HasHHMap (T1 T2 : Type _) (K V1 V2 : outParam (Type _)) [Store T1 K (Option V1)] [Store T2 K (Option V2)] where
  hhmap (f : K → V1 → Option V2) : T1 → T2
  hhmap_get (f : K → V1 → Option V2) : Store.get (hhmap f t) k = (get t k).bind (f k)
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



theorem hmap_alloc [Heap T K V] {t : T} {k : K} {f : K → V → Option V} :
    get t k = some v → Store.get (Heap.hmap f t) k = f k v := by
  intro H
  simp [get_hmap, Option.bind, H]

theorem hmap_unalloc [Heap T K V] {t : T} {k : K} {f : K → V → Option V} :
    get t k = none → get (hmap f t) k = none := by
  intro H
  simp [get_hmap, Option.bind, H]

/-- Lift a predicate on store values to a predicate on heap values, which is true for undefined entries. -/
def toHeapPred (P : K → V → Prop) (k : K) : Option V → Prop
| .some v => P k v
| .none => True

/-- The heap of a single point -/
def Heap.point [Heap T K V] (k : K) (v : Option V) : T := Store.set empty k v

/-- Delete an element from a heap by setting its value to .none -/
def Heap.delete [Heap T K V] (t : T) (k : K) : T := Store.set t k none

/-- The domain of a heap is the set of keys that map to .some values. -/
def Heap.dom [Heap T K V] (t : T) : K → Prop := fun k => (Store.get t k).isSome

@[simp] def Heap.union [Heap T K V] (t1 t2 : T) : T :=
  Heap.merge (fun v1 _ => v1) t1 t2

theorem Heap.point_get_eq [Heap T K V] : k = k' → Store.get (Heap.point k v : T) k' = v := by
  intro H; unfold point; rw [@get_set_eq]; exact H

theorem Heap.point_get_ne [Heap T K V] : k ≠ k' → Store.get (Heap.point k v : T) k' = none := by
  intro H; unfold point; rw [@get_set_ne, get_empty]; exact H

/-- An AllocHeap is a heap which can allocate elements under some condition. -/
class AllocHeap (T : Type _) (K V : outParam (Type _)) extends Heap T K V where
  notFull : T → Prop
  fresh {t : T} : notFull t → K
  get_fresh  {H : notFull t} : Store.get t (fresh H) = none
export AllocHeap (notFull fresh get_fresh)

/-- An UnboundeHeap is a heap which can allocate an unbounded number of elements starting at empty. -/
class UnboundedHeap (T : Type _) (K V : outParam (Type _)) extends AllocHeap T K V where
  notFull_empty : notFull (empty : T)
  notFull_set_fresh {H : notFull t} : notFull (Store.set t (fresh H) v)
export UnboundedHeap (notFull_empty notFull_set_fresh)

section ofe
open OFE

/-- The OFE on Store types is the discrete function OFE on its .get function. -/
instance Store_OFE [Store T K V] [OFE V] : OFE T where
  Equiv s0 s1  := Store.get s0 ≡ Store.get s1
  Dist n s0 s1 := Store.get s0 ≡{n}≡ Store.get s1
  dist_eqv     := ⟨fun _ => .of_eq rfl, (·.symm), (·.trans ·)⟩
  equiv_dist   := equiv_dist
  dist_lt      := dist_lt

@[simp] def Store.toMap [Store T K V] [OFE V] : T -n> (K → V) where
  f x := Store.get x
  ne.1 {_ _ _} H k := H k

@[simp] def Store.ofMap [Store T K V] [R : RepFunStore T K V] [OFE V] : {f : K → V // R.rep f} -n> T where
  f x := ofFun x
  ne.1 {_ _ _} H k := by rw [get_ofFun, get_ofFun]; exact H k

instance get_ne [Store T K V] [OFE V] (k : K) : NonExpansive (Store.get · k : T → V) where
  ne {_ _ _} Ht := Ht k

instance [Store T K V] [OFE V] (k : K) : NonExpansive₂ (Store.set · k · : T → V → T) where
  ne {n v1 v2} Hv {t1 t2} Ht k' := by
    cases (Classical.em (k = k'))
    · rename_i H; rw [Store.get_set_eq H, Store.get_set_eq H]; exact Ht
    · rename_i H; rw [Store.get_set_ne H, Store.get_set_ne H]; exact Hv k'

theorem Store.eqv_of_Equiv [OFE V] [Store T K V] {t1 t2 : T} :
    Store.Equiv t1 t2 → t1 ≡ t2 := by
  intro H
  intro k
  rw [H]


-- TODO
-- instance [Store T K V] [OFE V] (op : V → V → V) [NonExpansive₂ op] :
--     NonExpansive₂ (Store.merge (T := T) op) where
--   ne n {_ _} Ht {_ _} Hs k := by simp only [Heap.get_merge]; exact NonExpansive₂.ne (Ht k) (Hs k)

instance [Store T1 K V1] [Store T2 K V2] [OFE V1] [OFE V2] (f : K → V1 → V2) [∀ k, NonExpansive (f k)] [HasStoreMap T1 T2 K V1 V2] :
    NonExpansive (dmap f : T1 → T2) where
  ne _ {_ _} H k := by simp only [get_dmap]; exact NonExpansive.ne (H k)

/-- COFE Instance for Stores that can StoreMap to themselves.
NOTE: This is not the COFE on Heaps. -/
instance Store_COFE [Store T K V] [HasStoreMap T T K V V] [COFE V] : COFE T where
  compl c := HasStoreMap.dmap (fun k _ => COFE.compl <| c.map ⟨(Store.get · k), get_ne k⟩) (c 0)
  conv_compl _ := by rw [get_dmap]; apply IsCOFE.conv_compl

/-- Project a chain of stores through it's kth coordinate to a chain of values. -/
def get_Chain [Store T K V] [OFE V] (k : K) (c : Chain T) : Chain V where
  chain i := get (c i) k
  cauchy Hni := c.cauchy Hni k

theorem get_Chain_get [Store T K V] [OFE V] (k : K) (c : Chain T) :
    (get_Chain k c) i = get (c i) k := by simp [get_Chain]

/-- COFE Instance for Heaps
NOTE: Not the same as the store COFE on Heaps. -/
instance Heap_COFE [Heap T K V] [COFE V] : COFE (T) where
  compl c :=
    let F : K → V → Option V := (fun k _ => COFE.compl <| c.map ⟨(Store.get · k : T → Option V), get_ne k⟩)
    Heap.hmap F (c 0)
  conv_compl {n c} k := by
    simp only []
    let c_proj := @get_Chain (T) K (Option V) _ _ k c
    cases Hc0 : Store.get (c.chain 0) k
    · have H1 := @chain_none_const V 0 _ c_proj ?G
      case G => rw [← Hc0]; rfl
      rw [hmap_unalloc Hc0]
      rw [← @get_Chain_get]
      suffices none ≡{n}≡ (c_proj).chain n by exact this
      rw [H1]
      rfl
    · rename_i val
      let H1 := @chain_option_some V 0 val _ c_proj ?G
      rcases H1 with ⟨c', Hc'⟩
      case G => rw [← Hc0]; rfl
      rw [hmap_alloc Hc0]
      rw [← @get_Chain_get]
      have HR : (get_Chain k c) = c_proj := by rfl
      rw [HR]
      rw [Hc']
      simp [Chain.map]
      have X := @IsCOFE.conv_compl (Option V) (by infer_instance) _ n c_proj
      rw [Hc'] at X
      simp at X
      refine .trans ?_ X
      exact Dist.of_eq (congrArg IsCOFE.compl Hc')

end ofe

section cmra

open CMRA

/- ## A CMRA on Heaps -/

variable [Heap T K V] [CMRA V]

instance [CMRA V] : OFE.NonExpansive₂ (Heap.merge (T := T) (K := K) (V := V) op) where
  ne _ x1 x2 Hx y1 y2 Hy := by
    intro i
    have Hx' := Hx i
    have Hy' := Hy i
    simp [get_merge]
    cases h1 : Store.get x1 i <;> cases h2 : Store.get y1 i <;>
    cases h3 : Store.get x2 i <;> cases h4 : Store.get y2 i <;>
    simp_all
    exact OFE.Dist.op Hx' Hy'

@[simp] def store_op (s1 s2 : T) : T := Heap.merge (K := K) CMRA.op s1 s2
@[simp] def store_unit : T := Heap.empty
@[simp] def store_pcore (s : T) : Option (T) := some <| Heap.hmap (fun _ => CMRA.pcore) s
@[simp] def store_valid (s : T) : Prop := ∀ k, ✓ (Store.get s k : Option V)
@[simp] def store_validN (n : Nat) (s : T) : Prop := ∀ k, ✓{n} (Store.get s k : Option V)

theorem lookup_includedN n (m1 m2 : T) :
  (∃ (z : T), m2 ≡{n}≡ store_op m1 z) ↔
  ∀ i, (∃ z, (Store.get m2 i) ≡{n}≡ (Store.get m1 i) • z) := by
  constructor
  · intros H i
    rcases H with ⟨z, Hz⟩
    exists (Store.get z i)
    simp_all [CMRA.op, optionOp]
    have Hz' := Hz i
    simp [Heap.get_merge] at Hz'
    generalize HX : Store.get m1 i = X
    generalize HZ : Store.get z i = Z
    rw [HX, HZ] at Hz'
    cases X <;> cases Z <;> simp_all
  · intro H
    rcases (Classical.axiomOfChoice H) with ⟨f, Hf⟩
    suffices ∃ z, ∀ (x : K), Store.get m2 x ≡{n}≡ Store.get (store_op m1 z) x by exact this
    suffices ∃ z, ∀ (x : K), Store.get m1 x • f x ≡{n}≡ Store.get (store_op m1 z) x by
      rcases this with ⟨tx, tH⟩
      exists tx; intro i
      exact (Hf i).trans (tH i)
    simp [CMRA.op, optionOp, get_merge]
    exists (hmap (fun k _ => f k) m2)
    intro i
    cases h : Store.get m2 i
    · rw [hmap_unalloc h]
      -- Both Store.get m1 x and f x are none? No
      cases hh : Store.get m1 i <;>
      cases hhh : f i <;> simp
      · have Hf' := Hf i
        rw [h, hh, hhh] at Hf'
        simp [CMRA.op, optionOp] at Hf'
      · have Hf' := Hf i
        rw [h, hh, hhh] at Hf'
        simp [CMRA.op, optionOp] at Hf'
    · rw [hmap_alloc h]
      cases hh : Store.get m1 i <;>
      cases hhh : f i <;> simp

theorem lookup_included {m1 m2 : T} :
  (∃ (z : T), m2 ≡ store_op m1 z) ↔
  ∀ i, (∃ z, (Store.get m2 i) ≡ (Store.get m1 i) • z) := by
  constructor
  · intros H i
    rcases H with ⟨z, Hz⟩
    exists (Store.get z i)
    simp_all [CMRA.op, optionOp]
    have Hz' := Hz i
    simp [Heap.get_merge,  ] at Hz'
    generalize HX : get m1 i = X
    generalize HZ : get z i = Z
    rw [HX, HZ] at Hz'
    cases X <;> cases Z <;> simp_all
  · intro H
    rcases (Classical.axiomOfChoice H) with ⟨f, Hf⟩
    suffices ∃ z, ∀ (x : K), Store.get m2 x ≡ Store.get (store_op m1 z) x by exact this
    suffices ∃ z, ∀ (x : K), Store.get m1 x • f x ≡ Store.get (store_op m1 z) x by
      rcases this with ⟨tx, tH⟩
      exists tx; intro i
      exact (Hf i).trans (tH i)
    simp [CMRA.op, optionOp, get_merge]
    exists (hmap (fun k _ => f k) m2)
    intro i
    cases h : Store.get m2 i
    · rw [hmap_unalloc h]
      -- Both Store.get m1 x and f x are none? No
      cases hh : Store.get m1 i <;>
      cases hhh : f i <;> simp
      · have Hf' := Hf i
        rw [h, hh, hhh] at Hf'
        simp [CMRA.op, optionOp] at Hf'
      · have Hf' := Hf i
        rw [h, hh, hhh] at Hf'
        simp [CMRA.op, optionOp] at Hf'
    · rw [hmap_alloc h]
      cases hh : Store.get m1 i <;>
      cases hhh : f i <;> simp


-- TODO: Fix this
theorem pcore_idemp_1 {x cx : T} : store_pcore x = some cx → store_pcore cx ≡ some cx := by
  refine (fun H => ?_)
  have H' : ((store_pcore ((store_pcore x).getD x)).getD ((store_pcore x).getD x)) ≡ ((store_pcore x).getD x) := by
    intro k
    rw [H]
    simp only [Option.getD_some, get_dmap]
    simp [store_pcore] at H
    rw [← H]
    generalize HX : Store.get x k = X
    cases X <;> simp
    · rw [hmap_unalloc HX]
      rw [H]
      cases h : Store.get cx k
      · rw [hmap_unalloc h]
      · rw [hmap_alloc h]
        rw [← H] at h
        rw [hmap_unalloc HX] at h
        cases h
    rename_i v
    generalize HY : pcore v = Y
    cases Y
    · conv=>
        rhs
        rw [hmap_alloc HX]
      rw [HY]
      rw [H]
      cases h : Store.get cx k
      · rw [hmap_unalloc h]
      · exfalso
        rw [← H] at h
        rw [hmap_alloc HX] at h
        simp_all
    have Hidem := pcore_idem HY
    simp_all
    cases h : Store.get cx k
    · rw [hmap_unalloc h]
    · rw [hmap_alloc h]
      rw [← H] at h
      rw [hmap_alloc HX] at h
      simp_all
  apply (H ▸ H')

def pcore_extend_1 {n : Nat} {x y1 y2 : T} : store_validN n x → x ≡{n}≡ store_op y1 y2 → (z1 : T) ×' (z2 : T) ×' x ≡ store_op z1 z2 ∧ z1 ≡{n}≡ y1 ∧ z2 ≡{n}≡ y2 := by
  intro Hm Heq
  have F (i : K) := @CMRA.extend (Option V) _ n (Store.get x i) (Store.get y1 i) (Store.get y2 i) (Hm i) ?G
  case G =>
    apply ((get_ne (T := T) i).ne Heq).trans
    simp [CMRA.op, optionOp, get_merge]
    cases HX : Store.get y1 i <;> cases HY : Store.get y2 i <;> simp
  let FF1 (k : K) (_ : V) := (F k |>.fst)
  let FF2 (k : K) (_ : V) := (F k |>.snd.fst)
  exists hmap FF1 y1
  exists hmap FF2 y2
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
    <;> simp [store_op, get_merge]
    <;> rcases hF : (F i) with ⟨z1, z2, Hm, Hz1, Hz2⟩
  · refine Hm.trans ?_
    simp [CMRA.op, optionOp]
    cases z1 <;> cases z2 <;> simp_all [FF1, FF2] <;> cases h1 : Store.get y1 i <;> simp [h1] at Hz1 <;> cases h2 : Store.get y2 i <;> simp [h2] at Hz2
    · rw [hmap_unalloc h1]
      rw [hmap_unalloc h2]
      simp
    · rw [hmap_unalloc h1]
      rw [hmap_alloc h2]
      rw [hF]
      simp
    · rw [hmap_alloc h1]
      rw [hmap_unalloc h2]
      rw [hF]
      simp
    · rw [hmap_alloc h1]
      rw [hmap_alloc h2]
      rw [hF]
      simp
  · cases h : Store.get y1 i
    · rw [hmap_unalloc h]
    · rw [hmap_alloc h]
      rw [← h]
      refine .trans ?_ Hz1
      unfold FF1
      rw [hF]
  · cases h : Store.get y2 i
    · rw [hmap_unalloc h]
    · rw [hmap_alloc h]
      rw [← h]
      refine .trans ?_ Hz2
      unfold FF2
      rw [hF]

instance StoreO_CMRA : CMRA (T) where
  pcore := store_pcore
  op := store_op
  ValidN := store_validN
  Valid := store_valid
  op_ne := by
    intro x
    constructor
    intro n x1 x2 H1 i
    simp [store_op, get_merge]
    have H1' := H1 i
    revert H1'
    cases Store.get x1 i <;>
    cases Store.get x2 i <;>
    simp
    intro H
    cases (Store.get x i) <;> simp
    · trivial
    · apply op_right_dist; trivial
  pcore_ne {n x y cx} H := by
    simp only [store_pcore, Option.some.injEq, exists_eq_left']
    refine (· ▸ fun k => ?_)
    have H := H k
    revert H
    cases hx : Store.get x k <;> cases hy : Store.get y k <;> simp
    · rw [hmap_unalloc hx, hmap_unalloc hy]
    · rw [hmap_alloc hx, hmap_alloc hy]
      intro H1
      exact OFE.NonExpansive.ne H1
  validN_ne Hx H k := CMRA.validN_ne (OFE.NonExpansive.ne (f := (Store.get · k : T → Option V)) Hx) (H k)
  valid_iff_validN {x} :=
    ⟨fun H n k => valid_iff_validN.mp (H k) n, fun H k => valid_iff_validN.mpr (H · k)⟩
  validN_succ H k := validN_succ (H k)
  validN_op_left {n x1 x2} H k := by
    apply CMRA.validN_op_left (y := Store.get x2 k)
    simp [CMRA.op, optionOp, store_validN, Heap.get_merge,  ] at ⊢ H
    have H' := H k
    generalize HX : Store.get x1 k = X
    generalize HY : Store.get x2 k = Y
    simp_all
    cases X <;> cases Y <;> simp_all [CMRA.op, optionOp]
  assoc := by
    rintro x y z k
    simp [store_op, Heap.get_merge]
    cases h1 : Store.get x k <;>
    cases h2 : Store.get y k <;>
    cases h3 : Store.get z k <;>
    simp_all
    apply assoc
  comm := by
    rintro x y k
    simp [store_op, Heap.get_merge]
    cases h1 : Store.get x k <;>
    cases h2 : Store.get y k <;>
    simp_all
    exact comm
  pcore_op_left {x cx} := by
    refine (fun H => ?_)
    have H' : store_op ((store_pcore x).getD x) x ≡ x := by
      intro k
      simp [store_op, store_pcore, store_op, get_merge]
      simp [store_pcore] at H
      rw [H]
      cases hcx : Store.get cx k <;> cases hx : Store.get x k <;> simp
      · rw [← H] at hcx
        rw [hmap_unalloc hx] at hcx
        cases hcx
      · apply pcore_op_left
        rename_i val1 val2
        have HH : Store.get (hmap (fun x => pcore) x) k = Store.get cx k := by rw [H]
        rw [hcx] at HH
        rw [hmap_alloc hx] at HH
        trivial
    apply (H ▸ H')
  pcore_idem {x cx} := by exact pcore_idemp_1
  pcore_op_mono := by
    apply pcore_op_mono_of_core_op_mono
    let core' (x : T) := (store_pcore x).getD x
    let le' (x y : T) := ∃ z, y ≡ store_op x z

    -- First direction, no countability used
    have Hcore'le'1 (x y : T) : le' x y → ∀ (i : K), (Store.get x i ≼ Store.get y i) := by
      intros H i
      rcases H with ⟨z, Hz⟩
      exists (Store.get z i)
      simp_all [CMRA.op, optionOp]
      have Hz' := Hz i
      simp [Heap.get_merge,  ] at Hz'
      generalize HX : Store.get x i = X
      generalize HZ : Store.get z i = Z
      rw [HX, HZ] at Hz'
      cases X <;> cases Z <;> simp_all

    suffices ∀ x y : T, le' x y → le' (core' x) (core' y) by
      rintro x cx y Hxy' Hx
      have Hxy := this x y Hxy'
      unfold core' at Hxy
      simp [Hx] at Hxy
      simp [store_pcore]
      rcases Hxy with ⟨vv, Hvv⟩
      exists vv
      apply Hvv.trans
      intro i
      simp [get_merge]
      cases Store.get vv i <;> cases Store.get x i <;> simp_all
    intro x y H'
    unfold le'
    refine lookup_included.mpr ?_
    intro i
    suffices (core (Store.get x i)) ≼ (core (Store.get y i)) by
      simp_all [core', core, get_dmap]
      rcases this with ⟨vv, Hvv⟩
      exists vv
      simp_all [pcore, optionCore, Hvv]
      cases hx : Store.get x i <;> cases hy : Store.get y i <;> simp_all
      · simp [hmap_unalloc hx, hmap_unalloc hy, Hvv]
      · simp [hmap_unalloc hx, hmap_alloc hy, Hvv]
      · simp [hmap_alloc hx, hmap_unalloc hy, Hvv]
      · simp [hmap_alloc hx, hmap_alloc hy, Hvv]
    exact core_mono (Hcore'le'1 x y H' i)

  extend := fun {n} {x y₁ y₂} a a_1 => pcore_extend_1 a a_1

instance StoreO_UCMRA : UCMRA (T) where
  unit := store_unit
  unit_valid := by simp [CMRA.Valid, store_valid, optionValid, store_unit, Heap.get_empty]
  unit_left_id := by
    intro x k
    simp [CMRA.op, Heap.get_merge, store_unit, Heap.get_empty]
  pcore_unit := by
    intro k
    simp [CMRA.pcore, get_dmap, store_unit, Heap.get_empty]
    rw [hmap_unalloc Heap.get_empty]

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
      simp [store_op, get_merge]
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
  unfold Store.Equiv
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
        simp [CMRA.op, op, store_op, get_merge, Heap.point_get_ne He, get_set_ne (T := T) He]

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
  simp_all [CMRA.op, store_op, get_merge]
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
    Store.Equiv ((Store.set (m1 • m2) i (x • y))) ((Store.set m1 i x) • (Store.set m2 i y)) := by
  simp [Store.Equiv, Store.Equiv]
  apply funext
  intro j
  if He : i = j
    then
      simp [CMRA.op, get_set_eq (T := T) He, get_merge]
      simp [optionOp]
      cases x <;> cases y <;> simp_all
    else simp [CMRA.op, get_set_ne (T := T) He, Heap.get_merge]

theorem insert_op_eq [IsoFunStore (T) K (Option V)] {m1 m2 : T} : (Store.set (m1 • m2) i (x • y)) = (Store.set m1 i x) • (Store.set m2 i y) :=
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
  simp [CMRA.op, op, CMRA.ValidN, store_validN] at Hv
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
  simp [CMRA.op, op, CMRA.ValidN, store_validN] at Hv
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
  rcases lookup_included.mp Hinc i with ⟨z, Hz⟩
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

end heap_laws
