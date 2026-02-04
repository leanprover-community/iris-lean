/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE
import Iris.Std.Set
import Iris.Std.Heap
import Iris.Std.PartialMap

open Iris Std

section OFE

open OFE

namespace Store

instance instOFE [PartialMap M K] [OFE V] : OFE (M V) where
  Equiv s0 s1  := get? s0 ≡ get? s1
  Dist n s0 s1 := get? s0 ≡{n}≡ get? s1
  dist_eqv     := ⟨fun _ => .of_eq rfl, (·.symm), (·.trans ·)⟩
  equiv_dist   := equiv_dist
  dist_lt      := dist_lt

@[simp] def toMap [PartialMap M K] [OFE V] : (M V) -n> (K → Option V) where
  f x := get? x
  ne.1 {_ _ _} H k := H k

@[simp] def ofMap [PartialMap M K] [R : RepFunMap M K] [OFE V] :  (K → Option V) -n> (M V) where
  f x := of_fun x
  ne.1 {_ _ _} H k := by simp only [get_of_fun, H k]

instance get_ne [PartialMap M K] [OFE V] (k : K) : NonExpansive (get? · k : M V → Option V) where
  ne {_ _ _} Ht := Ht k

instance [PartialMap M K] [LawfulPartialMap M K] [OFE V] (k : K) : NonExpansive₂ (insert · k · : M V → V → M V) where
  ne {_ _ _} Hv {_ _} Ht k' := by
    by_cases h : k = k'
    · simp [get?_insert_eq h, Ht]
    · simp [get?_insert_ne h, Hv k']

theorem eqv_of_Equiv [OFE V] [PartialMap M K] {t1 t2 : M V} (H : PartialMap.equiv t1 t2) : t1 ≡ t2 :=
  (.of_eq <| H ·)

instance [Heap M K] [OFE V] (op : V → V → V) [NonExpansive₂ op] :
    NonExpansive₂ (merge (M := M) op) where
  ne _ {_ _} Ht {_ _} Hs k := by simp only [get?_merge]; exact NonExpansive₂.ne (Ht k) (Hs k)

-- instance [Store T1 K V1] [Store T2 K V2] [OFE V1] [OFE V2] (f : K → V1 → V2)
--   [∀ k, NonExpansive (f k)] [HasStoreMap T1 T2 K V1 V2] : NonExpansive (dmap f : T1 → T2) where
--   ne _ {_ _} H k := by simp only [get_dmap]; exact NonExpansive.ne (H k)

/-- Project a chain of stores through its kth coordinate to a chain of values. -/
def chain [Heap M K] [OFE V] (k : K) (c : Chain (M V)) : Chain (Option V) where
  chain i := get? (c i) k
  cauchy Hni := c.cauchy Hni k

theorem chain_get [Heap M K] [OFE V] (k : K) (c : Chain (M V)) :
    (chain k c) i = get? (c i) k := by simp [chain]

end Store

instance Heap.instCOFE [Functor M] [Heap M K] [COFE V] : COFE (M V) where
  compl c := (fun v => sorry) <$> (c 0) --  <$> (c 0) -- (fun x y => COFE.compl <| c.map ⟨PartialMap.get?, Store.get_ne y⟩)
  conv_compl {_ c} k := by
    sorry
    -- rw [get_hmap]
    -- rcases H : get (c.chain 0) k
    -- · simp [← Store.chain_get, chain_none_const (c := Store.chain k c) (n := 0) (H▸rfl)]
    -- · exact IsCOFE.conv_compl

end OFE

section CMRA
open CMRA

/- ## A CMRA on Heaps -/

namespace Store

variable [PartialMap M K] [CMRA V]

@[simp] def op (s1 s2 : T) : T := merge (K := K) CMRA.op s1 s2
@[simp] def unit : T := empty
@[simp] def pcore (s : T) : Option T := some <| hmap (fun _ => CMRA.pcore) s
@[simp] def valid (s : T) : Prop := ∀ k, ✓ (get s k : Option V)
@[simp] def validN (n : Nat) (s : T) : Prop := ∀ k, ✓{n} (get s k : Option V)

theorem lookup_incN {n} {m1 m2 : T} :
    (∃ (z : T), m2 ≡{n}≡ op m1 z) ↔
    ∀ i, (∃ z, (get m2 i) ≡{n}≡ (get m1 i) • z) := by
  refine ⟨fun ⟨z, Hz⟩ i => ?_, fun H => ?_⟩
  · refine ⟨get z i, ?_⟩
    refine .trans (get_ne i |>.ne Hz) ?_
    simp only [op, CMRA.op, get_merge]
    cases get m1 i <;> cases get z i <;> simp
  · obtain ⟨f, Hf⟩ := Classical.axiomOfChoice H
    exists hmap (fun k _ => f k) m2
    refine fun i => (Hf i).trans ?_
    specialize Hf i; revert Hf
    simp [CMRA.op, get_merge, get_hmap]
    cases get m2 i <;> cases get m1 i <;> cases f i <;> simp

theorem lookup_inc {m1 m2 : T} :
    (∃ (z : T), m2 ≡ op m1 z) ↔
    ∀ i, (∃ z, (get m2 i) ≡ (get m1 i) • z) := by
  refine ⟨fun ⟨z, Hz⟩ i => ?_, fun H => ?_⟩
  · refine ⟨get z i, ?_⟩
    refine .trans (get_ne i |>.eqv Hz) ?_
    simp only [CMRA.op, op, get_merge]
    cases get m1 i <;> cases get z i <;> simp
  · obtain ⟨f, Hf⟩ := Classical.axiomOfChoice H
    exists hmap (fun k _ => f k) m2
    refine fun i => (Hf i).trans ?_
    specialize Hf i; revert Hf
    simp [CMRA.op, optionOp, get_merge, get_hmap]
    cases get m2 i <;> cases get m1 i <;> cases f i <;> simp

open OFE in
instance instStoreCMRA : CMRA T where
  pcore := pcore
  op := op
  ValidN := validN
  Valid := valid
  op_ne.ne _ x1 x2 H i := by
    rename_i x _
    specialize H i; revert H
    simp [get_merge]
    cases get x1 i <;> cases get x2 i <;> cases get x i <;> simp
    apply op_right_dist
  pcore_ne {n x y _} H := by
    simp only [pcore, Option.some.injEq, exists_eq_left']
    refine (· ▸ fun k => ?_); specialize H k; revert H
    rw [get_hmap, get_hmap]
    cases get x k <;> cases get y k <;> simp
    exact (NonExpansive.ne ·)
  validN_ne Hx H k :=
    validN_ne (NonExpansive.ne (f := (get · k : T → Option V)) Hx) (H k)
  valid_iff_validN :=
    ⟨fun H n k => valid_iff_validN.mp (H k) n,
     fun H k => valid_iff_validN.mpr (H · k)⟩
  validN_succ H k := validN_succ (H k)
  validN_op_left {n x1 x2} H k := by
    refine validN_op_left (y := get x2 k) ?_
    specialize H k; revert H
    simp only [op, get_merge, Option.merge]
    cases get x1 k <;> cases get x2 k <;> simp [optionOp, CMRA.op]
  assoc {x y z} k := by
    simp only [op, get_merge]
    cases get x k <;> cases get y k <;> cases get z k <;> simp
    exact assoc
  comm {x y} k := by
    simp [op, Heap.get_merge]
    cases get x k <;> cases get y k <;> simp
    exact comm
  pcore_op_left {x cx} H k := by
    simp only [← Option.getD_some (a := cx) (b := cx), op, get_merge]
    cases Hcx : get cx k <;> cases hx : get x k <;>
      simp <;>
      simp only [pcore, Option.some.injEq] at H
    · rw [← H, hmap_unalloc hx] at Hcx
      cases Hcx
    · apply pcore_op_left
      rw [← Hcx, ← H, hmap_alloc hx]
  pcore_idem {x cx} H := by
    simp only [pcore, Option.some.injEq] at H
    change (pcore cx |>.getD cx) ≡ cx
    intro k
    simp [← H, get_hmap]
    rcases get x k with (_|v) <;> simp
    cases HY : CMRA.pcore v; simp
    exact pcore_idem HY
  pcore_op_mono := by
    apply pcore_op_mono_of_core_op_mono
    rintro x cx y ⟨z, Hz⟩
    suffices ∃ z, (pcore y |>.getD y) ≡ op (pcore x |>.getD x) z by
      rintro Hx
      simp only [pcore, Option.some.injEq, op, exists_eq_left']
      rcases this with ⟨z', Hz'⟩
      exists z'
      refine .trans Hz' (fun i => ?_)
      cases get z' i <;> cases get x i <;> simp_all
    refine lookup_inc.mpr (fun i => ?_)
    obtain ⟨v', Hv'⟩ : (core (get x i)) ≼ (core (get y i))  := by
      apply core_mono
      exists get z i
      have Hz := Hz i; revert Hz
      simp [CMRA.op, optionOp, get_merge]
      cases get x i <;> cases get z i <;> simp_all
    exists v'
    simp_all [CMRA.core, CMRA.pcore, optionCore, get_hmap]
  extend {n x y1 y2} Hm Heq := by
    have Hslice i : get x i ≡{n}≡ get y1 i • get y2 i := by
      refine (get_ne i |>.ne Heq).trans ?_
      simp [CMRA.op, get_merge, optionOp]
      cases get y1 i <;> cases get y2 i <;> simp
    let extendF (i : K) := CMRA.extend (Hm i) (Hslice i)
    exists hmap (fun k (_ : V) => extendF k |>.fst) y1
    exists hmap (fun k (_ : V) => extendF k |>.snd.fst) y2
    simp [op]
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
    all_goals rcases hF : extendF i with ⟨z1, z2, Hm, Hz1, Hz2⟩
    · refine Hm.trans ?_
      simp [get_merge, CMRA.op, optionOp]
      cases z1 <;> cases z2 <;> cases h1 : get y1 i <;> cases h2 : get y2 i <;> simp [h1, h2] at Hz1 Hz2
      · simp [hmap_unalloc h1, hmap_unalloc h2]
      · simp [hmap_unalloc h1, hmap_alloc h2]; rw [hF]; rfl
      · simp [hmap_alloc h1, hmap_unalloc h2, hF]
      · rw [hmap_alloc h1, hmap_alloc h2, hF]; simp
    · cases h : get y1 i
      · rw [hmap_unalloc h]
      · rw [hmap_alloc h, ← h, hF]; exact Hz1
    · cases h : get y2 i
      · rw [hmap_unalloc h]
      · rw [hmap_alloc h, ← h, hF]; exact Hz2

instance instStoreUCMRA : UCMRA T where
  unit := unit
  unit_valid := by simp [CMRA.Valid, get_empty]
  unit_left_id _ := by simp [CMRA.op, Heap.get_merge, get_empty]
  pcore_unit _ := by simp [hmap_unalloc, get_empty]

end Store
end CMRA

namespace Heap

variable {K V : Type _} [PartialMap M K] [CMRA V]

open CMRA Store

theorem validN_get_validN {m : T} (Hv : ✓{n} m) (He : get m i ≡{n}≡ some x) : ✓{n} x := by
  specialize Hv i; revert Hv
  rcases h : get m i <;> simp [h] at He
  exact OFE.Dist.validN He |>.mp

theorem valid_get_valid {m : T} (Hv : ✓ m) (He : get m i ≡ some x) : ✓ x :=
  valid_iff_validN.mpr (fun _ => validN_get_validN Hv.validN He.dist)

theorem set_validN {m : T} (Hx : ✓{n} x) (Hm : ✓{n} m) : ✓{n} (set m i x) := by
  intro k
  rw [get_set]; split; rename_i He
  · exact Hx
  · apply Hm

theorem set_valid {m : T} (Hx : ✓ x) (Hm : ✓ m) : ✓ (set m i x) :=
  valid_iff_validN.mpr (fun _ => set_validN Hx.validN Hm.validN)

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
  simp [CMRA.op, Store.op, get_merge, Option.merge, get_point, get_set]
  split <;> rename_i He
  · rw [← He, Hemp]; cases x <;> rfl
  · cases (get m k) <;> rfl

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
    cases get m i <;> simp
    exact core_id

instance [CoreId (x : V)] : CoreId (point (T := T) i (some x)) where
  core_id k := by
    simp [get_hmap, get_point]
    split <;> simp
    exact core_id

theorem point_incN_iff {m : T} :
    (point (T := T) i (some x)) ≼{n} m ↔ ∃ y, (get m i ≡{n}≡ some y) ∧ some x ≼{n} some y := by
  refine ⟨fun ⟨z, Hz⟩ => ?_, fun ⟨y, Hy, z, Hz⟩ => ?_⟩
  · specialize Hz i
    simp [CMRA.op, Store.op, get_merge, point_get_eq rfl, Option.merge] at Hz
    rcases He : get z i with (_|v)
    · exists x
      simp [He] at Hz
      exact ⟨Hz, incN_refl (some x)⟩
    · exists (x • v)
      simp [He] at Hz
      refine ⟨Hz, ?_⟩
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
    exact Option.eqv_of_inc_exclusive Hxy <| valid_get_valid Hv Hy
  · exists x

theorem point_inc_point_iff : (point i (T := T) (some x)) ≼ (point i (some y)) ↔ some x ≼ some y := by
  refine point_inc_iff.trans ⟨fun ⟨z, Hz, Hxz⟩ => ?_, fun H => ?_⟩
  · refine inc_of_inc_of_eqv Hxz ?_
    refine .trans Hz.symm ?_
    exact .of_eq <| point_get_eq rfl
  · refine ⟨y, ?_, H⟩
    exact .of_eq <| point_get_eq rfl

theorem total_point_inc_point_iff [IsTotal V] : (point i (T := T) (some x)) ≼ (point i (some y)) ↔ x ≼ y :=
  point_inc_point_iff.trans <| Option.some_inc_some_iff_isTotal

theorem point_inc_point_mono (Hinc : x ≼ y) : (point (T := T) i (some x)) ≼ (point i (some y)) :=
  point_inc_point_iff.mpr <| Option.some_inc_some_iff.mpr <| .inr Hinc

instance [H : Cancelable (some x)] : Cancelable (point (T := T) i (some x)) where
  cancelableN {n m1 m2} Hv He j := by
    specialize Hv j; revert Hv
    specialize He j; revert He
    simp only [CMRA.op, Store.op, get_merge, Option.merge, get_point]
    by_cases He : i = j
    · simp_all only [↓reduceIte]
      intro Hv He
      cases _ : get m1 j <;> cases _ : get m2 j
      all_goals apply H.cancelableN
      all_goals simp_all [CMRA.op, optionOp]
    · cases get m1 j <;> cases get m2 j <;> simp_all

instance {m : T} [Hid : ∀ x : V, IdFree x] [Hc : ∀ x : V, Cancelable x] : Cancelable m where
  cancelableN {n m1 m2} Hv He i := by
    apply cancelableN (x := get m i)
    · specialize Hv i; revert Hv
      simp [CMRA.op, Store.op, Heap.get_merge, optionOp]
      cases _ : get m i <;> cases _ : get m1 i <;> simp_all
    · specialize He i; revert He
      simp [Heap.get_merge, CMRA.op, Store.op, optionOp]
      cases get m i <;> cases get m1 i <;> cases get m2 i <;> simp_all

theorem set_op_equiv {m1 m2 : T} :
    Equiv ((set (V := Option V) (m1 • m2) i (x • y))) (set m1 i x • set m2 i y) := by
  refine funext fun j => ?_
  by_cases He : i = j
  · simp [CMRA.op, get_set_eq He, get_merge, optionOp]
    cases x <;> cases y <;> simp_all
  · simp [CMRA.op, get_set_ne (T := T) He, get_merge]

theorem set_op_eq [IsoFunStore T K (Option V)] {m1 m2 : T} :
    (set (V := Option V) (m1 • m2) i (x • y)) = (set m1 i x • set m2 i y) :=
  IsoFunStore.store_eq_of_Equiv set_op_equiv

theorem disjoint_op_equiv_union {m1 m2 : T} (Hd : Set.Disjoint (dom m1) (dom m2)) :
    Equiv (m1 • m2) (union m1 m2) := by
  refine funext fun j => ?_
  simp [CMRA.op, Store.op, Heap.get_merge]
  rcases _ : get m1 j <;> cases _ : get m2 j <;> simp_all
  refine (Hd j ?_).elim
  simp_all [dom]

theorem disjoint_op_eq_union [IsoFunStore T K (Option V)] {m1 m2 : T} (H : Set.Disjoint (dom m1) (dom m2)) :
    m1 • m2 = Heap.union m1 m2 :=
  IsoFunStore.store_eq_of_Equiv (disjoint_op_equiv_union H)

theorem valid0_disjoint_dom {m1 m2 : T} (Hv : ✓{0} (m1 • m2)) (H : ∀ {k x}, get m1 k = some x → Exclusive x) :
    Set.Disjoint (dom m1) (dom m2) := by
  rintro k
  simp only [dom, Option.isSome]
  rcases HX : get m1 k with (_|x) <;> simp
  rcases HY : get m2 k with (_|y) <;> simp
  apply (H HX).1 y
  simp [CMRA.op, CMRA.ValidN] at Hv; specialize Hv k; revert Hv
  simp [Heap.get_merge, HX, HY]

theorem valid_disjoint_dom {m1 m2 : T} (Hv : ✓ (m1 • m2)) (H : ∀ {k x}, get m1 k = some x → Exclusive x) :
    Set.Disjoint (dom m1) (dom m2) :=
  valid0_disjoint_dom (Valid.validN Hv) H

theorem dom_op_union (m1 m2 : T) : dom (m1 • m2) = Set.Union (dom m1) (dom m2) := by
  refine funext fun k => ?_
  cases get m1 k <;> cases get m2 k <;> simp_all [CMRA.op, dom, Set.Union, get_merge]

theorem inc_dom_inc {m1 m2 : T} (Hinc : m1 ≼ m2) : Set.Included (dom m1) (dom m2) := by
  intro i
  unfold Heap.dom
  rcases lookup_inc.mp Hinc i with ⟨z, Hz⟩
  revert Hz
  cases get m1 i <;> cases get m2 i <;> cases z <;> simp [CMRA.op, optionOp]

nonrec instance [HD : CMRA.Discrete V] [PartialMap M K] : Discrete T where
  discrete_0 {_ _} H := (OFE.Discrete.discrete_0 <| H ·)
  discrete_valid {_} := (CMRA.Discrete.discrete_valid <| · ·)

end Heap
