/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Puming Liu
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE
import Iris.Std.Set
import Iris.Std.PartialMap

open Iris Std

section OFE

open OFE

namespace PartialMap

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

instance get?_ne [PartialMap M K] [OFE V] (k : K) : NonExpansive (get? · k : M V → Option V) where
  ne {_ _ _} Ht := Ht k

instance [LawfulPartialMap M K] [OFE V] (k : K) : NonExpansive₂ (insert · k · : M V → V → M V) where
  ne {_ _ _} Hv {_ _} Ht k' := by
    by_cases h : k = k'
    · simp [get?_insert_eq h, Ht]
    · simp [get?_insert_ne h, Hv k']

theorem eqv_of_Equiv [OFE V] [PartialMap M K] {t1 t2 : M V} (H : PartialMap.equiv t1 t2) : t1 ≡ t2 :=
  (.of_eq <| H ·)

instance [LawfulPartialMap M K] [OFE V] (op : K → V → V → V) [∀ k, NonExpansive₂ (op k)] :
    NonExpansive₂ (merge (M := M) op) where
  ne _ {_ _} Ht {_ _} Hs k := by simp only [get?_merge]; exact NonExpansive₂.ne (Ht k) (Hs k)

-- instance [Store T1 K V1] [Store T2 K V2] [OFE V1] [OFE V2] (f : K → V1 → V2)
--   [∀ k, NonExpansive (f k)] [HasStoreMap T1 T2 K V1 V2] : NonExpansive (dmap f : T1 → T2) where
--   ne _ {_ _} H k := by simp only [get_dmap]; exact NonExpansive.ne (H k)

/-- Project a chain of stores through its kth coordinate to a chain of values. -/
def chain [PartialMap M K] [OFE V] (k : K) (c : Chain (M V)) : Chain (Option V) where
  chain i := get? (c i) k
  cauchy Hni := c.cauchy Hni k


-- class Heap (T : Type _) (K V : outParam (Type _)) extends Store T K (Option V) where
--   empty : T
--   hmap (f : K → V → Option V) : T → T
--   merge (op : V → V → V) : T → T → T
--   get_empty : get empty k = none
--   get_hmap : get (hmap f t) k = (get t k).bind (f k)
--   get_merge : get (merge op t1 t2) k = Option.merge op (get t1 k) (get t2 k)
-- export Heap (empty hmap merge get_empty get_hmap get_merge)
--
-- theorem hmap_alloc [Heap T K V] {t : T} (H : get t k = some v) : get (hmap f t) k = f k v := by
--   simp [get_hmap, H]
--
-- theorem hmap_unalloc [Heap T K V] {t : T} (H : get t k = none) : get (hmap f t) k = none := by
--   simp [get_hmap, H]


-- get?_map {m : M V} {f : K → V → Option V'} {k} :
--   get? (f k <$> m) k = (get? m k).bind (f k)


theorem chain_get [PartialMap M K] [OFE V] (k : K) (c : Chain (M V)) :
    (chain k c) i = get? (c i) k := by simp [chain]

end PartialMap

instance Heap.instCOFE [LawfulPartialMap M K] [COFE V] : COFE (M V) where
  compl c := bindAlter (fun _ => COFE.compl <| c.map ⟨_, PartialMap.get?_ne ·⟩) (c 0)
  conv_compl {_ c} k := by
    rw [get?_bindAlter]
    rcases H : get? (c.chain 0) k
    · simp [← PartialMap.chain_get, chain_none_const (c := PartialMap.chain k c) (n := 0) (H▸rfl)]
    · exact IsCOFE.conv_compl

end OFE

section CMRA
open CMRA

/- ## A CMRA on Heaps -/

namespace Heap

open PartialMap

variable [LawfulPartialMap M K] [CMRA V]

@[simp] def op (s1 s2 : M V) : M V := merge (K := K) (fun _ => CMRA.op) s1 s2
@[simp] def unit : M V := empty
@[simp] def pcore (s : M V) : Option (M V) := some <| bindAlter (fun _ => CMRA.pcore) s
@[simp] def valid (s : M V) : Prop := ∀ k, ✓ get? s k
@[simp] def validN (n : Nat) (s : M V) : Prop := ∀ k, ✓{n} get? s k

theorem lookup_incN {n} {m1 m2 : M V} :
    (∃ (z : M V), m2 ≡{n}≡ op m1 z) ↔
    ∀ i, (∃ z, (get? m2 i) ≡{n}≡ (get? m1 i) • z) := by
  refine ⟨fun ⟨z, Hz⟩ i => ?_, fun H => ?_⟩
  · refine ⟨get? z i, ?_⟩
    refine .trans (get?_ne i |>.ne Hz) ?_
    simp only [op, CMRA.op, get?_merge]
    cases get? m1 i <;> cases get? z i <;> simp
  · obtain ⟨f, Hf⟩ := Classical.axiomOfChoice H
    exists bindAlter (fun k _ => f k) m2
    refine fun i => (Hf i).trans ?_
    specialize Hf i; revert Hf
    simp [CMRA.op, get?_merge, get?_bindAlter]
    cases get? m2 i <;> cases get? m1 i <;> cases f i <;> simp

theorem lookup_inc {m1 m2 : M V} :
    (∃ (z : M V), m2 ≡ op m1 z) ↔
    ∀ i, (∃ z, (get? m2 i) ≡ (get? m1 i) • z) := by
  refine ⟨fun ⟨z, Hz⟩ i => ?_, fun H => ?_⟩
  · refine ⟨get? z i, ?_⟩
    refine .trans (get?_ne i |>.eqv Hz) ?_
    simp only [CMRA.op, op, get?_merge]
    cases get? m1 i <;> cases get? z i <;> simp
  · obtain ⟨f, Hf⟩ := Classical.axiomOfChoice H
    exists bindAlter (fun k _ => f k) m2
    refine fun i => (Hf i).trans ?_
    specialize Hf i; revert Hf
    simp [CMRA.op, optionOp, get?_merge, get?_bindAlter]
    cases get? m2 i <;> cases get? m1 i <;> cases f i <;> simp

open OFE in
instance instStoreCMRA : CMRA (M V) where
  pcore := pcore
  op := op
  ValidN := validN
  Valid := valid
  op_ne.ne _ x1 x2 H i := by
    rename_i x _
    specialize H i; revert H
    simp [get?_merge]
    cases get? x1 i <;> cases get? x2 i <;> cases get? x i <;> simp
    apply op_right_dist
  pcore_ne {n x y _} H := by
    simp only [pcore, Option.some.injEq, exists_eq_left']
    refine (· ▸ fun k => ?_); specialize H k; revert H
    rw [get?_bindAlter, get?_bindAlter]
    cases get? x k <;> cases get? y k <;> simp
    exact (NonExpansive.ne ·)
  validN_ne Hx H k :=
    validN_ne (NonExpansive.ne (f := (get? · k : M V → Option V)) Hx) (H k)
  valid_iff_validN :=
    ⟨fun H n k => valid_iff_validN.mp (H k) n,
     fun H k => valid_iff_validN.mpr (H · k)⟩
  validN_succ H k := validN_succ (H k)
  validN_op_left {n x1 x2} H k := by
    refine validN_op_left (y := get? x2 k) ?_
    specialize H k; revert H
    simp only [op, get?_merge, Option.merge]
    cases get? x1 k <;> cases get? x2 k <;> simp [optionOp, CMRA.op]
  assoc {x y z} k := by
    simp only [op, get?_merge]
    cases get? x k <;> cases get? y k <;> cases get? z k <;> simp
    exact assoc
  comm {x y} k := by
    simp [op, get?_merge]
    cases get? x k <;> cases get? y k <;> simp
    exact comm
  pcore_op_left {x cx} H k := by
    simp only [← Option.getD_some (a := cx) (b := cx), op, get?_merge]
    cases Hcx : get? cx k <;> cases hx : get? x k <;>
      simp <;>
      simp only [pcore, Option.some.injEq] at H
    · rw [← H, get?_bindAlter, hx] at Hcx
      cases Hcx
    · apply pcore_op_left
      simp [← Hcx, ← H, get?_bindAlter, hx]
  pcore_idem {x cx} H := by
    simp only [pcore, Option.some.injEq] at H
    change (pcore cx |>.getD cx) ≡ cx
    intro k
    simp [← H, get?_bindAlter]
    rcases get? x k with (_|v) <;> simp
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
      cases get? z' i <;> cases get? x i <;> simp_all
    refine lookup_inc.mpr (fun i => ?_)
    obtain ⟨v', Hv'⟩ : (core (get? x i)) ≼ (core (get? y i))  := by
      apply core_mono
      exists get? z i
      have Hz := Hz i; revert Hz
      simp [CMRA.op, optionOp, get?_merge]
      cases get? x i <;> cases get? z i <;> simp_all
    exists v'
    simp_all [CMRA.core, CMRA.pcore, optionCore, get?_bindAlter]
  extend {n x y1 y2} Hm Heq := by
    have Hslice i : get? x i ≡{n}≡ get? y1 i • get? y2 i := by
      refine (get?_ne i |>.ne Heq).trans ?_
      simp [CMRA.op, get?_merge, optionOp]
      cases get? y1 i <;> cases get? y2 i <;> simp
    let extendF (i : K) := CMRA.extend (Hm i) (Hslice i)
    exists bindAlter (fun k (_ : V) => extendF k |>.fst) y1
    exists bindAlter (fun k (_ : V) => extendF k |>.snd.fst) y2
    simp [op]
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
    all_goals rcases hF : extendF i with ⟨z1, z2, Hm, Hz1, Hz2⟩
    · refine Hm.trans ?_
      simp [get?_merge, CMRA.op, optionOp, Option.merge, get?_bindAlter]
      rw [hF]
      -- FIXME
      cases z1 <;> cases z2 <;> simp_all
      · cases h : (get? y2 i) <;> simp; simp [h] at Hz2
      · cases h : (get? y1 i) <;> simp; simp [h] at Hz1
      · cases h : (get? y2 i) <;> simp; simp [h] at Hz2
        cases h : (get? y1 i) <;> simp; simp [h] at Hz1
    · cases h : get? y1 i
      · rw [get?_bindAlter]
        simp [h]
      · rw [get?_bindAlter]
        simp only [h, hF, Option.bind_some]
        refine Hz1.trans (.of_eq h)
    · cases h : get? y2 i
      · rw [get?_bindAlter]
        simp [h]
      · rw [get?_bindAlter, hF]
        simp only [h, Option.bind_some]
        refine Hz2.trans (.of_eq h)

instance instStoreUCMRA : UCMRA (M V) where
  unit := unit
  unit_valid := by simp [CMRA.Valid, get?_empty]
  unit_left_id _ := by simp [CMRA.op, get?_merge, get?_empty]
  pcore_unit _ := by simp [get?_bindAlter, get?_empty]

end Heap
end CMRA

namespace Heap

-- TODO: Fix namespaces
-- TODO: Fix unnecessary Open Classical's
open PartialMap LawfulPartialMap

variable {K V : Type _} [LawfulPartialMap M K] [CMRA V]

open CMRA

theorem validN_get?_validN {m : M V} (Hv : ✓{n} m) (He : get? m i ≡{n}≡ some x) : ✓{n} x := by
  specialize Hv i; revert Hv
  rcases h : get? m i <;> simp [h] at He
  exact OFE.Dist.validN He |>.mp

theorem valid_get?_valid {m : M V} (Hv : ✓ m) (He : get? m i ≡ some x) : ✓ x :=
  valid_iff_validN.mpr (fun _ => validN_get?_validN Hv.validN He.dist)

open Classical in
theorem insert_validN {m : M V} (Hx : ✓{n} x) (Hm : ✓{n} m) : ✓{n} (insert m i x) := by
  intro k
  rw [get?_insert]; split
  · exact Hx
  · apply Hm

theorem insert_valid {m : M V} (Hx : ✓ x) (Hm : ✓ m) : ✓ (insert m i x) :=
  valid_iff_validN.mpr (fun _ => insert_validN Hx.validN Hm.validN)

open Classical in
theorem singleton_valid_iff : ✓ (singleton i x : M V) ↔ ✓ x := by
  refine ⟨fun H => ?_, fun H k => ?_⟩
  · specialize H i; rw [get?_singleton_eq rfl] at H; trivial
  · rw [get?_singleton]; split <;> trivial

open Classical in
theorem singleton_validN_iff : ✓{n} (singleton i x : M V) ↔ ✓{n} x := by
  refine ⟨fun H => ?_, fun H k => ?_⟩
  · specialize H i; rw [get?_singleton_eq rfl] at H; trivial
  · rw [get?_singleton]; split <;> trivial

open Classical in
theorem delete_validN {m : M V} (Hv : ✓{n} m) : ✓{n} (delete m i) := by
  intro k
  rw [get?_delete]; split
  · trivial
  · exact Hv k

theorem delete_valid {m : M V} (Hv : ✓ m) : ✓ (delete m i) :=
  valid_iff_validN.mpr (fun _ => delete_validN Hv.validN)

open Classical in
theorem insert_equiv_singleton_op_singleton {m : M V} (Hemp : get? m i = none) :
    equiv (insert m i x) (singleton i x • m) := by
  refine (fun k => ?_)
  simp [CMRA.op, Heap.op, get?_merge, Option.merge, get?_singleton, get?_insert]
  split <;> rename_i He
  · rw [← He, Hemp]
  · cases (get? m k) <;> rfl

theorem insert_eq_singleton_op_singleton [IsoFunMap M K] {m : M V} (Hemp : get? m i = none) :
    insert m i x = singleton i x • m :=
  IsoFunMap.ext (insert_equiv_singleton_op_singleton Hemp)

open Classical in
theorem core_singleton_equiv {i : K} {x : V} {cx : V} (Hpcore : CMRA.pcore x = some cx) :
    equiv (core <| singleton i x : M V) (singleton i cx) := by
  refine fun k => ?_
  simp [← Hpcore, core, CMRA.pcore, get?_singleton, get?_bindAlter]
  split <;> rfl

theorem singleton_core_eq [IsoFunMap M K] {i : K} {x : V} {cx} (Hpcore : CMRA.pcore x = some cx) :
    core (singleton i x : M V) = singleton i cx  :=
  IsoFunMap.ext (core_singleton_equiv Hpcore)

open Classical in
theorem singleton_core_eqv {i : K} {x : V} {cx} (Hpcore : CMRA.pcore x ≡ some cx) :
    core (singleton i x : M V) ≡ singleton i cx := by
  intro k
  simp [core, CMRA.pcore, get?_singleton, get?_bindAlter]
  split <;> trivial

theorem singleton_core_total [IsTotal V] {i : K} {x : V} :
    equiv (core <| singleton i x : M V) ((singleton i (core x))) :=
  core_singleton_equiv (pcore_eq_core x)

theorem singleton_core_total_eq [IsTotal V] [IsoFunMap M K] {i : K} {x : V} :
    core (singleton i x : M V) = singleton i (core x) :=
  IsoFunMap.ext singleton_core_total

open Classical in
theorem singleton_op_singleton {i : K} {x y : V} :
    equiv ((singleton i x : M V) • (singleton i y)) (singleton i (x • y)) := by
  refine fun k => ?_
  simp only [CMRA.op, Heap.op, get?_merge, get?_singleton]
  split <;> simp [Option.merge]

theorem singleton_op_singleton_eq [IsoFunMap M K] {i : K} {x y : V} :
    (singleton i x : M V) • (singleton i y) = (singleton i (x • y)) :=
  IsoFunMap.ext singleton_op_singleton

instance {m : M V} [I : ∀ x : V, CoreId x] : CoreId m where
  core_id i := by
    rw [get?_bindAlter]
    cases get? m i <;> simp
    exact core_id

open Classical in
instance [CoreId (x : V)] : CoreId (singleton i x : M V) where
  core_id k := by
    simp [get?_bindAlter, get?_singleton]
    split <;> simp
    exact core_id

open Classical in
theorem singleton_incN_iff {m : M V} :
    (singleton i x) ≼{n} m ↔ ∃ y, (get? m i ≡{n}≡ some y) ∧ some x ≼{n} some y := by
  refine ⟨fun ⟨z, Hz⟩ => ?_, fun ⟨y, Hy, z, Hz⟩ => ?_⟩
  · specialize Hz i; revert Hz
    simp only [CMRA.op, Heap.op, get?_merge, get?_singleton_eq rfl]
    rcases get? z i with (_|v)
    · intro _
      exists x
    · refine (⟨x • v, ·, ?_⟩)
      exists v
  · cases z
    · exists (PartialMap.delete m i)
      intros j
      simp [CMRA.op, get?_merge, get?_singleton, get?_delete]
      split
      · rename_i h
        simp
        refine (h ▸ Hy).trans <| Hz.trans ?_
        simp [CMRA.op]
      · simp
    · rename_i z
      exists (PartialMap.insert m i z)
      intros j
      simp [CMRA.op, get?_merge, get?_singleton, get?_insert]
      split
      · rename_i h
        simp
        refine (h ▸ Hy).trans <| Hz.trans ?_
        simp [CMRA.op]
      · simp

open Classical in
theorem singleton_inc_iff {m : M V} :
    (singleton i x) ≼ m ↔ ∃ y, (get? m i ≡ some y) ∧ some x ≼ some y := by
  refine ⟨fun ⟨z, Hz⟩ => ?_, fun ⟨y, Hy, z, Hz⟩ => ?_⟩
  · specialize Hz i; revert Hz
    simp only [CMRA.op, Heap.op, get?_merge, get?_singleton_eq rfl]
    rcases get? z i with (_|v)
    · intro _
      exists x
    · refine (⟨x • v, ·, ?_⟩)
      exists v
  · cases z
    · exists (PartialMap.delete m i)
      intros j
      simp [CMRA.op, get?_merge, get?_singleton, get?_delete]
      split
      · rename_i h
        simp
        refine (h ▸ Hy).trans <| Hz.trans ?_
        simp [CMRA.op]
      · simp
    · rename_i z
      exists (PartialMap.insert m i z)
      intros j
      simp [CMRA.op, get?_merge, get?_singleton, get?_insert]
      split
      · rename_i h
        simp
        refine (h ▸ Hy).trans <| Hz.trans ?_
        simp [CMRA.op]
      · simp

theorem exclusive_singleton_inc_iff {m : M V} (He : Exclusive x) (Hv : ✓ m) :
    (singleton i x) ≼ m ↔ (get? m i ≡ some x) := by
  refine singleton_inc_iff.trans ⟨fun ⟨y, Hy, Hxy⟩ => ?_, fun _ => ?_⟩
  · suffices x ≡ y by exact Hy.trans <| this.symm
    exact Option.eqv_of_inc_exclusive Hxy <| valid_get?_valid Hv Hy
  · exists x

theorem singleton_inc_singleton_iff : (singleton i x : M V) ≼ (singleton i y : M V) ↔ some x ≼ some y := by
  refine singleton_inc_iff.trans ⟨fun ⟨z, Hz, Hxz⟩ => ?_, fun H => ?_⟩
  · refine inc_of_inc_of_eqv Hxz ?_
    refine .trans Hz.symm ?_
    exact .of_eq <| get?_singleton_eq rfl
  · refine ⟨y, ?_, H⟩
    exact .of_eq <| get?_singleton_eq rfl

theorem total_singleton_inc_singleton_iff [IsTotal V] :
    (singleton i x : M V) ≼ (singleton i y) ↔ x ≼ y :=
  singleton_inc_singleton_iff.trans <| Option.some_inc_some_iff_isTotal

theorem singleton_inc_singleton_mono (Hinc : x ≼ y) :
    (singleton i x : M V) ≼ (singleton i y) :=
  singleton_inc_singleton_iff.mpr <| Option.some_inc_some_iff.mpr <| .inr Hinc

open Classical in
instance [H : Cancelable (some x)] : Cancelable (singleton i x : M V) where
  cancelableN {n m1 m2} Hv He j := by
    specialize Hv j; revert Hv
    specialize He j; revert He
    simp only [CMRA.op, Heap.op, get?_merge, Option.merge, get?_singleton]
    by_cases He : i = j
    · simp_all only [↓reduceIte]
      intro Hv He
      cases _ : get? m1 j <;> cases _ : get? m2 j
      all_goals apply H.cancelableN
      all_goals simp_all [CMRA.op, optionOp]
    · cases get? m1 j <;> cases get? m2 j <;> simp_all

instance {m : M V} [Hid : ∀ x : V, IdFree x] [Hc : ∀ x : V, Cancelable x] : Cancelable m where
  cancelableN {n m1 m2} Hv He i := by
    apply cancelableN (x := get? m i)
    · specialize Hv i; revert Hv
      simp [CMRA.op, Heap.op, get?_merge, optionOp]
      cases _ : get? m i <;> cases _ : get? m1 i <;> simp_all
    · specialize He i; revert He
      simp [get?_merge, CMRA.op, Heap.op, optionOp]
      cases get? m i <;> cases get? m1 i <;> cases get? m2 i <;> simp_all

theorem insert_op_equiv {m1 m2 : M V} :
    equiv ((insert (m1 • m2) i (x • y))) (insert m1 i x • insert m2 i y) := by
  refine fun j => ?_
  by_cases He : i = j
  · simp [CMRA.op, get?_insert_eq He, get?_merge]
  · simp [CMRA.op, get?_insert_ne He, get?_merge]

theorem insert_op_eq [IsoFunMap M K] {m1 m2 : M (Option V)} :
    (insert (m1 • m2) i (x • y)) = (insert m1 i x • insert m2 i y) :=
  IsoFunMap.ext insert_op_equiv

theorem disjoint_op_equiv_union {m1 m2 : M V} (Hd : Set.Disjoint (dom m1) (dom m2)) :
    equiv (m1 • m2) (union m1 m2) := by
  refine fun j => ?_
  simp [CMRA.op, Heap.op, get?_merge]
  rcases _ : get? m1 j <;> cases _ : get? m2 j <;> simp_all
  refine (Hd j ?_).elim
  simp_all [dom]

theorem disjoint_op_eq_union [IsoFunMap M K] {m1 m2 : M V} (H : Set.Disjoint (dom m1) (dom m2)) :
    m1 • m2 = union m1 m2 :=
  IsoFunMap.ext (disjoint_op_equiv_union H)

theorem valid0_disjoint_dom {m1 m2 : M V} (Hv : ✓{0} (m1 • m2)) (H : ∀ {k x}, get? m1 k = some x → Exclusive x) :
    Set.Disjoint (dom m1) (dom m2) := by
  rintro k
  simp only [dom, Option.isSome]
  rcases HX : get? m1 k with (_|x) <;> simp
  rcases HY : get? m2 k with (_|y) <;> simp
  apply (H HX).1 y
  simp [CMRA.op, CMRA.ValidN] at Hv; specialize Hv k; revert Hv
  simp [get?_merge, HX, HY]

theorem valid_disjoint_dom {m1 m2 : M V} (Hv : ✓ (m1 • m2)) (H : ∀ {k x}, get? m1 k = some x → Exclusive x) :
    Set.Disjoint (dom m1) (dom m2) :=
  valid0_disjoint_dom (Valid.validN Hv) H

theorem dom_op_union (m1 m2 : M V) : dom (m1 • m2) = Set.Union (dom m1) (dom m2) := by
  refine funext fun k => ?_
  cases get? m1 k <;> cases get? m2 k <;> simp_all [CMRA.op, dom, Set.Union, get?_merge]

theorem inc_dom_inc {m1 m2 : M V} (Hinc : m1 ≼ m2) : Set.Included (dom m1) (dom m2) := by
  intro i
  unfold dom
  rcases lookup_inc.mp Hinc i with ⟨z, Hz⟩
  revert Hz
  cases get? m1 i <;> cases get? m2 i <;> cases z <;> simp [CMRA.op, optionOp]

nonrec instance [HD : CMRA.Discrete V] [PartialMap M K] : Discrete (M V) where
  discrete_0 {_ _} H := (OFE.Discrete.discrete_0 <| H ·)
  discrete_valid {_} := (CMRA.Discrete.discrete_valid <| · ·)

end Heap

section HeapFunctor

variable {K} (H : Type _ → Type _) [LawfulPartialMap H K]

section HeapMap

def Heap.map (f : α → β) : H α → H β := PartialMap.bindAlter (fun _ a => some <| f a)

instance [OFE α] [OFE β] {f : α → β} [hne : OFE.NonExpansive f] : OFE.NonExpansive (Heap.map H f) where
  ne := by
    simp only [OFE.Dist, Option.Forall₂, Heap.map, get?_bindAlter, Option.bind]
    intro n m1 m2
    apply forall_imp
    intro k
    cases get? m1 k <;> cases get? m2 k <;> simp
    apply OFE.NonExpansive.ne

def Heap.map_id [OFE α] (a : H α):
    Heap.map H id a ≡ a := by
  simp [OFE.Equiv, Heap.map, get?_bindAlter, Option.bind, Option.Forall₂]
  intro x
  rcases (get? a x) <;> simp

def Heap.mapO [OFE α] [OFE β] (f : α -n> β) : OFE.Hom (H α) (H β) where
  f := Heap.map H f
  ne := inferInstance

def Heap.map_ext [OFE α] [OFE β] (f g : α -> β) (heq: f ≡ g) :
    Heap.map H f m ≡ Heap.map H g m := by
  intro k
  simp [Heap.map, get?_bindAlter, Option.bind]
  cases get? m k <;> simp
  exact heq _

def Heap.map_ne [OFE α] [OFE β] (f g : α -> β) (heq: f ≡{n}≡ g) :
    Heap.map H f m ≡{n}≡ Heap.map H g m := by
  simp [OFE.Dist, Option.Forall₂, Heap.map, get?_bindAlter]
  intro k
  cases get? m k <;> simp
  exact heq _

def Heap.map_compose [OFE α] [OFE β] [OFE γ] (f : α -> β) (g : β -> γ) m :
    Heap.map H (g.comp f) m ≡ Heap.map H g (Heap.map H f m) := by
  intro k
  simp [Heap.map, get?_bindAlter]
  cases get? m k <;> simp

def Heap.mapC [CMRA α] [CMRA β] (f : α -C> β) : CMRA.Hom (H α) (H β) where
  f := Heap.map H f
  ne := inferInstance
  validN {n x} := by
    simp only [Heap.map, CMRA.ValidN, Heap.validN, optionValidN]
    apply forall_imp
    intro k
    rw [get?_bindAlter]
    cases (get? x k) <;> simp
    apply CMRA.Hom.validN
  pcore m := by
    intro x
    simp [Heap.map, get?_bindAlter]
    rcases get? m x with _|v <;> simp
    have h : (CMRA.pcore v).bind (fun a => some (f a)) = (CMRA.pcore v).map f := by
      rw [Option.map_eq_bind]
      rfl
    rw [h]
    exact (CMRA.Hom.pcore f v)
  op m1 m2 n := by
    simp [CMRA.op, Heap.map, get?_bindAlter, get?_merge, Option.merge]
    cases get? m1 n <;> cases get? m2 n <;> simp
    apply CMRA.Hom.op

end HeapMap

abbrev HeapOF (F : COFE.OFunctorPre) : COFE.OFunctorPre :=
  fun A B _ _ => H (F A B)

instance {F} [COFE.OFunctor F] : COFE.OFunctor (HeapOF H F) where
  cofe := inferInstance
  map f g := Heap.mapO H (COFE.OFunctor.map f g)
  map_ne {_} _ _ _ _ _ _ _ := by
    constructor
    intros _ _ _ _ _ _ _ _
    apply Heap.map_ne
    apply COFE.OFunctor.map_ne.ne <;> simp_all
  map_id x := by
    symm
    apply OFE.Equiv.trans
    · exact (OFE.Equiv.symm (Heap.map_id H x))
    · apply Heap.map_ext
      exact (fun _ => OFE.Equiv.symm (COFE.OFunctor.map_id _))
  map_comp f g f' g' m := by
    simp [Heap.mapO, Heap.map]
    symm
    intro x
    simp [get?_bindAlter]
    cases (get? m x) <;> simp
    exact OFE.Equiv.symm (COFE.OFunctor.map_comp f g f' g' _)

instance {F} [RFunctor F] : URFunctor (HeapOF H F) where
  map f g := Heap.mapC H (RFunctor.map f g)
  map_ne {_} _ _ _ _ _ _ _ := by
    constructor
    intros _ _ _ _ _ _ _ _
    apply Heap.map_ne
    apply RFunctor.map_ne.ne <;> simp_all
  map_id x := by
    symm
    apply OFE.Equiv.trans
    · exact (OFE.Equiv.symm (Heap.map_id H x))
    · apply Heap.map_ext
      exact (fun _ => OFE.Equiv.symm (RFunctor.map_id _))
  map_comp f g f' g' m := by
    simp [Heap.mapC, Heap.map]
    symm
    intro x
    simp [get?_bindAlter]
    cases get? m x <;> simp
    exact OFE.Equiv.symm (RFunctor.map_comp f g f' g' _)

instance {F} [RFunctorContractive F] : URFunctorContractive (HeapOF H F) where
  map_contractive.1 H m := by
    apply Heap.map_ne _ _
    apply (RFunctorContractive.map_contractive.1 H)

end HeapFunctor
