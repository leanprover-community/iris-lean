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
[2] -> [3] when the store is a StoreIso
-/



/- # Datatype and CMRA for a generic heap-like structure. -/

/-- The type `T` can store and retrieve keys of type `K` and obtain values of type `V`. -/
class StoreLike (T : Type _) (K V : outParam (Type _)) where
  get : T → K → V
  set : T → K → V → T
  ofFun : (K → V) → T
export StoreLike (get set)

/-- `T`'s store and retrieve operations behave like a classical store. -/
class Store (T : Type _) (K V : outParam (Type _)) extends StoreLike T K V where
  get_set_eq {t k k' v} : k = k' → get (set t k v) k' = v
  get_set_ne {t k k' v} : k ≠ k' → get (set t k v) k' = get t k'
  /-- One-sided inverse between get and ofFun. The other direction does not need to hold. -/
  ofFun_get {f} : get (ofFun f) = f

/-- Two stores are (pointwise) equivalent -/
def Store.Equiv [StoreLike T K V] (t1 t2 : T) : Prop := get t1 = get t2

/-- Each value of `T` uniquely represents a function `K → V`. -/
class IsStoreIso (T : Type _) (K V : outParam (Type _)) [I : Store T K V] where
  get_ofFun t : I.toStoreLike.ofFun (get t) = t

def StoreLike.map [StoreLike T1 K V1] [StoreLike T2 K V2] (t : T1) (f : V1 → V2) : T2 :=
  StoreLike.ofFun (fun i => f <| StoreLike.get t i)

def StoreLike.merge [StoreLike T K V] (op : V → V → V) (t1 t2 : T) : T :=
  StoreLike.ofFun <| (fun k => op (StoreLike.get t1 k) (StoreLike.get t2 k))

/-- An (index-dependent) predicate holds at every member of the store. -/
def StoreLike.all [StoreLike T K V] (P : K → V → Prop) : T → Prop :=
  fun t => ∀ k, P k (StoreLike.get t k)

/-- Lift a predicate on store values to a predicate on heap values, which is true for undefined entries. -/
abbrev liftHeapPred (P : K → V → Prop) (k : K) : Option V → Prop
  | .some v => P k v
  | .none => True

class WithPoints (T : Type _) (K V : outParam (Type _)) where
  point : K → V → T

class HeapLike (T : Type _) (K V : outParam (Type _)) extends StoreLike T K (Option V)

/-- A Heap with a partial `fresh` function -/
class Alloc (T : Type _) (K V : outParam (Type _)) extends HeapLike T K V where
  notFull : T → Prop
  fresh : {t : T} → notFull t → K
  fresh_get {H : notFull t} : get t (fresh H) = none

/-- A type is HeapLike when it behaves like store for Optional values -/
class Heap (T : Type _) (K V : outParam (Type _))
    extends HeapLike T K V, Store T K (Option V), WithPoints T K (Option V) where
  point_get_eq {k k' v} : k = k' → get (point k v) k' = v
  point_get_ne {k k' v} : k ≠ k' → get (point k v) k' = none

/-- A Heap whose `fresh` function is total -/
class AllocHeap (T : Type _) (K V : outParam (Type _)) extends Heap T K V, Alloc T K V where
  notFull_set_fresh {H : notFull t} {v} : notFull (set t (fresh H) v)

/-- Delete an element from a heap by setting its value to .none -/
abbrev HeapLike.delete [HeapLike T K V] (t : T) (k : K) : T := StoreLike.set t k .none

/-- A heap is empty when its get function is .none. -/
abbrev HeapLike.empty [HeapLike T K V] : T := StoreLike.ofFun (fun _ => .none)

/-- The domain of a heap is the set of keys that map to .some values. -/
abbrev HeapLike.dom [HeapLike T K V] : T → K → Prop := fun t k => (StoreLike.get t k).isSome

/-- Value-generic heap, ie. a higher-order type that is heap-like at every type.
For heaps whose representation internalizes the type which it contains, (for example, lists,
trees, functions) this is probably the class you want. -/
abbrev HeapF (H : Type _ → Type _) (K : outParam (Type _)) :=
  ∀ T : Type _, HeapLike (H T) K T

theorem Store.get_merge [Store T K V] {op : V → V → V} (t1 t2 : T) (k : K) :
    StoreLike.get (StoreLike.merge op t1 t2) k = op (StoreLike.get t1 k) (StoreLike.get t2 k) := by
  unfold StoreLike.merge; rw [Store.ofFun_get]

theorem Store.get_map [StoreLike T1 K V1] [Store T2 K V2] {t : T1} {f : V1 → V2} {k : K} :
    StoreLike.get (StoreLike.map t f : T2) k = f (StoreLike.get t k) := by
  unfold StoreLike.map; rw [Store.ofFun_get]

theorem IsStoreIso.ext [Store T K V] [IsStoreIso T K V] {t1 t2 : T} (H : ∀ k, get t1 k = get t2 k) : t1 = t2 := by
  rw [← IsStoreIso.get_ofFun t1, ← IsStoreIso.get_ofFun t2]; refine congrArg ?_ (funext H)

theorem IsStoreIso.store_eq_of_Equiv [Store T K V] [IsStoreIso T K V] {t1 t2 : T} :
    Store.Equiv t1 t2 → t1 = t2 :=
  (IsStoreIso.ext <| fun k => congrFun · k)

/-- Wrapper type for functions with the Store OFE -/
@[ext] structure StoreO (T : Type _) where car : T

section ofe

open OFE 

/-- The OFE on StoreO is the discrete function OFE on its .get function. -/
instance StoreO_OFE [StoreLike T K V] [OFE V] : OFE (StoreO T) where
  Equiv s0 s1  := StoreLike.get s0.1 ≡ StoreLike.get s1.1
  Dist n s0 s1 := StoreLike.get s0.1 ≡{n}≡ StoreLike.get s1.1
  dist_eqv     := ⟨fun _ => .of_eq rfl, (·.symm), (·.trans ·)⟩
  equiv_dist   := equiv_dist
  dist_lt      := dist_lt

@[simp] def StoreO.toMap [StoreLike T K V] [OFE V] : (StoreO T) -n> (K → V) where
  f x := StoreLike.get <| StoreO.car x
  ne.1 {_ _ _} H k := H k

@[simp] def StoreO.ofMap [Store T K V] [OFE V] : (K → V) -n> (StoreO T) where
  f x := StoreO.mk <| StoreLike.ofFun x
  ne.1 {_ _ _} H k := by rw [Store.ofFun_get, Store.ofFun_get]; exact H k

@[simp] def StoreO.get [StoreLike T K V] (k : K) : StoreO T → V :=
  fun s => StoreLike.get s.1 k

-- TODO: A `Proper` class could avoid the variable reordering.
instance Store.get_ne [StoreLike T K V] [OFE V] (k : K) : NonExpansive (StoreO.get k : StoreO T → V) where
  ne {_ _ _} Ht := Ht k

@[simp] def StoreO.set [StoreLike T K V] [OFE V] (k : K) : V → StoreO T → StoreO T :=
  fun v s => StoreO.mk (StoreLike.set s.1 k v)

@[simp] def StoreO.Equiv [StoreLike T K V] : StoreO T → StoreO T → Prop :=
  (Store.Equiv ·.1 ·.1)

instance StoreO.Equiv_trans [StoreLike T K V] : Trans (StoreO.Equiv : StoreO T → StoreO T → Prop) (StoreO.Equiv : StoreO T → StoreO T → Prop) (StoreO.Equiv : StoreO T → StoreO T → Prop) where
  trans := by simp_all [Store.Equiv]

-- TODO: A `Proper` class could avoid the variable reordering.
instance [Store T K V] [OFE V] (k : K) : NonExpansive₂ (StoreO.set k : V → StoreO T → StoreO T) where
  ne {n v1 v2} Hv {t1 t2} Ht k' := by
    simp only [StoreO.set]
    cases (Classical.em (k = k'))
    · rename_i H; rw [Store.get_set_eq H, Store.get_set_eq H]; exact Hv
    · rename_i H; rw [Store.get_set_ne H, Store.get_set_ne H]; exact Ht k'

@[simp] def StoreO.merge [StoreLike T K V] (op : V → V → V) (s1 s2 : StoreO T) : StoreO T :=
  .mk (StoreLike.merge op s1.1 s2.1)

instance [Store T K V] [OFE V] (op : V → V → V) [NonExpansive₂ op] :
    NonExpansive₂ (StoreO.merge (T := T) op) where
  ne n {_ _} Ht {_ _} Hs k := by
    simp only [StoreO.merge, Store.get_merge]
    exact NonExpansive₂.ne (Ht k) (Hs k)

@[simp] def StoreO.map [StoreLike T1 K V1] [Store T2 K V2] (f : V1 → V2) : StoreO T1 → StoreO T2 :=
  fun t => ⟨StoreLike.map t.1 f⟩

instance [StoreLike T1 K V1] [Store T2 K V2] [OFE V1] [OFE V2] (f : V1 → V2) [NonExpansive f] :
    NonExpansive (StoreO.map f : StoreO T1 → StoreO T2) where
  ne n {_ _} H k := by simp [StoreO.map, Store.get_map]; exact NonExpansive.ne (H k)

instance StoreO_COFE [Store T K V] [COFE V] : COFE (StoreO T) where
  compl c := ⟨StoreLike.ofFun <| COFE.compl <| c.map StoreO.toMap⟩
  conv_compl {n c} k := by
    rw [Store.ofFun_get]
    exact COFE.conv_compl (c := Chain.map StoreO.toMap c) k

@[simp] def StoreO.all [StoreLike T K V] (P : K → V → Prop) : StoreO T → Prop :=
  fun t => StoreLike.all P t.1

@[simp] def StoreO.dom [HeapLike T K V] : StoreO T → K → Prop :=
  fun t k => HeapLike.dom t.1 k

abbrev StoreO.union_F : Option V → Option V → Option V
| .some v1 => fun _ => v1
| .none => id

@[simp] def StoreO.union [HeapLike T K V] (t1 t2 : StoreO T) : StoreO T :=
  let F : Option V → Option V → Option V
  | .some v1 => fun _ => v1
  | .none => id
  StoreO.merge F t1 t2

@[simp] def StoreO.empty [HeapLike T K V] : StoreO T := ⟨HeapLike.empty⟩

@[simp] def StoreO.delete [HeapLike T K V] : StoreO T → K → StoreO T :=
  fun t k => .mk <| HeapLike.delete t.1 k

@[simp] def StoreO.singleton [WithPoints T K V]: K → V → StoreO T :=
  fun t k => ⟨WithPoints.point t k⟩

/- [3] -> [2] -/
theorem StoreO.Equiv_of_eq [Store T K V] {t1 t2 : StoreO T} (H : t1 = t2) :
  StoreO.Equiv t1 t2 := H▸rfl

/- [2] -> [1] -/
theorem StoreO.Eqv_of_Equiv [Store T K V] [OFE V] {t1 t2 : StoreO T} (H : StoreO.Equiv t1 t2) :
    t1 ≡ t2 := fun i => Equiv.of_eq <| congrFun H i

/-- When the type is a StoreIso, equality coincides with pointwise equality ([2] -> [3]). -/
theorem IsStoreIso.eq_of_Equiv [Store T K V] [IsStoreIso T K V] {t1 t2 : StoreO T} :
    StoreO.Equiv t1 t2 → t1 = t2 :=
  (StoreO.ext <| store_eq_of_Equiv ·)

/-- When the value is Leibniz, pointwise equality coincides with OFE equivalence. ([1] -> [2]), -/
theorem IsStore.StoreO_Equiv_iff_leibniz [Store T K V] [OFE V] [Leibniz V] {t1 t2 : StoreO T}
    (H : t1 ≡ t2) : StoreO.Equiv t1 t2 := funext ((forall_congr fun _ => propext leibniz).mp H ·)

/-- When store is a StoreIso with Leibniz values, it is Leibniz -/
instance [Store T K V] [IsStoreIso T K V] [COFE V] [Leibniz V] : Leibniz (StoreO T) where
  eq_of_eqv {x y} H := by
    apply StoreO.ext
    rewrite [← IsStoreIso.get_ofFun x.car, ← IsStoreIso.get_ofFun y.car]
    congr 1
    apply funext
    intro k
    apply eq_of_eqv (H k)

instance [Store T K V] [COFE V] [Discrete V] : Discrete (StoreO T) where
  discrete_0 H k := discrete_0 <| H k

end ofe


section cmra

open CMRA

/- ## A CMRA on Heaps -/

variable [Heap T K V] [CMRA V]

abbrev op_merge : Option V → Option V → Option V
| .some v1, .some v2 => Option.some (v1 • v2)
| .some v1, .none    => Option.some v1
| .none,    .some v2 => Option.some v2
| _,        _        => Option.none

instance : OFE.NonExpansive₂ (op_merge (V := V)) where
  ne _ x1 x2 Hx y1 y2 Hy := by
    revert Hx Hy
    rcases x1 <;> rcases x2 <;> rcases y1 <;> rcases y2 <;> simp
    exact OFE.Dist.op

theorem op_merge_assoc {x y z : Option V} : op_merge x (op_merge y z) ≡ op_merge (op_merge x y) z := by
  cases x <;> cases y <;> cases z <;> simp [op_merge]
  exact assoc

theorem op_merge_comm {x y : Option V} : op_merge x y ≡ op_merge y x := by
  cases x <;> cases y <;> simp [op_merge]
  exact comm

abbrev pcore_F : Option V → Option V
| Option.some v => CMRA.pcore v
| Option.none => Option.none

instance : OFE.NonExpansive (pcore_F (V := V)) where
  ne _ x1 x2 := by
    cases x1 <;> cases x2 <;> simp [pcore_F]
    exact (OFE.NonExpansive.ne ·)

abbrev store_op (s1 s2 : StoreO T) : StoreO T := StoreO.merge op_merge s1 s2
abbrev store_unit : StoreO T := StoreO.empty
abbrev store_pcore (s : StoreO T) : Option (StoreO T) := some <| StoreO.map pcore_F s
abbrev store_valid (s : StoreO T) : Prop := ∀ k, ✓ (StoreO.get k s : Option V)
abbrev store_validN (n : Nat) (s : StoreO T) : Prop := ∀ k, ✓{n} (StoreO.get k s : Option V)

theorem lookup_includedN n (m1 m2 : StoreO T) :
  (∃ (z : StoreO T), m2 ≡{n}≡ store_op m1 z) ↔
  ∀ i, (∃ z, (StoreO.get i m2) ≡{n}≡ (StoreO.get i m1) • z) := by
  constructor
  · intros H i
    rcases H with ⟨⟨z⟩, Hz⟩
    exists (StoreO.get i ⟨z⟩)
    rcases m1 with ⟨m1⟩
    rcases m2 with ⟨m2⟩
    simp_all [CMRA.op, optionOp]
    have Hz' := Hz i
    simp [Store.get_merge, op_merge] at Hz'
    generalize HX : StoreLike.get m1 i = X
    generalize HZ : StoreLike.get z i = Z
    rw [HX, HZ] at Hz'
    cases X <;> cases Z <;> simp_all
  · intro H
    rcases (Classical.axiomOfChoice H) with ⟨f, Hf⟩
    exists ⟨StoreLike.ofFun f⟩
    intro i
    apply (Hf i).trans
    simp [store_op, Store.get_merge, op_merge, Store.ofFun_get]
    generalize HX : StoreLike.get m1.car i = X
    generalize HY : f i = Y
    cases X <;> cases Y <;> simp_all [CMRA.op, optionOp]

theorem lookup_included {m1 m2 : StoreO T} :
  (∃ (z : StoreO T), m2 ≡ store_op m1 z) ↔
  ∀ i, (∃ z, (StoreO.get i m2) ≡ (StoreO.get i m1) • z) := by
  constructor
  · intros H i
    rcases H with ⟨⟨z⟩, Hz⟩
    exists (StoreO.get i ⟨z⟩)
    rcases m1 with ⟨m1⟩
    rcases m2 with ⟨m2⟩
    simp_all [CMRA.op, optionOp]
    have Hz' := Hz i
    simp [Store.get_merge, op_merge] at Hz'
    generalize HX : StoreLike.get m1 i = X
    generalize HZ : StoreLike.get z i = Z
    rw [HX, HZ] at Hz'
    cases X <;> cases Z <;> simp_all
  · intro H
    rcases (Classical.axiomOfChoice H) with ⟨f, Hf⟩
    exists ⟨StoreLike.ofFun f⟩
    intro i
    apply (Hf i).trans
    simp [store_op, Store.get_merge, op_merge, Store.ofFun_get]
    generalize HX : StoreLike.get m1.car i = X
    generalize HY : f i = Y
    cases X <;> cases Y <;> simp_all [CMRA.op, optionOp]

instance StoreO_CMRA : CMRA (StoreO T) where
  pcore := store_pcore
  op := store_op
  ValidN := store_validN
  Valid := store_valid
  op_ne := ⟨fun _ _ _ H => OFE.NonExpansive₂.ne .rfl H⟩
  pcore_ne {n x y cx} H := by
    simp only [store_pcore, StoreO.map, Option.some.injEq, exists_eq_left']
    refine (· ▸ fun k => ?_)
    simp only [Store.get_map]
    exact OFE.NonExpansive.ne (H k)
  validN_ne Hx H k := CMRA.validN_ne (OFE.NonExpansive.ne Hx) (H k)
  valid_iff_validN {x} :=
    ⟨fun H n k => valid_iff_validN.mp (H k) n, fun H k => valid_iff_validN.mpr (H · k)⟩
  validN_succ H k := validN_succ (H k)
  validN_op_left {n x1 x2} H k := by
    apply CMRA.validN_op_left (y := StoreO.get k x2)
    simp [CMRA.op, optionOp, store_validN, Store.get_merge, op_merge] at ⊢ H
    have H' := H k
    generalize HX : StoreLike.get x1.car k = X
    generalize HY : StoreLike.get x2.car k = Y
    simp_all
    cases X <;> cases Y <;> simp_all
  assoc := by
    rintro ⟨x⟩ ⟨y⟩ ⟨z⟩ k
    simp [store_op, Store.get_merge]
    exact op_merge_assoc
  comm := by
    rintro ⟨x⟩ ⟨y⟩ k
    simp [store_op, Store.get_merge]
    exact op_merge_comm
  pcore_op_left {x cx} := by
    refine (fun H => ?_)
    have H' : store_op ((store_pcore x).getD x) x ≡ x := by
      rcases cx with ⟨cx⟩
      intro k
      simp [store_op, store_pcore, store_op]
      rw [Store.get_merge]
      simp [store_pcore] at H
      simp [op_merge, Store.get_map]
      unfold pcore_F
      generalize HX : StoreLike.get x.car k = X
      cases X <;> simp
      rename_i v
      generalize HY : pcore v = Y
      cases Y <;> simp
      exact pcore_op_left HY
    apply (H ▸ H')
  pcore_idem {x cx} := by
    refine (fun H => ?_)
    have H' : ((store_pcore ((store_pcore x).getD x)).getD ((store_pcore x).getD x)) ≡ ((store_pcore x).getD x) := by
      intro k
      rw [H]
      simp only [Option.getD_some, StoreO.map]
      rw [Store.get_map]
      simp [store_pcore] at H
      rw [← H]
      simp [pcore_F, Store.get_map]
      generalize HX : StoreLike.get x.car k = X
      cases X <;> simp
      rename_i v
      generalize HY : pcore v = Y
      cases Y <;> simp
      exact pcore_idem HY
    apply (H ▸ H')
  pcore_op_mono := by
    apply pcore_op_mono_of_core_op_mono
    let core' (x : StoreO T) := (store_pcore x).getD x
    let le' (x y : StoreO T) := ∃ z, y ≡ store_op x z

    -- First direction, no countability used
    have Hcore'le'1 (x y : StoreO T) : le' x y → ∀ (i : K), (StoreO.get i x ≼ StoreO.get i y) := by
      intros H i
      rcases H with ⟨⟨z⟩, Hz⟩
      exists (StoreO.get i ⟨z⟩)
      rcases x with ⟨x⟩
      rcases y with ⟨y⟩
      simp_all [CMRA.op, optionOp]
      have Hz' := Hz i
      simp [Store.get_merge, op_merge] at Hz'
      generalize HX : StoreLike.get x i = X
      generalize HZ : StoreLike.get z i = Z
      rw [HX, HZ] at Hz'
      cases X <;> cases Z <;> simp_all

    suffices ∀ x y : StoreO T, le' x y → le' (core' x) (core' y) by
      rintro x cx y Hxy' Hx
      have Hxy := this x y Hxy'
      unfold core' at Hxy
      simp [Hx] at Hxy
      simp [store_pcore]
      exact Hxy
    intro x y H'
    unfold le'
    refine lookup_included.mpr ?_
    intro i
    suffices (core (StoreO.get i x)) ≼ (core (StoreO.get i y)) by
      simp_all [core', pcore_F, core, Store.get_map]
      split <;> split <;> simp_all [pcore, optionCore, this] <;> exact this
    exact core_mono (Hcore'le'1 x y H' i)

  extend := by
    intro n m y1 y2 Hm Heq
    have F (i : K) := @CMRA.extend (Option V) _ n (StoreO.get i m) (StoreO.get i y1) (StoreO.get i y2) (Hm i) ?G
    case G =>
      apply ((Store.get_ne i).ne Heq).trans
      simp [CMRA.op, optionOp]
      rw [Store.get_merge]
      simp [op_merge]
      generalize HX : StoreLike.get y1.car i = X
      generalize HY : StoreLike.get y2.car i = Y
      cases X <;> cases Y <;> simp
    exists ⟨StoreLike.ofFun (F · |>.fst)⟩
    exists ⟨StoreLike.ofFun (F · |>.snd.fst)⟩
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
      <;> simp [store_op, Store.get_merge, Store.ofFun_get]
      <;> rcases (F i) with ⟨z1, z2, Hm, Hz1, Hz2⟩
    · refine Hm.trans ?_
      simp [CMRA.op, op_merge, optionOp]
      cases z1 <;> cases z2 <;> simp
    · exact Hz1
    · exact Hz2

instance StoreO_UCMRA : UCMRA (StoreO T) where
  unit := store_unit
  unit_valid := by simp [CMRA.Valid, store_valid, optionValid, HeapLike.empty, Store.ofFun_get]
  unit_left_id := by
    intro x k
    simp [CMRA.op, op_merge, HeapLike.empty, Store.get_merge, Store.ofFun_get]
    generalize HX : StoreLike.get x.car k = X <;> cases X <;> simp
  pcore_unit k := by simp [CMRA.pcore, Store.get_map, pcore_F, HeapLike.empty, Store.ofFun_get]
end cmra

section heap_laws

variable {T K V : Type _} [Heap T K V] [CMRA V]
open CMRA


theorem lookup_validN_Some {m : StoreO T} : ✓{n} m → StoreO.get i m ≡{n}≡ some x → ✓{n} x := by
  suffices ✓{n} StoreO.get i m → StoreO.get i m ≡{n}≡ some x → ✓{n} x by
    exact fun Hv => (this (Hv i) ·)
  simp only [ValidN, optionValidN]
  split <;> rename_i He <;> rw [He]
  · exact fun Hv => (·.validN |>.mp Hv)
  · rintro _ ⟨⟩

theorem lookup_valid_Some {m : StoreO T} (Hv : ✓ m) (He : StoreO.get i m ≡ some x) : ✓ x :=
  valid_iff_validN.mpr (fun _ => lookup_validN_Some Hv.validN He.dist)

theorem insert_validN {m : StoreO T} (Hx : ✓{n} x) (Hm : ✓{n} m) : ✓{n} (StoreO.set i x m) := by
  intro k
  simp [CMRA.Valid]
  if He : i = k
    then rw [Heap.get_set_eq He]; exact Hx
    else rw [Heap.get_set_ne (He ·)]; exact Hm k

theorem insert_valid {m : StoreO T} (Hx : ✓ x) (Hm : ✓ m) : ✓ (StoreO.set i x m) :=
  valid_iff_validN.mpr (fun _ => insert_validN Hx.validN Hm.validN)

theorem singleton_valid : ✓ (StoreO.singleton i x : StoreO T) ↔ ✓ x := by
  simp only [StoreO.singleton, StoreO.get]
  constructor <;> intro H
  · have H' := H i; simp [Heap.point_get_eq rfl] at H'; exact H'
  · intro k
    if He : i = k
      then simp [StoreO.get]; rw [Heap.point_get_eq He]; trivial
      else simp [StoreO.get]; rw [Heap.point_get_ne He]; trivial

theorem delete_validN {m : StoreO T} (Hv : ✓{n} m) : ✓{n} (StoreO.delete m i) := by
  intro k
  if He : i = k
    then simp only [StoreO.get, StoreO.delete]; rw [Store.get_set_eq He]; trivial
    else simp only [StoreO.get, StoreO.delete]; rw [Store.get_set_ne He]; exact Hv k

theorem delete_valid {m : StoreO T} (Hv : ✓ m) : ✓ (StoreO.delete m i) :=
  valid_iff_validN.mpr (fun _ => delete_validN Hv.validN)

theorem insert_singleton_op {m : StoreO T} (Hemp : StoreO.get i m = none) :
    StoreO.Equiv (StoreO.set i x m) (StoreO.singleton i x • m) := by
  simp_all [StoreO.singleton, StoreO.set, CMRA.op, op, StoreLike.merge, op_merge, Store.Equiv]
  refine funext (fun k => ?_)
  if He : i = k
    then
      rw [Store.get_set_eq He, Heap.ofFun_get, Heap.point_get_eq He, He.symm, Hemp]
      split
      · rename_i Hk; rcases Hk
      · rfl
      · rename_i Hk; rcases Hk
      · (expose_names; exact Option.eq_none_iff_forall_ne_some.mpr fun a a_1 => h_1 a a_1 rfl)
    else
      rw [Store.get_set_ne He, Heap.ofFun_get, Heap.point_get_ne He]
      split <;> rename_i Hk _
      · rcases Hk
      · rcases Hk
      · trivial
      · (expose_names; exact Option.eq_none_iff_forall_ne_some.mpr fun a => h_1 a rfl)

theorem insert_singleton_op_eq [IsStoreIso T K (Option V)] {m : StoreO T} (Hemp : StoreO.get i m = none) :
    StoreO.set i x m = StoreO.singleton i x • m :=
  IsStoreIso.eq_of_Equiv (insert_singleton_op Hemp)

theorem singleton_core {i : K} {x : V} {cx} (Hpcore : pcore x = some cx) :
    StoreO.Equiv (core (StoreO.singleton i (some x) : StoreO T)) ((StoreO.singleton i (some cx) : StoreO T)) := by
  simp [core, pcore]
  rw [← Hpcore]
  unfold StoreLike.map
  unfold Store.Equiv
  apply funext
  intro k
  if He : i = k
    then rw [Heap.ofFun_get, Heap.point_get_eq He, Heap.point_get_eq He]
    else rw [Heap.ofFun_get, Heap.point_get_ne He, Heap.point_get_ne He]

theorem singleton_core_eq [IsStoreIso T K (Option V)] {i : K} {x : V} {cx} (Hpcore : pcore x = some cx) :
    core (StoreO.singleton i (some x) : StoreO T) = (StoreO.singleton i (some cx) : StoreO T) :=
  IsStoreIso.eq_of_Equiv (singleton_core Hpcore)

theorem singleton_core' {i : K} {x : V} {cx} (Hpcore : pcore x ≡ some cx) :
    core (StoreO.singleton i (some x)) ≡ (StoreO.singleton i (some cx) : StoreO T) := by
  simp [core, pcore]
  unfold StoreLike.map
  intro k
  if He : i = k
    then rw [Heap.ofFun_get, Heap.point_get_eq He, Heap.point_get_eq He]; exact Hpcore
    else rw [Heap.ofFun_get, Heap.point_get_ne He, Heap.point_get_ne He]

theorem singleton_core_total [IsTotal V] {i : K} {x : V} :
    StoreO.Equiv (core (StoreO.singleton i (some x) : StoreO T)) ((StoreO.singleton i (some (core x)))) := by
  obtain ⟨xc, Hxc⟩ := total x
  apply StoreO.Equiv_trans.trans (singleton_core Hxc)
  simp [core, Hxc]
  rfl

theorem singleton_core_total_eq [IsTotal V] [IsStoreIso T K (Option V)] {i : K} {x : V} :
    core (StoreO.singleton i (some x) : StoreO T) = (StoreO.singleton i (some (core x))) :=
  IsStoreIso.eq_of_Equiv singleton_core_total

theorem singleton_op {i : K} {x y : V} :
    StoreO.Equiv ((StoreO.singleton i (some x) : StoreO T) • (StoreO.singleton i (some y))) ((StoreO.singleton i (some (x • y)))) := by
  unfold StoreO.Equiv
  unfold Store.Equiv
  apply funext
  intro k
  simp [op]
  rw [Store.get_merge]
  unfold op_merge
  if He : i = k
    then
      rw [Heap.point_get_eq He]
      rw [Heap.point_get_eq He]
      simp only []
      rw [Heap.point_get_eq He]
    else
      rw [Heap.point_get_ne He]
      rw [Heap.point_get_ne He]
      simp only []
      rw [Heap.point_get_ne He]

theorem singleton_op_eq [IsStoreIso T K (Option V)] {i : K} {x y : V} :
    (StoreO.singleton i (some x) : StoreO T) • (StoreO.singleton i (some y)) = (StoreO.singleton i (some (x • y))) :=
  IsStoreIso.eq_of_Equiv singleton_op

theorem gmap_core_id {m : StoreO T} (H : ∀ i (x : V), (StoreO.get i m = some x) → CoreId x) : CoreId m := by
  constructor
  intro i
  simp [StoreO.map]
  rw [Store.get_map]
  simp [pcore_F]
  split
  · rename_i H'
    rw [H']
    exact (H _ _ H').core_id
  · rename_i H'
    rw [H']

instance gmap_core_id' {m : StoreO T} (H : ∀ x : V, CoreId x) : CoreId m := by
  constructor
  intro i
  simp [StoreO.map]
  rw [Store.get_map]
  simp [pcore_F]
  split
  · rename_i H'
    rw [H']
    apply (H _).core_id
  · rename_i H'
    rw [H']

instance gmap_singleton_core_id (H : CoreId (x : V)) : CoreId (StoreO.singleton i (some x) : StoreO T) := by
  constructor
  intro k
  simp [Store.get_map]
  if He : i = k
    then
      rw [Heap.point_get_eq He]
      simp [pcore_F]
      exact H.core_id
    else
      rw [Heap.point_get_ne He]

theorem singleton_includedN_l {m : StoreO T} :
    (StoreO.singleton i (some x) : StoreO T) ≼{n} m ↔ ∃ y, (StoreO.get i m  ≡{n}≡ some y) ∧ some x ≼{n} some y := by
  constructor
  · rintro ⟨z, Hz⟩
    have Hz' := Hz i
    simp [CMRA.op, op] at Hz'
    rw [Store.get_merge] at Hz'
    simp [op_merge] at Hz'
    rw [Heap.point_get_eq rfl] at Hz'
    generalize Hz0 : StoreLike.get z.car i = z0
    cases z0 <;> simp [Hz0] at Hz'
    · exists x
    · rename_i v
      exists (x • v)
      refine ⟨Hz', ?_⟩
      exists v
  · rintro ⟨y, Hy, z, Hz⟩
    exists StoreO.set i z m
    intro j
    if He : i = j
      then
        simp [StoreO.singleton]
        simp [StoreO.get, He] at Hy
        refine Hy.trans (Hz.trans ?_)
        simp [CMRA.op, Store.get_merge, Heap.point_get_eq He, Heap.get_set_eq He, op_merge, optionOp]
        cases z <;> simp
      else
        simp [StoreO.singleton, CMRA.op]
        rw [Store.get_merge, Heap.point_get_ne He, Heap.get_set_ne He]
        simp [op_merge]
        cases (StoreLike.get m.car j) <;> simp

theorem singleton_included_l {m : StoreO T} :
    (StoreO.singleton i (some x) : StoreO T) ≼ m ↔ ∃ y, (StoreO.get i m ≡ some y) ∧ some x ≼ some y := by
  constructor
  · rintro ⟨z, Hz⟩
    have Hz' := Hz i
    simp [CMRA.op, op] at Hz'
    rw [Store.get_merge] at Hz'
    simp [op_merge] at Hz'
    rw [Heap.point_get_eq rfl] at Hz'
    generalize Hz0 : StoreLike.get z.car i = z0
    cases z0 <;> simp [Hz0] at Hz'
    · exists x
    · rename_i v
      exists (x • v)
      refine ⟨Hz', ?_⟩
      exists v
  · rintro ⟨y, Hy, z, Hz⟩
    exists StoreO.set i z m
    intro j
    if He : i = j
      then
        simp [StoreO.singleton]
        simp [StoreO.get, He] at Hy
        refine Hy.trans (Hz.trans ?_)
        simp [CMRA.op, Store.get_merge, Heap.point_get_eq He, Heap.get_set_eq He, op_merge, optionOp]
        cases z <;> simp
      else
        simp [StoreO.singleton, CMRA.op]
        rw [Store.get_merge, Heap.point_get_ne He, Heap.get_set_ne He]
        simp [op_merge]
        generalize Hx : StoreLike.get m.car j = x
        cases x <;> simp

theorem singleton_included_exclusive_l {m : StoreO T} (He : Exclusive x) (Hv : ✓ m) :
    (StoreO.singleton i (some x) : StoreO T) ≼ m ↔ (StoreO.get i m ≡ some x) := by
  apply singleton_included_l.trans
  constructor
  · rintro ⟨y, Hy, Hxy⟩
    suffices x ≡ y by apply Hy.trans this.symm
    exact some_inc_exclusive Hxy <| lookup_valid_Some Hv Hy
  · intro _; exists x

theorem singleton_included :
    (StoreO.singleton i (some x) : StoreO T) ≼ (StoreO.singleton i (some y)) ↔ some x ≼ some y := by
  apply singleton_included_l.trans
  constructor
  · rintro ⟨z, Hz, Hxz⟩
    simp [StoreO.get, StoreO.singleton] at Hz
    rw [Heap.point_get_eq rfl] at Hz
    exact inc_of_inc_of_eqv Hxz Hz.symm
  · intro H
    exists y
    simp [StoreO.get, StoreO.singleton]
    rw [Heap.point_get_eq rfl]
    exact ⟨.rfl, H⟩

theorem singleton_included_total [IsTotal V] :
    (StoreO.singleton i (some x) : StoreO T) ≼ (StoreO.singleton i (some y))  ↔ x ≼ y :=
  singleton_included.trans <| some_inc_total.trans <| Eq.to_iff rfl

theorem singleton_included_mono (Hinc : x ≼ y) : (StoreO.singleton i (some x) : StoreO T) ≼ (StoreO.singleton i (some y)) :=
  singleton_included.mpr <| some_inc.mpr <| .inr Hinc

instance singleton_cancelable (H : Cancelable (some x)) : Cancelable (StoreO.singleton i (some x) : StoreO T) := by
  constructor
  intro n m1 m2 Hv He j
  have Hv' := Hv j; clear Hv
  have He' := He j; clear He
  simp_all [StoreO.singleton, CMRA.op, store_op, StoreO.merge, Store.get_merge]
  if He : i = j
    then
      rw [Heap.point_get_eq He] at *
      apply H.cancelableN
      · simp [op_merge] at Hv'
        generalize HX : StoreLike.get m1.car j = X
        rw [HX] at Hv'
        cases X <;> simp_all [CMRA.op, op, optionOp]
      · generalize HX : (StoreLike.get m1.car j) = X
        generalize HY : (StoreLike.get m2.car j) = Y
        rw [HX, HY] at He'
        cases X <;> cases Y <;> simp_all [op_merge, CMRA.op, optionOp]
    else
      rw [Heap.point_get_ne He] at *
      simp [op_merge] at *
      generalize HX : StoreLike.get m1.car j = X
      generalize HY : (StoreLike.get m2.car j) = Y
      rw [HX, HY] at He'
      rw [HX] at Hv'
      cases X <;> cases Y <;> simp_all [op_merge, CMRA.op, optionOp]

instance heap_cancelable {m : StoreO T} [Hid : ∀ x : V, IdFree x] [Hc : ∀ x : V, Cancelable x] : Cancelable m := by
  constructor
  intro n m1 m2 Hv He i
  apply CMRA.cancelableN (x := StoreLike.get m.car i)
  · have Hv' := Hv i
    simp [StoreO.get, CMRA.op, op] at Hv'
    rw [Store.get_merge] at Hv'
    generalize HX : (StoreLike.get m.car i) = X
    generalize HY : (StoreLike.get m1.car i) = Y
    simp_all [CMRA.op, op, op_merge, optionOp]
    cases X <;> cases Y <;> simp_all
  · have He' := He i
    simp_all [CMRA.op, op, optionOp]
    rw [Store.get_merge] at He'
    simp [op_merge] at He'
    generalize HX : (StoreLike.get m.car i) = X
    generalize HY : (StoreLike.get m1.car i) = Y
    generalize HZ : (StoreLike.get m2.car i) = Z
    rw [HX, HY] at He'
    cases X <;> cases Y <;> cases Z <;> simp_all [Store.get_merge, op_merge]

theorem insert_op {m1 m2 : StoreO T} :
    StoreO.Equiv ((StoreO.set i (x • y) (m1 • m2))) ((StoreO.set i x m1) • (StoreO.set i y m2)) := by
  simp [StoreO.Equiv, Store.Equiv]
  apply funext
  intro j
  if He : i = j
    then
      simp [CMRA.op]
      rw [Heap.get_set_eq He, Store.get_merge]
      simp [op_merge]
      rw [Heap.get_set_eq He, Heap.get_set_eq He]
      simp [optionOp]
      cases x <;> cases y <;> simp_all
    else
      simp [CMRA.op]
      rw [Heap.get_set_ne He, Store.get_merge]
      simp [op_merge]
      rw [Store.get_merge]
      rw [Heap.get_set_ne He, Heap.get_set_ne He]

theorem insert_op_eq [IsStoreIso T K (Option V)] {m1 m2 : StoreO T} : (StoreO.set i (x • y) (m1 • m2)) = (StoreO.set i x m1) • (StoreO.set i y m2) :=
  IsStoreIso.eq_of_Equiv insert_op

-- TODO: Reuse set theory as defined in ghost maps PR, and delete this
def set_disjoint {X : Type _} (S1 S2 : X → Prop) : Prop := ∀ x : X, ¬(S1 x ∧ S2 x)
def set_union {X : Type _} (S1 S2 : X → Prop) : X → Prop := fun x => S1 x ∨ S2 x
def set_included {X : Type _} (S1 S2 : X → Prop) : Prop := ∀ x, S1 x → S2 x

theorem gmap_op_union {m1 m2 : StoreO T} : set_disjoint (StoreO.dom m1) (StoreO.dom m2) →
    StoreO.Equiv (m1 • m2) (StoreO.union m1 m2) := by
  intro Hd
  simp [StoreO.Equiv, Store.Equiv]
  apply funext
  intro j
  simp [CMRA.op, op, Store.get_merge, op_merge]
  generalize HX : StoreLike.get m2.car j = X
  generalize HY : StoreLike.get m1.car j = Y
  cases X <;> cases Y <;> simp_all
  exfalso
  apply Hd j
  simp [StoreO.dom, HeapLike.dom, HX, HY]

theorem gmap_op_union_eq [IsStoreIso T K (Option V)] {m1 m2 : StoreO T} (H : set_disjoint (StoreO.dom m1) (StoreO.dom m2)) :
    m1 • m2 = StoreO.union m1 m2 :=
  IsStoreIso.eq_of_Equiv (gmap_op_union H)

theorem gmap_op_valid0_disjoint {m1 m2 : StoreO T} (Hv : ✓{0} (m1 • m2)) (H : ∀ k x, StoreO.get k m1 = some x → Exclusive x) :
    set_disjoint (StoreO.dom m1) (StoreO.dom m2) := by
  rintro k
  simp [StoreO.dom, HeapLike.dom, Option.isSome]
  generalize HX : StoreLike.get m1.car k = X
  cases X <;> simp
  rename_i x
  simp [StoreO.get] at H
  have H' := H _ _ HX
  generalize HY : StoreLike.get m2.car k = Y
  cases Y <;> simp_all
  rcases H' with ⟨Hex⟩
  rename_i xx
  apply Hex xx
  simp [CMRA.op, op, CMRA.ValidN, store_validN] at Hv
  have Hv' := Hv k
  simp [Store.get_merge, optionValidN, HX, HY] at Hv'
  exact Hv'

-- TODO: Redundant proof from gmap_op_valid0_disjoint
theorem gmap_op_valid_disjoint {m1 m2 : StoreO T} (Hv : ✓ (m1 • m2)) (H : ∀ k x, StoreO.get k m1 = some x → Exclusive x) :
    set_disjoint (StoreO.dom m1) (StoreO.dom m2) := by
  rintro k
  simp [StoreO.dom, HeapLike.dom, Option.isSome]
  generalize HX : StoreLike.get m1.car k = X
  cases X <;> simp
  rename_i x
  simp [StoreO.get] at H
  have H' := H _ _ HX
  generalize HY : StoreLike.get m2.car k = Y
  cases Y <;> simp_all
  rcases H' with ⟨Hex⟩
  rename_i xx
  apply Hex xx
  simp [CMRA.op, op, CMRA.ValidN, store_validN] at Hv
  have Hv' := Hv k
  simp [Store.get_merge, optionValidN, HX, HY] at Hv'
  exact Valid.validN Hv'

theorem dom_op (m1 m2 : StoreO T) : StoreO.dom (m1 • m2) = set_union (StoreO.dom m1) (StoreO.dom m2) := by
  refine (funext fun k => ?_)
  simp only [CMRA.op, op, StoreO.dom, HeapLike.dom, set_union, StoreO.merge, Store.get_merge, op_merge]
  generalize HX : StoreLike.get m1.car k = X
  generalize HY : StoreLike.get m2.car k = Y
  cases X <;> cases Y <;> simp

theorem dom_included {m1 m2 : StoreO T} (Hinc : m1 ≼ m2) : set_included (StoreO.dom m1) (StoreO.dom m2) := by
  intro i
  rcases lookup_included.mp Hinc i with ⟨z, Hz⟩
  simp [StoreO.dom, HeapLike.dom]
  simp [StoreO.get, OFE.Equiv, Option.Forall₂] at Hz
  generalize HX : StoreLike.get m1.car i = X
  generalize HY : StoreLike.get m2.car i = Y
  cases X <;> cases Y <;> simp
  simp [HX, HY, CMRA.op, op, optionOp] at Hz
  cases z <;> simp at Hz

-- theorem StoreO.map_mono [CMRA V'] [Heap T' K V'] {f : Option V → Option V'} {m1 m2 : StoreO T}
--     (H1 : ∀ v1 v2 : V, v1 ≡ v2 → f v1 ≡ f v2)  (H2 : ∀ x y, x ≼ y → f x ≼ f y) (H3 : m1 ≼ m2) :
--     (StoreO.map f m1 : StoreO T') ≼ StoreO.map f m2 := by
--   s orry

end heap_laws
