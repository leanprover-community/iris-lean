/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE

open Iris

/- # Datatype and CMRA for a generic heap-like structure. -/

/-- The type `T` can store and retrieve keys of type `K` and obtain values of type `V`. -/
class StoreLike (T : Type _) (K V : outParam (Type _)) where
  get : T → K → V
  set : T → K → V → T
  of_fun : (K → V) → T
export StoreLike (get set)

/-- `T`'s store and retrieve operations behave like a classical store. -/
class Store (T : Type _) (K V : outParam (Type _)) extends StoreLike T K V where
  get_set_eq {t k k' v} : k = k' → get (set t k v) k' = v
  get_set_ne {t k k' v} : k ≠ k' → get (set t k v) k' = get t k'
  /-- One-sided inverse between get and of_fun. The other direction does not need to hold. -/
  of_fun_get {f} : get (of_fun f) = f

/-- Each value of `T` uniquely represents a function `K → V`. -/
class StoreIso (T : Type _) (K V : outParam (Type _)) extends Store T K V where
  get_of_fun t : of_fun (get t) = t

def StoreLike.map [StoreLike T1 K V1] [StoreLike T2 K V2] (t : T1) (f : V1 → V2) : T2 :=
  StoreLike.of_fun <| f ∘ StoreLike.get t

def StoreLike.merge [StoreLike T K V] (op : V → V → V) (t1 t2 : T) : T :=
  StoreLike.of_fun <| (fun k => op (StoreLike.get t1 k) (StoreLike.get t2 k))

/-- An (index-dependent) predicate holds at every member of the store. -/
def StoreLike.all [StoreLike T K V] (P : K → V → Prop) : T → Prop :=
  fun t => ∀ k, P k (StoreLike.get t k)

/-- Lift a predicate on store values to a predicate on heap values, which is true for undefined entries. -/
abbrev lift_dom (P : K → V → Prop) (k : K) : Option V → Prop
  | .some v => P k v
  | .none => True

class Alloc (T : Type _) (K : outParam (Type _)) where
  fresh : T → K

class WithPoints (T : Type _) (K V : outParam (Type _)) where
  point : K → V → T

class HeapLike (T : Type _) (K V : outParam (Type _)) extends StoreLike T K (Option V)

/-- A type is HeapLike when it behaves like store for Optional values -/
class Heap (T : Type _) (K V : outParam (Type _))
    extends HeapLike T K V,  Store T K (Option V), WithPoints T K (Option V) where
  point_get_eq {k k' v} : k = k' → get (point k v) k' = v
  point_get_ne {k k' v} : k ≠ k' → get (point k v) k' = none

/-- A Heap which can always generate new values. -/
class AllocHeap (T : Type _) (K V : outParam (Type _)) extends Heap T K V, Alloc T K where
  fresh_get {t} : get t (fresh t) = none

abbrev HeapLike.delete [HeapLike T K V] (t : T) (k : K) : T := StoreLike.set t k .none
abbrev HeapLike.empty [HeapLike T K V] : T := StoreLike.of_fun (fun _ => .none)
abbrev HeapLike.dom [HeapLike T K V] : T → K → Prop := fun t k => (StoreLike.get t k).isSome

/-- Value-generic heap, ie. a higher-order type that is heap-like at every type.
For heaps whose representation internalizes the type which it contains, (for example, lists,
trees, functions) this is probably the class you want. -/
abbrev HeapF (H : Type _ → Type _) (K : outParam (Type _)) :=
  ∀ T : Type _, HeapLike (H T) K T


theorem Store.get_merge [Store T K V] {op : V → V → V} (t1 t2 : T) (k : K) :
    StoreLike.get (StoreLike.merge op t1 t2) k = op (StoreLike.get t1 k) (StoreLike.get t2 k) := by
  unfold StoreLike.merge; rw [Store.of_fun_get]

theorem Store.get_map [StoreLike T1 K V1] [Store T2 K V2] {t : T1} {f : V1 → V2} {k : K} :
    StoreLike.get (StoreLike.map t f : T2) k = f (StoreLike.get t k) := by
  unfold StoreLike.map; rw [Store.of_fun_get]; rfl

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
  f x := StoreO.mk <| StoreLike.of_fun x
  ne.1 {_ _ _} H k := by rw [Store.of_fun_get, Store.of_fun_get]; exact H k

@[simp] def StoreO.get [StoreLike T K V] (k : K) : StoreO T → V :=
  fun s => StoreLike.get s.1 k

-- TODO: A `Proper` class could avoid the variable reordering.
instance Store.get_ne [StoreLike T K V] [OFE V] (k : K) : NonExpansive (StoreO.get k : StoreO T → V) where
  ne {_ _ _} Ht := Ht k

@[simp] def StoreO.set [StoreLike T K V] [OFE V] (k : K) : V → StoreO T → StoreO T :=
  fun v s => StoreO.mk (StoreLike.set s.1 k v)

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
  compl c := ⟨StoreLike.of_fun <| COFE.compl <| c.map StoreO.toMap⟩
  conv_compl {n c} k := by
    rw [Store.of_fun_get]
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

instance [Store T K V] [COFE V] [Discrete V] : Discrete (StoreO T) where
  discrete_0 H k := discrete_0 <| H k

/-- We can lift a Leibniz OFE on V to a Leibniz OFE on (StoreO T) as long as
stores uniquely represent functions. -/
instance [StoreIso T K V] [COFE V] [Leibniz V] : Leibniz (StoreO T) where
  eq_of_eqv {x y} H := by
    apply StoreO.ext
    rewrite [← StoreIso.get_of_fun x.car, ← StoreIso.get_of_fun y.car]
    congr 1
    apply funext
    intro k
    apply eq_of_eqv (H k)

end ofe


section cmra

open CMRA

/- ## A CMRA on Heaps
TODO: I think there may be a generic way to put a CMRA on Stores, but I'm not sure of it. -/

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
    exists ⟨StoreLike.of_fun f⟩
    intro i
    apply (Hf i).trans
    simp [store_op, Store.get_merge, op_merge, Store.of_fun_get]
    generalize HX : StoreLike.get m1.car i = X
    generalize HY : f i = Y
    cases X <;> cases Y <;> simp_all [CMRA.op, optionOp]

theorem lookup_included (m1 m2 : StoreO T) :
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
    exists ⟨StoreLike.of_fun f⟩
    intro i
    apply (Hf i).trans
    simp [store_op, Store.get_merge, op_merge, Store.of_fun_get]
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
    refine (lookup_included (core' x) (core' y)).mpr ?_
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
    exists ⟨StoreLike.of_fun (F · |>.fst)⟩
    exists ⟨StoreLike.of_fun (F · |>.snd.fst)⟩
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
      <;> simp [store_op, Store.get_merge, Store.of_fun_get]
      <;> rcases (F i) with ⟨z1, z2, Hm, Hz1, Hz2⟩
    · refine Hm.trans ?_
      simp [CMRA.op, op_merge, optionOp]
      cases z1 <;> cases z2 <;> simp
    · exact Hz1
    · exact Hz2

instance StoreO_UCMRA : UCMRA (StoreO T) where
  unit := store_unit
  unit_valid := by simp [CMRA.Valid, store_valid, optionValid, HeapLike.empty, Store.of_fun_get]
  unit_left_id := by
    intro x k
    simp [CMRA.op, op_merge, HeapLike.empty, Store.get_merge, Store.of_fun_get]
    generalize HX : StoreLike.get x.car k = X <;> cases X <;> simp
  pcore_unit k := by simp [CMRA.pcore, Store.get_map, pcore_F, HeapLike.empty, Store.of_fun_get]
end cmra

section heap_laws

variable {T K V : Type _} [Heap T K V] [CMRA V]
open CMRA

theorem lookup_validN_Some n (m : StoreO T) i x : ✓{n} m → StoreO.get i m ≡{n}≡ some x → ✓{n} x := sorry

theorem lookup_valid_Some (m : StoreO T) i x : ✓ m → StoreO.get i m ≡ some x → ✓ x := sorry

theorem insert_validN n (m : StoreO T) i x : ✓{n} x → ✓{n} m → ✓{n} (StoreO.set i x m) := sorry

theorem insert_valid (m : StoreO T) i x : ✓ x → ✓ m → ✓ (StoreO.set i x m) := sorry

theorem singleton_valid i x : ✓ (StoreO.singleton i x : StoreO T) ↔ ✓ x := sorry

theorem delete_validN n (m : StoreO T) i : ✓{n} m → ✓{n} (StoreO.delete m i) := sorry

theorem delete_valid (m : StoreO T) i : ✓ m → ✓ (StoreO.delete m i) := sorry

theorem insert_singleton_op (m : StoreO T) i x : StoreO.get i m = none → (StoreO.set i x m) = (StoreO.singleton i x • m) := sorry

theorem singleton_core (i : K) (x : V) cx :
  pcore x = some cx → core (StoreO.singleton i (some x) : StoreO T) = (StoreO.singleton i (some cx) : StoreO T) := sorry

theorem singleton_core' (i : K) (x : V) cx :
  pcore x ≡ some cx → core (StoreO.singleton i (some x)) ≡ (StoreO.singleton i (some cx) : StoreO T) := sorry

theorem singleton_core_total [IsTotal V] (i : K) (x : V) :
  core (StoreO.singleton i (some x) : StoreO T) = (StoreO.singleton i (some (core x))) := sorry

theorem singleton_op (i : K) (x y : V) :
 (StoreO.singleton i (some x) : StoreO T)  • (StoreO.singleton i (some y)) = (StoreO.singleton i (some (x • y))) := sorry

theorem gmap_core_id (m : StoreO T) : (∀ i (x : V), (StoreO.get i m = some x) → CoreId x) → CoreId m := sorry

instance gmap_core_id' (m : StoreO T) : (∀ x : V, CoreId x) → CoreId m := sorry

instance gmap_singleton_core_id i (x : V) : CoreId x → CoreId (StoreO.singleton i (some v) : StoreO T) := sorry

theorem singleton_includedN_l n (m : StoreO T) i x :
  (StoreO.singleton i (some x) : StoreO T) ≼{n} m ↔ ∃ y, (StoreO.get i m  ≡{n}≡ some y) ∧ some x ≼{n} some y := sorry

theorem singleton_included_l (m : StoreO T) i x :
  (StoreO.singleton i (some x) : StoreO T) ≼ m ↔ ∃ y, (StoreO.get i m ≡ some y) ∧ some x ≼ some y := sorry

theorem singleton_included_exclusive_l (m : StoreO T) i x :
  Exclusive x → ✓ m →
  (StoreO.singleton i (some x) : StoreO T) ≼ m ↔ (StoreO.get i m ≡ some x) := sorry

theorem singleton_included i x y :
  (StoreO.singleton i (some x) : StoreO T) ≼ (StoreO.singleton i (some y)) ↔ some x ≼ some y := sorry

theorem singleton_included_total [IsTotal V]  i x y :
  (StoreO.singleton i (some x) : StoreO T) ≼ (StoreO.singleton i (some y))  ↔ x ≼ y := sorry

theorem singleton_included_mono i x y :
  x ≼ y → (StoreO.singleton i (some x) : StoreO T) ≼ (StoreO.singleton i (some y))  := sorry

instance singleton_cancelable i x : Cancelable (some x) → Cancelable (StoreO.singleton i (some x) : StoreO T) := sorry

instance heap_cancelable (m : StoreO T) : (∀ x : V, IdFree x) → (∀ x : V, Cancelable x) → Cancelable m := sorry

theorem insert_op (m1 m2 : StoreO T) i x y : (StoreO.set i (x • y) (m1 • m2)) = (StoreO.set i x m1) • (StoreO.set i y m2) := sorry

-- TODO: Reuse set theory as defined in ghost maps PR, and delete this
def set_disjoint {X : Type _} (S1 S2 : X → Prop) : Prop := ∀ x : X, ¬(S1 x ∧ S2 x)
def set_union {X : Type _} (S1 S2 : X → Prop) : X → Prop := fun x => S1 x ∨ S2 x
def set_included {X : Type _} (S1 S2 : X → Prop) : Prop := ∀ x, S1 x → S2 x

theorem gmap_op_union (m1 m2 : StoreO T) : set_disjoint (StoreO.dom m1) (StoreO.dom m2) → m1 • m2 = StoreO.union m1 m2 := sorry

theorem gmap_op_valid0_disjoint (m1 m2 : StoreO T) :
  ✓{0} (m1 • m2) → (∀ k x, StoreO.get k m1 = some x → Exclusive x) → set_disjoint (StoreO.dom m1) (StoreO.dom m2) := sorry

theorem gmap_op_valid_disjoint (m1 m2 : StoreO T) :
  ✓ (m1 • m2) → (∀ k x, StoreO.get k m1 = some x → Exclusive x) → set_disjoint (StoreO.dom m1) (StoreO.dom m2) := sorry

theorem dom_op (m1 m2 : StoreO T) : StoreO.dom (m1 • m2) = set_union (StoreO.dom m1) (StoreO.dom m2) := sorry

theorem dom_included (m1 m2 : StoreO T) : m1 ≼ m2 → set_included (StoreO.dom m1) (StoreO.dom m2) := sorry

theorem StoreO.map_mono [CMRA V'] [Heap T' K V'] (f : Option V → Option V') (m1 m2 : StoreO T) :
  (∀ v1 v2 : V, v1 ≡ v2 → f v1 ≡ f v2) →
  (∀ x y, x ≼ y → f x ≼ f y) → m1 ≼ m2 →
  (StoreO.map f m1 : StoreO T') ≼ StoreO.map f m2 := sorry

end heap_laws
