/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE

open Iris

/- # Datatype and CMRA for a generic heap-like structure. -/

-- open Classical in
-- /- Update a (classical) function at a point. Used to specify the correctness of stores. -/
-- noncomputable def fset {K V : Type _} (f : K → V) (k : K) (v : V) : K → V :=
--   fun k' => if (k = k') then v else f k'

/-- `T` can store and retrieve keys and values. -/
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
  |.some v => P k v
  | .none => True

class Alloc (T : Type _) (K : outParam (Type _)) where
  fresh : T → K

class WithPoints (T : Type _) (K V : outParam (Type _)) where
  point : K → V → T

class HeapLike (T : Type _) (K V : outParam (Type _)) extends StoreLike T K (Option V)

/-- A type is HeapLike when it behaves like store for Optional values -/
class Heap (T : Type _) (K V : outParam (Type _))
    extends HeapLike T K V, Alloc T K, Store T K (Option V), WithPoints T K (Option V) where
  fresh_get {t} : get t (fresh t) = none
  point_get_eq {k k' v} : k = k' → get (point k v) k' = some v
  point_get_ne {k k' v} : k ≠ k' → get (point k v) k' = none

abbrev HeapLike.delete [HeapLike T K V] (t : T) (k : K) : T := StoreLike.set t k .none
abbrev HeapLike.empty [HeapLike T K V] : T := StoreLike.of_fun (fun _ => .none)
abbrev HeapLike.dom [HeapLike T K V] : T → K → Prop := fun t k => (StoreLike.get t k).isSome

/-- Value-generic heap, ie. a higher-order type that is heap-like at every type.
For heaps whose representation internalizes the type which it contains, (for example, lists,
trees, functions) this is probably the class you want. -/
abbrev HeapF (H : Type _ → Type _) (K : outParam (Type _)) :=
  ∀ T : Type _, HeapLike (H T) K T

-- Example:
-- abbrev FT (A B : Type _) : Type _ := A → B
-- instance (T V : Type _) : Heap (FT T V) T V := sorry
-- #synth HeapF (FT Nat) Nat

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
instance [StoreLike T K V] [OFE V] (k : K) : NonExpansive (StoreO.get k : StoreO T → V) where
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
| Option.some v1, Option.some v2 => Option.some (v1 • v2)
| _, _ => Option.none
abbrev pcore_F : Option V → Option V
| Option.some v => CMRA.pcore v
| Option.none => Option.none
abbrev store_op (s1 s2 : StoreO T) : StoreO T := StoreO.merge op_merge s1 s2
abbrev store_unit : StoreO T := StoreO.empty
abbrev store_pcore (s : StoreO T) : Option (StoreO T) := some <| StoreO.map pcore_F s
abbrev store_valid (s : StoreO T) : Prop := ∀ k, ✓ (StoreO.get k s : Option V)
abbrev store_validN (n : Nat) (s : StoreO T) : Prop := ∀ k, ✓{n} (StoreO.get k s : Option V)

instance StoreO_CMRA : CMRA (StoreO T) where
  pcore := store_pcore
  op := store_op
  ValidN := store_validN
  Valid := store_valid
  op_ne := sorry
  pcore_ne := sorry
  validN_ne := sorry
  valid_iff_validN := sorry
  validN_succ := sorry
  validN_op_left := sorry
  assoc := sorry
  comm := sorry
  pcore_op_left := sorry
  pcore_idem := sorry
  pcore_op_mono := sorry
  extend := sorry

instance StoreO_UCMRA : UCMRA (StoreO T) where
  unit := store_unit
  unit_valid := sorry
  unit_left_id := sorry
  pcore_unit := sorry

end cmra
