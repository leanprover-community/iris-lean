/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.Algebra.Agree
public import Iris.Algebra.Heap
public import Iris.Algebra.List
public import Iris.Algebra.LocalUpdates
public import Iris.Std.HeapInstances
meta import Iris.Std.RocqPorting

/-!
# Max prefix lists

An RA on lists whose composition is only defined when one operand is a prefix of the other,
in which case the result is the longer list. The core is the identity function for all elements.

A list is represented as a finite map from indices to agreed-upon elements, so that composition
is map union with `Agree` forcing the operands to agree on their common indices. `MaxPrefixList`
wraps that map in a single-field structure, which keeps it a type constructor in its own right:
the map instances in `Iris.Algebra.Heap` are stated for `M V`, so a bare type synonym would leave
instance synthesis unifying `?M ?V` against it and picking the wrong first-order solution.
-/

@[expose] public section

namespace Iris

open OFE CMRA Std

-- Named as a *functor* rather than an application so that the value type stays in last
-- position: `?M ?V` then unifies against `MaxPrefixListMap (Agree α)` correctly.
/-- The extensional finite map from list indices to agreed-upon elements. -/
abbrev MaxPrefixListMap : Type _ → Type _ := (Std.ExtTreeMap Nat · compare)

@[rocq_alias max_prefix_list, rocq_alias max_prefix_listR, rocq_alias max_prefix_listUR]
structure MaxPrefixList (α : Type _) where
  ofMap ::
  toMap : MaxPrefixListMap (Agree α)

namespace MaxPrefixList

variable {α β : Type _}

theorem toMap_inj {x y : MaxPrefixList α} (h : x.toMap = y.toMap) : x = y := congrArg ofMap h

/-! ## Algebraic structure, inherited from the underlying map -/

section Instances

variable [OFE α]

instance : OFE (MaxPrefixList α) where
  Dist n x y := x.toMap ≡{n}≡ y.toMap
  dist_eqv := ⟨fun _ => .rfl, (·.symm), (·.trans ·)⟩
  eq_dist := ⟨fun h _ => h ▸ .rfl, fun h => toMap_inj (eq_dist.mpr h)⟩
  dist_lt h hlt := h.lt hlt

@[local simp] theorem dist_toMap {n} {x y : MaxPrefixList α} :
    x ≡{n}≡ y ↔ x.toMap ≡{n}≡ y.toMap := .rfl

-- Every `Agree` element is its own core, so the core here is the identity; `pcore_toMap`
-- records that this agrees with the core of the underlying map.
instance : CMRA (MaxPrefixList α) where
  pcore x := some x
  op x y := ofMap (x.toMap • y.toMap)
  ValidN n x := ✓{n} x.toMap
  Valid x := ✓ x.toMap
  op_ne.ne _ _ _ h := dist_toMap.mpr (CMRA.op_ne.ne h)
  pcore_ne hd hcx := ⟨_, rfl, Option.some.inj hcx ▸ hd⟩
  validN_ne hd hv := CMRA.validN_ne hd hv
  valid_iff_validN := CMRA.valid_iff_validN
  validN_succ := CMRA.validN_succ
  validN_op_left := CMRA.validN_op_left
  assoc := toMap_inj CMRA.assoc
  comm := toMap_inj CMRA.comm
  pcore_op_left hcx := by
    obtain rfl := Option.some.inj hcx
    exact toMap_inj (op_self _)
  pcore_idem _ := rfl
  pcore_op_mono hcx y := by
    obtain rfl := Option.some.inj hcx
    exact ⟨y, rfl⟩
  extend hv hd := by
    obtain ⟨m₁, m₂, heq, h₁, h₂⟩ := CMRA.extend hv hd
    exact ⟨ofMap m₁, ofMap m₂, toMap_inj heq, h₁, h₂⟩

@[local simp] theorem toMap_op (x y : MaxPrefixList α) :
    (x • y).toMap = x.toMap • y.toMap := rfl
@[local simp] theorem pcore_eq_some (x : MaxPrefixList α) : pcore x = some x := rfl
@[local simp] theorem validN_toMap {n} {x : MaxPrefixList α} : ✓{n} x ↔ ✓{n} x.toMap := .rfl
@[local simp] theorem valid_toMap {x : MaxPrefixList α} : ✓ x ↔ ✓ x.toMap := .rfl

/-- The core agrees with the core of the underlying map. -/
theorem pcore_toMap (x : MaxPrefixList α) : pcore x = (pcore x.toMap).map ofMap := by
  simp [core_id (x := x.toMap)]

instance : UCMRA (MaxPrefixList α) where
  unit := ofMap UCMRA.unit
  unit_valid := valid_toMap.mpr UCMRA.unit_valid
  unit_left_id := toMap_inj UCMRA.unit_left_id
  pcore_unit := rfl

-- Rocq calls this `mono_list_lb_core_id`, a name `mono_list.v` reuses for the fragment; the
-- alias is attached there, on `MonoList.instCoreIdLb`.
instance (x : MaxPrefixList α) : CoreId x where
  core_id := rfl

instance [OFE.Discrete α] : CMRA.Discrete (MaxPrefixList α) where
  discrete_0 h := toMap_inj (OFE.discrete_0 h)
  discrete_valid := CMRA.discrete_valid (α := MaxPrefixListMap (Agree α))

@[local simp] theorem incN_toMap {n} {x y : MaxPrefixList α} :
    x ≼{n} y ↔ x.toMap ≼{n} y.toMap :=
  ⟨fun ⟨z, h⟩ => ⟨z.toMap, h⟩, fun ⟨m, h⟩ => ⟨ofMap m, h⟩⟩

@[local simp] theorem inc_toMap {x y : MaxPrefixList α} : x ≼ y ↔ x.toMap ≼ y.toMap :=
  ⟨fun ⟨z, h⟩ => ⟨z.toMap, congrArg toMap h⟩,
   fun ⟨m, h⟩ => ⟨ofMap m, toMap_inj h⟩⟩

/-- Lift a CMRA homomorphism between the underlying maps to one between `MaxPrefixList`s. -/
def homLift [OFE β] (f : MaxPrefixListMap (Agree α) -C> MaxPrefixListMap (Agree β)) :
    MaxPrefixList α -C> MaxPrefixList β where
  f x := ofMap (f x.toMap)
  ne.ne _ _ _ h := dist_toMap.mpr (f.ne.ne h)
  validN := f.validN
  pcore _ := rfl
  op x y := toMap_inj (f.op x.toMap y.toMap)

@[local simp] theorem toMap_homLift [OFE β]
    (f : MaxPrefixListMap (Agree α) -C> MaxPrefixListMap (Agree β)) (x : MaxPrefixList α) :
    (homLift f x).toMap = f x.toMap := rfl

end Instances

/-! ## The canonical embedding of lists -/

/-- `l`, agreed upon and placed at the indices `start`, `start + 1`, … -/
def ofListFrom (start : Nat) (l : List α) : MaxPrefixList α :=
  ofMap (Std.PartialMap.map toAgree (FiniteMap.map_seq start l))

@[rocq_alias to_max_prefix_list]
def toMaxPrefixList (l : List α) : MaxPrefixList α := ofListFrom 0 l

theorem get?_ofListFrom {start i : Nat} {l : List α} :
    get? (ofListFrom start l).toMap i
      = (if start ≤ i then l[i - start]? else none).map toAgree := by
  rw [ofListFrom, LawfulPartialMap.get?_map, LawfulFiniteMap.get?_map_seq]

theorem get?_toMaxPrefixList {i : Nat} {l : List α} :
    get? (toMaxPrefixList l).toMap i = l[i]?.map toAgree := by
  simp [toMaxPrefixList, get?_ofListFrom]

variable [OFE α]

theorem toMaxPrefixList_nil : toMaxPrefixList ([] : List α) = UCMRA.unit := by
  refine toMap_inj (LawfulPartialMap.equiv_iff_eq.mp fun i => ?_)
  rw [get?_toMaxPrefixList, List.getElem?_nil]
  exact (LawfulPartialMap.get?_empty i).symm

/-! ## Setoid properties -/

@[rocq_alias to_max_prefix_list_ne]
instance toMaxPrefixList_ne : NonExpansive (toMaxPrefixList (α := α)) where
  ne _ _ _ h i := by
    rw [get?_toMaxPrefixList, get?_toMaxPrefixList]
    exact Option.map_ne (fun _ _ hd => NonExpansive.ne hd) (list_dist_lookup.mp h i)

#rocq_ignore to_max_prefix_list_proper "OFE is Leibniz; use equality"

@[rocq_alias to_max_prefix_list_dist_inj]
theorem toMaxPrefixList_dist_inj {n} {l1 l2 : List α}
    (h : toMaxPrefixList l1 ≡{n}≡ toMaxPrefixList l2) : l1 ≡{n}≡ l2 := by
  refine list_dist_lookup.mpr fun i => ?_
  have hi := h i
  rw [get?_toMaxPrefixList, get?_toMaxPrefixList] at hi
  cases h1 : l1[i]? <;> cases h2 : l2[i]? <;> rw [h1, h2] at hi <;> simp_all
  exact Agree.toAgree_injN hi

@[rocq_alias to_max_prefix_list_inj]
theorem toMaxPrefixList_inj {l1 l2 : List α}
    (h : toMaxPrefixList l1 = toMaxPrefixList l2) : l1 = l2 :=
  eq_dist.mpr fun _ => toMaxPrefixList_dist_inj (Dist.of_eq h)

/-! ## Validity -/

@[rocq_alias to_max_prefix_list_valid]
theorem toMaxPrefixList_valid (l : List α) : ✓ toMaxPrefixList l := fun i => by
  rw [get?_toMaxPrefixList]
  cases l[i]? with
  | none => trivial
  | some a => exact Agree.toAgree_valid

@[rocq_alias to_max_prefix_list_validN]
theorem toMaxPrefixList_validN {n} (l : List α) : ✓{n} toMaxPrefixList l :=
  (toMaxPrefixList_valid l).validN

/-! ## Operation -/

@[rocq_alias to_max_prefix_list_app]
theorem toMaxPrefixList_app (l1 l2 : List α) :
    toMaxPrefixList (l1 ++ l2) = toMaxPrefixList l1 • ofListFrom l1.length l2 := by
  refine toMap_inj (LawfulPartialMap.equiv_iff_eq.mp fun i => ?_)
  rw [toMap_op, Heap.get?_op, get?_toMaxPrefixList, get?_toMaxPrefixList, get?_ofListFrom,
    List.getElem?_append]
  by_cases hi : i < l1.length
  · rw [if_pos hi, if_neg (by omega)]
    cases l1[i]? <;> simp [op, optionOp]
  · rw [if_neg hi, if_pos (by omega), List.getElem?_eq_none (by omega : l1.length ≤ i)]
    cases l2[i - l1.length]? <;> simp [op, optionOp]

@[rocq_alias to_max_prefix_list_op_l]
theorem toMaxPrefixList_op_left {l1 l2 : List α} (h : l1 <+: l2) :
    toMaxPrefixList l1 • toMaxPrefixList l2 = toMaxPrefixList l2 := by
  obtain ⟨l, rfl⟩ := h
  rw [toMaxPrefixList_app, assoc', op_self]

@[rocq_alias to_max_prefix_list_op_r]
theorem toMaxPrefixList_op_right {l1 l2 : List α} (h : l1 <+: l2) :
    toMaxPrefixList l2 • toMaxPrefixList l1 = toMaxPrefixList l2 :=
  comm'.trans (toMaxPrefixList_op_left h)

/-! ## Inclusion -/

@[rocq_alias max_prefix_list_included_includedN]
theorem inc_iff_forall_incN {ml1 ml2 : MaxPrefixList α} :
    ml1 ≼ ml2 ↔ ∀ n, ml1 ≼{n} ml2 := by
  refine ⟨fun h n => incN_of_inc n h, fun h => ⟨ml2, eq_dist.mpr fun n => ?_⟩⟩
  obtain ⟨l, hl⟩ := h n
  calc ml2 ≡{n}≡ ml1 • l := hl
    _ ≡{n}≡ (ml1 • ml1) • l := (congrArg (· • l) (op_self ml1)).symm.dist
    _ ≡{n}≡ ml1 • (ml1 • l) := assoc'.symm.dist
    _ ≡{n}≡ ml1 • ml2 := hl.symm.op_r

@[rocq_alias to_max_prefix_list_includedN_aux]
theorem toMaxPrefixList_incN_aux {n} {l1 l2 : List α}
    (h : toMaxPrefixList l1 ≼{n} toMaxPrefixList l2) : l2 ≡{n}≡ l1 ++ l2.drop l1.length := by
  refine list_dist_lookup.mpr fun i => ?_
  have hi := Heap.lookup_incN.mp (incN_toMap.mp h) i
  rw [get?_toMaxPrefixList, get?_toMaxPrefixList] at hi
  rw [List.getElem?_append]
  rcases Option.incN_iff_is_total.mp hi with hnone | ⟨a1, a2, ha1, ha2, ha⟩
  · have hlen : l1.length ≤ i := List.getElem?_eq_none_iff.mp (by simpa using hnone)
    refine .of_eq ?_
    rw [if_neg (by omega), List.getElem?_drop, show l1.length + (i - l1.length) = i by omega]
  · obtain ⟨x1, hx1, rfl⟩ := Option.map_eq_some_iff.mp ha1
    obtain ⟨x2, hx2, rfl⟩ := Option.map_eq_some_iff.mp ha2
    rw [hx2, if_pos (List.getElem?_eq_some_iff.mp hx1).1, hx1]
    exact some_dist_some.mpr (Agree.toAgree_includedN.mp ha).symm

@[rocq_alias to_max_prefix_list_includedN]
theorem toMaxPrefixList_incN_iff {n} {l1 l2 : List α} :
    toMaxPrefixList l1 ≼{n} toMaxPrefixList l2 ↔ ∃ l, l2 ≡{n}≡ l1 ++ l := by
  refine ⟨fun h => ⟨_, toMaxPrefixList_incN_aux h⟩, fun ⟨l, hl⟩ => ?_⟩
  refine incN_of_incN_of_dist ?_ (toMaxPrefixList_ne.ne hl).symm
  rw [toMaxPrefixList_app]
  exact incN_of_inc n (inc_op_left ..)

@[rocq_alias to_max_prefix_list_included]
theorem toMaxPrefixList_inc_iff {l1 l2 : List α} :
    toMaxPrefixList l1 ≼ toMaxPrefixList l2 ↔ ∃ l, l2 = l1 ++ l := by
  refine ⟨fun h => ⟨_, eq_dist.mpr fun n => toMaxPrefixList_incN_aux (incN_of_inc n h)⟩, ?_⟩
  rintro ⟨l, rfl⟩
  rw [toMaxPrefixList_app]
  exact inc_op_left ..

@[rocq_alias to_max_prefix_list_included_L]
theorem toMaxPrefixList_inc_iff_prefix {l1 l2 : List α} :
    toMaxPrefixList l1 ≼ toMaxPrefixList l2 ↔ l1 <+: l2 :=
  toMaxPrefixList_inc_iff.trans (exists_congr fun _ => eq_comm)

/-! ## Validity of compositions -/

@[rocq_alias to_max_prefix_list_op_validN_aux]
theorem toMaxPrefixList_op_validN_aux {n} {l1 l2 : List α} (hlen : l1.length ≤ l2.length)
    (h : ✓{n} (toMaxPrefixList l1 • toMaxPrefixList l2)) :
    l2 ≡{n}≡ l1 ++ l2.drop l1.length := by
  refine list_dist_lookup.mpr fun i => ?_
  have hi := validN_toMap.mp h i
  rw [toMap_op, Heap.get?_op, get?_toMaxPrefixList, get?_toMaxPrefixList] at hi
  rw [List.getElem?_append]
  cases h1 : l1[i]? with
  | none =>
    have hlen1 : l1.length ≤ i := List.getElem?_eq_none_iff.mp h1
    refine .of_eq ?_
    rw [if_neg (by omega), List.getElem?_drop, show l1.length + (i - l1.length) = i by omega]
  | some x1 =>
    have hlt := (List.getElem?_eq_some_iff.mp h1).1
    cases h2 : l2[i]? with
    | none => exact absurd (List.getElem?_eq_none_iff.mp h2) (by omega)
    | some x2 =>
      rw [if_pos hlt]
      rw [h1, h2] at hi
      have hv : ✓{n} (toAgree x1 • toAgree x2) := by
        simpa [op, optionOp, Option.some_validN] using hi
      exact some_dist_some.mpr (Agree.toAgree_op_validN_iff_dist.mp hv).symm

@[rocq_alias to_max_prefix_list_op_validN]
theorem toMaxPrefixList_op_validN {n} {l1 l2 : List α} :
    ✓{n} (toMaxPrefixList l1 • toMaxPrefixList l2)
      ↔ (∃ l, l2 ≡{n}≡ l1 ++ l) ∨ (∃ l, l1 ≡{n}≡ l2 ++ l) := by
  refine ⟨fun h => ?_, ?_⟩
  · by_cases hlen : l1.length ≤ l2.length
    · exact .inl ⟨_, toMaxPrefixList_op_validN_aux hlen h⟩
    · exact .inr ⟨_, toMaxPrefixList_op_validN_aux (by omega) (comm'.dist.validN.mp h)⟩
  · rintro (⟨l, hl⟩ | ⟨l, hl⟩)
    · refine (Dist.validN (toMaxPrefixList_ne.ne hl).op_r).mpr ?_
      rw [toMaxPrefixList_op_left (List.prefix_append ..)]
      exact toMaxPrefixList_validN _
    · refine (Dist.validN (toMaxPrefixList_ne.ne hl).op_l).mpr ?_
      rw [toMaxPrefixList_op_right (List.prefix_append ..)]
      exact toMaxPrefixList_validN _

@[rocq_alias to_max_prefix_list_op_valid]
theorem toMaxPrefixList_op_valid {l1 l2 : List α} :
    ✓ (toMaxPrefixList l1 • toMaxPrefixList l2)
      ↔ (∃ l, l2 = l1 ++ l) ∨ (∃ l, l1 = l2 ++ l) := by
  refine ⟨fun h => ?_, ?_⟩
  · by_cases hlen : l1.length ≤ l2.length
    · exact .inl ⟨_, eq_dist.mpr fun n => toMaxPrefixList_op_validN_aux hlen h.validN⟩
    · exact .inr ⟨_, eq_dist.mpr fun n =>
        toMaxPrefixList_op_validN_aux (by omega) (comm'.dist.validN.mp h.validN)⟩
  · rintro (⟨l, rfl⟩ | ⟨l, rfl⟩)
    · rw [toMaxPrefixList_op_left (List.prefix_append ..)]
      exact toMaxPrefixList_valid _
    · rw [toMaxPrefixList_op_right (List.prefix_append ..)]
      exact toMaxPrefixList_valid _

@[rocq_alias to_max_prefix_list_op_valid_L]
theorem toMaxPrefixList_op_valid_prefix {l1 l2 : List α} :
    ✓ (toMaxPrefixList l1 • toMaxPrefixList l2) ↔ l1 <+: l2 ∨ l2 <+: l1 :=
  toMaxPrefixList_op_valid.trans
    (or_congr (exists_congr fun _ => eq_comm) (exists_congr fun _ => eq_comm))

/-! ## Local updates -/

@[rocq_alias max_prefix_list_local_update]
theorem local_update {l1 l2 : List α} (h : l1 <+: l2) :
    (toMaxPrefixList l1, toMaxPrefixList l1) ~l~> (toMaxPrefixList l2, toMaxPrefixList l2) := by
  obtain ⟨l, rfl⟩ := h
  rw [toMaxPrefixList_app, comm' (x := toMaxPrefixList l1)]
  refine LocalUpdate.op fun n _ => ?_
  rw [comm', ← toMaxPrefixList_app]
  exact toMaxPrefixList_validN _

end MaxPrefixList

/-! ## Functors -/

open MaxPrefixList

@[rocq_alias max_prefix_listURF]
abbrev MaxPrefixListURF (F : COFE.OFunctorPre) : COFE.OFunctorPre :=
  fun A B _ _ => MaxPrefixList (F A B)

/-- The underlying map functor that `MaxPrefixListURF` wraps. -/
abbrev MaxPrefixListMapOF (F : COFE.OFunctorPre) : COFE.OFunctorPre :=
  PartialMap.PartialMapOF MaxPrefixListMap (AgreeRF F)

instance {F} [COFE.OFunctor F] : URFunctor (MaxPrefixListURF F) where
  map f g := homLift (URFunctor.map (F := MaxPrefixListMapOF F) f g)
  map_ne.ne _ _ _ hf _ _ hg x :=
    dist_toMap.mpr ((URFunctor.map_ne (F := MaxPrefixListMapOF F)).ne hf hg x.toMap)
  map_id x := toMap_inj (URFunctor.map_id (F := MaxPrefixListMapOF F) x.toMap)
  map_comp f g f' g' x :=
    toMap_inj (URFunctor.map_comp (F := MaxPrefixListMapOF F) f g f' g' x.toMap)

@[rocq_alias max_prefix_listURF_contractive]
instance {F} [COFE.OFunctorContractive F] : URFunctorContractive (MaxPrefixListURF F) where
  map_contractive.1 h x := dist_toMap.mpr
    ((URFunctorContractive.map_contractive (F := MaxPrefixListMapOF F)).1 h x.toMap)

@[rocq_alias max_prefix_listRF]
abbrev MaxPrefixListRF (F : COFE.OFunctorPre) : COFE.OFunctorPre := MaxPrefixListURF F

#rocq_ignore max_prefix_listRF_contractive "Found by typeclass inference"

end Iris
