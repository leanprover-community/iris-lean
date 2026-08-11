/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.Agree
public import Iris.Algebra.Heap
public import Iris.Algebra.List
public import Iris.Algebra.LocalUpdates
public import Iris.Std.HeapInstances
meta import Iris.Std.RocqPorting

/-! # Max prefix lists

An RA on lists, whose composition is the longer of the two lists, when their prefixes agree.
Here, the term "List" be being used liberally: it is implemented with an ExtTreeMap rather than
the List type itself. However, there is an embedding of Lists in to this data structure. -/

@[expose] public section

namespace Iris

open OFE CMRA Std

abbrev MaxPrefixListMap : Type _ → Type _ :=
  (Std.ExtTreeMap Nat · compare)

@[rocq_alias max_prefix_list, rocq_alias max_prefix_listR, rocq_alias max_prefix_listUR]
abbrev MaxPrefixList : Type _ → Type _ :=
  (MaxPrefixListMap <| Agree ·)

namespace MaxPrefixList

variable {α : Type _}

section Instances

variable [OFE α]

/-- OFE instance on [MaxPrefixList], inherited from the OFE on the underlying map. -/
instance instOFE : OFE (MaxPrefixList α) :=
  PartialMap.instOFE (M := MaxPrefixListMap) (K := Nat) (V := Agree α)

/-- CMRA instance on [MaxPrefixList], inherited from the CMRA on the underlying map. -/
instance instCMRA : CMRA (MaxPrefixList α) :=
  Heap.instStoreCMRA (M := MaxPrefixListMap) (K := Nat) (V := Agree α)

/-- UCMRA instance on [MaxPrefixList], inherited from the UCMRA on the underlying map. -/
instance instUCMRA : UCMRA (MaxPrefixList α) :=
  Heap.instStoreUCMRA (M := MaxPrefixListMap) (K := Nat) (V := Agree α)

instance instCoreId (x : MaxPrefixList α) : CoreId x :=
  Heap.instCoreId (M := MaxPrefixListMap) (K := Nat) (V := Agree α) (m := x)

instance instDiscrete [OFE.Discrete α] : CMRA.Discrete (MaxPrefixList α) where
  discrete_0 := OFE.discrete_0 (α := MaxPrefixListMap (Agree α))
  discrete_valid := CMRA.discrete_valid (α := MaxPrefixListMap (Agree α))

end Instances

/-! ## Embedding of lists into MaxPrefixList -/

/-- `l`, placed at the indices `start`, `start + 1`, … -/
def ofListFrom (start : Nat) (l : List α) : MaxPrefixList α :=
  Std.PartialMap.map (M := MaxPrefixListMap) toAgree (FiniteMap.map_seq start l)

@[rocq_alias to_max_prefix_list]
def toMaxPrefixList (l : List α) : MaxPrefixList α := ofListFrom 0 l

theorem get?_ofListFrom {start i : Nat} {l : List α} :
    get? (M := MaxPrefixListMap) (ofListFrom start l) i
      = (if start ≤ i then l[i - start]? else none).map toAgree := by
  rw [ofListFrom, LawfulPartialMap.get?_map, LawfulFiniteMap.get?_map_seq]

theorem get?_toMaxPrefixList {i : Nat} {l : List α} :
    get? (M := MaxPrefixListMap) (toMaxPrefixList l) i = l[i]?.map toAgree := by
  simp [toMaxPrefixList, get?_ofListFrom]

variable [OFE α]

theorem toMaxPrefixList_nil : toMaxPrefixList ([] : List α) = UCMRA.unit := by
  refine LawfulPartialMap.equiv_iff_eq (M := MaxPrefixListMap).mp fun i => ?_
  rw [get?_toMaxPrefixList, List.getElem?_nil]
  exact (LawfulPartialMap.get?_empty i).symm

/-! ## OFE properties -/

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
  obtain hi : Option.map toAgree l1[i]? ≡{n}≡ Option.map toAgree l2[i]? := by
    rw [← get?_toMaxPrefixList, ← get?_toMaxPrefixList]
    exact h i
  cases h1 : l1[i]? <;> cases h2 : l2[i]? <;> rw [h1, h2] at hi <;> simp_all
  exact Agree.toAgree_injN hi

@[rocq_alias to_max_prefix_list_inj]
theorem toMaxPrefixList_inj {l1 l2 : List α}
    (h : toMaxPrefixList l1 = toMaxPrefixList l2) : l1 = l2 :=
  eq_dist.mpr fun _ => toMaxPrefixList_dist_inj (Dist.of_eq h)

/-! ## CMRA Properties -/

@[rocq_alias to_max_prefix_list_valid]
theorem toMaxPrefixList_valid (l : List α) : ✓ toMaxPrefixList l := fun i => by
  rw [get?_toMaxPrefixList]
  cases l[i]? with
  | none => trivial
  | some a => exact Agree.toAgree_valid

@[rocq_alias to_max_prefix_list_validN]
theorem toMaxPrefixList_validN {n} (l : List α) : ✓{n} toMaxPrefixList l :=
  (toMaxPrefixList_valid l).validN

@[rocq_alias to_max_prefix_list_app]
theorem toMaxPrefixList_app (l1 l2 : List α) :
    toMaxPrefixList (l1 ++ l2) = toMaxPrefixList l1 • ofListFrom l1.length l2 := by
  refine LawfulPartialMap.equiv_iff_eq (M := MaxPrefixListMap).mp fun i => ?_
  rw [Heap.get?_op, get?_toMaxPrefixList, get?_toMaxPrefixList, get?_ofListFrom, List.getElem?_append]
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
  have hi := Heap.lookup_incN (M := MaxPrefixListMap).mp h i
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

@[rocq_alias to_max_prefix_list_op_validN_aux]
theorem toMaxPrefixList_op_validN_aux {n} {l1 l2 : List α} (hlen : l1.length ≤ l2.length)
    (h : ✓{n} (toMaxPrefixList l1 • toMaxPrefixList l2)) :
    l2 ≡{n}≡ l1 ++ l2.drop l1.length := by
  refine list_dist_lookup.mpr fun i => ?_
  obtain hi :  ✓{n} Option.map toAgree l1[i]? • Option.map toAgree l2[i]? := by
    rw [← get?_toMaxPrefixList, ← get?_toMaxPrefixList, ← Heap.get?_op]
    exact h i
  rw [List.getElem?_append]
  cases h1 : l1[i]? with
  | none =>
    have hlen1 : l1.length ≤ i := List.getElem?_eq_none_iff.mp h1
    refine .of_eq ?_
    rw [if_neg (by omega), List.getElem?_drop, show l1.length + (i - l1.length) = i by omega]
  | some x1 =>
    have hlt := (List.getElem?_eq_some_iff.mp h1).1
    cases h2 : l2[i]? with
    | none =>
      grind
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

/-! ## Updates -/

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

@[rocq_alias max_prefix_listURF]
abbrev MaxPrefixListURF (F : COFE.OFunctorPre) : COFE.OFunctorPre :=
  PartialMap.PartialMapOF MaxPrefixListMap (AgreeRF F)

@[rocq_alias max_prefix_listRF]
abbrev MaxPrefixListRF (F : COFE.OFunctorPre) : COFE.OFunctorPre := MaxPrefixListURF F

#rocq_ignore max_prefix_listURF_contractive "Found by typeclass inference"
#rocq_ignore max_prefix_listRF_contractive "Found by typeclass inference"

end Iris
