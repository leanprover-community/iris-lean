/-
Copyright (c) The Iris-Lean Contributors
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

open OFE ORA Iris.Std

abbrev MaxPrefixListMap : Type _ → Type _ :=
  (Std.ExtTreeMap Nat · compare)

@[rocq_alias max_prefix_list, rocq_alias max_prefix_listR, rocq_alias max_prefix_listUR, implicit_reducible]
def MaxPrefixList : Type _ → Type _ :=
  (MaxPrefixListMap <| Agree ·)

namespace MaxPrefixList

variable {α : Type _}

section Instances

variable [OFE α]

/-- OFE instance on [MaxPrefixList], inherited from the OFE on the underlying map. -/
instance instOFE : OFE (MaxPrefixList α) :=
  PartialMap.instOFE (M:= MaxPrefixListMap) (V := Agree α)

/-- ORA instance on [MaxPrefixList], inherited from the ORA on the underlying map. -/
instance instORA : ORA (MaxPrefixList α) :=
  Heap.instStoreCMRA (M:= MaxPrefixListMap) (V := Agree α)

/-- UORA instance on `MaxPrefixList`, inherited from the UORA on the underlying map. -/
instance instUCMRA : UORA (MaxPrefixList α) :=
  Heap.instStoreUCMRA  (M:= MaxPrefixListMap) (V := Agree α)

instance instIsInc : IsInc (MaxPrefixList α) :=
  inferInstanceAs (IsInc (MaxPrefixListMap (Agree α)))

instance instCoreId (x : MaxPrefixList α) : CoreId x :=
  Heap.instCoreId (M:= MaxPrefixListMap) (V := Agree α)

instance instDiscrete [OFE.Discrete α] : ORA.Discrete (MaxPrefixList α) where
  discrete_0 := OFE.discrete_0 (α := MaxPrefixListMap (Agree α))
  discrete_valid := discrete_valid (α := MaxPrefixListMap (Agree α))
  discrete_ord := discrete_ord (α := MaxPrefixListMap (Agree α))

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
  grind [get?_ofListFrom, toMaxPrefixList]

variable [OFE α]

theorem toMaxPrefixList_nil : toMaxPrefixList ([] : List α) = unit := by
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
  eq_dist_2 fun _ => toMaxPrefixList_dist_inj (Dist.of_eq h)

/-! ## ORA Properties -/

@[local grind ., rocq_alias to_max_prefix_list_valid]
theorem toMaxPrefixList_valid (l : List α) : ✓ toMaxPrefixList l := fun i => by
  rw [get?_toMaxPrefixList]
  cases l[i]? with
  | none => trivial
  | some a => exact Agree.toAgree_valid

@[local grind ., rocq_alias to_max_prefix_list_validN]
theorem toMaxPrefixList_validN {n} (l : List α) : ✓{n} toMaxPrefixList l :=
  (toMaxPrefixList_valid l).validN

@[local grind =, rocq_alias to_max_prefix_list_app]
theorem toMaxPrefixList_app (l1 l2 : List α) :
    toMaxPrefixList (l1 ++ l2) = toMaxPrefixList l1 • ofListFrom l1.length l2 := by
  unfold MaxPrefixList
  refine LawfulPartialMap.equiv_iff_eq (M := MaxPrefixListMap).mp fun i => ?_
  rw [Heap.get?_op, get?_toMaxPrefixList, get?_toMaxPrefixList, get?_ofListFrom, List.getElem?_append]
  have op_none (x : Option (Agree α)) : x • none = x ∧ none • x = x :=
    ⟨unit_right_id, unit_left_id⟩
  grind

@[local grind →, rocq_alias to_max_prefix_list_op_l]
theorem toMaxPrefixList_op_left {l1 l2 : List α} (h : l1 <+: l2) :
    toMaxPrefixList l1 • toMaxPrefixList l2 = toMaxPrefixList l2 := by
  obtain ⟨l, rfl⟩ := h
  grind [assoc', op_self]

@[local grind →, rocq_alias to_max_prefix_list_op_r]
theorem toMaxPrefixList_op_right {l1 l2 : List α} (h : l1 <+: l2) :
    toMaxPrefixList l2 • toMaxPrefixList l1 = toMaxPrefixList l2 :=
  comm'.trans (toMaxPrefixList_op_left h)

theorem ord_iff_forall_ordN {ml1 ml2 : MaxPrefixList α} :
    ml1 ≼ₒ ml2 ↔ ∀ n, ml1 ≼ₒ{n} ml2 := by
  refine ⟨fun h _ => h.ordN, fun h k => ?_⟩
  have hk : ∀ n, get? (M := MaxPrefixListMap) ml1 k ≼ₒ{n} get? (M := MaxPrefixListMap) ml2 k :=
    fun n => h n k
  revert hk
  cases get? (M := MaxPrefixListMap) ml1 k <;> cases get? (M := MaxPrefixListMap) ml2 k <;>
    intro hk
  · trivial
  · exact hk 0
  · exact (hk 0).elim
  · refine .inr (Agree.ord.mpr (eq_dist_2 fun n => ?_))
    rcases hk n with e | o
    · exact (e.op_r.trans (Dist.of_eq Agree.idemp)).symm
    · exact Agree.ordN.mp o

@[rocq_alias max_prefix_list_included_includedN]
theorem inc_iff_forall_incN {ml1 ml2 : MaxPrefixList α} :
    ml1 ≼ ml2 ↔ ∀ n, ml1 ≼{n} ml2 :=
  inc_iff_ord.trans <| ord_iff_forall_ordN.trans <| forall_congr' fun _ => incN_iff_ordN.symm

theorem toMaxPrefixList_ordN_aux {n} {l1 l2 : List α}
    (h : toMaxPrefixList l1 ≼ₒ{n} toMaxPrefixList l2) : l2 ≡{n}≡ l1 ++ l2.drop l1.length := by
  refine list_dist_lookup.mpr fun i => ?_
  have hi : Option.map toAgree l1[i]? ≼ₒ{n} Option.map toAgree l2[i]? := by
    have := h i
    rwa [get?_toMaxPrefixList, get?_toMaxPrefixList] at this
  cases hx1 : l1[i]? with
  | none => exact .of_eq (by grind)
  | some x1 =>
    cases hx2 : l2[i]? with
    | none => rw [hx1, hx2] at hi; exact hi.elim
    | some x2 =>
      rw [hx1, hx2] at hi
      have hx : x1 ≡{n}≡ x2 := by
        rcases hi with e | o
        · exact Agree.toAgree_injN e
        · exact Agree.toAgree_ordN.mp o
      rw [List.getElem?_append, ite_eq_left (List.getElem?_eq_some_iff.mp hx1).1, hx1]
      exact some_dist_some.mpr hx.symm

@[rocq_alias to_max_prefix_list_includedN_aux]
theorem toMaxPrefixList_incN_aux {n} {l1 l2 : List α}
    (h : toMaxPrefixList l1 ≼{n} toMaxPrefixList l2) : l2 ≡{n}≡ l1 ++ l2.drop l1.length :=
  toMaxPrefixList_ordN_aux (incN_iff_ordN.mp h)

theorem toMaxPrefixList_ordN_iff {n} {l1 l2 : List α} :
    toMaxPrefixList l1 ≼ₒ{n} toMaxPrefixList l2 ↔ ∃ l, l2 ≡{n}≡ l1 ++ l := by
  refine ⟨fun h => ⟨_, toMaxPrefixList_ordN_aux h⟩, fun ⟨l, hl⟩ => ?_⟩
  refine ordN_of_ordN_of_dist ?_ (toMaxPrefixList_ne.ne hl).symm
  rw [← toMaxPrefixList_op_left (List.prefix_append l1 l)]
  exact ordN_op_left n _ _

@[rocq_alias to_max_prefix_list_includedN]
theorem toMaxPrefixList_incN_iff {n} {l1 l2 : List α} :
    toMaxPrefixList l1 ≼{n} toMaxPrefixList l2 ↔ ∃ l, l2 ≡{n}≡ l1 ++ l :=
  incN_iff_ordN.trans toMaxPrefixList_ordN_iff

theorem toMaxPrefixList_ord_iff {l1 l2 : List α} :
    toMaxPrefixList l1 ≼ₒ toMaxPrefixList l2 ↔ l1 <+: l2 := by
  refine ⟨fun h => ⟨_, eq_dist_2 fun n => (toMaxPrefixList_ordN_aux h.ordN).symm⟩, fun h => ?_⟩
  rw [← toMaxPrefixList_op_left h]
  exact ord_op_left _ _

@[rocq_alias to_max_prefix_list_included]
theorem toMaxPrefixList_inc_iff {l1 l2 : List α} :
    toMaxPrefixList l1 ≼ toMaxPrefixList l2 ↔ l1 <+: l2 :=
  inc_iff_ord.trans toMaxPrefixList_ord_iff

#rocq_ignore to_max_prefix_list_included_L "Use toMaxPrefixList_inc_iff"

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
  | none => refine .of_eq (by grind)
  | some x1 =>
    cases h2 : l2[i]? with
    | none => grind
    | some x2 =>
      rw [h1, h2] at hi
      rw [ite_eq_left (List.getElem?_eq_some_iff.mp h1).1]
      refine some_dist_some.mpr (Agree.toAgree_op_validN_iff_dist.mp ?_).symm
      simpa [op, optionOp, Option.some_validN] using hi

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
      grind [List.prefix_append]
    · refine (Dist.validN (toMaxPrefixList_ne.ne hl).op_l).mpr ?_
      grind [List.prefix_append]

@[rocq_alias to_max_prefix_list_op_valid]
theorem toMaxPrefixList_op_valid {l1 l2 : List α} :
    ✓ (toMaxPrefixList l1 • toMaxPrefixList l2) ↔ l1 <+: l2 ∨ l2 <+: l1 := by
  refine ⟨fun h => ?_, ?_⟩
  · by_cases hlen : l1.length ≤ l2.length
    · exact .inl ⟨_, eq_dist_2 fun n => (toMaxPrefixList_op_validN_aux hlen h.validN).symm⟩
    · exact .inr ⟨_, eq_dist_2 fun n =>
        (toMaxPrefixList_op_validN_aux (by omega) (comm'.dist.validN.mp h.validN)).symm⟩
  · rintro (⟨l, rfl⟩ | ⟨l, rfl⟩) <;> grind [List.prefix_append]

#rocq_ignore to_max_prefix_list_op_valid_L "Use toMaxPrefixList_op_valid"

/-! ## Updates -/

@[rocq_alias max_prefix_list_local_update]
theorem local_update {l1 l2 : List α} (h : l1 <+: l2) :
    (toMaxPrefixList l1, toMaxPrefixList l1) ~l~> (toMaxPrefixList l2, toMaxPrefixList l2) := by
  grind [LocalUpdate.op, comm']

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
