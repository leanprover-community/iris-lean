import Iris.Algebra.Agree
import Iris.Algebra.GenMap
import Iris.Algebra.LocalUpdates

namespace Iris

open OFE CMRA

abbrev MaxPrefixList (A : Type _) [OFE A] := GenMap Nat (Agree A)

def toMaxPrefixList {A : Type _} [OFE A] (l : List A) : MaxPrefixList A :=
  ⟨fun i => (l[i]?).map toAgree⟩

def shiftMaxPrefixList {A : Type _} [OFE A] (start : Nat) (l : List A) : MaxPrefixList A :=
  ⟨fun i => if _h : start ≤ i then (l[i - start]?).map toAgree else none⟩

instance {A : Type _} [OFE A] (m : MaxPrefixList A) : CoreId m := by
  rw [CMRA.coreId_iff_core_eqv_self]
  show (core m).car ≡ m.car
  intro i
  change core (m.car i) ≡ m.car i
  cases h : m.car i <;> rfl

instance toMaxPrefixList_ne {A : Type _} [OFE A] : NonExpansive (toMaxPrefixList (A := A)) where
  ne := by
    intro n x1 x2 h i
    unfold toMaxPrefixList
    specialize h i
    cases h1 : x1[i]? <;> cases h2 : x2[i]? <;> simp [h1, h2] at h ⊢
    exact OFE.NonExpansive.ne h

theorem toMaxPrefixList_valid {A : Type _} [OFE A] (l : List A) : ✓ toMaxPrefixList l := by
  constructor
  · intro i
    unfold toMaxPrefixList
    cases h : l[i]? <;> simp [h, CMRA.Valid, Agree.valid, Agree.validN, toAgree]
  · refine ⟨fun n => l.length + n, ?_, ?_⟩
    · intro n
      unfold IsFree toMaxPrefixList
      simp [Nat.le_add_right]
    · intro n m h
      omega

theorem toMaxPrefixList_validN {A : Type _} [OFE A] (n : Nat) (l : List A) : ✓{n} toMaxPrefixList l :=
  (toMaxPrefixList_valid (A := A) l).validN

theorem toMaxPrefixList_dist_inj {A : Type _} [OFE A] {l1 l2 : List A} :
    toMaxPrefixList (A := A) l1 ≡{n}≡ toMaxPrefixList l2 → l1 ≡{n}≡ l2 := by
  intro h
  intro i
  specialize h i
  unfold toMaxPrefixList at h
  cases h1 : l1[i]? <;> cases h2 : l2[i]? <;> simp [h1, h2] at h ⊢
  exact Agree.toAgree_injN h

theorem toMaxPrefixList_inj {A : Type _} [OFE A] {l1 l2 : List A} :
    toMaxPrefixList (A := A) l1 ≡ toMaxPrefixList l2 → l1 ≡ l2 := by
  intro h
  intro i
  specialize h i
  unfold toMaxPrefixList at h
  cases h1 : l1[i]? <;> cases h2 : l2[i]? <;> simp [h1, h2] at h ⊢
  exact Agree.toAgree_inj h

theorem toMaxPrefixList_app {A : Type _} [OFE A] (l1 l2 : List A) :
    toMaxPrefixList (A := A) (l1 ++ l2) ≡
      toMaxPrefixList l1 • shiftMaxPrefixList l1.length l2 := by
  intro i
  simp [toMaxPrefixList, shiftMaxPrefixList, CMRA.op]
  by_cases h : i < l1.length
  · rw [List.getElem?_append_left h]
    simp [h, Nat.not_le_of_gt h]
  · have hle : l1.length ≤ i := Nat.le_of_not_lt h
    rw [List.getElem?_append_right hle]
    simp [h, hle]

theorem toMaxPrefixList_op_l {A : Type _} [OFE A] {l1 l2 : List A} :
    l1 <+: l2 → toMaxPrefixList l1 • toMaxPrefixList l2 ≡ toMaxPrefixList l2 := by
  intro h
  have hl : l1 ++ List.drop l1.length l2 = l2 := List.prefix_iff_eq_append.mp h
  have happ : toMaxPrefixList (A := A) (l1 ++ List.drop l1.length l2) ≡
      toMaxPrefixList l1 • shiftMaxPrefixList l1.length (List.drop l1.length l2) :=
    toMaxPrefixList_app (A := A) l1 (List.drop l1.length l2)
  have hidem : toMaxPrefixList (A := A) l1 • toMaxPrefixList l1 ≡ toMaxPrefixList l1 := by
    intro i
    unfold toMaxPrefixList
    cases h : l1[i]? <;> simp [h, CMRA.op, Agree.idemp]
  calc
    toMaxPrefixList l1 • toMaxPrefixList l2
        ≡ toMaxPrefixList l1 • toMaxPrefixList (l1 ++ List.drop l1.length l2) := by rw [hl]
    _ ≡ toMaxPrefixList l1 • (toMaxPrefixList l1 • shiftMaxPrefixList l1.length (List.drop l1.length l2)) := happ.op_r
    _ ≡ (toMaxPrefixList l1 • toMaxPrefixList l1) • shiftMaxPrefixList l1.length (List.drop l1.length l2) := assoc
    _ ≡ toMaxPrefixList l1 • shiftMaxPrefixList l1.length (List.drop l1.length l2) := hidem.op_l
    _ ≡ toMaxPrefixList (l1 ++ List.drop l1.length l2) := happ.symm
    _ ≡ toMaxPrefixList l2 := by rw [hl]

theorem toMaxPrefixList_op_r {A : Type _} [OFE A] {l1 l2 : List A} :
    l1 <+: l2 → toMaxPrefixList l2 • toMaxPrefixList l1 ≡ toMaxPrefixList l2 := by
  intro h
  exact comm.trans (toMaxPrefixList_op_l (A := A) h)

theorem toMaxPrefixList_op_validN_aux {A : Type _} [OFE A] (n : Nat) (l1 l2 : List A) :
    l1.length ≤ l2.length →
      ✓{n} (toMaxPrefixList (A := A) l1 • toMaxPrefixList l2) →
        l2 ≡{n}≡ l1 ++ List.drop l1.length l2 := by
  intro hlen hvalid
  intro i
  by_cases hi : i < l1.length
  · have hi2 : i < l2.length := Nat.lt_of_lt_of_le hi hlen
    have hv : ✓{n} (Option.map toAgree l1[i]? • Option.map toAgree l2[i]?) := by
      simpa [toMaxPrefixList, CMRA.op] using hvalid.1 i
    have h1 : l1[i]? = some l1[i] := List.getElem?_eq_getElem hi
    have h2 : l2[i]? = some l2[i] := List.getElem?_eq_getElem hi2
    rw [List.getElem?_append_left hi, h1, h2]
    rw [h1, h2] at hv
    exact (Agree.toAgree_op_validN_iff_dist (a := l1[i]) (b := l2[i])).1 hv |>.symm
  · have hge : l1.length ≤ i := Nat.le_of_not_lt hi
    rw [List.getElem?_append_right hge, List.getElem?_drop]
    have hs : l1.length + (i - l1.length) = i := Nat.add_sub_of_le hge
    simpa [hs]

theorem toMaxPrefixList_op_validN {A : Type _} [OFE A] (n : Nat) (l1 l2 : List A) :
    ✓{n} (toMaxPrefixList (A := A) l1 • toMaxPrefixList l2) ↔
      (∃ t, l2 ≡{n}≡ l1 ++ t) ∨ (∃ t, l1 ≡{n}≡ l2 ++ t) := by
  constructor
  · intro h
    by_cases hlen : l1.length ≤ l2.length
    · left
      exact ⟨List.drop l1.length l2, toMaxPrefixList_op_validN_aux (A := A) n l1 l2 hlen h⟩
    · right
      have hcomm : ✓{n} (toMaxPrefixList (A := A) l2 • toMaxPrefixList l1) := CMRA.validN_ne (CMRA.comm.dist) h
      have hlen' : l2.length ≤ l1.length := Nat.le_of_lt (Nat.lt_of_not_ge hlen)
      exact ⟨List.drop l2.length l1, toMaxPrefixList_op_validN_aux (A := A) n l2 l1 hlen' hcomm⟩
  · rintro (⟨t, ht⟩ | ⟨t, ht⟩)
    · have hp : l1 <+: l1 ++ t := ⟨t, rfl⟩
      have hEqMap : toMaxPrefixList (A := A) l2 ≡{n}≡ toMaxPrefixList (l1 ++ t) := toMaxPrefixList_ne.ne ht
      have hvalid : ✓{n} (toMaxPrefixList (A := A) l1 • toMaxPrefixList (l1 ++ t)) :=
        (toMaxPrefixList_op_l (A := A) hp).dist.validN.mpr (toMaxPrefixList_validN (A := A) n (l1 ++ t))
      exact CMRA.validN_ne ((hEqMap.op_r).symm) hvalid
    · have hp : l2 <+: l2 ++ t := ⟨t, rfl⟩
      have hEqMap : toMaxPrefixList (A := A) l1 ≡{n}≡ toMaxPrefixList (l2 ++ t) := toMaxPrefixList_ne.ne ht
      have hvalid : ✓{n} (toMaxPrefixList (A := A) (l2 ++ t) • toMaxPrefixList l2) :=
        (toMaxPrefixList_op_r (A := A) hp).dist.validN.mpr (toMaxPrefixList_validN (A := A) n (l2 ++ t))
      exact CMRA.validN_ne ((hEqMap.op_l).symm) hvalid

theorem toMaxPrefixList_op_valid {A : Type _} [OFE A] (l1 l2 : List A) :
    ✓ (toMaxPrefixList (A := A) l1 • toMaxPrefixList l2) ↔
      (∃ t, l2 ≡ l1 ++ t) ∨ (∃ t, l1 ≡ l2 ++ t) := by
  rw [CMRA.valid_iff_validN]
  constructor
  · intro h
    by_cases hlen : l1.length ≤ l2.length
    · left
      refine ⟨List.drop l1.length l2, ?_⟩
      exact OFE.equiv_dist.2 fun n => toMaxPrefixList_op_validN_aux (A := A) n l1 l2 hlen (h n)
    · right
      have hlen' : l2.length ≤ l1.length := Nat.le_of_lt (Nat.lt_of_not_ge hlen)
      refine ⟨List.drop l2.length l1, ?_⟩
      exact OFE.equiv_dist.2 fun n =>
        toMaxPrefixList_op_validN_aux (A := A) n l2 l1 hlen' (CMRA.validN_ne (CMRA.comm.dist) (h n))
  · intro h n
    exact (toMaxPrefixList_op_validN (A := A) n l1 l2).2 <|
      match h with
      | Or.inl ⟨t, ht⟩ => Or.inl ⟨t, ht.dist⟩
      | Or.inr ⟨t, ht⟩ => Or.inr ⟨t, ht.dist⟩

theorem toMaxPrefixList_mono {A : Type _} [OFE A] {l1 l2 : List A} :
    l1 <+: l2 → toMaxPrefixList l1 ≼ toMaxPrefixList l2 := by
  intro h
  have hl : l1 ++ List.drop l1.length l2 = l2 := List.prefix_iff_eq_append.mp h
  let z := shiftMaxPrefixList (A := A) l1.length (List.drop l1.length l2)
  have happ : toMaxPrefixList (A := A) (l1 ++ List.drop l1.length l2) ≡
      toMaxPrefixList l1 • z := by
    simpa [z] using toMaxPrefixList_app (A := A) l1 (List.drop l1.length l2)
  refine ⟨z, ?_⟩
  exact (OFE.Equiv.of_eq (by simpa [hl])).trans happ

theorem toMaxPrefixList_includedN {A : Type _} [OFE A] (n : Nat) (l1 l2 : List A) :
    toMaxPrefixList (A := A) l1 ≼{n} toMaxPrefixList l2 ↔ ∃ t, l2 ≡{n}≡ l1 ++ t := by
  constructor
  · intro h
    rcases h with ⟨z, hz⟩
    refine ⟨List.drop l1.length l2, ?_⟩
    intro i
    by_cases hi : i < l1.length
    · have h1 : l1[i]? = some l1[i] := List.getElem?_eq_getElem hi
      rw [List.getElem?_append_left hi, h1]
      have hiinc : some (toAgree l1[i]) ≼{n} (toMaxPrefixList (A := A) l2).car i := by
        refine ⟨z.car i, ?_⟩
        simpa [toMaxPrefixList, CMRA.op, h1] using hz i
      cases h2 : l2[i]? with
      | none =>
          have : some (toAgree l1[i]) ≼{n} none := by simpa [toMaxPrefixList, h2] using hiinc
          rcases this with ⟨w, hEq⟩
          cases w with
          | none => exact False.elim (not_none_dist_some hEq)
          | some val => exact False.elim (not_none_dist_some hEq)
      | some y =>
          have hiinc' : some (toAgree l1[i]) ≼{n} some (toAgree y) := by
            simpa [toMaxPrefixList, h2] using hiinc
          have hagree : toAgree l1[i] ≼{n} toAgree y := Option.some_incN_some_iff_isTotal.mp hiinc'
          have hy : l1[i] ≡{n}≡ y := Agree.toAgree_includedN.mp hagree
          have hi2 : i < l2.length := (List.getElem?_eq_some_iff.mp h2).1
          simpa [List.getElem?_eq_getElem hi2, h2] using hy.symm
    · have hge : l1.length ≤ i := Nat.le_of_not_lt hi
      rw [List.getElem?_append_right hge, List.getElem?_drop]
      have hs : l1.length + (i - l1.length) = i := Nat.add_sub_of_le hge
      simpa [hs]
  · rintro ⟨t, ht⟩
    have happ : toMaxPrefixList (A := A) (l1 ++ t) ≡{n}≡
        (toMaxPrefixList l1 • shiftMaxPrefixList l1.length t) := (toMaxPrefixList_app (A := A) l1 t).dist
    have hbase : toMaxPrefixList (A := A) l1 ≼{n} (toMaxPrefixList l1 • shiftMaxPrefixList l1.length t) :=
      CMRA.incN_op_left n _ _
    have hstep : toMaxPrefixList (A := A) l1 ≼{n} toMaxPrefixList (l1 ++ t) := (happ.incN_r).mpr hbase
    have hmap : toMaxPrefixList (A := A) (l1 ++ t) ≡{n}≡ toMaxPrefixList l2 := toMaxPrefixList_ne.ne ht.symm
    exact (hmap.incN_r).mp hstep

theorem toMaxPrefixList_included {A : Type _} [OFE A] (l1 l2 : List A) :
    toMaxPrefixList (A := A) l1 ≼ toMaxPrefixList l2 ↔ ∃ t, l2 ≡ l1 ++ t := by
  constructor
  · intro h
    rcases h with ⟨z, hz⟩
    refine ⟨List.drop l1.length l2, ?_⟩
    intro i
    by_cases hi : i < l1.length
    · have h1 : l1[i]? = some l1[i] := List.getElem?_eq_getElem hi
      rw [List.getElem?_append_left hi, h1]
      have hiinc : some (toAgree l1[i]) ≼ (toMaxPrefixList (A := A) l2).car i := by
        refine ⟨z.car i, ?_⟩
        simpa [toMaxPrefixList, CMRA.op, h1] using hz i
      cases h2 : l2[i]? with
      | none =>
          have : some (toAgree l1[i]) ≼ none := by simpa [toMaxPrefixList, h2] using hiinc
          rcases this with ⟨w, hEq⟩
          cases w with
          | none => exact False.elim (not_none_eqv_some hEq)
          | some val => exact False.elim (not_none_eqv_some hEq)
      | some y =>
          have hiinc' : some (toAgree l1[i]) ≼ some (toAgree y) := by
            simpa [toMaxPrefixList, h2] using hiinc
          have hagree : toAgree l1[i] ≼ toAgree y := Option.some_inc_some_iff_isTotal.mp hiinc'
          have hy : l1[i] ≡ y := Agree.toAgree_included.mp hagree
          have hi2 : i < l2.length := (List.getElem?_eq_some_iff.mp h2).1
          simpa [List.getElem?_eq_getElem hi2, h2] using hy.symm
    · have hge : l1.length ≤ i := Nat.le_of_not_lt hi
      rw [List.getElem?_append_right hge, List.getElem?_drop]
      have hs : l1.length + (i - l1.length) = i := Nat.add_sub_of_le hge
      simpa [hs]
  · rintro ⟨t, ht⟩
    refine ⟨shiftMaxPrefixList (A := A) l1.length t, ?_⟩
    calc
      toMaxPrefixList (A := A) l2 ≡ toMaxPrefixList (l1 ++ t) := OFE.NonExpansive.eqv ht
      _ ≡ toMaxPrefixList l1 • shiftMaxPrefixList l1.length t := toMaxPrefixList_app (A := A) l1 t

theorem toMaxPrefixList_included_L {A : Type _} [OFE A] [Leibniz A] (l1 l2 : List A) :
    toMaxPrefixList (A := A) l1 ≼ toMaxPrefixList l2 ↔ l1 <+: l2 := by
  rw [toMaxPrefixList_included]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, Leibniz.eq_of_eqv ht.symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, Equiv.rfl⟩

theorem maxPrefixList_localUpdate {A : Type _} [OFE A] {l1 l2 : List A} :
    l1 <+: l2 →
      (toMaxPrefixList l1, toMaxPrefixList l1) ~l~>
        (toMaxPrefixList l2, toMaxPrefixList l2) := by
  intro h
  have hl : l1 ++ List.drop l1.length l2 = l2 := List.prefix_iff_eq_append.mp h
  let z := shiftMaxPrefixList (A := A) l1.length (List.drop l1.length l2)
  have happ := toMaxPrefixList_app (A := A) l1 (List.drop l1.length l2)
  have hzEq : z • toMaxPrefixList l1 ≡ toMaxPrefixList l2 := by
    calc
      z • toMaxPrefixList l1 ≡ toMaxPrefixList l1 • z := comm
      _ ≡ toMaxPrefixList (l1 ++ List.drop l1.length l2) := happ.symm
      _ ≡ toMaxPrefixList l2 := by rw [hl]
  have hz : ∀ n, ✓{n} toMaxPrefixList l1 → ✓{n} (z • toMaxPrefixList l1) := by
    intro n _
    exact hzEq.dist.validN.mpr (toMaxPrefixList_valid (A := A) l2).validN
  exact LocalUpdate.equiv_right (x := (toMaxPrefixList l1, toMaxPrefixList l1))
    (y := (z • toMaxPrefixList l1, z • toMaxPrefixList l1))
    (z := (toMaxPrefixList l2, toMaxPrefixList l2))
    ⟨hzEq, hzEq⟩
    (LocalUpdate.op (x := toMaxPrefixList l1) (y := toMaxPrefixList l1) (z := z) hz)

abbrev MaxPrefixListURF (F : COFE.OFunctorPre) [RFunctor F] : COFE.OFunctorPre :=
  GenMapOF Nat (AgreeRF F)

instance {F} [RFunctor F] : URFunctor (MaxPrefixListURF F) := by
  simpa [MaxPrefixListURF] using (inferInstance : URFunctor (GenMapOF Nat (AgreeRF F)))

instance {F} [RFunctorContractive F] : URFunctorContractive (MaxPrefixListURF F) := by
  simpa [MaxPrefixListURF] using (inferInstance : URFunctorContractive (GenMapOF Nat (AgreeRF F)))

abbrev MaxPrefixListRF (F : COFE.OFunctorPre) [RFunctor F] : COFE.OFunctorPre :=
  GenMapOF Nat (AgreeRF F)

instance {F} [RFunctor F] : RFunctor (MaxPrefixListRF F) := by
  simpa [MaxPrefixListRF] using (inferInstance : RFunctor (GenMapOF Nat (AgreeRF F)))

instance {F} [RFunctorContractive F] : RFunctorContractive (MaxPrefixListRF F) := by
  simpa [MaxPrefixListRF] using (inferInstance : RFunctorContractive (GenMapOF Nat (AgreeRF F)))

end Iris
