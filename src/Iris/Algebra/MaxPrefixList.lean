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
