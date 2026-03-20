import Iris.Algebra.CMRA
import Iris.Algebra.LocalUpdates
import Iris.Algebra.Updates
import Iris.Std.HeapInstances

namespace Iris

open OFE CMRA
open Iris.Std PartialMap LawfulPartialMap

abbrev PosNat := { n : Nat // 0 < n }

structure GMultiset (K : Type _) [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K] where
  car : Std.TreeMap K PosNat compare

namespace GMultiset

variable {K : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]

def equiv (X Y : GMultiset K) : Prop :=
  ∀ k : K, X.car[k]? = Y.car[k]?

abbrev empty : GMultiset K :=
  { car := (∅ : Std.TreeMap K PosNat compare) }

instance : OFE (GMultiset K) :=
  OFE.ofDiscrete equiv (by
    constructor
    · intro X k
      rfl
    · intro X Y h k
      exact (h k).symm
    · intro X Y Z h1 h2 k
      exact (h1 k).trans (h2 k))

@[simp] theorem equiv_def {X Y : GMultiset K} : X ≡ Y ↔ ∀ k : K, X.car[k]? = Y.car[k]? :=
  Iff.rfl

instance : OFE.Discrete (GMultiset K) where
  discrete_0 h := h

private def addCounts (_ : K) (n m : PosNat) : PosNat :=
  ⟨n.1 + m.1, Nat.add_pos_left n.2 _⟩

private abbrev opG (X Y : GMultiset K) : GMultiset K :=
  { car := Iris.Std.merge (M := fun V => Std.TreeMap K V compare) (K := K) addCounts X.car Y.car }

private theorem empty_op_empty_eqv :
    (empty (K := K)) ≡ opG (empty (K := K)) (empty (K := K)) := by
  intro k
  change none = Iris.Std.get? (M := fun V => Std.TreeMap K V compare)
    (Iris.Std.merge (M := fun V => Std.TreeMap K V compare) (K := K) addCounts
      ((∅ : Std.TreeMap K PosNat compare)) ((∅ : Std.TreeMap K PosNat compare))) k
  have h0 : Iris.Std.get? (M := fun V => Std.TreeMap K V compare)
      ((∅ : Std.TreeMap K PosNat compare)) k = none :=
    LawfulPartialMap.get?_empty (M := fun V => Std.TreeMap K V compare) (K := K) k
  rw [LawfulPartialMap.get?_merge]
  simp [h0, Option.merge]

private theorem op_assoc_eqv (X Y Z : GMultiset K) :
    opG X (opG Y Z) ≡ opG (opG X Y) Z := by
  intro k
  change (Iris.Std.get? (M := fun V => Std.TreeMap K V compare)
      (Iris.Std.merge (M := fun V => Std.TreeMap K V compare) (K := K) addCounts X.car
        (Iris.Std.merge (M := fun V => Std.TreeMap K V compare) (K := K) addCounts Y.car Z.car)) k =
    Iris.Std.get? (M := fun V => Std.TreeMap K V compare)
      (Iris.Std.merge (M := fun V => Std.TreeMap K V compare) (K := K) addCounts
        (Iris.Std.merge (M := fun V => Std.TreeMap K V compare) (K := K) addCounts X.car Y.car) Z.car) k)
  repeat rw [LawfulPartialMap.get?_merge]
  cases hx : Iris.Std.get? (M := fun V => Std.TreeMap K V compare) X.car k <;>
    cases hy : Iris.Std.get? (M := fun V => Std.TreeMap K V compare) Y.car k <;>
    cases hz : Iris.Std.get? (M := fun V => Std.TreeMap K V compare) Z.car k <;>
    simp [addCounts, Option.merge, Nat.add_assoc]

private theorem op_comm_eqv (X Y : GMultiset K) :
    opG X Y ≡ opG Y X := by
  intro k
  change (Iris.Std.get? (M := fun V => Std.TreeMap K V compare)
      (Iris.Std.merge (M := fun V => Std.TreeMap K V compare) (K := K) addCounts X.car Y.car) k =
    Iris.Std.get? (M := fun V => Std.TreeMap K V compare)
      (Iris.Std.merge (M := fun V => Std.TreeMap K V compare) (K := K) addCounts Y.car X.car) k)
  repeat rw [LawfulPartialMap.get?_merge]
  cases hx : Iris.Std.get? (M := fun V => Std.TreeMap K V compare) X.car k <;>
    cases hy : Iris.Std.get? (M := fun V => Std.TreeMap K V compare) Y.car k <;>
    simp [addCounts, Option.merge, Nat.add_comm]

instance opG_ne (x : GMultiset K) : NonExpansive (opG x) where
  ne := by
    intro n Y1 Y2 h k
    change Iris.Std.get? (M := fun V => Std.TreeMap K V compare)
      (Iris.Std.merge (M := fun V => Std.TreeMap K V compare) (K := K) addCounts x.car Y1.car) k =
      Iris.Std.get? (M := fun V => Std.TreeMap K V compare)
        (Iris.Std.merge (M := fun V => Std.TreeMap K V compare) (K := K) addCounts x.car Y2.car) k
    repeat rw [LawfulPartialMap.get?_merge]
    simpa [addCounts] using
      congrArg (Option.merge (addCounts k)
        (Iris.Std.get? (M := fun V => Std.TreeMap K V compare) x.car k)) (h k)

instance : CMRA (GMultiset K) where
  pcore _ := some (empty (K := K))
  op := opG
  ValidN _ _ := True
  Valid _ := True

  op_ne := inferInstance
  pcore_ne := by
    intro n X Y h cx hcx
    cases hcx
    exact ⟨empty (K := K), rfl, Dist.rfl⟩
  validN_ne {n x y} := by
    intro _ _
    trivial

  valid_iff_validN {x} := ⟨fun _ _ => trivial, fun _ => trivial⟩
  validN_succ {n x} := by intro _; trivial
  validN_op_left {n x y} := by intro _; trivial

  assoc := op_assoc_eqv _ _ _
  comm := op_comm_eqv _ _

  pcore_op_left {x cx} := by
    intro hcx i
    cases hcx
    change (Iris.Std.get? (M := fun V => Std.TreeMap K V compare)
      (Iris.Std.merge (M := fun V => Std.TreeMap K V compare) (K := K) addCounts
        ((∅ : Std.TreeMap K PosNat compare)) x.car) i =
      Iris.Std.get? (M := fun V => Std.TreeMap K V compare) x.car i)
    have h0 : Iris.Std.get? (M := fun V => Std.TreeMap K V compare)
        ((∅ : Std.TreeMap K PosNat compare)) i = none :=
      LawfulPartialMap.get?_empty (M := fun V => Std.TreeMap K V compare) (K := K) i
    rw [LawfulPartialMap.get?_merge, h0]
    cases hx : Iris.Std.get? (M := fun V => Std.TreeMap K V compare) x.car i <;>
      simp [Option.merge]
  pcore_idem {x cx} := by
    intro hcx
    have : cx = empty (K := K) := Option.some.inj hcx.symm
    subst this
    exact Equiv.rfl
  pcore_op_mono {x cx} := by
    intro hcx y
    cases hcx
    refine ⟨empty (K := K), ?_⟩
    exact OFE.some_eqv_some.mpr empty_op_empty_eqv
  extend {n x y1 y2} := by
    intro _ h
    exact ⟨y1, ⟨y2, h, Dist.rfl, Dist.rfl⟩⟩

instance : CMRA.Discrete (GMultiset K) where
  discrete_valid {x} := by
    intro _; trivial

instance : UCMRA (GMultiset K) where
  unit := empty (K := K)
  unit_valid := trivial
  unit_left_id {x} := by
    intro i
    change (Iris.Std.get? (M := fun V => Std.TreeMap K V compare)
      (Iris.Std.merge (M := fun V => Std.TreeMap K V compare) (K := K) addCounts
        ((∅ : Std.TreeMap K PosNat compare)) x.car) i =
      Iris.Std.get? (M := fun V => Std.TreeMap K V compare) x.car i)
    have h0 : Iris.Std.get? (M := fun V => Std.TreeMap K V compare)
        ((∅ : Std.TreeMap K PosNat compare)) i = none :=
      LawfulPartialMap.get?_empty (M := fun V => Std.TreeMap K V compare) (K := K) i
    rw [LawfulPartialMap.get?_merge, h0]
    cases hx : Iris.Std.get? (M := fun V => Std.TreeMap K V compare) x.car i <;>
      simp [Option.merge]
  pcore_unit := by
    rfl

theorem gMultiset_update (X Y : GMultiset K) : X ~~> Y := by
  intro _ _ _
  trivial

end GMultiset

end Iris
