import Iris.Algebra.Numbers

namespace Iris

open OFE CMRA
open scoped OrdCommMonoidLike

/-- Naturals under `max`, matching Coq's `max_natR`. -/
abbrev MaxNat := LeibnizO Nat

instance : COFE MaxNat := inferInstanceAs (COFE (LeibnizO Nat))
instance : OFE.Leibniz MaxNat := inferInstanceAs (OFE.Leibniz (LeibnizO Nat))
instance : OFE.Discrete MaxNat := inferInstanceAs (OFE.Discrete (LeibnizO Nat))
instance : Coe Nat MaxNat := ⟨(⟨·⟩)⟩
instance : Add MaxNat := ⟨fun x y => ((max x.1 y.1 : Nat) : MaxNat)⟩
instance : Zero MaxNat := ⟨((0 : Nat) : MaxNat)⟩

instance : Std.Associative (α := MaxNat) Add.add where
  assoc x y z := by
    apply LeibnizO.ext
    exact Nat.max_assoc x.1 y.1 z.1

instance : Std.Commutative (α := MaxNat) Add.add where
  comm x y := by
    apply LeibnizO.ext
    exact Nat.max_comm x.1 y.1

instance : Std.IdempotentOp (α := MaxNat) Add.add where
  idempotent x := by
    apply LeibnizO.ext
    exact Nat.max_self x.1

instance : Std.LawfulIdentity (α := MaxNat) Add.add 0 where
  left_id x := by
    apply LeibnizO.ext
    exact Nat.zero_max x.1
  right_id x := by
    apply LeibnizO.ext
    exact Nat.max_zero x.1

instance : CMRA MaxNat := inferInstanceAs (CMRA MaxNat)
instance : CMRA.Discrete MaxNat := inferInstanceAs (CMRA.Discrete MaxNat)
instance : CMRA.IsTotal MaxNat where
  total x := ⟨x, rfl⟩
instance : UCMRA MaxNat where
  unit := 0
  unit_valid := trivial
  unit_left_id {x} := by
    apply OFE.Equiv.of_eq
    apply LeibnizO.ext
    exact Nat.zero_max _
  pcore_unit := .symm .rfl

namespace MaxNat

theorem included (x y : MaxNat) : x ≼ y ↔ x.1 ≤ y.1 := by
  constructor
  · rintro ⟨z, hz⟩
    have hz' : y = x • z := OFE.Leibniz.eq_of_eqv hz
    calc
      x.1 ≤ max x.1 z.1 := Nat.le_max_left _ _
      _ = y.1 := by simpa [CMRA.op] using congrArg (fun t : MaxNat => t.1) hz'.symm
  · intro h
    refine ⟨y, ?_⟩
    apply OFE.Equiv.of_eq
    apply LeibnizO.ext
    exact (Nat.max_eq_right h).symm

theorem localUpdate (x y x' : MaxNat) :
    x.1 ≤ x'.1 → (x, y) ~l~> (x', x') := by
  intro h
  refine (local_update_unital_discrete x y x' x').mpr ?_
  intro z _ hz
  refine ⟨trivial, ?_⟩
  have hz' : x = y • z := OFE.Leibniz.eq_of_eqv hz
  have hzle : z.1 ≤ x'.1 := by
    calc
      z.1 ≤ max y.1 z.1 := Nat.le_max_right _ _
      _ = x.1 := by simpa [CMRA.op] using congrArg (fun t : MaxNat => t.1) hz'.symm
      _ ≤ x'.1 := h
  apply OFE.Equiv.of_eq
  apply LeibnizO.ext
  exact (Nat.max_eq_left hzle).symm

end MaxNat

/-- Integers under `max`, matching Coq's `max_ZR`. This is only a CMRA,
so the auth wrapper will live over `Option MaxInt`. -/
abbrev MaxInt := LeibnizO Int

instance : COFE MaxInt := inferInstanceAs (COFE (LeibnizO Int))
instance : OFE.Leibniz MaxInt := inferInstanceAs (OFE.Leibniz (LeibnizO Int))
instance : OFE.Discrete MaxInt := inferInstanceAs (OFE.Discrete (LeibnizO Int))
instance : Coe Int MaxInt := ⟨(⟨·⟩)⟩
instance : Add MaxInt := ⟨fun x y => ((max x.1 y.1 : Int) : MaxInt)⟩
instance : Zero MaxInt := ⟨((0 : Int) : MaxInt)⟩

instance : Std.Associative (α := MaxInt) Add.add where
  assoc x y z := by
    apply LeibnizO.ext
    exact Int.max_assoc x.1 y.1 z.1

instance : Std.Commutative (α := MaxInt) Add.add where
  comm x y := by
    apply LeibnizO.ext
    exact Int.max_comm x.1 y.1

instance : Std.IdempotentOp (α := MaxInt) Add.add where
  idempotent x := by
    apply LeibnizO.ext
    exact Int.max_self x.1

instance : CMRA MaxInt := inferInstanceAs (CMRA MaxInt)
instance : CMRA.Discrete MaxInt := inferInstanceAs (CMRA.Discrete MaxInt)
instance : CMRA.IsTotal MaxInt where
  total x := ⟨x, rfl⟩

namespace MaxInt

theorem included (x y : MaxInt) : x ≼ y ↔ x.1 ≤ y.1 := by
  constructor
  · rintro ⟨z, hz⟩
    have hz' : y = x • z := OFE.Leibniz.eq_of_eqv hz
    calc
      x.1 ≤ max x.1 z.1 := Int.le_max_left _ _
      _ = y.1 := by simpa [CMRA.op] using congrArg (fun t : MaxInt => t.1) hz'.symm
  · intro h
    refine ⟨y, ?_⟩
    apply OFE.Equiv.of_eq
    apply LeibnizO.ext
    exact (Int.max_eq_right h).symm

theorem localUpdate (x y x' : MaxInt) :
    x.1 ≤ x'.1 → (x, y) ~l~> (x', x') := by
  intro h
  refine (LocalUpdate.discrete x y x' x').mpr ?_
  intro mz _ hz
  cases mz with
  | none =>
      exact ⟨trivial, OFE.Equiv.rfl⟩
  | some z =>
      refine ⟨trivial, ?_⟩
      have hz' : x = y • z := OFE.Leibniz.eq_of_eqv hz
      have hzle : z.1 ≤ x'.1 := by
        calc
          z.1 ≤ max y.1 z.1 := Int.le_max_right _ _
          _ = x.1 := by simpa [CMRA.op] using congrArg (fun t : MaxInt => t.1) hz'.symm
          _ ≤ x'.1 := h
      apply OFE.Equiv.of_eq
      apply LeibnizO.ext
      exact (Int.max_eq_left hzle).symm

end MaxInt

end Iris
