/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Iris

/-! ## Commutative Monoid CMRAs

`(ℝ, +)` and `(ℝ≥0∞, +)` are commutative monoids, hence "constant core" CMRAs in the sense of
`CommMonoidLike`: every element is valid, the core of every element is `0`, and the unit is `0`.

-/

@[expose] public section

local stepindex Nat

/-- Relationship between Mathlib's AddZeroClass to the Stdlib Std.LawfulLeftIdentity on Add. -/
instance AddZeroClass.to_isLawfulLeftIdentity {M : Type _} [AddZeroClass M] :
    Std.LawfulLeftIdentity (α := M) (· + ·) (Zero.zero : M) where
  left_id := zero_add

/-! ### (ℝ, +) -/

namespace Real

open Iris
open scoped CommMonoidLike

/-- The discrete OFE on `ℝ`. -/
scoped instance : COFE ℝ := COFE.ofDiscrete ℝ
scoped instance : OFE.Discrete ℝ := ⟨fun h => h⟩

scoped instance realOp : Op ℝ := CommMonoidLike.instOp
scoped instance realPCore : PCore ℝ := CommMonoidLike.instPCore
scoped instance realRA : RA ℝ := CommMonoidLike.instRA
scoped instance realURA : URA ℝ := CommMonoidLike.instURA
scoped instance realUCMRA : UCMRA ℝ := CommMonoidLike.instUCMRA
scoped instance realDiscrete : ORA.Discrete ℝ := CommMonoidLike.instDiscrete
scoped instance : LeftCancelAdd ℝ := ⟨add_left_cancel⟩
scoped instance realCancelable {x : ℝ} : ORA.Cancelable x := CommMonoidLike.instCancelable
scoped instance realCoreIdZero : ORA.CoreId (0 : ℝ) := CommMonoidLike.instCoreIdZero

theorem op_eq {x y : ℝ} : Op.op x y = x + y := rfl

theorem inc (x y : ℝ) : x ≼ y := CommMonoidLike.included_iff.mpr ⟨y - x, by ring⟩

theorem local_update {x y x' y' : ℝ} (h : x + y' = x' + y) : (x, y) ~l~> (x', y') :=
  CommMonoidLike.leftCancelAdd_local_update h

end Real

/-! ### (ℝ≥0∞, +) -/

namespace ENNReal

open Iris
open scoped CommMonoidLike

/-- The discrete OFE on `ℝ≥0∞`. -/
scoped instance : COFE ℝ≥0∞ := COFE.ofDiscrete ℝ≥0∞
scoped instance : OFE.Discrete ℝ≥0∞ := ⟨fun h => h⟩

scoped instance ennrealOp : Op ℝ≥0∞ := CommMonoidLike.instOp
scoped instance ennrealPCore : PCore ℝ≥0∞ := CommMonoidLike.instPCore
scoped instance ennrealRA : RA ℝ≥0∞ := CommMonoidLike.instRA
scoped instance ennrealURA : URA ℝ≥0∞ := CommMonoidLike.instURA
scoped instance ennrealUCMRA : UCMRA ℝ≥0∞ := CommMonoidLike.instUCMRA
scoped instance ennrealDiscrete : ORA.Discrete ℝ≥0∞ := CommMonoidLike.instDiscrete
scoped instance ennrealCoreIdZero : ORA.CoreId (0 : ℝ≥0∞) := CommMonoidLike.instCoreIdZero
scoped instance : LawfulAddLE ℝ≥0∞ := ⟨le_iff_exists_add⟩

theorem op_eq {x y : ℝ≥0∞} : Op.op x y = x + y := rfl

theorem inc_iff {x y : ℝ≥0∞} : x ≼ y ↔ x ≤ y := CommMonoidLike.inc_iff_le

end ENNReal
