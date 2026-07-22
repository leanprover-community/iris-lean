/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Shreyas Srinivas, Mario Carneiro
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.OFE
public import Iris.Algebra.IsOp
meta import Iris.Std.RocqPorting

/-!
# The Frac CMRA

This CMRA captures the notion of fractional ownership of another resource.
This version follows Iris Rocq in fixing the underlying type of fractions to be `ℚ ∩ (0, 1]`
-/

@[expose] public section

namespace Rat

/-- ## Helper lemmas for Rat -/

theorem div_pos {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [Rat.div_def]; exact Rat.mul_pos ha (Rat.inv_pos.mpr hb)

theorem mul_div_cancel_left {a b : Rat} (ha : a ≠ 0) : a * (b / a) = b := by
  rw [Rat.mul_comm, Rat.div_mul_cancel ha]

end Rat

namespace Iris

/-- The type of positive rational numbers, used as fractions -/
@[rocq_alias fracO, rocq_alias fracR]
abbrev Qp := { q : Rat // 0 < q }

-- TODO: Should we move the positivity condition into the validity predicate? My initial guess is not,
-- but we should avoid duplicating the Rat terms (add, half, etc) somehow.

instance instQpOne : One Qp where
  one := ⟨1, Rat.neg_lt_neg_iff.mp rfl⟩

abbrev Qp.add (x y : Qp) : Qp := ⟨x.val + y.val, by grind⟩

instance instHaddQpQpQp : HAdd Qp Qp Qp where
  hAdd := Qp.add

def Qp.half (q : Qp) : Qp where
  val := q.val / 2
  property := by
    let ⟨v, P⟩ := q
    grind

def Qp.div (x y : Qp) : Qp := ⟨x.val / y.val, Rat.div_pos x.2 y.2⟩

instance instHDivQpQpQp : HDiv Qp Qp Qp where
  hDiv := Qp.div

def Qp.divide_even (q : Qp) (n : Nat) (hn : 0 < n) : Qp :=
  ⟨q.val / n, Rat.div_pos q.2 (by exact_mod_cast hn)⟩

instance instCOFEQp : COFE Qp := COFE.ofDiscrete _

instance instCMRAQp : CMRA Qp where
  pcore _ := none
  op x y := x + y
  ValidN _ x := x.val ≤ 1
  Valid x := x.val ≤ 1
  op_ne.ne n x1 x2 H := by rw [(H : x1 = x2)]
  pcore_ne _ H := by rcases H
  validN_ne H := by rw [(H : _ = _)]; exact id
  valid_iff_validN := .symm (forall_const _)
  validN_succ := id
  validN_op_left {n x y} h := by
    show x.val ≤ 1
    have h' : x.val + y.val ≤ 1 := h
    grind
  assoc := Subtype.ext (Rat.add_assoc ..).symm
  comm := Subtype.ext (Rat.add_comm ..)
  pcore_op_left H := by rcases H
  pcore_idem H := by rcases H
  pcore_op_mono H := by rcases H
  extend {_ x y z} := by
    rintro H He; exact ⟨y, z, He, .rfl, .rfl⟩


-- TODO: A different solution to having these bridge lemmas might be to internalize
-- positivity into the CMRA's validity predicate, removing the sybtype, and having Qp
-- become just a Leibniz CMRA over Rat. This admits two-way coercions to Rat for the automation.

@[simp, grind =] theorem Qp.val_add (x y : Qp) : (x + y).val = x.val + y.val := rfl
@[simp, grind =] theorem Qp.val_one : (1 : Qp).val = 1 := rfl
@[simp, grind =] theorem Qp.val_half (q : Qp) : q.half.val = q.val / 2 := rfl
@[simp, grind =] theorem Qp.val_div (x y : Qp) : (x / y).val = x.val / y.val := rfl
@[simp, grind =] theorem Qp.val_divide_even (q : Qp) (n : Nat) (hn : 0 < n) :
    (q.divide_even n hn).val = q.val / n := rfl
@[simp, grind =] theorem Qp.val_op (x y : Qp) : (x • y).val = x.val + y.val := rfl
@[simp, grind =] theorem Qp.validN_iff {n} {x : Qp} : ✓{n} x ↔ x.val ≤ 1 := Iff.rfl
@[simp, grind =] theorem Qp.valid_iff {x : Qp} : ✓ x ↔ x.val ≤ 1 := Iff.rfl
@[simp, grind =] theorem Qp.le_iff {x y : Qp} : x ≤ y ↔ x.val ≤ y.val := Iff.rfl
@[simp, grind =] theorem Qp.lt_iff {x y : Qp} : x < y ↔ x.val < y.val := Iff.rfl
@[simp] theorem Qp.ext_iff {x y : Qp} : x = y ↔ x.val = y.val := Subtype.ext_iff
@[simp] theorem Qp.dist_iff {n} {x y : Qp} : x ≡{n}≡ y ↔ x.val = y.val := Subtype.ext_iff
@[simp, rocq_alias frac_valid_1] theorem Qp.valid_one : ✓ (1 : Qp) := by grind
@[simp, grind =] theorem Qp.half_add_half (q : Qp) : q.half + q.half = q := Subtype.ext (by grind)

theorem Qp.lt_iff_exists_add {a b : Qp} : a < b ↔ ∃ c : Qp, a + c = b := by
  refine ⟨fun h => ⟨⟨b.val - a.val, by have := Qp.lt_iff.mp h; grind⟩, Subtype.ext (by grind)⟩, ?_⟩
  rintro ⟨c, rfl⟩; have := c.2; grind

#rocq_ignore frac_op_instance "Use CMRA instance"
#rocq_ignore frac_pcore_instance "Use CMRA instance"
#rocq_ignore frac_valid_instance "Use CMRA instance"
#rocq_ignore frac_ra_mixin "Use CMRA instance"

@[rocq_alias frac_included]
theorem Frac.inc_iff {p q : Qp} : p ≼ q ↔ p < q := by
  refine ⟨fun ⟨r, Hr⟩ => ?_, fun H => ?_⟩
  · have := r.2; simp only [Qp.lt_iff, Qp.ext_iff, Qp.val_op] at *; grind
  · exact ⟨⟨q.val - p.val, by grind⟩, by simp only [Qp.ext_iff, Qp.val_op]; grind⟩

@[rocq_alias frac_included_weak]
theorem Frac.le_of_inc {p q : Qp} (H : p ≼ q) : p ≤ q := by
  have := inc_iff.mp H; grind

@[rocq_alias frac_cmra_discrete]
instance instDiscreteQp : CMRA.Discrete Qp where
  discrete_0 := fun h => h
  discrete_valid := id

@[rocq_alias frac_full_exclusive]
instance instExclusiveQp1 : CMRA.Exclusive (α := Qp) 1 where
  exclusive0_l x := by have := x.2; grind

@[rocq_alias frac_cancelable]
instance instCancelableQp {a : Qp} : CMRA.Cancelable (α := Qp) a where
  cancelableN {n x y} _ (H : a • x = a • y) := by
    simp only [Qp.dist_iff, Qp.ext_iff, Qp.val_op] at *; grind

@[rocq_alias frac_id_free]
instance instIdFreeQp {a : Qp} : CMRA.IdFree a where
  id_free0_r b _ H := by
    have := b.2; simp only [Qp.dist_iff, Qp.val_op] at H; grind

@[rocq_alias frac_op]
theorem Frac.op_eq (p q : Qp) : p • q = p + q := rfl

@[rocq_alias frac_valid]
theorem Frac.valid_iff {p : Qp} : ✓ p ↔ p.val ≤ 1 := .rfl

set_option synthInstance.checkSynthOrder false in
@[rocq_alias frac_is_op]
instance (priority := default - 10) (q1 q2 : Qp) :
    IsOpMerge (q1 + q2 : Qp) q1 q2 where
  is_op := rfl

set_option synthInstance.checkSynthOrder false in
@[rocq_alias is_op_frac]
instance (q : Qp) : IsOp io1 q io2 q.half io3 q.half where
  is_op := by refine q.ext ?_; grind
