/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.Algebra.View
public import Iris.Algebra.Numbers
public import Iris.Algebra.IsOp

@[expose] public section

/-! # RA for time receipts -/

namespace Iris

variable {SI : stepindex (Type _)} [instSI : SIdx SI]

open OFE ORA View
open _root_.Std (Associative Commutative LeftIdentity LawfulLeftIdentity)

namespace Algebra.TimeReceipt

/-- The additive counter: natural numbers with `+` as the resource operation. A `def` (not an
`abbrev`), so its algebra does not leak to `Nat`. -/
def Count := Nat

/-- The count `n` (cf. Mathlib's `Multiplicative.ofAdd`). -/
def Count.ofNat (n : Nat) : Count := n

/-- The underlying natural number. -/
def Count.toNat (c : Count) : Nat := c

instance : Add Count := inferInstanceAs (Add Nat)
instance : Zero Count := ⟨Count.ofNat 0⟩
instance : Associative (α := Count) (· + ·) := ⟨Nat.add_assoc⟩
instance : Commutative (α := Count) (· + ·) := ⟨Nat.add_comm⟩
instance : LeftIdentity (α := Count) (· + ·) Zero.zero := ⟨⟩
instance : LawfulLeftIdentity (α := Count) (· + ·) Zero.zero := ⟨Nat.zero_add⟩

instance : COFE SI Count := COFE.ofDiscrete _
instance : OFE.Discrete SI Count := ⟨fun h => h⟩
instance : Op Count := CommMonoidLike.instOp
instance : PCore Count := CommMonoidLike.instPCore
instance : RA Count := CommMonoidLike.instRA
instance : URA Count := CommMonoidLike.instURA
instance : UCMRA SI Count := CommMonoidLike.instUCMRA
instance : ORA.Discrete SI Count := CommMonoidLike.instDiscrete
instance : CoreId (Count.ofNat 0) := CommMonoidLike.instCoreIdZero
set_option synthInstance.checkSynthOrder false in
instance {x y : Count} : IsOp d (x + y) x y := CommMonoidLike.instIsOp

@[simp] theorem Count.toNat_ofNat (n : Nat) : (Count.ofNat n).toNat = n := rfl
@[simp] theorem Count.toNat_op (a b : Count) : (a • b).toNat = a.toNat + b.toNat := rfl
theorem Count.ofNat_add (n m : Nat) : Count.ofNat (n + m) = Count.ofNat n • Count.ofNat m := rfl

/-- The fragments: a lower bound on the additive and on the persistent partition. -/
@[rocq_alias time_receipt_view_fragUR]
abbrev frag := Count × MaxNat

/-- The view relation: the authoritative `a` can be split into an additive part `a₁` and a
persistent part `a₂ ≥ a₁`, which the two components of the fragment bound from below. -/
@[rocq_alias time_receipt_view_rel_raw]
def viewRel : ViewRel SI Count frag := fun _ a f =>
  ∃ a₁ a₂, a.toNat = a₁ + a₂ ∧ a₁ ≤ a₂ ∧ f.1.toNat ≤ a₁ ∧ f.2.toNat ≤ a₂

@[rocq_alias time_receipt_view_rel]
private instance : IsViewRel viewRel (SI := SI) := .ofMonoOrd
  (fun {n₁ : SI} {_} f₁ n₂ _ f₂ h ha hf hn => by
    obtain ⟨b₁, b₂, hb₀, hb, h₁, h₂⟩ := h
    obtain rfl := (ha : _ = _)
    obtain ⟨⟨z, hz : f₁.1.toNat = f₂.1.toNat + z.toNat⟩, hf₂⟩ := Prod.incN_def.mp (ordN_incN hf)
    have hle : f₂.2.toNat ≤ f₁.2.toNat := MaxNat.inc_iff.mp <| (inc_iff_incN n₂).mpr hf₂
    exact ⟨b₁, b₂, hb₀, hb, by omega, by omega⟩)
  (fun _ _ _ _ => ⟨trivial, trivial⟩)
  (fun _ => ⟨0, 0, 0, rfl, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)

#rocq_ignore time_receipt_view_rel_raw_mono "Defined in the IsViewRel instance"
#rocq_ignore time_receipt_view_rel_raw_valid "Defined in the IsViewRel instance"
#rocq_ignore time_receipt_view_rel_raw_unit "Defined in the IsViewRel instance"

@[rocq_alias time_receipt_view_rel_exists]
theorem viewRel_exists_iff {n : SI} : (∃ a, viewRel n a f) ↔ ✓{n} f :=
  ⟨fun _ => ⟨trivial, trivial⟩,
   fun _ => ⟨Count.ofNat (f.1.toNat + max f.1.toNat f.2.toNat), f.1.toNat, max f.1.toNat f.2.toNat,
     rfl, Nat.le_max_left .., Nat.le_refl _, Nat.le_max_right ..⟩⟩

@[rocq_alias time_receipt_view_rel_unit]
theorem viewRel_unit_iff {n : SI} : viewRel n a UnitOp.unit ↔ ✓{n} a :=
  ⟨fun _ => trivial,
   fun _ => ⟨0, a.toNat, (Nat.zero_add _).symm, Nat.zero_le _, Nat.le_refl _,
     Nat.zero_le _⟩⟩

@[rocq_alias time_receipt_view_rel_discrete]
instance : IsViewRelDiscrete viewRel (SI := SI) where
  discrete _ _ _ h := h

variable (SI) in
/-- Time receipts. A `def` (not an `abbrev`), so clients see only the instances below. -/
@[indexed, rocq_alias time_receipt]
def _root_.Iris.Algebra.TimeReceipt := View viewRel (SI := SI)

@[rocq_alias time_receiptO]
instance : OFE SI (TimeReceipt SI) := View.instOFE
instance : OFE.Discrete SI (TimeReceipt SI) := inferInstanceAs (OFE.Discrete SI (View viewRel))
instance : Op (TimeReceipt SI) := inferInstanceAs (Op (View viewRel))
instance : PCore (TimeReceipt SI) := inferInstanceAs (PCore (View viewRel))
instance : RA (TimeReceipt SI) := inferInstanceAs (RA (View viewRel))
instance : URA (TimeReceipt SI) := inferInstanceAs (URA (View viewRel))
@[rocq_alias time_receiptR]
instance : CMRA SI (TimeReceipt SI) := inferInstanceAs (CMRA SI (View viewRel))
@[rocq_alias time_receiptUR]
instance : UCMRA SI (TimeReceipt SI) := inferInstanceAs (UCMRA SI (View viewRel))
instance : ORA.Discrete SI (TimeReceipt SI) := inferInstanceAs (ORA.Discrete SI (View viewRel))

/-- A view as a time receipt (cf. Mathlib's `Multiplicative.ofAdd`). -/
def ofView (x : View viewRel (SI := SI)) : TimeReceipt SI := x

theorem ofView_op (x y : View viewRel (SI := SI)) : ofView (x • y) = ofView x • ofView y := rfl
theorem valid_ofView {x : View viewRel (SI := SI)} : ✓[SI] ofView x ↔ ✓[SI] x := .rfl
theorem update_ofView {x y : View viewRel (SI := SI)} : ofView x ~~>[SI] ofView y ↔ x ~~>[SI] y := .rfl

/-- The authoritative total amount of time receipts. -/
@[rocq_alias time_receipt_auth]
def auth (m : Nat) : TimeReceipt SI := ofView (●V Count.ofNat m)

variable (SI) in
/-- An exclusive lower bound on the additive partition. -/
@[indexed, rocq_alias time_receipt_frag_excl]
def fragExcl (n : Nat) : TimeReceipt SI := ofView (◯V (Count.ofNat n, MaxNat.ofNat 0))

variable (SI) in
/-- A persistent lower bound on the persistent partition. -/
@[indexed, rocq_alias time_receipt_frag_pers]
def fragPers (n : Nat) : TimeReceipt SI := ofView (◯V (Count.ofNat 0, MaxNat.ofNat n))

@[rocq_alias time_receipt_frag_pers_core_id]
instance {n : Nat} : CoreId (fragPers SI n) := inferInstanceAs (CoreId (◯V _ : View viewRel))

@[rocq_alias time_receipt_frag_excl_0_core_id]
instance : CoreId (fragExcl SI 0) := inferInstanceAs (CoreId (◯V _ : View viewRel))

@[rocq_alias time_receipt_frag_excl_op]
theorem fragExcl_op (n₁ n₂ : Nat) : fragExcl _ (n₁ + n₂) = fragExcl SI n₁ • fragExcl _ n₂ := rfl

@[rocq_alias time_receipt_frag_pers_op]
theorem fragPers_op (n₁ n₂ : Nat) : fragPers _ (max n₁ n₂) = fragPers SI n₁ • fragPers _ n₂ := rfl

@[rocq_alias time_receipt_frag_excl_is_op]
instance {n n₁ n₂ : Nat} [h : IsOp d (Count.ofNat n) (Count.ofNat n₁) (Count.ofNat n₂)] :
    IsOp d (fragExcl SI n) (fragExcl _ n₁) (fragExcl _ n₂) where
  is_op := congrArg (fragExcl _ ·.toNat) h.is_op

@[rocq_alias time_receipt_frag_pers_is_op]
instance {n n₁ n₂ : Nat} [h : IsOp d (MaxNat.ofNat n) (MaxNat.ofNat n₁) (MaxNat.ofNat n₂)] :
    IsOp d (fragPers SI n) (fragPers _ n₁) (fragPers _ n₂) where
  is_op := congrArg (fragPers _ ·.toNat) h.is_op

@[rocq_alias time_receipt_frag_excl_valid]
theorem auth_op_fragExcl_valid_iff (m n : Nat) : ✓[SI] (auth (SI := SI) m • fragExcl _ n) ↔ n + n ≤ m := by
  rw [auth, fragExcl, ← ofView_op, valid_ofView, auth_one_op_frag_valid_iff]
  refine ⟨fun h => ?_, fun h _ => ⟨n, m - n, by simp; omega, by omega, Nat.le_refl _, Nat.zero_le _⟩⟩
  obtain ⟨_, _, h₀, _, h₁, h₂⟩ := h 0
  simp only [Count.toNat_ofNat] at h₀ h₁ h₂
  omega

@[rocq_alias time_receipt_frag_pers_valid]
theorem auth_op_fragPers_valid_iff (m n : Nat) : ✓[SI] (auth (SI := SI) m • fragPers _ n) ↔ n ≤ m := by
  rw [auth, fragPers, ← ofView_op, valid_ofView, auth_one_op_frag_valid_iff]
  refine ⟨fun h => ?_, fun h _ => ⟨0, m, (Nat.zero_add m).symm, Nat.zero_le _, Nat.le_refl _, h⟩⟩
  obtain ⟨_, _, h₀, _, h₁, h₂⟩ := h 0
  simp only [Count.toNat_ofNat] at h₀ h₁ h₂
  omega

@[rocq_alias time_receipt_view_frag_both_valid]
theorem le_of_auth_op_frag_valid {m n₁ n₂ : Nat}
    (h : ✓[SI] (auth (SI := SI) m • (fragExcl _ n₁ • fragPers _ n₂))) : n₁ + n₂ ≤ m := by
  rw [auth, fragExcl, fragPers, ← ofView_op, ← ofView_op, valid_ofView, ← frag_op_eq,
    auth_one_op_frag_valid_iff] at h
  obtain ⟨_, _, h₀, _, h₁, h₂⟩ := h 0
  simp only [Prod.mk_op_mk, Count.toNat_op, Count.toNat_ofNat, MaxNat.toNat_op]
    at h₀ h₁ h₂
  omega

@[rocq_alias time_receipt_frag_excl_persist]
theorem fragExcl_persist (n₁ n₂ : Nat) : fragExcl SI n₁ • fragPers _ n₂ ~~>[SI] fragPers _ (n₁ + n₂) := by
  rw [fragExcl, fragPers, fragPers, ← ofView_op, update_ofView, ← frag_op_eq]
  refine frag_update fun _ _ ⟨_, _⟩ ⟨a, b, h⟩ => ⟨a - n₁, b + n₁, ?_⟩
  simp only [Prod.mk_op_mk, Count.toNat_op, Count.toNat_ofNat, MaxNat.toNat_op]
    at h ⊢
  omega

@[rocq_alias time_receipt_frag_excl_get_pers]
theorem fragExcl_get_pers (n : Nat) : fragExcl SI n ~~>[SI] fragExcl _ n • fragPers _ n := by
  rw [fragExcl, fragPers, ← ofView_op, update_ofView, ← frag_op_eq]
  refine frag_update fun _ _ ⟨_, _⟩ ⟨a, b, h⟩ => ⟨a, b, ?_⟩
  simp only [Prod.mk_op_mk, Count.toNat_op, Count.toNat_ofNat, MaxNat.toNat_op]
    at h ⊢
  omega

@[rocq_alias time_receipt_auth_incr]
theorem auth_incr (m n k : Nat) :
    auth (SI := SI) m • fragPers _ n ~~>[SI] (auth (m + k + k) • fragPers _ (n + k)) • fragExcl _ k := by
  rw [← assoc_L, auth, auth, fragPers, fragPers, fragExcl, ← ofView_op, ← ofView_op, ← ofView_op,
    update_ofView, ← frag_op_eq]
  refine auth_one_op_frag_update fun _ ⟨_, _⟩ ⟨a, b, h⟩ => ⟨a + k, b + k, ?_⟩
  simp only [Prod.mk_op_mk, Count.toNat_op, Count.toNat_ofNat, MaxNat.toNat_op]
    at h ⊢
  omega

end Algebra.TimeReceipt

end Iris
