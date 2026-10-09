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

variable {SI : Type _} [instSI : SIdx SI]

open OFE ORA View

namespace Algebra.TimeReceipt

scoped instance : COFE SI Nat := COFE.ofDiscrete _
scoped instance : OFE.Discrete SI Nat := ⟨fun h => h⟩
scoped instance : URA Nat := CommMonoidLike.instURA
scoped instance : UCMRA SI Nat := CommMonoidLike.instUCMRA
scoped instance : ORA.Discrete SI Nat := CommMonoidLike.instDiscrete
scoped instance : CoreId (0 : Nat) := CommMonoidLike.instCoreIdZero

/-- The fragments: a lower bound on the additive and on the persistent partition. -/
@[rocq_alias time_receipt_view_fragUR]
abbrev frag := Nat × MaxNat

/-- The view relation: the authoritative `a` can be split into an additive part `a₁` and a
persistent part `a₂ ≥ a₁`, which the two components of the fragment bound from below. -/
@[rocq_alias time_receipt_view_rel_raw]
def viewRel : ViewRel SI Nat frag := fun _ a f =>
  ∃ a₁ a₂, a = a₁ + a₂ ∧ a₁ ≤ a₂ ∧ f.1 ≤ a₁ ∧ f.2.toNat ≤ a₂

@[rocq_alias time_receipt_view_rel]
private instance : IsViewRel viewRel (SI := SI) := .ofMonoOrd
  (fun {n₁ : SI} {_} f₁ n₂ _ f₂ h ha hf hn => by
    obtain ⟨b₁, b₂, rfl, hb, h₁, h₂⟩ := h
    obtain rfl := (ha : _ = _)
    obtain ⟨⟨z, hz : f₁.1 = f₂.1 + z⟩, hf₂⟩ := Prod.incN_def.mp (ordN_incN hf)
    have hle : f₂.2.toNat ≤ f₁.2.toNat := MaxNat.inc_iff.mp <| (inc_iff_incN n₂).mpr hf₂
    exact ⟨b₁, b₂, rfl, hb, by omega, by omega⟩)
  (fun _ _ _ _ => ⟨trivial, trivial⟩)
  (fun _ => ⟨0, 0, 0, rfl, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)

#rocq_ignore time_receipt_view_rel_raw_mono "Defined in the IsViewRel instance"
#rocq_ignore time_receipt_view_rel_raw_valid "Defined in the IsViewRel instance"
#rocq_ignore time_receipt_view_rel_raw_unit "Defined in the IsViewRel instance"

@[rocq_alias time_receipt_view_rel_exists]
theorem viewRel_exists_iff {n : SI} : (∃ a, viewRel n a f) ↔ ✓{n} f :=
  ⟨fun _ => ⟨trivial, trivial⟩,
   fun _ => ⟨_, f.1, max f.1 f.2.toNat, rfl, Nat.le_max_left .., Nat.le_refl _,
     Nat.le_max_right ..⟩⟩

@[rocq_alias time_receipt_view_rel_unit]
theorem viewRel_unit_iff {n : SI} : viewRel n a UnitOp.unit ↔ ✓{n} a :=
  ⟨fun _ => trivial,
   fun _ => ⟨0, a, (Nat.zero_add a).symm, Nat.zero_le _, Nat.le_refl _,
     Nat.zero_le _⟩⟩

@[rocq_alias time_receipt_view_rel_discrete]
instance : IsViewRelDiscrete viewRel (SI := SI) where
  discrete _ _ _ h := h

variable (SI) in
@[rocq_alias time_receipt]
abbrev _root_.Iris.Algebra.TimeReceipt := View viewRel (SI := SI)

/- The `Nat` camera instances are scoped, so these are needed outside `namespace TimeReceipt`. -/
@[rocq_alias time_receiptO]
instance : OFE SI (TimeReceipt SI) := View.instOFE
instance : RA (TimeReceipt SI) := inferInstance
instance : URA (TimeReceipt SI) := inferInstance
@[rocq_alias time_receiptR]
instance : CMRA SI (TimeReceipt SI) := inferInstance
@[rocq_alias time_receiptUR]
instance : UCMRA SI (TimeReceipt SI) := inferInstance

/-- The authoritative total amount of time receipts. -/
@[rocq_alias time_receipt_auth]
def auth (m : Nat) : TimeReceipt SI := ●V m

variable (SI) in
/-- An exclusive lower bound on the additive partition. -/
@[rocq_alias time_receipt_frag_excl]
def fragExcl (n : Nat) : TimeReceipt SI := ◯V (n, MaxNat.ofNat 0)

variable (SI) in
/-- A persistent lower bound on the persistent partition. -/
@[rocq_alias time_receipt_frag_pers]
def fragPers (n : Nat) : TimeReceipt SI := ◯V (0, MaxNat.ofNat n)

@[rocq_alias time_receipt_frag_pers_core_id]
instance {n : Nat} : CoreId (fragPers SI n) := inferInstanceAs (CoreId (◯V _))

@[rocq_alias time_receipt_frag_excl_0_core_id]
instance : CoreId (fragExcl SI 0) := inferInstanceAs (CoreId (◯V _))

@[rocq_alias time_receipt_frag_excl_op]
theorem fragExcl_op (n₁ n₂ : Nat) : fragExcl _ (n₁ + n₂) = fragExcl SI n₁ • fragExcl _ n₂ := rfl

@[rocq_alias time_receipt_frag_pers_op]
theorem fragPers_op (n₁ n₂ : Nat) : fragPers _ (max n₁ n₂) = fragPers SI n₁ • fragPers _ n₂ := rfl

@[rocq_alias time_receipt_frag_excl_is_op]
instance {n n₁ n₂ : Nat} [h : IsOp d n n₁ n₂] :
    IsOp d (fragExcl SI n) (fragExcl _ n₁) (fragExcl _ n₂) where
  is_op := congrArg (fragExcl _) h.is_op

@[rocq_alias time_receipt_frag_pers_is_op]
instance {n n₁ n₂ : Nat} [h : IsOp d (MaxNat.ofNat n) (MaxNat.ofNat n₁) (MaxNat.ofNat n₂)] :
    IsOp d (fragPers SI n) (fragPers _ n₁) (fragPers _ n₂) where
  is_op := congrArg (fragPers _ ·.toNat) h.is_op

@[rocq_alias time_receipt_frag_excl_valid]
theorem auth_op_fragExcl_valid_iff (m n : Nat) : ✓[SI] (auth (SI := SI) m • fragExcl _ n) ↔ n + n ≤ m := by
  rw [auth, fragExcl, auth_one_op_frag_valid_iff]
  refine ⟨fun h => ?_, fun h _ => ⟨n, m - n, by omega, by omega, Nat.le_refl _, Nat.zero_le _⟩⟩
  obtain ⟨_, _, rfl, _, h₁, h₂⟩ := h 0
  dsimp only at h₁ h₂
  omega

@[rocq_alias time_receipt_frag_pers_valid]
theorem auth_op_fragPers_valid_iff (m n : Nat) : ✓[SI] (auth (SI := SI) m • fragPers _ n) ↔ n ≤ m := by
  rw [auth, fragPers, auth_one_op_frag_valid_iff]
  refine ⟨fun h => ?_, fun h _ => ⟨0, m, (Nat.zero_add m).symm, Nat.zero_le _, Nat.le_refl _, h⟩⟩
  obtain ⟨_, _, rfl, _, h₁, h₂⟩ := h 0
  dsimp only at h₁ h₂
  omega

@[rocq_alias time_receipt_view_frag_both_valid]
theorem le_of_auth_op_frag_valid {m n₁ n₂ : Nat}
    (h : ✓[SI] (auth (SI := SI) m • (fragExcl _ n₁ • fragPers _ n₂))) : n₁ + n₂ ≤ m := by
  rw [auth, fragExcl, fragPers, ← frag_op_eq, auth_one_op_frag_valid_iff] at h
  obtain ⟨_, _, rfl, _, h₁, h₂⟩ := h 0
  simp only [Prod.mk_op_mk, CommMonoidLike.op_eq, MaxNat.toNat_add, Nat.max_eq_max] at h₁ h₂
  omega

@[rocq_alias time_receipt_frag_excl_persist]
theorem fragExcl_persist (n₁ n₂ : Nat) : fragExcl SI n₁ • fragPers _ n₂ ~~>[SI] fragPers _ (n₁ + n₂) := by
  rw [fragExcl, fragPers, ← frag_op_eq]
  refine frag_update fun _ _ ⟨_, _⟩ ⟨a, b, h⟩ => ⟨a - n₁, b + n₁, ?_⟩
  simp only [Prod.mk_op_mk, CommMonoidLike.op_eq, MaxNat.toNat_add, Nat.max_eq_max] at h ⊢
  omega

@[rocq_alias time_receipt_frag_excl_get_pers]
theorem fragExcl_get_pers (n : Nat) : fragExcl SI n ~~>[SI] fragExcl _ n • fragPers _ n := by
  rw [fragExcl, fragPers, ← frag_op_eq]
  refine frag_update fun _ _ ⟨_, _⟩ ⟨a, b, h⟩ => ⟨a, b, ?_⟩
  simp only [Prod.mk_op_mk, CommMonoidLike.op_eq, MaxNat.toNat_add, Nat.max_eq_max] at h ⊢
  omega

@[rocq_alias time_receipt_auth_incr]
theorem auth_incr (m n k : Nat) :
    auth (SI := SI) m • fragPers _ n ~~>[SI] (auth (m + k + k) • fragPers _ (n + k)) • fragExcl _ k := by
  rw [← assoc_L, auth, auth, fragPers, fragPers, fragExcl, ← frag_op_eq]
  refine auth_one_op_frag_update fun _ ⟨_, _⟩ ⟨a, b, h⟩ => ⟨a + k, b + k, ?_⟩
  simp only [Prod.mk_op_mk, CommMonoidLike.op_eq, MaxNat.toNat_add, Nat.max_eq_max] at h ⊢
  omega

end Algebra.TimeReceipt

end Iris
