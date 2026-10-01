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

/-!
# RA for time receipts

The authoritative element is a single natural number representing the total amount of time
receipts. It is split into an additive and a persistent partition, where the persistent
partition is at least as large as the additive one. The exact partitioning is not fixed by the
authoritative element.

There are two kinds of fragments: an exclusive (additive) lower bound `fragExcl` on the additive
partition and a persistent lower bound `fragPers` on the persistent partition.

The key properties of this resource algebra are:
1. Without the authoritative element, persistent fragments can be derived from additive ones in a
   snapshot operation (`fragExcl_get_pers`).
2. Without the authoritative element, additive fragments can be used to shrink the additive and
   expand the persistent partition (`fragExcl_persist`).
3. Increasing the authoritative element expands both partitions by the same amount, generating
   new additive fragments and incrementing any persistent fragment (`auth_incr`).

This RA is used to implement time receipts, which are permissions to eliminate laters around
(program) steps.
-/

namespace Iris

open OFE CMRA View

namespace TimeReceipt

scoped instance : COFE Nat := COFE.ofDiscrete _
scoped instance : OFE.Discrete Nat := ⟨fun h => h⟩
scoped instance : UCMRA Nat := CommMonoidLike.instUCMRA
scoped instance : CMRA.Discrete Nat := CommMonoidLike.instDiscrete
scoped instance : CoreId (0 : Nat) := CommMonoidLike.instCoreIdZero

/-- The fragments: a lower bound on the additive and on the persistent partition. -/
@[rocq_alias time_receipt_view_fragUR]
abbrev Frag := Nat × MaxNat

/-- The view relation: the authoritative `a` can be split into an additive part `a₁` and a
persistent part `a₂ ≥ a₁`, which the two components of the fragment bound from below. -/
@[rocq_alias time_receipt_view_rel_raw]
def viewRel : ViewRel Nat Frag := fun _ a f =>
  ∃ a₁ a₂, a = a₁ + a₂ ∧ a₁ ≤ a₂ ∧ f.1 ≤ a₁ ∧ f.2.toNat ≤ a₂

section ViewRel

variable {n n₁ n₂ a a₁ a₂ : Nat} {f f₁ f₂ : Frag}

@[rocq_alias time_receipt_view_rel_raw_mono]
theorem viewRel_mono (h : viewRel n₁ a₁ f₁)
    (ha : a₁ ≡{n₂}≡ a₂) (hf : f₂ ≼{n₂} f₁) (_hn : n₂ ≤ n₁) : viewRel n₂ a₂ f₂ := by
  obtain ⟨b₁, b₂, rfl, hb, h₁, h₂⟩ := h
  obtain rfl := (ha : _ = _)
  obtain ⟨⟨z, hz : f₁.1 = f₂.1 + z⟩, hf₂⟩ := Prod.incN_def.mp hf
  have hinc : f₂.2 ≼ f₁.2 := (inc_iff_incN n₂).mpr hf₂
  have hle : f₂.2.toNat ≤ f₁.2.toNat := MaxNat.inc_iff.mp hinc
  exact ⟨b₁, b₂, rfl, hb, by omega, by omega⟩

@[rocq_alias time_receipt_view_rel, rocq_alias time_receipt_view_rel_raw_valid,
  rocq_alias time_receipt_view_rel_raw_unit]
instance : IsViewRel viewRel where
  mono := viewRel_mono
  rel_validN _ _ _ _ := ⟨trivial, trivial⟩
  rel_unit _ := ⟨0, 0, 0, rfl, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

@[rocq_alias time_receipt_view_rel_exists]
theorem viewRel_exists_iff : (∃ a, viewRel n a f) ↔ ✓{n} f :=
  ⟨fun _ => ⟨trivial, trivial⟩,
   fun _ => ⟨_, f.1, max f.1 f.2.toNat, rfl, Nat.le_max_left .., Nat.le_refl _,
     Nat.le_max_right ..⟩⟩

@[rocq_alias time_receipt_view_rel_unit]
theorem viewRel_unit_iff : viewRel n a UCMRA.unit ↔ ✓{n} a :=
  ⟨fun _ => trivial,
   fun _ => ⟨0, a, (Nat.zero_add a).symm, Nat.zero_le _, Nat.le_refl _,
     Nat.zero_le _⟩⟩

end ViewRel

@[rocq_alias time_receipt_view_rel_discrete]
instance : IsViewRelDiscrete viewRel where
  discrete _ _ _ h := h

/-- The RA of time receipts. -/
@[rocq_alias time_receipt]
abbrev _root_.Iris.TimeReceipt := View viewRel

/- The `Nat` camera instances are scoped, so these are needed outside `namespace TimeReceipt`. -/
@[rocq_alias time_receiptO]
instance : OFE TimeReceipt := View.instOFE
@[rocq_alias time_receiptR]
instance : CMRA TimeReceipt := View.instCMRA
@[rocq_alias time_receiptUR]
instance : UCMRA TimeReceipt := View.instUCMRA

/-- The authoritative total amount of time receipts. -/
@[rocq_alias time_receipt_auth]
def auth (m : Nat) : TimeReceipt := ●V m

/-- An exclusive lower bound on the additive partition. -/
@[rocq_alias time_receipt_frag_excl]
def fragExcl (n : Nat) : TimeReceipt := ◯V ((n, MaxNat.ofNat 0) : Frag)

/-- A persistent lower bound on the persistent partition. -/
@[rocq_alias time_receipt_frag_pers]
def fragPers (n : Nat) : TimeReceipt := ◯V ((0, MaxNat.ofNat n) : Frag)

@[rocq_alias time_receipt_frag_pers_core_id]
instance {n : Nat} : CoreId (fragPers n) := inferInstanceAs (CoreId (◯V _))

@[rocq_alias time_receipt_frag_excl_0_core_id]
instance : CoreId (fragExcl 0) := inferInstanceAs (CoreId (◯V _))

@[rocq_alias time_receipt_frag_excl_op]
theorem fragExcl_op (n₁ n₂ : Nat) : fragExcl (n₁ + n₂) = fragExcl n₁ • fragExcl n₂ := rfl

@[rocq_alias time_receipt_frag_pers_op]
theorem fragPers_op (n₁ n₂ : Nat) : fragPers (max n₁ n₂) = fragPers n₁ • fragPers n₂ := rfl

set_option synthInstance.checkSynthOrder false in
@[rocq_alias time_receipt_frag_excl_is_op]
instance {n n₁ n₂ : Nat} [h : IsOp d n n₁ n₂] :
    IsOp d (fragExcl n) (fragExcl n₁) (fragExcl n₂) where
  is_op := congrArg fragExcl h.is_op

set_option synthInstance.checkSynthOrder false in
@[rocq_alias time_receipt_frag_pers_is_op]
instance {n n₁ n₂ : Nat} [h : IsOp d (MaxNat.ofNat n) (MaxNat.ofNat n₁) (MaxNat.ofNat n₂)] :
    IsOp d (fragPers n) (fragPers n₁) (fragPers n₂) where
  is_op := congrArg (fragPers ·.toNat) h.is_op

@[rocq_alias time_receipt_frag_excl_valid]
theorem auth_op_fragExcl_valid_iff (m n : Nat) : ✓ (auth m • fragExcl n) ↔ n + n ≤ m := by
  rw [auth, fragExcl, auth_one_op_frag_valid_iff]
  refine ⟨fun h => ?_, fun h _ => ?_⟩
  · obtain ⟨_, _, rfl, _, h₁, h₂⟩ := h 0
    dsimp only at h₁ h₂
    omega
  · exact ⟨n, m - n, by omega, by omega, Nat.le_refl _, Nat.zero_le _⟩

@[rocq_alias time_receipt_frag_pers_valid]
theorem auth_op_fragPers_valid_iff (m n : Nat) : ✓ (auth m • fragPers n) ↔ n ≤ m := by
  rw [auth, fragPers, auth_one_op_frag_valid_iff]
  refine ⟨fun h => ?_, fun h _ => ?_⟩
  · obtain ⟨_, _, rfl, _, h₁, h₂⟩ := h 0
    dsimp only at h₁ h₂
    omega
  · exact ⟨0, m, (Nat.zero_add m).symm, Nat.zero_le _, Nat.le_refl _, h⟩

@[rocq_alias time_receipt_view_frag_both_valid]
theorem le_of_auth_op_frag_valid {m n₁ n₂ : Nat}
    (h : ✓ (auth m • (fragExcl n₁ • fragPers n₂))) : n₁ + n₂ ≤ m := by
  rw [auth, fragExcl, fragPers, ← frag_op_eq, auth_one_op_frag_valid_iff] at h
  obtain ⟨_, _, rfl, _, h₁, h₂⟩ := h 0
  simp only [Prod.mk_op_mk, CommMonoidLike.op_eq, MaxNat.toNat_op] at h₁ h₂
  omega

@[rocq_alias time_receipt_frag_excl_persist]
theorem fragExcl_persist (n₁ n₂ : Nat) : fragExcl n₁ • fragPers n₂ ~~> fragPers (n₁ + n₂) := by
  rw [fragExcl, fragPers, ← frag_op_eq]
  refine frag_update fun _ _ ⟨_, _⟩ ⟨a, b, h⟩ => ⟨a - n₁, b + n₁, ?_⟩
  simp only [Prod.mk_op_mk, CommMonoidLike.op_eq, MaxNat.toNat_op] at h ⊢
  omega

@[rocq_alias time_receipt_frag_excl_get_pers]
theorem fragExcl_get_pers (n : Nat) : fragExcl n ~~> fragExcl n • fragPers n := by
  rw [fragExcl, fragPers, ← frag_op_eq]
  refine frag_update fun _ _ ⟨_, _⟩ ⟨a, b, h⟩ => ⟨a, b, ?_⟩
  simp only [Prod.mk_op_mk, CommMonoidLike.op_eq, MaxNat.toNat_op] at h ⊢
  omega

/-- Increments the authoritative element by incrementing both the additive and the persistent
partition by `k`, so that the persistent partition remains at least as large as the additive one.
A persistent fragment is taken as witness to be increased; no additive fragment is needed, since
the resulting additive fragment can be combined with any existing one. -/
@[rocq_alias time_receipt_auth_incr]
theorem auth_incr (m n k : Nat) :
    auth m • fragPers n ~~> (auth (m + k + k) • fragPers (n + k)) • fragExcl k := by
  rw [← assoc_L, auth, auth, fragPers, fragPers, fragExcl, ← frag_op_eq]
  refine auth_one_op_frag_update fun _ ⟨_, _⟩ ⟨a, b, h⟩ => ⟨a + k, b + k, ?_⟩
  simp only [Prod.mk_op_mk, CommMonoidLike.op_eq, MaxNat.toNat_op] at h ⊢
  omega

end TimeReceipt

end Iris
