/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Iris

@[expose] public section

noncomputable section

open Iris

/-- In a successor order without a maximum, `Order.succ m` is the successor of `m`. -/
theorem isSucc_succ {α : Type _} [LinearOrder α] [SuccOrder α] [NoMaxOrder α] (m : α) :
    IsSucc m (Order.succ m) :=
  ⟨Order.lt_succ m, fun ⟨_, h1, h2⟩ => (not_lt.mpr (Order.lt_succ_iff.mp h2)) h1⟩

theorem Iris.IsSucc.eq_succ {α : Type _} [LinearOrder α] [SuccOrder α] {m sm : α}
    (h : IsSucc m sm) : sm = Order.succ m :=
  le_antisymm
    (not_lt.mp fun hlt => h.least ⟨_, Order.lt_succ_of_not_isMax (not_isMax_of_lt h.lt), hlt⟩)
    (Order.succ_le_of_lt h.lt)

/-- The `weak_case` field of `SIdx`, for any successor order without a maximum. -/
def weakCase {α : Type _} [LinearOrder α] [SuccOrder α] [NoMaxOrder α] (n : α) :
    (Σ' m : α, IsSucc m n) ⊕' ∀ m sm : α, m < n → IsSucc m sm → sm < n :=
  letI : Decidable (∃ m, n = Order.succ m) := Classical.propDecidable _
  if h : ∃ m, n = Order.succ m then
    .inl ⟨h.choose, (congrArg (IsSucc h.choose) h.choose_spec).mpr (isSucc_succ _)⟩
  else .inr fun m _ hm hs => by
    rw [hs.eq_succ]
    exact lt_of_le_of_ne (Order.succ_le_of_lt hm) fun he => h ⟨m, he.symm⟩

instance ordinalSIdx : SIdx Ordinal where
  toLT := inferInstance
  toLE := inferInstance
  toZero := inferInstance
  lt_trans := lt_trans
  lt_wf := Ordinal.lt_wf
  lt_trichotomyT n m :=
    if h : n < m then by left; exact h
    else if h' : m < n then by right; right; exact h'
    else by right; left; exact le_antisymm (not_lt.mp h') (not_lt.mp h)
  le_lteq := le_iff_lt_or_eq
  not_lt_zero _ := by simp
  weak_case := weakCase

instance ordinalSIdxSucc : SIdxSucc Ordinal where
  succ := Order.succ
  succ_isSucc := isSucc_succ

theorem ordinalToType_noMaxOrder (κ : Ordinal) (hκ : Order.IsSuccLimit κ) :
    NoMaxOrder κ.ToType := by
  have : Nonempty κ.ToType := Ordinal.nonempty_toType_iff.mpr hκ.pos.ne'
  apply Ordinal.isSuccPrelimit_type_lt_iff.mp
  simp only [Ordinal.type_toType, hκ.isSuccPrelimit]

@[reducible]
def ordinalToTypeSIdx (κ : Ordinal) (hκ : Order.IsSuccLimit κ) : SIdx κ.ToType :=
  haveI : Nonempty κ.ToType := Ordinal.nonempty_toType_iff.mpr hκ.pos.ne'
  letI : OrderBot κ.ToType := WellFoundedLT.toOrderBot κ.ToType
  haveI := ordinalToType_noMaxOrder κ hκ
  {
    toLT := inferInstance
    toLE := inferInstance
    toZero := ⟨⊥⟩
    lt_trans := lt_trans
    lt_wf := wellFounded_lt
    lt_trichotomyT n m :=
      if h : n < m then by left; exact h
      else if h' : m < n then by right; right; exact h'
      else by right; left; exact le_antisymm (not_lt.mp h') (not_lt.mp h)
    le_lteq := le_iff_lt_or_eq
    not_lt_zero _ := not_lt_bot
    weak_case := weakCase
  }

@[reducible]
def ordinalToTypeSIdxSucc (κ : Ordinal) (hκ : Order.IsSuccLimit κ) :
    @SIdxSucc κ.ToType (ordinalToTypeSIdx κ hκ) :=
  letI := ordinalToTypeSIdx κ hκ
  haveI := ordinalToType_noMaxOrder κ hκ
  { succ := Order.succ, succ_isSucc := isSucc_succ }

theorem limit_iff_isSuccLimit {o : Ordinal} : SIdx.Limit o ↔ Order.IsSuccLimit o := by
  constructor
  · intro h
    constructor
    · exact not_isMin_iff.mpr ⟨0, pos_iff_ne_zero.mpr h.ne_zero⟩
    · intro b hb
      apply hb.right (Order.lt_succ b) (h.gt_succ b _ hb.left (isSucc_succ b))
  · intro h
    constructor
    · intro _ _ hm hs
      rw [hs.eq_succ]
      exact h.succ_lt hm
    · exact h.pos.ne'
