/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Iris

@[expose] public section

noncomputable section

open Iris

instance ordinalSIdx : SIdx Ordinal.{u} where
  toLT := Ordinal.partialOrder.toLT
  toLE := Preorder.toLE
  toZero := Ordinal.zero
  succ := Order.succ
  lt_trans := lt_trans
  lt_wf := Ordinal.lt_wf
  lt_trichotomyT n m :=
    if h : n < m then .inl h
    else if h' : m < n then .inr <| .inr h'
    else .inr <| .inl <| le_antisymm (not_lt.mp h') (not_lt.mp h)
  le_lteq := le_iff_lt_or_eq
  not_lt_zero _ := by simp
  lt_succ_self := Order.lt_succ
  succ_le_of_lt := Order.succ_le_of_lt
  weak_case n :=
    letI : Decidable (∃ m, n = Order.succ m) := Classical.propDecidable _
    if h : ∃ m, n = Order.succ m then
      .inl ⟨h.choose, h.choose_spec⟩
    else
      .inr fun m hm => lt_of_le_of_ne (Order.succ_le_of_lt hm) fun he => h ⟨m, he.symm⟩

@[reducible]
def ordinalSubtypeSIdx (κ : Ordinal.{u}) (hκ : Order.IsSuccLimit κ) :
    SIdx {o : Ordinal.{u} // o < κ} where
  toLT := Subtype.instLT
  toLE := Subtype.instLE
  toZero := by constructor; constructor; exact hκ.pos
  succ o := ⟨Order.succ o.val, hκ.succ_lt o.2⟩
  lt_trans h₁ h₂ := _root_.lt_trans h₁ h₂
  lt_wf := InvImage.wf Subtype.val Ordinal.lt_wf
  lt_trichotomyT n m :=
    if h : n < m then .inl h
    else if h' : m < n then .inr <| .inr h'
    else .inr <| .inl <| le_antisymm (not_lt.mp h') (not_lt.mp h)
  le_lteq := le_iff_lt_or_eq
  not_lt_zero n :=
    show ¬n.val < 0
    by simp
  lt_succ_self n := Order.lt_succ n.val
  succ_le_of_lt {n m} h := by
    change Order.succ n.val ≤ m.val
    simpa
  weak_case n :=
    letI : Decidable (∃ m, n = (fun o : { o // o < κ } =>
        ⟨Order.succ o.val, hκ.succ_lt o.property⟩) m) :=
      Classical.propDecidable _
    if h : ∃ m, n = (fun o => ⟨Order.succ o.val, hκ.succ_lt o.property⟩) m then
      .inl ⟨h.choose, h.choose_spec⟩
    else
      .inr fun m hm =>
        lt_of_le_of_ne (Order.succ_le_of_lt hm : Order.succ m.val ≤ n.val)
          fun he => h ⟨m, he.symm⟩

theorem limit_iff_isSuccLimit {o : Ordinal.{u}} :
    SIdx.Limit o ↔ Order.IsSuccLimit o := by
  constructor
  · intro h
    constructor
    · exact not_isMin_iff.mpr ⟨0, h.limit_lt_0⟩
    · intro b hb
      apply hb.right (Order.lt_succ b) (h.succ_lt b hb.left)
  · intro h
    constructor
    · intro _ hm
      exact h.succ_lt hm
    · exact h.pos.ne'
