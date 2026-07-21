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

instance instSIdxOrdinal : SIdx Ordinal.{u} where
  toLT   := inferInstance
  toLE   := inferInstance
  toZero := inferInstance
  succ := Order.succ
  lt_trans h₁ h₂ := _root_.lt_trans h₁ h₂
  lt_wf := Ordinal.lt_wf
  lt_trichotomyT n m :=
    if h : n < m then .inl h
    else if h' : m < n then .inr <| .inr h'
    else .inr <| .inl <| le_antisymm (not_lt.mp h') (not_lt.mp h)
  le_lteq := le_iff_lt_or_eq
  not_lt_zero n := by simp
  lt_succ_self n := Order.lt_succ n
  succ_le_of_lt h := Order.succ_le_of_lt h
  weak_case n :=
    letI : Decidable (∃ m, n = Order.succ m) := Classical.propDecidable _
    if h : ∃ m, n = Order.succ m then
      .inl ⟨h.choose, h.choose_spec⟩
    else
      .inr fun m hm => lt_of_le_of_ne (Order.succ_le_of_lt hm) fun he => h ⟨m, he.symm⟩
