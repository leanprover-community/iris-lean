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

instance ordinalSIdx : SIdx Ordinal where
  toLT := inferInstance
  toLE := inferInstance
  toZero := inferInstance
  succ := Order.succ
  lt_trans := lt_trans
  lt_wf := Ordinal.lt_wf
  lt_trichotomyT n m :=
    if h : n < m then by left; exact h
    else if h' : m < n then by right; right; exact h'
    else by right; left; exact le_antisymm (not_lt.mp h') (not_lt.mp h)
  le_lteq := le_iff_lt_or_eq
  not_lt_zero _ := by simp
  lt_succ_self := Order.lt_succ
  succ_le_of_lt := Order.succ_le_of_lt
  weak_case n :=
    letI : Decidable (∃ m, n = Order.succ m) := Classical.propDecidable _
    if h : ∃ m, n = Order.succ m then by left; exact ⟨h.choose, h.choose_spec⟩
    else by
      right; intro m hm
      apply lt_of_le_of_ne
      · exact Order.succ_le_of_lt hm
      · intro he
        exact h ⟨m, he.symm⟩

@[reducible]
def ordinalToTypeSIdx (κ : Ordinal) (hκ : Order.IsSuccLimit κ) : SIdx κ.ToType :=
  haveI : Nonempty κ.ToType := Ordinal.nonempty_toType_iff.mpr hκ.pos.ne'
  letI : OrderBot κ.ToType := WellFoundedLT.toOrderBot κ.ToType
  haveI : NoMaxOrder κ.ToType := by
    apply Ordinal.isSuccPrelimit_type_lt_iff.mp
    simp only [Ordinal.type_toType, hκ.isSuccPrelimit]
  {
    toLT := inferInstance
    toLE := inferInstance
    toZero := ⟨⊥⟩
    succ := Order.succ
    lt_trans := lt_trans
    lt_wf := wellFounded_lt
    lt_trichotomyT n m :=
      if h : n < m then by left; exact h
      else if h' : m < n then by right; right; exact h'
      else by right; left; exact le_antisymm (not_lt.mp h') (not_lt.mp h)
    le_lteq := le_iff_lt_or_eq
    not_lt_zero _ := not_lt_bot
    lt_succ_self := Order.lt_succ
    succ_le_of_lt := Order.succ_le_of_lt
    weak_case n :=
      letI : Decidable (∃ m, n = Order.succ m) := Classical.propDecidable _
      if h : ∃ m, n = Order.succ m then by
        left; exact ⟨h.choose, h.choose_spec⟩
      else by
        right; intro m hm
        apply lt_of_le_of_ne
        · exact Order.succ_le_of_lt hm
        · intro he
          exact h ⟨m, he.symm⟩
  }

theorem limit_iff_isSuccLimit {o : Ordinal} : SIdx.Limit o ↔ Order.IsSuccLimit o := by
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
