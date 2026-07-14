/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Alvin Tang
-/
module

public meta import Iris.Std.RocqPorting
public import Iris.Std.Classes

@[expose] public section

namespace Iris

@[rocq_alias sidx]
class SIdx (I : Type u) extends LT I, LE I, Zero I where
  succ : I → I
  lt_trans : ∀ {n m p : I}, n < m → m < p → n < p
  lt_wf : WellFounded ((· < ·) : I → I → Prop)
  lt_trichotomyT : ∀ n m : I, n < m ⊕' n = m ⊕' m < n
  le_lteq : ∀ {m n : I}, n ≤ m ↔ n < m ∨ n = m
  not_lt_zero : ∀ n : I, ¬n < 0
  lt_succ_self : ∀ n : I, n < succ n
  succ_le_of_lt : ∀ {n m : I}, n < m → succ n ≤ m
  weak_case : ∀ n : I, (Σ' m : I, n = succ m) ⊕' ∀ m : I, m < n → succ m < n

/-- The step-indexing successor operator. -/
scoped prefix:max "succᵢ" => SIdx.succ

class SIdxFinite (I : Type u) [SIdx I] : Prop where
  finite_index : ∀ n : I, n = 0 ∨ ∃ m, n = succᵢ m

#rocq_ignore SIdxMixin "Use the type class SIdx instead"

namespace SIdx

open Iris Std

variable {I : Type u} [inst : SIdx I] {m n p : I}

@[rocq_alias SIdx.nlt_0_r]
theorem nlt_0_r : ¬n < 0 := inst.not_lt_zero n

@[rocq_alias SIdx.lt_succ_diag_r]
theorem lt_succ_diag_r : n < succᵢ n := inst.lt_succ_self n

@[rocq_alias SIdx.le_succ_l_2]
theorem le_succ_l_2 (h : n < m) : succᵢ n ≤ m := inst.succ_le_of_lt h

@[rocq_alias SIdx.inhabited]
instance inhabited : Inhabited I where
  default := 0

instance lt_irrefl : Irreflexive inst.lt where
  irrefl := by
    intro n
    induction n using lt_wf.induction with
    | x_1 => assumption
    | h x ih =>
      apply ih
      sorry

@[rocq_alias SIdx.lt_strict]
instance lt_struct : StrictOrder inst.lt where
  trans := inst.lt_trans

/-- For the `rfl` tactic. -/
@[refl]
theorem le_refl_thm : n ≤ n := inst.le_lteq.mpr <| .inr rfl

instance le_refl : Reflexive inst.le where
  refl := le_refl_thm

instance le_trans : Transitive inst.le where
  trans := by
    intro x y z hxy hyz
    sorry

instance le_antisymm : Antisymmetric Eq inst.le where
  antisymm := by
    intro x y hxy hyx
    sorry

@[rocq_alias SIdx.le_po]
instance le_po : PartialOrder inst.le where

@[rocq_alias SIdx.lt_le_incl]
theorem lt_le_incl (h : n < m) : n ≤ m := by
  apply le_lteq.mpr; left; assumption

@[rocq_alias SIdx.le_total]
theorem le_total : Total inst.le where
  total := by
    intro x y
    sorry

@[rocq_alias SIdx.lt_le_trans]
theorem lt_le_trans (h1 : n < m) (h2 : m ≤ p) : n < p := by
  rcases SIdx.le_lteq.mp h2 with (h2 | h2)
  · exact SIdx.lt_trans h1 h2
  · subst h2; assumption

@[rocq_alias SIdx.le_lt_trans]
theorem le_lt_trans (h1 : n ≤ m) (h2 : m < p) : n < p := by
  rcases SIdx.le_lteq.mp h1 with (h1 | h1)
  · exact SIdx.lt_trans h1 h2
  · subst h1; assumption

@[rocq_alias SIdx.le_succ_l]
theorem le_succ_l : succᵢ n ≤ m ↔ n < m := by
  constructor <;> intro h
  · exact lt_le_trans (lt_succ_self n) h
  · exact le_succ_l_2 h

@[rocq_alias SIdx.lt_succ_r]
theorem lt_succ_r : n < succᵢ m ↔ n ≤ m := by
  constructor <;> intro h
  · have b := le_succ_l_2 h
    sorry
  · exact le_lt_trans h lt_succ_diag_r

@[rocq_alias SIdx.succ_le_mono]
theorem succ_le_mono : n ≤ m ↔ succᵢ n ≤ succᵢ m := by
  rewrite [le_succ_l, lt_succ_r]; rfl

@[rocq_alias SIdx.succ_lt_mono]
theorem succ_lt_mono : n < m ↔ succᵢ n < succᵢ m := by
  rewrite [lt_succ_r, le_succ_l]; rfl

-- instance succ_inj : Function.Injective Eq Eq (fun x => succᵢ x)

@[rocq_alias SIdx.le_succ_diag_r]
theorem le_succ_diag_r : n ≤ succᵢ n := by
  apply lt_le_incl
  apply lt_succ_diag_r

@[rocq_alias SIdx.neq_0_lt_0]
theorem neq_0_lt_0 : n ≠ 0 ↔ 0 < n := by
  constructor <;> intro h
  · sorry
  · have h1 := nlt_0_r (inst := inst) (n := 0)
    sorry

@[rocq_alias SIdx.lt_ge_cases]
theorem lt_ge_cases : n < m ∨ m ≤ n := sorry

@[rocq_alias SIdx.le_gt_cases]
theorem le_gt_cases : n ≤ m ∨ m < n := sorry

@[rocq_alias SIdx.le_ngt]
theorem le_ngt : n ≤ m ↔ ¬ m < n := sorry

@[rocq_alias SIdx.lt_nge]
theorem lt_nge : n < m ↔ ¬ m ≤ n := sorry

@[rocq_alias SIdx.le_neq]
theorem le_neq : n < m ↔ n ≤ m ∧ n ≠ m := sorry

@[rocq_alias SIdx.nlt_succ_r]
theorem nlt_succ_r : ¬ m < succᵢ n ↔ n < m := sorry

@[rocq_alias SIdx.le_0_l]
theorem le_0_l : 0 ≤ n := le_ngt.mpr nlt_0_r

@[rocq_alias SIdx.le_0_r]
theorem le_0_r : n ≤ 0 ↔ n = 0 := by
  constructor <;> intro h
  · apply antisymm
    · assumption
    · exact le_0_l
  · subst h; rfl

@[rocq_alias neq_succ_0]
theorem neq_succ_0 : succᵢ n ≠ 0 := neq_0_lt_0.mpr <| lt_succ_r.mpr le_0_l

@[rocq_alias succ_neq]
theorem succ_neq : n ≠ succᵢ n := sorry

end SIdx
