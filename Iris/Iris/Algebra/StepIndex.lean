/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Alvin Tang
-/
module

public meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris

@[rocq_alias sidx]
class SIdx (I : Type u) extends LT I, LE I, Zero I where
  succ : I → I
  lt_trans : ∀ (n m p : I), n < m → m < p → n < p
  lt_wf : WellFounded ((· < ·) : I → I → Prop)
  lt_trichotomyT : ∀ n m : I, n < m ⊕' n = m ⊕' m < n
  le_lteq : ∀ m n : I, n ≤ m ↔ n < m ∨ n = m
  not_lt_zero : ∀ n : I, ¬n < Zero.zero
  lt_succ_self : ∀ n : I, n < succ n
  succ_le_of_lt : ∀ n m : I, n < m → succ n ≤ m
  weak_case : ∀ n : I, (Σ' m : I, n = succ m) ⊕' ∀ m : I, m < n → succ m < n

#rocq_ignore SIdxMixin "Use the type class SIdx instead"

namespace SIdx

open Iris

variable {I : Type u} [inst : SIdx I] {m n p : I}

@[rocq_alias SIdx.nlt_0_r]
theorem nlt_0_r : ¬n < 0 := inst.not_lt_zero n

end SIdx
