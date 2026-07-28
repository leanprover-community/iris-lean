/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public import Iris.Algebra.StepIndex
public import Iris.Algebra.OFE
public import Iris.Std.Classes
public meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris

@[rocq_alias natSI, rocq_alias nat_sidx_mixin]
instance natSIdx : SIdx Nat where
  toLT := instLTNat
  toLE := instLENat
  zero := 0
  succ := Nat.succ
  lt_trans := Nat.lt_trans
  lt_wf := Nat.lt_wfRel.wf
  lt_trichotomyT n m :=
    if h : n < m then by left; exact h
    else if he : n = m then by right; left; exact he
    else by
      right; right; apply Nat.lt_of_not_ge
      change ¬n ≤ m
      rw [Nat.le_iff_lt_or_eq]
      intro h'
      exact h'.elim h he
  le_lteq {n m} := Nat.le_iff_lt_or_eq
  not_lt_zero n := by simp
  lt_succ_self n := by simp
  succ_le_of_lt h := h
  weak_case n :=
    match n with
    | 0 => by right; intro m h; exact absurd h (Nat.not_lt_zero m)
    | m + 1 => by left; constructor; rfl

@[rocq_alias nat_sidx_finite]
instance natSIdxFinite : SIdxFinite Nat where
  finite_index := by
    intro n
    cases n with
    | zero => left; rfl
    | succ n => right; exists n

namespace OFE

variable {α : Type _} [OFE Nat α]

@[rocq_alias dist_le]
theorem Dist.le [OFE α] {m n} {x y : α} (h : x ≡{n}≡ y) (h' : m ≤ n) : x ≡{m}≡ y :=
  if hm : m = n then hm ▸ h else h.lt (Nat.lt_of_le_of_ne h' hm)

@[rocq_alias contractive_S]
theorem Contractive.succ [OFE α] [OFE β] (f : α → β) [Contractive f] {n x y}
    (h : x ≡{n}≡ y) : f x ≡{n.succ}≡ f y :=
  Contractive.distLater_dist (distLater_succ.2 h)

#rocq_ignore dist_S "Subsumed by `Dist.lt`/`Dist.le`."

end OFE
