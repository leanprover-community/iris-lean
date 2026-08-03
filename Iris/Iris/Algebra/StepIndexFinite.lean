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
  zero := 0
  succ := Nat.succ
  lt_trans := Nat.lt_trans
  lt_wf := Nat.lt_wfRel.wf
  lt_trichotomyT n m :=
    if h : n < m then .inl h
    else if he : n = m then .inr <| .inl he
    else .inr <| .inr (by omega)
  le_lteq {_ _} := Nat.le_iff_lt_or_eq
  not_lt_zero n := by simp
  lt_succ_self n := by simp
  succ_le_of_lt h := h
  weak_case
    | 0 => .inr (by omega)
    | m + 1 => .inl ⟨_, rfl⟩

@[rocq_alias nat_sidx_finite]
instance natSIdxFinite : SIdxFinite Nat where
  finite_index | 0 => .inl rfl | n + 1 => .inr ⟨n, rfl⟩

def SIdx.Limit.elim {I : Type u} [SIdx I] [SIdxFinite I] {n : I} {C : Sort v}
    (h : SIdx.Limit n) : C := SIdx.limit_finite n h |>.elim

namespace OFE

theorem Dist.leNat [OFE Nat α] {m n} {x y : α} (h : x ≡{n}≡ y) (h' : m ≤ n) : x ≡{m}≡ y :=
  if hm : m = n then hm ▸ h else h.lt <| Nat.lt_of_le_of_ne h' hm

theorem Contractive.succNat [OFE Nat α] [OFE Nat β] (f : α → β) [Contractive f] {n x y}
    (h : x ≡{n}≡ y) : f x ≡{n.succ}≡ f y :=
  Contractive.distLater_dist <| distLater_succ.mpr h

instance DiscreteO.instCOFE_Nat {α : Type _} : COFE Nat (DiscreteO α) := DiscreteO.instCOFE

instance DiscreteO.discrete_Nat {α : Type _} : OFE.Discrete (SI := Nat) (DiscreteO α) :=
  DiscreteO.OFE

instance unitCOFE_Nat : COFE Nat Unit := COFE.unitCOFE

end OFE
