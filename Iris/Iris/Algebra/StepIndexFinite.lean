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
  lt_trans := Nat.lt_trans
  lt_wf := Nat.lt_wfRel.wf
  lt_trichotomyT n m :=
    if h : n < m then .inl h
    else if he : n = m then .inr <| .inl he
    else .inr <| .inr (by omega)
  le_lteq {_ _} := Nat.le_iff_lt_or_eq
  not_lt_zero n := by simp
  weak_case
    | 0 => .inr fun _ _ h => absurd h (by omega)
    | m + 1 => .inl ⟨m, by simp, fun ⟨p, h1, h2⟩ => by omega⟩

instance natSIdxSucc : SIdxSucc Nat where
  succ := Nat.succ
  succ_isSucc n := ⟨by simp, fun ⟨p, h1, h2⟩ => by omega⟩

@[rocq_alias nat_sidx_finite]
instance natSIdxFinite : SIdxFinite Nat where
  finite_index | 0 => .inl rfl | n + 1 => .inr ⟨n, by simp, fun ⟨p, h1, h2⟩ => by omega⟩

/-- No step-indexing: `Unit` has the single index `0`, so nothing lies below it. -/
instance unitSIdx : SIdx Unit where
  lt _ _ := False
  le _ _ := True
  zero := ()
  lt_trans h := h.elim
  lt_wf := ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩
  lt_trichotomyT _ _ := .inr (.inl rfl)
  le_lteq := ⟨fun _ => .inr rfl, fun _ => trivial⟩
  not_lt_zero _ h := h
  weak_case _ := .inr fun _ _ h => h.elim

instance unitSIdxZero : SIdxZero Unit := ⟨fun _ => rfl⟩

def SIdx.Limit.elim {I : Type u} [SIdx I] [SIdxFinite I] {n : I} {C : Sort v}
    (h : SIdx.Limit n) : C := SIdx.limit_finite n h |>.elim

namespace OFE


theorem Dist.leNat [OFE Nat α] {m n : Nat} {x y : α} (h : x ≡{n}≡ y) (h' : m ≤ n) : x ≡{m}≡ y :=
  if hm : m = n then hm ▸ h else h.lt <| Nat.lt_of_le_of_ne h' hm

theorem Contractive.succNat [OFE Nat α] [OFE Nat β] (f : α → β) [Contractive Nat f] {n : Nat} {x y}
    (h : x ≡{n}≡ y) : f x ≡{n.succ}≡ f y :=
  Contractive.distLater_dist <| distLater_succ.mpr h

end OFE

end Iris
