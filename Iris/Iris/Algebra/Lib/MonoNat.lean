/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra.Auth
public import Iris.Algebra.LocalUpdates
public import Iris.Algebra.Numbers

@[expose] public section

namespace Iris

open _root_.Std (Associative Commutative LeftIdentity LawfulLeftIdentity)

section MaxNat

abbrev MaxNat := Nat

scoped instance : Add MaxNat := ⟨max⟩
scoped instance : Associative (Add.add (α := MaxNat)) where
  assoc := Nat.max_assoc
scoped instance : Commutative (Add.add (α := MaxNat)) where
  comm := Nat.max_comm
scoped instance : Zero MaxNat := ⟨0⟩
scoped instance : LawfulLeftIdentity (Add.add (α := MaxNat)) (0 : MaxNat) where
  left_id := Nat.zero_max
scoped instance : Std.IdempotentOp (Add.add (α := MaxNat)) where
  idempotent x := by simp [Add.add]
scoped instance : COFE MaxNat := COFE.ofDiscrete _
scoped instance : OFE.Discrete MaxNat := ⟨fun h => h⟩
scoped instance : UCMRA MaxNat := OrdCommMonoidLike.instUCMRAOfLawfulLeftIdentityAddZero
scoped instance : CMRA.Discrete MaxNat := OrdCommMonoidLike.instDiscrete
scoped instance : CMRA.CoreId (a : MaxNat) := OrdCommMonoidLike.instCoreId _

end MaxNat

abbrev MonoNat := Auth MaxNat

namespace MonoNat

@[rocq_alias mono_nat_auth]
def auth (dq : DFrac) (n : MaxNat) : MonoNat := (●{dq} n) • (◯ n)
@[rocq_alias mono_nat_lb]
def lb (n : MaxNat) : MonoNat := ◯ n

notation "●MN{" dq "} " n => auth dq n
notation "●MN " n => auth (DFrac.own 1) n
notation "●MN□ " n => auth DFrac.discard n
notation "◯MN " n => lb n

scoped instance : OFE.DiscreteE (◯MN n : MonoNat) := Auth.frag_discrete
scoped instance : OFE.DiscreteE (●MN{dq} n : MonoNat) :=
  ⟨fun h => OFE.discrete h⟩
scoped instance : IsUnit (◯MN 0 : MonoNat) where
  unit_valid := by simp only [lb, Auth.frag_valid]; exact True.intro
  unit_left_id {x} := rfl
  pcore_unit := rfl

@[rocq_alias mono_nat_lb_core_id]
instance {n : MaxNat} : CMRA.CoreId (◯MN n : MonoNat) := by
  unfold lb
  infer_instance

@[rocq_alias mono_nat_auth_core_id]
instance {l : MaxNat} : CMRA.CoreId (●MN□ l : MonoNat) := by
  unfold auth
  infer_instance

@[rocq_alias mono_nat_auth_dfrac_op]
theorem auth_dfrac_op (dq1 dq2 : DFrac) (n : MaxNat) :
  (●MN{dq1 • dq2} n : MonoNat) = (●MN{dq1} n) • (●MN{dq2} n) :=
  CMRA.comm'.trans <|
  (congrArg ((◯ n) • ·) Auth.auth_dfrac_op).trans <|
  CMRA.comm'.trans <|
  CMRA.assoc'.symm.trans <|
  (congrArg ((●{dq1} n) • ·) CMRA.comm').trans <|
  (congrArg ((●{dq1} n) • ·) (congrArg (· • ●{dq2} n) (CMRA.op_self (◯ n)).symm)).trans <|
  (congrArg ((●{dq1} n) • ·) CMRA.assoc'.symm).trans <|
  CMRA.assoc'.trans <|
  congrArg (((●{dq1} n) • ◯ n) • ·) CMRA.comm'

@[rocq_alias mono_nat_lb_op]
theorem lb_op (n1 n2 : MaxNat) :
  (◯MN (max n1 n2) : MonoNat) = ((◯MN n1) • (◯MN n2) : MonoNat) :=
  Auth.frag_op

@[rocq_alias mono_nat_auth_lb_op]
theorem auth_lb_op (dq : DFrac) (n : MaxNat) :
  (●MN{dq} n : MonoNat) = (●MN{dq} n) • (◯MN n) := by
  refine .trans ?_ CMRA.assoc'
  simp only [lb, ←Auth.frag_op]
  refine congrArg ((●{dq} n) • ·) ?_
  simp [CMRA.op, Add.add]

@[rocq_alias mono_nat_lb_op_le_l]
theorem lb_op_le_l (n n' : MaxNat) (h : n' ≤ n) :
  (◯MN n : MonoNat) = ((◯MN n') • (◯MN n) : MonoNat) := by
  rw [←lb_op]
  congr
  simp only [h, Nat.max_eq_right]

@[rocq_alias mono_nat_auth_dfrac_valid]
theorem auth_dfrac_valid (dq : DFrac) (n : MaxNat) :
  (✓ (●MN{dq} n : MonoNat)) ↔ ✓ dq := by
  refine Auth.both_dfrac_valid_discrete.trans ?_
  simpa only [CMRA.inc_refl, true_and] using ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, True.intro⟩⟩

@[rocq_alias mono_nat_auth_valid]
theorem auth_valid (n : MaxNat) :
  ✓ (●MN n : MonoNat) :=
  auth_dfrac_valid _ _ |>.mpr DFrac.valid_own_one

@[rocq_alias mono_nat_auth_dfrac_op_valid]
theorem auth_dfrac_op_valid (dq1 dq2 : DFrac) (n1 n2 : MaxNat) :
  (✓ ((●MN{dq1} n1) • (●MN{dq2} n2) : MonoNat)) ↔ ✓ (dq1 • dq2) ∧ n1 = n2 := by
  constructor
  · intro h
    unfold auth at h
    replace h := (CMRA.assoc'.symm.trans <|
      (congrArg (CMRA.op (●{dq1} n1)) <|
        CMRA.assoc'.trans <|
          (congrArg (CMRA.op · (◯ n2)) CMRA.comm').trans CMRA.assoc'.symm).trans
      CMRA.assoc') ▸ h
    have ⟨hdq, heq, _⟩ := Auth.auth_dfrac_op_valid.mp (CMRA.valid_op_left h)
    exact ⟨hdq, heq⟩
  · rintro ⟨hdq, rfl⟩
    exact auth_dfrac_op dq1 dq2 n1 ▸
      Auth.both_dfrac_valid_discrete.mpr ⟨hdq, CMRA.inc_refl n1, trivial⟩

@[rocq_alias mono_nat_auth_op_valid]
theorem auth_op_valid (n1 n2 : MaxNat) :
  (✓ ((●MN n1) • (●MN n2) : MonoNat)) ↔ False := by
  refine (auth_dfrac_op_valid _ _ n1 n2).trans ?_
  refine ⟨fun ⟨h, _⟩ => ?_, False.elim⟩
  exact DFrac.own_whole_exclusive |>.exclusive0_l _ h.validN

@[rocq_alias mono_nat_both_dfrac_valid]
theorem both_dfrac_valid (dq : DFrac) (n m : MaxNat) :
  (✓ ((●MN{dq} n) • (◯MN m) : MonoNat)) ↔ ✓ dq ∧ m ≤ n := by
  unfold auth lb
  rw [CMRA.assoc'.symm, ←Auth.frag_op, Auth.both_dfrac_valid_discrete]
  constructor
  · intro ⟨hdq, ⟨k, hk⟩, _⟩; refine ⟨hdq, ?_⟩
    simp only [CMRA.op, Add.add] at hk
    grind
  · intro ⟨hdq, hle⟩; refine ⟨hdq, ⟨0, ?_⟩, trivial⟩
    simp [CMRA.op, Add.add, Nat.max_eq_left hle]

@[rocq_alias mono_nat_both_valid]
theorem both_valid (n m : MaxNat) :
  (✓ ((●MN n) • (◯MN m) : MonoNat)) ↔ m ≤ n := by
  rw [both_dfrac_valid]
  exact ⟨fun h => h.2, fun h => ⟨DFrac.valid_own_one, h⟩⟩

@[rocq_alias mono_nat_lb_mono]
theorem lb_mono (n1 n2 : MaxNat) (h : n1 ≤ n2) :
  (◯MN n1 : MonoNat) ≼ ◯MN n2 := by
  refine Auth.frag_inc_of_inc ?_
  exists n2
  simp only [CMRA.op, Add.add]
  grind

@[rocq_alias mono_nat_included]
theorem included (dq : DFrac) (n : MaxNat) :
  (◯MN n : MonoNat) ≼ ●MN{dq} n :=
  CMRA.inc_op_right _ _

@[rocq_alias mono_nat_update]
theorem update {n : MaxNat} (n' : MaxNat) (h : n ≤ n') :
  (●MN n : MonoNat) ~~> ●MN n' := by
  refine Auth.auth_update (fun _ mz _ hn => ?_)
  refine ⟨trivial, ?_⟩
  cases mz with | none => rfl | some z =>
  simp only [CMRA.op?, CMRA.op, Add.add] at hn ⊢
  exact OFE.Dist.of_eq (Nat.max_eq_left (Nat.le_trans (hn ▸ Nat.le_max_right n z) h)).symm

@[rocq_alias mono_nat_auth_persist]
theorem auth_persist (n : MaxNat) (dq : DFrac) :
  (●MN{dq} n : MonoNat) ~~> ●MN□ n :=
  Update.op Auth.auth_update_auth_persist (fun _ _ h => h)

@[rocq_alias mono_nat_auth_unpersist]
theorem auth_unpersist (n : MaxNat) :
  (●MN□ n : MonoNat) ~~>: (fun k => ∃ q, k = ●MN{DFrac.own q} n) :=
  Auth.auth_updateP_both_unpersist

set_option synthInstance.checkSynthOrder false in
@[rocq_alias mono_nat_auth_dfrac_is_op]
instance {dq dq1 dq2 : DFrac} {n : MaxNat}
    [h : IsOp d dq dq1 dq2] :
    IsOp d (●MN{dq} n) (●MN{dq1} n) (●MN{dq2} n) where
  is_op := by rw [h.is_op]; apply auth_dfrac_op

@[rocq_alias mono_nat_lb_max_is_op]
instance {n n1 n2 : MaxNat}
    [h : IsOp d n n1 n2] :
    IsOp d (◯MN n : MonoNat) (◯MN n1) (◯MN n2) where
  is_op := by rw [h.is_op]; exact rfl

end MonoNat

end Iris
