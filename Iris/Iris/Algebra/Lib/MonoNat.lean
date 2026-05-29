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
scoped instance : COFE MaxNat := COFE.ofDiscrete _ Eq_Equivalence
scoped instance : OFE.Discrete MaxNat := ⟨congrArg id⟩
scoped instance : OFE.Leibniz MaxNat := ⟨congrArg id⟩
scoped instance : UCMRA MaxNat := OrdCommMonoidLike.instUCMRAOfLawfulLeftIdentityAddZero
scoped instance : CMRA.Discrete MaxNat := OrdCommMonoidLike.instDiscrete
scoped instance : CMRA.CoreId (a : MaxNat) := OrdCommMonoidLike.instCoreId _

end MaxNat

abbrev MonoNat (F : Type _) [UFraction F] := Auth F MaxNat

namespace MonoNat

variable [UFraction F]

@[rocq_alias mono_nat_auth]
def auth (dq : DFrac F) (n : MaxNat) : MonoNat F := (●{dq} n) • (◯ n)
@[rocq_alias mono_nat_lb]
def lb (n : MaxNat) : MonoNat F := ◯ n

notation "●MN{" dq "} " n => auth dq n
notation "●MN " n => auth (DFrac.own One.one) n
notation "●MN□ " n => auth DFrac.discard n
notation "◯MN " n => lb n

scoped instance : OFE.DiscreteE (◯MN n : MonoNat F) :=
  Auth.frag_discrete OrdCommMonoidLike.instDiscreteE
scoped instance : OFE.DiscreteE (●MN{dq} n : MonoNat F) :=
  ⟨fun h => OFE.discrete h⟩
scoped instance : IsUnit (◯MN 0 : MonoNat F) where
  unit_valid := by
    simpa only [lb, Auth.frag_valid] using True.intro
  unit_left_id {x} := .rfl
  pcore_unit := .rfl

@[rocq_alias mono_nat_lb_core_id]
instance {n : MaxNat} : CMRA.CoreId (◯MN n : MonoNat F) := by
  unfold lb
  infer_instance

@[rocq_alias mono_nat_auth_core_id]
instance {l : MaxNat} : CMRA.CoreId (●MN□ l : MonoNat F) := by
  unfold auth
  infer_instance

@[rocq_alias mono_nat_auth_dfrac_op]
theorem auth_dfrac_op (dq1 dq2 : DFrac F) (n : MaxNat) :
  (●MN{dq1 • dq2} n : MonoNat F) ≡ (●MN{dq1} n) • (●MN{dq2} n) := by
  refine CMRA.comm.trans ?_
  refine (CMRA.op_right_eqv _ Auth.auth_dfrac_op).trans ?_
  refine CMRA.comm.trans ?_
  refine CMRA.assoc.symm.trans ?_
  refine (CMRA.op_right_eqv _ CMRA.comm).trans ?_
  refine (CMRA.op_right_eqv _ (CMRA.op_self (◯ n)).symm.op_l).trans ?_
  refine (CMRA.op_right_eqv _ CMRA.assoc.symm).trans ?_
  refine CMRA.assoc.trans ?_
  refine CMRA.op_right_eqv _ CMRA.comm

@[rocq_alias mono_nat_lb_op]
theorem lb_op (n1 n2 : MaxNat) :
  (◯MN (max n1 n2) : MonoNat F) = ((◯MN n1) • (◯MN n2) : MonoNat F) :=
  Auth.frag_op

@[rocq_alias mono_nat_auth_lb_op]
theorem auth_lb_op (dq : DFrac F) (n : MaxNat) :
  (●MN{dq} n : MonoNat F) ≡ (●MN{dq} n) • (◯MN n) := by
  refine .trans ?_ CMRA.assoc
  simp only [lb, ←Auth.frag_op]
  refine CMRA.op_right_eqv _ ?_
  simp [CMRA.op, Add.add]

@[rocq_alias mono_nat_lb_op_le_l]
theorem lb_op_le_l (n n' : MaxNat) (h : n' ≤ n) :
  (◯MN n : MonoNat F) = ((◯MN n') • (◯MN n) : MonoNat F) := by
  rw [←lb_op]
  congr
  simp only [h, Nat.max_eq_right]

@[rocq_alias mono_nat_auth_dfrac_valid]
theorem auth_dfrac_valid (dq : DFrac F) (n : MaxNat) :
  (✓ (●MN{dq} n : MonoNat F)) ↔ ✓ dq := by
  refine Auth.both_dfrac_valid_discrete.trans ?_
  simpa only [CMRA.inc_refl, true_and] using ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, True.intro⟩⟩

@[rocq_alias mono_nat_auth_valid]
theorem auth_valid (n : MaxNat) :
  ✓ (●MN n : MonoNat F) :=
  auth_dfrac_valid _ _ |>.mpr DFrac.valid_own_one

@[rocq_alias mono_nat_auth_dfrac_op_valid]
theorem auth_dfrac_op_valid (dq1 dq2 : DFrac F) (n1 n2 : MaxNat) :
  (✓ ((●MN{dq1} n1) • (●MN{dq2} n2) : MonoNat F)) ↔ ✓ (dq1 • dq2) ∧ n1 = n2 := by
  constructor
  · intro h
    unfold auth at h
    replace h := CMRA.valid_of_eqv (CMRA.assoc.symm.trans <| (CMRA.op_right_eqv _ <|
      CMRA.assoc.trans <| (CMRA.op_left_eqv _ CMRA.comm).trans CMRA.assoc.symm).trans
      CMRA.assoc) h
    have ⟨hdq, heq, _⟩ := Auth.auth_dfrac_op_valid.mp (CMRA.valid_op_left h)
    exact ⟨hdq, OFE.Leibniz.eq_of_eqv heq⟩
  · rintro ⟨hdq, rfl⟩
    refine CMRA.valid_of_eqv ?_ (Auth.both_dfrac_valid_discrete.mpr ⟨hdq, CMRA.inc_refl n1, trivial⟩)
    exact auth_dfrac_op dq1 dq2 n1

@[rocq_alias mono_nat_auth_op_valid]
theorem auth_op_valid (n1 n2 : MaxNat) :
  (✓ ((●MN n1) • (●MN n2) : MonoNat F)) ↔ False := by
  refine (auth_dfrac_op_valid _ _ n1 n2).trans ?_
  refine ⟨fun ⟨h, _⟩ => ?_, False.elim⟩
  exact DFrac.own_whole_exclusive UFraction.one_whole |>.exclusive0_l _ h.validN

@[rocq_alias mono_nat_both_dfrac_valid]
theorem both_dfrac_valid (dq : DFrac F) (n m : MaxNat) :
  (✓ ((●MN{dq} n) • (◯MN m) : MonoNat F)) ↔ ✓ dq ∧ m ≤ n := by
  unfold auth lb
  rw [CMRA.valid_iff CMRA.assoc.symm, ←Auth.frag_op, Auth.both_dfrac_valid_discrete]
  constructor
  · intro ⟨hdq, ⟨k, hk⟩, _⟩; refine ⟨hdq, ?_⟩
    simp only [CMRA.op, Add.add, OFE.Equiv] at hk
    grind
  · intro ⟨hdq, hle⟩; refine ⟨hdq, ⟨0, ?_⟩, trivial⟩
    simp [CMRA.op, Add.add, OFE.Equiv, Nat.max_eq_left hle]

@[rocq_alias mono_nat_both_valid]
theorem both_valid (n m : MaxNat) :
  (✓ ((●MN n) • (◯MN m) : MonoNat F)) ↔ m ≤ n := by
  simp only [both_dfrac_valid, DFrac.valid_own_one, true_and]

@[rocq_alias mono_nat_lb_mono]
theorem lb_mono (n1 n2 : MaxNat) (h : n1 ≤ n2) :
  (◯MN n1 : MonoNat F) ≼ ◯MN n2 := by
  refine Auth.frag_inc_of_inc ?_
  exists n2
  simp only [CMRA.op, Add.add, OFE.Equiv]
  grind

@[rocq_alias mono_nat_included]
theorem included (dq : DFrac F) (n : MaxNat) :
  (◯MN n : MonoNat F) ≼ ●MN{dq} n :=
  CMRA.inc_op_right _ _

@[rocq_alias mono_nat_update]
theorem update {n : MaxNat} (n' : MaxNat) (h : n ≤ n') :
  (●MN n : MonoNat F) ~~> ●MN n' := by
  refine Auth.auth_update (fun _ mz _ hn => ?_)
  refine ⟨trivial, ?_⟩
  cases mz with | none => rfl | some z =>
  simp only [CMRA.op?, CMRA.op, Add.add] at hn ⊢
  exact OFE.Dist.of_eq (Nat.max_eq_left (Nat.le_trans (hn ▸ Nat.le_max_right n z) h)).symm

@[rocq_alias mono_nat_auth_persist]
theorem auth_persist (n : MaxNat) (dq : DFrac F) :
  (●MN{dq} n : MonoNat F) ~~> ●MN□ n :=
  Update.op Auth.auth_update_auth_persist (fun _ _ h => h)

@[rocq_alias mono_nat_auth_unpersist]
theorem auth_unpersist [IsHalfFraction F] (n : MaxNat) :
  (●MN□ n : MonoNat F) ~~>: (fun k => ∃ q, k = ●MN{DFrac.own q} n) :=
  Auth.auth_updateP_both_unpersist

set_option synthInstance.checkSynthOrder false in
@[rocq_alias mono_nat_auth_dfrac_is_op]
instance {dq dq1 dq2 : DFrac F} {n : MaxNat}
    [h : IsOp io1 dq io2 dq1 io3 dq2] :
    IsOp io1 (●MN{dq} n) io2 (●MN{dq1} n) io3 (●MN{dq2} n) where
  is_op := by rw [h.is_op]; apply auth_dfrac_op

@[rocq_alias mono_nat_lb_max_is_op]
instance {n n1 n2 : MaxNat}
    [h : IsOp io1 n io2 n1 io3 n2] :
    IsOp io1 (◯MN n : MonoNat F) io2 (◯MN n1) io3 (◯MN n2) where
  is_op := by rw [h.is_op]; .rfl

end MonoNat

end Iris
