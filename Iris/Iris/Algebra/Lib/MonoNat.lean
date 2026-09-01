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

@[rocq_alias mono_nat]
abbrev MonoNat := Auth MaxNat

#rocq_ignore mono_natR "Use the MonoNat type and View.instCMRA typeclass"
#rocq_ignore mono_natUR "Use the MonoNat type and View.instUCMRA typeclass"

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
  unit_valid := Auth.frag_valid.mpr trivial
  unit_left_id := rfl
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
  (●MN{dq1 • dq2} n : MonoNat) = (●MN{dq1} n) • (●MN{dq2} n) := by
  unfold auth
  rw [← CMRA.assoc', RABase.op_core_right_of_incExt (RABase.incExt_op_right ..), CMRA.assoc',
    ← Auth.auth_dfrac_op]

@[rocq_alias mono_nat_lb_op]
theorem lb_op (n1 n2 : MaxNat) :
  (◯MN (n1 + n2) : MonoNat) = ((◯MN n1) • (◯MN n2) : MonoNat) :=
  Auth.frag_op

@[rocq_alias mono_nat_auth_lb_op]
theorem auth_lb_op (dq : DFrac) (n : MaxNat) :
  (●MN{dq} n : MonoNat) = (●MN{dq} n) • (◯MN n) :=
  (RABase.op_core_left_of_incExt (RABase.incExt_op_right ..)).symm

@[rocq_alias mono_nat_lb_op_le_l]
theorem lb_op_le_l (n n' : MaxNat) (h : n' ≤ n) :
  (◯MN n : MonoNat) = ((◯MN n') • (◯MN n) : MonoNat) :=
  (congrArg lb (by grind)).trans (lb_op n' n)

@[rocq_alias mono_nat_auth_dfrac_valid]
theorem auth_dfrac_valid (dq : DFrac) (n : MaxNat) :
  (✓ (●MN{dq} n : MonoNat)) ↔ ✓ dq :=
  Auth.both_dfrac_valid_discrete.trans ⟨And.left, fun h => ⟨h, RABase.incExt_refl _, trivial⟩⟩

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
    have ⟨hdq, heq, _⟩ := Auth.auth_dfrac_op_valid.mp <|
      RABase.valid_of_incExt
        (RABase.op_mono_ext (RABase.incExt_op_left ..) (RABase.incExt_op_left ..)) h
    exact ⟨hdq, heq⟩
  · rintro ⟨hdq, rfl⟩
    exact auth_dfrac_op dq1 dq2 n1 ▸ (auth_dfrac_valid _ n1).mpr hdq

@[rocq_alias mono_nat_auth_op_valid]
theorem auth_op_valid (n1 n2 : MaxNat) :
  (✓ ((●MN n1) • (●MN n2) : MonoNat)) ↔ False :=
  (auth_dfrac_op_valid ..).trans
    ⟨fun ⟨h, _⟩ => DFrac.own_whole_exclusive.exclusive0_l _ h.validN, False.elim⟩

@[rocq_alias mono_nat_both_dfrac_valid]
theorem both_dfrac_valid (dq : DFrac) (n m : MaxNat) :
  (✓ ((●MN{dq} n) • (◯MN m) : MonoNat)) ↔ ✓ dq ∧ m ≤ n := by
  unfold auth lb
  rw [CMRA.assoc'.symm, ← Auth.frag_op, Auth.both_dfrac_valid_discrete, MaxNat.inc_iff]
  exact ⟨fun ⟨hdq, hle, _⟩ => ⟨hdq, by grind⟩, fun ⟨hdq, hle⟩ => ⟨hdq, by grind, trivial⟩⟩

@[rocq_alias mono_nat_both_valid]
theorem both_valid (n m : MaxNat) :
  (✓ ((●MN n) • (◯MN m) : MonoNat)) ↔ m ≤ n :=
  (both_dfrac_valid ..).trans ⟨And.right, fun h => ⟨DFrac.valid_own_one, h⟩⟩

@[rocq_alias mono_nat_lb_mono]
theorem lb_mono (n1 n2 : MaxNat) (h : n1 ≤ n2) :
  (◯MN n1 : MonoNat) ≼ₑ ◯MN n2 :=
  Auth.frag_incExt_of_incExt (MaxNat.inc_iff.mpr h)

@[rocq_alias mono_nat_included]
theorem included (dq : DFrac) (n : MaxNat) :
  (◯MN n : MonoNat) ≼ₑ ●MN{dq} n :=
  RABase.incExt_op_right ..

@[rocq_alias mono_nat_update]
theorem update {n : MaxNat} (n' : MaxNat) (h : n ≤ n') :
  (●MN n : MonoNat) ~~> ●MN n' := by
  unfold auth
  exact Auth.auth_update_of_localUpdate (fun h => h) (MaxNat.local_update h)

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
  is_op := by rw [h.is_op]; exact auth_dfrac_op ..

@[rocq_alias mono_nat_lb_max_is_op]
instance {n n1 n2 : MaxNat}
    [h : IsOp d n n1 n2] :
    IsOp d (◯MN n : MonoNat) (◯MN n1) (◯MN n2) where
  is_op := by rw [h.is_op]; exact rfl

end MonoNat

end Iris
