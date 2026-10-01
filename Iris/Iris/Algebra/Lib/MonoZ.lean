/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.Auth
public import Iris.Algebra.LocalUpdates
public import Iris.Algebra.Numbers

@[expose] public section

/-!
# Authoritative ORA over `MaxInt`
-/

namespace Iris

@[rocq_alias mono_Z]
abbrev MonoZ := Auth (Option MaxInt)

#rocq_ignore mono_ZR "Use the MonoZ type and View.instCMRA typeclass"
#rocq_ignore mono_ZUR "Use the MonoZ type and View.instUCMRA typeclass"

namespace MonoZ

@[rocq_alias mono_Z_auth]
def auth (dq : DFrac) (n : MaxInt) : MonoZ := (●{dq} some n) • (◯ some n)
@[rocq_alias mono_Z_lb]
def lb (n : MaxInt) : MonoZ := ◯ some n

notation "●MZ{" dq "} " n => auth dq n
notation "●MZ " n => auth (DFrac.own 1) n
notation "●MZ□ " n => auth DFrac.discard n
notation "◯MZ " n => lb n

@[rocq_alias mono_Z_lb_core_id]
instance {n : MaxInt} : ORA.CoreId (◯MZ n : MonoZ) := by
  unfold lb
  infer_instance

@[rocq_alias mono_Z_auth_core_id]
instance {l : MaxInt} : ORA.CoreId (●MZ□ l : MonoZ) := by
  unfold auth
  infer_instance

@[rocq_alias mono_Z_auth_dfrac_op]
theorem auth_dfrac_op (dq1 dq2 : DFrac) (n : MaxInt) :
    (●MZ{dq1 • dq2} n : MonoZ) = (●MZ{dq1} n) • (●MZ{dq2} n) := by
  unfold auth
  rw [← ORA.assoc', ORA.op_core_right_of_inc (ORA.inc_op_right ..), ORA.assoc',
    ← Auth.auth_dfrac_op]

@[rocq_alias mono_Z_lb_op]
theorem lb_op (n1 n2 : MaxInt) : (◯MZ (n1 + n2) : MonoZ) = ((◯MZ n1) • (◯MZ n2) : MonoZ) :=
  Auth.frag_op (b1 := some n1) (b2 := some n2)

@[rocq_alias mono_Z_auth_lb_op]
theorem auth_lb_op (dq : DFrac) (n : MaxInt) : (●MZ{dq} n : MonoZ) = (●MZ{dq} n) • (◯MZ n) :=
  (ORA.op_core_left_of_inc (ORA.inc_op_right ..)).symm

@[rocq_alias mono_Z_lb_op_le_l]
theorem lb_op_le_l (n n' : MaxInt) (h : n' ≤ n) :
    (◯MZ n : MonoZ) = ((◯MZ n') • (◯MZ n) : MonoZ) :=
  (congrArg lb (by grind)).trans (lb_op n' n)

@[rocq_alias mono_Z_auth_dfrac_valid]
theorem auth_dfrac_valid (dq : DFrac) (n : MaxInt) : (✓ (●MZ{dq} n : MonoZ)) ↔ ✓ dq :=
  Auth.both_dfrac_valid_discrete_ord.trans ⟨And.left, fun h => ⟨h, ORA.ord_refl _, trivial⟩⟩

@[rocq_alias mono_Z_auth_valid]
theorem auth_valid (n : MaxInt) : ✓ (●MZ n : MonoZ) :=
  auth_dfrac_valid _ _ |>.mpr DFrac.valid_own_one

@[rocq_alias mono_Z_auth_dfrac_op_valid]
theorem auth_dfrac_op_valid (dq1 dq2 : DFrac) (n1 n2 : MaxInt) :
    (✓ ((●MZ{dq1} n1) • (●MZ{dq2} n2) : MonoZ)) ↔ ✓ (dq1 • dq2) ∧ n1 = n2 := by
  constructor
  · intro h
    unfold auth at h
    have ⟨hdq, heq, _⟩ := Auth.auth_dfrac_op_valid.mp <|
      ORA.valid_of_inc
        (ORA.op_mono_ext (ORA.inc_op_left ..) (ORA.inc_op_left ..)) h
    exact ⟨hdq, Option.some_inj.mp heq⟩
  · rintro ⟨hdq, rfl⟩
    exact auth_dfrac_op dq1 dq2 n1 ▸ (auth_dfrac_valid _ n1).mpr hdq

@[rocq_alias mono_Z_auth_op_valid]
theorem auth_op_valid (n1 n2 : MaxInt) : (✓ ((●MZ n1) • (●MZ n2) : MonoZ)) ↔ False :=
  (auth_dfrac_op_valid ..).trans
    ⟨fun ⟨h, _⟩ => DFrac.own_whole_exclusive.exclusive0_l _ h.validN, False.elim⟩

@[rocq_alias mono_Z_both_dfrac_valid]
theorem both_dfrac_valid (dq : DFrac) (n m : MaxInt) :
    (✓ ((●MZ{dq} n) • (◯MZ m) : MonoZ)) ↔ ✓ dq ∧ m ≤ n := by
  unfold auth lb
  rw [ORA.assoc'.symm, ← Auth.frag_op, Auth.both_dfrac_valid_discrete_ord, ← Option.some_op,
    Option.some_ord_some_iff_ordRefl, MaxInt.ord_iff]
  exact ⟨fun ⟨hdq, hle, _⟩ => ⟨hdq, by grind⟩, fun ⟨hdq, hle⟩ => ⟨hdq, by grind, trivial⟩⟩

@[rocq_alias mono_Z_both_valid]
theorem both_valid (n m : MaxInt) : (✓ ((●MZ n) • (◯MZ m) : MonoZ)) ↔ m ≤ n :=
  (both_dfrac_valid ..).trans ⟨And.right, fun h => ⟨DFrac.valid_own_one, h⟩⟩

theorem lb_mono_ord (n1 n2 : MaxInt) (h : n1 ≤ n2) : (◯MZ n1 : MonoZ) ≼ₒ ◯MZ n2 :=
  Auth.frag_ord_of_ord <| Option.some_ord_some_of_ord <| MaxInt.ord_iff.mpr h

@[rocq_alias mono_Z_lb_mono]
theorem lb_mono (n1 n2 : MaxInt) (h : n1 ≤ n2) : (◯MZ n1 : MonoZ) ≼ ◯MZ n2 :=
  inc_iff_ord.mpr (lb_mono_ord n1 n2 h)

theorem ord (dq : DFrac) (n : MaxInt) : (◯MZ n : MonoZ) ≼ₒ ●MZ{dq} n :=
  ORA.ord_op_right ..

@[rocq_alias mono_Z_included]
theorem included (dq : DFrac) (n : MaxInt) : (◯MZ n : MonoZ) ≼ ●MZ{dq} n :=
  inc_iff_ord.mpr (ord dq n)

@[rocq_alias mono_Z_update]
theorem update {n : MaxInt} (n' : MaxInt) (h : n ≤ n') : (●MZ n : MonoZ) ~~> ●MZ n' :=
  Auth.auth_update
    (LocalUpdate.option (MaxInt.local_update h))

@[rocq_alias mono_Z_auth_persist]
theorem auth_persist (n : MaxInt) (dq : DFrac) : (●MZ{dq} n : MonoZ) ~~> ●MZ□ n :=
  Update.op Auth.auth_update_auth_persist fun _ _ h => h

@[rocq_alias mono_Z_auth_unpersist]
theorem auth_unpersist (n : MaxInt) :
    (●MZ□ n : MonoZ) ~~>: (fun k => ∃ q, k = ●MZ{DFrac.own q} n) :=
  Auth.auth_updateP_both_unpersist

set_option synthInstance.checkSynthOrder false in
@[rocq_alias mono_Z_auth_dfrac_is_op]
instance {dq dq1 dq2 : DFrac} {n : MaxInt} [h : IsOp d dq dq1 dq2] :
    IsOp d (●MZ{dq} n) (●MZ{dq1} n) (●MZ{dq2} n) where
  is_op := by rw [h.is_op]; exact auth_dfrac_op ..

@[rocq_alias mono_Z_lb_max_is_op]
instance {n n1 n2 : MaxInt} [h : IsOp d n n1 n2] :
    IsOp d (◯MZ n : MonoZ) (◯MZ n1) (◯MZ n2) where
  is_op := by rw [h.is_op]; exact rfl

end MonoZ

end Iris
