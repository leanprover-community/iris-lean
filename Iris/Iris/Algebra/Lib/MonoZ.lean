/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.Algebra.Auth
public import Iris.Algebra.LocalUpdates
public import Iris.Algebra.Numbers
meta import Iris.Std.RocqPorting

@[expose] public section

/-!
# Authoritative CMRA over `MaxZ`
-/

namespace Iris

@[rocq_alias mono_Z]
abbrev MonoZ := Auth (Option MaxZ)

#rocq_ignore mono_ZR "Use the MonoZ type and View.instCMRA typeclass"
#rocq_ignore mono_ZUR "Use the MonoZ type and View.instUCMRA typeclass"

namespace MonoZ

@[rocq_alias mono_Z_auth]
def auth (dq : DFrac) (n : MaxZ) : MonoZ := (●{dq} some n) • (◯ some n)
@[rocq_alias mono_Z_lb]
def lb (n : MaxZ) : MonoZ := ◯ some n

notation "●MZ{" dq "} " n => auth dq n
notation "●MZ " n => auth (DFrac.own 1) n
notation "●MZ□ " n => auth DFrac.discard n
notation "◯MZ " n => lb n

@[rocq_alias mono_Z_lb_core_id]
instance {n : MaxZ} : CMRA.CoreId (◯MZ n : MonoZ) := by
  unfold lb
  infer_instance

@[rocq_alias mono_Z_auth_core_id]
instance {l : MaxZ} : CMRA.CoreId (●MZ□ l : MonoZ) := by
  unfold auth
  infer_instance

@[rocq_alias mono_Z_auth_dfrac_op]
theorem auth_dfrac_op (dq1 dq2 : DFrac) (n : MaxZ) :
    (●MZ{dq1 • dq2} n : MonoZ) = (●MZ{dq1} n) • (●MZ{dq2} n) := by
  unfold auth
  rw [← CMRA.assoc', CMRA.op_core_right_of_inc (CMRA.inc_op_right ..), CMRA.assoc',
    ← Auth.auth_dfrac_op]

@[rocq_alias mono_Z_lb_op]
theorem lb_op (n1 n2 : MaxZ) : (◯MZ (n1 + n2) : MonoZ) = ((◯MZ n1) • (◯MZ n2) : MonoZ) :=
  Auth.frag_op (b1 := some n1) (b2 := some n2)

@[rocq_alias mono_Z_auth_lb_op]
theorem auth_lb_op (dq : DFrac) (n : MaxZ) : (●MZ{dq} n : MonoZ) = (●MZ{dq} n) • (◯MZ n) :=
  (CMRA.op_core_left_of_inc (CMRA.inc_op_right ..)).symm

@[rocq_alias mono_Z_lb_op_le_l]
theorem lb_op_le_l (n n' : MaxZ) (h : n' ≤ n) :
    (◯MZ n : MonoZ) = ((◯MZ n') • (◯MZ n) : MonoZ) :=
  (congrArg lb (by grind)).trans (lb_op n' n)

@[rocq_alias mono_Z_auth_dfrac_valid]
theorem auth_dfrac_valid (dq : DFrac) (n : MaxZ) : (✓ (●MZ{dq} n : MonoZ)) ↔ ✓ dq :=
  Auth.both_dfrac_valid_discrete.trans ⟨And.left, fun h => ⟨h, CMRA.inc_refl _, trivial⟩⟩

@[rocq_alias mono_Z_auth_valid]
theorem auth_valid (n : MaxZ) : ✓ (●MZ n : MonoZ) :=
  auth_dfrac_valid _ _ |>.mpr DFrac.valid_own_one

@[rocq_alias mono_Z_auth_dfrac_op_valid]
theorem auth_dfrac_op_valid (dq1 dq2 : DFrac) (n1 n2 : MaxZ) :
    (✓ ((●MZ{dq1} n1) • (●MZ{dq2} n2) : MonoZ)) ↔ ✓ (dq1 • dq2) ∧ n1 = n2 := by
  constructor
  · intro h
    unfold auth at h
    have ⟨hdq, heq, _⟩ := Auth.auth_dfrac_op_valid.mp <|
      CMRA.valid_of_inc (CMRA.op_mono (CMRA.inc_op_left ..) (CMRA.inc_op_left ..)) h
    exact ⟨hdq, Option.some_inj.mp heq⟩
  · rintro ⟨hdq, rfl⟩
    exact auth_dfrac_op dq1 dq2 n1 ▸ (auth_dfrac_valid _ n1).mpr hdq

@[rocq_alias mono_Z_auth_op_valid]
theorem auth_op_valid (n1 n2 : MaxZ) : (✓ ((●MZ n1) • (●MZ n2) : MonoZ)) ↔ False :=
  (auth_dfrac_op_valid ..).trans
    ⟨fun ⟨h, _⟩ => DFrac.own_whole_exclusive.exclusive0_l _ h.validN, False.elim⟩

@[rocq_alias mono_Z_both_dfrac_valid]
theorem both_dfrac_valid (dq : DFrac) (n m : MaxZ) :
    (✓ ((●MZ{dq} n) • (◯MZ m) : MonoZ)) ↔ ✓ dq ∧ m ≤ n := by
  unfold auth lb
  rw [CMRA.assoc'.symm, ← Auth.frag_op, Auth.both_dfrac_valid_discrete, ← Option.some_op,
    Option.some_inc_some_iff_is_total, MaxZ.inc_iff]
  exact ⟨fun ⟨hdq, hle, _⟩ => ⟨hdq, by grind⟩, fun ⟨hdq, hle⟩ => ⟨hdq, by grind, trivial⟩⟩

@[rocq_alias mono_Z_both_valid]
theorem both_valid (n m : MaxZ) : (✓ ((●MZ n) • (◯MZ m) : MonoZ)) ↔ m ≤ n :=
  (both_dfrac_valid ..).trans ⟨And.right, fun h => ⟨DFrac.valid_own_one, h⟩⟩

@[rocq_alias mono_Z_lb_mono]
theorem lb_mono (n1 n2 : MaxZ) (h : n1 ≤ n2) : (◯MZ n1 : MonoZ) ≼ ◯MZ n2 :=
  Auth.frag_inc_of_inc <| Option.some_inc_some_iff_is_total.mpr <| MaxZ.inc_iff.mpr h

@[rocq_alias mono_Z_included]
theorem included (dq : DFrac) (n : MaxZ) : (◯MZ n : MonoZ) ≼ ●MZ{dq} n :=
  CMRA.inc_op_right ..

@[rocq_alias mono_Z_update]
theorem update {n : MaxZ} (n' : MaxZ) (h : n ≤ n') : (●MZ n : MonoZ) ~~> ●MZ n' :=
  Auth.auth_update (LocalUpdate.option (MaxZ.local_update h))

@[rocq_alias mono_Z_auth_persist]
theorem auth_persist (n : MaxZ) (dq : DFrac) : (●MZ{dq} n : MonoZ) ~~> ●MZ□ n :=
  Update.op Auth.auth_update_auth_persist fun _ _ h => h

@[rocq_alias mono_Z_auth_unpersist]
theorem auth_unpersist (n : MaxZ) :
    (●MZ□ n : MonoZ) ~~>: (fun k => ∃ q, k = ●MZ{DFrac.own q} n) :=
  Auth.auth_updateP_both_unpersist

set_option synthInstance.checkSynthOrder false in
@[rocq_alias mono_Z_auth_dfrac_is_op]
instance {dq dq1 dq2 : DFrac} {n : MaxZ} [h : IsOp d dq dq1 dq2] :
    IsOp d (●MZ{dq} n) (●MZ{dq1} n) (●MZ{dq2} n) where
  is_op := by rw [h.is_op]; exact auth_dfrac_op ..

@[rocq_alias mono_Z_lb_max_is_op]
instance {n n1 n2 : MaxZ} [h : IsOp d n n1 n2] :
    IsOp d (◯MZ n : MonoZ) (◯MZ n1) (◯MZ n2) where
  is_op := by rw [h.is_op]; exact rfl

end MonoZ

end Iris
