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

The authoritative element is a monotonically increasing `Int`, while a fragment is a lower
bound. Unlike `MaxNat`, `MaxZ` has no unit, so the underlying UCMRA is `Option MaxZ`.
-/

namespace Iris

open _root_.Std (Associative Commutative IdempotentOp)

section MaxZ

@[grind cases]
structure MaxZ where
  ofInt ::
  toInt : Int

@[grind]
def MaxZ.max (a b : MaxZ) : MaxZ where
  toInt := Max.max a.toInt b.toInt

scoped instance : Add MaxZ where add := .max
scoped instance : LE MaxZ where le a b := a.toInt ≤ b.toInt

@[simp, grind =]
theorem MaxZ.le_toInt (a b : MaxZ) : a ≤ b ↔ a.toInt ≤ b.toInt := by rfl

@[simp, grind =]
theorem MaxZ.toInt_add (a b : MaxZ) : (a + b).toInt = Max.max a.toInt b.toInt := rfl

@[simp, grind =]
theorem MaxZ.add_ofInt (a b : Int) : (MaxZ.ofInt a + MaxZ.ofInt b) = MaxZ.ofInt (Max.max a b) := rfl

theorem MaxZ.eq_toInt (a b : MaxZ) : a = b ↔ a.toInt = b.toInt := by
  constructor
  · rintro rfl; rfl
  · cases a; cases b; rintro rfl; rfl

scoped instance : Associative (α := MaxZ) (· + ·) where
  assoc := by grind
scoped instance : Commutative (α := MaxZ) (· + ·) where
  comm := by grind
scoped instance : IdempotentOp (α := MaxZ) (· + ·) where
  idempotent x := by grind
scoped instance : COFE MaxZ := COFE.ofDiscrete _
scoped instance : OFE.Discrete MaxZ := ⟨fun h => h⟩
scoped instance : CMRA MaxZ := OrdCommMonoidLike.instCMRA
scoped instance : CMRA.Discrete MaxZ := OrdCommMonoidLike.instDiscrete
scoped instance : CMRA.IsTotal MaxZ := OrdCommMonoidLike.instIsTotal
scoped instance : CMRA.CoreId (a : MaxZ) := OrdCommMonoidLike.instCoreId _

end MaxZ

@[rocq_alias mono_Z]
abbrev MonoZ := Auth (Option MaxZ)

#rocq_ignore mono_ZR "Use the MonoZ type and View.instCMRA typeclass"
#rocq_ignore mono_ZUR "Use the MonoZ type and View.instUCMRA typeclass"

namespace MonoZ

/-- The authoritative element. The definition includes the fragment at the same value so that
`MonoZ.included` holds; without this trick a frame-preserving update lemma would be required
instead. -/
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
    (●MZ{dq1 • dq2} n : MonoZ) = (●MZ{dq1} n) • (●MZ{dq2} n) :=
  CMRA.comm'.trans <|
  (congrArg ((◯ some n) • ·) Auth.auth_dfrac_op).trans <|
  CMRA.comm'.trans <|
  CMRA.assoc'.symm.trans <|
  (congrArg ((●{dq1} some n) • ·) CMRA.comm').trans <|
  (congrArg ((●{dq1} some n) • ·)
    (congrArg (· • ●{dq2} some n) (CMRA.op_self (◯ some n)).symm)).trans <|
  (congrArg ((●{dq1} some n) • ·) CMRA.assoc'.symm).trans <|
  CMRA.assoc'.trans <|
  congrArg (((●{dq1} some n) • ◯ some n) • ·) CMRA.comm'

@[rocq_alias mono_Z_lb_op]
theorem lb_op (n1 n2 : MaxZ) : (◯MZ (n1 + n2) : MonoZ) = ((◯MZ n1) • (◯MZ n2) : MonoZ) :=
  Auth.frag_op (b1 := some n1) (b2 := some n2)

@[rocq_alias mono_Z_auth_lb_op]
theorem auth_lb_op (dq : DFrac) (n : MaxZ) : (●MZ{dq} n : MonoZ) = (●MZ{dq} n) • (◯MZ n) := by
  refine .trans ?_ CMRA.assoc'
  simp only [lb, ← Auth.frag_op]
  refine congrArg ((●{dq} some n) • ·) ?_
  simp [CMRA.op, Add.add, MaxZ.max]

/-- Rephrasing of `MonoZ.lb_op`, useful for weakening a fragment to a smaller lower bound. -/
@[rocq_alias mono_Z_lb_op_le_l]
theorem lb_op_le_l (n n' : MaxZ) (h : n' ≤ n) :
    (◯MZ n : MonoZ) = ((◯MZ n') • (◯MZ n) : MonoZ) := by
  rw [← lb_op]
  grind

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
    replace h := (CMRA.assoc'.symm.trans <|
      (congrArg (CMRA.op (●{dq1} some n1)) <|
        CMRA.assoc'.trans <|
          (congrArg (CMRA.op · (◯ some n2)) CMRA.comm').trans CMRA.assoc'.symm).trans
      CMRA.assoc') ▸ h
    have ⟨hdq, heq, _⟩ := Auth.auth_dfrac_op_valid.mp (CMRA.valid_op_left h)
    exact ⟨hdq, Option.some_inj.mp heq⟩
  · rintro ⟨hdq, rfl⟩
    exact auth_dfrac_op dq1 dq2 n1 ▸
      Auth.both_dfrac_valid_discrete.mpr ⟨hdq, CMRA.inc_refl (some n1), trivial⟩

@[rocq_alias mono_Z_auth_op_valid]
theorem auth_op_valid (n1 n2 : MaxZ) : (✓ ((●MZ n1) • (●MZ n2) : MonoZ)) ↔ False := by
  refine (auth_dfrac_op_valid _ _ n1 n2).trans ?_
  refine ⟨fun ⟨h, _⟩ => ?_, False.elim⟩
  exact DFrac.own_whole_exclusive |>.exclusive0_l _ h.validN

@[rocq_alias mono_Z_both_dfrac_valid]
theorem both_dfrac_valid (dq : DFrac) (n m : MaxZ) :
    (✓ ((●MZ{dq} n) • (◯MZ m) : MonoZ)) ↔ ✓ dq ∧ m ≤ n := by
  unfold auth lb
  rw [CMRA.assoc'.symm, ← Auth.frag_op, Auth.both_dfrac_valid_discrete, ← Option.some_op,
    Option.some_inc_some_iff_is_total]
  constructor
  · intro ⟨hdq, ⟨k, hk⟩, _⟩; refine ⟨hdq, ?_⟩
    simp only [CMRA.op, Add.add] at hk
    grind
  · intro ⟨hdq, hle⟩
    refine ⟨hdq, ⟨n, ?_⟩, trivial⟩
    dsimp only [CMRA.op, Add.add]
    grind

@[rocq_alias mono_Z_both_valid]
theorem both_valid (n m : MaxZ) : (✓ ((●MZ n) • (◯MZ m) : MonoZ)) ↔ m ≤ n := by
  rw [both_dfrac_valid]
  exact ⟨fun h => h.2, fun h => ⟨DFrac.valid_own_one, h⟩⟩

@[rocq_alias mono_Z_lb_mono]
theorem lb_mono (n1 n2 : MaxZ) (h : n1 ≤ n2) : (◯MZ n1 : MonoZ) ≼ ◯MZ n2 := by
  refine Auth.frag_inc_of_inc (Option.some_inc_some_iff_is_total.mpr ?_)
  exists n2
  simp only [CMRA.op, Add.add]
  grind

@[rocq_alias mono_Z_included]
theorem included (dq : DFrac) (n : MaxZ) : (◯MZ n : MonoZ) ≼ ●MZ{dq} n :=
  CMRA.inc_op_right _ _

@[rocq_alias mono_Z_update]
theorem update {n : MaxZ} (n' : MaxZ) (h : n ≤ n') : (●MZ n : MonoZ) ~~> ●MZ n' := by
  refine Auth.auth_update (LocalUpdate.option fun _ mz _ hn => ⟨trivial, ?_⟩)
  cases mz with | none => rfl | some z =>
  simp only [CMRA.op?, CMRA.op, Add.add] at hn ⊢
  refine OFE.Dist.of_eq ?_
  simp only [MaxZ.eq_toInt, MaxZ.max]
  refine Int.max_eq_left ?_ |>.symm
  refine Int.le_trans ?_ h
  refine hn ▸ ?_
  simp only [MaxZ.max]
  apply Int.le_max_right

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
