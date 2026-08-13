/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.Auth
public import Iris.Algebra.MaxPrefixList
import Iris.Std.RocqPorting

/-! # Monotone lists -/

@[expose] public section

namespace Iris

open OFE CMRA

variable {α : Type _} [OFE α]

@[rocq_alias mono_listR, rocq_alias mono_listUR]
def MonoList (α : Type _) [OFE α] := Auth (MaxPrefixList α)

instance : OFE (MonoList α) :=
  Auth.instOFE

instance : CMRA (MonoList α) :=
  Auth.instCMRA

instance : UCMRA (MonoList α) :=
  Auth.instUCMRA

instance instDiscrete [OFE.Discrete α] : CMRA.Discrete (MonoList α) := by
  unfold MonoList
  infer_instance

namespace MonoList

open MaxPrefixList

@[rocq_alias mono_list_auth]
def auth (dq : DFrac) (l : List α) : MonoList α :=
  (●{dq} toMaxPrefixList l) • ◯ toMaxPrefixList l

@[rocq_alias mono_list_lb]
def lb (l : List α) : MonoList α := ◯ toMaxPrefixList l

notation:max "●ML{" dq "} " l:max => auth dq l
notation:max "●ML " l:max => auth (DFrac.own 1) l
notation:max "●ML□ " l:max => auth DFrac.discard l
notation:max "◯ML " l:max => lb l

/-- Exchange the two inner factors of a product of products. -/
theorem op_op_op_comm (x y z w : MonoList α) : (x • y) • (z • w) = (x • z) • (y • w) :=
  Algebra.MonoidOps.op_op_op_comm

/-! ## Setoid properties -/

@[rocq_alias mono_list_auth_ne]
instance auth_ne {dq : DFrac} : NonExpansive (auth dq : List α → MonoList α) where
  ne _ _ _ h :=
    (Auth.auth_ne.ne (toMaxPrefixList_ne.ne h)).op (Auth.frag_ne.ne (toMaxPrefixList_ne.ne h))

@[rocq_alias mono_list_lb_ne]
instance lb_ne : NonExpansive (lb : List α → MonoList α) where
  ne _ _ _ h := Auth.frag_ne.ne (toMaxPrefixList_ne.ne h)

#rocq_ignore mono_list_auth_proper "OFE is Leibniz; use equality"
#rocq_ignore mono_list_lb_proper "OFE is Leibniz; use equality"

@[rocq_alias mono_list_lb_dist_inj]
theorem lb_dist_inj {n} {l1 l2 : List α} (h : ◯ML l1 ≡{n}≡ ◯ML l2) : l1 ≡{n}≡ l2 :=
  toMaxPrefixList_dist_inj (Auth.frag_dist_inj h)

@[rocq_alias mono_list_lb_inj]
theorem lb_inj {l1 l2 : List α} (h : ◯ML l1 = ◯ML l2) : l1 = l2 :=
  toMaxPrefixList_inj (Auth.frag_inj h)

/-! ## Operation -/

@[rocq_alias mono_list_lb_core_id]
instance {l : List α} : CoreId (◯ML l) := by
  unfold lb MonoList
  infer_instance

@[rocq_alias mono_list_auth_core_id]
instance {l : List α} : CoreId (●ML□ l) := by
  unfold auth MonoList
  infer_instance

theorem lb_nil : ◯ML ([] : List α) = UCMRA.unit := by
  unfold lb MonoList
  rw [toMaxPrefixList_nil]
  rfl

instance : IsUnit (◯ML ([] : List α)) := by
  rw [lb_nil]
  infer_instance

@[rocq_alias mono_list_auth_dfrac_op]
theorem auth_dfrac_op (dq1 dq2 : DFrac) (l : List α) :
    ●ML{dq1 • dq2} l = ●ML{dq1} l • ●ML{dq2} l := by
  unfold auth MonoList
  rw [Algebra.MonoidOps.op_op_op_comm (M := Auth (MaxPrefixList α)) (op := (· • ·)),
    ← Auth.frag_op, op_self, Auth.auth_dfrac_op]

@[rocq_alias mono_list_lb_op_l]
theorem lb_op_left {l1 l2 : List α} (h : l1 <+: l2) : ◯ML l1 • ◯ML l2 = ◯ML l2 := by
  unfold lb MonoList
  rw [← Auth.frag_op, toMaxPrefixList_op_left h]

@[rocq_alias mono_list_lb_op_r]
theorem lb_op_right {l1 l2 : List α} (h : l1 <+: l2) : ◯ML l2 • ◯ML l1 = ◯ML l2 := by
  unfold lb MonoList
  rw [← Auth.frag_op, toMaxPrefixList_op_right h]

@[rocq_alias mono_list_auth_lb_op]
theorem auth_lb_op (dq : DFrac) (l : List α) : ●ML{dq} l = ●ML{dq} l • ◯ML l := by
  unfold auth lb MonoList
  rw [← assoc', ← Auth.frag_op, op_self]

set_option synthInstance.checkSynthOrder false in
@[rocq_alias mono_list_auth_dfrac_is_op]
instance {dq dq1 dq2 : DFrac} {l : List α} [h : IsOp d dq dq1 dq2] :
    IsOp d (●ML{dq} l) (●ML{dq1} l) (●ML{dq2} l) where
  is_op := by
    rw [h.is_op]
    exact auth_dfrac_op ..

/-! ## Validity -/

@[rocq_alias mono_list_auth_dfrac_validN]
theorem auth_dfrac_validN {n} (dq : DFrac) (l : List α) : ✓{n} (●ML{dq} l) ↔ ✓ dq := by
  unfold auth MonoList
  rw [Auth.both_dfrac_validN]
  exact ⟨fun h => h.1, fun h => ⟨h, incN_refl _, toMaxPrefixList_validN _⟩⟩

@[rocq_alias mono_list_auth_validN]
theorem auth_validN {n} (l : List α) : ✓{n} (●ML l) :=
  (auth_dfrac_validN ..).mpr DFrac.valid_own_one

@[rocq_alias mono_list_auth_dfrac_valid]
theorem auth_dfrac_valid (dq : DFrac) (l : List α) : ✓ (●ML{dq} l) ↔ ✓ dq := by
  unfold auth MonoList
  rw [Auth.both_dfrac_valid]
  exact ⟨fun h => h.1, fun h => ⟨h, fun _ => incN_refl _, toMaxPrefixList_valid _⟩⟩

@[rocq_alias mono_list_auth_valid]
theorem auth_valid (l : List α) : ✓ (●ML l) :=
  (auth_dfrac_valid ..).mpr DFrac.valid_own_one

@[rocq_alias mono_list_auth_dfrac_op_validN]
theorem auth_dfrac_op_validN {n} (dq1 dq2 : DFrac) (l1 l2 : List α) :
    ✓{n} (●ML{dq1} l1 • ●ML{dq2} l2) ↔ ✓ (dq1 • dq2) ∧ l1 ≡{n}≡ l2 := by
  refine ⟨fun h => ?_, fun ⟨hdq, hl⟩ => ?_⟩
  · unfold auth MonoList at h
    rw [Algebra.MonoidOps.op_op_op_comm (M := Auth (MaxPrefixList α)) (op := (· • ·))] at h
    have ⟨hdq, ha, _⟩ := Auth.auth_dfrac_op_validN.mp (validN_op_left h)
    exact ⟨hdq, toMaxPrefixList_dist_inj ha⟩
  · refine (Dist.validN (auth_ne.ne hl.symm).op_r).mpr ?_
    rw [← auth_dfrac_op]
    exact (auth_dfrac_validN ..).mpr hdq

@[rocq_alias mono_list_auth_op_validN]
theorem auth_op_validN {n} (l1 l2 : List α) : ✓{n} (●ML l1 • ●ML l2) ↔ False := by
  refine (auth_dfrac_op_validN ..).trans ⟨fun ⟨h, _⟩ => ?_, False.elim⟩
  exact DFrac.own_whole_exclusive.exclusive0_l _ h.validN

@[rocq_alias mono_list_auth_dfrac_op_valid]
theorem auth_dfrac_op_valid (dq1 dq2 : DFrac) (l1 l2 : List α) :
    ✓ (●ML{dq1} l1 • ●ML{dq2} l2) ↔ ✓ (dq1 • dq2) ∧ l1 = l2 := by
  simp only [valid_iff_validN, eq_dist, auth_dfrac_op_validN]
  exact ⟨fun h => ⟨(h 0).1, fun n => (h n).2⟩, fun ⟨hdq, hl⟩ n => ⟨hdq, hl n⟩⟩

@[rocq_alias mono_list_auth_op_valid]
theorem auth_op_valid (l1 l2 : List α) : ✓ (●ML l1 • ●ML l2) ↔ False := by
  refine (auth_dfrac_op_valid ..).trans ⟨fun ⟨h, _⟩ => ?_, False.elim⟩
  exact DFrac.own_whole_exclusive.exclusive0_l _ h.validN

#rocq_ignore mono_list_auth_dfrac_op_valid_L "OFE is Leibniz; use auth_dfrac_op_valid"

@[rocq_alias mono_list_both_dfrac_validN]
theorem both_dfrac_validN {n} (dq : DFrac) (l1 l2 : List α) :
    ✓{n} (●ML{dq} l1 • ◯ML l2) ↔ ✓ dq ∧ ∃ l, l1 ≡{n}≡ l2 ++ l := by
  unfold auth lb MonoList
  rw [← assoc', ← Auth.frag_op, Auth.both_dfrac_validN]
  refine ⟨fun ⟨hdq, hinc, _⟩ => ⟨hdq, ?_⟩, fun ⟨hdq, hl⟩ => ⟨hdq, ?_, ?_⟩⟩
  · exact toMaxPrefixList_incN_iff.mp (incN_trans (incN_op_right ..) hinc)
  · have hinc := op_monoN_right (toMaxPrefixList l1) (toMaxPrefixList_incN_iff.mpr hl)
    rwa [op_self] at hinc
  · exact toMaxPrefixList_validN _

@[rocq_alias mono_list_both_validN]
theorem both_validN {n} (l1 l2 : List α) :
    ✓{n} (●ML l1 • ◯ML l2) ↔ ∃ l, l1 ≡{n}≡ l2 ++ l := by
  rw [both_dfrac_validN]
  exact ⟨fun h => h.2, fun h => ⟨DFrac.valid_own_one, h⟩⟩

@[rocq_alias mono_list_both_dfrac_valid]
theorem both_dfrac_valid (dq : DFrac) (l1 l2 : List α) :
    ✓ (●ML{dq} l1 • ◯ML l2) ↔ ✓ dq ∧ l2 <+: l1 := by
  unfold auth lb MonoList
  rw [← assoc', ← Auth.frag_op, Auth.both_dfrac_valid, ← inc_iff_forall_incN]
  refine ⟨fun ⟨hdq, hinc, _⟩ => ⟨hdq, ?_⟩, fun ⟨hdq, hl⟩ => ⟨hdq, ?_, ?_⟩⟩
  · exact toMaxPrefixList_inc_iff.mp (inc_trans (inc_op_right ..) hinc)
  · have hinc := op_mono_right (toMaxPrefixList l1) (toMaxPrefixList_inc_iff.mpr hl)
    rwa [op_self] at hinc
  · exact toMaxPrefixList_valid _

#rocq_ignore mono_list_both_dfrac_valid_L "Use both_dfrac_valid"

@[rocq_alias mono_list_both_valid]
theorem both_valid (l1 l2 : List α) : ✓ (●ML l1 • ◯ML l2) ↔ l2 <+: l1 := by
  rw [both_dfrac_valid]
  exact ⟨fun h => h.2, fun h => ⟨DFrac.valid_own_one, h⟩⟩

#rocq_ignore mono_list_both_valid_L "Use both_valid"

@[rocq_alias mono_list_lb_op_validN]
theorem lb_op_validN {n} (l1 l2 : List α) :
    ✓{n} (◯ML l1 • ◯ML l2) ↔ (∃ l, l2 ≡{n}≡ l1 ++ l) ∨ (∃ l, l1 ≡{n}≡ l2 ++ l) := by
  unfold lb MonoList
  rw [Auth.frag_op_validN, toMaxPrefixList_op_validN]

@[rocq_alias mono_list_lb_op_valid]
theorem lb_op_valid (l1 l2 : List α) :
    ✓ (◯ML l1 • ◯ML l2) ↔ l1 <+: l2 ∨ l2 <+: l1 := by
  unfold lb MonoList
  rw [Auth.frag_op_valid, toMaxPrefixList_op_valid]

#rocq_ignore mono_list_lb_op_valid_L "Use lb_op_valid"
#rocq_ignore mono_list_lb_op_valid_1_L "Use lb_op_valid.mp"
#rocq_ignore mono_list_lb_op_valid_2_L "Use lb_op_valid.mpr"

@[rocq_alias mono_list_lb_mono]
theorem lb_mono {l1 l2 : List α} (h : l1 <+: l2) : ◯ML l1 ≼ ◯ML l2 :=
  ⟨◯ML l2, (lb_op_left h).symm⟩

@[rocq_alias mono_list_included]
theorem included (dq : DFrac) (l : List α) : ◯ML l ≼ ●ML{dq} l := inc_op_right ..

/-! ## Updates -/

@[rocq_alias mono_list_update]
theorem update {l1 : List α} (l2 : List α) (h : l1 <+: l2) : ●ML l1 ~~> ●ML l2 :=
  Auth.auth_update (local_update h)

@[rocq_alias mono_list_auth_persist]
theorem auth_persist (dq : DFrac) (l : List α) : ●ML{dq} l ~~> ●ML□ l :=
  Update.op Auth.auth_update_auth_persist fun _ _ h => h

@[rocq_alias mono_list_auth_unpersist]
theorem auth_unpersist (l : List α) : ●ML□ l ~~>: fun k => ∃ q, k = ●ML{DFrac.own q} l :=
  Auth.auth_updateP_both_unpersist

end MonoList

/-! ## Functors -/

@[rocq_alias mono_listURF]
abbrev MonoListURF (F : COFE.OFunctorPre) [COFE.OFunctor F] : COFE.OFunctorPre :=
  Auth.AuthURF (MaxPrefixListURF F)

#rocq_ignore mono_listURF_contractive "Found by typeclass inference"

@[rocq_alias mono_listRF]
abbrev MonoListRF (F : COFE.OFunctorPre) [COFE.OFunctor F] : COFE.OFunctorPre :=
  Auth.AuthRF (MaxPrefixListURF F)

#rocq_ignore mono_listRF_contractive "Found by typeclass inference"

end Iris
