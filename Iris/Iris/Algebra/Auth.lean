/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bai, Janine Lohse
-/
module

public import Iris.Algebra.View
public import Iris.Algebra.LocalUpdates

/-!
# Authoritative Camera

The authoritative camera has 2 types of elements:
- the authoritative element `●{dq} a`
- the fragment `◯ b`
-/

@[expose] public section

variable {SI : Type _} [instSI : Iris.SIdx SI]

open Iris

open OFE ORA UORA View

/-!
## Definition of the view relation for the authoritative camera.
-/
@[rocq_alias auth_view_rel_raw]
def AuthViewRel [UORA SI A] : ViewRel SI A A := fun n a b => (∃ c, b • c ≼ₒ{n} a) ∧ ✓{n} a

def AuthViewRelInc [UORA SI A] : ViewRel SI A A := fun n a b => b ≼{n} a ∧ ✓{n} a

namespace AuthViewRel

variable [UORA SI A]

@[rocq_alias auth_view_rel]
instance instViewRel_authViewRel : IsViewRel (AuthViewRel (SI := SI) (A := A)) where
  mono := fun ⟨⟨c, hinc⟩, hv⟩ ha hb hn =>
    ⟨⟨c, calc _ ≼ₒ{_} _ := op_monoN_left_ord c hb
              _ ≼ₒ{_} _ := ordN_of_ordN_le hn hinc
              _ ≼ₒ{_} _ := ha.to_ordN⟩,
     validN_ne ha (validN_of_le hn hv)⟩
  op_left {_ _ _ d} := fun ⟨⟨c, hinc⟩, hv⟩ => ⟨⟨d • c, by rw [assoc']; exact hinc⟩, hv⟩
  rel_validN _ _ _ := fun ⟨⟨_, hinc⟩, hv⟩ => validN_op_left (validN_of_ordN hinc hv)
  rel_unit _ := ⟨unit, ⟨unit, by rw [unit_right_id]⟩, ORA.unit_valid.validN⟩

theorem of_inc {n : SI} {a b : A} : AuthViewRelInc n a b → AuthViewRel n a b
  | ⟨⟨c, hc⟩, hv⟩ => ⟨⟨c, ordN_of_dist hc.symm⟩, hv⟩

theorem iff_inc [OrdInc SI A] {n : SI} {a b : A} : AuthViewRel n a b ↔ AuthViewRelInc n a b :=
  and_congr_left fun _ => exists_op_ordN_iff_incN

#rocq_ignore auth_view_rel_raw_mono "Use the IsViewRel typeclass"
#rocq_ignore auth_view_rel_raw_valid "Use the IsViewRel typeclass"
#rocq_ignore auth_view_rel_raw_unit "Use the IsViewRel typeclass"

@[rocq_alias auth_view_rel_unit]
theorem authViewRel_unit_iff {n : SI} {a : A} : AuthViewRel n a unit ↔ ✓{n} a :=
  ⟨(·.2), (⟨⟨a, by rw [ucmra_unit_left_id]⟩, ·⟩)⟩

@[rocq_alias auth_view_rel_exists]
theorem authViewRel_exists_iff {n : SI} {b : A} : (∃ a, AuthViewRel n a b) ↔ ✓{n} b :=
  ⟨fun ⟨_, h⟩ => IsViewRel.rel_validN _ _ _ h, (⟨b, ⟨unit, by rw [unit_right_id]⟩, ·⟩)⟩

@[rocq_alias auth_view_rel_discrete]
instance [ORA.Discrete SI A] : IsViewRelDiscrete (AuthViewRel (SI := SI) (A := A)) where
  discrete _ _ _ := fun ⟨⟨c, h⟩, hv⟩ =>
    ⟨⟨c, ordN_of_ord _ (discrete_ord h)⟩, (discrete_valid hv).validN⟩

end AuthViewRel


/-! ## Definition and operations on the authoritative camera -/

abbrev Auth (A : Type _) [UORA SI A] :=
  View (AuthViewRel (SI := SI) (A := A))

namespace Auth
variable [UORA SI A]

instance : OFE SI (Auth (SI := SI) A) := View.instOFE
instance instORA : ORA SI (Auth (SI := SI) A) := View.instORA
instance instUCMRA : UORA SI (Auth (SI := SI) A) := View.instUCMRA

#rocq_ignore authO "Use the Auth type and View.instOFE typeclass"
#rocq_ignore authR "Use the Auth type and View.instORA typeclass"
#rocq_ignore authUR "Use the Auth type and View.instUCMRA typeclass"

#rocq_ignore auth_cmra_discrete "Inference succeeds automatically"
#rocq_ignore auth_ofe_discrete "Inference succeeds automatically"

@[rocq_alias auth_auth]
abbrev auth (dq : DFrac) (a : A) : Auth (SI := SI) A := View.Auth dq a

@[rocq_alias auth_frag]
abbrev frag (b : A) : Auth (SI := SI) A := Frag b

notation "●{" dq "} " a => auth dq a
notation "● " a => auth (DFrac.own 1) a
notation "◯ " b => frag b

@[rocq_alias auth_auth_ne]
nonrec instance auth_ne {dq : DFrac} : NonExpansive SI (auth dq : A → Auth (SI := SI) A) :=
  auth_ne

#rocq_ignore auth_auth_proper "Derivable from auth_ne with NonExpansive.eqv"

@[rocq_alias auth_frag_ne]
nonrec instance frag_ne : NonExpansive SI (frag (SI := SI) : A → Auth (SI := SI) A) :=
  frag_ne

#rocq_ignore auth_frag_proper "Derivable from frag_ne with NonExpansive.eqv"

@[rocq_alias auth_auth_dist_inj]
nonrec theorem auth_dist_inj {n : SI} {dq1 dq2 : DFrac} {a1 a2 : A}
    (h : (●{dq1} a1 : Auth (SI := SI) A) ≡{n}≡ ●{dq2} a2) : dq1 = dq2 ∧ a1 ≡{n}≡ a2 :=
  ⟨auth_inj_frac h, dist_of_auth_dist h⟩

@[rocq_alias auth_auth_inj]
theorem auth_inj {dq1 dq2 : DFrac} {a1 a2 : A} (h : (●{dq1} a1 : Auth (SI := SI) A) = ●{dq2} a2) :
    dq1 = dq2 ∧ a1 = a2 :=
  ⟨auth_inj_frac (n := 0) h.dist, OFE.eq_dist_2 fun _ => dist_of_auth_dist h.dist⟩

@[rocq_alias auth_frag_dist_inj]
theorem frag_dist_inj {n : SI} {b1 b2 : A} (h : (◯ b1 : Auth (SI := SI) A) ≡{n}≡ ◯ b2) : b1 ≡{n}≡ b2 :=
  dist_of_frag_dist h

@[rocq_alias auth_frag_inj]
theorem frag_inj {b1 b2 : A} (h : (◯ b1 : Auth (SI := SI) A) = ◯ b2) : b1 = b2 :=
  OFE.eq_dist_2 fun _ => dist_of_frag_dist h.dist

@[rocq_alias auth_auth_discrete]
nonrec instance auth_discrete {dq : DFrac} {a : A} [DiscreteE SI a] [DiscreteE SI (unit : A)] :
    DiscreteE SI (●{dq} a : Auth (SI := SI) A) := auth_discrete

@[rocq_alias auth_frag_discrete]
nonrec instance frag_discrete {a : A} [DiscreteE SI a] : DiscreteE SI (◯ a : Auth (SI := SI) A) :=
  frag_discrete

/-! ## Operations -/
@[rocq_alias auth_auth_dfrac_op]
nonrec theorem auth_dfrac_op {dq1 dq2 : DFrac} {a : A} :
    (●{dq1 • dq2} a : Auth (SI := SI) A) = (●{dq1} a) • (●{dq2} a) :=
  auth_op_auth_eqv

set_option synthInstance.checkSynthOrder false in
@[rocq_alias auth_auth_dfrac_is_op]
instance {dq dq1 dq2 : DFrac} {a : A} [h : IsOp SI d dq dq1 dq2] :
    IsOp SI d (●{dq} a : Auth (SI := SI) A) (●{dq1} a) (●{dq2} a) where
  is_op := by
    rw [h.is_op]
    apply auth_dfrac_op

@[rocq_alias auth_frag_op]
theorem frag_op {b1 b2 : A} : (◯ (b1 • b2) : Auth (SI := SI) A) = ((◯ b1 : Auth (SI := SI) A) • ◯ b2) :=
  frag_op_eq

nonrec theorem frag_ord_of_ord {b1 b2 : A} (h : b1 ≼ₒ[SI] b2) : (◯ b1 : Auth (SI := SI) A) ≼ₒ[SI] ◯ b2 :=
  frag_ord_of_ord h

@[rocq_alias auth_frag_mono]
nonrec theorem frag_inc_of_inc {b1 b2 : A} (h : b1 ≼ b2) : (◯ b1 : Auth (SI := SI) A) ≼ ◯ b2 :=
  frag_inc_of_inc h

@[rocq_alias auth_frag_core]
nonrec theorem frag_core {b : A} : core (◯ b : Auth (SI := SI) A) = ◯ (core b) :=
  frag_core

@[rocq_alias auth_both_core_discarded]
theorem auth_both_core_discarded :
    core ((●{.discard} a) • ◯ b : Auth (SI := SI) A) = (●{.discard} a) • ◯ (core b) :=
  auth_discard_op_frag_core

@[rocq_alias auth_both_core_frac]
theorem auth_both_core_frac {q : Qp} {a b : A} :
    core ((●{.own q} a) • ◯ b : Auth (SI := SI) A) = ◯ (core b) :=
  auth_own_op_frag_core

@[rocq_alias auth_auth_core_id]
nonrec instance {a : A} : CoreId (●{.discard} a : Auth (SI := SI) A) :=
  instCoreIdAuthDiscard

@[rocq_alias auth_frag_core_id]
nonrec instance {b : A} [CoreId b] : CoreId (◯ b : Auth (SI := SI) A) :=
  instCoreIdFrag

@[rocq_alias auth_both_core_id]
nonrec instance {a : A} {b : A} [CoreId b] :
    CoreId ((●{.discard} a : Auth (SI := SI) A) • ◯ b) :=
  instCoreIdOpAuthDiscardFrag

@[rocq_alias auth_frag_is_op]
instance {a b1 b2 : A} [h : IsOp SI d a b1 b2] :
    IsOp SI d (◯ a : Auth (SI := SI) A) (◯ b1) (◯ b2) where
  is_op := (congrArg frag h.is_op).trans frag_op

#rocq_ignore auth_frag_sep_homomorphism "Found by typeclass inference from the View.Frag instance"

section BigOp
open Algebra Std

@[rocq_alias big_opL_auth_frag]
theorem bigOpL_frag (g : Nat → C → A) (l : List C) :
    (◯ ([^ op list] k ↦ x ∈ l, g k x) : Auth (SI := SI) A) = [^ op list] k ↦ x ∈ l, ◯ (g k x) :=
  View.bigOpL_frag _ _

@[rocq_alias big_opM_auth_frag]
theorem bigOpM_frag [LawfulFiniteMap M' K] (g : K → C → A) (m : M' C) :
    (◯ ([^ op map] k ↦ x ∈ m, g k x) : Auth (SI := SI) A) = [^ op map] k ↦ x ∈ m, ◯ (g k x) :=
  View.bigOpM_frag _ _

@[rocq_alias big_opS_auth_frag]
theorem bigOpS_frag [LawfulFiniteSet S' C] (g : C → A) (X : S') :
    (◯ ([^ op set] x ∈ X, g x) : Auth (SI := SI) A) = [^ op set] x ∈ X, ◯ (g x) :=
  View.bigOpS_frag _ _

@[rocq_alias big_opMS_auth_frag]
theorem bigOpMS_frag [LawfulFiniteMultiSet MS' C] (g : C → A) (X : MS') :
    (◯ ([^ op mset] x ∈ X, g x) : Auth (SI := SI) A) = [^ op mset] x ∈ X, ◯ (g x) :=
  View.bigOpMS_frag _ _

end BigOp

/-! ## Validity -/

@[rocq_alias auth_auth_dfrac_op_invN]
theorem auth_dfrac_op_invN {n : SI} {dq1 dq2 : DFrac} {a b : A}
    (h : ✓{n} ((●{dq1} a : Auth (SI := SI) A) • ●{dq2} b)) : a ≡{n}≡ b :=
  dist_of_validN_auth h

@[rocq_alias auth_auth_dfrac_op_inv]
theorem auth_dfrac_op_inv {dq1 dq2 : DFrac} {a b : A}
    (h : ✓[SI] ((●{dq1} a : Auth (SI := SI) A) • ●{dq2} b)) : a = b :=
  eq_of_valid_auth h

#rocq_ignore auth_auth_dfrac_op_inv_L "Use auth_dfrac_op_inv"


@[rocq_alias auth_auth_dfrac_validN]
theorem auth_dfrac_validN {n : SI} {dq : DFrac} {a : A} :
    (✓{n} (●{dq} a : Auth (SI := SI) A)) ↔ (✓[SI] dq ∧ ✓{n} a) := by
  rw [auth_validN_iff]
  exact and_congr_right fun _ => AuthViewRel.authViewRel_unit_iff

@[rocq_alias auth_auth_validN]
theorem auth_validN {n : SI} {a : A} :
    (✓{n} (● a : Auth (SI := SI) A)) ↔ (✓{n} a) := by
  rw [auth_dfrac_validN]
  exact and_iff_right_iff_imp.mpr fun _ => DFrac.valid_own_one

@[rocq_alias auth_auth_dfrac_op_validN]
theorem auth_dfrac_op_validN {n : SI} {dq1 dq2 : DFrac} {a1 a2 : A} :
    (✓{n} ((●{dq1} a1 : Auth (SI := SI) A) • ●{dq2} a2)) ↔ (✓[SI] (dq1 • dq2) ∧ a1 ≡{n}≡ a2 ∧ ✓{n} a1) := by
  rw [View.auth_op_auth_validN_iff]
  exact and_congr_right fun _ => and_congr_right fun _ => AuthViewRel.authViewRel_unit_iff

@[rocq_alias auth_auth_op_validN]
theorem auth_op_validN {n : SI} {a1 a2 : A} : (✓{n} ((● a1 : Auth (SI := SI) A) • ● a2)) ↔ False :=
  auth_one_op_auth_one_validN_iff

@[rocq_alias auth_frag_validN]
theorem frag_validN {n : SI} {b : A} : (✓{n} (◯ b : Auth (SI := SI) A)) ↔ (✓{n} b) := by
  rw [frag_validN_iff, AuthViewRel.authViewRel_exists_iff]

#rocq_ignore auth_frag_validN_1 "Use frag_validN.mp"
#rocq_ignore auth_frag_validN_2 "Use frag_validN.mpr"

@[rocq_alias auth_frag_op_validN]
theorem frag_op_validN {n : SI} {b1 b2 : A} :
    (✓{n} ((◯ b1 : Auth (SI := SI) A) • ◯ b2)) ↔ (✓{n} (b1 • b2)) := by
  rw [← frag_op]; exact frag_validN

#rocq_ignore auth_frag_op_validN_1 "Use frag_op_validN"
#rocq_ignore auth_frag_op_validN_2 "Use frag_op_validN"

theorem both_dfrac_validN_frame {n : SI} {dq : DFrac} {a b : A} :
    (✓{n} ((●{dq} a : Auth (SI := SI) A) • ◯ b)) ↔ (✓[SI] dq ∧ (∃ c, b • c ≼ₒ{n} a) ∧ ✓{n} a) :=
  auth_op_frag_validN_iff

theorem both_dfrac_validN_ord [IncOrd SI A] {n : SI} {dq : DFrac} {a b : A} :
    (✓{n} ((●{dq} a : Auth (SI := SI) A) • ◯ b)) ↔ (✓[SI] dq ∧ b ≼ₒ{n} a ∧ ✓{n} a) :=
  both_dfrac_validN_frame.trans
    (and_congr_right fun _ => and_congr_left fun _ => exists_op_ordN_iff_ordN)

@[rocq_alias auth_both_dfrac_validN]
theorem both_dfrac_validN [OrdInc SI A] {n : SI} {dq : DFrac} {a b : A} :
    (✓{n} ((●{dq} a : Auth (SI := SI) A) • ◯ b)) ↔ (✓[SI] dq ∧ b ≼{n} a ∧ ✓{n} a) :=
  both_dfrac_validN_frame.trans
    (and_congr_right fun _ => and_congr_left fun _ => exists_op_ordN_iff_incN)

theorem both_validN_frame {n : SI} {a b : A} :
    (✓{n} ((● a : Auth (SI := SI) A) • ◯ b)) ↔ ((∃ c, b • c ≼ₒ{n} a) ∧ ✓{n} a) :=
  auth_one_op_frag_validN_iff

theorem both_validN_ord [IncOrd SI A] {n : SI} {a b : A} :
    (✓{n} ((● a : Auth (SI := SI) A) • ◯ b)) ↔ (b ≼ₒ{n} a ∧ ✓{n} a) :=
  both_validN_frame.trans (and_congr_left fun _ => exists_op_ordN_iff_ordN)

@[rocq_alias auth_both_validN]
theorem both_validN [OrdInc SI A] {n : SI} {a b : A} :
    (✓{n} ((● a : Auth (SI := SI) A) • ◯ b)) ↔ (b ≼{n} a ∧ ✓{n} a) :=
  both_validN_frame.trans (and_congr_left fun _ => exists_op_ordN_iff_incN)

@[rocq_alias auth_auth_dfrac_valid]
theorem auth_dfrac_valid {dq : DFrac} {a : A} : (✓[SI] (●{dq} a : Auth (SI := SI) A)) ↔ (✓[SI] dq ∧ ✓[SI] a) := by
  rw [auth_valid_iff]
  refine and_congr_right fun _ => ?_
  rw [valid_iff_validN]
  exact forall_congr' fun _ => AuthViewRel.authViewRel_unit_iff

@[rocq_alias auth_auth_valid]
theorem auth_valid {a : A} : (✓[SI] (● a : Auth (SI := SI) A)) ↔ (✓[SI] a) := by
  rw [auth_dfrac_valid]
  exact and_iff_right_iff_imp.mpr fun _ => DFrac.valid_own_one

@[rocq_alias auth_auth_dfrac_op_valid]
theorem auth_dfrac_op_valid {dq1 dq2 : DFrac} {a1 a2 : A} :
    (✓[SI] ((●{dq1} a1 : Auth (SI := SI) A) • ●{dq2} a2)) ↔ (✓[SI] (dq1 • dq2) ∧ a1 = a2 ∧ ✓[SI] a1) := by
  rw [auth_op_auth_valid_iff]
  constructor
  · exact fun ⟨hdq, ha, hr⟩ => ⟨hdq, ha, valid_iff_validN.mpr (hr · |>.2)⟩
  · exact fun ⟨hdq, ha, hv⟩ =>
      ⟨hdq, ha, fun _ => AuthViewRel.authViewRel_unit_iff.mpr hv.validN⟩

@[rocq_alias auth_auth_op_valid]
theorem auth_op_valid {a1 a2 : A} : (✓[SI] ((● a1 : Auth (SI := SI) A) • ● a2)) ↔ False :=
  auth_one_op_auth_one_valid_iff

@[rocq_alias auth_frag_valid]
theorem frag_valid {b : A} : (✓[SI] (◯ b : Auth (SI := SI) A)) ↔ (✓[SI] b) := by
  simp only [valid_iff_validN]
  exact forall_congr' fun _ => frag_validN

#rocq_ignore auth_frag_valid_1 "Use frag_valid"
#rocq_ignore auth_frag_valid_2 "Use frag_valid"

@[rocq_alias auth_frag_op_valid]
theorem frag_op_valid {b1 b2 : A} : (✓[SI] ((◯ b1 : Auth (SI := SI) A) • ◯ b2)) ↔ (✓[SI] (b1 • b2)) := by
  rw [← frag_op]; exact frag_valid

#rocq_ignore auth_frag_op_valid_1 "Use frag_op_valid"
#rocq_ignore auth_frag_op_valid_2 "Use frag_op_valid"

theorem both_dfrac_valid_frame {dq : DFrac} {a b : A} :
    (✓[SI] ((●{dq} a : Auth (SI := SI) A) • ◯ b)) ↔ (✓[SI] dq ∧ (∀ (n : SI), ∃ c, b • c ≼ₒ{n} a) ∧ ✓[SI] a) := by
  simp only [valid_iff_validN]
  constructor
  · refine fun h => ⟨fun n => (both_dfrac_validN_frame.mp (h n)).1, fun n => ?_, fun n => ?_⟩
    · exact (both_dfrac_validN_frame.mp (h n)).2.1
    · exact (both_dfrac_validN_frame.mp (h n)).2.2
  · exact fun ⟨hdq, hinc, hv⟩ n => both_dfrac_validN_frame.mpr ⟨hdq n, hinc n, hv n⟩

theorem both_dfrac_valid_ord [IncOrd SI A] {dq : DFrac} {a b : A} :
    (✓[SI] ((●{dq} a : Auth (SI := SI) A) • ◯ b)) ↔ (✓[SI] dq ∧ (∀ (n : SI), b ≼ₒ{n} a) ∧ ✓[SI] a) :=
  both_dfrac_valid_frame.trans (and_congr_right fun _ => and_congr_left fun _ =>
    forall_congr' fun _ => exists_op_ordN_iff_ordN)

@[rocq_alias auth_both_dfrac_valid]
theorem both_dfrac_valid [OrdInc SI A] {dq : DFrac} {a b : A} :
    (✓[SI] ((●{dq} a : Auth (SI := SI) A) • ◯ b)) ↔ (✓[SI] dq ∧ (∀ (n : SI), b ≼{n} a) ∧ ✓[SI] a) :=
  both_dfrac_valid_frame.trans (and_congr_right fun _ => and_congr_left fun _ =>
    forall_congr' fun _ => exists_op_ordN_iff_incN)

theorem auth_both_valid_frame {a b : A} :
    (✓[SI] ((● a : Auth (SI := SI) A) • ◯ b)) ↔ ((∀ (n : SI), ∃ c, b • c ≼ₒ{n} a) ∧ ✓[SI] a) := by
  rw [both_dfrac_valid_frame]
  constructor
  · exact fun ⟨_, hinc, hv⟩ => ⟨hinc, hv⟩
  · exact fun ⟨hinc, hv⟩ => ⟨DFrac.valid_own_one, hinc, hv⟩

theorem auth_both_valid_ord [IncOrd SI A] {a b : A} :
    (✓[SI] ((● a : Auth (SI := SI) A) • ◯ b)) ↔ ((∀ (n : SI), b ≼ₒ{n} a) ∧ ✓[SI] a) :=
  auth_both_valid_frame.trans
    (and_congr_left fun _ => forall_congr' fun _ => exists_op_ordN_iff_ordN)

@[rocq_alias auth_both_valid]
theorem auth_both_valid [OrdInc SI A] {a b : A} :
    (✓[SI] ((● a : Auth (SI := SI) A) • ◯ b)) ↔ ((∀ (n : SI), b ≼{n} a) ∧ ✓[SI] a) :=
  auth_both_valid_frame.trans
    (and_congr_left fun _ => forall_congr' fun _ => exists_op_ordN_iff_incN)

theorem auth_both_dfrac_valid_2_ord {dq : DFrac} {a b : A} (hdq : ✓[SI] dq) (ha : ✓[SI] a)
    (hb : b ≼ₒ[SI] a) : ✓[SI] ((●{dq} a : Auth (SI := SI) A) • ◯ b) :=
  both_dfrac_valid_frame.mpr
    ⟨hdq, fun n => ⟨unit, by rw [unit_right_id]; exact ordN_of_ord n hb⟩, ha⟩

/-- Note: The reverse direction only holds if the camera is discrete. -/
@[rocq_alias auth_both_dfrac_valid_2]
theorem auth_both_dfrac_valid_2 {dq : DFrac} {a b : A} (hdq : ✓[SI] dq) (ha : ✓[SI] a)
    (hb : b ≼ a) : ✓[SI] ((●{dq} a : Auth (SI := SI) A) • ◯ b) :=
  let ⟨c, hc⟩ := hb
  both_dfrac_valid_frame.mpr ⟨hdq, fun _ => ⟨c, ordN_of_dist (.of_eq hc.symm)⟩, ha⟩

theorem auth_both_valid_2_ord {a b : A} (ha : ✓[SI] a) (hb : b ≼ₒ[SI] a) :
    ✓[SI] ((● a : Auth (SI := SI) A) • ◯ b) :=
  auth_both_dfrac_valid_2_ord DFrac.valid_own_one ha hb

@[rocq_alias auth_both_valid_2]
theorem auth_both_valid_2 {a b : A} (ha : ✓[SI] a) (hb : b ≼ a) :
    ✓[SI] ((● a : Auth (SI := SI) A) • ◯ b) :=
  auth_both_dfrac_valid_2 DFrac.valid_own_one ha hb

theorem both_dfrac_valid_discrete_frame [ORA.Discrete SI A] {dq : DFrac} {a b : A} :
    (✓[SI] ((●{dq} a : Auth (SI := SI) A) • ◯ b)) ↔ (✓[SI] dq ∧ (∃ c, b • c ≼ₒ[SI] a) ∧ ✓[SI] a) := by
  rw [both_dfrac_valid_frame]
  constructor
  · exact fun ⟨hdq, hinc, hv⟩ => let ⟨c, h⟩ := hinc 0; ⟨hdq, ⟨c, discrete_ord h⟩, hv⟩
  · exact fun ⟨hdq, ⟨c, h⟩, hv⟩ => ⟨hdq, fun n => ⟨c, ordN_of_ord n h⟩, hv⟩

theorem both_dfrac_valid_discrete_ord [ORA.Discrete SI A] [IncOrd SI A] {dq : DFrac} {a b : A} :
    (✓[SI] ((●{dq} a : Auth (SI := SI) A) • ◯ b)) ↔ (✓[SI] dq ∧ b ≼ₒ[SI] a ∧ ✓[SI] a) :=
  both_dfrac_valid_discrete_frame.trans
    (and_congr_right fun _ => and_congr_left fun _ => exists_op_ord_iff_ord)

@[rocq_alias auth_both_dfrac_valid_discrete]
theorem both_dfrac_valid_discrete [ORA.Discrete SI A] [OrdInc SI A] {dq : DFrac} {a b : A} :
    (✓[SI] ((●{dq} a : Auth (SI := SI) A) • ◯ b)) ↔ (✓[SI] dq ∧ b ≼ a ∧ ✓[SI] a) :=
  both_dfrac_valid_discrete_frame.trans
    (and_congr_right fun _ => and_congr_left fun _ => exists_op_ord_iff_inc)

theorem auth_both_valid_discrete_frame [ORA.Discrete SI A] {a b : A} :
    (✓[SI] ((● a : Auth (SI := SI) A) • ◯ b)) ↔ ((∃ c, b • c ≼ₒ[SI] a) ∧ ✓[SI] a) := by
  rw [both_dfrac_valid_discrete_frame]
  constructor
  · exact fun ⟨_, hinc, hv⟩ => ⟨hinc, hv⟩
  · exact fun ⟨hinc, hv⟩ => ⟨DFrac.valid_own_one, hinc, hv⟩

theorem auth_both_valid_discrete_ord [ORA.Discrete SI A] [IncOrd SI A] {a b : A} :
    (✓[SI] ((● a : Auth (SI := SI) A) • ◯ b)) ↔ (b ≼ₒ[SI] a ∧ ✓[SI] a) :=
  auth_both_valid_discrete_frame.trans (and_congr_left fun _ => exists_op_ord_iff_ord)

@[rocq_alias auth_both_valid_discrete]
theorem auth_both_valid_discrete [ORA.Discrete SI A] [OrdInc SI A] {a b : A} :
    (✓[SI] ((● a : Auth (SI := SI) A) • ◯ b)) ↔ (b ≼ a ∧ ✓[SI] a) :=
  auth_both_valid_discrete_frame.trans (and_congr_left fun _ => exists_op_ord_iff_inc)

/-! ## Inclusion -/

@[rocq_alias auth_auth_dfrac_includedN]
theorem auth_dfrac_incN {n : SI} {dq1 dq2 : DFrac} {a1 a2 b : A} :
    ((●{dq1} a1 : Auth (SI := SI) A) ≼{n} ((●{dq2} a2) • ◯ b)) ↔ ((dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2) :=
  auth_incN_auth_op_frag_iff

@[rocq_alias auth_auth_dfrac_included]
theorem auth_dfrac_inc {dq1 dq2 : DFrac} {a1 a2 b : A} :
    ((●{dq1} a1 : Auth (SI := SI) A) ≼ ((●{dq2} a2) • ◯ b)) ↔ ((dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 = a2) :=
  auth_inc_auth_op_frag_iff

@[rocq_alias auth_auth_includedN]
theorem auth_incN {n : SI} {a1 a2 b : A} :
    ((● a1 : Auth (SI := SI) A) ≼{n} ((● a2) • ◯ b)) ↔ (a1 ≡{n}≡ a2) :=
  auth_one_incN_auth_one_op_frag_iff

@[rocq_alias auth_auth_included]
theorem auth_inc {a1 a2 b : A} :
    ((● a1 : Auth (SI := SI) A) ≼ ((● a2) • ◯ b)) ↔ (a1 = a2) :=
  auth_one_inc_auth_one_op_frag_iff

@[rocq_alias auth_frag_includedN]
theorem frag_incN {n : SI} {dq : DFrac} {a b1 b2 : A} :
    ((◯ b1 : Auth (SI := SI) A) ≼{n} ((●{dq} a) • ◯ b2)) ↔ (b1 ≼{n} b2) :=
  frag_incN_auth_op_frag_iff

@[rocq_alias auth_frag_included]
theorem frag_inc {dq : DFrac} {a b1 b2 : A} : ((◯ b1 : Auth (SI := SI) A) ≼ ((●{dq} a) • ◯ b2)) ↔ (b1 ≼ b2) :=
  frag_inc_auth_op_frag_iff

/-- The weaker `auth_both_included` lemmas below are a consequence of the
    `auth_included` and `frag_included` lemmas above. -/
@[rocq_alias auth_both_dfrac_includedN]
theorem auth_both_dfrac_incN {n : SI} {dq1 dq2 : DFrac} {a1 a2 b1 b2 : A} :
    (((●{dq1} a1 : Auth (SI := SI) A) • ◯ b1) ≼{n} ((●{dq2} a2) • ◯ b2)) ↔
      ((dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2 ∧ b1 ≼{n} b2) :=
  auth_op_frag_incN_auth_op_frag_iff

@[rocq_alias auth_both_dfrac_included]
theorem auth_both_dfrac_inc {dq1 dq2 : DFrac} {a1 a2 b1 b2 : A} :
    (((●{dq1} a1 : Auth (SI := SI) A) • ◯ b1) ≼ ((●{dq2} a2) • ◯ b2)) ↔
      ((dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 = a2 ∧ b1 ≼ b2) :=
  auth_op_frag_inc_auth_op_frag_iff

@[rocq_alias auth_both_includedN]
theorem auth_both_incN {n : SI} {a1 a2 b1 b2 : A} :
    (((● a1 : Auth (SI := SI) A) • ◯ b1) ≼{n} ((● a2) • ◯ b2)) ↔ (a1 ≡{n}≡ a2 ∧ b1 ≼{n} b2) :=
  auth_one_op_frag_incN_auth_one_op_frag_iff

@[rocq_alias auth_both_included]
theorem auth_both_inc {a1 a2 b1 b2 : A} :
    (((● a1 : Auth (SI := SI) A) • ◯ b1) ≼ ((● a2) • ◯ b2)) ↔ (a1 = a2 ∧ b1 ≼ b2) :=
  auth_one_op_frag_inc_auth_one_op_frag_iff

theorem auth_dfrac_ordN {n : SI} {dq1 dq2 : DFrac} {a1 a2 b : A} [Increasing SI b] :
    ((●{dq1} a1 : Auth (SI := SI) A) ≼ₒ{n} ((●{dq2} a2) • ◯ b)) ↔ ((dq1 ≼ₒ[SI] dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2) :=
  auth_ordN_auth_op_frag_iff

theorem auth_dfrac_ord {dq1 dq2 : DFrac} {a1 a2 b : A} [Increasing SI b] :
    ((●{dq1} a1 : Auth (SI := SI) A) ≼ₒ[SI] ((●{dq2} a2) • ◯ b)) ↔ ((dq1 ≼ₒ[SI] dq2 ∨ dq1 = dq2) ∧ a1 = a2) :=
  auth_ord_auth_op_frag_iff

theorem auth_ordN {n : SI} {a1 a2 b : A} [Increasing SI b] :
    ((● a1 : Auth (SI := SI) A) ≼ₒ{n} ((● a2) • ◯ b)) ↔ (a1 ≡{n}≡ a2) :=
  auth_one_ordN_auth_one_op_frag_iff

theorem auth_ord {a1 a2 b : A} [Increasing SI b] :
    ((● a1 : Auth (SI := SI) A) ≼ₒ[SI] ((● a2) • ◯ b)) ↔ (a1 = a2) :=
  auth_one_ord_auth_one_op_frag_iff

theorem frag_ordN {n : SI} {dq : DFrac} {a b1 b2 : A} :
    ((◯ b1 : Auth (SI := SI) A) ≼ₒ{n} ((●{dq} a) • ◯ b2)) ↔ (b1 ≼ₒ{n} b2) :=
  frag_ordN_auth_op_frag_iff

theorem frag_ord {dq : DFrac} {a b1 b2 : A} : ((◯ b1 : Auth (SI := SI) A) ≼ₒ[SI] ((●{dq} a) • ◯ b2)) ↔ (b1 ≼ₒ[SI] b2) :=
  frag_ord_auth_op_frag_iff

theorem auth_both_dfrac_ordN {n : SI} {dq1 dq2 : DFrac} {a1 a2 b1 b2 : A} :
    (((●{dq1} a1 : Auth (SI := SI) A) • ◯ b1) ≼ₒ{n} ((●{dq2} a2) • ◯ b2)) ↔
      ((dq1 ≼ₒ[SI] dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2 ∧ b1 ≼ₒ{n} b2) :=
  auth_op_frag_ordN_auth_op_frag_iff

theorem auth_both_dfrac_ord {dq1 dq2 : DFrac} {a1 a2 b1 b2 : A} :
    (((●{dq1} a1 : Auth (SI := SI) A) • ◯ b1) ≼ₒ[SI] ((●{dq2} a2) • ◯ b2)) ↔
      ((dq1 ≼ₒ[SI] dq2 ∨ dq1 = dq2) ∧ a1 = a2 ∧ b1 ≼ₒ[SI] b2) :=
  auth_op_frag_ord_auth_op_frag_iff

theorem auth_both_ordN {n : SI} {a1 a2 b1 b2 : A} :
    (((● a1 : Auth (SI := SI) A) • ◯ b1) ≼ₒ{n} ((● a2) • ◯ b2)) ↔ (a1 ≡{n}≡ a2 ∧ b1 ≼ₒ{n} b2) :=
  auth_one_op_frag_ordN_auth_one_op_frag_iff

theorem auth_both_ord {a1 a2 b1 b2 : A} :
    (((● a1 : Auth (SI := SI) A) • ◯ b1) ≼ₒ[SI] ((● a2) • ◯ b2)) ↔ (a1 = a2 ∧ b1 ≼ₒ[SI] b2) :=
  auth_one_op_frag_ord_auth_one_op_frag_iff

/-! ## Updates -/

theorem auth_update_ord {a b a' b' : A}
    (hup : ∀ (n : SI) (bf : A), b • bf ≼ₒ{n} a → ✓{n} a → b' • bf ≼ₒ{n} a' ∧ ✓{n} a') :
    ((● a : Auth (SI := SI) A) • ◯ b) ~~>[SI] (● a') • ◯ b' :=
  auth_one_op_frag_update fun n bf ⟨⟨c, hinc⟩, hv⟩ => by
    rw [← assoc'] at hinc
    obtain ⟨hinc', hv'⟩ := hup n (bf • c) hinc hv
    exact ⟨⟨c, by rw [← assoc']; exact hinc'⟩, hv'⟩

theorem auth_update_alloc_ord {a a' b' : A}
    (hup : ∀ (n : SI) (bf : A), bf ≼ₒ{n} a → ✓{n} a → b' • bf ≼ₒ{n} a' ∧ ✓{n} a') :
    (● a : Auth (SI := SI) A) ~~>[SI] (● a') • ◯ b' :=
  auth_one_alloc fun n bf ⟨⟨c, hinc⟩, hv⟩ => by
    obtain ⟨hinc', hv'⟩ := hup n (bf • c) hinc hv
    exact ⟨⟨c, by rw [← assoc']; exact hinc'⟩, hv'⟩

theorem auth_update_dealloc_ord {a b a' : A}
    (hup : ∀ (n : SI) (bf : A), b • bf ≼ₒ{n} a → ✓{n} a → bf ≼ₒ{n} a' ∧ ✓{n} a') :
    ((● a : Auth (SI := SI) A) • ◯ b) ~~>[SI] ● a' :=
  auth_one_op_frag_dealloc fun n bf ⟨⟨c, hinc⟩, hv⟩ => by
    rw [← assoc'] at hinc
    obtain ⟨hinc', hv'⟩ := hup n (bf • c) hinc hv
    exact ⟨⟨c, hinc'⟩, hv'⟩

theorem auth_update_auth_ord {a a' : A}
    (hup : ∀ (n : SI) (bf : A), bf ≼ₒ{n} a → ✓{n} a → bf ≼ₒ{n} a' ∧ ✓{n} a') :
    (● a : Auth (SI := SI) A) ~~>[SI] ● a' :=
  auth_one_update fun n bf ⟨⟨c, hinc⟩, hv⟩ =>
    let ⟨hinc', hv'⟩ := hup n (bf • c) hinc hv
    ⟨⟨c, hinc'⟩, hv'⟩

@[rocq_alias auth_update]
theorem auth_update [OrdInc SI A] {a b a' b' : A} (hup : (a, b) ~l~>[SI] (a', b')) :
    ((● a : Auth (SI := SI) A) • ◯ b) ~~>[SI] (● a') • ◯ b' := by
  refine auth_one_op_frag_update fun n bf h => ?_
  obtain ⟨⟨c, hinc⟩, hv⟩ := AuthViewRel.iff_inc.mp h
  have ⟨hv', ha'_eq⟩ := hup n (some (bf • c)) hv (hinc.trans assoc.symm.dist)
  exact AuthViewRel.of_inc ⟨⟨c, ha'_eq.trans assoc.dist⟩, hv'⟩

@[rocq_alias auth_update_alloc]
theorem auth_update_alloc [OrdInc SI A] {a a' b' : A} (hup : (a, unit) ~l~>[SI] (a', b')) :
    (● a : Auth (SI := SI) A) ~~>[SI] (● a') • ◯ b' := by
  rw [← unit_right_id (SI := SI) (x := (● a : Auth (SI := SI) A))]
  exact auth_update hup

@[rocq_alias auth_update_dealloc]
theorem auth_update_dealloc [OrdInc SI A] {a b a' : A} (hup : (a, b) ~l~>[SI] (a', unit)) :
    ((● a : Auth (SI := SI) A) • ◯ b) ~~>[SI] ● a' := by
  rw [← unit_right_id (SI := SI) (x := (● a' : Auth (SI := SI) A))]
  exact auth_update hup

@[rocq_alias auth_update_auth]
theorem auth_update_auth [OrdInc SI A] {a a' b' : A} (hup : (a, unit) ~l~>[SI] (a', b')) :
    (● a : Auth (SI := SI) A) ~~>[SI] ● a' :=
  Update.trans (auth_update_alloc hup) Update.op_l

@[rocq_alias auth_update_auth_persist]
theorem auth_update_auth_persist {dq : DFrac} {a : A} :
    (●{dq} a : Auth (SI := SI) A) ~~>[SI] ●{DFrac.discard} a :=
  auth_discard

@[rocq_alias auth_updateP_auth_unpersist]
theorem auth_updateP_auth_unpersist {a : A} :
    (●{DFrac.discard} a : Auth (SI := SI) A) ~~>:[SI]
      fun k => ∃ q, k = ●{DFrac.own q} a :=
  auth_acquire

@[rocq_alias auth_updateP_both_unpersist]
theorem auth_updateP_both_unpersist {a b : A} :
    ((●{DFrac.discard} a : Auth (SI := SI) A) • ◯ b) ~~>:[SI]
      fun k => ∃ q, k = ((●{DFrac.own q} a : Auth (SI := SI) A) • ◯ b) :=
  auth_op_frag_acquire

@[rocq_alias auth_update_dfrac_alloc]
theorem auth_update_dfrac_alloc {dq : DFrac} {a b : A} [CoreId b] (hb : b ≼ a) :
    (●{dq} a : Auth (SI := SI) A) ~~>[SI] (●{dq} a) • ◯ b := by
  refine auth_alloc fun n bf ⟨⟨c, hinc⟩, hv⟩ => ⟨⟨c, ?_⟩, hv⟩
  have hba : b • a = a := comm'.trans (op_core_left_of_inc hb)
  rw [← assoc']
  exact (ordN_iff_right hba.dist).mp (op_monoN_right_ord b hinc)

theorem auth_local_update_ord {a b0 b1 a' b0' b1' : A} (hup : (b0, b1) ~l~>[SI] (b0', b1'))
    (hinc : b0' ≼ₒ[SI] a') (hv : ✓[SI] a') :
    ((● a : Auth (SI := SI) A) • ◯ b0, (● a) • ◯ b1) ~l~>[SI] ((● a' : Auth (SI := SI) A) • ◯ b0', (● a') • ◯ b1') :=
  view_local_update hup fun n _ =>
    ⟨⟨unit, by rw [unit_right_id]; exact ordN_of_ord n hinc⟩, hv.validN⟩

@[rocq_alias auth_local_update]
theorem auth_local_update {a b0 b1 a' b0' b1' : A} (hup : (b0, b1) ~l~>[SI] (b0', b1'))
    (hinc : b0' ≼ a') (hv : ✓[SI] a') :
    ((● a : Auth (SI := SI) A) • ◯ b0, (● a) • ◯ b1) ~l~>[SI] ((● a' : Auth (SI := SI) A) • ◯ b0', (● a') • ◯ b1') :=
  let ⟨c, hc⟩ := hinc
  view_local_update hup fun _ _ => ⟨⟨c, ordN_of_dist (.of_eq hc.symm)⟩, hv.validN⟩

/-! ## Functor -/

/-- The AuthViewRel is preserved under ORA homomorphisms. -/
theorem authViewRel_map [UORA SI A'] [UORA SI B']
    (g : A' -C>[SI] B') (n : SI) (a : A')
    (b : A') : AuthViewRel n a b → AuthViewRel n (g a) (g b) :=
  fun ⟨⟨c, hinc⟩, hv⟩ => ⟨⟨g c, by rw [← g.op]; exact g.monoN_ord hinc⟩, g.validN hv⟩

@[rocq_alias authURF]
abbrev AuthURF (T : COFE.OFunctorPre SI) [URFunctor SI T] : COFE.OFunctorPre SI :=
  fun A B _ _ => Auth (SI := SI) (T A B)

instance instURFunctorAuthURF {T : COFE.OFunctorPre SI} [URFunctor SI T] :
    URFunctor SI (AuthURF T) where
  map {A A'} {B B'} _ _ _ _ f g :=
    mapC
      (URFunctor.map (F := T) f g).toHom
      (URFunctor.map (F := T) f g)
      (authViewRel_map (URFunctor.map f g))
  map_ne.ne a b c hx d e hy x :=
    map_ne _ (URFunctor.map_ne.ne hx hy) (URFunctor.map_ne.ne hx hy)
  map_id x := by
    refine .trans ?_ (map_id x)
    refine congrArg (View.map _ · _ _) (funext fun _ => URFunctor.map_id _) |>.trans
      (congrArg (View.map _ _ · _) (funext fun _ => URFunctor.map_id _))
  map_comp f g f' g' x := by
    simp only [mapC]
    refine .trans ?_ (map_compose' ..)
    refine congrArg (View.map _ · _ _) (funext fun _ => URFunctor.map_comp f g f' g' _) |>.trans
      (congrArg (View.map _ _ · _) (funext fun _ => URFunctor.map_comp f g f' g' _))

instance instRFunctorAffineURF {T : COFE.OFunctorPre SI} [URFunctor SI T] [RFunctorAffine SI T] :
    RFunctorAffine SI (AuthURF T) where
  affine := inferInstance

@[rocq_alias authURF_contractive]
instance instURFunctorContractiveAuthURF {T : COFE.OFunctorPre SI} [URFunctorContractive SI T] :
    URFunctorContractive SI (AuthURF T) where
  map_contractive.1 h x := by
    apply map_ne <;> apply URFunctorContractive.map_contractive.1 h

@[rocq_alias authRF]
abbrev AuthRF (T : COFE.OFunctorPre SI) [URFunctor SI T] : COFE.OFunctorPre SI :=
  fun A B _ _ => Auth (SI := SI) (T A B)

instance instRFunctorAuthRF {T : COFE.OFunctorPre SI} [URFunctor SI T] :
    RFunctor SI (AuthRF T) where
  map {A A'} {B B'} _ _ _ _ f g :=
    mapC
      (URFunctor.map (F := T) f g).toHom
      (URFunctor.map (F := T) f g)
      (authViewRel_map (URFunctor.map f g))
  map_ne.ne a b c hx d e hy x := by
    apply map_ne <;> exact URFunctor.map_ne.ne hx hy
  map_id x := by
    refine .trans ?_ (map_id x)
    refine congrArg (View.map _ · _ _) (funext fun _ => URFunctor.map_id _) |>.trans
      (congrArg (View.map _ _ · _) (funext fun _ => URFunctor.map_id _))
  map_comp f g f' g' x := by
    simp only [mapC]
    rw [← map_compose']
    refine congrArg (View.map _ · _ _) (funext fun _ => URFunctor.map_comp f g f' g' _) |>.trans
      (congrArg (View.map _ _ · _) (funext fun _ => URFunctor.map_comp f g f' g' _))

instance instRFunctorAffineRF {T : COFE.OFunctorPre SI} [URFunctor SI T] [RFunctorAffine SI T] :
    RFunctorAffine SI (AuthRF T) where
  affine := inferInstance

@[rocq_alias authRF_contractive]
instance instRFunctorContractiveAuthRF {T : COFE.OFunctorPre SI} [URFunctorContractive SI T] :
    RFunctorContractive SI (AuthRF T) where
  map_contractive.1 h x := by
    apply View.map_ne <;> apply URFunctorContractive.map_contractive.1 h

end Auth
