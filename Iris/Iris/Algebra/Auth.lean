/-
Copyright (c) 2025 Alexander Bai. All rights reserved.
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

open Iris

open OFE CMRA UCMRA View

/-!
## Definition of the view relation for the authoritative camera.
-/
/-- The authoritative view relation: the fragment is below the authority in the *order*
(Amaryllis-style). Meaningful for affine algebras only — dropping a fragment summand must not
break the bound, which is affineness. -/
@[rocq_alias auth_view_rel_raw]
def AuthViewRel [UCMRA A] : ViewRel A A := fun n a b => b ≼{n} a ∧ ✓{n} a

namespace AuthViewRel

variable [UCMRA A] [CMRA.Affine A]

@[rocq_alias auth_view_rel]
instance instViewRel_authViewRel : IsViewRel (AuthViewRel (A := A)) :=
  .ofMonoOrd
    (fun ⟨hinc, hv⟩ ha hb hn =>
      ⟨calc _ ≼{_} _ := hb
            _ ≼{_} _ := CMRA.incN_of_incN_le hn hinc
            _ ≼{_} _ := ha.to_incN,
       validN_ne ha (validN_of_le hn hv)⟩)
    (fun _ _ _ ⟨hinc, hv⟩ => validN_of_incN hinc hv)
    (fun _ => ⟨unit, incN_refl unit, unit_valid.validN⟩)

#rocq_ignore auth_view_rel_raw_mono "Use the IsViewRel typeclass"
#rocq_ignore auth_view_rel_raw_valid "Use the IsViewRel typeclass"
#rocq_ignore auth_view_rel_raw_unit "Use the IsViewRel typeclass"

@[rocq_alias auth_view_rel_unit]
theorem authViewRel_unit_iff {n : Nat} {a : A} : AuthViewRel n a unit ↔ ✓{n} a :=
  ⟨(·.2), (⟨CMRA.incN_unit, ·⟩)⟩

@[rocq_alias auth_view_rel_exists]
theorem authViewRel_exists_iff {n : Nat} {b : A} : (∃ a, AuthViewRel n a b) ↔ ✓{n} b :=
  ⟨fun ⟨_, h⟩ => IsViewRel.rel_validN _ _ _ h, (⟨b, incN_refl b, ·⟩)⟩

@[rocq_alias auth_view_rel_discrete]
instance [OFE.Discrete A] [CMRA.Discrete A] : IsViewRelDiscrete (AuthViewRel (A := A)) where
  discrete _ _ _ h :=
    ⟨CMRA.incN_of_inc _ (CMRA.discrete_inc h.1), (discrete_valid h.2).validN⟩

end AuthViewRel


/-! ## Definition and operations on the authoritative camera -/

abbrev Auth (A : Type _) [UCMRA A] :=
  View (AuthViewRel (A := A))

namespace Auth
variable [UCMRA A] [CMRA.Affine A]

instance : OFE (Auth A) := View.instOFE
instance instCMRA : CMRA (Auth A) := View.instCMRA
instance instUCMRA : UCMRA (Auth A) := View.instUCMRA

#rocq_ignore authO "Use the Auth type and View.instOFE typeclass"
#rocq_ignore authR "Use the Auth type and View.instCMRA typeclass"
#rocq_ignore authUR "Use the Auth type and View.instUCMRA typeclass"

#rocq_ignore auth_cmra_discrete "Inference succeeds automatically"
#rocq_ignore auth_ofe_discrete "Inference succeeds automatically"

@[rocq_alias auth_auth]
abbrev auth (dq : DFrac) (a : A) : Auth A := View.Auth dq a

@[rocq_alias auth_frag]
abbrev frag (b : A) : Auth A := Frag b

notation "●{" dq "} " a => auth dq a
notation "● " a => auth (DFrac.own 1) a
notation "◯ " b => frag b

@[rocq_alias auth_auth_ne]
nonrec instance auth_ne {dq : DFrac} : NonExpansive (auth dq : A → Auth A) :=
  auth_ne

#rocq_ignore auth_auth_proper "Derivable from auth_ne with NonExpansive.eqv"

@[rocq_alias auth_frag_ne]
nonrec instance frag_ne : NonExpansive (frag : A → Auth A) :=
  frag_ne

#rocq_ignore auth_frag_proper "Derivable from frag_ne with NonExpansive.eqv"

omit [CMRA.Affine A] in
@[rocq_alias auth_auth_dist_inj]
nonrec theorem auth_dist_inj {n : Nat} {dq1 dq2 : DFrac} {a1 a2 : A}
    (h : (●{dq1} a1) ≡{n}≡ ●{dq2} a2) : dq1 = dq2 ∧ a1 ≡{n}≡ a2 :=
  ⟨auth_inj_frac h, dist_of_auth_dist h⟩

omit [CMRA.Affine A] in
@[rocq_alias auth_auth_inj]
theorem auth_inj {dq1 dq2 : DFrac} {a1 a2 : A} (h : (●{dq1} a1) = ●{dq2} a2) :
    dq1 = dq2 ∧ a1 = a2 :=
  ⟨auth_inj_frac (n := 0) h.dist, OFE.eq_dist_2 fun _ => dist_of_auth_dist h.dist⟩

omit [CMRA.Affine A] in
@[rocq_alias auth_frag_dist_inj]
theorem frag_dist_inj {n : Nat} {b1 b2 : A} (h : (◯ b1 : Auth A) ≡{n}≡ ◯ b2) : b1 ≡{n}≡ b2 :=
  dist_of_frag_dist h

omit [CMRA.Affine A] in
@[rocq_alias auth_frag_inj]
theorem frag_inj {b1 b2 : A} (h : (◯ b1 : Auth A) = ◯ b2) : b1 = b2 :=
  OFE.eq_dist_2 fun _ => dist_of_frag_dist h.dist

@[rocq_alias auth_auth_discrete]
nonrec instance auth_discrete {dq : DFrac} {a : A} [DiscreteE a] [DiscreteE (unit : A)] :
    DiscreteE (●{dq} a) := auth_discrete

@[rocq_alias auth_frag_discrete]
nonrec instance frag_discrete {a : A} [DiscreteE a] : DiscreteE (◯ a : Auth A) :=
  frag_discrete

/-! ## Operations -/
@[rocq_alias auth_auth_dfrac_op]
nonrec theorem auth_dfrac_op {dq1 dq2 : DFrac} {a : A} :
    (●{dq1 • dq2} a) = (●{dq1} a) • (●{dq2} a) :=
  auth_op_auth_eqv

set_option synthInstance.checkSynthOrder false in
@[rocq_alias auth_auth_dfrac_is_op]
instance {dq dq1 dq2 : DFrac} {a : A} [h : IsOp d dq dq1 dq2] :
    IsOp d (●{dq} a : Auth A) (●{dq1} a) (●{dq2} a) where
  is_op := by
    rw [h.is_op]
    apply auth_dfrac_op

@[rocq_alias auth_frag_op]
theorem frag_op {b1 b2 : A} : (◯ (b1 • b2) : Auth A) = ((◯ b1 : Auth A) • ◯ b2) :=
  frag_op_eq

@[rocq_alias auth_frag_mono]
nonrec theorem frag_incExt_of_incExt {b1 b2 : A} (h : b1 ≼ₑ b2) : (◯ b1 : Auth A) ≼ₑ ◯ b2 :=
  frag_incExt_of_incExt h

@[rocq_alias auth_frag_core]
nonrec theorem frag_core {b : A} : core (◯ b : Auth A) = ◯ (core b) :=
  frag_core

@[rocq_alias auth_both_core_discarded]
theorem auth_both_core_discarded :
    core ((●{.discard} a) • ◯ b : Auth A) = (●{.discard} a) • ◯ (core b) :=
  auth_discard_op_frag_core

@[rocq_alias auth_both_core_frac]
theorem auth_both_core_frac {q : Qp} {a b : A} :
    core ((●{.own q} a) • ◯ b : Auth A) = ◯ (core b) :=
  auth_own_op_frag_core

@[rocq_alias auth_auth_core_id]
nonrec instance {a : A} : CoreId (●{.discard} a : Auth A) :=
  instCoreIdAuthDiscard

@[rocq_alias auth_frag_core_id]
nonrec instance {b : A} [CoreId b] : CoreId (◯ b : Auth A) :=
  instCoreIdFrag

@[rocq_alias auth_both_core_id]
nonrec instance {a : A} {b : A} [CoreId b] :
    CoreId ((●{.discard} a : Auth A) • ◯ b) :=
  instCoreIdOpAuthDiscardFrag

@[rocq_alias auth_frag_is_op]
instance {a b1 b2 : A} [h : IsOp d a b1 b2] :
    IsOp d (◯ a : Auth A) (◯ b1) (◯ b2) where
  is_op := (congrArg frag h.is_op).trans frag_op

#rocq_ignore auth_frag_sep_homomorphism "Found by typeclass inference from the View.Frag instance"

section BigOp
open Algebra Std

@[rocq_alias big_opL_auth_frag]
theorem bigOpL_frag (g : Nat → C → A) (l : List C) :
    (◯ ([^ CMRA.op list] k ↦ x ∈ l, g k x) : Auth A) = [^ CMRA.op list] k ↦ x ∈ l, ◯ (g k x) :=
  View.bigOpL_frag _ _

@[rocq_alias big_opM_auth_frag]
theorem bigOpM_frag [LawfulFiniteMap M' K] (g : K → C → A) (m : M' C) :
    (◯ ([^ CMRA.op map] k ↦ x ∈ m, g k x) : Auth A) = [^ CMRA.op map] k ↦ x ∈ m, ◯ (g k x) :=
  View.bigOpM_frag _ _

@[rocq_alias big_opS_auth_frag]
theorem bigOpS_frag [LawfulFiniteSet S' C] (g : C → A) (X : S') :
    (◯ ([^ CMRA.op set] x ∈ X, g x) : Auth A) = [^ CMRA.op set] x ∈ X, ◯ (g x) :=
  View.bigOpS_frag _ _

@[rocq_alias big_opMS_auth_frag]
theorem bigOpMS_frag [LawfulFiniteMultiSet MS' C] (g : C → A) (X : MS') :
    (◯ ([^ CMRA.op mset] x ∈ X, g x) : Auth A) = [^ CMRA.op mset] x ∈ X, ◯ (g x) :=
  View.bigOpMS_frag _ _

end BigOp

/-! ## Validity

The fragment–authority relation is stated with the primitive *order* `≼{n}`/`≼`, which for
classical algebras — those built with `withExtensionOrder` — coincides definitionally with the
extension inclusion of the Rocq originals. Likewise, `[IsTotal]` hypotheses that only provided
reflexivity become `[IncRefl]`; total classical algebras satisfy it automatically. -/

@[rocq_alias auth_auth_dfrac_op_invN]
theorem auth_dfrac_op_invN {n : Nat} {dq1 dq2 : DFrac} {a b : A}
    (h : ✓{n} ((●{dq1} a) • ●{dq2} b)) : a ≡{n}≡ b :=
  dist_of_validN_auth h

@[rocq_alias auth_auth_dfrac_op_inv]
theorem auth_dfrac_op_inv {dq1 dq2 : DFrac} {a b : A}
    (h : ✓ ((●{dq1} a) • ●{dq2} b)) : a = b :=
  eq_of_valid_auth h

#rocq_ignore auth_auth_dfrac_op_inv_L "Use auth_dfrac_op_inv"


@[rocq_alias auth_auth_dfrac_validN]
theorem auth_dfrac_validN {n : Nat} {dq : DFrac} {a : A} :
    (✓{n} (●{dq} a)) ↔ (✓ dq ∧ ✓{n} a) := by
  rw [auth_validN_iff]
  exact ⟨fun ⟨hdq, _, hv⟩ => ⟨hdq, hv⟩, fun ⟨hdq, hv⟩ => ⟨hdq, CMRA.incN_unit, hv⟩⟩

@[rocq_alias auth_auth_validN]
theorem auth_validN {n : Nat} {a : A} :
    (✓{n} (● a : Auth A)) ↔ (✓{n} a) := by
  rw [auth_dfrac_validN]
  exact and_iff_right_iff_imp.mpr fun _ => DFrac.valid_own_one

@[rocq_alias auth_auth_dfrac_op_validN]
theorem auth_dfrac_op_validN {n : Nat} {dq1 dq2 : DFrac} {a1 a2 : A} :
    (✓{n} ((●{dq1} a1) • ●{dq2} a2)) ↔ (✓ (dq1 • dq2) ∧ a1 ≡{n}≡ a2 ∧ ✓{n} a1) := by
  rw [View.auth_op_auth_validN_iff]
  exact ⟨fun ⟨hdq, ha, ⟨_, hv⟩⟩ => ⟨hdq, ha, hv⟩, fun ⟨hdq, ha, hv⟩ => ⟨hdq, ha, CMRA.incN_unit, hv⟩⟩

@[rocq_alias auth_auth_op_validN]
theorem auth_op_validN {n : Nat} {a1 a2 : A} : (✓{n} ((● a1 : Auth A) • ● a2)) ↔ False :=
  auth_one_op_auth_one_validN_iff

@[rocq_alias auth_frag_validN]
theorem frag_validN {n : Nat} {b : A} : (✓{n} (◯ b : Auth A)) ↔ (✓{n} b) := by
  rw [frag_validN_iff, AuthViewRel.authViewRel_exists_iff]

#rocq_ignore auth_frag_validN_1 "Use frag_validN.mp"
#rocq_ignore auth_frag_validN_2 "Use frag_validN.mpr"

@[rocq_alias auth_frag_op_validN]
theorem frag_op_validN {n : Nat} {b1 b2 : A} :
    (✓{n} ((◯ b1 : Auth A) • ◯ b2)) ↔ (✓{n} (b1 • b2)) := by
  rw [← frag_op]; exact frag_validN

#rocq_ignore auth_frag_op_validN_1 "Use frag_op_validN"
#rocq_ignore auth_frag_op_validN_2 "Use frag_op_validN"

@[rocq_alias auth_both_dfrac_validN]
theorem both_dfrac_validN {n : Nat} {dq : DFrac} {a b : A} :
    (✓{n} ((●{dq} a) • ◯ b)) ↔ (✓ dq ∧ b ≼{n} a ∧ ✓{n} a) :=
  auth_op_frag_validN_iff

@[rocq_alias auth_both_validN]
theorem both_validN {n : Nat} {a b : A} :
    (✓{n} ((● a : Auth A) • ◯ b)) ↔ (b ≼{n} a ∧ ✓{n} a) :=
  auth_one_op_frag_validN_iff

@[rocq_alias auth_auth_dfrac_valid]
theorem auth_dfrac_valid {dq : DFrac} {a : A} : (✓ (●{dq} a : Auth A)) ↔ (✓ dq ∧ ✓ a) := by
  rw [auth_valid_iff]
  refine and_congr_right fun _ => ?_
  rw [valid_iff_validN]
  exact forall_congr' fun _ => AuthViewRel.authViewRel_unit_iff

@[rocq_alias auth_auth_valid]
theorem auth_valid {a : A} : (✓ (● a : Auth A)) ↔ (✓ a) := by
  rw [auth_dfrac_valid]
  exact and_iff_right_iff_imp.mpr fun _ => DFrac.valid_own_one

@[rocq_alias auth_auth_dfrac_op_valid]
theorem auth_dfrac_op_valid {dq1 dq2 : DFrac} {a1 a2 : A} :
    (✓ ((●{dq1} a1) • ●{dq2} a2)) ↔ (✓ (dq1 • dq2) ∧ a1 = a2 ∧ ✓ a1) := by
  rw [auth_op_auth_valid_iff]
  constructor
  · exact fun ⟨hdq, ha, hr⟩ => ⟨hdq, ha, valid_iff_validN.mpr (hr · |>.2)⟩
  · exact fun ⟨hdq, ha, hv⟩ => ⟨hdq, ha, fun _ => ⟨CMRA.incN_unit, hv.validN⟩⟩

@[rocq_alias auth_auth_op_valid]
theorem auth_op_valid {a1 a2 : A} : (✓ ((● a1 : Auth A) • ● a2)) ↔ False :=
  auth_one_op_auth_one_valid_iff

@[rocq_alias auth_frag_valid]
theorem frag_valid {b : A} : (✓ (◯ b : Auth A)) ↔ (✓ b) := by
  simp only [valid_iff_validN]
  exact forall_congr' fun _ => frag_validN

#rocq_ignore auth_frag_valid_1 "Use frag_valid"
#rocq_ignore auth_frag_valid_2 "Use frag_valid"

@[rocq_alias auth_frag_op_valid]
theorem frag_op_valid {b1 b2 : A} : (✓ ((◯ b1 : Auth A) • ◯ b2)) ↔ (✓ (b1 • b2)) := by
  rw [← frag_op]; exact frag_valid

#rocq_ignore auth_frag_op_valid_1 "Use frag_op_valid"
#rocq_ignore auth_frag_op_valid_2 "Use frag_op_valid"

@[rocq_alias auth_both_dfrac_valid]
theorem both_dfrac_valid {dq : DFrac} {a b : A} :
    (✓ ((●{dq} a) • ◯ b)) ↔ (✓ dq ∧ (∀ n, b ≼{n} a) ∧ ✓ a) := by
  simp only [valid_iff_validN]
  constructor
  · refine fun h => ⟨fun n => (both_dfrac_validN.mp (h n)).1, fun n => ?_, fun n => ?_⟩
    · exact (both_dfrac_validN.mp (h n)).2.1
    · exact (both_dfrac_validN.mp (h n)).2.2
  · exact fun ⟨hdq, hinc, hv⟩ n => both_dfrac_validN.mpr ⟨hdq n, hinc n, hv n⟩

@[rocq_alias auth_both_valid]
theorem auth_both_valid {a b : A} :
    (✓ ((● a : Auth A) • ◯ b)) ↔ ((∀ n, b ≼{n} a) ∧ ✓ a) := by
  rw [both_dfrac_valid]
  constructor
  · exact fun ⟨_, hinc, hv⟩ => ⟨hinc, hv⟩
  · exact fun ⟨hinc, hv⟩ => ⟨DFrac.valid_own_one, hinc, hv⟩

/-- Note: The reverse direction only holds if the camera is discrete. -/
@[rocq_alias auth_both_dfrac_valid_2]
theorem auth_both_dfrac_valid_2 {dq : DFrac} {a b : A} (hdq : ✓ dq) (ha : ✓ a)
    (hb : b ≼ a) : ✓ ((●{dq} a) • ◯ b) :=
  both_dfrac_valid.mpr ⟨hdq, (CMRA.incN_of_inc · hb), ha⟩

@[rocq_alias auth_both_valid_2]
theorem auth_both_valid_2 {a b : A} (ha : ✓ a) (hb : b ≼ a) :
    ✓ ((● a : Auth A) • ◯ b) :=
  auth_both_dfrac_valid_2 DFrac.valid_own_one ha hb

@[rocq_alias auth_both_dfrac_valid_discrete]
theorem both_dfrac_valid_discrete [CMRA.Discrete A] {dq : DFrac} {a b : A} :
    (✓ ((●{dq} a : Auth A) • ◯ b)) ↔ (✓ dq ∧ b ≼ a ∧ ✓ a) := by
  constructor
  · intro h
    have ⟨hdq, hinc, hv⟩ := both_dfrac_valid.mp h
    exact ⟨hdq, CMRA.discrete_inc (hinc 0), hv⟩
  · exact fun ⟨hdq, hinc, hv⟩ => auth_both_dfrac_valid_2 hdq hv hinc

@[rocq_alias auth_both_valid_discrete]
theorem auth_both_valid_discrete [CMRA.Discrete A] {a b : A} :
    (✓ ((● a : Auth A) • ◯ b)) ↔ (b ≼ a ∧ ✓ a) := by
  rw [both_dfrac_valid_discrete]
  constructor
  · exact fun ⟨_, hinc, hv⟩ => ⟨hinc, hv⟩
  · exact fun ⟨hinc, hv⟩ => ⟨DFrac.valid_own_one, hinc, hv⟩

/-! ## Inclusion -/

@[rocq_alias auth_auth_dfrac_includedN]
theorem auth_dfrac_incExtN {n : Nat} {dq1 dq2 : DFrac} {a1 a2 b : A} :
    ((●{dq1} a1) ≼ₑ{n} ((●{dq2} a2) • ◯ b)) ↔ ((dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2) :=
  auth_incExtN_auth_op_frag_iff

@[rocq_alias auth_auth_dfrac_included]
theorem auth_dfrac_incExt {dq1 dq2 : DFrac} {a1 a2 b : A} :
    ((●{dq1} a1) ≼ₑ ((●{dq2} a2) • ◯ b)) ↔ ((dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 = a2) :=
  auth_incExt_auth_op_frag_iff

@[rocq_alias auth_auth_includedN]
theorem auth_incExtN {n : Nat} {a1 a2 b : A} :
    ((● a1 : Auth A) ≼ₑ{n} ((● a2) • ◯ b)) ↔ (a1 ≡{n}≡ a2) :=
  auth_one_incExtN_auth_one_op_frag_iff

@[rocq_alias auth_auth_included]
theorem auth_incExt {a1 a2 b : A} :
    ((● a1 : Auth A) ≼ₑ ((● a2) • ◯ b)) ↔ (a1 = a2) :=
  auth_one_incExt_auth_one_op_frag_iff

@[rocq_alias auth_frag_includedN]
theorem frag_incExtN {n : Nat} {dq : DFrac} {a b1 b2 : A} :
    ((◯ b1) ≼ₑ{n} ((●{dq} a) • ◯ b2)) ↔ (b1 ≼ₑ{n} b2) :=
  frag_incExtN_auth_op_frag_iff

@[rocq_alias auth_frag_included]
theorem frag_incExt {dq : DFrac} {a b1 b2 : A} : ((◯ b1) ≼ₑ ((●{dq} a) • ◯ b2)) ↔ (b1 ≼ₑ b2) :=
  frag_incExt_auth_op_frag_iff

/-- The weaker `auth_both_included` lemmas below are a consequence of the
    `auth_included` and `frag_included` lemmas above. -/
@[rocq_alias auth_both_dfrac_includedN]
theorem auth_both_dfrac_incExtN {n : Nat} {dq1 dq2 : DFrac} {a1 a2 b1 b2 : A} :
    (((●{dq1} a1) • ◯ b1) ≼ₑ{n} ((●{dq2} a2) • ◯ b2)) ↔
      ((dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2 ∧ b1 ≼ₑ{n} b2) :=
  auth_op_frag_incExtN_auth_op_frag_iff

@[rocq_alias auth_both_dfrac_included]
theorem auth_both_dfrac_incExt {dq1 dq2 : DFrac} {a1 a2 b1 b2 : A} :
    (((●{dq1} a1) • ◯ b1) ≼ₑ ((●{dq2} a2) • ◯ b2)) ↔
      ((dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 = a2 ∧ b1 ≼ₑ b2) :=
  auth_op_frag_incExt_auth_op_frag_iff

@[rocq_alias auth_both_includedN]
theorem auth_both_incExtN {n : Nat} {a1 a2 b1 b2 : A} :
    (((● a1 : Auth A) • ◯ b1) ≼ₑ{n} ((● a2) • ◯ b2)) ↔ (a1 ≡{n}≡ a2 ∧ b1 ≼ₑ{n} b2) :=
  auth_one_op_frag_incExtN_auth_one_op_frag_iff

@[rocq_alias auth_both_included]
theorem auth_both_incExt {a1 a2 b1 b2 : A} :
    (((● a1 : Auth A) • ◯ b1) ≼ₑ ((● a2) • ◯ b2)) ↔ (a1 = a2 ∧ b1 ≼ₑ b2) :=
  auth_one_op_frag_incExt_auth_one_op_frag_iff

/-! ## Updates -/

/-- The primitive authority update: transport the order bound of the fragment composite
past the update, for every fragment frame `bf`. `auth_update_of_localUpdate` recovers the
frame-based Rocq interface for classical fragment algebras. -/
theorem auth_update {a b a' b' : A}
    (hup : ∀ n (bf : A), b • bf ≼{n} a → ✓{n} a → b' • bf ≼{n} a' ∧ ✓{n} a') :
    ((● a : Auth A) • ◯ b) ~~> (● a') • ◯ b' :=
  auth_one_op_frag_update fun n bf ⟨hinc, hv⟩ => hup n bf hinc hv

/-- `auth_update` in allocation form: the fragment starts empty. -/
theorem auth_update_alloc {a a' b' : A}
    (hup : ∀ n (bf : A), bf ≼{n} a → ✓{n} a → b' • bf ≼{n} a' ∧ ✓{n} a') :
    (● a : Auth A) ~~> (● a') • ◯ b' :=
  auth_one_alloc fun n bf ⟨hinc, hv⟩ => hup n bf hinc hv

/-- `auth_update` in deallocation form: the fragment is given up. -/
theorem auth_update_dealloc {a b a' : A}
    (hup : ∀ n (bf : A), b • bf ≼{n} a → ✓{n} a → bf ≼{n} a' ∧ ✓{n} a') :
    ((● a : Auth A) • ◯ b) ~~> ● a' :=
  auth_one_op_frag_dealloc fun n bf ⟨hinc, hv⟩ => hup n bf hinc hv

/-- `auth_update` for the authority alone: every fragment bound is preserved. -/
theorem auth_update_auth {a a' : A}
    (hup : ∀ n (bf : A), bf ≼{n} a → ✓{n} a → bf ≼{n} a' ∧ ✓{n} a') :
    (● a : Auth A) ~~> ● a' :=
  auth_one_update fun n bf ⟨hinc, hv⟩ => hup n bf hinc hv

/-- On a classical algebra — one whose order coincides with the extension inclusion, witnessed
by the plain hypothesis `hsub` — a frame-based local update drives the authority update. -/
@[rocq_alias auth_update]
theorem auth_update_of_localUpdate {a b a' b' : A}
    (hsub : ∀ {n : Nat} {x y : A}, x ≼{n} y → x ≼ₑ{n} y)
    (hup : (a, b) ~l~> (a', b')) :
    ((● a : Auth A) • ◯ b) ~~> (● a') • ◯ b' := by
  refine auth_update fun n bf hinc hv => ?_
  obtain ⟨c, hc⟩ := hsub hinc
  have ha_eq : a ≡{n}≡ b •? some (bf • c) := by
    simp only [CMRA.op?]; exact hc.trans assoc.symm.dist
  have ⟨hv', ha'_eq⟩ := hup n (some (bf • c)) hv ha_eq
  simp only [CMRA.op?] at ha'_eq
  refine ⟨CMRA.incN_of_incExtN ⟨c, ha'_eq.trans assoc.dist⟩, hv'⟩

/-- `auth_update_of_localUpdate` in allocation form. -/
@[rocq_alias auth_update_alloc]
theorem auth_update_alloc_of_localUpdate {a a' b' : A}
    (hsub : ∀ {n : Nat} {x y : A}, x ≼{n} y → x ≼ₑ{n} y)
    (hup : (a, unit) ~l~> (a', b')) :
    (● a : Auth A) ~~> (● a') • ◯ b' := by
  rw [← unit_right_id (x := (● a : Auth A))]
  exact auth_update_of_localUpdate hsub hup

/-- `auth_update_of_localUpdate` in deallocation form. -/
@[rocq_alias auth_update_dealloc]
theorem auth_update_dealloc_of_localUpdate {a b a' : A}
    (hsub : ∀ {n : Nat} {x y : A}, x ≼{n} y → x ≼ₑ{n} y)
    (hup : (a, b) ~l~> (a', unit)) :
    ((● a : Auth A) • ◯ b) ~~> ● a' := by
  rw [← unit_right_id (x := (● a' : Auth A))]
  exact auth_update_of_localUpdate hsub hup

/-- `auth_update_of_localUpdate` for the authority alone. -/
@[rocq_alias auth_update_auth]
theorem auth_update_auth_of_localUpdate {a a' b' : A}
    (hsub : ∀ {n : Nat} {x y : A}, x ≼{n} y → x ≼ₑ{n} y)
    (hup : (a, unit) ~l~> (a', b')) :
    (● a : Auth A) ~~> ● a' :=
  Update.trans (auth_update_alloc_of_localUpdate hsub hup) Update.op_l

@[rocq_alias auth_update_auth_persist]
theorem auth_update_auth_persist {dq : DFrac} {a : A} :
    (●{dq} a : Auth A) ~~> ●{DFrac.discard} a :=
  auth_discard

@[rocq_alias auth_updateP_auth_unpersist]
theorem auth_updateP_auth_unpersist {a : A} :
    (●{DFrac.discard} a : Auth A) ~~>:
      fun k => ∃ q, k = ●{DFrac.own q} a :=
  auth_acquire

@[rocq_alias auth_updateP_both_unpersist]
theorem auth_updateP_both_unpersist {a b : A} :
    ((●{DFrac.discard} a : Auth A) • ◯ b) ~~>:
      fun k => ∃ q, k = ((●{DFrac.own q} a : Auth A) • ◯ b) :=
  auth_op_frag_acquire

@[rocq_alias auth_update_dfrac_alloc]
theorem auth_update_dfrac_alloc {dq : DFrac} {a b : A} [CoreId b] (hb : b ≼ₑ a) :
    (●{dq} a) ~~> (●{dq} a) • ◯ b := by
  refine auth_alloc fun n bf ⟨hinc, hv⟩ => ⟨?_, hv⟩
  have hba : b • a = a := comm'.trans (RABase.op_core_left_of_incExt hb)
  exact (CMRA.incN_iff_right hba.dist).mp (CMRA.op_monoN_right b hinc)

@[rocq_alias auth_local_update]
theorem auth_local_update {a b0 b1 a' b0' b1' : A} (hup : (b0, b1) ~l~> (b0', b1'))
    (hinc : b0' ≼ a') (hv : ✓ a') :
    ((● a : Auth A) • ◯ b0, (● a) • ◯ b1) ~l~> ((● a' : Auth A) • ◯ b0', (● a') • ◯ b1') :=
  view_local_update hup fun n _ => ⟨CMRA.incN_of_inc n hinc, hv.validN⟩

/-! ## Functor -/

/-- The AuthViewRel is preserved under CMRA homomorphisms. -/
theorem authViewRel_map [UCMRA A'] [UCMRA B']
    (g : A' -C> B') (n : Nat) (a : A')
    (b : A') : AuthViewRel n a b → AuthViewRel n (g a) (g b) :=
  fun ⟨hinc, hv⟩ => ⟨g.monoN hinc, CMRA.Hom.validN g hv⟩

@[rocq_alias authURF]
abbrev AuthURF (T : COFE.OFunctorPre) [URFunctor T] : COFE.OFunctorPre :=
  fun A B _ _ => Auth (T A B)

instance instURFunctorAuthURF {T : COFE.OFunctorPre} [URFunctor T]
    [RFunctorAffine T] : URFunctor (AuthURF T) where
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

instance {T : COFE.OFunctorPre} [URFunctor T] [RFunctorAffine T] :
    RFunctorAffine (AuthURF T) where
  affine := inferInstance

@[rocq_alias authURF_contractive]
instance instURFunctorContractiveAuthURF {T : COFE.OFunctorPre} [URFunctorContractive T]
    [RFunctorAffine T] : URFunctorContractive (AuthURF T) where
  map_contractive.1 h x := by
    apply map_ne <;> apply URFunctorContractive.map_contractive.1 h

@[rocq_alias authRF]
abbrev AuthRF (T : COFE.OFunctorPre) [URFunctor T] : COFE.OFunctorPre :=
  fun A B _ _ => Auth (T A B)

instance instRFunctorAuthRF {T : COFE.OFunctorPre} [URFunctor T]
    [RFunctorAffine T] : RFunctor (AuthRF T) where
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

instance {T : COFE.OFunctorPre} [URFunctor T] [RFunctorAffine T] :
    RFunctorAffine (AuthRF T) where
  affine := inferInstance

@[rocq_alias authRF_contractive]
instance instRFunctorContractiveAuthRF {T : COFE.OFunctorPre} [URFunctorContractive T]
    [RFunctorAffine T] : RFunctorContractive (AuthRF T) where
  map_contractive.1 h x := by
    apply View.map_ne <;> apply URFunctorContractive.map_contractive.1 h

end Auth
