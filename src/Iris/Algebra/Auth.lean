/-
Copyright (c) 2025 Alexander Bai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bai
-/
import Iris.Algebra.View
import Iris.Algebra.LocalUpdates

/-!
# Authoritative Camera

The authoritative camera has 2 types of elements:
- the authoritative element `●{dq} a`
-  and the fragment `◯ b`
-/

open Iris

open OFE CMRA UCMRA

/-!
## Definition of the view relation for the authoritative camera.

`auth_view_rel n a b` holds when `b ≼{n} a` and `✓{n} a`.

Rocq: `auth_view_rel_raw`
-/
def AuthViewRel [UCMRA A] : ViewRel A A := fun n a b => b ≼{n} a ∧ ✓{n} a

namespace authViewRel

variable [UCMRA A]

/-- Rocq: `auth_view_rel_raw_mono`, `auth_view_rel_raw_valid`, `auth_view_rel_raw_unit` -/
instance : IsViewRel (AuthViewRel (A := A)) where
  mono := by
    intro n1 a1 b1 n2 a2 b2 ⟨Hinc, Hv⟩ Ha Hb Hn
    constructor
    · calc b2 ≼{n2} b1 := Hb
           _ ≼{n2} a1 := incN_of_incN_le Hn Hinc
           _ ≼{n2} a2 := Ha.to_incN
    · exact validN_ne Ha (validN_of_le Hn Hv)
  rel_validN n a b := by
    intro ⟨Hinc, Hv⟩
    exact validN_of_incN Hinc Hv
  rel_unit n := ⟨unit, incN_refl unit, unit_valid.validN⟩

theorem authViewRel_unit {n : Nat} {a : A} : AuthViewRel n a unit ↔ ✓{n} a := by
  constructor
  · intro ⟨_, Hv⟩; exact Hv
  · intro Hv; exact ⟨incN_unit, Hv⟩

theorem authViewRel_exists {n : Nat} {b : A} : (∃ a, AuthViewRel n a b) ↔ ✓{n} b := by
  constructor
  · intro ⟨a, Hrel⟩; exact IsViewRel.rel_validN n a b Hrel
  · intro Hv; exact ⟨b, incN_refl b, Hv⟩

/-- Rocq: `auth_view_rel_discrete` -/
instance [OFE.Discrete A] [CMRA.Discrete A] : IsViewRelDiscrete (AuthViewRel (A := A)) where
  discrete n a b := by
    intro ⟨Hinc, Hv⟩
    constructor
    · exact incN_of_inc n ((inc_iff_incN 0).mpr Hinc)
    · exact (discrete_valid Hv).validN

end authViewRel


/-! ## Definition and operations on the authoritative camera -/

abbrev Auth (F : Type _) (A : Type _) [UFraction F] [UCMRA A] := View F (AuthViewRel (A := A))

namespace Auth
variable [UFraction F] [UCMRA A]

/-- Rocq: `authO` -/
instance : OFE (Auth F A) := View.instOFE
/-- Rocq: `authR` -/
instance : CMRA (Auth F A) := View.instCMRA
/-- Rocq: `authUR` -/
instance : UCMRA (Auth F A) := View.instUCMRA

abbrev auth (dq : DFrac F) (a : A) : Auth F A := View.Auth dq a
abbrev authFull (a : A) : Auth F A := View.Auth (DFrac.own One.one) a
abbrev frag (b : A) : Auth F A := View.Frag b

notation "●{" dq "} " a => auth dq a
notation "● " a => authFull a
notation "◯ " b => frag b

instance auth_ne {dq : DFrac F} : NonExpansive (auth dq : A → Auth F A) := View.auth_ne
instance frag_ne : NonExpansive (frag : A → Auth F A) := View.frag_ne

theorem auth_dist_inj {n : Nat} {dq1 dq2 : DFrac F} {a1 a2 : A}
    (H : (●{dq1} a1) ≡{n}≡ ●{dq2} a2) : dq1 = dq2 ∧ a1 ≡{n}≡ a2 :=
  ⟨View.auth_inj_frac H, View.dist_of_auth_dist H⟩

theorem auth_inj {dq1 dq2 : DFrac F} {a1 a2 : A}
  (H : (●{dq1} a1) ≡ ●{dq2} a2) : dq1 = dq2 ∧ a1 ≡ a2 :=
    ⟨H.1.1, equiv_dist.mpr fun _ => View.dist_of_auth_dist H.dist⟩

theorem frag_dist_inj {n : Nat} {b1 b2 : A}
    (H : (◯ b1 : Auth F A) ≡{n}≡ ◯ b2) : b1 ≡{n}≡ b2 :=
  View.dist_of_frag_dist H

theorem frag_inj {b1 b2 : A}
    (H : (◯ b1 : Auth F A) ≡ ◯ b2) : b1 ≡ b2 :=
  equiv_dist.mpr fun _ => View.dist_of_frag_dist H.dist


theorem auth_discrete {dq : DFrac F} {a : A} (Ha : DiscreteE a) (Hu : DiscreteE (unit : A)) :
    DiscreteE (●{dq} a) :=
  View.auth_discrete Ha Hu

theorem frag_discrete {a : A} (Hb : DiscreteE a) :
    DiscreteE (◯ a : Auth F A) :=
  View.frag_discrete Hb

instance [OFE.Discrete A] : OFE.Discrete (Auth F A) := inferInstance
instance [OFE.Discrete A] [CMRA.Discrete A] : CMRA.Discrete (Auth F A) := inferInstance


/-! ## Operations -/
theorem auth_dfrac_op {dq1 dq2 : DFrac F} {a : A} :
    (●{dq1 • dq2} a) ≡ (●{dq1} a) • (●{dq2} a) :=
  View.auth_op_auth_eqv

-- TODO: auth_auth_dfrac_is_op

theorem frag_op {b1 b2 : A} : (◯ (b1 • b2) : Auth F A) = ((◯ b1 : Auth F A) • ◯ b2) :=
  View.frag_op_eq

theorem frag_inc_of_inc {b1 b2 : A} (H : b1 ≼ b2) : (◯ b1 : Auth F A) ≼ ◯ b2 :=
  View.frag_inc_of_inc H

theorem frag_core {b : A} : core (◯ b : Auth F A) = ◯ (core b) :=
  View.frag_core

theorem auth_both_core_discarded :
  core ((●{.discard} a) • ◯ b : Auth F A) ≡ (●{.discard} a) • ◯ (core b) :=
  View.auth_discard_op_frag_core

theorem auth_both_core_frac {q : F} {a b : A}:
    core ((●{.own q} a) • ◯ b : Auth F A) ≡ ◯ (core b) :=
  View.auth_own_op_frag_core

/-- Rocq: `auth_auth_core_id` -/
instance {a : A} : CoreId (●{.discard} a : Auth F A) := View.instCoreIdAuthDiscard

/-- Rocq: `auth_frag_core_id` -/
instance {b : A} [CoreId b] : CoreId (◯ b : Auth F A) := View.instCoreIdFrag

/-- Rocq: `auth_both_core_id` -/
instance {a : A} {b : A} [CoreId b] : CoreId ((●{.discard} a : Auth F A) • ◯ b) :=
  View.instCoreIdOpAuthDiscardFrag

-- TODO: auth_frag_is_op
-- TODO: auth_frag_sep_homomorphism

/- TODO: BigOPs
    big_opL_auth_frag
    big_opM_auth_frag
    big_opS_auth_frag
    big_opMS_auth_frag
-/

/-! ## Validity -/

theorem auth_dfrac_op_invN {n : Nat} {dq1 dq2 : DFrac F} {a b : A}
    (H : ✓{n} ((●{dq1} a) • ●{dq2} b)) : a ≡{n}≡ b :=
  View.dist_of_validN_auth H

theorem auth_dfrac_op_inv {dq1 dq2 : DFrac F} {a b : A}
    (H : ✓ ((●{dq1} a) • ●{dq2} b)) : a ≡ b :=
  View.eqv_of_valid_auth H

theorem auth_dfrac_op_inv_L [Leibniz A] {dq1 dq2 : DFrac F} {a b : A}
    (H : ✓ ((●{dq1} a) • ●{dq2} b)) : a = b :=
  Leibniz.eq_of_eqv (auth_dfrac_op_inv H)


theorem auth_dfrac_validN {n : Nat} {dq : DFrac F} {a : A} :
    (✓{n} (●{dq} a)) ↔ (✓ dq ∧ ✓{n} a) := by
  rw [View.auth_validN_iff]
  simp only [AuthViewRel]
  constructor
  · intro ⟨Hdq, _, Hv⟩; exact ⟨Hdq, Hv⟩
  · intro ⟨Hdq, Hv⟩; exact ⟨Hdq, incN_unit, Hv⟩

theorem auth_validN {n : Nat} {a : A} :
    (✓{n} (● a : Auth F A)) ↔ (✓{n} a) := by
  rw [auth_dfrac_validN]
  exact and_iff_right_iff_imp.mpr fun _ => DFrac.valid_own_one


theorem auth_dfrac_op_validN {n : Nat} {dq1 dq2 : DFrac F} {a1 a2 : A} :
    (✓{n} ((●{dq1} a1) • ●{dq2} a2)) ↔ (✓ (dq1 • dq2) ∧ a1 ≡{n}≡ a2 ∧ ✓{n} a1) := by
  rw [View.auth_op_auth_validN_iff]
  simp only [AuthViewRel]
  constructor
  · intro ⟨Hdq, Ha, ⟨_, Hv⟩⟩; exact ⟨Hdq, Ha, Hv⟩
  · intro ⟨Hdq, Ha, Hv⟩; exact ⟨Hdq, Ha, incN_unit, Hv⟩

theorem auth_op_validN {n : Nat} {a1 a2 : A} :
    (✓{n} ((● a1 : Auth F A) • ● a2)) ↔ False :=
  View.auth_one_op_auth_one_validN_iff


theorem frag_validN {n : Nat} {b : A} :
    (✓{n} (◯ b : Auth F A)) ↔ (✓{n} b) := by
  rw [View.frag_validN_iff, authViewRel.authViewRel_exists]

theorem frag_op_validN {n : Nat} {b1 b2 : A} :
    (✓{n} ((◯ b1 : Auth F A) • ◯ b2)) ↔ (✓{n} (b1 • b2)) := by
  rw [← frag_op]; exact frag_validN


theorem both_dfrac_validN {n : Nat} {dq : DFrac F} {a b : A} :
    (✓{n} ((●{dq} a) • ◯ b)) ↔ (✓ dq ∧ b ≼{n} a ∧ ✓{n} a) := by
  rw [View.auth_op_frag_validN_iff]; simp only [AuthViewRel]

theorem both_validN {n : Nat} {a b : A} :
    (✓{n} ((● a : Auth F A) • ◯ b)) ↔ (b ≼{n} a ∧ ✓{n} a) := by
  exact View.auth_one_op_frag_validN_iff

theorem auth_dfrac_valid {dq : DFrac F} {a : A} :
    (✓ (●{dq} a : Auth F A)) ↔ (✓ dq ∧ ✓ a) := by
  rw [View.auth_valid_iff]
  refine and_congr_right fun _ => ?_
  rw [valid_iff_validN]
  exact forall_congr' fun _ => authViewRel.authViewRel_unit

theorem auth_valid {a : A} :
    (✓ (● a : Auth F A)) ↔ (✓ a) := by
  rw [auth_dfrac_valid]
  exact and_iff_right_iff_imp.mpr fun _ => DFrac.valid_own_one

/-- Rocq: `auth_dfrac_op_valid` -/
theorem auth_dfrac_op_valid {dq1 dq2 : DFrac F} {a1 a2 : A} :
    (✓ ((●{dq1} a1) • ●{dq2} a2)) ↔ (✓ (dq1 • dq2) ∧ a1 ≡ a2 ∧ ✓ a1) := by
  rw [View.auth_op_auth_valid_iff]
  simp only [AuthViewRel]
  constructor
  · intro ⟨Hdq, Ha, Hr⟩
    refine ⟨Hdq, Ha, valid_iff_validN.mpr fun n => (Hr n).2⟩
  · intro ⟨Hdq, Ha, Hv⟩
    exact ⟨Hdq, Ha, fun n => ⟨incN_unit, Hv.validN⟩⟩

theorem auth_op_valid {a1 a2 : A} :
    (✓ ((● a1 : Auth F A) • ● a2)) ↔ False :=
  View.auth_one_op_auth_one_valid_iff

theorem frag_valid {b : A} :
    (✓ (◯ b : Auth F A)) ↔ (✓ b) := by
  simp only [valid_iff_validN]
  exact forall_congr' fun _ => frag_validN

theorem frag_op_valid {b1 b2 : A} :
    (✓ ((◯ b1 : Auth F A) • ◯ b2)) ↔ (✓ (b1 • b2)) := by
  rw [← frag_op]; exact frag_valid

theorem both_dfrac_valid {dq : DFrac F} {a b : A} :
    (✓ ((●{dq} a) • ◯ b)) ↔ (✓ dq ∧ (∀ n, b ≼{n} a) ∧ ✓ a) := by
  simp only [valid_iff_validN]
  constructor
  · intro H
    refine ⟨fun n => (both_dfrac_validN.mp (H n)).1, fun n => ?_, fun n => ?_⟩
    · exact (both_dfrac_validN.mp (H n)).2.1
    · exact (both_dfrac_validN.mp (H n)).2.2
  · intro ⟨Hdq, Hinc, Hv⟩ n
    exact both_dfrac_validN.mpr ⟨Hdq n, Hinc n, Hv n⟩

theorem auth_both_valid {a b : A} :
    (✓ ((● a : Auth F A) • ◯ b)) ↔ ((∀ n, b ≼{n} a) ∧ ✓ a) := by
  rw [both_dfrac_valid]
  constructor
  · intro ⟨_, Hinc, Hv⟩; exact ⟨Hinc, Hv⟩
  · intro ⟨Hinc, Hv⟩; exact ⟨DFrac.valid_own_one, Hinc, Hv⟩

/-- Note: The reverse direction only holds if the camera is discrete. -/
theorem auth_both_dfrac_valid_2 {dq : DFrac F} {a b : A}
    (Hdq : ✓ dq) (Ha : ✓ a) (Hb : b ≼ a) : ✓ ((●{dq} a) • ◯ b) :=
  both_dfrac_valid.mpr ⟨Hdq, fun n => incN_of_inc n Hb, Ha⟩

theorem auth_both_valid_2 {a b : A}
    (Ha : ✓ a) (Hb : b ≼ a) : ✓ ((● a : Auth F A) • ◯ b) :=
  auth_both_dfrac_valid_2 DFrac.valid_own_one Ha Hb

theorem both_dfrac_valid_discrete [CMRA.Discrete A] {dq : DFrac F} {a b : A} :
    (✓ ((●{dq} a : Auth F A) • ◯ b)) ↔ (✓ dq ∧ b ≼ a ∧ ✓ a) := by
  constructor
  · intro H
    have ⟨Hdq, Hinc, Hv⟩ := both_dfrac_valid.mp H
    exact ⟨Hdq, (inc_iff_incN 0).mpr (Hinc 0), Hv⟩
  · intro ⟨Hdq, Hinc, Hv⟩
    exact auth_both_dfrac_valid_2 Hdq Hv Hinc

theorem auth_both_valid_discrete [CMRA.Discrete A] {a b : A} :
    (✓ ((● a : Auth F A) • ◯ b)) ↔ (b ≼ a ∧ ✓ a) := by
  rw [both_dfrac_valid_discrete]
  constructor
  · intro ⟨_, Hinc, Hv⟩; exact ⟨Hinc, Hv⟩
  · intro ⟨Hinc, Hv⟩; exact ⟨DFrac.valid_own_one, Hinc, Hv⟩

/-! ## Inclusion -/

theorem auth_dfrac_includedN {n : Nat} {dq1 dq2 : DFrac F} {a1 a2 b : A} :
    ((●{dq1} a1) ≼{n} ((●{dq2} a2) • ◯ b)) ↔ ((dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2) :=
  View.auth_incN_auth_op_frag_iff

theorem auth_dfrac_included {dq1 dq2 : DFrac F} {a1 a2 b : A} :
    ((●{dq1} a1) ≼ ((●{dq2} a2) • ◯ b)) ↔ ((dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡ a2) :=
  View.auth_inc_auth_op_frag_iff

theorem auth_includedN {n : Nat} {a1 a2 b : A} :
    ((● a1 : Auth F A) ≼{n} ((● a2) • ◯ b)) ↔ (a1 ≡{n}≡ a2) :=
  View.auth_one_incN_auth_one_op_frag_iff

theorem auth_included {a1 a2 b : A} :
    ((● a1 : Auth F A) ≼ ((● a2) • ◯ b)) ↔ (a1 ≡ a2) :=
  View.auth_one_inc_auth_one_op_frag_iff


theorem frag_includedN {n : Nat} {dq : DFrac F} {a b1 b2 : A} :
    ((◯ b1) ≼{n} ((●{dq} a) • ◯ b2)) ↔ (b1 ≼{n} b2) :=
  View.frag_incN_auth_op_frag_iff

theorem frag_included {dq : DFrac F} {a b1 b2 : A} :
    ((◯ b1) ≼ ((●{dq} a) • ◯ b2)) ↔ (b1 ≼ b2) :=
  View.frag_inc_auth_op_frag_iff

/-- The weaker `auth_both_included` lemmas below are a consequence of the
    `auth_included` and `frag_included` lemmas above. -/
theorem auth_both_dfrac_includedN {n : Nat} {dq1 dq2 : DFrac F} {a1 a2 b1 b2 : A} :
    (((●{dq1} a1) • ◯ b1) ≼{n} ((●{dq2} a2) • ◯ b2)) ↔
      ((dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2 ∧ b1 ≼{n} b2) :=
  View.auth_op_frag_incN_auth_op_frag_iff

theorem auth_both_dfrac_included {dq1 dq2 : DFrac F} {a1 a2 b1 b2 : A} :
    (((●{dq1} a1) • ◯ b1) ≼ ((●{dq2} a2) • ◯ b2)) ↔
      ((dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡ a2 ∧ b1 ≼ b2) :=
  View.auth_op_frag_inc_auth_op_frag_iff

theorem auth_both_includedN {n : Nat} {a1 a2 b1 b2 : A} :
    (((● a1 : Auth F A) • ◯ b1) ≼{n} ((● a2) • ◯ b2)) ↔ (a1 ≡{n}≡ a2 ∧ b1 ≼{n} b2) :=
  View.auth_one_op_frag_incN_auth_one_op_frag_iff

theorem auth_both_included {a1 a2 b1 b2 : A} :
    (((● a1 : Auth F A) • ◯ b1) ≼ ((● a2) • ◯ b2)) ↔ (a1 ≡ a2 ∧ b1 ≼ b2) :=
  View.auth_one_op_frag_inc_auth_one_op_frag_iff

/-! ## Updates -/

theorem auth_update {a b a' b' : A}
    (Hup : (a, b) ~l~> (a', b')) :
    ((● a : Auth F A) • ◯ b) ~~> (● a') • ◯ b' := by
  apply View.auth_one_op_frag_update
  intro n bf ⟨⟨c, Hinc⟩, Hv⟩
  have Ha_eq : a ≡{n}≡ b •? some (bf • c) := by
    simp only [CMRA.op?]; exact Hinc.trans assoc.symm.dist
  have ⟨Hv', Ha'_eq⟩ := Hup n (some (bf • c)) Hv Ha_eq
  simp only [CMRA.op?] at Ha'_eq
  exact ⟨⟨c, Ha'_eq.trans assoc.dist⟩, Hv'⟩


theorem auth_update_alloc {a a' b' : A}
    (Hup : (a, unit) ~l~> (a', b')) :
    (● a : Auth F A) ~~> (● a') • ◯ b' :=
  Update.equiv_left unit_right_id (auth_update Hup)

theorem auth_update_dealloc {a b a' : A}
    (Hup : (a, b) ~l~> (a', unit)) :
    ((● a : Auth F A) • ◯ b) ~~> ● a' :=
  Update.equiv_right unit_right_id (auth_update Hup)

theorem auth_update_auth {a a' b' : A}
    (Hup : (a, unit) ~l~> (a', b')) :
    (● a : Auth F A) ~~> ● a' :=
  Update.trans (auth_update_alloc Hup) Update.op_l


theorem auth_update_auth_persist {dq : DFrac F} {a : A} :
    (●{dq} a : Auth F A) ~~> ●{DFrac.discard} a :=
  View.auth_discard
theorem auth_updateP_auth_unpersist [IsSplitFraction F] {a : A} :
    (●{DFrac.discard} a : Auth F A) ~~>: fun k => ∃ q, k = ●{DFrac.own q} a :=
  View.auth_acquire

theorem auth_updateP_both_unpersist [IsSplitFraction F] {a b : A} :
    ((●{DFrac.discard} a : Auth F A) • ◯ b) ~~>:
      fun k => ∃ q, k = ((●{DFrac.own q} a : Auth F A) • ◯ b) :=
  View.auth_op_frag_acquire

theorem auth_update_dfrac_alloc {dq : DFrac F} {a b : A} [CoreId b]
    (Hb : b ≼ a) : (●{dq} a) ~~> (●{dq} a) • ◯ b :=
  View.auth_alloc fun n bf ⟨Hinc, Hv⟩ => by
    constructor
    · have Hba : b • a ≡ a := comm.trans (op_core_left_of_inc Hb)
      exact (incN_iff_right Hba.dist).mp (op_monoN_right b Hinc)
    · exact Hv

theorem auth_local_update {a b0 b1 a' b0' b1' : A}
    (Hup : (b0, b1) ~l~> (b0', b1'))
    (Hinc : b0' ≼ a') (Hv : ✓ a') :
    ((● a : Auth F A) • ◯ b0, (● a) • ◯ b1) ~l~>
    ((● a' : Auth F A) • ◯ b0', (● a') • ◯ b1') :=
  View.view_local_update Hup fun n _ => ⟨incN_of_inc n Hinc, Hv.validN⟩

/-! ## Functor -/

/-- The authViewRel is preserved under CMRA homomorphisms. -/
theorem authViewRel_map [UCMRA A'] [UCMRA B'] (g : A' -C> B') (n : Nat) (a : A') (b : A') :
    AuthViewRel n a b → AuthViewRel n (g a) (g b) := by
  intro ⟨Hinc, Hv⟩
  constructor
  · exact CMRA.Hom.monoN g n Hinc
  · exact CMRA.Hom.validN g Hv

abbrev AuthURF (T : COFE.OFunctorPre) [URFunctor T] : COFE.OFunctorPre :=
  fun A B _ _ => Auth F (T A B)

instance instURFunctorAuthURF {T : COFE.OFunctorPre} [URFunctor T] :
    URFunctor (AuthURF (F := F) T) where
  map {A A'} {B B'} _ _ _ _ f g :=
    View.mapC
      (URFunctor.map (F := T) f g).toHom
      (URFunctor.map (F := T) f g)
      (authViewRel_map (URFunctor.map f g))
  map_ne.ne a b c Hx d e Hy x := by
    simp [View.mapC]
    apply View.map_ne <;> intro y <;> exact URFunctor.map_ne.ne Hx Hy y
  map_id x := by
    simp only [View.mapC]
    conv => rhs; rw [← View.map_id (R := AuthViewRel) x]
    apply View.map_ext <;> apply URFunctor.map_id
  map_comp f g f' g' x := by
    simp only [View.mapC]
    rw [← View.map_compose']
    apply View.map_ext <;> apply URFunctor.map_comp f g f' g'

instance instURFunctorContractiveAuthURF {T : COFE.OFunctorPre} [URFunctorContractive T] :
    URFunctorContractive (AuthURF (F := F) T) where
  map_contractive.1 H x := by
    apply View.map_ne <;> apply URFunctorContractive.map_contractive.1 H

abbrev AuthRF (T : COFE.OFunctorPre) [URFunctor T] : COFE.OFunctorPre :=
  fun A B _ _ => Auth F (T A B)

instance instRFunctorAuthRF {T : COFE.OFunctorPre} [URFunctor T] :
    RFunctor (AuthRF (F := F) T) where
  map {A A'} {B B'} _ _ _ _ f g :=
    View.mapC
      (URFunctor.map (F := T) f g).toHom
      (URFunctor.map (F := T) f g)
      (authViewRel_map (URFunctor.map f g))
  map_ne.ne a b c Hx d e Hy x := by
    simp [View.mapC]
    apply View.map_ne <;> intro y <;> exact URFunctor.map_ne.ne Hx Hy y
  map_id x := by
    simp only [View.mapC]
    conv => rhs; rw [← View.map_id x]
    apply View.map_ext <;> apply URFunctor.map_id
  map_comp f g f' g' x := by
    simp only [View.mapC]
    rw [← View.map_compose']
    apply View.map_ext <;> apply URFunctor.map_comp f g f' g'

instance instRFunctorContractiveAuthRF {T : COFE.OFunctorPre} [URFunctorContractive T] :
    RFunctorContractive (AuthRF (F := F) T) where
  map_contractive.1 H x := by
    apply View.map_ne <;> apply URFunctorContractive.map_contractive.1 H

end Auth
