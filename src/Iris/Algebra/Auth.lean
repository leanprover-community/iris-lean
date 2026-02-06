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

open OFE CMRA UCMRA View

/-!
## Definition of the view relation for the authoritative camera.

`auth_view_rel n a b` holds when `b ≼{n} a` and `✓{n} a`.

Rocq: `auth_view_rel_raw`
-/
def AuthViewRel [UCMRA A] : ViewRel A A := fun n a b => b ≼{n} a ∧ ✓{n} a

namespace AuthViewRel

variable [UCMRA A]

/-- Rocq: `auth_view_rel_raw_mono`, `auth_view_rel_raw_valid`, `auth_view_rel_raw_unit` -/
instance : IsViewRel (AuthViewRel (A := A)) where
  mono := by
    intro _ a1 b1 n2 a2 b2 ⟨hinc, hv⟩ ha hb hn
    refine ⟨?_, validN_ne ha (validN_of_le hn hv)⟩
    calc b2 ≼{n2} b1 := hb
         _  ≼{n2} a1 := incN_of_incN_le hn hinc
         _  ≼{n2} a2 := ha.to_incN
  rel_validN n a b := fun ⟨hinc, hv⟩ => validN_of_incN hinc hv
  rel_unit n := ⟨unit, incN_refl unit, unit_valid.validN⟩

theorem authViewRel_unit_iff {n : Nat} {a : A} : AuthViewRel n a unit ↔ ✓{n} a :=
  ⟨(·.2), (⟨incN_unit, ·⟩)⟩

theorem authViewRel_exists_iff {n : Nat} {b : A} : (∃ a, AuthViewRel n a b) ↔ ✓{n} b :=
  ⟨fun ⟨_, h⟩ => IsViewRel.rel_validN _ _ _ h, (⟨b, incN_refl b, ·⟩)⟩

/-- Rocq: `auth_view_rel_discrete` -/
instance [OFE.Discrete A] [CMRA.Discrete A] : IsViewRelDiscrete (AuthViewRel (A := A)) where
  discrete _ _ _ h := ⟨incN_of_inc _ ((inc_iff_incN 0).mpr h.1), (discrete_valid h.2).validN⟩

end AuthViewRel


/-! ## Definition and operations on the authoritative camera -/

abbrev Auth (F : Type _) (A : Type _) [UFraction F] [UCMRA A] :=
  View F (AuthViewRel (A := A))

namespace Auth
variable [UFraction F] [UCMRA A]

/-- Rocq: `authO` -/
instance : OFE (Auth F A) := View.instOFE
/-- Rocq: `authR` -/
instance : CMRA (Auth F A) := View.instCMRA
/-- Rocq: `authUR` -/
instance : UCMRA (Auth F A) := View.instUCMRA

abbrev auth (dq : DFrac F) (a : A) : Auth F A := View.Auth dq a
abbrev authFull (a : A) : Auth F A := Auth (DFrac.own One.one) a
abbrev frag (b : A) : Auth F A := Frag b

notation "●{" dq "} " a => auth dq a
notation "● " a => authFull a
notation "◯ " b => frag b

nonrec instance auth_ne {dq : DFrac F} : NonExpansive (auth dq : A → Auth F A) :=
  auth_ne

nonrec instance frag_ne : NonExpansive (frag : A → Auth F A) :=
  frag_ne

nonrec theorem auth_dist_inj {n : Nat} {dq1 dq2 : DFrac F} {a1 a2 : A}
    (h : (●{dq1} a1) ≡{n}≡ ●{dq2} a2) : dq1 = dq2 ∧ a1 ≡{n}≡ a2 :=
  ⟨auth_inj_frac h, dist_of_auth_dist h⟩

theorem auth_inj {dq1 dq2 : DFrac F} {a1 a2 : A} (h : (●{dq1} a1) ≡ ●{dq2} a2) :
    dq1 = dq2 ∧ a1 ≡ a2 := ⟨h.1.1, equiv_dist.mpr fun _ => dist_of_auth_dist h.dist⟩

theorem frag_dist_inj {n : Nat} {b1 b2 : A} (h : (◯ b1 : Auth F A) ≡{n}≡ ◯ b2) : b1 ≡{n}≡ b2 :=
  dist_of_frag_dist h

theorem frag_inj {b1 b2 : A} (h : (◯ b1 : Auth F A) ≡ ◯ b2) : b1 ≡ b2 :=
  equiv_dist.mpr fun _ => dist_of_frag_dist h.dist

nonrec theorem auth_discrete {dq : DFrac F} {a : A} (ha : DiscreteE a) (hu : DiscreteE (unit : A)) :
    DiscreteE (●{dq} a) := auth_discrete ha hu

nonrec theorem frag_discrete {a : A} (hb : DiscreteE a) : DiscreteE (◯ a : Auth F A) :=
  frag_discrete hb

/-! ## Operations -/
nonrec theorem auth_dfrac_op {dq1 dq2 : DFrac F} {a : A} :
    (●{dq1 • dq2} a) ≡ (●{dq1} a) • (●{dq2} a) :=
  auth_op_auth_eqv

-- TODO: auth_auth_dfrac_is_op

theorem frag_op {b1 b2 : A} : (◯ (b1 • b2) : Auth F A) = ((◯ b1 : Auth F A) • ◯ b2) :=
  frag_op_eq

nonrec theorem frag_inc_of_inc {b1 b2 : A} (h : b1 ≼ b2) : (◯ b1 : Auth F A) ≼ ◯ b2 :=
  frag_inc_of_inc h

nonrec theorem frag_core {b : A} : core (◯ b : Auth F A) = ◯ (core b) :=
  frag_core

theorem auth_both_core_discarded :
    core ((●{.discard} a) • ◯ b : Auth F A) ≡ (●{.discard} a) • ◯ (core b) :=
  auth_discard_op_frag_core

theorem auth_both_core_frac {q : F} {a b : A} :
    core ((●{.own q} a) • ◯ b : Auth F A) ≡ ◯ (core b) :=
  auth_own_op_frag_core

/-- Rocq: `auth_auth_core_id` -/
nonrec instance {a : A} : CoreId (●{.discard} a : Auth F A) :=
  instCoreIdAuthDiscard

/-- Rocq: `auth_frag_core_id` -/
nonrec instance {b : A} [CoreId b] : CoreId (◯ b : Auth F A) :=
  instCoreIdFrag

/-- Rocq: `auth_both_core_id` -/
nonrec instance {a : A} {b : A} [CoreId b] :
    CoreId ((●{.discard} a : Auth F A) • ◯ b) :=
  instCoreIdOpAuthDiscardFrag

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
    (h : ✓{n} ((●{dq1} a) • ●{dq2} b)) : a ≡{n}≡ b :=
  dist_of_validN_auth h

theorem auth_dfrac_op_inv {dq1 dq2 : DFrac F} {a b : A}
    (h : ✓ ((●{dq1} a) • ●{dq2} b)) : a ≡ b :=
  eqv_of_valid_auth h

theorem auth_dfrac_op_inv_L [Leibniz A] {dq1 dq2 : DFrac F} {a b : A}
    (h : ✓ ((●{dq1} a) • ●{dq2} b)) : a = b :=
  Leibniz.eq_of_eqv (auth_dfrac_op_inv h)


theorem auth_dfrac_validN {n : Nat} {dq : DFrac F} {a : A} :
    (✓{n} (●{dq} a)) ↔ (✓ dq ∧ ✓{n} a) := by
  rw [auth_validN_iff]
  exact ⟨fun ⟨hdq, _, hv⟩ => ⟨hdq, hv⟩, fun ⟨hdq, hv⟩ => ⟨hdq, incN_unit, hv⟩⟩

theorem auth_validN {n : Nat} {a : A} :
    (✓{n} (● a : Auth F A)) ↔ (✓{n} a) := by
  rw [auth_dfrac_validN]
  exact and_iff_right_iff_imp.mpr fun _ => DFrac.valid_own_one

theorem auth_dfrac_op_validN {n : Nat} {dq1 dq2 : DFrac F} {a1 a2 : A} :
    (✓{n} ((●{dq1} a1) • ●{dq2} a2)) ↔ (✓ (dq1 • dq2) ∧ a1 ≡{n}≡ a2 ∧ ✓{n} a1) := by
  rw [View.auth_op_auth_validN_iff]
  exact ⟨fun ⟨hdq, ha, ⟨_, hv⟩⟩ => ⟨hdq, ha, hv⟩, fun ⟨hdq, ha, hv⟩ => ⟨hdq, ha, incN_unit, hv⟩⟩

theorem auth_op_validN {n : Nat} {a1 a2 : A} : (✓{n} ((● a1 : Auth F A) • ● a2)) ↔ False :=
  auth_one_op_auth_one_validN_iff

theorem frag_validN {n : Nat} {b : A} : (✓{n} (◯ b : Auth F A)) ↔ (✓{n} b) := by
  rw [frag_validN_iff, AuthViewRel.authViewRel_exists_iff]

theorem frag_op_validN {n : Nat} {b1 b2 : A} :
    (✓{n} ((◯ b1 : Auth F A) • ◯ b2)) ↔ (✓{n} (b1 • b2)) := by
  rw [← frag_op]; exact frag_validN

theorem both_dfrac_validN {n : Nat} {dq : DFrac F} {a b : A} :
    (✓{n} ((●{dq} a) • ◯ b)) ↔ (✓ dq ∧ b ≼{n} a ∧ ✓{n} a) :=
  auth_op_frag_validN_iff

theorem both_validN {n : Nat} {a b : A} :
    (✓{n} ((● a : Auth F A) • ◯ b)) ↔ (b ≼{n} a ∧ ✓{n} a) :=
  auth_one_op_frag_validN_iff

theorem auth_dfrac_valid {dq : DFrac F} {a : A} : (✓ (●{dq} a : Auth F A)) ↔ (✓ dq ∧ ✓ a) := by
  rw [auth_valid_iff]
  refine and_congr_right fun _ => ?_
  rw [valid_iff_validN]
  exact forall_congr' fun _ => AuthViewRel.authViewRel_unit_iff

theorem auth_valid {a : A} : (✓ (● a : Auth F A)) ↔ (✓ a) := by
  rw [auth_dfrac_valid]
  exact and_iff_right_iff_imp.mpr fun _ => DFrac.valid_own_one

/-- Rocq: `auth_dfrac_op_valid` -/
theorem auth_dfrac_op_valid {dq1 dq2 : DFrac F} {a1 a2 : A} :
    (✓ ((●{dq1} a1) • ●{dq2} a2)) ↔ (✓ (dq1 • dq2) ∧ a1 ≡ a2 ∧ ✓ a1) := by
  rw [auth_op_auth_valid_iff]
  constructor
  · exact fun ⟨hdq, ha, hr⟩ => ⟨hdq, ha, valid_iff_validN.mpr (hr · |>.2)⟩
  · exact fun ⟨hdq, ha, hv⟩ => ⟨hdq, ha, fun _ => ⟨incN_unit, hv.validN⟩⟩

theorem auth_op_valid {a1 a2 : A} : (✓ ((● a1 : Auth F A) • ● a2)) ↔ False :=
  auth_one_op_auth_one_valid_iff

theorem frag_valid {b : A} : (✓ (◯ b : Auth F A)) ↔ (✓ b) := by
  simp only [valid_iff_validN]
  exact forall_congr' fun _ => frag_validN

theorem frag_op_valid {b1 b2 : A} : (✓ ((◯ b1 : Auth F A) • ◯ b2)) ↔ (✓ (b1 • b2)) := by
  rw [← frag_op]; exact frag_valid

theorem both_dfrac_valid {dq : DFrac F} {a b : A} :
    (✓ ((●{dq} a) • ◯ b)) ↔ (✓ dq ∧ (∀ n, b ≼{n} a) ∧ ✓ a) := by
  simp only [valid_iff_validN]
  constructor
  · refine fun h => ⟨fun n => (both_dfrac_validN.mp (h n)).1, fun n => ?_, fun n => ?_⟩
    · exact (both_dfrac_validN.mp (h n)).2.1
    · exact (both_dfrac_validN.mp (h n)).2.2
  · exact fun ⟨hdq, hinc, hv⟩ n => both_dfrac_validN.mpr ⟨hdq n, hinc n, hv n⟩

theorem auth_both_valid {a b : A} :
    (✓ ((● a : Auth F A) • ◯ b)) ↔ ((∀ n, b ≼{n} a) ∧ ✓ a) := by
  rw [both_dfrac_valid]
  constructor
  · exact fun ⟨_, hinc, hv⟩ => ⟨hinc, hv⟩
  · exact fun ⟨hinc, hv⟩ => ⟨DFrac.valid_own_one, hinc, hv⟩

/-- Note: The reverse direction only holds if the camera is discrete. -/
theorem auth_both_dfrac_valid_2 {dq : DFrac F} {a b : A} (hdq : ✓ dq) (ha : ✓ a)
    (hb : b ≼ a) : ✓ ((●{dq} a) • ◯ b) :=
  both_dfrac_valid.mpr ⟨hdq, (incN_of_inc · hb), ha⟩

theorem auth_both_valid_2 {a b : A} (ha : ✓ a) (hb : b ≼ a) :
    ✓ ((● a : Auth F A) • ◯ b) :=
  auth_both_dfrac_valid_2 DFrac.valid_own_one ha hb

theorem both_dfrac_valid_discrete [CMRA.Discrete A] {dq : DFrac F} {a b : A} :
    (✓ ((●{dq} a : Auth F A) • ◯ b)) ↔ (✓ dq ∧ b ≼ a ∧ ✓ a) := by
  constructor
  · intro h
    have ⟨hdq, hinc, hv⟩ := both_dfrac_valid.mp h
    exact ⟨hdq, (inc_iff_incN 0).mpr (hinc 0), hv⟩
  · exact fun ⟨hdq, hinc, hv⟩ => auth_both_dfrac_valid_2 hdq hv hinc

theorem auth_both_valid_discrete [CMRA.Discrete A] {a b : A} :
    (✓ ((● a : Auth F A) • ◯ b)) ↔ (b ≼ a ∧ ✓ a) := by
  rw [both_dfrac_valid_discrete]
  constructor
  · exact fun ⟨_, hinc, hv⟩ => ⟨hinc, hv⟩
  · exact fun ⟨hinc, hv⟩ => ⟨DFrac.valid_own_one, hinc, hv⟩

/-! ## Inclusion -/

theorem auth_dfrac_includedN {n : Nat} {dq1 dq2 : DFrac F} {a1 a2 b : A} :
    ((●{dq1} a1) ≼{n} ((●{dq2} a2) • ◯ b)) ↔ ((dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2) :=
  auth_incN_auth_op_frag_iff

theorem auth_dfrac_included {dq1 dq2 : DFrac F} {a1 a2 b : A} :
    ((●{dq1} a1) ≼ ((●{dq2} a2) • ◯ b)) ↔ ((dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡ a2) :=
  auth_inc_auth_op_frag_iff

theorem auth_includedN {n : Nat} {a1 a2 b : A} :
    ((● a1 : Auth F A) ≼{n} ((● a2) • ◯ b)) ↔ (a1 ≡{n}≡ a2) :=
  auth_one_incN_auth_one_op_frag_iff

theorem auth_included {a1 a2 b : A} :
    ((● a1 : Auth F A) ≼ ((● a2) • ◯ b)) ↔ (a1 ≡ a2) :=
  auth_one_inc_auth_one_op_frag_iff

theorem frag_includedN {n : Nat} {dq : DFrac F} {a b1 b2 : A} :
    ((◯ b1) ≼{n} ((●{dq} a) • ◯ b2)) ↔ (b1 ≼{n} b2) :=
  frag_incN_auth_op_frag_iff

theorem frag_included {dq : DFrac F} {a b1 b2 : A} : ((◯ b1) ≼ ((●{dq} a) • ◯ b2)) ↔ (b1 ≼ b2) :=
  frag_inc_auth_op_frag_iff

/-- The weaker `auth_both_included` lemmas below are a consequence of the
    `auth_included` and `frag_included` lemmas above. -/
theorem auth_both_dfrac_includedN {n : Nat} {dq1 dq2 : DFrac F} {a1 a2 b1 b2 : A} :
    (((●{dq1} a1) • ◯ b1) ≼{n} ((●{dq2} a2) • ◯ b2)) ↔
      ((dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2 ∧ b1 ≼{n} b2) :=
  auth_op_frag_incN_auth_op_frag_iff

theorem auth_both_dfrac_included {dq1 dq2 : DFrac F} {a1 a2 b1 b2 : A} :
    (((●{dq1} a1) • ◯ b1) ≼ ((●{dq2} a2) • ◯ b2)) ↔
      ((dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡ a2 ∧ b1 ≼ b2) :=
  auth_op_frag_inc_auth_op_frag_iff

theorem auth_both_includedN {n : Nat} {a1 a2 b1 b2 : A} :
    (((● a1 : Auth F A) • ◯ b1) ≼{n} ((● a2) • ◯ b2)) ↔ (a1 ≡{n}≡ a2 ∧ b1 ≼{n} b2) :=
  auth_one_op_frag_incN_auth_one_op_frag_iff

theorem auth_both_included {a1 a2 b1 b2 : A} :
    (((● a1 : Auth F A) • ◯ b1) ≼ ((● a2) • ◯ b2)) ↔ (a1 ≡ a2 ∧ b1 ≼ b2) :=
  auth_one_op_frag_inc_auth_one_op_frag_iff

/-! ## Updates -/

theorem auth_update {a b a' b' : A} (hup : (a, b) ~l~> (a', b')) :
    ((● a : Auth F A) • ◯ b) ~~> (● a') • ◯ b' := by
  refine auth_one_op_frag_update fun n bf ⟨⟨c, hinc⟩, hv⟩ => ?_
  have ha_eq : a ≡{n}≡ b •? some (bf • c) := by
    simp only [CMRA.op?]; exact hinc.trans assoc.symm.dist
  have ⟨hv', ha'_eq⟩ := hup n (some (bf • c)) hv ha_eq
  simp only [CMRA.op?] at ha'_eq
  exact ⟨⟨c, ha'_eq.trans assoc.dist⟩, hv'⟩

theorem auth_update_alloc {a a' b' : A} (hup : (a, unit) ~l~> (a', b')) :
    (● a : Auth F A) ~~> (● a') • ◯ b' :=
  Update.equiv_left unit_right_id (auth_update hup)

theorem auth_update_dealloc {a b a' : A} (hup : (a, b) ~l~> (a', unit)) :
    ((● a : Auth F A) • ◯ b) ~~> ● a' :=
  Update.equiv_right unit_right_id (auth_update hup)

theorem auth_update_auth {a a' b' : A} (hup : (a, unit) ~l~> (a', b')) :
    (● a : Auth F A) ~~> ● a' :=
  Update.trans (auth_update_alloc hup) Update.op_l

theorem auth_update_auth_persist {dq : DFrac F} {a : A} :
    (●{dq} a : Auth F A) ~~> ●{DFrac.discard} a :=
  auth_discard

theorem auth_updateP_auth_unpersist [IsSplitFraction F] {a : A} :
    (●{DFrac.discard} a : Auth F A) ~~>:
      fun k => ∃ q, k = ●{DFrac.own q} a :=
  auth_acquire

theorem auth_updateP_both_unpersist [IsSplitFraction F] {a b : A} :
    ((●{DFrac.discard} a : Auth F A) • ◯ b) ~~>:
      fun k => ∃ q, k = ((●{DFrac.own q} a : Auth F A) • ◯ b) :=
  auth_op_frag_acquire

theorem auth_update_dfrac_alloc {dq : DFrac F} {a b : A} [CoreId b] (hb : b ≼ a) :
    (●{dq} a) ~~> (●{dq} a) • ◯ b := by
  refine auth_alloc fun n bf ⟨hinc, hv⟩ => ⟨?_, hv⟩
  have hba : b • a ≡ a := comm.trans (op_core_left_of_inc hb)
  exact (incN_iff_right hba.dist).mp (op_monoN_right b hinc)

theorem auth_local_update {a b0 b1 a' b0' b1' : A} (hup : (b0, b1) ~l~> (b0', b1'))
    (hinc : b0' ≼ a') (hv : ✓ a') :
    ((● a : Auth F A) • ◯ b0, (● a) • ◯ b1) ~l~> ((● a' : Auth F A) • ◯ b0', (● a') • ◯ b1') :=
  view_local_update hup fun n _ => ⟨incN_of_inc n hinc, hv.validN⟩

/-! ## Functor -/

/-- The AuthViewRel is preserved under CMRA homomorphisms. -/
theorem authViewRel_map [UCMRA A'] [UCMRA B'] (g : A' -C> B') (n : Nat) (a : A')
    (b : A') : AuthViewRel n a b → AuthViewRel n (g a) (g b) :=
  fun ⟨hinc, hv⟩ => ⟨CMRA.Hom.monoN g n hinc, CMRA.Hom.validN g hv⟩

abbrev AuthURF (T : COFE.OFunctorPre) [URFunctor T] : COFE.OFunctorPre :=
  fun A B _ _ => Auth F (T A B)

instance instURFunctorAuthURF {T : COFE.OFunctorPre} [URFunctor T] :
    URFunctor (AuthURF (F := F) T) where
  map {A A'} {B B'} _ _ _ _ f g :=
    mapC
      (URFunctor.map (F := T) f g).toHom
      (URFunctor.map (F := T) f g)
      (authViewRel_map (URFunctor.map f g))
  map_ne.ne a b c hx d e hy x :=
    map_ne _ (URFunctor.map_ne.ne hx hy) (URFunctor.map_ne.ne hx hy)
  map_id x := by
    refine .trans ?_ (.of_eq <| map_id x)
    apply map_ext <;> exact URFunctor.map_id
  map_comp f g f' g' x := by
    simp only [mapC]
    refine .trans ?_ (.of_eq (map_compose' ..))
    apply View.map_ext <;> exact URFunctor.map_comp f g f' g'

instance instURFunctorContractiveAuthURF {T : COFE.OFunctorPre} [URFunctorContractive T] :
    URFunctorContractive (AuthURF (F := F) T) where
  map_contractive.1 h x := by
    apply map_ne <;> apply URFunctorContractive.map_contractive.1 h

abbrev AuthRF (T : COFE.OFunctorPre) [URFunctor T] : COFE.OFunctorPre :=
  fun A B _ _ => Auth F (T A B)

instance instRFunctorAuthRF {T : COFE.OFunctorPre} [URFunctor T] :
    RFunctor (AuthRF (F := F) T) where
  map {A A'} {B B'} _ _ _ _ f g :=
    mapC
      (URFunctor.map (F := T) f g).toHom
      (URFunctor.map (F := T) f g)
      (authViewRel_map (URFunctor.map f g))
  map_ne.ne a b c hx d e hy x := by
    apply map_ne <;> exact URFunctor.map_ne.ne hx hy
  map_id x := by
    refine .trans ?_ (.of_eq <| map_id x)
    apply map_ext <;> exact URFunctor.map_id
  map_comp f g f' g' x := by
    simp only [mapC]
    rw [← map_compose']
    apply map_ext <;> exact URFunctor.map_comp f g f' g'

instance instRFunctorContractiveAuthRF {T : COFE.OFunctorPre} [URFunctorContractive T] :
    RFunctorContractive (AuthRF (F := F) T) where
  map_contractive.1 h x := by
    apply View.map_ne <;> apply URFunctorContractive.map_contractive.1 h

end Auth
