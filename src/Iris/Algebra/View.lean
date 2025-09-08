/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE
import Iris.Algebra.Frac
import Iris.Algebra.DFrac
import Iris.Algebra.Agree
import Iris.Algebra.Updates
import Iris.Algebra.LocalUpdates

open Iris

abbrev view_rel (A B : Type _) := Nat → A → B → Prop

class ViewRel [OFE A] [UCMRA B] (R : view_rel A B) where
  mono : R n1 a1 b1 → a1 ≡{n2}≡ a2 → b2 ≼{n2} b1 → n2 ≤ n1 → R n2 a2 b2
  rel_validN n a b : R n a b → ✓{n} b
  rel_unit n : ∃ a, R n a UCMRA.unit

class ViewRelDiscrete [OFE A] [UCMRA B] (R : view_rel A B) extends ViewRel R where
  discrete n a b : R 0 a b → R n a b

namespace viewrel
open ViewRel DFrac

variable [OFE A] [UCMRA B] {R : view_rel A B} [ViewRel R]

theorem ne (Ha : a1 ≡{n}≡ a2) (Hb : b1 ≡{n}≡ b2) : R n a1 b1 ↔ R n a2 b2 :=
  ⟨(mono · Ha Hb.symm.to_incN n.le_refl), (mono · Ha.symm Hb.to_incN n.le_refl)⟩

theorem eqv_ne (Ha : a1 ≡ a2) (Hb : b1 ≡ b2) : R n a1 b1 ↔ R n a2 b2 :=
  ne Ha.dist Hb.dist

end viewrel

structure View (F : Type _) {A B : Type _} (R : view_rel A B) where
  π_auth : Option ((DFrac F) × Agree A)
  π_frag : B

abbrev View.Auth [UCMRA B] {R : view_rel A B} (dq : DFrac F) (a : A) : View F R :=
  ⟨some (dq, toAgree a), UCMRA.unit⟩

abbrev View.Frag {R : view_rel A B} (b : B) : View F R := ⟨none, b⟩

notation "●V{" dq "} " a => View.Auth dq a
notation "●V " a => View.Auth (DFrac.own One.one) a
notation "◯V " b => View.Frag b

namespace View
section ofe

variable [OFE A] [OFE B] {R : view_rel A B}

abbrev equiv (x y : View F R) : Prop := x.π_auth ≡ y.π_auth ∧ x.π_frag ≡ y.π_frag
abbrev dist (n : Nat) (x y : View F R) : Prop := x.π_auth ≡{n}≡ y.π_auth ∧ x.π_frag ≡{n}≡ y.π_frag

instance : OFE (View F R) where
  Equiv := equiv
  Dist := dist
  dist_eqv := {
    refl _ := ⟨OFE.Dist.of_eq rfl, OFE.Dist.of_eq rfl⟩
    symm H := ⟨H.1.symm, H.2.symm⟩
    trans H1 H2 := ⟨H1.1.trans H2.1, H1.2.trans H2.2⟩
  }
  equiv_dist :=
    ⟨fun H _ => ⟨H.1.dist, H.2.dist⟩,
     fun H => ⟨OFE.equiv_dist.mpr (H · |>.1), OFE.equiv_dist.mpr (H · |>.2)⟩⟩
  dist_lt H Hn := ⟨OFE.dist_lt H.1 Hn, OFE.dist_lt H.2 Hn⟩

instance View.mk.ne : OFE.NonExpansive₂ (View.mk : _ → _ → View F R) := ⟨fun _ _ _ Ha _ _ Hb => ⟨Ha, Hb⟩⟩
instance View.π_auth.ne : OFE.NonExpansive (View.π_auth : View F R → _) := ⟨fun _ _ _ H => H.1⟩
instance View.π_frag.ne : OFE.NonExpansive (View.π_frag : View F R → _) := ⟨fun _ _ _ H => H.2⟩

theorem View.is_discrete {ag : Option ((DFrac F) × Agree A)} (Ha : OFE.DiscreteE ag) (Hb : OFE.DiscreteE b) :
  OFE.DiscreteE (α := View F R) (View.mk ag b) := ⟨fun H => ⟨Ha.discrete H.1, Hb.discrete H.2⟩⟩

open OFE in
instance [Discrete A] [Discrete B] : Discrete (View F R) where
  discrete_0 H := ⟨discrete_0 H.1, discrete_0 H.2⟩

theorem View.auth_inj_frac [UCMRA B] {q1 q2 : DFrac F} {a1 a2 : A} {n} (H : (●V{q1} a1 : View F R) ≡{n}≡ ●V{q2} a2) :
    q1 = q2 := H.1.1

theorem View.auth_inj_ag [UCMRA B] {q1 q2 : DFrac F} {a1 a2 : A} {n} (H : (●V{q1} a1 : View F R) ≡{n}≡ ●V{q2} a2) :
    a1 ≡{n}≡ a2 := toAgree.inj H.1.2

theorem View.frag_inj [UCMRA B] {b1 b2 : B} {n} (H : (◯V b1 : View F R) ≡{n}≡ ◯V b2) :
    b1 ≡{n}≡ b2 := H.2

theorem View.auth_is_discrete [UFraction F] [UCMRA B] {dq a} (Ha : OFE.DiscreteE a) (He : OFE.DiscreteE (UCMRA.unit : B)) :
    OFE.DiscreteE (●V{dq} a : View F R) := by
  refine View.is_discrete ?_ He
  apply OFE.Option.some_is_discrete
  apply OFE.prod.is_discrete DFrac.is_discrete
  apply Agree.toAgree.is_discrete
  exact Ha

theorem View.frag_is_discrete [UCMRA B] {b : B} (Hb : OFE.DiscreteE b) : (OFE.DiscreteE (◯V b : View F R)) :=
  View.is_discrete OFE.Option.none_is_discrete Hb

end ofe

section cmra
open ViewRel toAgree OFE

variable [UFraction F] [OFE A] [IB : UCMRA B] {R : view_rel A B} [ViewRel R]

theorem ViewRel.of_agree_dst_iff (Hb : b' ≡{n}≡ b) :
    (∃ a', toAgree a ≡{n}≡ toAgree a' ∧ R n a' b') ↔ R n a b := by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · rcases H with ⟨_, HA, HR⟩
    exact mono HR (inj HA.symm) Hb.symm.to_incN n.le_refl
  · exact ⟨a, .rfl, mono H .rfl Hb.to_incN n.le_refl⟩

instance auth_ne {dq : DFrac F} : NonExpansive (Auth dq : A → View F R) where
  ne _ _ _ H := by
    refine View.mk.ne.ne ?_ .rfl
    refine some_dist_some.mpr ⟨.rfl, ?_⟩
    simp only
    exact OFE.NonExpansive.ne H

instance auth_ne₂ : NonExpansive₂ (Auth : DFrac F → A → View F R) where
  ne _ _ _ Hq _ _ Hf := by
    unfold View.Auth
    refine (NonExpansive₂.ne ?_ .rfl)
    refine NonExpansive.ne ?_
    exact dist_prod_ext Hq (NonExpansive.ne Hf)

instance frag_ne : NonExpansive (Frag : B → View F R) where
  ne _ _ _ H := View.mk.ne.ne .rfl H

@[simp] def Valid (v : View F R) : Prop :=
  match v.π_auth with
  | some (dq, ag) => ✓ dq ∧ (∀ n, ∃ a, ag ≡{n}≡ toAgree a ∧ R n a (π_frag v))
  | none => ∀ n, ∃ a, R n a (π_frag v)

@[simp] def ValidN (n : Nat) (v : View F R) : Prop :=
  match v.π_auth with
  | some (dq, ag) => ✓{n} dq ∧ (∃ a, ag ≡{n}≡ toAgree a ∧ R n a (π_frag v))
  | none => ∃ a, R n a (π_frag v)

@[simp] def Pcore (v : View F R) : Option (View F R) :=
  some <| View.mk (CMRA.core v.1) (CMRA.core v.2)

@[simp] def Op (v1 v2 : View F R) : View F R :=
  View.mk (v1.1 • v2.1) (v1.2 • v2.2)

instance : CMRA (View F R) where
  pcore := Pcore
  op := Op
  ValidN := ValidN
  Valid := Valid
  op_ne.ne n x1 x2 H := by
    refine View.mk.ne.ne ?_ ?_
    · exact cmraOption.op_ne.ne <| NonExpansive.ne H
    · exact IB.op_ne.ne <| NonExpansive.ne H
  pcore_ne {n x y} cx H := by
    simp only [Pcore, Option.some.injEq]
    rintro ⟨rfl⟩
    exists ⟨CMRA.core y.π_auth, CMRA.core y.π_frag⟩
    exact ⟨rfl, OFE.Dist.core H.1, OFE.Dist.core H.2⟩
  validN_ne {n x1 x2} := by
    rintro ⟨Hl, Hr⟩
    rcases x1 with ⟨_|⟨q1, ag1⟩, b1⟩ <;>
    rcases x2 with ⟨_|⟨q2, ag2⟩, b2⟩ <;>
    simp_all
    · exact fun x H => ⟨x, ViewRel.mono H .rfl Hr.symm.to_incN n.le_refl⟩
    intro Hq a Hag HR
    refine ⟨CMRA.discrete_valid <| DFrac_CMRA.validN_ne Hl.1 Hq, ?_⟩
    refine ⟨a, ?_⟩
    refine ⟨Hl.2.symm.trans Hag, ?_⟩
    refine ViewRel.mono HR .rfl ?_ n.le_refl
    exact Dist.to_incN Hr.symm
  valid_iff_validN {x} := by
    simp only [Valid, ValidN]; split
    · exact ⟨fun H n => ⟨H.1, H.2 n⟩, fun H => ⟨(H 0).1, fun n => (H n).2⟩⟩
    · exact Eq.to_iff rfl
  validN_succ {x n} := by
    simp only [ValidN]
    split
    · refine fun H => ⟨H.1, ?_⟩
      rcases H.2 with ⟨ag, Ha⟩; exists ag
      refine ⟨Dist.le Ha.1 n.le_succ, ?_⟩
      exact mono Ha.2 .rfl (CMRA.incN_refl x.π_frag) n.le_succ
    · rintro ⟨z, HR⟩
      exact ⟨z, mono HR .rfl (CMRA.incN_refl _) n.le_succ⟩
  validN_op_left {n x y} := by
    rcases x with ⟨_|⟨q1, ag1⟩, b1⟩ <;>
    rcases y with ⟨_|⟨q2, ag2⟩, b2⟩ <;>
    simp [CMRA.op, optionOp]
    · exact fun a Hr => ⟨a, mono Hr .rfl (CMRA.incN_op_left n b1 b2) n.le_refl⟩
    · exact fun _ a _ Hr => ⟨a, mono Hr .rfl (CMRA.incN_op_left n b1 b2) n.le_refl⟩
    · exact fun Hq a H Hr => ⟨Hq, ⟨a, ⟨H, mono Hr .rfl (CMRA.incN_op_left n b1 b2) n.le_refl⟩⟩⟩
    · refine fun Hq a H Hr => ⟨CMRA.validN_op_left Hq, ⟨a, ?_, ?_⟩⟩
      · refine .trans ?_ H
        refine .trans Agree.idemp.symm.dist ?_
        exact CMRA.op_ne.ne <| Agree.op_invN (Agree.validN_ne H.symm trivial)
      · exact ViewRel.mono Hr .rfl (CMRA.incN_op_left n b1 b2) n.le_refl
  assoc := OFE.NonExpansive₂.eqv CMRA.assoc CMRA.assoc
  comm := OFE.NonExpansive₂.eqv CMRA.comm CMRA.comm
  pcore_op_left {x _} := by
    simp only [Pcore, Option.some.injEq]
    exact fun H => H ▸ OFE.NonExpansive₂.eqv (CMRA.core_op x.π_auth) (CMRA.core_op x.π_frag)
  pcore_idem {_ cx} := by
    simp only [Pcore, Option.some.injEq, OFE.some_eqv_some]
    rcases cx
    simp only [mk.injEq, and_imp]
    intro H1 H2
    constructor
    · simp only; exact H1 ▸ CMRA.core_idem _
    · exact H2 ▸ CMRA.core_idem _

  -- Here

  pcore_op_mono := by
    apply pcore_op_mono_of_core_op_mono
    let f : (Option ((DFrac F) × Agree A) × B) → View F R := fun x => ⟨x.1, x.2⟩
    let g : View F R → (Option ((DFrac F) × Agree A) × B) := fun x => (x.1, x.2)
    let opM' (x : View F R) (y : Option (View F R)) : View F R :=
      match y with | some y => Op x y | none => x

    have g_pcore_0 {y : View F R} : CMRA.pcore (g y) ≡ g <$> Pcore y := by
      rcases y with ⟨x, b⟩
      simp only [pcore, Option.map_eq_map, Option.map, g]
      simp [CMRA.pcore, Prod.pcore, optionCore]
      simp [CMRA.pcore_eq_core]
      rfl

    have g_pcore {y cy : View F R} : Pcore y ≡ some cy ↔ CMRA.pcore (g y) ≡ some (g cy) := by
      suffices y.Pcore ≡ some cy ↔ g <$> y.Pcore ≡ some (g cy) by
        exact ⟨g_pcore_0.trans ∘ this.mp, this.mpr ∘ g_pcore_0.symm.trans⟩
      refine Iff.trans OFE.equiv_dist (Iff.trans ?_ OFE.equiv_dist.symm)
      exact ⟨fun H n => H n, fun H n => H n⟩

    have g_opM_f {x y} : g (opM' y (f x)) ≡ CMRA.op (g y) x := by
      simp [opM', g, f, CMRA.op, Prod.op]

    rintro y1 cy y2 ⟨z, Hy2⟩ Hy1
    let Lcore := (@CMRA.pcore_mono' _ _ (g y1) (g y2) (g cy) ?G1 ?G2)
    case G1 => exists (g z)
    case G2 => exact g_pcore.mp <| OFE.Equiv.of_eq Hy1
    rcases Lcore with ⟨cx, Hcgy2, ⟨x, Hcx⟩⟩
    have Hcx' : cx ≡ g (opM' cy (f x)) := Hcx
    have Hcgy2' : CMRA.pcore (g y2) ≡ some (g (opM' cy (f x))) := by rw [Hcgy2]; exact Hcx
    have Hcgy2'' : Pcore y2 ≡ some (opM' cy (f x)) := g_pcore.mpr Hcgy2'
    generalize HC : y2.Pcore = C
    rw [HC] at Hcgy2''
    cases C; exact Hcgy2''.elim
    rename_i cy'
    refine ⟨cy', ⟨rfl, ?_⟩⟩
    exists (f x)
  extend {n x y1 y2} Hv He := by
    let g : View F R → (Option ((DFrac F) × Agree A) × B) := fun x => (x.1, x.2)
    have H2 := @CMRA.extend _ _ n (g x) (g y1) (g y2) ?G1 He
    case G1 =>
      simp_all [ValidN, CMRA.ValidN, Prod.ValidN, g, optionValidN]
      rcases x with ⟨_|⟨q1, ag1⟩, b1⟩ <;> simp_all only
      · refine ⟨trivial, ?_⟩
        rcases Hv with ⟨_, Ha⟩
        apply ViewRel.rel_validN _ _ _ Ha
      · rcases Hv with ⟨Hq, ⟨a, ⟨Ha1, Ha2⟩⟩⟩
        refine ⟨⟨trivial, ?_⟩, ?_⟩
        · exact Agree.validN_ne Ha1.symm trivial
        · exact ViewRel.rel_validN _ _ _ Ha2
    rcases H2 with ⟨z1, z2, Hze, Hz1, Hz2⟩
    exists ⟨z1.1, z1.2⟩
    exists ⟨z2.1, z2.2⟩

instance [OFE.Discrete A] [CMRA.Discrete B] [ViewRelDiscrete R] : CMRA.Discrete (View F R) where
  discrete_valid := by
    simp [CMRA.ValidN, ValidN, CMRA.Valid, Valid]
    intro x
    split
    · rintro ⟨H1, ⟨a, H2, H3⟩⟩
      refine ⟨H1, fun n => ⟨a, ⟨?_, ?_⟩⟩⟩
      · exact OFE.equiv_dist.mp (OFE.Discrete.discrete_0 H2) _
      · exact ViewRelDiscrete.discrete _ _ _ H3
    · rintro ⟨a, H⟩ _
      exact ⟨a, ViewRelDiscrete.discrete _ _ _ H⟩

instance : UCMRA (View F R) where
  unit := ⟨UCMRA.unit, UCMRA.unit⟩
  unit_valid := ViewRel.rel_unit
  unit_left_id := ⟨UCMRA.unit_left_id, UCMRA.unit_left_id⟩
  pcore_unit := ⟨by rfl, CMRA.core_eqv_self UCMRA.unit⟩

theorem auth_op_eqv : (●V{dq1 • dq2} a : View F R) ≡ (●V{dq1} a) • ●V{dq2} a :=
  ⟨⟨rfl, Agree.idemp.symm⟩, UCMRA.unit_left_id.symm⟩

theorem frag_op_eq : (◯V (b1 • b2) : View F R) = ((◯V b1) • ◯V b2 : View F R):= rfl

theorem frag_inc_of_inc (H : b1 ≼ b2) : (◯V b1 : View F R) ≼ ◯V b2 := by
  rcases H with ⟨c, H⟩
  refine CMRA.inc_of_inc_of_eqv ?_ (NonExpansive.eqv H.symm)
  rw [View.frag_op_eq]
  exact CMRA.inc_op_left _ _

theorem core_frag : CMRA.core (◯V b : View F R) = ◯V (CMRA.core b) := rfl

theorem core_discard_op_frag_eqv : CMRA.core ((●V{.discard} a) • ◯V b : View F R) ≡ (●V{.discard} a) • ◯V (CMRA.core b) :=
  ⟨.rfl, (CMRA.core_ne.eqv UCMRA.unit_left_id).trans UCMRA.unit_left_id.symm⟩

theorem core_own_op_frag_eqv : CMRA.core ((●V{.own q} a) • ◯V b : View F R) ≡ ◯V (CMRA.core b) :=
  ⟨trivial, CMRA.core_ne.eqv UCMRA.unit_left_id⟩

instance : CMRA.CoreId (●V{.discard} a : View F R) where
  core_id := ⟨.rfl, CMRA.core_eqv_self UCMRA.unit⟩

instance [CMRA.CoreId b] : CMRA.CoreId (◯V b : View F R) where
  core_id := ⟨.rfl, CMRA.coreId_iff_core_eqv_self.mp (by trivial)⟩

instance [CMRA.CoreId b] : CMRA.CoreId ((●V{.discard} a : View F R) • ◯V b) where
  core_id := by
    refine ⟨.rfl, ?_⟩
    refine (CMRA.core_ne.eqv UCMRA.unit_left_id).trans ?_
    refine (CMRA.coreId_iff_core_eqv_self.mp (by trivial)).trans ?_
    refine UCMRA.unit_left_id.symm

theorem dst_of_validN_auth (H : ✓{n} ((●V{dq1} a1 : View F R) • ●V{dq2} a2)) : a1 ≡{n}≡ a2 := by
  rcases H with ⟨_, _, H, _⟩
  refine toAgree.inj (Agree.op_invN ?_)
  exact Agree.validN_ne H.symm trivial

theorem eqv_of_valid_auth (H : ✓ ((●V{dq1} a1 : View F R) • ●V{dq2} a2)) : a1 ≡ a2 :=
  OFE.equiv_dist.mpr fun _ => dst_of_validN_auth H.validN

theorem auth_validN_iff : ✓{n} (●V{dq} a : View F R) ↔ ✓{n}dq ∧ R n a UCMRA.unit :=
  and_congr_right fun _ => ViewRel.of_agree_dst_iff .rfl

theorem auth_one_validN_iff n a : ✓{n} (●V a : View F R) ↔ R n a UCMRA.unit :=
  ⟨(auth_validN_iff.mp · |>.2), (auth_validN_iff.mpr ⟨UFraction.one_whole.1, ·⟩)⟩

theorem auth_op_auth_validN_iff :
    ✓{n} ((●V{dq1} a1 : View F R) • ●V{dq2} a2) ↔ ✓(dq1 • dq2) ∧ a1 ≡{n}≡ a2 ∧ R n a1 UCMRA.unit := by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · let Ha' : a1 ≡{n}≡ a2 := dst_of_validN_auth H
    rcases H with ⟨Hq, _, Ha, HR⟩
    refine ⟨Hq, Ha', ViewRel.mono HR ?_ CMRA.incN_unit n.le_refl⟩
    refine .trans ?_ Ha'.symm
    refine toAgree.inj ?_
    apply Ha.symm.trans
    apply CMRA.op_commN.trans
    apply (CMRA.op_ne.ne (toAgree.ne.ne Ha')).trans
    apply Agree.idemp
  · simp [CMRA.op, CMRA.ValidN, ValidN, optionOp, Prod.op]
    refine ⟨H.1, a1, ?_, ?_⟩
    · exact (CMRA.op_ne.ne <| toAgree.ne.ne H.2.1.symm).trans Agree.idemp.dist
    · refine ViewRel.mono H.2.2 .rfl ?_ n.le_refl
      exact OFE.Dist.to_incN <| CMRA.unit_left_id_dist UCMRA.unit

theorem auth_one_op_validN_iff : ✓{n} ((●V a1 : View F R) • ●V a2) ↔ False := by
  refine auth_op_auth_validN_iff.trans ?_
  simp only [iff_false, not_and]
  intro _
  refine (UFraction.one_whole (α := F)).2 ?_ |>.elim
  exists 1

theorem frag_validN_iff : ✓{n} (◯V b : View F R) ↔ ∃ a, R n a b := by rfl

theorem auth_op_frag_validN_iff : ✓{n} ((●V{dq} a : View F R) • ◯V b) ↔ ✓dq ∧ R n a b :=
  and_congr_right (fun _ => ViewRel.of_agree_dst_iff <| CMRA.unit_left_id_dist b)

theorem auth_one_op_frag_validN_iff : ✓{n} ((●V a : View F R) • ◯V b) ↔ R n a b :=
  auth_op_frag_validN_iff.trans <| and_iff_right_iff_imp.mpr (fun _ => valid_own_one)

theorem auth_valid_iff : ✓ (●V{dq} a : View F R) ↔ ✓dq ∧ ∀ n, R n a UCMRA.unit :=
  and_congr_right (fun _=> forall_congr' fun _ => ViewRel.of_agree_dst_iff .rfl)

theorem auth_one_valid_iff : ✓ (●V a : View F R) ↔ ∀ n, R n a UCMRA.unit :=
  auth_valid_iff.trans <| and_iff_right_iff_imp.mpr (fun _ => valid_own_one)

theorem auth_op_auth_valid_iff : ✓ ((●V{dq1} a1 : View F R) • ●V{dq2} a2) ↔ ✓(dq1 • dq2) ∧ a1 ≡ a2 ∧ ∀ n, R n a1 UCMRA.unit := by
  refine CMRA.valid_iff_validN.trans ?_
  refine ⟨fun H => ?_, fun H n => ?_⟩
  · simp [CMRA.Valid, valid, Auth, CMRA.op, op, optionOp, CMRA.ValidN, ValidN] at H
    let Hn (n) := dst_of_validN_auth (H n)
    refine ⟨(H 0).1, OFE.equiv_dist.mpr Hn, fun n => ?_⟩
    · rcases (H n) with ⟨_, _, Hl, H⟩
      apply ViewRel.mono H ?_ CMRA.incN_unit n.le_refl
      apply toAgree.inj
      apply Hl.symm.trans
      exact (CMRA.op_ne.ne <| toAgree.ne.ne (Hn _).symm).trans Agree.idemp.dist
  · exact auth_op_auth_validN_iff.mpr ⟨H.1, H.2.1.dist, H.2.2 n⟩

theorem auth_one_op_auth_one_valid_iff : ✓ ((●V a1 : View F R) • ●V a2) ↔ False := by
  refine auth_op_auth_valid_iff.trans ?_
  simp [CMRA.op, op, CMRA.Valid, op, valid]
  intro _
  refine (UFraction.one_whole (α := F)).2 ?_ |>.elim
  exists 1

theorem frag_valid_iff : ✓ (◯V b : View F R) ↔ ∀ n, ∃ a, R n a b := by rfl

theorem auth_op_frag_valid_iff : ✓ ((●V{dq} a : View F R) • ◯V b) ↔ ✓dq ∧ ∀ n, R n a b :=
  and_congr_right (fun _ => forall_congr' fun _ => ViewRel.of_agree_dst_iff <| CMRA.unit_left_id_dist b)

theorem auth_one_op_frag_valid_iff : ✓ ((●V a : View F R) • ◯V b) ↔ ∀ n, R n a b :=
  auth_op_frag_valid_iff.trans <| and_iff_right_iff_imp.mpr (fun _ => valid_own_one)

theorem auth_incN_auth_op_frag_iff : (●V{dq1} a1 : View F R) ≼{n} ((●V{dq2} a2) • ◯V b) ↔ (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2 := by
  refine ⟨?_, ?_⟩
  · simp only [Auth, Frag, CMRA.IncludedN, CMRA.op, op, optionOp, Prod.op]
    rintro ⟨(_|⟨dqf, af⟩),⟨⟨x1, x2⟩, y⟩⟩
    · exact ⟨Or.inr x1.symm, toAgree.inj x2.symm⟩
    · simp_all only []
      apply And.intro
      · left; exists dqf
      · apply toAgree.incN.mp; exists af
  · intro H
    -- simp only [auth, frag, CMRA.IncludedN, CMRA.op, op, optionOp, Prod.op]
    rcases H with ⟨(⟨z, HRz⟩| HRa2), HRb⟩
    · -- have _ := @View.auth_op_eqv
      apply (CMRA.incN_iff_right <| ?G).mp
      case G =>
        apply OFE.equiv_dist.mp
        apply CMRA.comm
      apply (CMRA.incN_iff_right <| ?G).mp
      case G =>
        apply CMRA.op_ne.ne
        apply OFE.NonExpansive₂.ne HRz.symm HRb
      apply (CMRA.incN_iff_right <| ?G).mp
      case G =>
        apply CMRA.op_ne.ne
        apply OFE.equiv_dist.mp
        apply View.auth_op_eqv.symm
      apply (CMRA.incN_iff_right <| ?G).mp
      case G =>
        apply CMRA.op_ne.ne
        apply OFE.equiv_dist.mp
        apply CMRA.comm
      apply (CMRA.incN_iff_right <| ?G).mp
      case G =>
        apply OFE.equiv_dist.mp
        apply CMRA.assoc.symm
      apply (CMRA.incN_iff_right <| ?G).mp
      case G =>
        apply OFE.equiv_dist.mp
        apply CMRA.comm
      exists ((◯V b) • ●V{z} a1)
    · exists (◯V b)
      refine .trans (OFE.equiv_dist.mp CMRA.comm _) (.trans ?_ (OFE.equiv_dist.mp CMRA.comm _))
      apply CMRA.op_ne.ne
      rw [HRa2]
      exact OFE.NonExpansive₂.ne rfl HRb.symm

theorem auth_inc_auth_op_frag_iff : ((●V{dq1} a1 : View F R) ≼ (●V{dq2} a2 : View F R) • ◯V b) ↔ (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡ a2 := by
  refine ⟨fun H => ⟨?_, ?_⟩, fun H => ?_⟩
  · exact auth_incN_auth_op_frag_iff (n := 0) |>.mp (CMRA.incN_of_inc _ H) |>.1
  · refine OFE.equiv_dist.mpr (fun n => ?_)
    exact auth_incN_auth_op_frag_iff |>.mp (CMRA.incN_of_inc _ H) |>.2
  · rcases H with ⟨(⟨q, Hq⟩|Hq), Ha⟩
    · apply (CMRA.inc_iff_right <| ?G).mp
      case G =>
        apply OFE.Equiv.symm
        apply CMRA.comm.trans
        apply CMRA.op_ne.eqv
        exact NonExpansive₂.eqv Hq Ha.symm
      apply (CMRA.inc_iff_right <| ?G1).mp
      case G1 =>
        apply CMRA.op_ne.eqv
        apply View.auth_op_eqv.symm
      apply (CMRA.inc_iff_right <| CMRA.comm).mp
      apply (CMRA.inc_iff_right <| CMRA.assoc).mp
      exists ((●V{q} a1) • ◯V b)
    · exists (◯V b)
      refine .trans CMRA.comm (.trans ?_ CMRA.comm )
      apply CMRA.op_ne.eqv
      rw [Hq]
      exact OFE.NonExpansive₂.eqv rfl Ha.symm

theorem auth_one_incN_auth_one_op_frag_iff : (●V a1 : View F R) ≼{n} ((●V a2) • ◯V b) ↔ a1 ≡{n}≡ a2 :=
  auth_incN_auth_op_frag_iff.trans <| and_iff_right_iff_imp.mpr <| fun _ => .inr rfl

theorem auth_one_inc_auth_one_op_frag_iff : (●V a1 : View F R) ≼ ((●V a2) • ◯V b) ↔ a1 ≡ a2 :=
  auth_inc_auth_op_frag_iff.trans <| and_iff_right_iff_imp.mpr <| fun _ => .inr rfl

theorem frag_incN_auth_frag_iff : (◯V b1 : View F R) ≼{n} ((●V{p} a) • ◯V b2) ↔ b1 ≼{n} b2 := by
  constructor
  · rintro ⟨xf, ⟨_, Hb⟩⟩
    simp [Auth, Frag, CMRA.op, op] at Hb
    have Hb' : b2 ≡{n}≡ b1 • xf.π_frag := by
      apply OFE.Dist.trans
      apply OFE.Dist.symm
      apply OFE.equiv_dist.mp
      apply UCMRA.unit_left_id
      apply Hb
    apply (CMRA.incN_iff_right <| Hb'.symm).mp
    exists xf.π_frag
  · rintro ⟨bf, Hbf⟩
    apply (CMRA.incN_iff_right <| ?G).mp
    case G =>
      apply CMRA.op_ne.ne
      apply NonExpansive.ne Hbf.symm
    rw [View.frag_op_eq]
    apply (CMRA.incN_iff_right <| ?G).mp
    case G =>
      apply OFE.equiv_dist.mp
      apply CMRA.comm
    apply (CMRA.incN_iff_right <| ?G).mp
    case G =>
      apply OFE.equiv_dist.mp
      apply CMRA.assoc
    exists ((◯V bf) • ●V{p} a)

theorem frag_inc_auth_op_frag : (◯V b1 : View F R) ≼ ((●V{p} a) • ◯V b2) ↔ b1 ≼ b2 := by
  constructor
  · rintro ⟨xf, ⟨_, Hb⟩⟩
    simp [Auth, Frag, CMRA.op, op] at Hb
    have Hb' : b2 ≡ b1 • xf.π_frag := by
      apply OFE.Equiv.trans
      apply OFE.Equiv.symm
      apply UCMRA.unit_left_id
      apply Hb
    apply (CMRA.inc_iff_right <| Hb'.symm).mp
    exists xf.π_frag
  · rintro ⟨bf, Hbf⟩
    apply (CMRA.inc_iff_right <| ?G).mp
    case G =>
      apply CMRA.op_ne.eqv
      apply NonExpansive.eqv Hbf.symm
    rw [View.frag_op_eq]
    apply (CMRA.inc_iff_right <| ?G).mp
    case G => apply CMRA.comm
    apply (CMRA.inc_iff_right <| ?G).mp
    case G =>
      apply CMRA.assoc
    exists ((◯V bf) • ●V{p} a)

theorem auth_op_frag_incN_auth_op_frag_iff :
    ((●V{dq1} a1 : View F R) • ◯V b1) ≼{n} ((●V{dq2} a2) • ◯V b2) ↔
      (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2 ∧ b1 ≼{n} b2 := by
  constructor
  · intro H
    rw [← and_assoc]
    constructor
    · apply (auth_incN_auth_op_frag_iff (R := R)).mp
      apply CMRA.incN_trans ?_ H
      exact CMRA.incN_op_left n (●V{dq1} a1) (◯V b1)
    · apply (frag_incN_auth_frag_iff (R := R) (F := F)).mp
      apply CMRA.incN_trans (CMRA.incN_op_right _ _ _)
      apply H
  · rintro ⟨H0, H1, ⟨bf, H2⟩⟩
    apply (CMRA.incN_iff_right <| ?G).mp
    case G =>
      apply CMRA.op_ne.ne
      apply NonExpansive.ne
      apply OFE.Dist.symm
      apply H2.trans
      apply OFE.equiv_dist.mp
      apply CMRA.comm
    rewrite [View.frag_op_eq]
    apply (CMRA.incN_iff_right <| ?G).mp
    case G =>
      apply OFE.equiv_dist.mp
      apply CMRA.assoc.symm
    refine CMRA.op_monoN_left (◯V b1) ?_
    apply auth_incN_auth_op_frag_iff.mpr
    exact ⟨H0, H1⟩

theorem auth_op_frag_inc_auth_op_frag_iff : ((●V{dq1} a1 : View F R) • ◯V b1) ≼ ((●V{dq2} a2) • ◯V b2) ↔
      (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡ a2 ∧ b1 ≼ b2 := by
  constructor
  · intro H
    rw [← and_assoc]
    constructor
    · apply (auth_inc_auth_op_frag_iff (R := R)).mp
      apply CMRA.inc_trans ?_ H
      exact CMRA.inc_op_left (●V{dq1} a1) (◯V b1)
    · apply (frag_inc_auth_op_frag (R := R) (F := F)).mp
      apply CMRA.inc_trans (CMRA.inc_op_right _ _)
      apply H
  · rintro ⟨H0, H1, ⟨bf, H2⟩⟩
    apply (CMRA.inc_iff_right <| ?G).mp
    case G =>
      apply CMRA.op_ne.eqv
      apply NonExpansive.eqv
      apply OFE.Equiv.symm
      apply H2.trans
      apply CMRA.comm
    rewrite [View.frag_op_eq]
    apply (CMRA.inc_iff_right <| ?G).mp
    case G =>
      apply CMRA.assoc.symm
    refine CMRA.op_mono_left (◯V b1) ?_
    apply auth_inc_auth_op_frag_iff.mpr
    exact ⟨H0, H1⟩

theorem auth_one_op_frag_incN_auth_one_op_frag_iff : ((●V a1 : View F R) • ◯V b1) ≼{n} ((●V a2) • ◯V b2) ↔ (a1 ≡{n}≡ a2 ∧ b1 ≼{n} b2) :=
  auth_op_frag_incN_auth_op_frag_iff.trans <| and_iff_right_iff_imp.mpr <| fun _ => .inr rfl

theorem auth_op_one_frag_inc_auth_one_op_frag_iff : ((●V a1 : View F R) • ◯V b1) ≼ ((●V a2) • ◯V b2) ↔ a1 ≡ a2 ∧ b1 ≼ b2 :=
  auth_op_frag_inc_auth_op_frag_iff.trans <| and_iff_right_iff_imp.mpr <| fun _ => .inr rfl

end cmra

section updates

variable [UFraction F] [OFE A] [IB : UCMRA B] {R : view_rel A B} [ViewRel R]

theorem auth_op_frag_update {Pab : A → B → Prop}
    (Hup : ∀ n bf, R n a (b • bf) → ∃ a' b', Pab a' b' ∧ R n a' (b' • bf)) :
    ((●V a) • ◯V b : View F R) ~~>: fun k => ∃ a' b', k = ((●V a') • ◯V b' : View F R) ∧ Pab a' b' := by
  refine UpdateP.total.mpr (fun n ⟨ag, bf⟩ => ?_)
  rcases ag with (_|⟨dq, ag⟩)
  · intro H
    simp [CMRA.op, op, CMRA.ValidN, optionOp, ValidN] at H
    obtain ⟨_, a0, He', Hrel'⟩ := H
    have He := toAgree.inj He'; clear He'
    have Hrel : R n a (b • bf) := by
      apply ViewRel.mono Hrel' He.symm _ n.le_refl
      apply Iris.OFE.Dist.to_incN
      refine CMRA.comm.dist.trans (.trans ?_ CMRA.comm.dist)
      refine CMRA.op_ne.ne ?_
      exact (CMRA.unit_left_id_dist b).symm
    obtain ⟨a', b', Hab', Hrel''⟩ := Hup _ _ Hrel
    refine ⟨((●V a') • ◯V b'), ?_, ⟨by trivial, ?_⟩⟩
    · exists a'; exists b'
    · refine ⟨a', .rfl, ?_⟩
      apply ViewRel.mono Hrel'' .rfl _ n.le_refl
      simp [CMRA.op, op]
      apply Iris.OFE.Dist.to_incN
      refine CMRA.comm.dist.trans (.trans ?_ CMRA.comm.dist)
      refine CMRA.op_ne.ne ?_
      exact (CMRA.unit_left_id_dist b')
  · -- FIXME: Why doesn't this synthesize?
    have _ : CMRA.Exclusive (DFrac.own One.one : DFrac F) := by
      apply own_whole_exclusive <| UFraction.one_whole
    exact (CMRA.not_valid_exclN_op_left ·.1 |>.elim)

theorem auth_one_op_frag_update (Hup : ∀ n bf, R n a (b • bf) → R n a' (b' • bf)) :
    ((●V a) • ◯V b : View F R) ~~> (●V a') • ◯V b' := by
  apply Update.of_updateP
  apply UpdateP.weaken
  · apply auth_op_frag_update (Pab := fun a b => a = a' ∧ b = b')
    intro _ _ H
    exact ⟨a', b', ⟨rfl, rfl⟩, Hup _ _ H⟩
  · rintro y ⟨a', b', H, rfl, rfl⟩; exact H.symm

theorem auth_one_alloc (Hup : ∀ n bf, R n a bf → R n a' (b' • bf)) :
    ((●V a) ~~> ((●V a' : View F R) • ◯V b')) := by
  refine Update.equiv_left CMRA.unit_right_id ?_
  refine auth_one_op_frag_update (fun n bf H => Hup n bf <| ViewRel.mono H .rfl ?_ n.le_refl)
  exact CMRA.incN_op_right n UCMRA.unit bf

theorem auth_one_op_frag_dealloc (Hup : (∀ n bf, R n a (b • bf) → R n a' bf)) :
    ((●V a : View F R) • ◯V b) ~~> ●V a' := by
  refine Update.equiv_right CMRA.unit_right_id ?_
  refine auth_one_op_frag_update (fun n bf H => ?_)
  refine ViewRel.mono (Hup n bf H) .rfl ?_ n.le_refl
  exact Iris.OFE.Dist.to_incN (CMRA.unit_left_id_dist bf)

theorem auth_one_update (Hup : ∀ n bf, R n a bf → R n a' bf) :
    (●V a : View F R) ~~> ●V a' := by
  refine Update.equiv_right CMRA.unit_right_id ?_
  refine Update.equiv_left  CMRA.unit_right_id ?_
  refine auth_one_op_frag_update (fun n bf H => ?_)
  exact ViewRel.mono (Hup n _ H) .rfl .rfl n.le_refl

theorem auth_update (Hupd : dq ~~>: P) :
    (●V{dq} a : View F R ) ~~>: (fun k => ∃ dq', (k = ●V{dq'} a) ∧ P dq') := by
  refine UpdateP.total.mpr (fun n ⟨ag, bf⟩ => ?_)
  rcases ag with (_|⟨dq', ag⟩) <;> rintro ⟨Hv, a', _, _⟩
  · obtain ⟨dr, Hdr, Heq⟩ := Hupd n none Hv
    refine ⟨●V{dr} a, (by exists dr), ⟨Heq, (by exists a')⟩⟩
  · obtain ⟨dr, Hdr, Heq⟩ := Hupd n (some dq') Hv
    refine ⟨●V{dr} a, (by exists dr), ⟨Heq, (by exists a')⟩⟩

theorem auth_discard : (●V{dq} a : View F R) ~~> ●V{.discard} a := by
  apply Update.lift_updateP (g := fun dq => ●V{dq} a)
  · intro P
    apply auth_update
  · exact DFrac.update_discard

theorem auth_acquire [IsSplitFraction F] :
    (●V{.discard} a : View F R) ~~>: fun k => ∃ q, k = ●V{.own q} a := by
  apply UpdateP.weaken
  · apply auth_update
    exact DFrac.update_acquire
  · rintro y ⟨dq, rfl, q', rfl⟩
    exists q'

theorem auth_op_frag_acquire [IsSplitFraction F] :
    ((●V{.discard} a : View F R) • ◯V b) ~~>: fun k => ∃ q, k = ((●V{.own q} a : View F R) • ◯V b ):= by
  apply UpdateP.op
  apply auth_acquire
  apply UpdateP.id rfl
  rintro z1 z2 ⟨q, rfl⟩ rfl; exists q

theorem frag_updateP {P : B → Prop} (Hupd : ∀ a n bf, R n a (b • bf) → ∃ b', P b' ∧ R n a (b' • bf)) :
    (◯V b : View F R) ~~>: (fun k => ∃ b', (k = (◯V b' : View F R)) ∧ P b') := by
  refine UpdateP.total.mpr (fun n ⟨ag, bf⟩ => ?_)
  rcases ag with (_|⟨dq,af⟩)
  simp only [CMRA.ValidN, ValidN]
  · rintro ⟨a, Ha⟩
    obtain ⟨b', HP, Hb'⟩ := Hupd a n bf Ha
    exists (◯V b')
    simp only [mk.injEq, true_and, exists_eq_left']
    refine ⟨HP, ⟨a, Hb'⟩⟩
  · rintro ⟨Hq, a, Hae, Hr⟩
    obtain ⟨b', Hb', Hp⟩ := Hupd a n bf Hr
    exists (◯V b')
    simp only [mk.injEq, true_and, exists_eq_left']
    refine ⟨Hb', ?_⟩
    simp [CMRA.ValidN, ValidN, CMRA.op, op, optionOp]
    refine ⟨Hq, ⟨a, Hae, Hp⟩⟩

theorem frag_update (Hupd : ∀ a n bf, R n a (b • bf) → R n a (b' • bf)) :
    (◯V b : View F R) ~~> (◯V b' : View F R) := by
  refine Update.total.mpr (fun n ⟨ag, bf⟩ => ?_)
  rcases ag with (_|⟨dq,af⟩)
  simp only [CMRA.ValidN, ValidN]
  · simp_all [CMRA.op, optionOp]
    intro a HR
    exists a
    apply Hupd _ _ _ HR
  · simp_all [CMRA.op, op, optionOp, CMRA.ValidN, ValidN]
    intro Hq a He Hr
    exists a
    exact ⟨He, Hupd _ _ _ Hr⟩

theorem auth_alloc (Hup : ∀ n bf, R n a bf → R n a (b • bf)) :
    (●V{dq} a : View F R) ~~> ((●V{dq} a) • ◯V b) := by
  refine Update.total.mpr (fun n ⟨ag', bf⟩ => ?_)
  obtain (_|⟨p, ag⟩) := ag'
  · simp [CMRA.op, op, optionOp, CMRA.ValidN, ValidN]
    intro Hq a' Hag HR
    refine ⟨Hq, a', Hag, ?_⟩
    have He := toAgree.inj Hag
    have HR' := ViewRel.mono HR He.symm (CMRA.incN_op_right n UCMRA.unit bf) n.le_refl
    apply ViewRel.mono (Hup n bf HR') He ?_ n.le_refl
    apply Iris.OFE.Dist.to_incN
    refine CMRA.comm.dist.trans (.trans ?_ CMRA.comm.dist)
    refine CMRA.op_ne.ne ?_
    exact (CMRA.unit_left_id_dist _)
  · rintro ⟨Hv, a0, Hag, Hrel⟩
    refine ⟨Hv, ?_⟩
    simp
    exists a0
    refine ⟨Hag, ?_⟩
    simp_all [CMRA.op, op]
    have Heq  := toAgree.incN.mp ⟨ag, Hag.symm⟩
    have HR' := ViewRel.mono Hrel Heq.symm (CMRA.incN_op_right n UCMRA.unit bf) n.le_refl
    apply ViewRel.mono (Hup _ _ HR') Heq ?_ n.le_refl
    apply Iris.OFE.Dist.to_incN
    refine CMRA.comm.dist.trans (.trans ?_ CMRA.comm.dist)
    refine CMRA.op_ne.ne ?_
    exact (CMRA.unit_left_id_dist _)

-- TODO: Local update lemma

end updates
end View
