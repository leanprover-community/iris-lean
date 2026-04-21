/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Puming Liu
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.OFE
public import Iris.Algebra.Frac
public import Iris.Algebra.DFrac
public import Iris.Algebra.Agree
public import Iris.Algebra.Updates
public import Iris.Algebra.LocalUpdates

@[expose] public section

open Iris

abbrev ViewRel (A B : Type _) := Nat → A → B → Prop

class IsViewRel [OFE A] [UCMRA B] (R : ViewRel A B) where
  mono : R n1 a1 b1 → a1 ≡{n2}≡ a2 → b2 ≼{n2} b1 → n2 ≤ n1 → R n2 a2 b2
  rel_validN n a b : R n a b → ✓{n} b
  rel_unit n : ∃ a, R n a UCMRA.unit

class IsViewRelDiscrete [OFE A] [UCMRA B] (R : ViewRel A B) extends IsViewRel R where
  discrete n a b : R 0 a b → R n a b

namespace ViewRel
open IsViewRel DFrac

variable [OFE A] [UCMRA B] {R : ViewRel A B} [IsViewRel R]

theorem iff_of_dist (Ha : a1 ≡{n}≡ a2) (Hb : b1 ≡{n}≡ b2) : R n a1 b1 ↔ R n a2 b2 :=
  ⟨(mono · Ha Hb.symm.to_incN n.le_refl), (mono · Ha.symm Hb.to_incN n.le_refl)⟩

theorem iff_of_equiv (Ha : a1 ≡ a2) (Hb : b1 ≡ b2) : R n a1 b1 ↔ R n a2 b2 :=
  iff_of_dist Ha.dist Hb.dist

end ViewRel

structure View (F : Type _) {A B : Type _} (R : ViewRel A B) where
  auth : Option ((DFrac F) × Agree A)
  frag : B

abbrev View.Auth [UCMRA B] {R : ViewRel A B} (dq : DFrac F) (a : A) : View F R :=
  ⟨some (dq, toAgree a), UCMRA.unit⟩

abbrev View.Frag {R : ViewRel A B} (b : B) : View F R := ⟨none, b⟩

notation "●V{" dq "} " a => View.Auth dq a
notation "●V " a => View.Auth (DFrac.own One.one) a
notation "◯V " b => View.Frag b

namespace View
section OFE
open OFE UCMRA
variable [OFE A] [OFE B] {R : ViewRel A B}

def equiv (x y : View F R) : Prop := x.auth ≡ y.auth ∧ x.frag ≡ y.frag
def dist (n : Nat) (x y : View F R) : Prop := x.auth ≡{n}≡ y.auth ∧ x.frag ≡{n}≡ y.frag

instance : OFE (View F R) where
  Equiv := equiv
  Dist := dist
  dist_eqv := {
    refl _ := ⟨.of_eq rfl, .of_eq rfl⟩
    symm H := ⟨H.1.symm, H.2.symm⟩
    trans H1 H2 := ⟨H1.1.trans H2.1, H1.2.trans H2.2⟩
  }
  equiv_dist :=
    ⟨fun H _ => ⟨H.1.dist, H.2.dist⟩,
     fun H => ⟨equiv_dist.mpr (H · |>.1), equiv_dist.mpr (H · |>.2)⟩⟩
  dist_lt H Hn := ⟨dist_lt H.1 Hn, dist_lt H.2 Hn⟩

instance mk.ne : NonExpansive₂ (mk : _ → _ → View F R) := ⟨fun _ _ _ Ha _ _ Hb => ⟨Ha, Hb⟩⟩
instance auth.ne : NonExpansive (auth : View F R → _) := ⟨fun _ _ _ H => H.1⟩
instance frag.ne : NonExpansive (frag : View F R → _) := ⟨fun _ _ _ H => H.2⟩

theorem discrete {ag : Option ((DFrac F) × Agree A)} (Ha : DiscreteE ag) (Hb : DiscreteE b) :
  DiscreteE (α := View F R) (mk ag b) := ⟨fun H => ⟨Ha.discrete H.1, Hb.discrete H.2⟩⟩

instance [Discrete A] [Discrete B] : Discrete (View F R) where
  discrete_0 H := ⟨discrete_0 H.1, discrete_0 H.2⟩

theorem auth_inj_frac [UCMRA B] {q1 q2 : DFrac F} {a1 a2 : A} {n} (H : (●V{q1} a1 : View F R) ≡{n}≡ ●V{q2} a2) :
    q1 = q2 := H.1.1

theorem dist_of_auth_dist [UCMRA B] {q1 q2 : DFrac F} {a1 a2 : A} {n} (H : (●V{q1} a1 : View F R) ≡{n}≡ ●V{q2} a2) :
    a1 ≡{n}≡ a2 := toAgree.inj H.1.2

theorem dist_of_frag_dist [UCMRA B] {b1 b2 : B} {n} (H : (◯V b1 : View F R) ≡{n}≡ ◯V b2) :
    b1 ≡{n}≡ b2 := H.2

theorem auth_discrete [UFraction F] [UCMRA B] {dq a} (Ha : DiscreteE a) (He : DiscreteE (unit : B)) :
    DiscreteE (●V{dq} a : View F R) := by
  refine discrete ?_ He
  refine Option.some_is_discrete ?_
  refine prod.is_discrete DFrac.is_discrete ?_
  exact Agree.toAgree.is_discrete Ha

theorem frag_discrete [UCMRA B] (Hb : DiscreteE b) : (DiscreteE (◯V b : View F R)) :=
  discrete Option.none_is_discrete Hb

end OFE

section CMRA
open IsViewRel toAgree OFE DFrac

variable [UFraction F] [OFE A] [UCMRA B] {R : ViewRel A B} [IsViewRel R]

theorem IsViewRel.of_agree_dist_iff (Hb : b' ≡{n}≡ b) :
    (∃ a', toAgree a ≡{n}≡ toAgree a' ∧ R n a' b') ↔ R n a b := by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · rcases H with ⟨_, HA, HR⟩
    exact mono HR (inj HA.symm) Hb.symm.to_incN n.le_refl
  · exact ⟨a, .rfl, mono H .rfl Hb.to_incN n.le_refl⟩

instance auth_ne {dq : DFrac F} : NonExpansive (Auth dq : A → View F R) where
  ne _ _ _ H := by
    refine mk.ne.ne ?_ .rfl
    refine some_dist_some.mpr ⟨.rfl, ?_⟩
    simp only
    exact OFE.NonExpansive.ne H

instance auth_ne₂ : NonExpansive₂ (Auth : DFrac F → A → View F R) where
  ne _ _ _ Hq _ _ Hf := by
    unfold Auth
    refine (NonExpansive₂.ne ?_ .rfl)
    refine NonExpansive.ne ?_
    exact dist_prod_ext Hq (NonExpansive.ne Hf)

instance frag_ne : NonExpansive (Frag : B → View F R) where
  ne _ _ _ H := mk.ne.ne .rfl H

@[simp] def Valid (v : View F R) : Prop :=
  match v.auth with
  | some (dq, ag) => ✓ dq ∧ (∀ n, ∃ a, ag ≡{n}≡ toAgree a ∧ R n a (frag v))
  | none => ∀ n, ∃ a, R n a (frag v)

@[simp] def ValidN (n : Nat) (v : View F R) : Prop :=
  match v.auth with
  | some (dq, ag) => ✓{n} dq ∧ (∃ a, ag ≡{n}≡ toAgree a ∧ R n a (frag v))
  | none => ∃ a, R n a (frag v)

@[simp] def Pcore (v : View F R) : Option (View F R) :=
  some <| mk (CMRA.core v.auth) (CMRA.core v.frag)

@[simp] def Op (v1 v2 : View F R) : View F R :=
  mk (v1.auth • v2.auth) (v1.frag • v2.frag)

instance : CMRA (View F R) where
  pcore := Pcore
  op := Op
  ValidN := ValidN
  Valid := Valid
  op_ne.ne n x1 x2 H := by
    refine mk.ne.ne ?_ ?_
    · exact cmraOption.op_ne.ne <| NonExpansive.ne H
    · exact CMRA.op_ne.ne  <| NonExpansive.ne H
  pcore_ne {n x y} cx H := by
    simp only [Pcore, Option.some.injEq]
    rintro ⟨rfl⟩
    exists ⟨CMRA.core y.auth, CMRA.core y.frag⟩
    exact ⟨rfl, OFE.Dist.core H.1, OFE.Dist.core H.2⟩
  validN_ne {n x1 x2} := by
    rintro ⟨Hl, Hr⟩
    rcases x1 with ⟨_|⟨q1, ag1⟩, b1⟩ <;>
    rcases x2 with ⟨_|⟨q2, ag2⟩, b2⟩ <;>
    simp_all
    · exact fun x H => ⟨x, mono H .rfl Hr.symm.to_incN n.le_refl⟩
    intro Hq a Hag HR
    refine ⟨CMRA.discrete_valid <| DFrac_CMRA.validN_ne Hl.1 Hq, ?_⟩
    refine ⟨a, ?_⟩
    refine ⟨Hl.2.symm.trans Hag, ?_⟩
    exact mono HR .rfl Hr.symm.to_incN n.le_refl
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
      exact mono Ha.2 .rfl (CMRA.incN_refl x.frag) n.le_succ
    · exact fun ⟨z, HR⟩ => ⟨z, mono HR .rfl (CMRA.incN_refl _) n.le_succ⟩
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
      · exact mono Hr .rfl (CMRA.incN_op_left n b1 b2) n.le_refl
  assoc := NonExpansive₂.eqv CMRA.assoc CMRA.assoc
  comm := NonExpansive₂.eqv CMRA.comm CMRA.comm
  pcore_op_left {x _} := by
    simp only [Pcore, Option.some.injEq]
    exact fun H => H ▸ NonExpansive₂.eqv (CMRA.core_op x.auth) (CMRA.core_op x.frag)
  pcore_idem {_ cx} := by
    simp only [Pcore, Option.some.injEq, OFE.some_eqv_some]
    rcases cx
    simp only [mk.injEq, and_imp]
    intro H1 H2
    constructor
    · simp only; exact H1 ▸ CMRA.core_idem _
    · exact H2 ▸ CMRA.core_idem _
  pcore_op_mono := by
    let f : (Option ((DFrac F) × Agree A) × B) → View F R := fun x => ⟨x.1, x.2⟩
    let g : View F R → (Option ((DFrac F) × Agree A) × B) := fun x => (x.auth, x.frag)
    have Hg_eqv {y : View F R} : CMRA.pcore (g y) ≡ g <$> Pcore y := by
      rcases y with ⟨x, b⟩
      simp [Option.map_eq_map, Option.map, g, CMRA.pcore, Prod.pcore, optionCore, CMRA.pcore_eq_core]
      rfl
    have Hg_core {y cy : View F R} : Pcore y ≡ some cy ↔ CMRA.pcore (g y) ≡ some (g cy) := by
      suffices y.Pcore ≡ some cy ↔ g <$> y.Pcore ≡ some (g cy) by
        exact ⟨Hg_eqv.trans ∘ this.mp, this.mpr ∘ Hg_eqv.symm.trans⟩
      exact Eq.to_iff rfl
    apply pcore_op_mono_of_core_op_mono
    rintro y1 cy y2 ⟨z, Hy2⟩ Hy1
    have Hle : g y1 ≼ g y2 := ⟨g z, Hy2⟩
    obtain ⟨_, Hcgy2, x, Hcx⟩ := CMRA.pcore_mono' Hle (Hg_core.mp <| .of_eq Hy1)
    exact ⟨_, rfl, f x, Hg_core.mpr (Hcgy2 ▸ Hcx)⟩
  extend {n x y1 y2} Hv He := by
    let g : View F R → (Option ((DFrac F) × Agree A) × B) := fun x => (x.auth, x.frag)
    obtain H1 : ✓{n} g x := by
      simp_all [ValidN, CMRA.ValidN, Prod.ValidN, g, optionValidN]
      rcases x with ⟨_|⟨q1, ag1⟩, b1⟩ <;> simp_all only
      · refine ⟨trivial, ?_⟩
        rcases Hv with ⟨_, Ha⟩
        apply IsViewRel.rel_validN _ _ _ Ha
      · rcases Hv with ⟨Hq, ⟨a, ⟨Ha1, Ha2⟩⟩⟩
        refine ⟨⟨trivial, ?_⟩, ?_⟩
        · exact Agree.validN_ne Ha1.symm trivial
        · exact IsViewRel.rel_validN _ _ _ Ha2
    rcases @CMRA.extend _ _ _ _ (g y1) (g y2) H1 He with ⟨z1, z2, Hze, Hz1, Hz2⟩
    exists ⟨z1.1, z1.2⟩
    exists ⟨z2.1, z2.2⟩

instance [Discrete A] [CMRA.Discrete B] [IsViewRelDiscrete R] : CMRA.Discrete (View F R) where
  discrete_valid {x} := by
    simp only [CMRA.ValidN, ValidN, CMRA.Valid, Valid]
    split
    · rintro ⟨H1, ⟨a, H2, H3⟩⟩
      refine ⟨H1, fun n => ⟨a, ⟨?_, ?_⟩⟩⟩
      · exact equiv_dist.mp (OFE.Discrete.discrete_0 H2) _
      · exact IsViewRelDiscrete.discrete _ _ _ H3
    · exact fun ⟨a, H⟩ _ => ⟨a, IsViewRelDiscrete.discrete _ _ _ H⟩

instance : UCMRA (View F R) where
  unit := ⟨UCMRA.unit, UCMRA.unit⟩
  unit_valid := IsViewRel.rel_unit
  unit_left_id := ⟨UCMRA.unit_left_id, UCMRA.unit_left_id⟩
  pcore_unit := ⟨.rfl, CMRA.core_eqv_self UCMRA.unit⟩

theorem auth_op_auth_eqv : (●V{dq1 • dq2} a : View F R) ≡ (●V{dq1} a) • ●V{dq2} a :=
  ⟨⟨rfl, Agree.idemp.symm⟩, UCMRA.unit_left_id.symm⟩

theorem frag_op_eq : (◯V (b1 • b2) : View F R) = ((◯V b1) • ◯V b2 : View F R) := rfl

theorem frag_inc_of_inc (H : b1 ≼ b2) : (◯V b1 : View F R) ≼ ◯V b2 := by
  rcases H with ⟨c, H⟩
  refine CMRA.inc_of_inc_of_eqv ?_ (NonExpansive.eqv H.symm)
  rw [frag_op_eq]
  exact CMRA.inc_op_left _ _

theorem frag_core : CMRA.core (◯V b : View F R) = ◯V (CMRA.core b) := rfl

theorem auth_discard_op_frag_core : CMRA.core ((●V{.discard} a) • ◯V b : View F R) ≡ (●V{.discard} a) • ◯V (CMRA.core b) :=
  ⟨.rfl, (CMRA.core_ne.eqv UCMRA.unit_left_id).trans UCMRA.unit_left_id.symm⟩

theorem auth_own_op_frag_core : CMRA.core ((●V{.own q} a) • ◯V b : View F R) ≡ ◯V (CMRA.core b) :=
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

theorem dist_of_validN_auth (H : ✓{n} ((●V{dq1} a1 : View F R) • ●V{dq2} a2)) : a1 ≡{n}≡ a2 := by
  rcases H with ⟨_, _, H, _⟩
  refine toAgree.inj (Agree.op_invN ?_)
  exact Agree.validN_ne H.symm trivial

theorem eqv_of_valid_auth (H : ✓ ((●V{dq1} a1 : View F R) • ●V{dq2} a2)) : a1 ≡ a2 :=
  equiv_dist.mpr fun _ => dist_of_validN_auth H.validN

theorem auth_validN_iff : ✓{n} (●V{dq} a : View F R) ↔ ✓{n}dq ∧ R n a UCMRA.unit :=
  and_congr_right fun _ => IsViewRel.of_agree_dist_iff .rfl

theorem auth_one_validN_iff n a : ✓{n} (●V a : View F R) ↔ R n a UCMRA.unit :=
  ⟨(auth_validN_iff.mp · |>.2), (auth_validN_iff.mpr ⟨UFraction.one_whole.1, ·⟩)⟩

theorem auth_op_auth_validN_iff :
    ✓{n} ((●V{dq1} a1 : View F R) • ●V{dq2} a2) ↔ ✓(dq1 • dq2) ∧ a1 ≡{n}≡ a2 ∧ R n a1 UCMRA.unit := by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · let Ha' : a1 ≡{n}≡ a2 := dist_of_validN_auth H
    rcases H with ⟨Hq, _, Ha, HR⟩
    refine ⟨Hq, Ha', mono HR ?_ CMRA.incN_unit n.le_refl⟩
    refine .trans ?_ Ha'.symm
    refine toAgree.inj (Ha.symm.trans ?_)
    apply CMRA.op_commN.trans
    apply (CMRA.op_ne.ne (toAgree.ne.ne Ha')).trans
    apply Agree.idemp
  · simp [CMRA.op, CMRA.ValidN, ValidN, optionOp, Prod.op]
    refine ⟨H.1, a1, ?_, ?_⟩
    · exact (CMRA.op_ne.ne <| toAgree.ne.ne H.2.1.symm).trans Agree.idemp.dist
    · refine mono H.2.2 .rfl ?_ n.le_refl
      exact OFE.Dist.to_incN <| CMRA.unit_left_id_dist UCMRA.unit

theorem auth_one_op_auth_one_validN_iff : ✓{n} ((●V a1 : View F R) • ●V a2) ↔ False := by
  refine auth_op_auth_validN_iff.trans ?_
  simp only [iff_false, not_and]
  refine fun _ => (UFraction.one_whole (α := F)).2 ?_ |>.elim
  exists 1

theorem frag_validN_iff : ✓{n} (◯V b : View F R) ↔ ∃ a, R n a b := by rfl

theorem auth_op_frag_validN_iff : ✓{n} ((●V{dq} a : View F R) • ◯V b) ↔ ✓dq ∧ R n a b :=
  and_congr_right (fun _ => IsViewRel.of_agree_dist_iff <| CMRA.unit_left_id_dist b)

theorem auth_one_op_frag_validN_iff : ✓{n} ((●V a : View F R) • ◯V b) ↔ R n a b :=
  auth_op_frag_validN_iff.trans <| and_iff_right_iff_imp.mpr (fun _ => valid_own_one)

theorem auth_valid_iff : ✓ (●V{dq} a : View F R) ↔ ✓dq ∧ ∀ n, R n a UCMRA.unit :=
  and_congr_right (fun _=> forall_congr' fun _ => IsViewRel.of_agree_dist_iff .rfl)

theorem auth_one_valid_iff : ✓ (●V a : View F R) ↔ ∀ n, R n a UCMRA.unit :=
  auth_valid_iff.trans <| and_iff_right_iff_imp.mpr (fun _ => valid_own_one)

theorem auth_op_auth_valid_iff : ✓ ((●V{dq1} a1 : View F R) • ●V{dq2} a2) ↔ ✓(dq1 • dq2) ∧ a1 ≡ a2 ∧ ∀ n, R n a1 UCMRA.unit := by
  refine CMRA.valid_iff_validN.trans ?_
  refine ⟨fun H => ?_, fun H n => ?_⟩
  · simp [valid, CMRA.op, op, optionOp, CMRA.ValidN, ValidN] at H
    let Hn n := dist_of_validN_auth <| H n
    refine ⟨(H 0).1, equiv_dist.mpr Hn, fun n => ?_⟩
    · rcases (H n) with ⟨_, _, Hl, H⟩
      apply mono H ?_ CMRA.incN_unit n.le_refl
      apply toAgree.inj (Hl.symm.trans ?_)
      exact (CMRA.op_ne.ne <| toAgree.ne.ne (Hn _).symm).trans Agree.idemp.dist
  · exact auth_op_auth_validN_iff.mpr ⟨H.1, H.2.1.dist, H.2.2 n⟩

theorem auth_one_op_auth_one_valid_iff : ✓ ((●V a1 : View F R) • ●V a2) ↔ False := by
  refine auth_op_auth_valid_iff.trans ?_
  simp [CMRA.op, op, CMRA.Valid, op, valid]
  refine fun _ => (UFraction.one_whole (α := F)).2 ?_ |>.elim
  exists 1

theorem frag_valid_iff : ✓ (◯V b : View F R) ↔ ∀ n, ∃ a, R n a b := by rfl

theorem auth_op_frag_valid_iff : ✓ ((●V{dq} a : View F R) • ◯V b) ↔ ✓dq ∧ ∀ n, R n a b :=
  and_congr_right (fun _ => forall_congr' fun _ => IsViewRel.of_agree_dist_iff <| CMRA.unit_left_id_dist b)

theorem auth_one_op_frag_valid_iff : ✓ ((●V a : View F R) • ◯V b) ↔ ∀ n, R n a b :=
  auth_op_frag_valid_iff.trans <| and_iff_right_iff_imp.mpr (fun _ => valid_own_one)

open CMRA in
theorem auth_incN_auth_op_frag_iff : (●V{dq1} a1 : View F R) ≼{n} ((●V{dq2} a2) • ◯V b) ↔ (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2 := by
  refine ⟨?_, fun H => ?_⟩
  · simp only [Auth, Frag, CMRA.IncludedN, CMRA.op]
    rintro ⟨(_|⟨dqf, af⟩),⟨⟨x1, x2⟩, y⟩⟩
    · exact ⟨.inr x1.symm, toAgree.inj x2.symm⟩
    · exact ⟨.inl ⟨dqf, x1⟩, toAgree.incN.mp ⟨af, x2⟩⟩
  · rcases H with ⟨(⟨z, HRz⟩| HRa2), HRb⟩
    · calc (●V{dq1} a1 : View F R)
             ≼{n} ((●V{dq1} a1) • ((◯V b) • ●V{z} a1)) := by exists ((◯V b) • ●V{z} a1)
           _ ≼{n} ((◯V b) • ●V{z} a1) • ●V{dq1} a1 := incN_of_incN_of_dist .rfl op_commN.symm
           _ ≼{n} (◯V b) • ((●V{z} a1) • ●V{dq1} a1) := incN_of_incN_of_dist .rfl op_assocN.symm
           _ ≼{n} (◯V b) • ((●V{dq1} a1) • ●V{z} a1) := incN_of_incN_of_dist .rfl (op_ne.ne op_commN)
           _ ≼{n} (◯V b) • ●V{dq1 • z} a1 :=
              incN_of_incN_of_dist .rfl (op_ne.ne <| equiv_dist.mp (auth_op_auth_eqv.symm) _)
           _ ≼{n} (◯V b) • ●V{dq2} a2 :=
             incN_of_incN_of_dist .rfl (op_ne.ne (NonExpansive₂.ne HRz.symm HRb))
           _ ≼{n} ((●V{dq2} a2) • ◯V b) := incN_of_incN_of_dist .rfl op_commN
    · exists (◯V b)
      refine (equiv_dist.mp comm _).trans ?_
      refine (.trans ?_ (equiv_dist.mp comm _))
      apply CMRA.op_ne.ne
      exact HRa2 ▸NonExpansive₂.ne rfl HRb.symm

open CMRA in
theorem auth_inc_auth_op_frag_iff : ((●V{dq1} a1 : View F R) ≼ (●V{dq2} a2 : View F R) • ◯V b) ↔ (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡ a2 := by
  refine ⟨fun H => ⟨?_, ?_⟩, fun H => ?_⟩
  · exact auth_incN_auth_op_frag_iff (n := 0) |>.mp (CMRA.incN_of_inc _ H) |>.1
  · refine OFE.equiv_dist.mpr (fun n => ?_)
    exact auth_incN_auth_op_frag_iff |>.mp (CMRA.incN_of_inc _ H) |>.2
  · rcases H with ⟨(⟨q, Hq⟩|Hq), Ha⟩
    · calc (●V{dq1} a1 : View F R)
           _ ≼ (●V{dq1} a1) • ((●V{q} a1) • ◯V b) := by exists ((●V{q} a1) • ◯V b)
           _ ≼ ((●V{dq1} a1) • ●V{q} a1) • ◯V b := inc_of_inc_of_eqv .rfl assoc
           _ ≼ (◯V b) • ((●V{dq1} a1) • ●V{q} a1) := inc_of_inc_of_eqv .rfl comm
           _ ≼ (◯V b) • ●V{dq1 • q} a1 :=
             inc_of_inc_of_eqv .rfl <| op_ne.eqv (View.auth_op_auth_eqv.symm)
           _ ≼ (●V{dq2} a2) • ◯V b := by
             refine inc_of_inc_of_eqv .rfl ?_
             exact (comm.trans (op_ne.eqv <| NonExpansive₂.eqv Hq Ha.symm)).symm
    · exists (◯V b)
      refine .trans CMRA.comm (.trans ?_ CMRA.comm )
      apply CMRA.op_ne.eqv
      exact Hq ▸ NonExpansive₂.eqv rfl Ha.symm

theorem auth_one_incN_auth_one_op_frag_iff : (●V a1 : View F R) ≼{n} ((●V a2) • ◯V b) ↔ a1 ≡{n}≡ a2 :=
  auth_incN_auth_op_frag_iff.trans <| and_iff_right_iff_imp.mpr <| fun _ => .inr rfl

theorem auth_one_inc_auth_one_op_frag_iff : (●V a1 : View F R) ≼ ((●V a2) • ◯V b) ↔ a1 ≡ a2 :=
  auth_inc_auth_op_frag_iff.trans <| and_iff_right_iff_imp.mpr <| fun _ => .inr rfl

open CMRA in
theorem frag_incN_auth_op_frag_iff : (◯V b1 : View F R) ≼{n} ((●V{p} a) • ◯V b2) ↔ b1 ≼{n} b2 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨xf, ⟨_, Hb⟩⟩
    have Hb' : b2 ≡{n}≡ b1 • xf.frag := equiv_dist.mp UCMRA.unit_left_id _ |>.symm.trans Hb
    refine (incN_iff_right <| Hb'.symm).mp ?_
    exists xf.frag
  · rintro ⟨bf, Hbf⟩
    calc (◯V b1 : View F R)
         _ ≼{n} (◯V b1) • ((◯V bf) • ●V{p} a) := by exists ((◯V bf) • ●V{p} a)
         _ ≼{n} ((◯V b1) • ◯V bf) • ●V{p} a := incN_of_incN_of_dist .rfl op_assocN
         _ ≼{n} (●V{p} a) • ((◯V b1) • ◯V bf) := incN_of_incN_of_dist .rfl op_commN
         _ ≼{n} (●V{p} a) • ◯V b1 • bf := by rw [frag_op_eq]
         _ ≼{n} (●V{p} a) • ◯V b2 := incN_of_incN_of_dist .rfl (op_ne.ne (NonExpansive.ne Hbf.symm))

open CMRA in
theorem frag_inc_auth_op_frag_iff : (◯V b1 : View F R) ≼ ((●V{p} a) • ◯V b2) ↔ b1 ≼ b2 := by
  constructor
  · rintro ⟨xf, ⟨_, Hb⟩⟩
    have Hb' : b2 ≡ b1 • xf.frag := (UCMRA.unit_left_id).symm.trans Hb
    apply (inc_iff_right <| Hb'.symm).mp
    exists xf.frag
  · rintro ⟨bf, Hbf⟩
    calc (◯V b1 : View F R)
         _ ≼ (◯V b1) • ((◯V bf) • ●V{p} a) := by exists ((◯V bf) • ●V{p} a)
         _ ≼ ((◯V b1) • ◯V bf) • ●V{p} a := inc_of_inc_of_eqv .rfl assoc
         _ ≼ (●V{p} a) • ((◯V b1) • ◯V bf) := inc_of_inc_of_eqv .rfl comm
         _ ≼ (●V{p} a) • ◯V b1 • bf := by rw [frag_op_eq]
         _ ≼ (●V{p} a) • ◯V b2 := inc_of_inc_of_eqv .rfl (op_ne.eqv (NonExpansive.eqv Hbf.symm))

open CMRA in
theorem auth_op_frag_incN_auth_op_frag_iff :
    ((●V{dq1} a1 : View F R) • ◯V b1) ≼{n} ((●V{dq2} a2) • ◯V b2) ↔
      (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2 ∧ b1 ≼{n} b2 := by
  refine ⟨fun H => ?_, fun ⟨H0, H1, ⟨bf, H2⟩⟩ => ?_⟩
  · rw [← and_assoc]
    refine ⟨?_, ?_⟩
    · apply (auth_incN_auth_op_frag_iff (R := R)).mp
      exact incN_trans (incN_op_left _ (●V{dq1} a1) (◯V b1)) H
    · apply (frag_incN_auth_op_frag_iff (R := R) (F := F)).mp
      exact incN_trans (CMRA.incN_op_right _ _ _) H
  · calc ((●V{dq1} a1) • ◯V b1 : View F R)
         _ ≼{n} ((●V{dq2} a2) • ◯V bf) • ◯V b1 :=
           op_monoN_left _ <| auth_incN_auth_op_frag_iff.mpr ⟨H0, H1⟩
         _ ≼{n} (●V{dq2} a2) • ((◯V bf) • ◯V b1) := incN_of_incN_of_dist .rfl  op_assocN.symm
         _ ≼{n} (●V{dq2} a2) • ◯V bf • b1 := by rw [frag_op_eq]
         _ ≼{n} (●V{dq2} a2) • ◯V b2 := by
           refine incN_of_incN_of_dist .rfl  ?_
           refine CMRA.op_ne.ne (NonExpansive.ne ?_)
           exact H2.trans (equiv_dist.mp comm _) |>.symm

open CMRA in
theorem auth_op_frag_inc_auth_op_frag_iff : ((●V{dq1} a1 : View F R) • ◯V b1) ≼ ((●V{dq2} a2) • ◯V b2) ↔
      (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡ a2 ∧ b1 ≼ b2 := by
  refine ⟨fun H => ?_, fun ⟨H0, H1, ⟨bf, H2⟩⟩ => ?_⟩
  · rw [← and_assoc]
    refine ⟨?_, ?_⟩
    · apply (auth_inc_auth_op_frag_iff (R := R)).mp
      apply CMRA.inc_trans ?_ H
      exact CMRA.inc_op_left (●V{dq1} a1) (◯V b1)
    · apply (frag_inc_auth_op_frag_iff (R := R) (F := F)).mp
      apply CMRA.inc_trans (CMRA.inc_op_right _ _)
      apply H
  · calc ((●V{dq1} a1) • ◯V b1 : View F R)
         _ ≼ ((●V{dq2} a2) • ◯V bf) • ◯V b1 :=
           op_mono_left _ <| auth_inc_auth_op_frag_iff.mpr ⟨H0, H1⟩
         _ ≼ (●V{dq2} a2) • ((◯V bf) • ◯V b1) := inc_of_inc_of_eqv .rfl assoc.symm
         _ ≼ (●V{dq2} a2) • ◯V bf • b1 := .rfl
         _ ≼ (●V{dq2} a2) • ◯V b2 := by
           refine inc_of_inc_of_eqv .rfl  ?_
           refine op_ne.eqv (NonExpansive.eqv ?_)
           exact (H2.trans comm).symm

theorem auth_one_op_frag_incN_auth_one_op_frag_iff : ((●V a1 : View F R) • ◯V b1) ≼{n} ((●V a2) • ◯V b2) ↔ (a1 ≡{n}≡ a2 ∧ b1 ≼{n} b2) :=
  auth_op_frag_incN_auth_op_frag_iff.trans <| and_iff_right_iff_imp.mpr <| fun _ => .inr rfl

theorem auth_one_op_frag_inc_auth_one_op_frag_iff : ((●V a1 : View F R) • ◯V b1) ≼ ((●V a2) • ◯V b2) ↔ a1 ≡ a2 ∧ b1 ≼ b2 :=
  auth_op_frag_inc_auth_op_frag_iff.trans <| and_iff_right_iff_imp.mpr <| fun _ => .inr rfl

end CMRA

section Updates

variable [UFraction F] [OFE A] [IB : UCMRA B] {R : ViewRel A B} [IsViewRel R]

open CMRA DFrac

theorem auth_one_op_frag_updateP {Pab : A → B → Prop}
    (Hup : ∀ n bf, R n a (b • bf) → ∃ a' b', Pab a' b' ∧ R n a' (b' • bf)) :
    ((●V a) • ◯V b : View F R) ~~>: fun k => ∃ a' b', k = ((●V a') • ◯V b' : View F R) ∧ Pab a' b' := by
  refine UpdateP.total.mpr (fun n ⟨ag, bf⟩ => ?_)
  rcases ag with (_|⟨dq, ag⟩)
  · intro H
    obtain ⟨_, a0, He', Hrel'⟩ := H
    have Hrel : R n a (b • bf) := by
      apply IsViewRel.mono Hrel' (toAgree.inj He').symm _ n.le_refl
      apply Iris.OFE.Dist.to_incN
      refine CMRA.comm.dist.trans (.trans ?_ CMRA.comm.dist)
      refine CMRA.op_ne.ne ?_
      exact (CMRA.unit_left_id_dist b).symm
    obtain ⟨a', b', Hab', Hrel''⟩ := Hup _ _ Hrel
    refine ⟨((●V a') • ◯V b'), ?_, ⟨by trivial, ?_⟩⟩
    · exists a'; exists b'
    · refine ⟨a', .rfl, ?_⟩
      apply IsViewRel.mono Hrel'' .rfl _ n.le_refl
      apply Iris.OFE.Dist.to_incN
      refine comm.dist.trans (.trans ?_ CMRA.comm.dist)
      refine op_ne.ne <| unit_left_id_dist b'
  · letI _ := own_whole_exclusive <| (UFraction.one_whole (α := F))
    exact (not_valid_exclN_op_left ·.1 |>.elim)

theorem auth_one_op_frag_update (Hup : ∀ n bf, R n a (b • bf) → R n a' (b' • bf)) :
    ((●V a) • ◯V b : View F R) ~~> (●V a') • ◯V b' := by
  apply Update.of_updateP
  apply UpdateP.weaken
  · apply auth_one_op_frag_updateP (Pab := fun a b => a = a' ∧ b = b')
    exact fun _ _ H => ⟨a', b', ⟨rfl, rfl⟩, Hup _ _ H⟩
  · rintro y ⟨a', b', H, rfl, rfl⟩
    exact H.symm

theorem auth_one_alloc (Hup : ∀ n bf, R n a bf → R n a' (b' • bf)) :
    ((●V a) ~~> ((●V a' : View F R) • ◯V b')) := by
  refine Update.equiv_left CMRA.unit_right_id ?_
  refine auth_one_op_frag_update (fun n bf H => Hup n bf <| IsViewRel.mono H .rfl ?_ n.le_refl)
  exact incN_op_right n unit bf

theorem auth_one_op_frag_dealloc (Hup : (∀ n bf, R n a (b • bf) → R n a' bf)) :
    ((●V a : View F R) • ◯V b) ~~> ●V a' := by
  refine Update.equiv_right CMRA.unit_right_id ?_
  refine auth_one_op_frag_update (fun n bf H => ?_)
  refine IsViewRel.mono (Hup n bf H) .rfl ?_ n.le_refl
  exact (unit_left_id_dist bf).to_incN

theorem auth_one_update (Hup : ∀ n bf, R n a bf → R n a' bf) :
    (●V a : View F R) ~~> ●V a' := by
  refine Update.equiv_right unit_right_id ?_
  refine Update.equiv_left  unit_right_id ?_
  refine auth_one_op_frag_update (fun n bf H => ?_)
  exact IsViewRel.mono (Hup n _ H) .rfl .rfl n.le_refl

theorem auth_updateP (Hupd : dq ~~>: P) :
    (●V{dq} a : View F R) ~~>: (fun k => ∃ dq', (k = ●V{dq'} a) ∧ P dq') := by
  refine UpdateP.total.mpr (fun n ⟨ag, bf⟩ => ?_)
  rcases ag with (_|⟨dq', ag⟩) <;> rintro ⟨Hv, a', _, _⟩
  · obtain ⟨dr, Hdr, Heq⟩ := Hupd n none Hv
    refine ⟨●V{dr} a, (by exists dr), ⟨Heq, (by exists a')⟩⟩
  · obtain ⟨dr, Hdr, Heq⟩ := Hupd n (some dq') Hv
    refine ⟨●V{dr} a, (by exists dr), ⟨Heq, (by exists a')⟩⟩

theorem auth_discard : (●V{dq} a : View F R) ~~> ●V{.discard} a := by
  apply Update.lift_updateP (g := fun dq => ●V{dq} a)
  · exact fun _ => auth_updateP
  · exact DFrac.update_discard

theorem auth_acquire [IsSplitFraction F] :
    (●V{.discard} a : View F R) ~~>: fun k => ∃ q, k = ●V{.own q} a := by
  apply UpdateP.weaken
  · apply auth_updateP
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
  · rintro ⟨a, Ha⟩
    obtain ⟨b', HP, Hb'⟩ := Hupd a n bf Ha
    exists (◯V b')
    simp only [mk.injEq, true_and, exists_eq_left']
    exact ⟨HP, ⟨a, Hb'⟩⟩
  · rintro ⟨Hq, a, Hae, Hr⟩
    obtain ⟨b', Hb', Hp⟩ := Hupd a n bf Hr
    exists (◯V b')
    simp only [mk.injEq, true_and, exists_eq_left']
    refine ⟨Hb', ?_⟩
    simp [CMRA.ValidN, ValidN, CMRA.op, optionOp]
    exact ⟨Hq, ⟨a, Hae, Hp⟩⟩

theorem frag_update (Hupd : ∀ a n bf, R n a (b • bf) → R n a (b' • bf)) :
    (◯V b : View F R) ~~> (◯V b' : View F R) := by
  refine Update.total.mpr (fun n ⟨ag, bf⟩ => ?_)
  rcases ag with (_|⟨dq,af⟩)
  simp only [CMRA.ValidN]
  · simp_all [CMRA.op, optionOp]
    intro a HR
    exists a
    exact Hupd _ _ _ HR
  · simp_all [CMRA.op, CMRA.ValidN]
    intro Hq a He Hr
    exists a
    exact ⟨He, Hupd _ _ _ Hr⟩

theorem auth_alloc (Hup : ∀ n bf, R n a bf → R n a (b • bf)) :
    (●V{dq} a : View F R) ~~> ((●V{dq} a) • ◯V b) := by
  refine Update.total.mpr (fun n ⟨ag', bf⟩ => ?_)
  obtain (_|⟨p, ag⟩) := ag'
  · simp [CMRA.op, optionOp, CMRA.ValidN, ValidN]
    intro Hq a' Hag HR
    refine ⟨Hq, a', Hag, ?_⟩
    have HR' := IsViewRel.mono HR (toAgree.inj Hag).symm (CMRA.incN_op_right n UCMRA.unit bf) n.le_refl
    apply IsViewRel.mono (Hup n bf HR') (toAgree.inj Hag) ?_ n.le_refl
    apply Iris.OFE.Dist.to_incN
    refine CMRA.comm.dist.trans (.trans ?_ CMRA.comm.dist)
    refine CMRA.op_ne.ne ?_
    exact (CMRA.unit_left_id_dist _)
  · rintro ⟨Hv, a0, Hag, Hrel⟩
    refine ⟨Hv, ?_⟩
    exists a0
    refine ⟨Hag, ?_⟩
    have Heq  := toAgree.incN.mp ⟨ag, Hag.symm⟩
    have HR' := IsViewRel.mono Hrel Heq.symm (CMRA.incN_op_right n UCMRA.unit bf) n.le_refl
    apply IsViewRel.mono (Hup _ _ HR') Heq ?_ n.le_refl
    apply Iris.OFE.Dist.to_incN
    refine CMRA.comm.dist.trans (.trans ?_ CMRA.comm.dist)
    refine CMRA.op_ne.ne ?_
    exact (CMRA.unit_left_id_dist _)

theorem view_local_update {a a' : A} {b0 b1 b0' b1' : B}
    (Hup : (b0, b1) ~l~> (b0', b1'))
    (Hrel : ∀ n, R n a b0 → R n a' b0') :
    ((●V a : View F R) • ◯V b0, (●V a) • ◯V b1) ~l~> ((●V a') • ◯V b0', (●V a') • ◯V b1') := by
  rw [local_update_unital]
  rintro n ⟨(_ | ⟨dq, ag'⟩), bf⟩ Hv Heq <;> rw [auth_one_op_frag_validN_iff] at Hv
  · refine ⟨auth_one_op_frag_validN_iff.mpr (Hrel n Hv), ⟨.rfl, ?_⟩⟩
    refine .trans ?_ (unit_left_id_dist b1').symm.op_l
    refine unit_left_id_dist b0' |>.trans ?_
    refine (local_update_unital.mp Hup _ _ (IsViewRel.rel_validN _ _ _ Hv) ?_).2
    exact (unit_left_id_dist b0).symm.trans Heq.2 |>.trans (unit_left_id_dist b1).op_l
  · refine ((UFraction.one_whole (α := F)).2 ?_).elim
    refine DFrac.valid_own_op (validN_ne Heq ?_).1
    exact auth_one_op_frag_validN_iff.mpr Hv

end Updates

section ViewMap

def map {R : ViewRel A B} (R' : ViewRel A' B') (f : A → A') (g : B → B') (v : View F R) : View F R' where
  auth := match v.auth with | none => none | some (fr, a) => (fr, a.map' f)
  frag := g v.frag

theorem map_id {R : ViewRel A B} (v : View F R) : View.map R id id v = v := by
  rcases v with ⟨a, b⟩
  cases a <;> simp [View.map, Agree.map']

theorem map_compose {R : ViewRel A B} {R' : ViewRel A' B'} {R'' : ViewRel A'' B''}
    f g (f' : A' → A'') (g' : B' → B'') (v : View F R) :
    View.map R'' (f' ∘ f) (g' ∘ g) v = View.map R'' f' g' (View.map R' f g v) := by
  rcases v with ⟨a, b⟩
  cases a <;> simp [View.map, Agree.map']

section mapO

variable [OFE A] [OFE B] [OFE A'] [OFE B'] {R : ViewRel A B} {R' : ViewRel A' B'}

theorem map_compose' [OFE A''] [OFE B''] {R'' : ViewRel A'' B''}
    f g (f' : A' -n> A'') (g' : B' -n> B'') (v : View F R) :
    View.map R'' (f'.comp f) (g'.comp g) v = View.map R'' f' g' (View.map R' f g v) :=
  map_compose f.f g.f f'.f g'.f v

omit [OFE B] in
theorem map_ext {f1 f2 : A → A'} {g1 g2 : B → B'} [OFE.NonExpansive f1] [OFE.NonExpansive f2]
    (v : View F R) (h1 : ∀ a, f1 a ≡ f2 a) (h2 : ∀ b, g1 b ≡ g2 b) :
    View.map R' f1 g1 v ≡ View.map R' f2 g2 v := by
  refine ⟨?_, h2 _⟩
  simp only [View.map]
  split
  · rfl
  · exact ⟨rfl, Agree.agree_map_ext h1⟩

omit [OFE B] in
theorem map_ne {f1 f2 : A → A'} {g1 g2 : B → B'} [OFE.NonExpansive f1] [OFE.NonExpansive f2]
    (v : View F R) (h1 : ∀ a, f1 a ≡{n}≡ f2 a) (h2 : ∀ b, g1 b ≡{n}≡ g2 b) :
    View.map R' f1 g1 v ≡{n}≡ View.map R' f2 g2 v := by
  refine ⟨?_, h2 _⟩
  simp only [View.map]
  split
  · rfl
  · exact ⟨rfl, Agree.map_ne h1⟩

instance (f : A → A') (g : B → B') [OFE.NonExpansive f] [hne : OFE.NonExpansive g] :
    OFE.NonExpansive (View.map R' f g : (View F R → _)) where
  ne := by
    rintro n _ _ ⟨h1, h2⟩
    refine ⟨?_, hne.ne h2⟩
    simp only [map]
    split <;> split <;> simp_all
    exact ⟨h1.1, Agree.map f |>.ne.ne h1.2⟩

instance mapO (f : A -n> A') (g : B -n> B') : View F R -n> View F R' where
  f := View.map R' f g
  ne := inferInstance

end mapO

instance mapC [UFraction F] [OFE A] [UCMRA B] [OFE A'] [UCMRA B']
    {R : ViewRel A B} [IsViewRel R] {R' : ViewRel A' B'} [IsViewRel R']
    (f : A -n> A') (g : B -C> B') (H : ∀ n a b, R n a b → R' n (f a) (g b)) :
    View F R -C> View F R' where
  f := View.map R' f g
  ne := inferInstance
  validN {n x} hval := by
    simp [CMRA.ValidN, map] at *
    rcases x with ⟨_ | ⟨fr,a⟩, b⟩ <;> simp_all
    · obtain ⟨a, hr⟩ := hval
      exists f a
      exact (H n a b hr)
    · rcases hval with ⟨hfr, a1, ha, hr⟩
      exact ⟨f a1, ⟨OFE.NonExpansive.ne ha, H n a1 b hr⟩⟩
  pcore x := by
    simp [CMRA.pcore, map, CMRA.core, Option.getD]
    constructor
    · rcases x.auth with _|⟨fr, a⟩ <;> simp [Prod.pcore]
      rcases (CMRA.pcore fr) <;> simp
      rcases h : (CMRA.pcore a) <;> cases h <;> simp [CMRA.pcore]
    · have _ := CMRA.Hom.pcore g x.frag
      rcases _ : (CMRA.pcore x.frag) <;>
      rcases _ : (CMRA.pcore (g.f x.frag)) <;> simp_all
  op x y := by
    constructor <;> simp [CMRA.Hom.op, CMRA.op, map]
    cases x.auth <;> cases y.auth <;> simp [Prod.op]
    exact ⟨rfl, (Agree.map _).op _ _⟩

end ViewMap

end View
