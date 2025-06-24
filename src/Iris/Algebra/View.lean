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

open Iris

abbrev view_rel (A B : Type _) := Nat → A → B → Prop

class ViewRel [OFE A] [UCMRA B] (R : view_rel A B) where
  mono {n1 n2 : Nat} {a1 a2 : A} {b1 b2 : B} :
    R n1 a1 b1 → a1 ≡{n2}≡ a2 → b2 ≼{n2} b1 → n2 ≤ n1 → R n2 a2 b2
  rel_validN n a b : R n a b → ✓{n} b
  rel_unit n : ∃ a, R n a ε

class ViewRelDiscrete [OFE A] [UCMRA B] (R : view_rel A B) extends ViewRel R where
  discrete n a b : R 0 a b → R n a b

namespace viewrel

variable [OFE A] [UCMRA B] {R : view_rel A B} [ViewRel R]

theorem ne {a1 a2 : A} {b1 b2 : B} {n : Nat} (Ha : a1 ≡{n}≡ a2) (Hb : b1 ≡{n}≡ b2) : R n a1 b1 ↔ R n a2 b2 :=
  ⟨(ViewRel.mono · Ha Hb.symm.to_incN n.le_refl), (ViewRel.mono · Ha.symm Hb.to_incN n.le_refl)⟩

theorem eqv_ne {a1 a2 : A} {b1 b2 : B} (Ha : a1 ≡ a2) (Hb : b1 ≡ b2) : R n a1 b1 ↔ R n a2 b2 :=
  ne Ha.dist Hb.dist

end viewrel

structure View (F : Type _) {A B : Type _} (R : view_rel A B) where
  π_auth : Option ((DFrac F) × Agree A)
  π_frag : B

def View.auth [UCMRA B] {R : view_rel A B} (dq : DFrac F) (a : A) : View F R :=
  ⟨some (dq, toAgree a), UCMRA.unit⟩

def View.frag {R : view_rel A B} (b : B) : View F R := ⟨none, b⟩

notation "●V{" dq "} " a => View.auth dq a
notation "◯V " b => View.frag b

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

theorem is_discrete {ag : Option ((DFrac F) × Agree A)} (Ha : OFE.DiscreteE ag) (Hb : OFE.DiscreteE b) :
  OFE.DiscreteE (α := View F R) (View.mk ag b) := fun H => ⟨Ha H.1, Hb H.2⟩

instance [OFE.Discrete A] [OFE.Discrete B] : OFE.Discrete (View F R) where
  discrete_0 H := ⟨OFE.Discrete.discrete_0 H.1, OFE.Discrete.discrete_0 H.2⟩

end ofe

section cmra
variable [DFractional F] [OFE A] [IB : UCMRA B] {R : view_rel A B} [ViewRel R]

instance {dq : DFrac F} : OFE.NonExpansive (View.auth dq : A → View F R) where
  ne _ _ _ H := by
    refine View.mk.ne.ne ?_ .rfl
    refine OFE.some_dist_some.mpr ⟨.rfl, ?_⟩
    simp only
    exact OFE.NonExpansive.ne H

instance : OFE.NonExpansive (View.frag : B → View F R) where
  ne _ _ _ H := View.mk.ne.ne .rfl H

omit [ViewRel R] [DFractional F] in
theorem view_auth.frac_inj {q1 q2 : DFrac F} {a1 a2 : A} {n} (H : (●V{q1} a1 : View F R) ≡{n}≡ ●V{q2} a2) :
    q1 = q2 := H.1.1

omit [ViewRel R] [DFractional F] in
theorem view_auth.ag_inj {q1 q2 : DFrac F} {a1 a2 : A} {n} (H : (●V{q1} a1 : View F R) ≡{n}≡ ●V{q2} a2) :
    a1 ≡{n}≡ a2 := toAgree.inj H.1.2

omit [ViewRel R] [DFractional F] in
theorem view_frag.inj {b1 b2 : B} {n} (H : (◯V b1 : View F R) ≡{n}≡ ◯V b2) :
    b1 ≡{n}≡ b2 := H.2

abbrev valid (v : View F R) : Prop :=
  match v.π_auth with
  | some (dq, ag) => ✓ dq ∧ (∀ n, ∃ a, ag ≡{n}≡ toAgree a ∧ R n a (π_frag v))
  | none => ∀ n, ∃ a, R n a (π_frag v)

abbrev validN (n : Nat) (v : View F R) : Prop :=
  match v.π_auth with
  | some (dq, ag) => ✓ dq ∧ (∃ a, ag ≡{n}≡ toAgree a ∧ R n a (π_frag v))
  | none => ∃ a, R n a (π_frag v)

def pcore (v : View F R) : Option (View F R) :=
  let ag : Option (DFrac F × Agree A) := CMRA.core v.1
  let b : B := CMRA.core v.2
  some <| View.mk ag b

abbrev op (v1 v2 : View F R) : View F R :=
  View.mk (v1.1 • v2.1) (v1.2 • v2.2)

instance : CMRA (View F R) where
  pcore := pcore
  op := op
  ValidN := validN
  Valid := valid
  op_ne.ne n x1 x2 H := by
    refine View.mk.ne.ne ?_ ?_
    · refine cmraOption.op_ne.ne ?_
      exact OFE.NonExpansive.ne H
    · refine IB.op_ne.ne ?_
      exact OFE.NonExpansive.ne H
  pcore_ne {n x y} cx H := by
    simp only [pcore, Option.some.injEq]
    intro Hc; subst Hc
    exists { π_auth := CMRA.core y.π_auth, π_frag := CMRA.core y.π_frag }
    exact ⟨rfl, ⟨OFE.Dist.core H.1, OFE.Dist.core H.2⟩⟩
  validN_ne {n x1 x2} H := by
    simp [validN]
    rcases H with ⟨Hl, Hr⟩
    rcases x1 with ⟨_|⟨q1, ag1⟩, b1⟩ <;>
    rcases x2 with ⟨_|⟨q2, ag2⟩, b2⟩ <;>
    simp_all
    · exact fun x h => ViewRel.rel_unit n
    intro Hq a Hag HR
    refine ⟨CMRA.discrete_valid <| DFrac_CMRA.validN_ne Hl.1 Hq, ?_⟩
    refine ⟨a, ?_⟩
    refine ⟨Hl.2.symm.trans Hag, ?_⟩
    refine ViewRel.mono HR .rfl ?_ n.le_refl
    exact OFE.Dist.to_incN Hr.symm
  valid_iff_validN {x} := by
    simp only [valid, validN]; split
    · exact ⟨fun H n => ⟨H.1, H.2 n⟩, fun H => ⟨(H 0).1, fun n => (H n).2⟩⟩
    · exact Eq.to_iff rfl
  validN_succ {x n} := by
    simp only [validN]
    split
    · refine fun H => ⟨H.1, ?_⟩
      rcases H.2 with ⟨ag, Ha⟩; exists ag
      refine ⟨OFE.Dist.le Ha.1 n.le_succ, ?_⟩
      exact ViewRel.mono Ha.2 .rfl (CMRA.incN_refl x.π_frag) n.le_succ
    · exact fun _ => ViewRel.rel_unit n
  validN_op_left {n x y} := by
    simp [op, validN]
    rcases x with ⟨_|⟨q1, ag1⟩, b1⟩ <;>
    rcases y with ⟨_|⟨q2, ag2⟩, b2⟩ <;>
    simp [CMRA.op, optionOp]
    · refine fun a Hr => ⟨a, ?_⟩
      exact ViewRel.mono Hr .rfl (CMRA.incN_op_left n b1 b2) n.le_refl
    · refine fun _ a _ Hr => ⟨a, ?_⟩
      apply ViewRel.mono Hr .rfl (CMRA.incN_op_left n b1 b2) n.le_refl
    · refine fun Hq a H Hr => ⟨Hq, ⟨a, ⟨H, ?_⟩⟩⟩
      apply ViewRel.mono Hr .rfl (CMRA.incN_op_left n b1 b2) n.le_refl
    · refine fun Hq a H Hr => ⟨CMRA.valid_op_left Hq, ⟨a, ?_⟩⟩
      refine ⟨?_, ?_⟩
      · refine .trans ?_ H
        refine .trans Agree.idemp.symm.dist ?_
        exact Agree_CMRA.op_ne.ne <| Agree.op_invN (Agree.validN_ne H.symm trivial)
      · exact ViewRel.mono Hr .rfl (CMRA.incN_op_left n b1 b2) n.le_refl
  assoc := OFE.NonExpansive₂.eqv CMRA.assoc CMRA.assoc
  comm := OFE.NonExpansive₂.eqv CMRA.comm CMRA.comm
  pcore_op_left {x _} := by
    simp only [pcore, Option.some.injEq]
    exact fun H => H ▸ OFE.NonExpansive₂.eqv (CMRA.core_op x.π_auth) (CMRA.core_op x.π_frag)
  pcore_idem {_ cx} := by
    simp only [pcore, Option.some.injEq, OFE.some_eqv_some]
    rcases cx
    simp only [mk.injEq, and_imp]
    intro H1 H2
    constructor
    · simp only; exact H1 ▸ CMRA.core_idem _
    · exact H2 ▸ CMRA.core_idem _
  pcore_op_mono := by
    apply pcore_op_mono_of_core_op_mono

    -- A is (Option ((DFrac F) × Agree A) × B)
    -- B is View F R
    let f : (Option ((DFrac F) × Agree A) × B) → View F R := fun x => ⟨x.1, x.2⟩
    let g : View F R → (Option ((DFrac F) × Agree A) × B) := fun x => (x.1, x.2)
    let opM' (x : View F R) (y : Option (View F R)) : View F R :=
      match y with | some y => op x y | none => x

    have g_pcore_0 {y : View F R} : CMRA.pcore (g y) ≡ g <$> pcore y := by
      rcases y with ⟨x, b⟩
      simp only [pcore, Option.map_eq_map, Option.map, g]
      simp [CMRA.pcore, prod.pcore, optionCore]
      simp [CMRA.pcore_eq_core]
      rfl

    have g_pcore {y cy : View F R} : pcore y ≡ some cy ↔ CMRA.pcore (g y) ≡ some (g cy) := by
      suffices y.pcore ≡ some cy ↔ g <$> y.pcore ≡ some (g cy) by
        exact ⟨g_pcore_0.trans ∘ this.mp, this.mpr ∘ g_pcore_0.symm.trans⟩
      refine Iff.trans OFE.equiv_dist (Iff.trans ?_ OFE.equiv_dist.symm)
      exact ⟨fun H n => H n, fun H n => H n⟩

    have g_opM_f {x y} : g (opM' y (f x)) ≡ CMRA.op (g y) x := by
      simp [opM', g, f, CMRA.op, prod.op]

    -- Port: Line 1921 of CMRA
    rintro y1 cy y2 ⟨z, Hy2⟩ Hy1
    let Lcore := (@CMRA.pcore_mono' _ _ (g y1) (g y2) (g cy) ?G1 ?G2)
    case G1 => exists (g z)
    case G2 => exact g_pcore.mp <| OFE.Equiv.of_eq Hy1
    rcases Lcore with ⟨cx, Hcgy2, ⟨x, Hcx⟩⟩
    have Hcx' : cx ≡ g (opM' cy (f x)) := Hcx
    have Hcgy2' : CMRA.pcore (g y2) ≡ some (g (opM' cy (f x))) := by rw [Hcgy2]; exact Hcx
    have Hcgy2'' : pcore y2 ≡ some (opM' cy (f x)) := g_pcore.mpr Hcgy2'
    generalize HC : y2.pcore = C
    rw [HC] at Hcgy2''
    cases C; exact Hcgy2''.elim
    rename_i cy'
    refine ⟨cy', ⟨rfl, ?_⟩⟩
    exists (f x)
  extend {n x y1 y2} Hv He := by
    let g : View F R → (Option ((DFrac F) × Agree A) × B) := fun x => (x.1, x.2)
    -- let g_ne : OFE.NonExpansive g := ⟨fun _ _ _ H => ⟨H.1, H.2⟩⟩
    have H2 := @CMRA.extend _ _ n (g x) (g y1) (g y2) ?G1 He
    case G1 =>
      simp_all [validN, CMRA.ValidN, prod.ValidN, g, optionValidN]
      rcases x with ⟨_|⟨q1, ag1⟩, b1⟩ <;> simp_all only
      · refine ⟨trivial, ?_⟩
        rcases Hv with ⟨_, Ha⟩
        apply ViewRel.rel_validN _ _ _ Ha
      · rcases Hv with ⟨Hq, ⟨a, ⟨Ha1, Ha2⟩⟩⟩
        refine ⟨⟨Hq, ?_⟩, ?_⟩
        · exact Agree.validN_ne Ha1.symm trivial
        · exact ViewRel.rel_validN _ _ _ Ha2
    rcases H2 with ⟨z1, z2, Hze, Hz1, Hz2⟩
    exists ⟨z1.1, z1.2⟩
    exists ⟨z2.1, z2.2⟩

end cmra
end View
