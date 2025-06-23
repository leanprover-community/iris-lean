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

instance : OFE.NonExpansive₂ (View.mk : _ → _ → View F R) := ⟨fun _ _ _ Ha _ _ Hb => ⟨Ha, Hb⟩⟩
instance : OFE.NonExpansive (View.π_auth : View F R → _) := ⟨fun _ _ _ H => H.1⟩
instance : OFE.NonExpansive (View.π_frag : View F R → _) := ⟨fun _ _ _ H => H.2⟩

theorem is_discrete {ag : Option ((DFrac F) × Agree A)} (Ha : OFE.DiscreteE ag) (Hb : OFE.DiscreteE b) :
  OFE.DiscreteE (α := View F R) (View.mk ag b) := fun H => ⟨Ha H.1, Hb H.2⟩

instance [OFE.Discrete A] [OFE.Discrete B] : OFE.Discrete (View F R) where
  discrete_0 H := ⟨OFE.Discrete.discrete_0 H.1, OFE.Discrete.discrete_0 H.2⟩

end ofe

section cmra

variable [OFE A] [UCMRA B] {R : view_rel A B} [ViewRel R]

end cmra

end View
