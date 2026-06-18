/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Markus de Medeiros, Michael Sammler
-/
module

public import Iris.BI.Classes
public import Iris.BI.Extensions
public import Iris.BI.BI
public import Iris.Std.Nat
public import Iris.Std.Classes
public import Iris.Std.Rewrite
public import Iris.Std.TC
import Iris.Std.RocqPorting
public meta import Iris.Algebra.NeCongrAttr

@[expose] public section

namespace Iris.BI
open Iris.Std BI

/-! # Entails -/

instance entails_trans [BI PROP] : Trans (α := PROP) Entails Entails Entails where
  trans h1 h2 := h1.trans h2
instance entails_antisymm [BI PROP] : Antisymmetric (α := PROP) BiEntails Entails where
  antisymm h1 h2 := ⟨h1, h2⟩
#rocq_ignore bi.entails_proper "Derivable from _ne with NonExpansive.eqv."

instance equiv_trans [BI PROP] : Trans (α := PROP) BiEntails BiEntails BiEntails where
  trans h1 h2 := h1.trans h2

instance equiv_entails_trans [BI PROP] : Trans (α := PROP) BiEntails Entails Entails where
  trans h1 h2 := h1.1.trans h2

instance entails_equiv_trans [BI PROP] : Trans (α := PROP) Entails BiEntails Entails where
  trans h1 h2 := h1.trans h2.1

/-! # Logic -/

@[rocq_alias bi.and_elim_l']
theorem and_elim_left_trans [BI PROP] {P Q R : PROP} (h : P ⊢ R) : P ∧ Q ⊢ R := and_elim_l.trans h

@[rocq_alias bi.and_elim_r']
theorem and_elim_right_trans [BI PROP] {P Q R : PROP} (h : Q ⊢ R) : P ∧ Q ⊢ R := and_elim_r.trans h

@[rocq_alias bi.or_intro_l']
theorem or_intro_left_trans [BI PROP] {P Q R : PROP} (h : P ⊢ Q) : P ⊢ Q ∨ R := h.trans or_intro_l

@[rocq_alias bi.or_intro_r']
theorem or_intro_right_trans [BI PROP] {P Q R : PROP} (h : P ⊢ R) : P ⊢ Q ∨ R := h.trans or_intro_r

theorem and_symm [BI PROP] {P Q : PROP} : P ∧ Q ⊢ Q ∧ P := and_intro and_elim_r and_elim_l

theorem or_symm [BI PROP] {P Q : PROP} : P ∨ Q ⊢ Q ∨ P := or_elim or_intro_r or_intro_l

@[rocq_alias bi.impl_intro_l]
theorem imp_intro_swap [BI PROP] {P Q R : PROP} (h : Q ∧ P ⊢ R) : P ⊢ Q → R :=
  imp_intro <| and_symm.trans h

@[rocq_alias bi.impl_elim]
theorem imp_mp [BI PROP] {P Q R : PROP} (h1 : P ⊢ Q → R) (h2 : P ⊢ Q) : P ⊢ R :=
  (and_intro .rfl h2).trans (imp_elim h1)

@[rocq_alias bi.impl_elim_r']
theorem imp_elim_swap [BI PROP] {P Q R : PROP} (h : Q ⊢ P → R) : P ∧ Q ⊢ R :=
  and_symm.trans <| imp_elim h

@[rocq_alias bi.impl_elim_l]
theorem imp_elim_left [BI PROP] {P Q : PROP} : (P → Q) ∧ P ⊢ Q := imp_elim .rfl

@[rocq_alias bi.impl_elim_r]
theorem imp_elim_right [BI PROP] {P Q : PROP} : P ∧ (P → Q) ⊢ Q := imp_elim_swap .rfl

theorem imp_elim_alt [BI PROP] {P Q R : PROP} (h : P ⊢ Q → R) : P ∧ Q ⊢ R := imp_elim h

@[rocq_alias bi.False_elim]
theorem false_elim [BI PROP] {P : PROP} : False ⊢ P := pure_elim' False.elim

@[rocq_alias bi.True_intro]
theorem true_intro [BI PROP] {P : PROP} : P ⊢ True := pure_intro trivial

@[rocq_alias bi.entails_eq_True]
theorem entails_eq_true [BI PROP] {P Q : PROP} (h : P ⊢ Q) : (P → Q) ⊣⊢ (True : PROP) :=
  ⟨true_intro, imp_intro (and_elim_r.trans h)⟩

@[rocq_alias bi.entails_impl_True]
theorem entails_impl_true [BI PROP] {P Q : PROP} : (P ⊢ Q) ↔ ((True : PROP) ⊢ P → Q) :=
  ⟨fun h => imp_intro (and_elim_r.trans h),
   fun h => and_intro (true_intro.trans h) .rfl |>.trans imp_elim_left⟩

@[rocq_alias bi.entails_equiv_and]
theorem entails_equiv_and [BI PROP] {P Q : PROP} : (P ⊣⊢ Q ∧ P) ↔ (P ⊢ Q) :=
  ⟨fun h => h.mp.trans and_elim_l, fun h => ⟨and_intro h .rfl, and_elim_r⟩⟩

@[rocq_alias bi.entails_equiv_l]
theorem entails_equiv_left [BI PROP] {P Q R : PROP} (h1 : P ⊣⊢ Q) (h2 : Q ⊢ R) : P ⊢ R := h1.1.trans h2

@[rocq_alias bi.entails_equiv_r]
theorem entails_equiv_right [BI PROP] {P Q R : PROP} (h1 : P ⊢ Q) (h2 : Q ⊣⊢ R) : P ⊢ R := h1.trans h2.1

@[rw_mono_rule, rocq_alias bi.and_mono]
theorem and_mono [BI PROP] {P P' Q Q' : PROP} (h1 : P ⊢ Q) (h2 : P' ⊢ Q') : P ∧ P' ⊢ Q ∧ Q' :=
  and_intro (and_elim_left_trans h1) (and_elim_right_trans h2)
#rocq_ignore bi.and_proper "Derivable from _ne with NonExpansive.eqv."

@[rocq_alias bi.and_mono_l]
theorem and_mono_left [BI PROP] {P P' Q : PROP} (h : P ⊢ P') : P ∧ Q ⊢ P' ∧ Q := and_mono h .rfl

@[rocq_alias bi.and_mono_r]
theorem and_mono_right [BI PROP] {P Q Q' : PROP} (h : Q ⊢ Q') : P ∧ Q ⊢ P ∧ Q' := and_mono .rfl h

@[rw_mono_rule]
theorem and_congr [BI PROP] {P P' Q Q' : PROP} (h1 : P ⊣⊢ Q) (h2 : P' ⊣⊢ Q') : P ∧ P' ⊣⊢ Q ∧ Q' :=
  ⟨and_mono h1.1 h2.1, and_mono h1.2 h2.2⟩

theorem and_congr_left [BI PROP] {P P' Q : PROP} (h : P ⊣⊢ P') : P ∧ Q ⊣⊢ P' ∧ Q := and_congr h .rfl

theorem and_congr_right [BI PROP] {P Q Q' : PROP} (h : Q ⊣⊢ Q') : P ∧ Q ⊣⊢ P ∧ Q' := and_congr .rfl h

@[rw_mono_rule, rocq_alias bi.or_mono]
theorem or_mono [BI PROP] {P P' Q Q' : PROP} (h1 : P ⊢ Q) (h2 : P' ⊢ Q') : P ∨ P' ⊢ Q ∨ Q' :=
  or_elim (or_intro_left_trans h1) (or_intro_right_trans h2)
#rocq_ignore bi.or_proper "Derivable from _ne with NonExpansive.eqv."

@[rocq_alias bi.or_mono_l]
theorem or_mono_left [BI PROP] {P P' Q : PROP} (h : P ⊢ P') : P ∨ Q ⊢ P' ∨ Q := or_mono h .rfl

@[rocq_alias bi.or_mono_r]
theorem or_mono_right [BI PROP] {P Q Q' : PROP} (h : Q ⊢ Q') : P ∨ Q ⊢ P ∨ Q' := or_mono .rfl h

@[rw_mono_rule]
theorem or_congr [BI PROP] {P P' Q Q' : PROP} (h1 : P ⊣⊢ Q) (h2 : P' ⊣⊢ Q') : P ∨ P' ⊣⊢ Q ∨ Q' :=
  ⟨or_mono h1.1 h2.1, or_mono h1.2 h2.2⟩

theorem or_congr_left [BI PROP] {P P' Q : PROP} (h : P ⊣⊢ P') : P ∨ Q ⊣⊢ P' ∨ Q := or_congr h .rfl

theorem or_congr_right [BI PROP] {P Q Q' : PROP} (h : Q ⊣⊢ Q') : P ∨ Q ⊣⊢ P ∨ Q' := or_congr .rfl h

@[rw_mono_rule, rocq_alias bi.impl_mono]
theorem imp_mono [BI PROP] {P P' Q Q' : PROP} (h1 : Q ⊢ P) (h2 : P' ⊢ Q') : (P → P') ⊢ Q → Q' :=
  imp_intro <| (and_mono_right h1).trans <| (imp_elim .rfl).trans h2
#rocq_ignore bi.impl_proper "Derivable from _ne with NonExpansive.eqv"

theorem imp_mono_left [BI PROP] {P P' Q : PROP} (h : P' ⊢ P) : (P → Q) ⊢ (P' → Q) := imp_mono h .rfl

theorem imp_mono_right [BI PROP] {P Q Q' : PROP} (h : Q ⊢ Q') : (P → Q) ⊢ (P → Q') := imp_mono .rfl h

@[rw_mono_rule]
theorem imp_congr [BI PROP] {P P' Q Q' : PROP}
    (h1 : P ⊣⊢ Q) (h2 : P' ⊣⊢ Q') : (P → P') ⊣⊢ (Q → Q') :=
  ⟨imp_mono h1.2 h2.1, imp_mono h1.1 h2.2⟩

theorem imp_congr_left [BI PROP] {P P' Q : PROP} (h : P ⊣⊢ P') : (P → Q) ⊣⊢ (P' → Q) :=
  imp_congr h .rfl

theorem imp_congr_right [BI PROP] {P Q Q' : PROP} (h : Q ⊣⊢ Q') : (P → Q) ⊣⊢ (P → Q') :=
  imp_congr .rfl h

@[ne_congr high, rocq_alias bi.forall_ne]
theorem forall_ne [BI PROP] {Φ Ψ : α → PROP} (h : ∀ a, Φ a ≡{n}≡ Ψ a) :
    iprop(∀ a, Φ a) ≡{n}≡ iprop(∀ a, Ψ a) := sForall_ne <| by
  constructor <;> rintro _ ⟨a, rfl⟩ <;> exact ⟨_, ⟨a, rfl⟩, h _⟩

@[rocq_alias bi.forall_intro]
theorem forall_intro [BI PROP] {P : PROP} {Ψ : α → PROP} (h : ∀ a, P ⊢ Ψ a) : P ⊢ ∀ a, Ψ a :=
  sForall_intro fun _ ⟨_, eq⟩ => eq ▸ h _

@[rocq_alias bi.forall_elim]
theorem forall_elim [BI PROP] {Ψ : α → PROP} (a : α) : (∀ a, Ψ a) ⊢ Ψ a := sForall_elim ⟨_, rfl⟩

@[rocq_alias bi.forall_elim']
theorem forall_elim_trans [BI PROP] {Ψ : α → PROP} {P : PROP} (h : P ⊢ ∀ a, Ψ a) :
  ∀ (a : α), P ⊢ Ψ a := fun a => h.trans (forall_elim a)

@[rw_mono_rule, rocq_alias bi.forall_mono]
theorem forall_mono [BI PROP] {Φ Ψ : α → PROP} (h : ∀ a, Φ a ⊢ Ψ a) : (∀ a, Φ a) ⊢ ∀ a, Ψ a :=
  forall_intro fun a => (forall_elim a).trans (h a)
#rocq_ignore bi.forall_proper "Derivable from _ne with NonExpansive.eqv."

@[rw_mono_rule]
theorem forall_congr [BI PROP] {Φ Ψ : α → PROP} (h : ∀ a, Φ a ⊣⊢ Ψ a) : (∀ a, Φ a) ⊣⊢ ∀ a, Ψ a :=
  ⟨forall_mono fun a => (h a).1, forall_mono fun a => (h a).2⟩

@[ne_congr, rocq_alias bi.exist_ne]
theorem exists_ne [BI PROP] {Φ Ψ : α → PROP} (h : ∀ a, Φ a ≡{n}≡ Ψ a) :
    iprop(∃ a, Φ a) ≡{n}≡ iprop(∃ a, Ψ a) := sExists_ne <| by
  constructor <;> rintro _ ⟨a, rfl⟩ <;> exact ⟨_, ⟨a, rfl⟩, h _⟩

@[rocq_alias bi.exist_intro]
theorem exists_intro [BI PROP] {Ψ : α → PROP} (a : α) : Ψ a ⊢ ∃ a, Ψ a :=
  sExists_intro ⟨_, rfl⟩

@[rocq_alias bi.exist_intro']
theorem exists_intro_trans [BI PROP] {P : PROP} {Ψ : α → PROP} (a : α) (h : P ⊢ Ψ a) :
    P ⊢ ∃ a, Ψ a := h.trans (exists_intro a)

@[rocq_alias bi.exist_elim]
theorem exists_elim [BI PROP] {Φ : α → PROP} {Q : PROP} (h : ∀ a, Φ a ⊢ Q) : (∃ a, Φ a) ⊢ Q :=
  sExists_elim fun _ ⟨_, eq⟩ => eq ▸ h _

@[rw_mono_rule, rocq_alias bi.exist_mono]
theorem exists_mono [BI PROP] {Φ Ψ : α → PROP} (h : ∀ a, Φ a ⊢ Ψ a) : (∃ a, Φ a) ⊢ ∃ a, Ψ a :=
  exists_elim fun a => (h a).trans (exists_intro a)
#rocq_ignore bi.exist_proper "Derivable from _ne with NonExpansive.eqv."

@[rw_mono_rule]
theorem exists_congr [BI PROP] {Φ Ψ : α → PROP} (h : ∀ a, Φ a ⊣⊢ Ψ a) : (∃ a, Φ a) ⊣⊢ ∃ a, Ψ a :=
  ⟨exists_mono fun a => (h a).1, exists_mono fun a => (h a).2⟩

theorem and_self [BI PROP] {P : PROP} : P ∧ P ⊣⊢ P := ⟨and_elim_l, and_intro .rfl .rfl⟩
@[rocq_alias bi.and_idem]
instance [BI PROP] : Idempotent (α := PROP) BiEntails and := ⟨and_self⟩

theorem or_self [BI PROP] {P : PROP} : P ∨ P ⊣⊢ P := ⟨or_elim .rfl .rfl, or_intro_l⟩
@[rocq_alias bi.or_idem]
instance [BI PROP] : Idempotent (α := PROP) BiEntails or := ⟨or_self⟩

#rocq_ignore bi.and_mono' "Use and_mono"
#rocq_ignore bi.and_flip_mono' "Use and_mono"
#rocq_ignore bi.or_flip_mono' "Use or_mono"
#rocq_ignore bi.or_mono' "Use or_mono"
#rocq_ignore bi.impl_flip_mono' "Use imp_mono"
#rocq_ignore bi.impl_mono' "Use imp_mono"
#rocq_ignore bi.forall_flip_mono' "Use forall_mono"
#rocq_ignore bi.forall_mono' "Use forall_mono"
#rocq_ignore bi.exist_flip_mono' "Use exists_mono"
#rocq_ignore bi.exist_mono' "Use exists_mono"

@[rocq_alias bi.and_comm]
theorem and_comm [BI PROP] {P Q : PROP} : P ∧ Q ⊣⊢ Q ∧ P := ⟨and_symm, and_symm⟩
instance [BI PROP] : Commutative (α := PROP) BiEntails and := ⟨and_comm⟩

@[rocq_alias bi.or_comm]
theorem or_comm [BI PROP] {P Q : PROP} : P ∨ Q ⊣⊢ Q ∨ P := ⟨or_symm, or_symm⟩
instance [BI PROP] : Commutative (α := PROP) BiEntails or := ⟨or_comm⟩

@[rocq_alias bi.True_and]
theorem true_and [BI PROP] {P : PROP} : True ∧ P ⊣⊢ P :=
  ⟨and_elim_r, and_intro (pure_intro trivial) .rfl⟩
instance [BI PROP] : LeftId (· ⊣⊢@{PROP} ·) iprop(True) and := ⟨true_and⟩

@[rocq_alias bi.and_True]
theorem and_true [BI PROP] {P : PROP} : P ∧ True ⊣⊢ P := and_comm.trans true_and
instance [BI PROP] : RightId (· ⊣⊢@{PROP} ·) iprop(True) and := ⟨and_true⟩

@[rocq_alias bi.False_and]
theorem false_and [BI PROP] {P : PROP} : False ∧ P ⊣⊢ False := ⟨and_elim_l, false_elim⟩
instance [BI PROP] : LeftAbsorb (· ⊣⊢@{PROP} ·) iprop(False) and := ⟨false_and⟩

@[rocq_alias bi.and_False]
theorem and_false [BI PROP] {P : PROP} : P ∧ False ⊣⊢ False := and_comm.trans false_and
instance [BI PROP] : RightAbsorb (· ⊣⊢@{PROP} ·) iprop(False) and := ⟨and_false⟩

@[rocq_alias bi.True_or]
theorem true_or [BI PROP] {P : PROP} : True ∨ P ⊣⊢ True := ⟨true_intro, or_intro_l⟩
instance [BI PROP] : LeftAbsorb (· ⊣⊢@{PROP} ·) iprop(True) or := ⟨true_or⟩

@[rocq_alias bi.or_True]
theorem or_true [BI PROP] {P : PROP} : P ∨ True ⊣⊢ True := or_comm.trans true_or
instance [BI PROP] : RightAbsorb (· ⊣⊢@{PROP} ·) iprop(True) or := ⟨or_true⟩

@[rocq_alias bi.False_or]
theorem false_or [BI PROP] {P : PROP} : False ∨ P ⊣⊢ P := ⟨or_elim false_elim .rfl, or_intro_r⟩
instance [BI PROP] : LeftId (α := PROP) BiEntails iprop(False) or := ⟨false_or⟩

@[rocq_alias bi.or_False]
theorem or_false [BI PROP] {P : PROP} : P ∨ False ⊣⊢ P := or_comm.trans false_or
instance [BI PROP] : RightId (α := PROP) BiEntails iprop(False) or := ⟨or_false⟩

@[rocq_alias bi.and_assoc]
theorem and_assoc [BI PROP] {P Q R : PROP} : (P ∧ Q) ∧ R ⊣⊢ P ∧ Q ∧ R :=
  ⟨and_intro (and_elim_left_trans and_elim_l) (and_mono_left and_elim_r),
   and_intro (and_mono_right and_elim_l) (and_elim_right_trans and_elim_r)⟩
instance [BI PROP] : Associative (α := PROP) BiEntails and := ⟨and_assoc⟩

@[rocq_alias bi.or_assoc]
theorem or_assoc [BI PROP] {P Q R : PROP} : (P ∨ Q) ∨ R ⊣⊢ P ∨ Q ∨ R :=
  ⟨or_elim (or_mono_right or_intro_l) (or_intro_right_trans or_intro_r),
   or_elim (or_intro_left_trans or_intro_l) (or_mono_left or_intro_r)⟩
instance [BI PROP] : Associative (α := PROP) BiEntails or := ⟨or_assoc⟩

@[rocq_alias bi.True_impl]
theorem true_imp [BI PROP] {P : PROP} : (True → P) ⊣⊢ P :=
  ⟨and_true.2.trans imp_elim_left, imp_intro and_elim_l⟩
instance [BI PROP] : LeftId (· ⊣⊢@{PROP} ·) iprop(True) imp := ⟨true_imp⟩

@[rocq_alias bi.impl_refl]
theorem imp_self [BI PROP] {P Q : PROP} : Q ⊢ P → P := imp_intro and_elim_r

@[rocq_alias bi.impl_trans]
theorem imp_trans [BI PROP] {P Q R : PROP} : (P → Q) ∧ (Q → R) ⊢ P → R :=
  imp_intro_swap <| and_assoc.2.trans <| (and_mono_left imp_elim_right).trans imp_elim_right

@[rocq_alias bi.False_impl]
theorem false_imp [BI PROP] {P : PROP} : (False → P) ⊣⊢ True :=
  ⟨true_intro, imp_intro <| and_elim_r.trans false_elim⟩

@[rocq_alias bi.exist_impl_forall]
theorem exists_impl_forall [BI PROP] {Ψ : α → PROP} {P : PROP} :
    ((∃ x, Ψ x) → P) ⊣⊢ ∀ x, Ψ x → P :=
  ⟨forall_intro fun x => imp_mono (exists_intro x) .rfl,
   imp_intro <| imp_elim_swap <| exists_elim fun x =>
     imp_intro <| and_comm.1.trans <| (and_mono (forall_elim x) .rfl).trans imp_elim_left⟩

@[rocq_alias bi.forall_unit]
theorem forall_unit [BI PROP] {Ψ : Unit → PROP} : (∀ x, Ψ x) ⊣⊢ Ψ () :=
  ⟨forall_elim (), forall_intro fun () => .rfl⟩

@[rocq_alias bi.exist_unit]
theorem exists_unit [BI PROP] {Ψ : Unit → PROP} : (∃ x, Ψ x) ⊣⊢ Ψ () :=
  ⟨exists_elim fun () => .rfl, exists_intro ()⟩

@[rocq_alias bi.exist_exist]
theorem exists_exists [BI PROP] {Ψ : α → β → PROP} : (∃ x y, Ψ x y) ⊣⊢ (∃ y x, Ψ x y) :=
  ⟨exists_elim fun x => exists_elim fun y =>
     (exists_intro (Ψ:=λ x => Ψ x y) x).trans (exists_intro (Ψ:=λ y => (∃ x, Ψ x y)) y),
   exists_elim fun y => exists_elim fun x =>
     (exists_intro (Ψ:=λ y => Ψ x y) y).trans (exists_intro (Ψ:=λ x => (∃ y, Ψ x y)) x)⟩

@[rocq_alias bi.forall_forall]
theorem forall_forall [BI PROP] {Ψ : α → β → PROP} : (∀ x y, Ψ x y) ⊣⊢ (∀ y x, Ψ x y) :=
  ⟨forall_intro fun y => forall_intro fun x => (forall_elim x).trans (forall_elim y),
   forall_intro fun x => forall_intro fun y => (forall_elim y).trans (forall_elim x)⟩

@[rocq_alias bi.exist_forall]
theorem exists_forall [BI PROP] {Ψ : α → β → PROP} : (∃ x, ∀ y, Ψ x y) ⊢ (∀ y, ∃ x, Ψ x y) :=
  forall_intro fun y => exists_elim fun x =>
    (forall_elim y).trans (exists_intro (Ψ := λ x => Ψ x y) x)

@[rocq_alias bi.impl_curry]
theorem impl_curry [BI PROP] {P Q R : PROP} : (P → Q → R) ⊣⊢ (P ∧ Q → R) :=
  ⟨imp_intro <| and_assoc.2.trans <| (and_mono_left imp_elim_left).trans imp_elim_left,
   imp_intro <| imp_intro <| and_assoc.1.trans <| imp_elim_left⟩

@[rocq_alias bi.or_and_l]
theorem or_and_left [BI PROP] {P Q R : PROP} : P ∨ (Q ∧ R) ⊣⊢ (P ∨ Q) ∧ (P ∨ R) :=
  ⟨or_elim (and_intro or_intro_l or_intro_l) (and_mono or_intro_r or_intro_r),
   imp_elim_swap <| or_elim (imp_intro <| or_intro_left_trans and_elim_l) <|
     imp_intro <| imp_elim_swap <| or_elim (imp_intro <| or_intro_left_trans and_elim_l)
       (imp_intro <| or_intro_right_trans <| and_intro and_elim_l and_elim_r)⟩

@[rocq_alias bi.or_and_r]
theorem or_and_right [BI PROP] {P Q R : PROP} : (P ∧ Q) ∨ R ⊣⊢ (P ∨ R) ∧ (Q ∨ R) :=
  (or_comm.trans <| or_and_left.trans <| and_congr or_comm or_comm)

@[rocq_alias bi.and_or_l]
theorem and_or_left [BI PROP] {P Q R : PROP} : P ∧ (Q ∨ R) ⊣⊢ P ∧ Q ∨ P ∧ R :=
  ⟨imp_elim_swap <| or_elim (imp_intro_swap or_intro_l) (imp_intro_swap or_intro_r),
   and_intro (or_elim and_elim_l and_elim_l)
    (or_elim (or_intro_left_trans and_elim_r) (or_intro_right_trans and_elim_r))⟩

@[rocq_alias bi.and_or_r]
theorem and_or_right [BI PROP] {P Q R : PROP} : (P ∨ Q) ∧ R ⊣⊢ (P ∧ R) ∨ (Q ∧ R) :=
  and_comm.trans <| and_or_left.trans <| or_congr and_comm and_comm

@[rocq_alias bi.and_exist_l]
theorem and_exists_left [BI PROP] {P : PROP} {Ψ : α → PROP} : P ∧ (∃ a, Ψ a) ⊣⊢ ∃ a, P ∧ Ψ a :=
  ⟨imp_elim_swap <| exists_elim fun _ =>
    imp_intro_swap (exists_intro (Ψ := fun a => iprop(P ∧ Ψ a)) _),
   exists_elim fun _ => and_mono_right (exists_intro _)⟩

@[rocq_alias bi.and_exist_r]
theorem and_exists_right [BI PROP] {Φ : α → PROP} {P : PROP} : (∃ a, Φ a) ∧ P ⊣⊢ ∃ a, Φ a ∧ P :=
  and_comm.trans <| and_exists_left.trans <| exists_congr fun _ => and_comm

@[rocq_alias bi.or_exist]
theorem or_exists [BI PROP] {Φ Ψ : α → PROP} : (∃ a, Φ a ∨ Ψ a) ⊣⊢ (∃ a, Φ a) ∨ (∃ a, Ψ a) :=
  ⟨exists_elim fun a => or_elim (or_intro_left_trans (exists_intro a)) (or_intro_right_trans (exists_intro a)),
   or_elim (exists_mono fun _ => or_intro_l) (exists_mono fun _ => or_intro_r)⟩

@[rocq_alias bi.and_alt]
theorem and_forall_ite [BI PROP] {P Q : PROP} :
    P ∧ Q ⊣⊢ «forall» (fun b : Bool => if b then P else Q) :=
  ⟨forall_intro (·.casesOn and_elim_r and_elim_l),
   and_intro (forall_elim true) (forall_elim false)⟩

@[rocq_alias bi.or_alt]
theorem or_exists_ite [BI PROP] {P Q : PROP} :
    P ∨ Q ⊣⊢ «exists» (fun b : Bool => if b then P else Q) :=
  ⟨or_elim (exists_intro (Ψ:=λ b => if b then P else Q) true)
           (exists_intro (Ψ:=λ b => if b then P else Q) false),
   exists_elim (Bool.rec or_intro_r or_intro_l ·)⟩

@[rocq_alias bi.bi_and_monoid]
instance bi_and_monoid [BI PROP] : LawfulBigOp and (iprop(True) : PROP) BiEntails where
  refl := .rfl
  symm h := h.symm
  trans h1 h2 := h1.trans h2
  comm := and_comm
  assoc := and_assoc
  left_id := left_id
  congr_l := and_congr_left

/-! # BI -/

@[rocq_alias bi.sep_mono_l]
theorem sep_mono_left [BI PROP] {P P' Q : PROP} (h : P ⊢ P') : P ∗ Q ⊢ P' ∗ Q := sep_mono h .rfl

@[rocq_alias bi.sep_mono_r]
theorem sep_mono_right [BI PROP] {P Q Q' : PROP} (h : Q ⊢ Q') : P ∗ Q ⊢ P ∗ Q' := sep_mono .rfl h

@[rw_mono_rule]
theorem sep_congr [BI PROP] {P P' Q Q' : PROP} (h1 : P ⊣⊢ Q) (h2 : P' ⊣⊢ Q') :
    (P ∗ P') ⊣⊢ (Q ∗ Q') := ⟨sep_mono h1.1 h2.1, sep_mono h1.2 h2.2⟩
#rocq_ignore bi.sep_flip_mono' "Use _mono."
#rocq_ignore bi.sep_mono' "Use _mono."
#rocq_ignore bi.sep_proper "Derivable from _ne with NonExpansive.eqv."

theorem sep_congr_left [BI PROP] {P P' Q : PROP} (h : P ⊣⊢ P') : P ∗ Q ⊣⊢ P' ∗ Q := sep_congr h .rfl

theorem sep_congr_right [BI PROP] {P Q Q' : PROP} (h : Q ⊣⊢ Q') : P ∗ Q ⊣⊢ P ∗ Q' := sep_congr .rfl h

@[rw_mono_rule, rocq_alias bi.wand_mono]
theorem wand_mono [BI PROP] {P P' Q Q' : PROP} (h1 : Q ⊢ P) (h2 : P' ⊢ Q') :
    (P -∗ P') ⊢ Q -∗ Q' := wand_intro <| (sep_mono_right h1).trans <| (wand_elim .rfl).trans h2
#rocq_ignore bi.wand_flip_mono' "Use _mono."
#rocq_ignore bi.wand_mono' "Use _mono."
#rocq_ignore bi.wand_proper "Derivable from _ne with NonExpansive.eqv."

theorem wand_mono_left [BI PROP] {P P' Q : PROP} (h : P' ⊢ P) : (P -∗ Q) ⊢ P' -∗ Q := wand_mono h .rfl

theorem wand_mono_right [BI PROP] {P Q Q' : PROP} (h : Q ⊢ Q') : (P -∗ Q) ⊢ P -∗ Q' := wand_mono .rfl h

@[rw_mono_rule]
theorem wand_congr [BI PROP] {P P' Q Q' : PROP} (h1 : P ⊣⊢ Q) (h2 : P' ⊣⊢ Q') :
    (P -∗ P') ⊣⊢ (Q -∗ Q') := ⟨wand_mono h1.2 h2.1, wand_mono h1.1 h2.2⟩

theorem wand_congr_left [BI PROP] {P P' Q : PROP} (h : P ⊣⊢ P') : (P -∗ Q) ⊣⊢ (P' -∗ Q) :=
  wand_congr h .rfl

theorem wand_congr_right [BI PROP] {P Q Q' : PROP} (h : Q ⊣⊢ Q') : (P -∗ Q) ⊣⊢ (P -∗ Q') :=
  wand_congr .rfl h

@[rocq_alias bi.sep_comm]
theorem sep_comm [BI PROP] {P Q : PROP} : P ∗ Q ⊣⊢ Q ∗ P := ⟨sep_symm, sep_symm⟩
instance [BI PROP] : Commutative (α := PROP) BiEntails sep := ⟨sep_comm⟩

@[rocq_alias bi.sep_assoc]
theorem sep_assoc [BI PROP] {P Q R : PROP} : (P ∗ Q) ∗ R ⊣⊢ P ∗ Q ∗ R :=
  ⟨sep_assoc_l, (sep_comm.trans <| sep_congr_left sep_comm).1.trans <|
    sep_assoc_l.trans (sep_comm.trans <| sep_congr_right sep_comm).2⟩
instance [BI PROP] : Associative (α := PROP) BiEntails sep := ⟨sep_assoc⟩

theorem sep_left_comm [BI PROP] {P Q R : PROP} : P ∗ Q ∗ R ⊣⊢ Q ∗ P ∗ R :=
  sep_assoc.symm.trans <| (sep_congr_left sep_comm).trans sep_assoc

theorem sep_right_comm [BI PROP] {P Q R : PROP} : (P ∗ Q) ∗ R ⊣⊢ (P ∗ R) ∗ Q :=
  sep_assoc.trans <| (sep_congr_right sep_comm).trans sep_assoc.symm

theorem sep_sep_sep_comm [BI PROP] {P Q R S : PROP} : (P ∗ Q) ∗ (R ∗ S) ⊣⊢ (P ∗ R) ∗ (Q ∗ S) :=
  sep_assoc.trans <| (sep_congr_right sep_left_comm).trans sep_assoc.symm

@[rocq_alias bi.emp_sep]
instance [BI PROP] : LeftId (α := PROP) BiEntails emp sep := ⟨emp_sep⟩

theorem sep_emp [BI PROP] {P : PROP} : P ∗ emp ⊣⊢ P := sep_comm.trans emp_sep
@[rocq_alias bi.sep_emp]
instance [BI PROP] : RightId (α := PROP) BiEntails emp sep := ⟨sep_emp⟩

@[rocq_alias bi.bi_sep_monoid]
instance bi_sep_monoid [BI PROP] : LawfulBigOp sep (emp : PROP) BiEntails where
  refl := .rfl
  symm h := h.symm
  trans h1 h2 := h1.trans h2
  comm := sep_comm
  assoc := sep_assoc
  left_id := left_id
  congr_l := sep_congr_left

@[rocq_alias bi.True_sep_2]
theorem true_sep_mpr [BI PROP] {P : PROP} : P ⊢ True ∗ P :=
  emp_sep.2.trans (sep_mono_left true_intro)

@[rocq_alias bi.sep_True_2]
theorem sep_true_mpr [BI PROP] {P : PROP} : P ⊢ P ∗ True :=
  true_sep_mpr.trans sep_comm.mp

@[rocq_alias bi.wand_intro_l]
theorem wand_intro_left [BI PROP] {P Q R : PROP} (h : Q ∗ P ⊢ R) : P ⊢ Q -∗ R :=
  wand_intro <| sep_symm.trans h

theorem wand_elim_swap [BI PROP] {P Q R : PROP} (h : Q ⊢ P -∗ R) : P ∗ Q ⊢ R :=
  sep_symm.trans (wand_elim h)

@[rocq_alias bi.wand_elim_l]
theorem wand_elim_left [BI PROP] {P Q : PROP} : (P -∗ Q) ∗ P ⊢ Q := wand_elim .rfl

theorem false_sep [BI PROP] {P : PROP} : False ∗ P ⊣⊢ False :=
  ⟨(sep_mono_left (P' := iprop(P -∗ False)) false_elim).trans wand_elim_left, false_elim⟩
@[rocq_alias bi.False_sep]
instance [BI PROP] : LeftAbsorb (· ⊣⊢@{PROP} ·) iprop(False) sep where
  left_absorb := false_sep

theorem sep_false [BI PROP] {P : PROP} : P ∗ False ⊣⊢ False := sep_comm.trans false_sep
@[rocq_alias bi.sep_False]
instance [BI PROP] : RightAbsorb (· ⊣⊢@{PROP} ·) iprop(False) sep where
  right_absorb := sep_false

@[rocq_alias bi.wand_elim_r]
theorem wand_elim_right [BI PROP] {P Q : PROP} : P ∗ (P -∗ Q) ⊢ Q := wand_elim_swap .rfl

@[rocq_alias bi.sep_or_l]
theorem sep_or_left [BI PROP] {P Q R : PROP} : P ∗ (Q ∨ R) ⊣⊢ (P ∗ Q) ∨ (P ∗ R) :=
  ⟨wand_elim_swap <| or_elim (wand_intro_left or_intro_l) (wand_intro_left or_intro_r),
   or_elim (sep_mono_right or_intro_l) (sep_mono_right or_intro_r)⟩

@[rocq_alias bi.sep_or_r]
theorem sep_or_right [BI PROP] {P Q R : PROP} : (P ∨ Q) ∗ R ⊣⊢ (P ∗ R) ∨ (Q ∗ R) :=
  sep_comm.trans <| sep_or_left.trans (or_congr sep_comm sep_comm)

@[rocq_alias bi.sep_exist_l]
theorem sep_exists_left [BI PROP] {P : PROP} {Ψ : α → PROP} : P ∗ (∃ a, Ψ a) ⊣⊢ ∃ a, P ∗ Ψ a :=
  ⟨wand_elim_swap <| exists_elim fun _ =>
    wand_intro_left (exists_intro (Ψ := fun a => iprop(P ∗ Ψ a)) _),
   exists_elim fun _ => sep_mono_right (exists_intro _)⟩

@[rocq_alias bi.sep_exist_r]
theorem sep_exists_right [BI PROP] {Φ : α → PROP} {Q : PROP} : (∃ a, Φ a) ∗ Q ⊣⊢ ∃ a, Φ a ∗ Q :=
  sep_comm.trans <| sep_exists_left.trans <| exists_congr fun _ => sep_comm

@[rocq_alias bi.sep_intro_emp_valid_l]
theorem sep_intro_emp_valid_left [BI PROP] {P Q R : PROP} (h1 : ⊢ P) (h2 : R ⊢ Q) : R ⊢ P ∗ Q :=
  h2.trans <| emp_sep.mpr.trans <| sep_mono_left h1

@[rocq_alias bi.sep_intro_emp_valid_r]
theorem sep_intro_emp_valid_right [BI PROP] {P Q R : PROP} (h1 : R ⊢ P) (h2 : ⊢ Q) : R ⊢ P ∗ Q :=
  h1.trans <| sep_emp.mpr.trans <| sep_mono_right h2

@[rocq_alias bi.sep_elim_emp_valid_l]
theorem sep_elim_emp_valid_left [BI PROP] {P Q R : PROP} (h1 : ⊢ P) (h2 : P ∗ R ⊢ Q) : R ⊢ Q :=
  emp_sep.mpr.trans <| (sep_mono_left h1).trans h2

@[rocq_alias bi.sep_elim_emp_valid_r]
theorem sep_elim_emp_valid_right [BI PROP] {P Q R : PROP} (h1 : ⊢ P) (h2 : R ∗ P ⊢ Q) : R ⊢ Q :=
  sep_emp.mpr.trans <| (sep_mono_right h1).trans h2

@[rocq_alias bi.sep_and_l]
theorem sep_and_left [BI PROP] {P Q R : PROP} : P ∗ (Q ∧ R) ⊢ (P ∗ Q) ∧ (P ∗ R) :=
  and_intro (sep_mono_right and_elim_l) (sep_mono_right and_elim_r)

@[rocq_alias bi.sep_and_r]
theorem sep_and_right [BI PROP] {P Q R : PROP} : (P ∧ Q) ∗ R ⊢ (P ∗ R) ∧ (Q ∗ R) :=
  and_intro (sep_mono_left and_elim_l) (sep_mono_left and_elim_r)

@[rocq_alias bi.sep_forall_l]
theorem sep_forall_left [BI PROP] {P : PROP} {Ψ : α → PROP} : P ∗ (∀ a, Ψ a) ⊢ ∀ a, P ∗ Ψ a :=
  forall_intro (sep_mono_right <| forall_elim ·)

@[rocq_alias bi.sep_forall_r]
theorem sep_forall_right [BI PROP] {Φ : α → PROP} {Q : PROP} : (∀ a, Φ a) ∗ Q ⊢ ∀ a, Φ a ∗ Q :=
  forall_intro (sep_mono_left <| forall_elim ·)

@[rocq_alias bi.wand_refl]
theorem wand_rfl [BI PROP] {P : PROP} : ⊢ P -∗ P := wand_intro emp_sep.1

@[rocq_alias bi.wand_curry]
theorem wand_curry [BI PROP] {P Q R: PROP} : (P -∗ Q -∗ R) ⊣⊢ ((P ∗ Q) -∗ R) := by
  refine ⟨?_, ?_⟩
  · refine wand_intro_left ?_
    refine sep_mono_left (sep_symm) |>.trans sep_assoc.1 |>.trans ?_
    exact wand_elim_swap (wand_elim_swap .rfl)
  · refine wand_intro_left <| wand_intro_left ?_
    refine sep_assoc.2.trans (sep_mono_left sep_symm) |>.trans ?_
    exact wand_elim_swap .rfl

@[rocq_alias bi.False_wand]
theorem false_wand [BI PROP] {P : PROP} : (False -∗ P) ⊣⊢ True :=
  ⟨true_intro, wand_intro_left <|
    (sep_mono_left (P' := iprop(True -∗ P)) false_elim).trans wand_elim_left⟩

@[rocq_alias bi.wand_apply]
theorem wand_apply [BI PROP] {P Q R S : PROP} (h1 : P ⊢ Q -∗ R) (h2 : S ⊢ P ∗ Q) : S ⊢ R :=
  h2.trans <| (sep_mono_left h1).trans wand_elim_left

@[rocq_alias bi.wand_trans]
theorem wand_trans [BI PROP] {P Q R : PROP} : (P -∗ Q) ∗ (Q -∗ R) ⊢ (P -∗ R) :=
  wand_intro_left <| sep_assoc.mpr.trans <| sep_mono_left wand_elim_right |>.trans wand_elim_right

@[rocq_alias bi.wand_frame_l]
theorem wand_frame_left [BI PROP] {P Q R : PROP} : (Q -∗ R) ⊢ (P ∗ Q -∗ P ∗ R) :=
  wand_intro_left <| sep_assoc.1.trans <| sep_mono_right wand_elim_right

@[rocq_alias bi.wand_frame_r]
theorem wand_frame_right [BI PROP] {P Q R : PROP} : (Q -∗ R) ⊢ (Q ∗ P -∗ R ∗ P) := by
  refine wand_intro_left ?_
  exact sep_symm.trans <| sep_assoc.mpr.trans <| sep_mono_left wand_elim_left

@[rocq_alias bi.wand_elim_r']
theorem wand_elim_left_trans [BI PROP] {P Q R : PROP} (h : Q ⊢ P -∗ R) : Q ∗ P ⊢ R :=
  (sep_mono_left h).trans wand_elim_left

@[rw_mono_rule]
theorem wandIff_congr [BI PROP] {P P' Q Q' : PROP} (h1 : P ⊣⊢ Q) (h2 : P' ⊣⊢ Q') :
    (P ∗-∗ P') ⊣⊢ (Q ∗-∗ Q') := and_congr (wand_congr h1 h2) (wand_congr h2 h1)

theorem wandIff_congr_left [BI PROP] {P P' Q : PROP} (h : P ⊣⊢ P') : (P ∗-∗ Q) ⊣⊢ (P' ∗-∗ Q) :=
  wandIff_congr h .rfl

theorem wandIff_congr_right [BI PROP] {P Q Q' : PROP} (h : Q ⊣⊢ Q') : (P ∗-∗ Q) ⊣⊢ (P ∗-∗ Q') :=
  wandIff_congr .rfl h

@[rocq_alias bi.wand_iff_refl]
theorem wandIff_refl [BI PROP] {P : PROP} : ⊢ P ∗-∗ P := and_intro wand_rfl wand_rfl

@[rocq_alias bi.iff_ne]
instance iff_ne [BI PROP] : OFE.NonExpansive₂ (BIBase.iff (PROP := PROP)) :=
  ⟨fun {_ _ _} h₁ {_ _} h₂ => and_ne.ne (imp_ne.ne h₁ h₂) (imp_ne.ne h₂ h₁)⟩
#rocq_ignore bi.iff_proper "Derivable from _ne with NonExpansive.eqv."

@[rocq_alias bi.iff_refl]
theorem iff_refl_alias [BI PROP] {Q P : PROP} : Q ⊢ iprop(P ↔ P) :=
  true_intro.trans <| and_intro (imp_intro and_elim_r) (imp_intro and_elim_r)

@[rocq_alias bi.wand_iff_ne]
instance wandIff_ne [BI PROP] : OFE.NonExpansive₂ (wandIff (PROP := PROP)) :=
  ⟨fun {_ _ _} h₁ {_ _} h₂ => and_ne.ne (wand_ne.ne h₁ h₂) (wand_ne.ne h₂ h₁)⟩
#rocq_ignore bi.wand_iff_proper "Derivable from _ne with NonExpansive.eqv."

@[rocq_alias bi.wand_entails]
theorem wand_entails [BI PROP] {P Q : PROP} (h : ⊢ P -∗ Q) : P ⊢ Q :=
  emp_sep.2.trans (wand_elim h)

@[rocq_alias bi.wand_entails']
theorem wand_entails_emp [BI PROP] {P Q : PROP} (h: (emp ⊢ (P -∗ Q))) : P ⊢ Q :=
 wand_entails h

@[rocq_alias bi.entails_wand]
theorem entails_wand [BI PROP] {P Q : PROP} (h : P ⊢ Q) : ⊢ P -∗ Q :=
  wand_intro (emp_sep.1.trans h)

@[rocq_alias bi.entails_wand']
theorem entails_wand_emp [BI PROP] {P Q : PROP} (h: P ⊢ Q) : emp ⊢ (P -∗ Q) :=
 entails_wand h

@[rocq_alias bi.equiv_wand_iff]
theorem equiv_wandIff [BI PROP] {P Q : PROP} (h : P ⊣⊢ Q) : ⊢ P ∗-∗ Q :=
  wandIff_refl.trans (wandIff_congr_left h).2

@[rocq_alias bi.wand_iff_equiv]
theorem wandIff_equiv [BI PROP] {P Q : PROP} (h : ⊢ P ∗-∗ Q) : P ⊣⊢ Q :=
  ⟨wand_entails (h.trans and_elim_l), wand_entails (h.trans and_elim_r)⟩

/-! # Pure -/

@[rocq_alias bi.pure_elim]
theorem pure_elim [BI PROP] (φ : Prop) {Q R : PROP} (h1 : Q ⊢ ⌜φ⌝) (h2 : φ → Q ⊢ R) : Q ⊢ R :=
  (and_self (PROP := PROP)).2.trans <| imp_elim <| h1.trans <| pure_elim' fun h =>
    imp_intro_swap <| and_elim_l.trans (h2 h)

@[rocq_alias bi.pure_mono]
theorem pure_mono [BI PROP] {φ1 φ2 : Prop} (h : φ1 → φ2) : ⌜φ1⌝ ⊢ (⌜φ2⌝ : PROP) :=
  pure_elim' <| pure_intro ∘ h
#rocq_ignore bi.pure_mono' "Use _mono."
#rocq_ignore bi.pure_proper "Derivable from _ne with NonExpansive.eqv."

theorem pure_congr [BI PROP] {φ1 φ2 : Prop} (h : φ1 ↔ φ2) : ⌜φ1⌝ ⊣⊢ (⌜φ2⌝ : PROP) :=
  ⟨pure_mono h.1,pure_mono h.2⟩

@[rocq_alias bi.pure_elim_l]
theorem pure_elim_left [BI PROP] {φ : Prop} {Q R : PROP} (h : φ → Q ⊢ R) : ⌜φ⌝ ∧ Q ⊢ R :=
  pure_elim _ and_elim_l <| and_elim_right_trans ∘ h

@[rocq_alias bi.pure_elim_r]
theorem pure_elim_right [BI PROP] {φ : Prop} {Q R : PROP} (h : φ → Q ⊢ R) : Q ∧ ⌜φ⌝ ⊢ R :=
  and_comm.1.trans (pure_elim_left h)

@[rocq_alias bi.pure_True]
theorem pure_true [BI PROP] {φ : Prop} (h : φ) : ⌜φ⌝ ⊣⊢ (True : PROP) := eq_true h ▸ .rfl

@[rocq_alias bi.pure_False]
theorem pure_false [BI PROP] {φ : Prop} (h : ¬ φ) : ⌜φ⌝ ⊣⊢ (False : PROP) := eq_false h ▸ .rfl

@[rocq_alias bi.pure_iff]
theorem pure_iff [BI PROP] {φ1 φ2 : Prop} (h : φ1 ↔ φ2) : ⌜φ1⌝ ⊣⊢ (⌜φ2⌝ : PROP) :=
  ⟨pure_mono h.mp, pure_mono h.mpr⟩

theorem pure_imp_elim [BI PROP] {φ : Prop} {R : PROP} (h : φ) : (⌜φ⌝ → R) ⊢ R :=
  (and_intro .rfl (pure_intro h)).trans imp_elim_left

@[rocq_alias bi.pure_and]
theorem pure_and [BI PROP] {φ1 φ2 : Prop} : ⌜φ1⌝ ∧ (⌜φ2⌝ : PROP) ⊣⊢ ⌜φ1 ∧ φ2⌝ :=
  ⟨pure_elim φ1 and_elim_l fun h => and_elim_right_trans <| pure_mono <| And.intro h,
   and_intro (pure_mono And.left) (pure_mono And.right)⟩

@[rocq_alias bi.pure_or]
theorem pure_or [BI PROP] {φ1 φ2 : Prop} : ⌜φ1⌝ ∨ (⌜φ2⌝ : PROP) ⊣⊢ ⌜φ1 ∨ φ2⌝ :=
  ⟨or_elim (pure_mono Or.inl) (pure_mono Or.inr),
   pure_elim' (·.elim (or_intro_left_trans ∘ pure_intro) (or_intro_right_trans ∘ pure_intro))⟩

@[rocq_alias bi.pure_impl]
theorem pure_imp [BI PROP] {φ1 φ2 : Prop} : ⌜φ1 → φ2⌝ ⊣⊢@{PROP} (⌜φ1⌝ → ⌜φ2⌝)   := by
  refine ⟨imp_intro <| pure_and.1.trans <| pure_mono (And.elim id), ?_⟩
  by_cases h : φ1
  · exact (imp_mp .rfl (pure_intro h)).trans (pure_mono fun h _ => h)
  · exact pure_intro h.elim

#rocq_ignore bi.pure_impl_1 "Proven as pure_imp.1"
#rocq_ignore bi.pure_impl_2 "Proven as pure_imp.2"

@[rocq_alias bi.pure_forall]
theorem pure_forall [BI PROP] {φ : α → Prop} :  ⌜∀ x, φ x⌝ ⊣⊢@{PROP} (∀ x, ⌜φ x⌝) := by
  refine ⟨forall_intro fun _ => pure_mono (· _), ?_⟩
  by_cases h : ∃ x, ¬φ x
  · let ⟨x, h⟩ := h
    exact (forall_elim x).trans (pure_mono h.elim)
  · exact pure_intro fun x => Classical.not_not.1 <| mt (⟨x, ·⟩) h

#rocq_ignore bi.pure_forall_1 "Proven as pure_forall.1"

@[rocq_alias bi.pure_exist]
theorem pure_exists [BI PROP] {φ : α → Prop} : (∃ x, ⌜φ x⌝ : PROP) ⊣⊢ ⌜∃ x, φ x⌝ :=
  ⟨exists_elim fun a => pure_mono (⟨a, ·⟩),
   pure_elim' fun ⟨x, h⟩ => (pure_intro h).trans (exists_intro (Ψ := fun a => iprop(⌜φ a⌝)) x)⟩

#rocq_ignore bi.bi_pure_forall_em "Do not need BiPureForall in Lean"

/-! # Affine -/

@[rocq_alias bi.affinely_ne]
instance affinely_ne [BI PROP] : OFE.NonExpansive (@affinely PROP _) where
  ne _ _ _ h := and_ne.1 .rfl h
#rocq_ignore bi.affinely_flip_mono' "Use _mono."
#rocq_ignore bi.affinely_mono' "Use _mono."
#rocq_ignore bi.affinely_proper "Derivable from _ne with NonExpansive.eqv."

@[rw_mono_rule]
theorem affinely_congr [BI PROP] {P P' : PROP} (h : P ⊣⊢ P') :
    <affine> P ⊣⊢ <affine> P' := and_congr_right h

@[rocq_alias bi.affinely_elim_emp]
theorem affinely_elim_emp [BI PROP] {P : PROP} : <affine> P ⊢ emp := and_elim_l

@[rocq_alias bi.affinely_elim]
theorem affinely_elim [BI PROP] {P : PROP} : <affine> P ⊢ P := and_elim_r

@[rw_mono_rule, rocq_alias bi.affinely_mono]
theorem affinely_mono [BI PROP] {P Q : PROP} : (P ⊢ Q) → <affine> P ⊢ <affine> Q := and_mono_right

@[rocq_alias bi.affinely_idemp]
theorem affinely_idem [BI PROP] {P : PROP} : <affine> <affine> P ⊣⊢ <affine> P :=
  and_assoc.symm.trans (and_congr_left and_self)

@[rocq_alias bi.affinely_intro']
theorem affinely_intro_of_affinely [BI PROP] {P Q : PROP}
    (h : <affine> P ⊢ Q) : <affine> P ⊢ <affine> Q :=
  affinely_idem.mpr.trans (affinely_mono h)

theorem affinely_intro_affinely [BI PROP] {P Q : PROP} (h : P ⊢ <affine> Q) :
    <affine> P ⊢ <affine> Q := (affinely_mono h).trans affinely_idem.1

@[rocq_alias bi.affinely_False]
theorem affinely_false [BI PROP] : <affine> False ⊣⊢ (False : PROP) := and_false

@[rocq_alias bi.affinely_emp]
theorem affinely_emp [BI PROP] : <affine> emp ⊣⊢ (emp : PROP) := and_self

@[rocq_alias bi.affinely_or]
theorem affinely_or [BI PROP] {P Q : PROP} : <affine> (P ∨ Q) ⊣⊢ <affine> P ∨ <affine> Q := and_or_left

@[rocq_alias bi.affinely_and]
theorem affinely_and [BI PROP] {P Q : PROP} : <affine> (P ∧ Q) ⊣⊢ <affine> P ∧ <affine> Q :=
  (and_congr_left and_self.symm).trans <| and_assoc.trans <|
    (and_congr_right (and_assoc.symm.trans <| (and_congr_left and_comm).trans and_assoc)).trans
      and_assoc.symm

@[rocq_alias bi.affinely_sep_2]
theorem affinely_sep_mpr [BI PROP] {P Q : PROP} : <affine> P ∗ <affine> Q ⊢ <affine> (P ∗ Q) :=
  and_intro
    (sep_mono affinely_elim_emp affinely_elim_emp |>.trans sep_emp.1)
    (sep_mono affinely_elim affinely_elim)

theorem affinely_sep_right [BI PROP] [BIPositive PROP] {P Q : PROP} :
    <affine> (P ∗ Q) ⊢ P ∗ <affine> Q :=
  (affinely_mono sep_symm).trans <| affinely_sep_l.trans sep_symm

@[rocq_alias bi.affinely_sep]
theorem affinely_sep [BI PROP] [BIPositive PROP] {P Q : PROP} :
    <affine> (P ∗ Q) ⊣⊢ <affine> P ∗ <affine> Q :=
  ⟨affinely_idem.2.trans <| (affinely_mono affinely_sep_right).trans affinely_sep_l, affinely_sep_mpr⟩

@[rocq_alias bi.affinely_forall]
theorem affinely_forall [BI PROP] {Φ : α → PROP} : <affine> (∀ a, Φ a) ⊢ ∀ a, <affine> (Φ a) :=
  forall_intro fun a => affinely_mono (forall_elim a)

@[rocq_alias bi.affinely_exist]
theorem affinely_exists [BI PROP] {Φ : α → PROP} : <affine> (∃ a, Φ a) ⊣⊢ ∃ a, <affine> (Φ a) :=
  and_exists_left

@[rocq_alias bi.affinely_True_emp]
theorem affinely_true [BI PROP] : <affine> True ⊣⊢ (emp : PROP) :=
  ⟨and_elim_l, and_intro .rfl true_intro⟩

@[rocq_alias bi.affinely_and_l]
theorem affinely_and_left [BI PROP] {P Q : PROP} : <affine> P ∧ Q ⊣⊢ <affine> (P ∧ Q) := and_assoc

@[rocq_alias bi.affinely_and_r]
theorem affinely_and_right [BI PROP] {P Q : PROP} : P ∧ <affine> Q ⊣⊢ <affine> (P ∧ Q) :=
  and_assoc.symm.trans <| (and_congr_left and_comm).trans and_assoc

@[rocq_alias bi.affinely_and_lr]
theorem affinely_and_left_right [BI PROP] {P Q : PROP} : <affine> P ∧ Q ⊣⊢ P ∧ <affine> Q :=
  affinely_and_left.trans affinely_and_right.symm

/-! # Affine instances -/

@[rocq_alias bi.emp_affine]
instance emp_affine [BI PROP] : Affine (PROP := PROP) iprop(emp) where
  affine := .rfl
#rocq_ignore bi.Affine_proper "Derivable from _ne with NonExpansive.eqv."

theorem affine_mono [BI PROP] {P Q : PROP} (h : P ⊢ Q) [Affine Q] : Affine P where
  affine := h.trans affine

@[rocq_alias bi.False_affine]
instance false_affine [BI PROP] : Affine (PROP := PROP) iprop(False) where
  affine := false_elim

@[rocq_alias bi.and_affine_l]
instance and_affine_left [BI PROP] (P Q : PROP) [Affine P] : Affine iprop(P ∧ Q) where
  affine := and_elim_l.trans affine

@[rocq_alias bi.and_affine_r]
instance and_affine_right [BI PROP] (P Q : PROP) [Affine Q] : Affine iprop(P ∧ Q) where
  affine := and_elim_r.trans affine

@[rocq_alias bi.or_affine]
instance or_affine [BI PROP] (P Q : PROP) [Affine P] [Affine Q] : Affine iprop(P ∨ Q) where
  affine := or_elim affine affine

@[rocq_alias bi.forall_affine]
instance forall_affine [Inhabited α] [BI PROP] (Φ : α → PROP) [∀ x, Affine (Φ x)] :
    Affine iprop(∀ x, Φ x) where
  affine := (forall_elim default).trans affine

@[rocq_alias bi.exist_affine]
instance exists_affine [BI PROP] (Φ : α → PROP) [∀ x, Affine (Φ x)] : Affine iprop(∃ x, Φ x) where
  affine := exists_elim fun _ => affine

@[rocq_alias bi.sep_affine]
instance sep_affine [BI PROP] (P Q : PROP) [Affine P] [Affine Q] : Affine iprop(P ∗ Q) where
  affine := (sep_mono affine affine).trans sep_emp.1

@[rocq_alias bi.affinely_affine]
instance affinely_affine [BI PROP] (P : PROP) : Affine iprop(<affine> P) where
  affine := affinely_elim_emp

instance [BIBase PROP] : Inhabited PROP where
  default := emp

/-! # Absorbing -/

@[rocq_alias bi.absorbingly_ne]
instance absorbingly_ne [BI PROP] : OFE.NonExpansive (@absorbingly PROP _) where
  ne _ _ _ h := sep_ne.1 .rfl h
#rocq_ignore bi.absorbingly_flip_mono' "Use _mono."
#rocq_ignore bi.absorbingly_mono' "Use _mono."
#rocq_ignore bi.absorbingly_proper "Derivable from _ne with NonExpansive.eqv."

@[rw_mono_rule]
theorem absorbingly_congr [BI PROP] {P P' : PROP} (h : P ⊣⊢ P') :
    <absorb> P ⊣⊢ <absorb> P' := sep_congr_right h

@[rocq_alias bi.absorbingly_intro]
theorem absorbingly_intro [BI PROP] {P : PROP} : P ⊢ <absorb> P := true_sep_mpr

@[rw_mono_rule, rocq_alias bi.absorbingly_mono]
theorem absorbingly_mono [BI PROP] {P Q : PROP} : (P ⊢ Q) → <absorb> P ⊢ <absorb> Q := sep_mono_right

@[rocq_alias bi.absorbingly_idemp]
theorem absorbingly_idem [BI PROP] {P : PROP} : <absorb> <absorb> P ⊣⊢ <absorb> P :=
  ⟨sep_assoc.2.trans (sep_mono_left true_intro), absorbingly_intro⟩

@[rocq_alias bi.absorbingly_absorbing]
instance absorbingly_absorbing [BI PROP] (P : PROP) : Absorbing iprop(<absorb> P) where
  absorbing := absorbingly_idem.1
#rocq_ignore bi.Absorbing_proper "Derivable from _ne with NonExpansive.eqv."

@[rocq_alias bi.absorbingly_pure]
theorem absorbingly_pure {φ : Prop} [BI PROP] : <absorb> ⌜φ⌝ ⊣⊢ (⌜φ⌝ : PROP) :=
  ⟨wand_elim_swap <| pure_elim' fun h => wand_intro_left <| pure_intro h, absorbingly_intro⟩

@[rocq_alias bi.absorbingly_True]
theorem absorbingly_true [BI PROP] : <absorb> True ⊣⊢ (True : PROP) := absorbingly_pure

@[rocq_alias bi.absorbingly_or]
theorem absorbingly_or [BI PROP] {P Q : PROP} : <absorb> (P ∨ Q) ⊣⊢ <absorb> P ∨ <absorb> Q :=
  sep_or_left

@[rocq_alias bi.absorbingly_and_1]
theorem absorbingly_and [BI PROP] {P Q : PROP} : <absorb> (P ∧ Q) ⊢ <absorb> P ∧ <absorb> Q :=
  and_intro (absorbingly_mono and_elim_l) (absorbingly_mono and_elim_r)

@[rocq_alias bi.absorbingly_forall]
theorem absorbingly_forall [BI PROP] {Φ : α → PROP} : <absorb> (∀ a, Φ a) ⊢ ∀ a, <absorb> (Φ a) :=
  forall_intro fun a => absorbingly_mono (forall_elim a)

@[rocq_alias bi.absorbingly_exist]
theorem absorbingly_exists [BI PROP] {Φ : α → PROP} :
    <absorb> (∃ a, Φ a) ⊣⊢ ∃ a, <absorb> (Φ a) := by
  simp [absorbingly, sep_exists_left]

@[rocq_alias bi.absorbingly_sep]
theorem absorbingly_sep [BI PROP] {P Q : PROP} : <absorb> (P ∗ Q) ⊣⊢ <absorb> P ∗ <absorb> Q :=
  absorbingly_idem.symm.trans <| (sep_congr_right sep_left_comm).trans sep_assoc.symm

@[rocq_alias bi.absorbingly_emp_True]
theorem absorbingly_emp [BI PROP] : <absorb> (emp : PROP) ⊣⊢ True := sep_emp

@[rocq_alias bi.absorbingly_wand]
theorem absorbingly_wand [BI PROP] {P Q : PROP} : <absorb> (P -∗ Q) ⊢ <absorb> P -∗ <absorb> Q :=
  wand_intro_left <| absorbingly_sep.2.trans <| absorbingly_mono wand_elim_right

@[rocq_alias bi.absorbingly_sep_l]
theorem absorbingly_sep_left [BI PROP] {P Q : PROP} : <absorb> P ∗ Q ⊣⊢ <absorb> (P ∗ Q) := sep_assoc

@[rocq_alias bi.absorbingly_sep_r]
theorem absorbingly_sep_right [BI PROP] {P Q : PROP} : P ∗ <absorb> Q ⊣⊢ <absorb> (P ∗ Q) :=
  sep_left_comm

@[rocq_alias bi.absorbingly_sep_lr]
theorem absorbingly_sep_left_right [BI PROP] {P Q : PROP} : <absorb> P ∗ Q ⊣⊢ P ∗ <absorb> Q :=
  absorbingly_sep_left.trans absorbingly_sep_right.symm

theorem affinely_absorbingly [BI PROP] [BIPositive PROP] {P : PROP} :
    <affine> <absorb> P ⊣⊢ <affine> P :=
  affinely_sep.trans <| (sep_congr_left affinely_true).trans emp_sep

@[rocq_alias bi.affinely_absorbingly_elim]
theorem affinely_absorbingly_elim [BI PROP] {P : PROP} [BIPositive PROP] :
    <affine> <absorb> P ⊣⊢ <affine> P :=
  ⟨affinely_absorbingly.mp, affinely_mono absorbingly_intro⟩

/-! # Absorbing instances -/

@[rocq_alias bi.pure_absorbing]
instance pure_absorbing [BI PROP] (φ : Prop) : Absorbing iprop(⌜φ⌝ : PROP) where
  absorbing := absorbingly_pure.1

@[rocq_alias bi.and_absorbing]
instance and_absorbing [BI PROP] (P Q : PROP) [Absorbing P] [Absorbing Q] :
    Absorbing iprop(P ∧ Q) where
  absorbing := absorbingly_and.trans (and_mono absorbing absorbing)

@[rocq_alias bi.or_absorbing]
instance or_absorbing [BI PROP] (P Q : PROP) [Absorbing P] [Absorbing Q] :
    Absorbing iprop(P ∨ Q) where
  absorbing := absorbingly_or.1.trans (or_mono absorbing absorbing)

@[rocq_alias bi.forall_absorbing]
instance forall_absorbing [BI PROP] (Φ : α → PROP) [∀ x, Absorbing (Φ x)] :
    Absorbing iprop(∀ x, Φ x) where
  absorbing := absorbingly_forall.trans (forall_mono fun _ => absorbing)

@[rocq_alias bi.exist_absorbing]
instance exists_absorbing [BI PROP] (Φ : α → PROP) [∀ x, Absorbing (Φ x)] :
    Absorbing iprop(∃ x, Φ x) where
  absorbing := absorbingly_exists.1.trans (exists_mono fun _ => absorbing)

@[rocq_alias bi.sep_absorbing_l]
instance sep_absorbing_left [BI PROP] (P Q : PROP) [Absorbing P] : Absorbing iprop(P ∗ Q) where
  absorbing := absorbingly_sep_left.2.trans (sep_mono_left absorbing)

@[rocq_alias bi.sep_absorbing_r]
instance sep_absorbing_right [BI PROP] (P Q : PROP) [Absorbing Q] : Absorbing iprop(P ∗ Q) where
  absorbing := absorbingly_sep_right.2.trans (sep_mono_right absorbing)

@[rocq_alias bi.bi_affine_absorbing]
instance (priority := default + 10) bi_affine_absorbing [BI PROP] [BIAffine PROP]
    (P : PROP) : Absorbing P where
  absorbing := (sep_mono_left affine).trans emp_sep.1

/-! # Affine / Absorbing Propositions -/

@[rocq_alias bi.affine_affinely]
theorem affine_affinely [BI PROP] (P : PROP) [Affine P] : <affine> P ⊣⊢ P :=
  ⟨affinely_elim, and_intro affine .rfl⟩

@[rocq_alias bi.True_emp_iff_BiAffine]
theorem biaffine_iff_true_emp [BI PROP] : BIAffine PROP ↔ (True : PROP) ⊢ emp :=
  ⟨fun _ => affine, fun h => ⟨fun _ => ⟨true_intro.trans h⟩⟩⟩

theorem biaffine_of_true_affine [BI PROP] [Affine (iprop(True) : PROP)] : BIAffine PROP :=
  biaffine_iff_true_emp.2 affine

@[rocq_alias bi.absorbing_absorbingly]
theorem absorbing_absorbingly [BI PROP] {P : PROP} [Absorbing P] : <absorb> P ⊣⊢ P :=
  ⟨absorbing, absorbingly_intro⟩

@[rocq_alias bi.emp_absorbing_all_absorbing]
theorem absorbing_of_emp_absorbing [BI PROP] [Absorbing (emp : PROP)] (P : PROP) : Absorbing P where
  absorbing := (absorbingly_mono emp_sep.2).trans <| absorbingly_sep_left.2.trans <|
    (sep_mono_left absorbing).trans emp_sep.1

@[rocq_alias bi.sep_elim_l]
theorem sep_elim_left [BI PROP] {P Q : PROP} : [TCOr (Affine Q) (Absorbing P)] → P ∗ Q ⊢ P
  | TCOr.l => (sep_mono_right affine).trans sep_emp.1
  | TCOr.r => (sep_mono_right true_intro).trans <| sep_comm.1.trans absorbing

@[rocq_alias bi.sep_elim_r]
theorem sep_elim_right [BI PROP] {P Q : PROP} [TCOr (Affine P) (Absorbing Q)] : P ∗ Q ⊢ Q :=
  sep_comm.1.trans sep_elim_left

@[rocq_alias bi.wand_absorbing_l]
instance wand_absorbing_left [BI PROP] (P Q : PROP) [Absorbing P] : Absorbing iprop(P -∗ Q) where
  absorbing := wand_intro_left <| sep_assoc.2.trans <| (sep_mono_left sep_elim_left).trans wand_elim_right

@[rocq_alias bi.wand_absorbing_r]
instance wand_absorbing_right [BI PROP] (P Q : PROP) [Absorbing Q] : Absorbing iprop(P -∗ Q) where
  absorbing := absorbingly_wand.trans (wand_mono absorbingly_intro absorbing)

@[rocq_alias bi.sep_and]
theorem sep_and [BI PROP] {P Q : PROP}
    [TCOr (Affine P) (Absorbing Q)] [TCOr (Affine Q) (Absorbing P)] : P ∗ Q ⊢ P ∧ Q :=
  and_intro sep_elim_left sep_elim_right

@[rocq_alias bi.affinely_intro]
theorem affinely_intro [BI PROP] {P Q : PROP} [Affine P] (h : P ⊢ Q) : P ⊢ <affine> Q :=
  (affine_affinely _).2.trans (affinely_mono h)

@[rocq_alias bi.emp_and]
theorem emp_and [BI PROP] {P : PROP} [Affine P] : emp ∧ P ⊣⊢ P :=
  ⟨and_elim_r, and_intro affine .rfl⟩
@[rocq_alias bi.emp_and']
instance emp_and_biaffine [BI PROP] [BIAffine PROP] : LeftId (α := PROP) BiEntails emp and := ⟨emp_and⟩

@[rocq_alias bi.and_emp]
theorem and_emp [BI PROP] {P : PROP} [Affine P] : P ∧ emp ⊣⊢ P := and_comm.trans emp_and
@[rocq_alias bi.and_emp']
instance and_emp_biaffine [BI PROP] [BIAffine PROP] : RightId (α := PROP) BiEntails emp and := ⟨and_emp⟩

@[rocq_alias bi.emp_or]
theorem emp_or [BI PROP] {P : PROP} [Affine P] : emp ∨ P ⊣⊢ emp := ⟨or_elim .rfl affine, or_intro_l⟩

@[rocq_alias bi.emp_wand]
theorem emp_wand [BI PROP] {P : PROP} : (emp -∗ P) ⊣⊢ P :=
  ⟨emp_sep.mpr.trans wand_elim_right, wand_intro_left emp_sep.mp⟩

@[rocq_alias bi.or_emp]
theorem or_emp [BI PROP] {P : PROP} [Affine P] : P ∨ emp ⊣⊢ emp := or_comm.trans emp_or

@[rocq_alias bi.True_emp]
theorem true_emp [BI PROP] [h : BIAffine PROP] : (True : PROP) ⊣⊢ emp :=
  ⟨biaffine_iff_true_emp.1 h, true_intro⟩

@[rocq_alias bi.True_affine_all_affine]
theorem True_affine_all_affine [BI PROP] [Affine (iprop(True) : PROP)] (P : PROP) : Affine P where
  affine := true_intro.trans (Affine.affine (P := iprop((True : PROP))))

instance [BI PROP] [BIAffine PROP] (P : PROP) : Absorbing P where
  absorbing := (sep_mono_left affine).trans emp_sep.1

@[rocq_alias bi.True_sep]
theorem true_sep [BI PROP] {P : PROP} [Absorbing P] : True ∗ P ⊣⊢ P := ⟨absorbing, true_sep_mpr⟩
instance [BI PROP] [BIAffine PROP] : LeftId (α := PROP) BiEntails iprop(True) sep := ⟨true_sep⟩

@[rocq_alias bi.True_sep']
theorem true_sep_flip [BI PROP] {P : PROP} [Absorbing P] : P ⊣⊢ True ∗ P := true_sep.symm

@[rocq_alias bi.sep_True]
theorem sep_true [BI PROP] {P : PROP} [Absorbing P] : P ∗ True ⊣⊢ P := sep_comm.trans true_sep
instance [BI PROP] [BIAffine PROP] : RightId (α := PROP) BiEntails iprop(True) sep := ⟨sep_true⟩

@[rocq_alias bi.sep_True']
theorem sep_true_flip [BI PROP] {P : PROP} [Absorbing P] : P ⊣⊢ P ∗ True :=
  ⟨sep_emp.mpr.trans (sep_mono_right true_intro), sep_comm.mp.trans true_sep.mp⟩

@[rocq_alias bi.bi_affine_positive]
instance bi_affine_positive [BI PROP] [BIAffine PROP] : BIPositive PROP where
  affinely_sep_l := (affine_affinely _).1.trans (sep_mono_left (affine_affinely _).2)

@[rocq_alias bi.impl_wand_1]
theorem imp_wand [BI PROP] [BIAffine PROP] {P Q : PROP} : (P → Q) ⊢ P -∗ Q :=
  wand_intro <| sep_and.trans imp_elim_left

theorem pure_sep [BI PROP] {φ1 φ2 : Prop} : ⌜φ1⌝ ∗ (⌜φ2⌝ : PROP) ⊣⊢ ⌜φ1 ∧ φ2⌝ :=
  ⟨sep_and.trans pure_and.1, pure_elim' fun ⟨a, b⟩ => by
    rw [eq_true a, eq_true b]; exact true_sep_mpr⟩

theorem pure_wand_mpr [BI PROP] {φ1 φ2 : Prop} : ⌜φ1 → φ2⌝ ⊢ (⌜φ1⌝ -∗ (⌜φ2⌝ : PROP)) :=
  pure_elim' fun a => wand_intro <| absorbing.trans (pure_mono a)

theorem pure_wand [BI PROP] {φ1 φ2 : Prop} : (⌜φ1⌝ -∗ (⌜φ2⌝ : PROP)) ⊣⊢ ⌜φ1 → φ2⌝ := by
  refine ⟨(imp_intro_swap ?_).trans pure_imp.2, pure_wand_mpr⟩
  exact pure_elim_left fun h => true_sep_mpr.trans (eq_true h ▸ wand_elim_right)

/-! # Properties of the persistence modality -/

@[rw_mono_rule]
theorem persistently_congr [BI PROP] {P P' : PROP} (h : P ⊣⊢ P') :
    <pers> P ⊣⊢ <pers> P' := ⟨persistently_mono h.1, persistently_mono h.2⟩
#rocq_ignore bi.persistently_flip_mono' "Use _mono."
#rocq_ignore bi.persistently_mono' "Use _mono."
#rocq_ignore bi.persistently_proper "Derivable from _ne with NonExpansive.eqv."

@[rocq_alias bi.persistently_persistent]
instance persistently_persistent [BI PROP] (P : PROP) : Persistent iprop(<pers> P) where
  persistent := persistently_idem_2
#rocq_ignore bi.Persistent_proper "Derivable from _ne with NonExpansive.eqv."

theorem persistently_absorb_right [BI PROP] {P Q : PROP} : P ∗ <pers> Q ⊢ <pers> Q :=
  sep_comm.1.trans persistently_absorb_l

@[rocq_alias bi.absorbingly_elim_persistently]
theorem absorbingly_persistently [BI PROP] {P : PROP} : <absorb> <pers> P ⊣⊢ <pers> P :=
  ⟨persistently_absorb_right, absorbingly_intro⟩

@[rocq_alias bi.persistently_absorbing]
instance persistently_absorbing [BI PROP] (P : PROP) : Absorbing iprop(<pers> P) where
  absorbing := absorbingly_persistently.1

@[rocq_alias bi.persistently_forall_1]
theorem persistently_forall_mp [BI PROP] {Ψ : α → PROP} : <pers> (∀ a, Ψ a) ⊢ ∀ a, <pers> (Ψ a) :=
  forall_intro fun x => persistently_mono (forall_elim x)

@[rocq_alias bi.persistently_forall]
theorem persistently_forall [BI PROP] [h : BIPersistentlyForall PROP] {Ψ : α → PROP} :
    <pers> (∀ a, Ψ a) ⊣⊢ ∀ a, <pers> (Ψ a) := by
  refine ⟨persistently_forall_mp, (forall_intro fun _ => imp_intro <| pure_elim_right ?_).trans (h.1 _)⟩
  rintro ⟨_, rfl⟩; apply forall_elim

@[rocq_alias bi.persistently_exist]
theorem persistently_exists [BI PROP] {Ψ : α → PROP} : <pers> (∃ a, Ψ a) ⊣⊢ ∃ a, <pers> (Ψ a) := by
  refine ⟨persistently_sExists_1.trans ?_, exists_elim fun a => persistently_mono (exists_intro a)⟩
  refine exists_elim fun _ => pure_elim_left fun ⟨_, eq⟩ => eq ▸ sExists_intro ⟨_, rfl⟩

@[rocq_alias bi.persistently_and]
theorem persistently_and [BI PROP] {P Q : PROP} : <pers> (P ∧ Q) ⊣⊢ <pers> P ∧ <pers> Q :=
  ⟨and_intro (persistently_mono and_elim_l) (persistently_mono and_elim_r), persistently_and_2⟩

theorem persistently_ite {p : Bool} [BI PROP] {P Q : PROP} :
    iprop(<pers> if p then P else Q) = iprop(if p then <pers> P else <pers> Q) := by
  cases p <;> simp

@[rocq_alias bi.persistently_or]
theorem persistently_or [BI PROP] {P Q : PROP} : <pers> (P ∨ Q) ⊣⊢ <pers> P ∨ <pers> Q :=
  (persistently_congr or_exists_ite).trans <| persistently_exists.trans <|
    (or_exists_ite.trans <| exists_congr fun _ => persistently_ite (PROP := PROP) ▸ .rfl).symm

@[rocq_alias bi.persistently_impl]
theorem persistently_imp [BI PROP] {P Q : PROP} : <pers> (P → Q) ⊢ (<pers> P → <pers> Q) :=
  imp_intro <| persistently_and.2.trans (persistently_mono imp_elim_left)

@[rocq_alias bi.persistently_emp_intro]
theorem persistently_emp_intro [BI PROP] {P : PROP} : P ⊢ <pers> emp :=
  emp_sep.2.trans <| (sep_mono_left persistently_emp_2).trans (persistently_absorb_l (Q := P))

@[rocq_alias bi.persistently_emp]
theorem persistently_emp [BI PROP] : <pers> (emp : PROP) ⊣⊢ True :=
  ⟨true_intro, persistently_emp_intro⟩

@[rocq_alias bi.persistently_True]
theorem persistently_true [BI PROP] : <pers> (True : PROP) ⊣⊢ True :=
  ⟨true_intro, persistently_emp.2.trans <| persistently_mono true_intro⟩

@[rocq_alias bi.persistently_True_emp]
theorem persistently_True_emp [BI PROP] : <pers> (True : PROP) ⊣⊢ <pers> emp := by
  refine ⟨?_, persistently_mono true_intro⟩
  exact (persistently_emp_intro : <pers> (True : PROP) ⊢ <pers> emp)

@[rocq_alias bi.persistently_affinely_elim]
theorem persistently_affinely [BI PROP] {P : PROP} : <pers> <affine> P ⊣⊢ <pers> P :=
  ⟨persistently_mono affinely_elim,
   (and_intro persistently_emp_intro .rfl).trans persistently_and.2⟩

theorem persistently_and_affinely_sep [BI PROP] {P Q : PROP} : <pers> P ∧ Q ⊢ <affine> P ∗ Q :=
  (and_mono_left persistently_affinely.2).trans persistently_and_l

@[rocq_alias bi.persistently_and_sep_assoc]
theorem persistently_and_sep_assoc [BI PROP] {P Q R : PROP} :
    <pers> P ∧ (Q ∗ R) ⊣⊢ (<pers> P ∧ Q) ∗ R := by
  constructor
  · refine (and_mono_left persistently_idem_2).trans <| persistently_and_affinely_sep.trans <|
      sep_assoc.2.trans <| sep_mono_left <| and_intro ?_ ?_
    · exact (sep_mono_left and_elim_r).trans persistently_absorb_l
    · exact (sep_mono_left and_elim_l).trans emp_sep.1
  · exact and_intro ((sep_mono_left and_elim_l).trans persistently_absorb_l) (sep_mono_left and_elim_r)

@[rocq_alias bi.intuitionistically_elim]
theorem intuitionistically_elim [BI PROP] {P : PROP} : □ P ⊢ P :=
  and_comm.2.trans <| persistently_and_affinely_sep.trans <| sep_emp.1.trans affinely_elim

@[rocq_alias bi.persistently_into_absorbingly]
theorem absorbingly_of_persistently [BI PROP] {P : PROP} : <pers> P ⊢ <absorb> P :=
  and_true.2.trans <| (and_mono_right emp_sep.2).trans <| persistently_and_sep_assoc.1.trans <|
    (sep_mono_left <| and_comm.1.trans intuitionistically_elim).trans sep_comm.1

@[rocq_alias bi.persistently_elim]
theorem persistently_elim [BI PROP] {P : PROP} [Absorbing P] : <pers> P ⊢ P :=
  absorbingly_of_persistently.trans absorbing

@[rocq_alias bi.persistently_idemp]
theorem persistently_idem [BI PROP] {P : PROP} : <pers> <pers> P ⊣⊢ <pers> P :=
  ⟨absorbingly_of_persistently.trans absorbingly_persistently.1, persistently_idem_2⟩

#rocq_ignore bi.persistently_idemp_1 "Use `persistently_idem.mp`."

@[rocq_alias bi.persistently_intro']
theorem persistently_intro_persistently [BI PROP] {P Q : PROP} (h : <pers> P ⊢ Q) : <pers> P ⊢ <pers> Q :=
 persistently_idem.2.trans (persistently_mono h)

@[rocq_alias bi.persistently_pure]
theorem persistently_pure {φ : Prop} [BI PROP] : <pers> ⌜φ⌝ ⊣⊢ (⌜φ⌝ : PROP) :=
  ⟨absorbingly_of_persistently.trans absorbingly_pure.1,
   pure_elim' fun h => persistently_true.2.trans <| persistently_mono <| pure_intro h⟩

@[rocq_alias bi.persistently_and_sep_l_1]
theorem persistently_and_imp_sep [BI PROP] {P Q : PROP} : <pers> P ∧ Q ⊢ <pers> P ∗ Q :=
  (and_mono_right emp_sep.2).trans <| persistently_and_sep_assoc.1.trans <| sep_mono_left and_elim_l

@[rocq_alias bi.persistently_and_sep_r_1]
theorem and_persistently_imp_sep [BI PROP] {P Q : PROP} : P ∧ <pers> Q ⊢ P ∗ <pers> Q :=
  and_symm.trans <| persistently_and_imp_sep.trans sep_symm

@[rocq_alias bi.persistently_sep_dup]
theorem persistently_sep_persistently [BI PROP] {P : PROP} : <pers> P ∗ <pers> P ⊣⊢ <pers> P :=
  ⟨sep_elim_right, and_self.2.trans persistently_and_imp_sep⟩

@[rocq_alias bi.persistently_and_sep]
theorem persistently_and_sep [BI PROP] {P Q : PROP} : <pers> (P ∧ Q) ⊢ <pers> (P ∗ Q) :=
  persistently_and.1.trans <| (and_mono_left persistently_idem.2).trans <|
  persistently_and.2.trans <| persistently_mono <|
  (and_mono_right emp_sep.2).trans <| persistently_and_sep_assoc.1.trans <|
  sep_mono_left <| and_comm.1.trans intuitionistically_elim

@[rocq_alias bi.and_sep_persistently]
theorem persistently_and_persistently_sep [BI PROP] {P Q : PROP} :
    <pers> P ∧ <pers> Q ⊣⊢ <pers> P ∗ <pers> Q :=
  ⟨persistently_and_imp_sep, and_intro persistently_absorb_l persistently_absorb_right⟩

@[rocq_alias bi.persistently_sep_2]
theorem persistently_sep_mpr [BI PROP] {P Q : PROP} : <pers> P ∗ <pers> Q ⊢ <pers> (P ∗ Q) :=
  (persistently_and.trans persistently_and_persistently_sep).2.trans persistently_and_sep

@[rocq_alias bi.persistently_sep]
theorem persistently_sep [BI PROP] [BIPositive PROP] {P Q : PROP} :
    <pers> (P ∗ Q) ⊣⊢ <pers> P ∗ <pers> Q := by
  refine ⟨persistently_affinely.2.trans ?_, persistently_sep_mpr⟩
  refine persistently_mono affinely_sep.1 |>.trans ?_ |>.trans persistently_and_persistently_sep.1
  exact and_intro
    (persistently_mono <| (sep_mono_right affinely_elim_emp).trans <| sep_emp.1.trans affinely_elim)
    (persistently_mono <| (sep_mono_left affinely_elim_emp).trans <| emp_sep.1.trans affinely_elim)

@[rocq_alias bi.persistently_alt_fixpoint]
theorem self_sep_persistently [BI PROP] {P : PROP} : P ∗ <pers> P ⊣⊢ <pers> P :=
  ⟨sep_elim_right, and_self.2.trans persistently_and_l⟩

@[rocq_alias bi.persistently_alt_fixpoint']
theorem affinely_sep_persistently [BI PROP] {P : PROP} : <affine> P ∗ <pers> P ⊣⊢ <pers> P :=
  (sep_congr_right persistently_affinely.symm).trans <|
  self_sep_persistently.trans persistently_affinely

@[rocq_alias bi.persistently_wand]
theorem persistently_wand [BI PROP] {P Q : PROP} : <pers> (P -∗ Q) ⊢ (<pers> P -∗ <pers> Q) :=
  wand_intro <| persistently_sep_mpr.trans <| persistently_mono wand_elim_left

@[rocq_alias bi.persistently_entails_l]
theorem persistently_entails_left [BI PROP] {P Q : PROP} (h : P ⊢ <pers> Q) : P ⊢ <pers> Q ∗ P :=
  (and_intro h .rfl).trans persistently_and_imp_sep

@[rocq_alias bi.persistently_entails_r]
theorem persistently_entails_right [BI PROP] {P Q : PROP} (h : P ⊢ <pers> Q) : P ⊢ P ∗ <pers> Q :=
  (persistently_entails_left h).trans sep_symm

@[rocq_alias bi.persistently_impl_wand_2]
theorem persistently_imp_wand_mpr [BI PROP] {P Q : PROP} : <pers> (P -∗ Q) ⊢ <pers> (P → Q) :=
  persistently_intro_persistently <| imp_intro <| persistently_and_affinely_sep.trans <|
  (sep_mono_left affinely_elim).trans wand_elim_left

@[rocq_alias bi.impl_wand_persistently_2]
theorem imp_wand_persistently_mpr [BI PROP] {P Q : PROP} : (<pers> P -∗ Q) ⊢ (<pers> P → Q) :=
  imp_intro <| and_persistently_imp_sep.trans wand_elim_left

theorem persistently_emp_affine [BI PROP] [BIAffine PROP] : <pers> (emp : PROP) ⊣⊢ emp :=
  persistently_emp.trans true_emp

@[rocq_alias bi.persistently_and_sep_l]
theorem persistently_and_iff_sep [BI PROP] [BIAffine PROP] {P Q : PROP} :
    <pers> P ∧ Q ⊣⊢ <pers> P ∗ Q := ⟨persistently_and_imp_sep, sep_and⟩

@[rocq_alias bi.persistently_and_sep_r]
theorem and_persistently_iff_sep [BI PROP] [BIAffine PROP] {P Q : PROP} :
    P ∧ <pers> Q ⊣⊢ P ∗ <pers> Q := ⟨and_persistently_imp_sep, sep_and⟩

@[rocq_alias bi.persistently_impl_wand]
theorem persistently_imp_wand [BI PROP] [BIAffine PROP] {P Q : PROP} :
    <pers> (P → Q) ⊣⊢ <pers> (P -∗ Q) := by
  refine ⟨persistently_intro_persistently (wand_intro ?_), persistently_imp_wand_mpr⟩
  exact persistently_and_iff_sep.2.trans <| (and_mono_left persistently_elim).trans imp_elim_left

@[rocq_alias bi.impl_wand_persistently]
theorem imp_wand_persistently [BI PROP] [BIAffine PROP] {P Q : PROP} :
    (<pers> P → Q) ⊣⊢ (<pers> P -∗ Q) := ⟨imp_wand, imp_wand_persistently_mpr⟩

@[rocq_alias bi.wand_alt]
theorem wand_iff_exists_persistently [BI PROP] [BIAffine PROP] {P Q : PROP} :
    (P -∗ Q) ⊣⊢ ∃ R, R ∗ <pers> (P ∗ R → Q) := by
  constructor
  · refine (sep_true.2.trans ?_).trans (exists_intro iprop(P -∗ Q))
    exact sep_mono_right <| persistently_pure.2.trans <| persistently_intro_persistently <|
      imp_intro <| (and_mono persistently_pure.1 wand_elim_right).trans and_elim_r
  · exact exists_elim fun R => wand_intro_left <| sep_assoc.2.trans <|
      and_persistently_iff_sep.2.trans <| (and_mono_right persistently_elim).trans imp_elim_right

@[rocq_alias bi.persistently_and_emp]
theorem persistently_and_emp {P : PROP} [BI PROP] : <pers> P ⊣⊢ <pers> (emp ∧ P) :=
  ⟨(and_intro persistently_emp_intro .rfl).trans persistently_and.2,
   (persistently_mono and_elim_r).trans .rfl⟩

@[rocq_alias bi.persistently_and_sep_elim_emp]
theorem persistently_and_sep_elim_emp {P Q : PROP} [BI PROP] : <pers> P ∧ Q ⊢ (emp ∧ P) ∗ Q :=
  (and_mono persistently_and_emp.1 BIBase.Entails.rfl).trans persistently_and_l

@[rocq_alias bi.persistently_and_emp_elim]
theorem persistently_and_emp_elim {P : PROP} [BI PROP] : emp ∧ <pers> P ⊢ P :=
  and_comm.1.trans <| persistently_and_sep_elim_emp.trans <| sep_emp.1.trans and_elim_r

/-! # Persistence instances -/

@[rocq_alias bi.pure_persistent]
instance pure_persistent (φ : Prop) [BI PROP] : Persistent (PROP := PROP) iprop(⌜φ⌝) where
  persistent := persistently_pure.2

@[rocq_alias bi.emp_persistent]
instance emp_persistent [BI PROP] : Persistent (PROP := PROP) iprop(emp) where
  persistent := persistently_emp_intro

@[rocq_alias bi.and_persistent]
instance and_persistent [BI PROP] (P Q : PROP) [Persistent P] [Persistent Q] :
    Persistent iprop(P ∧ Q) where
  persistent := (and_mono persistent persistent).trans persistently_and.2

@[rocq_alias bi.or_persistent]
instance or_persistent [BI PROP] (P Q : PROP) [Persistent P] [Persistent Q] :
    Persistent iprop(P ∨ Q) where
  persistent := (or_mono persistent persistent).trans persistently_or.2

theorem sForall_persistent [BI PROP] [h : BIPersistentlyForall PROP] (Ψ : PROP → Prop)
    (H : ∀ p, Ψ p → Persistent p) : Persistent iprop(sForall Ψ) where
  persistent := by
    refine (forall_intro fun _ => imp_intro ?_).trans (h.1 _)
    exact pure_elim_right fun h => (sForall_elim h).trans (H _ h).1

@[rocq_alias bi.forall_persistent]
instance forall_persistent [BI PROP] [BIPersistentlyForall PROP] (Ψ : α → PROP)
    [h : ∀ x, Persistent (Ψ x)] : Persistent iprop(∀ x, Ψ x) :=
  sForall_persistent _ fun _ ⟨_, eq⟩ => eq ▸ h _

theorem sExists_persistent [BI PROP] (Ψ : PROP → Prop)
    (H : ∀ p, Ψ p → Persistent p) : Persistent iprop(sExists Ψ) where
  persistent := sExists_elim fun _ hp => (H _ hp).1.trans (persistently_mono <| sExists_intro hp)

@[rocq_alias bi.exist_persistent]
instance exists_persistent [BI PROP] (Ψ : α → PROP) [h : ∀ x, Persistent (Ψ x)] :
    Persistent iprop(∃ x, Ψ x) := sExists_persistent _ fun _ ⟨_, eq⟩ => eq ▸ h _

@[rocq_alias bi.sep_persistent]
instance sep_persistent [BI PROP] (P Q : PROP) [Persistent P] [Persistent Q] :
    Persistent iprop(P ∗ Q) where
  persistent := (sep_mono persistent persistent).trans persistently_sep_mpr

@[rocq_alias bi.affinely_persistent]
instance affinely_persistent [BI PROP] (P : PROP) [Persistent P] : Persistent iprop(<affine> P) :=
  inferInstanceAs (Persistent iprop(_ ∧ _))

@[rocq_alias bi.absorbingly_persistent]
instance absorbingly_persistent [BI PROP] (P : PROP) [Persistent P] :
    Persistent iprop(<absorb> P) :=
  inferInstanceAs (Persistent iprop(_ ∗ _))

/-! # The intuitionistic modality -/

@[rocq_alias bi.intuitionistically_ne]
instance intuitionistically_ne [BI PROP] : OFE.NonExpansive (@intuitionistically PROP _) where
  ne _ _ _ h := affinely_ne.1 (persistently_ne.1 h)
#rocq_ignore bi.intuitionistically_flip_mono' "Use _mono."
#rocq_ignore bi.intuitionistically_mono' "Use _mono."
#rocq_ignore bi.intuitionistically_proper "Derivable from _ne with NonExpansive.eqv."

@[rw_mono_rule]
theorem intuitionistically_congr [BI PROP] {P Q : PROP} (h : P ⊣⊢ Q) : □ P ⊣⊢ □ Q :=
  affinely_congr <| persistently_congr h

@[rw_mono_rule]
theorem intuitionistically_mono [BI PROP] {P Q : PROP} (h : P ⊢ Q) : □ P ⊢ □ Q :=
  affinely_mono <| persistently_mono h

@[rocq_alias bi.intuitionistically_affine]
instance intuitionistically_affine [BI PROP] (P : PROP) : Affine iprop(□ P) :=
  inferInstanceAs (Affine iprop(<affine> _))

@[rocq_alias bi.intuitionistically_persistent]
instance intuitionistically_persistent [BI PROP] (P : PROP) : Persistent iprop(□ P) :=
  inferInstanceAs (Persistent iprop(<affine> _))

instance intuitionisticallyIf_persistent [BI PROP] (P : PROP) : Persistent iprop(□?true P) :=
  inferInstanceAs (Persistent iprop(□ _))

@[rocq_alias bi.intuitionistically_def]
theorem intuitionistically_def [BI PROP] {P : PROP} : iprop(□ P) = iprop(<affine> <pers> P) := rfl

@[rocq_alias bi.intuitionistically_elim_emp]
theorem intuitionistically_elim_emp [BI PROP] {P : PROP} : □ P ⊢ emp := affinely_elim_emp

@[rocq_alias bi.intuitionistically_emp]
theorem intuitionistically_emp [BI PROP] : □ emp ⊣⊢ (emp : PROP) :=
  (affinely_congr persistently_emp).trans affinely_true

@[rocq_alias bi.intuitionistically_False]
theorem intuitionistically_false [BI PROP] : □ False ⊣⊢ (False : PROP) :=
  (affinely_congr persistently_pure).trans affinely_false

@[rocq_alias bi.intuitionistically_True_emp]
theorem intuitionistically_true [BI PROP] : □ True ⊣⊢ (emp : PROP) :=
  (affinely_congr persistently_true).trans affinely_true

@[rocq_alias bi.intuitionistically_and]
theorem intuitionistically_and [BI PROP] {P Q : PROP} : □ (P ∧ Q) ⊣⊢ □ P ∧ □ Q :=
  (affinely_congr persistently_and).trans affinely_and

@[rocq_alias bi.intuitionistically_forall]
theorem intuitionistically_forall [BI PROP] {Φ : α → PROP} : □ (∀ x, Φ x) ⊢ ∀ x, □ Φ x :=
  (affinely_mono persistently_forall_mp).trans affinely_forall

@[rocq_alias bi.intuitionistically_or]
theorem intuitionistically_or [BI PROP] {P Q : PROP} : □ (P ∨ Q) ⊣⊢ □ P ∨ □ Q :=
  (affinely_congr persistently_or).trans affinely_or

@[rocq_alias bi.intuitionistically_exist]
theorem intuitionistically_exists [BI PROP] {Φ : α → PROP} : □ (∃ x, Φ x) ⊣⊢ ∃ x, □ Φ x :=
  (affinely_congr persistently_exists).trans affinely_exists

@[rocq_alias bi.intuitionistically_sep_2]
theorem intuitionistically_sep_mpr [BI PROP] {P Q : PROP} : □ P ∗ □ Q ⊢ □ (P ∗ Q) :=
  affinely_sep_mpr.trans (affinely_mono persistently_sep_mpr)

@[rocq_alias bi.intuitionistically_sep]
theorem intuitionistically_sep [BI PROP] [BIPositive PROP] {P Q : PROP} : □ (P ∗ Q) ⊣⊢ □ P ∗ □ Q :=
  (affinely_congr persistently_sep).trans affinely_sep

@[rocq_alias bi.intuitionistically_idemp]
theorem intuitionistically_idem [BI PROP] {P : PROP} : □ □ P ⊣⊢ □ P :=
  (affinely_congr persistently_affinely).trans (affinely_congr persistently_idem)

@[rocq_alias bi.intuitionistically_intro']
theorem intuitionistically_intro_intuitionistically [BI PROP] {P Q : PROP} (h : □ P ⊢ Q) : □ P ⊢ □ Q :=
  intuitionistically_idem.2.trans (intuitionistically_mono h)

@[rocq_alias bi.intuitionistically_into_persistently_1]
theorem persistently_of_intuitionistically [BI PROP] {P : PROP} : □ P ⊢ <pers> P :=
  affinely_elim

@[rocq_alias bi.intuitionistically_persistently_elim]
theorem intuitionistically_persistently [BI PROP] {P : PROP} : □ <pers> P ⊣⊢ □ P :=
  affinely_congr persistently_idem

theorem intuitionistically_of_intuitionistic [BI PROP] {P : PROP} [Affine P] [Persistent P] :
    □ P ⊣⊢ P :=
  ⟨intuitionistically_elim, (affine_affinely P).2.trans (affinely_mono persistent)⟩

@[rocq_alias bi.intuitionistic_intuitionistically]
theorem intuitionistic_intuitionistically_alias [BI PROP] {P : PROP} [Persistent P] [Affine P] :
    □ P ⊣⊢ P :=
  ⟨intuitionistically_elim, (affine_affinely P).mpr.trans (affinely_mono Persistent.persistent)⟩

@[rocq_alias bi.intuitionistic]
theorem intuitionistic_alias [BI PROP] {P : PROP} [Persistent P] [Affine P] : P ⊢ □ P :=
  intuitionistic_intuitionistically_alias.mpr

theorem affinely_of_intuitionistically [BI PROP] {P : PROP} : □ P ⊢ <affine> P :=
  and_intro and_elim_l intuitionistically_elim

@[rocq_alias bi.intuitionistically_affinely, rocq_alias bi.intuitionistically_affinely_elim]
theorem intuitionistically_affinely [BI PROP] {P : PROP} : □ <affine> P ⊣⊢ □ P :=
  affinely_congr persistently_affinely

@[rocq_alias bi.persistently_and_intuitionistically_sep_l]
theorem persistently_and_intuitionistically_sep_left [BI PROP] {P Q : PROP} :
    <pers> P ∧ Q ⊣⊢ □ P ∗ Q :=
  ⟨(and_mono_right emp_sep.2).trans <| persistently_and_sep_assoc.1.trans (sep_congr_left and_comm).2,
   and_intro ((sep_mono_left affinely_elim).trans persistently_absorb_l)
     ((sep_mono_left affinely_elim_emp).trans emp_sep.1)⟩

@[rocq_alias bi.persistently_and_intuitionistically_sep_r]
theorem persistently_and_intuitionistically_sep_right [BI PROP] {P Q : PROP} :
    P ∧ <pers> Q ⊣⊢ P ∗ □ Q :=
  and_comm.trans <| persistently_and_intuitionistically_sep_left.trans sep_comm

@[rocq_alias bi.and_sep_intuitionistically]
theorem and_sep_intuitionistically [BI PROP] {P Q : PROP} : □ P ∧ □ Q ⊣⊢ □ P ∗ □ Q :=
  (affinely_and_right.trans affinely_and).symm.trans persistently_and_intuitionistically_sep_left

theorem intuitionistically_and_sep [BI PROP] {P Q : PROP} : □ (P ∧ Q) ⊣⊢ □ P ∗ □ Q :=
  intuitionistically_and.trans and_sep_intuitionistically

@[rocq_alias bi.intuitionistically_sep_dup]
theorem intuitionistically_sep_idem [BI PROP] {P : PROP} : □ P ∗ □ P ⊣⊢ □ P :=
  and_sep_intuitionistically.symm.trans and_self

theorem intuitionistically_wand [BI PROP] {P Q : PROP} : (□ P -∗ Q) ⊣⊢ (<pers> P → Q) :=
  ⟨imp_intro <| persistently_and_intuitionistically_sep_right.1.trans wand_elim_left,
   wand_intro <|persistently_and_intuitionistically_sep_right.2.trans imp_elim_left⟩

theorem affinely_self_sep_intuitionistically [BI PROP] {P : PROP} :
    <affine> (P ∗ □ P) ⊣⊢ □ P :=
  ⟨affinely_mono <| (sep_mono_right persistently_of_intuitionistically).trans self_sep_persistently.1,
   and_intro affinely_elim_emp <|
   intuitionistically_sep_idem.2.trans <| sep_mono_left intuitionistically_elim⟩

@[rocq_alias bi.intuitionistically_impl_wand_2]
theorem intuitionistically_imp_wand [BI PROP] {P Q : PROP} : □ (P -∗ Q) ⊢ □ (P → Q) :=
  affinely_mono persistently_imp_wand_mpr

theorem imp_iff_exists_persistently [BI PROP] [BIAffine PROP] {P Q : PROP} :
    (P → Q) ⊣⊢ ∃ R, R ∧ <pers> (P ∧ R -∗ Q) := by
  constructor
  · refine (and_true.2.trans ?_).trans (exists_intro iprop(P → Q))
    exact and_mono_right <| persistently_emp.2.trans <| persistently_mono <|
      wand_intro <| emp_sep.1.trans imp_elim_right
  · exact exists_elim fun R => imp_intro_swap <| and_assoc.2.trans <|
      persistently_and_intuitionistically_sep_right.1.trans <|
      (sep_mono_right intuitionistically_elim).trans wand_elim_right

theorem intuitionistically_iff_persistently [BI PROP] [BIAffine PROP]
    {P : PROP} : □ P ⊣⊢ <pers> P := affine_affinely _

@[rocq_alias bi.intuitionistically_into_persistently]
theorem intuitionistically_into_persistently [BI PROP] {P : PROP} [BIAffine PROP] : □ P ⊣⊢ <pers> P :=
  ⟨affinely_elim, (affine_affinely _).mpr⟩

/-! # Conditional affinely modality -/

@[simp] theorem affinelyIf_false [BI PROP] (P : PROP) : iprop(<affine>?false P) = P := rfl
@[simp] theorem affinelyIf_true [BI PROP] (P : PROP) :
    iprop(<affine>?true P) = iprop(<affine> P) := rfl

@[rocq_alias bi.affinely_if_ne]
instance affinelyIf_ne {p : Bool} [BI PROP] : OFE.NonExpansive (affinelyIf (PROP := PROP) p) :=
  match p with
  | true => affinely_ne
  | false => OFE.id_ne
#rocq_ignore bi.affinely_if_flip_mono' "Use _mono."
#rocq_ignore bi.affinely_if_mono' "Use _mono."
#rocq_ignore bi.affinely_if_proper "Derivable from _ne with NonExpansive.eqv."

@[rw_mono_rule, rocq_alias bi.affinely_if_mono]
theorem affinelyIf_mono {p : Bool} [BI PROP] {P Q : PROP}
    (h : P ⊢ Q) : <affine>?p P ⊢ <affine>?p Q :=
  match p with
  | true => affinely_mono h
  | false => h

@[rw_mono_rule]
theorem affinelyIf_congr {p : Bool} [BI PROP] {P Q : PROP} (h : P ⊣⊢ Q) :
    <affine>?p P ⊣⊢ <affine>?p Q :=
  ⟨affinelyIf_mono h.1, affinelyIf_mono h.2⟩

@[rocq_alias bi.affinely_if_affine]
instance affinelyIf_affine (p : Bool) [BI PROP] (P : PROP) [Affine P] :
    Affine iprop(<affine>?p P) := by
  cases p <;> simp [affinelyIf] <;> infer_instance

@[rocq_alias bi.affinely_if_persistent]
instance affinelyIf_persistent (p : Bool) [BI PROP] (P : PROP) [Persistent P] :
    Persistent iprop(<affine>?p P) := by
  cases p <;> simp [affinelyIf] <;> infer_instance

@[rocq_alias bi.affinely_if_flag_mono]
theorem affinelyIf_flag_mono {p q : Bool} [BI PROP] {P : PROP} (h : q → p) :
    <affine>?p P ⊢ <affine>?q P :=
  match p, q with
  | true, true | false, false => .rfl
  | true, false => affinely_elim
  | false, true => nomatch h rfl

@[rocq_alias bi.affinely_if_elim]
theorem affinelyIf_elim {p : Bool} [BI PROP] {P : PROP} : <affine>?p P ⊢ P :=
  match p with
  | false => .rfl
  | true => affinely_elim

@[rocq_alias bi.affinely_affinely_if]
theorem affinely_affinelyIf {p : Bool} [BI PROP] {P : PROP} : <affine> P ⊢ <affine>?p P :=
  match p with
  | true => .rfl
  | false => affinely_elim

@[rocq_alias bi.affinely_if_intro']
theorem affinelyIf_intro_affinelyIf {p : Bool} [BI PROP] {P Q : PROP} :
    (P ⊢ <affine>?p Q) → <affine>?p P ⊢ <affine>?p Q :=
  match p with
  | true => affinely_intro_affinely
  | false => id

@[rocq_alias bi.affinely_if_emp]
theorem affinelyIf_emp {p : Bool} [BI PROP] : (<affine>?p emp : PROP) ⊣⊢ emp :=
  match p with
  | false => .rfl
  | true => affinely_emp

@[rocq_alias bi.affinely_if_and]
theorem affinelyIf_and {p : Bool} [BI PROP] {P Q : PROP} :
    <affine>?p (P ∧ Q) ⊣⊢ <affine>?p P ∧ <affine>?p Q :=
  match p with
  | false => .rfl
  | true => affinely_and

@[rocq_alias bi.affinely_if_or]
theorem affinelyIf_or {p : Bool} [BI PROP] {P Q : PROP} :
    <affine>?p (P ∨ Q) ⊣⊢ <affine>?p P ∨ <affine>?p Q :=
  match p with
  | false => .rfl
  | true => affinely_or

@[rocq_alias bi.affinely_if_exist]
theorem affinelyIf_exists {p : Bool} [BI PROP] {Ψ : α → PROP} :
    <affine>?p (∃ a, Ψ a) ⊣⊢ ∃ a, <affine>?p (Ψ a) :=
  match p with
  | false => .rfl
  | true => affinely_exists

theorem affinelyIf_forall {p : Bool} [BI PROP] {Ψ : α → PROP} :
    <affine>?p (∀ a, Ψ a) ⊢ ∀ a, <affine>?p (Ψ a) :=
  match p with
  | false => .rfl
  | true => affinely_forall

@[rocq_alias bi.affinely_if_sep_2]
theorem affinelyIf_sep_mpr {p : Bool} [BI PROP] {P Q : PROP} :
    <affine>?p P ∗ <affine>?p Q ⊢ <affine>?p (P ∗ Q) :=
  match p with
  | false => .rfl
  | true => affinely_sep_mpr

@[rocq_alias bi.affinely_if_sep]
theorem affinelyIf_sep {p : Bool} [BI PROP] [BIPositive PROP] {P Q : PROP} :
    <affine>?p (P ∗ Q) ⊣⊢ <affine>?p P ∗ <affine>?p Q :=
  match p with
  | false => .rfl
  | true => affinely_sep

theorem affinelyIf_idem {p : Bool} [BI PROP] [BIPositive PROP] {P : PROP} :
    <affine>?p <affine>?p P ⊣⊢ <affine>?p P :=
  match p with
  | false => .rfl
  | true => affinely_idem

@[rocq_alias bi.affinely_if_idemp]
theorem affinely_if_idem [BI PROP] {p : Bool} {P : PROP} : <affine>?p <affine>?p P ⊣⊢ <affine>?p P :=
  match p with | true => affinely_idem | false => .rfl

@[rocq_alias bi.affinely_if_and_l]
theorem affinelyIf_and_left {p : Bool} [BI PROP] {P Q : PROP} :
    <affine>?p P ∧ Q ⊣⊢ <affine>?p (P ∧ Q) :=
  match p with
  | false => .rfl
  | true => affinely_and_left

@[rocq_alias bi.affinely_if_and_r]
theorem affinelyIf_and_right {p : Bool} [BI PROP] {P Q : PROP} :
    P ∧ <affine>?p Q ⊣⊢ <affine>?p (P ∧ Q) :=
  match p with
  | false => .rfl
  | true => affinely_and_right

@[rocq_alias bi.affinely_if_and_lr]
theorem affinelyIf_and_left_right {p : Bool} [BI PROP] {P Q : PROP} :
    <affine>?p P ∧ Q ⊣⊢ P ∧ <affine>?p Q :=
  affinelyIf_and_left.trans affinelyIf_and_right.symm

/-! # Conditional absorbingly modality -/

@[simp] theorem absorbinglyIf_false [BI PROP] (P : PROP) : iprop(<absorb>?false P) = P := rfl
@[simp] theorem absorbinglyIf_true [BI PROP] (P : PROP) :
    iprop(<absorb>?true P) = iprop(<absorb> P) := rfl

@[rocq_alias bi.absorbingly_if_ne]
instance absorbinglyIf_ne {p : Bool} [BI PROP] : OFE.NonExpansive (absorbinglyIf (PROP := PROP) p) :=
  match p with
  | true => absorbingly_ne
  | false => OFE.id_ne
#rocq_ignore bi.absorbingly_if_flip_mono' "Use _mono."
#rocq_ignore bi.absorbingly_if_mono' "Use _mono."
#rocq_ignore bi.absorbingly_if_proper "Derivable from _ne with NonExpansive.eqv."

@[rw_mono_rule, rocq_alias bi.absorbingly_if_mono]
theorem absorbinglyIf_mono {p : Bool} [BI PROP] {P Q : PROP} (h : P ⊢ Q) :
    <absorb>?p P ⊢ <absorb>?p Q :=
  match p with
  | false => h
  | true => absorbingly_mono h

@[rw_mono_rule]
theorem absorbinglyIf_congr {p : Bool} [BI PROP] {P Q : PROP} (h : P ⊣⊢ Q) :
    <absorb>?p P ⊣⊢ <absorb>?p Q :=
  ⟨absorbinglyIf_mono h.1, absorbinglyIf_mono h.2⟩

@[rocq_alias bi.absorbingly_if_persistent]
instance absorbinglyIf_persistent (p : Bool) [BI PROP] (P : PROP) [Persistent P] :
    Persistent iprop(<absorb>?p P) := by
  cases p <;> simp [absorbinglyIf] <;> infer_instance

theorem absorbingly_of_absorbinglyIf {p : Bool} [BI PROP] {P : PROP} : <absorb>?p P ⊢ <absorb> P :=
  match p with
  | false => absorbingly_intro
  | true => .rfl

@[rocq_alias bi.absorbingly_if_intro]
theorem absorbinglyIf_intro {p : Bool} [BI PROP] {P : PROP} : P ⊢ <absorb>?p P :=
  match p with
  | false => .rfl
  | true => absorbingly_intro

@[rocq_alias bi.absorbingly_if_flag_mono]
theorem absorbinglyIf_flag_mono {p q : Bool} [BI PROP] {P : PROP} (h : p → q) :
    <absorb>?p P ⊢ <absorb>?q P :=
  match p, q with
  | true, true | false, false => .rfl
  | false, true => absorbingly_intro
  | true, false => nomatch h rfl

theorem absorbinglyIf_idem {p : Bool} [BI PROP] {P : PROP} :
    <absorb>?p <absorb>?p P ⊣⊢ <absorb>?p P :=
  match p with
  | false => .rfl
  | true => absorbingly_idem

@[rocq_alias bi.absorbingly_if_absorbingly]
theorem absorbingly_if_absorbingly [BI PROP] {p : Bool} {P : PROP} : <absorb>?p <absorb> P ⊣⊢ <absorb> P :=
  match p with | true => absorbingly_idem | false => .rfl

@[rocq_alias bi.absorbingly_if_idemp]
theorem absorbingly_if_idem [BI PROP] {p : Bool} {P : PROP} : <absorb>?p <absorb>?p P ⊣⊢ <absorb>?p P :=
  match p with | true => absorbingly_idem | false => .rfl

@[rocq_alias bi.absorbingly_if_pure]
theorem absorbinglyIf_pure {p : Bool} [BI PROP] {φ : Prop} : (<absorb>?p ⌜φ⌝ : PROP) ⊣⊢ ⌜φ⌝ :=
  match p with
  | false => .rfl
  | true => absorbingly_pure

@[rocq_alias bi.absorbingly_if_or]
theorem absorbinglyIf_or {p : Bool} [BI PROP] {P Q : PROP} :
    <absorb>?p (P ∨ Q) ⊣⊢ <absorb>?p P ∨ <absorb>?p Q :=
  match p with
  | false => .rfl
  | true => absorbingly_or

@[rocq_alias bi.absorbingly_if_and_1]
theorem absorbinglyIf_and {p : Bool} [BI PROP] {P Q : PROP} :
    <absorb>?p (P ∧ Q) ⊢ <absorb>?p P ∧ <absorb>?p Q :=
  match p with
  | false => .rfl
  | true => absorbingly_and

@[rocq_alias bi.absorbingly_if_forall]
theorem absorbinglyIf_forall {p : Bool} [BI PROP] {Φ : α → PROP} :
    <absorb>?p (∀ a, Φ a) ⊢ ∀ a, <absorb>?p (Φ a) :=
  match p with
  | false => .rfl
  | true => absorbingly_forall

@[rocq_alias bi.absorbingly_if_exist]
theorem absorbinglyIf_exists {p : Bool} [BI PROP] {Φ : α → PROP} :
    <absorb>?p (∃ a, Φ a) ⊣⊢ ∃ a, <absorb>?p (Φ a) :=
  match p with
  | false => .rfl
  | true => absorbingly_exists

@[rocq_alias bi.absorbingly_if_sep]
theorem absorbinglyIf_sep {p : Bool} [BI PROP] {P Q : PROP} :
    <absorb>?p (P ∗ Q) ⊣⊢ <absorb>?p P ∗ <absorb>?p Q :=
  match p with
  | false => .rfl
  | true => absorbingly_sep

@[rocq_alias bi.absorbingly_if_wand]
theorem absorbinglyIf_wand {p : Bool} [BI PROP] {P Q : PROP} :
    <absorb>?p (P -∗ Q) ⊢ (<absorb>?p P -∗ <absorb>?p Q) :=
  match p with
  | false => .rfl
  | true => absorbingly_wand

@[rocq_alias bi.absorbingly_if_sep_l]
theorem absorbinglyIf_sep_left {p : Bool} [BI PROP] {P Q : PROP} :
    <absorb>?p P ∗ Q ⊣⊢ <absorb>?p (P ∗ Q) :=
  match p with
  | false => .rfl
  | true => absorbingly_sep_left

@[rocq_alias bi.absorbingly_if_sep_r]
theorem absorbinglyIf_sep_right {p : Bool} [BI PROP] {P Q : PROP} :
    P ∗ <absorb>?p Q ⊣⊢ <absorb>?p (P ∗ Q) :=
  match p with
  | false => .rfl
  | true => absorbingly_sep_right

@[rocq_alias bi.absorbingly_if_sep_lr]
theorem absorbinglyIf_sep_left_right {p : Bool} [BI PROP] {P Q : PROP} :
    <absorb>?p P ∗ Q ⊣⊢ P ∗ <absorb>?p Q :=
  absorbinglyIf_sep_left.trans absorbinglyIf_sep_right.symm

theorem affinelyIf_absorbinglyIf {p : Bool} [BI PROP] [BIPositive PROP] {P : PROP} :
    <affine>?p <absorb>?p P ⊣⊢ <affine>?p P :=
  match p with
  | false => .rfl
  | true => affinely_absorbingly

@[rocq_alias bi.affinely_if_absorbingly_if_elim]
theorem affinely_if_absorbingly_if_elim [BI PROP] {p : Bool} {P : PROP} [BIPositive PROP] :
    <affine>?p <absorb>?p P ⊣⊢ <affine>?p P :=
  match p with | true => affinely_absorbingly_elim | false => .rfl

/-! # Conditional persistently -/

@[simp] theorem persistentlyIf_false [BI PROP] (P : PROP) : iprop(<pers>?false P) = P := rfl
@[simp] theorem persistentlyIf_true [BI PROP] (P : PROP) :
    iprop(<pers>?true P) = iprop(<pers> P) := rfl

@[rocq_alias bi.persistently_if_ne]
instance persistentlyIf_ne {p : Bool} [BI PROP] :
    OFE.NonExpansive (persistentlyIf (PROP := PROP) p) :=
  match p with
  | true => persistently_ne
  | false => OFE.id_ne
#rocq_ignore bi.persistently_if_flip_mono' "Use _mono."
#rocq_ignore bi.persistently_if_mono' "Use _mono."
#rocq_ignore bi.persistently_if_proper "Derivable from _ne with NonExpansive.eqv."

@[rw_mono_rule, rocq_alias bi.persistently_if_mono]
theorem persistentlyIf_mono {p : Bool} [BI PROP] {P Q : PROP} (h : P ⊢ Q) :
    <pers>?p P ⊢ <pers>?p Q :=
  match p with
  | false => h
  | true => persistently_mono h

@[rw_mono_rule]
theorem persistentlyIf_congr {p : Bool} [BI PROP] {P Q : PROP} (h : P ⊣⊢ Q) :
    <pers>?p P ⊣⊢ <pers>?p Q :=
  ⟨persistentlyIf_mono h.1, persistentlyIf_mono h.2⟩

@[rocq_alias bi.persistently_if_absorbing]
instance persistentlyIf_absorbing [BI PROP] (P : PROP) (p : Bool) [Absorbing P] :
    Absorbing iprop(<pers>?p P) := by
  cases p <;> simp [persistentlyIf] <;> infer_instance

@[rocq_alias bi.persistently_if_pure]
theorem persistentlyIf_pure {p : Bool} [BI PROP] {φ : Prop} : (<pers>?p ⌜φ⌝ : PROP) ⊣⊢ ⌜φ⌝ :=
  match p with
  | false => .rfl
  | true => persistently_pure

@[rocq_alias bi.persistently_if_and]
theorem persistentlyIf_and {p : Bool} [BI PROP] {P Q : PROP} :
    <pers>?p (P ∧ Q) ⊣⊢ <pers>?p P ∧ <pers>?p Q :=
  match p with
  | false => .rfl
  | true => persistently_and

@[rocq_alias bi.persistently_if_or]
theorem persistentlyIf_or {p : Bool} [BI PROP] {P Q : PROP} :
    <pers>?p (P ∨ Q) ⊣⊢ <pers>?p P ∨ <pers>?p Q :=
  match p with
  | false => .rfl
  | true => persistently_or

theorem persistentlyIf_forall {p : Bool} [BI PROP] {Φ : α → PROP} :
    <pers>?p (∀ a, Φ a) ⊢ ∀ a, <pers>?p (Φ a) :=
  match p with
  | false => .rfl
  | true => persistently_forall_mp

@[rocq_alias bi.persistently_if_exist]
theorem persistentlyIf_exists {p : Bool} [BI PROP] {Φ : α → PROP} :
    <pers>?p (∃ a, Φ a) ⊣⊢ ∃ a, <pers>?p (Φ a) :=
  match p with
  | false => .rfl
  | true => persistently_exists

@[rocq_alias bi.persistently_if_sep_2]
theorem persistentlyIf_sep_mpr {p : Bool} [BI PROP] {P Q : PROP} :
    <pers>?p P ∗ <pers>?p Q ⊢ <pers>?p (P ∗ Q) :=
  match p with
  | false => .rfl
  | true => persistently_sep_mpr

@[rocq_alias bi.persistently_if_sep]
theorem persistentlyIf_sep {p : Bool} [BI PROP] [BIPositive PROP] {P Q : PROP} :
    <pers>?p (P ∗ Q) ⊣⊢ <pers>?p P ∗ <pers>?p Q :=
  match p with
  | false => .rfl
  | true => persistently_sep

theorem persistentlyIf_idem {p : Bool} [BI PROP] [BIPositive PROP] {P : PROP} :
    <pers>?p <pers>?p P ⊣⊢ <pers>?p P :=
  match p with
  | false => .rfl
  | true => persistently_idem

@[rocq_alias bi.persistently_if_idemp]
theorem persistently_if_idem [BI PROP] {p : Bool} {P : PROP} : <pers>?p <pers>?p P ⊣⊢ <pers>?p P :=
  match p with | true => persistently_idem | false => .rfl

theorem persistentlyIf_persistently {p : Bool} [BI PROP] {P : PROP} :
    <pers>?p <pers> P ⊣⊢ <pers> P :=
  match p with
  | false => .rfl
  | true => persistently_idem

theorem persistentlyIf_intutitionistically {p : Bool} [BI PROP] {P : PROP} :
    <pers>?p □ P ⊢ <pers> P :=
  match p with
  | false => persistently_of_intuitionistically
  | true => persistently_mono intuitionistically_elim

/-! # Conditional intuitionistically -/

@[simp] theorem intuitionisticallyIf_false' [BI PROP] (P : PROP) : iprop(□?false P) = P := rfl
@[simp] theorem intuitionisticallyIf_true [BI PROP] (P : PROP) : iprop(□?true P) = iprop(□ P) := rfl

@[rocq_alias bi.intuitionistically_if_ne]
instance intuitionisticallyIf_ne {p : Bool} [BI PROP] :
    OFE.NonExpansive (intuitionisticallyIf (PROP := PROP) p) :=
  match p with
  | true => intuitionistically_ne
  | false => OFE.id_ne
#rocq_ignore bi.intuitionistically_if_flip_mono' "Use _mono."
#rocq_ignore bi.intuitionistically_if_mono' "Use _mono."
#rocq_ignore bi.intuitionistically_if_proper "Derivable from _ne with NonExpansive.eqv."

@[rw_mono_rule, rocq_alias bi.intuitionistically_if_mono]
theorem intuitionisticallyIf_mono {p : Bool} [BI PROP] {P Q : PROP} (h : P ⊢ Q) : □?p P ⊢ □?p Q :=
  match p with
  | false => h
  | true => intuitionistically_mono h

@[rw_mono_rule]
theorem intuitionisticallyIf_congr {p : Bool} [BI PROP] {P Q : PROP}
    (h : P ⊣⊢ Q) : □?p P ⊣⊢ □?p Q :=
  ⟨intuitionisticallyIf_mono h.1, intuitionisticallyIf_mono h.2⟩

instance (priority := default + 10) intuitionisticallyIf_true_affine [BI PROP] (P : PROP) :
    Affine iprop(□?true P) := inferInstanceAs (Affine iprop(□ _))

@[rocq_alias bi.intuitionistically_if_affine]
instance intuitionisticallyIf_affine (p : Bool) [BI PROP] (P : PROP) [Affine P] :
    Affine iprop(□?p P) := by
  cases p <;> simp [intuitionisticallyIf] <;> infer_instance

@[rocq_alias bi.intuitionistically_if_flag_mono]
theorem intuitionisticallyIf_flag_mono {p q : Bool} [BI PROP] {P : PROP} (h : q → p) :
    □?p P ⊢ □?q P :=
  match p, q with
  | true, true | false, false => .rfl
  | true, false => intuitionistically_elim
  | false, true => nomatch h rfl

@[rocq_alias bi.intuitionistically_if_elim]
theorem intuitionisticallyIf_elim {p : Bool} [BI PROP] {P : PROP} : □?p P ⊢ P :=
  match p with
  | false => .rfl
  | true => intuitionistically_elim

@[rocq_alias bi.intuitionistically_intuitionistically_if]
theorem intuitionisticallyIf_of_intuitionistically (p : Bool) [BI PROP] {P : PROP} : □ P ⊢ □?p P :=
  match p with
  | true => .rfl
  | false => intuitionistically_elim

@[rocq_alias bi.intuitionistically_if_intro']
theorem intuitionisticallyIf_intro_intuitionisticallyIf {p : Bool} [BI PROP] {P Q : PROP} :
    (□?p P ⊢ Q) → □?p P ⊢ □?p Q :=
  match p with
  | true => intuitionistically_intro_intuitionistically
  | false => id

@[rocq_alias bi.intuitionistically_if_emp]
theorem intuitionisticallyIf_emp {p : Bool} [BI PROP] : (□?p emp : PROP) ⊣⊢ emp :=
  match p with
  | false => .rfl
  | true => intuitionistically_emp

@[rocq_alias bi.intuitionistically_if_False]
theorem intuitionisticallyIf_false {p : Bool} [BI PROP] : (□?p False : PROP) ⊣⊢ False :=
  match p with
  | false => .rfl
  | true => intuitionistically_false

@[rocq_alias bi.intuitionistically_if_and]
theorem intuitionisticallyIf_and {p : Bool} [BI PROP] {P Q : PROP} : □?p (P ∧ Q) ⊣⊢ □?p P ∧ □?p Q :=
  match p with
  | false => .rfl
  | true => intuitionistically_and

@[rocq_alias bi.intuitionistically_if_or]
theorem intuitionisticallyIf_or (p : Bool) [BI PROP] {P Q : PROP} : □?p (P ∨ Q) ⊣⊢ □?p P ∨ □?p Q :=
  match p with
  | false => .rfl
  | true => intuitionistically_or

theorem intuitionisticallyIf_exists {p : Bool} [BI PROP] {Ψ : α → PROP} :
    (□?p ∃ a, Ψ a) ⊣⊢ ∃ a, □?p Ψ a :=
  match p with
  | false => .rfl
  | true => intuitionistically_exists

@[rocq_alias bi.intuitionistically_if_sep_2]
theorem intuitionisticallyIf_sep_mpr {p : Bool} [BI PROP] {P Q : PROP} :
    □?p P ∗ □?p Q ⊢ □?p (P ∗ Q) :=
  match p with
  | false => .rfl
  | true => intuitionistically_sep_mpr

@[rocq_alias bi.intuitionistically_if_sep]
theorem intuitionisticallyIf_sep {p : Bool} [BI PROP] [BIPositive PROP] {P Q : PROP} :
    □?p (P ∗ Q) ⊣⊢ □?p P ∗ □?p Q :=
  match p with
  | false => .rfl
  | true => intuitionistically_sep

theorem intuitionisticallyIf_sep_conj {p1 p2 : Bool} [BI PROP] {P Q : PROP} :
  (□?p1 P ∗ □?p2 Q) ⊢ □?(p1 && p2) (P ∗ Q) :=
  match p1, p2 with
  | false, false => refl
  | false, true  => sep_mono_right intuitionisticallyIf_elim
  | true,  false => sep_mono_left intuitionisticallyIf_elim
  | true,  true  => intuitionisticallyIf_sep_mpr

theorem intuitionisticallyIf_idem {p : Bool} [BI PROP] {P : PROP} : □?p □?p P ⊣⊢ □?p P :=
  match p with
  | false => .rfl
  | true => intuitionistically_idem

@[rocq_alias bi.intuitionistically_if_unfold]
theorem intuitionistically_if_unfold [BI PROP] {p : Bool} {P : PROP} : □?p P ⊣⊢ if p then □ P else P :=
  match p with | true => .rfl | false => .rfl

@[rocq_alias bi.intuitionistically_if_exist]
theorem intuitionistically_if_exists [BI PROP] {p : Bool} {Ψ : α → PROP} :
    (□?p (∃ a, Ψ a)) ⊣⊢ ∃ a, □?p (Ψ a) :=
  match p with | true => intuitionistically_exists | false => .rfl

@[rocq_alias bi.intuitionistically_if_idemp]
theorem intuitionistically_if_idem [BI PROP] {p : Bool} {P : PROP} : (□?p □?p P) ⊣⊢ □?p P :=
  match p with | true => intuitionistically_idem | false => .rfl

theorem intuitionisticallyIf_def_iff {p : Bool} [BI PROP] {P : PROP} :
    iprop(□?p P) = iprop(<affine>?p <pers>?p P) := by cases p <;> rfl

theorem intuitionisticallyIf_comm {p q : Bool} [BI PROP] {P : PROP} :
    iprop(□?p □?q P) = iprop(□?q □?p P) := by cases p <;> cases q <;> rfl

theorem intuitionisticallyIf_comm_iff {p q : Bool} [BI PROP] {P : PROP} :
    □?p □?q P ⊣⊢ □?q □?p P := .of_eq intuitionisticallyIf_comm

theorem intuitionisticallyIf_affinely {p : Bool} [BI PROP] {P : PROP} :
    □?p <affine> P ⊣⊢ <affine> □?p P :=
  match p with
  | false => .rfl
  | true =>
    ⟨(intuitionistically_mono affinely_elim).trans (and_intro affinely_elim_emp .rfl),
     affinely_elim.trans intuitionistically_affinely.2⟩

theorem intuitionisticallyIf_intutitionistically {p : Bool} [BI PROP] {P : PROP} : □?p □ P ⊣⊢ □ P :=
  match p with
  | false => .rfl
  | true => intuitionistically_idem

theorem affinelyIf_of_intuitionisticallyIf {p : Bool} [BI PROP] {P : PROP} : □?p P ⊢ <affine>?p P :=
  match p with
  | false => .rfl
  | true => affinely_of_intuitionistically

theorem persistentlyIf_of_intuitionisticallyIf {p : Bool} [BI PROP] {P : PROP} : □?p P ⊢ <pers>?p P :=
  match p with
  | false => .rfl
  | true => persistently_of_intuitionistically

/-! # Properties of persistent propositions -/

theorem persistent_congr [BI PROP] {P Q : PROP} (H : P ⊣⊢ Q) : Persistent P ↔ Persistent Q :=
  ⟨fun ⟨h⟩ => ⟨H.2.trans <| h.trans (persistently_mono H.1)⟩,
   fun ⟨h⟩ => ⟨H.1.trans <| h.trans (persistently_mono H.2)⟩⟩

theorem persistently_intro [BI PROP] {P : PROP} [Persistent P] : P ⊢ <pers> P := persistent

@[rocq_alias bi.persistent_persistently]
theorem persistently_iff [BI PROP] {P : PROP} [Persistent P] [Absorbing P] :
    <pers> P ⊣⊢ P := ⟨persistently_elim, persistent⟩

#rocq_ignore bi.persistent_persistently_2 "Use `Persistent.persistent`."

@[rocq_alias bi.persistently_intro]
theorem persistently_intro_of_persistent [BI PROP] {P : PROP} [Persistent P] (h : P ⊢ Q) : P ⊢ <pers> Q :=
  persistent.trans (persistently_mono h)

@[rocq_alias bi.persistent_and_affinely_sep_l_1]
theorem persistent_and_affinely_sep_left_mp [BI PROP] {P Q : PROP} [Persistent P] :
    P ∧ Q ⊢ <affine> P ∗ Q :=
  (and_mono_left persistent).trans <| persistently_and_intuitionistically_sep_left.1.trans <|
    sep_mono_left affinely_of_intuitionistically

@[rocq_alias bi.persistent_and_affinely_sep_r_1]
theorem persistent_and_affinely_sep_right_mp [BI PROP] {P Q : PROP} [Persistent Q] :
    P ∧ Q ⊢ P ∗ <affine> Q :=
  and_comm.1.trans <| persistent_and_affinely_sep_left_mp.trans sep_comm.1

@[rocq_alias bi.persistent_and_affinely_sep_l]
theorem persistent_and_affinely_sep_left [BI PROP] {P Q : PROP} [Persistent P] [Absorbing P] :
    P ∧ Q ⊣⊢ <affine> P ∗ Q :=
  ⟨persistent_and_affinely_sep_left_mp, (sep_mono_left <| affinely_mono persistent).trans <|
    persistently_and_intuitionistically_sep_left.2.trans <| and_mono_left persistently_elim⟩

@[rocq_alias bi.persistent_and_affinely_sep_r]
theorem persistent_and_affinely_sep_right [BI PROP] {P Q : PROP} [Persistent Q] [Absorbing Q] :
    P ∧ Q ⊣⊢ P ∗ <affine> Q :=
  and_comm.trans <| persistent_and_affinely_sep_left.trans sep_comm

@[rocq_alias bi.persistent_and_sep_1]
theorem persistent_and_sep_mp[BI PROP] {P Q : PROP} :
    [TCOr (Persistent P) (Persistent Q)] → P ∧ Q ⊢ P ∗ Q
  | TCOr.l => persistent_and_affinely_sep_left_mp.trans (sep_mono_left affinely_elim)
  | TCOr.r => persistent_and_affinely_sep_right_mp.trans (sep_mono_right affinely_elim)


@[rocq_alias bi.persistent_and_sep]
theorem persistent_and_sep [BI PROP] [BIAffine PROP] {P Q : PROP} :
    [TCOr (Persistent P) (Persistent Q)] → P ∧ Q ⊣⊢ P ∗ Q
  | TCOr.l => (and_congr_left persistently_iff.symm).trans <|
              persistently_and_iff_sep.trans (sep_congr_left persistently_iff)
  | TCOr.r => (and_congr_right persistently_iff.symm).trans <|
              and_persistently_iff_sep.trans (sep_congr_right persistently_iff)


@[rocq_alias bi.persistent_entails_l]
theorem persistent_entails_right [BI PROP] {P Q : PROP} [Persistent Q] (H : P ⊢ Q) : P ⊢ Q ∗ P :=
  (and_intro H .rfl).trans persistent_and_sep_mp

@[rocq_alias bi.persistent_entails_r]
theorem persistent_entails_left [BI PROP] {P Q : PROP} [Persistent Q] (H : P ⊢ Q) : P ⊢ P ∗ Q :=
  (and_intro .rfl H).trans persistent_and_sep_mp

@[rocq_alias bi.absorbingly_intuitionistically_into_persistently]
theorem absorbingly_intuitionistically [BI PROP] {P : PROP} : <absorb> □ P ⊣⊢ <pers> P :=
  ⟨(absorbingly_mono persistently_of_intuitionistically).trans absorbingly_persistently.1,
   and_self.2.trans <| persistently_and_intuitionistically_sep_right.1.trans <| sep_mono_left true_intro⟩

@[rocq_alias bi.persistent_absorbingly_affinely_2]
theorem absorbingly_affinely_intro_of_persistent [BI PROP] {P : PROP} [Persistent P] :
    P ⊢ <absorb> <affine> P :=
  persistent.trans <| absorbingly_intuitionistically.2.trans <|
  absorbingly_mono affinely_of_intuitionistically

@[rocq_alias bi.impl_absorbing]
instance imp_absorbing [BI PROP] (P Q : PROP) [Persistent P] [Absorbing P] [Absorbing Q] :
    Absorbing iprop(P → Q) where
  absorbing := imp_intro_swap <| persistent_and_affinely_sep_left.1.trans <| absorbingly_sep_right.1.trans <|
    (absorbingly_mono <| persistent_and_affinely_sep_left.2.trans imp_elim_right).trans absorbing

theorem bigOp_sep_nil [BI PROP] : iprop([∗] []) ⊣⊢ (emp : PROP) := .rfl

theorem bigOp_and_nil [BI PROP] : iprop([∧] []) ⊣⊢ (True : PROP) := .rfl

theorem bigOp_sep_cons [BI PROP] {P : PROP} {Ps : List PROP} :
    [∗] (P :: Ps) ⊣⊢ P ∗ [∗] Ps := bigOp_cons

theorem bigOp_and_cons [BI PROP] {P : PROP} {Ps : List PROP} :
    [∧] (P :: Ps) ⊣⊢ P ∧ [∧] Ps := bigOp_cons

/-! # Limits -/

@[rocq_alias bi.limit_preserving_entails]
theorem LimitPreserving.entails [BI PROP] [COFE A] (Φ Ψ : A → PROP) [Φne : OFE.NonExpansive Φ]
    [Ψne : OFE.NonExpansive Ψ] : LimitPreserving (λ x ↦ Φ x ⊢ Ψ x) := by
  refine .ext (P := λ x ↦ True ⊣⊢ (Φ x → Ψ x)) (@fun x => ?_) ?_
  · exact ⟨(true_and.2.trans <| imp_elim ·.1), (⟨imp_intro <| true_and.1.trans ·, true_intro⟩)⟩
  · let f : A -n> PROP := ⟨λ x ↦ iprop(True), inferInstance⟩
    let g : A -n> PROP := {
       f x := iprop(Φ x → Ψ x),
       ne.ne _ {_ _} x := imp_ne.ne (Φne.ne x) (Ψne.ne x)
    }
    refine fun c h' => ?_
    refine equiv_iff.1 ?_
    refine LimitPreserving.equiv f g _ ?_
    exact (equiv_iff.mpr <| h' ·)

@[rocq_alias bi.limit_preserving_Persistent]
instance limitPreserving_persistent [BI PROP] [COFE A] (Φ : A → PROP) [Φne : OFE.NonExpansive Φ] :
 LimitPreserving (fun x => Persistent (Φ x)) := by
  letI _ : OFE.NonExpansive fun x => iprop(<pers> Φ x) := .comp persistently_ne Φne
  refine fun c h => ⟨?_⟩
  refine LimitPreserving.entails _ (fun x => iprop(<pers> (Φ x))) _ ?_
  exact (fun n => h n |>.persistent)

instance limitPreserving_absorbing [BI PROP] [COFE A] (Φ : A → PROP) [Φne : OFE.NonExpansive Φ] :
 LimitPreserving (fun x => Absorbing (Φ x)) := by
  letI _ : OFE.NonExpansive fun x => iprop(<absorb> Φ x) := .comp absorbingly_ne Φne
  refine fun c h => ⟨?_⟩
  refine LimitPreserving.entails (fun x => iprop(<absorb> (Φ x))) _ _ ?_
  exact (fun n => h n |>.absorbing)

instance limitPreserving_affine [BI PROP] [COFE A] (Φ : A → PROP) [Φne : OFE.NonExpansive Φ] :
 LimitPreserving (fun x => Affine (Φ x)) := by
  refine fun c h => ⟨?_⟩
  refine LimitPreserving.entails (fun x => iprop((Φ x))) (fun _ => iprop(emp)) _ ?_
  exact (fun n => h n |>.affine)

@[rocq_alias bi.iter_modal_intro]
theorem iter_modal_intro [BI PROP] (M : PROP → PROP) (n : Nat) {P : PROP} (H : ∀ {Q}, Q ⊢ M Q) :
    P ⊢ n.repeat (fun x => M x) P := by
  induction n with
  | zero => simp [Nat.repeat]
  | succ _ IH => simpa only [Nat.repeat] using IH.trans H

@[rocq_alias bi.iter_modal_mono]
theorem iter_modal_mono [BI PROP] (M : PROP → PROP) (n : Nat) {P Q : PROP}
    (H : ∀ {P Q}, (P -∗ Q) ⊢ M P -∗ M Q) :
    (P -∗ Q) ⊢ n.repeat (fun x => M x) P -∗ n.repeat (fun x => M x) Q := by
  induction n with
  | zero => simp [Nat.repeat]
  | succ _ IH => simpa only [Nat.repeat] using IH.trans H

#rocq_ignore bi.equiv_entails_1_1 "Use `BiEntails.mp`."
#rocq_ignore bi.equiv_entails_1_2 "Use `BiEntails.mpr`."

@[rocq_alias bi.bi_emp_valid_mono]
theorem bi_emp_valid_mono [BI PROP] {P Q : PROP} (h : P ⊢ Q) : (⊢ P) → ⊢ Q := (·.trans h)
#rocq_ignore bi.bi_emp_valid_proper "Derivable from _ne with NonExpansive.eqv."

@[rocq_alias bi.bi_emp_valid_flip_mono]
theorem bi_emp_valid_flip_mono [BI PROP] {P Q : PROP} (h : P ⊣⊢ Q) : (⊢ P) ↔ ⊢ Q :=
  ⟨(·.trans h.1), (·.trans h.2)⟩
