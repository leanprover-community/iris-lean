/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Std.Logic
import Iris.BI.Classes
import Iris.BI.Extensions
import Iris.BI.BI
import Iris.Std.Classes
import Iris.Std.Rewrite
import Iris.Std.TC

namespace Iris.BI
open Iris.Std BI

-- Entails
instance entails_trans [BI PROP] : Trans (α := PROP) Entails Entails Entails where
  trans h1 h2 := h1.trans h2
instance entails_antisymm [BI PROP] : Antisymmetric (α := PROP) BiEntails Entails where
  antisymm h1 h2 := ⟨h1, h2⟩

instance equiv_trans [BI PROP] : Trans (α := PROP) BiEntails BiEntails BiEntails where
  trans h1 h2 := h1.trans h2

-- Logic
theorem and_elim_l' [BI PROP] {P Q R : PROP} (h : P ⊢ R) : P ∧ Q ⊢ R := and_elim_l.trans h

theorem and_elim_r' [BI PROP] {P Q R : PROP} (h : Q ⊢ R) : P ∧ Q ⊢ R := and_elim_r.trans h

theorem or_intro_l' [BI PROP] {P Q R : PROP} (h : P ⊢ Q) : P ⊢ Q ∨ R := h.trans or_intro_l

theorem or_intro_r' [BI PROP] {P Q R : PROP} (h : P ⊢ R) : P ⊢ Q ∨ R := h.trans or_intro_r

theorem and_symm [BI PROP] {P Q : PROP} : P ∧ Q ⊢ Q ∧ P :=
  and_intro and_elim_r and_elim_l

theorem imp_intro' [BI PROP] {P Q R : PROP} (h : Q ∧ P ⊢ R) : P ⊢ Q → R :=
  imp_intro <| and_symm.trans h

theorem mp [BI PROP] {P Q R : PROP} (h1 : P ⊢ Q → R) (h2 : P ⊢ Q) : P ⊢ R :=
  (and_intro .rfl h2).trans (imp_elim h1)

theorem imp_elim' [BI PROP] {P Q R : PROP} (h : Q ⊢ P → R) : P ∧ Q ⊢ R :=
  and_symm.trans <| imp_elim h

theorem imp_elim_l [BI PROP] {P Q : PROP} : (P → Q) ∧ P ⊢ Q := imp_elim .rfl

theorem imp_elim_r [BI PROP] {P Q : PROP} : P ∧ (P → Q) ⊢ Q := imp_elim' .rfl

theorem false_elim [BI PROP] {P : PROP} : False ⊢ P := pure_elim' False.elim

theorem true_intro [BI PROP] {P : PROP} : P ⊢ True := pure_intro trivial

@[rw_mono_rule]
theorem and_mono [BI PROP] {P P' Q Q' : PROP} (h1 : P ⊢ Q) (h2 : P' ⊢ Q') : P ∧ P' ⊢ Q ∧ Q' :=
  and_intro (and_elim_l' h1) (and_elim_r' h2)

theorem and_mono_l [BI PROP] {P P' Q : PROP} (h : P ⊢ P') : P ∧ Q ⊢ P' ∧ Q := and_mono h .rfl

theorem and_mono_r [BI PROP] {P Q Q' : PROP} (h : Q ⊢ Q') : P ∧ Q ⊢ P ∧ Q' := and_mono .rfl h

@[rw_mono_rule]
theorem and_congr [BI PROP] {P P' Q Q' : PROP} (h1 : P ⊣⊢ Q) (h2 : P' ⊣⊢ Q') : P ∧ P' ⊣⊢ Q ∧ Q' :=
  ⟨and_mono h1.1 h2.1, and_mono h1.2 h2.2⟩

theorem and_congr_l [BI PROP] {P P' Q : PROP} (h : P ⊣⊢ P') : P ∧ Q ⊣⊢ P' ∧ Q := and_congr h .rfl

theorem and_congr_r [BI PROP] {P Q Q' : PROP} (h : Q ⊣⊢ Q') : P ∧ Q ⊣⊢ P ∧ Q' := and_congr .rfl h

@[rw_mono_rule]
theorem or_mono [BI PROP] {P P' Q Q' : PROP} (h1 : P ⊢ Q) (h2 : P' ⊢ Q') : P ∨ P' ⊢ Q ∨ Q' :=
  or_elim (or_intro_l' h1) (or_intro_r' h2)

theorem or_mono_l [BI PROP] {P P' Q : PROP} (h : P ⊢ P') : P ∨ Q ⊢ P' ∨ Q := or_mono h .rfl

theorem or_mono_r [BI PROP] {P Q Q' : PROP} (h : Q ⊢ Q') : P ∨ Q ⊢ P ∨ Q' := or_mono .rfl h

@[rw_mono_rule]
theorem or_congr [BI PROP] {P P' Q Q' : PROP} (h1 : P ⊣⊢ Q) (h2 : P' ⊣⊢ Q') : P ∨ P' ⊣⊢ Q ∨ Q' :=
  ⟨or_mono h1.1 h2.1, or_mono h1.2 h2.2⟩

theorem or_congr_l [BI PROP] {P P' Q : PROP} (h : P ⊣⊢ P') : P ∨ Q ⊣⊢ P' ∨ Q := or_congr h .rfl

theorem or_congr_r [BI PROP] {P Q Q' : PROP} (h : Q ⊣⊢ Q') : P ∨ Q ⊣⊢ P ∨ Q' := or_congr .rfl h

@[rw_mono_rule]
theorem imp_mono [BI PROP] {P P' Q Q' : PROP} (h1 : Q ⊢ P) (h2 : P' ⊢ Q') : (P → P') ⊢ Q → Q' :=
  imp_intro <| (and_mono_r h1).trans <| (imp_elim .rfl).trans h2

theorem imp_mono_l [BI PROP] {P P' Q : PROP} (h : P' ⊢ P) : (P → Q) ⊢ (P' → Q) := imp_mono h .rfl

theorem imp_mono_r [BI PROP] {P Q Q' : PROP} (h : Q ⊢ Q') : (P → Q) ⊢ (P → Q') := imp_mono .rfl h

@[rw_mono_rule]
theorem imp_congr [BI PROP] {P P' Q Q' : PROP} (h1 : P ⊣⊢ Q) (h2 : P' ⊣⊢ Q') : (P → P') ⊣⊢ (Q → Q') :=
  ⟨imp_mono h1.2 h2.1, imp_mono h1.1 h2.2⟩

theorem imp_congr_l [BI PROP] {P P' Q : PROP} (h : P ⊣⊢ P') : (P → Q) ⊣⊢ (P' → Q) := imp_congr h .rfl

theorem imp_congr_r [BI PROP] {P Q Q' : PROP} (h : Q ⊣⊢ Q') : (P → Q) ⊣⊢ (P → Q') := imp_congr .rfl h

@[rw_mono_rule]
theorem forall_mono [BI PROP] {Φ Ψ : α → PROP} (h : ∀ a, Φ a ⊢ Ψ a) : (∀ a, Φ a) ⊢ ∀ a, Ψ a :=
  forall_intro fun a => (forall_elim a).trans (h a)

@[rw_mono_rule]
theorem forall_congr [BI PROP] {Φ Ψ : α → PROP} (h : ∀ a, Φ a ⊣⊢ Ψ a) : (∀ a, Φ a) ⊣⊢ ∀ a, Ψ a :=
  ⟨forall_mono fun a => (h a).1, forall_mono fun a => (h a).2⟩

@[rw_mono_rule]
theorem exists_mono [BI PROP] {Φ Ψ : α → PROP} (h : ∀ a, Φ a ⊢ Ψ a) : (∃ a, Φ a) ⊢ ∃ a, Ψ a :=
  exists_elim fun a => (h a).trans (exists_intro a)

@[rw_mono_rule]
theorem exists_congr [BI PROP] {Φ Ψ : α → PROP} (h : ∀ a, Φ a ⊣⊢ Ψ a) : (∃ a, Φ a) ⊣⊢ ∃ a, Ψ a :=
  ⟨exists_mono fun a => (h a).1, exists_mono fun a => (h a).2⟩

theorem and_self [BI PROP] {P : PROP} : P ∧ P ⊣⊢ P := ⟨and_elim_l, and_intro .rfl .rfl⟩
instance [BI PROP] : Idempotent (α := PROP) BiEntails and := ⟨and_self⟩

theorem or_self [BI PROP] {P : PROP} : P ∨ P ⊣⊢ P := ⟨or_elim .rfl .rfl, or_intro_l⟩
instance [BI PROP] : Idempotent (α := PROP) BiEntails or := ⟨or_self⟩

theorem and_comm [BI PROP] {P : PROP} : P ∧ Q ⊣⊢ Q ∧ P := ⟨and_symm, and_symm⟩
instance [BI PROP] : Commutative (α := PROP) BiEntails and := ⟨and_comm⟩

theorem true_and [BI PROP] {P : PROP} : True ∧ P ⊣⊢ P :=
  ⟨and_elim_r, and_intro (pure_intro trivial) .rfl⟩
instance [BI PROP] : LeftId (α := PROP) BiEntails iprop(True) and := ⟨true_and⟩

theorem and_true [BI PROP] {P : PROP} : P ∧ True ⊣⊢ P := and_comm.trans true_and
instance [BI PROP] : RightId (α := PROP) BiEntails iprop(True) and := ⟨and_true⟩

theorem and_assoc [BI PROP] {P Q R : PROP} : (P ∧ Q) ∧ R ⊣⊢ P ∧ Q ∧ R :=
  ⟨and_intro (and_elim_l' and_elim_l) (and_mono_l and_elim_r),
   and_intro (and_mono_r and_elim_l) (and_elim_r' and_elim_r)⟩

instance [BI PROP] : LawfulBigOp and (iprop(True) : PROP) BiEntails where
  refl := .rfl
  symm h := h.symm
  trans h1 h2 := h1.trans h2
  comm := and_comm
  assoc := and_assoc
  left_id := true_and
  congr_l := and_congr_l

theorem and_left_comm [BI PROP] {P Q R : PROP} : P ∧ Q ∧ R ⊣⊢ Q ∧ P ∧ R :=
  and_assoc.symm.trans <| (and_congr_l and_comm).trans and_assoc

instance [BI PROP] : Associative (α := PROP) BiEntails and := ⟨and_assoc⟩

theorem and_or_l [BI PROP] {P Q R : PROP} : P ∧ (Q ∨ R) ⊣⊢ P ∧ Q ∨ P ∧ R :=
  ⟨imp_elim' <| or_elim (imp_intro' or_intro_l) (imp_intro' or_intro_r),
   and_intro (or_elim and_elim_l and_elim_l)
    (or_elim (or_intro_l' and_elim_r) (or_intro_r' and_elim_r))⟩

theorem and_exists_l [BI PROP] {P : PROP} {Ψ : α → PROP} : P ∧ (∃ a, Ψ a) ⊣⊢ ∃ a, P ∧ Ψ a :=
  ⟨imp_elim' <| exists_elim fun _ =>
    imp_intro' (exists_intro (Ψ := fun a => iprop(P ∧ Ψ a)) _),
   exists_elim fun _ => and_mono_r (exists_intro _)⟩

theorem or_eq_ite [BI PROP] {P Q : PROP} : P ∨ Q ⊣⊢ ∃ (b : Bool), if b then P else Q := by
  constructor
  · apply or_elim
    · exact exists_intro (Ψ := fun b => if b = true then P else Q) true
    · exact exists_intro (Ψ := fun b => if b = true then P else Q) false
  · exact exists_elim fun | true => or_intro_l | false => or_intro_r

theorem exists_intro' [BI PROP] {Ψ : α → PROP} (a : α) (h : P ⊢ Ψ a) : P ⊢ ∃ a, Ψ a :=
  h.trans (exists_intro a)

-- BI
theorem sep_mono_l [BI PROP] {P P' Q : PROP} (h : P ⊢ P') : P ∗ Q ⊢ P' ∗ Q := sep_mono h .rfl

theorem sep_mono_r [BI PROP] {P Q Q' : PROP} (h : Q ⊢ Q') : P ∗ Q ⊢ P ∗ Q' := sep_mono .rfl h

@[rw_mono_rule]
theorem sep_congr [BI PROP] {P P' Q Q' : PROP} (h1 : P ⊣⊢ Q) (h2 : P' ⊣⊢ Q') :
    (P ∗ P') ⊣⊢ (Q ∗ Q') := ⟨sep_mono h1.1 h2.1, sep_mono h1.2 h2.2⟩

theorem sep_congr_l [BI PROP] {P P' Q : PROP} (h : P ⊣⊢ P') : P ∗ Q ⊣⊢ P' ∗ Q := sep_congr h .rfl

theorem sep_congr_r [BI PROP] {P Q Q' : PROP} (h : Q ⊣⊢ Q') : P ∗ Q ⊣⊢ P ∗ Q' := sep_congr .rfl h

@[rw_mono_rule]
theorem wand_mono [BI PROP] {P P' Q Q' : PROP} (h1 : Q ⊢ P) (h2 : P' ⊢ Q') :
    (P -∗ P') ⊢ Q -∗ Q' := wand_intro <| (sep_mono_r h1).trans <| (wand_elim .rfl).trans h2

theorem wand_mono_l [BI PROP] {P P' Q : PROP} (h : P' ⊢ P) : (P -∗ Q) ⊢ P' -∗ Q := wand_mono h .rfl

theorem wand_mono_r [BI PROP] {P Q Q' : PROP} (h : Q ⊢ Q') : (P -∗ Q) ⊢ P -∗ Q' := wand_mono .rfl h

@[rw_mono_rule]
theorem wand_congr [BI PROP] {P P' Q Q' : PROP} (h1 : P ⊣⊢ Q) (h2 : P' ⊣⊢ Q') :
    (P -∗ P') ⊣⊢ (Q -∗ Q') := ⟨wand_mono h1.2 h2.1, wand_mono h1.1 h2.2⟩

theorem wand_congr_l [BI PROP] {P P' Q : PROP} (h : P ⊣⊢ P') : (P -∗ Q) ⊣⊢ (P' -∗ Q) := wand_congr h .rfl

theorem wand_congr_r [BI PROP] {P Q Q' : PROP} (h : Q ⊣⊢ Q') : (P -∗ Q) ⊣⊢ (P -∗ Q') := wand_congr .rfl h

theorem sep_comm [BI PROP] {P Q : PROP} : P ∗ Q ⊣⊢ Q ∗ P := ⟨sep_symm, sep_symm⟩
instance [BI PROP] : Commutative (α := PROP) BiEntails sep := ⟨sep_comm⟩

theorem sep_assoc [BI PROP] {P Q R : PROP} : (P ∗ Q) ∗ R ⊣⊢ P ∗ Q ∗ R :=
  ⟨sep_assoc_l, (sep_comm.trans <| sep_congr_l sep_comm).1.trans <|
    sep_assoc_l.trans (sep_comm.trans <| sep_congr_r sep_comm).2⟩
instance [BI PROP] : Associative (α := PROP) BiEntails sep := ⟨sep_assoc⟩

theorem sep_left_comm [BI PROP] {P Q R : PROP} : P ∗ Q ∗ R ⊣⊢ Q ∗ P ∗ R :=
  sep_assoc.symm.trans <| (sep_congr_l sep_comm).trans sep_assoc

theorem sep_right_comm [BI PROP] {P Q R : PROP} : (P ∗ Q) ∗ R ⊣⊢ (P ∗ R) ∗ Q :=
  sep_assoc.trans <| (sep_congr_r sep_comm).trans sep_assoc.symm

theorem emp_sep [BI PROP] {P : PROP} : emp ∗ P ⊣⊢ P := ⟨emp_sep_1, emp_sep_2⟩
instance [BI PROP] : LeftId (α := PROP) BiEntails emp sep := ⟨emp_sep⟩

theorem sep_emp [BI PROP] {P : PROP} : P ∗ emp ⊣⊢ P := sep_comm.trans emp_sep
instance [BI PROP] : RightId (α := PROP) BiEntails emp sep := ⟨sep_emp⟩

instance [BI PROP] : LawfulBigOp sep (emp : PROP) BiEntails where
  refl := .rfl
  symm h := h.symm
  trans h1 h2 := h1.trans h2
  comm := sep_comm
  assoc := sep_assoc
  left_id := emp_sep
  congr_l := sep_congr_l

theorem true_sep_2 [BI PROP] {P : PROP} : P ⊢ True ∗ P := emp_sep_2.trans (sep_mono_l true_intro)

theorem wand_intro' [BI PROP] {P Q R : PROP} (h : Q ∗ P ⊢ R) : P ⊢ Q -∗ R :=
  wand_intro <| sep_symm.trans h

theorem wand_elim' [BI PROP] {P Q R : PROP} (h : Q ⊢ P -∗ R) : P ∗ Q ⊢ R :=
  sep_symm.trans (wand_elim h)

theorem wand_elim_l [BI PROP] {P Q : PROP} : (P -∗ Q) ∗ P ⊢ Q := wand_elim .rfl

theorem wand_elim_r [BI PROP] {P Q : PROP} : P ∗ (P -∗ Q) ⊢ Q := wand_elim' .rfl

theorem sep_or_l [BI PROP] {P Q R : PROP} : P ∗ (Q ∨ R) ⊣⊢ (P ∗ Q) ∨ (P ∗ R) :=
  ⟨wand_elim' <| or_elim (wand_intro' or_intro_l) (wand_intro' or_intro_r),
   or_elim (sep_mono_r or_intro_l) (sep_mono_r or_intro_r)⟩

theorem sep_or_r [BI PROP] {P Q R : PROP} : (P ∨ Q) ∗ R ⊣⊢ (P ∗ R) ∨ (Q ∗ R) :=
  sep_comm.trans <| sep_or_l.trans (or_congr sep_comm sep_comm)

theorem sep_exists_l [BI PROP] {P : PROP} {Ψ : α → PROP} : P ∗ (∃ a, Ψ a) ⊣⊢ ∃ a, P ∗ Ψ a :=
  ⟨wand_elim' <| exists_elim fun _ =>
    wand_intro' (exists_intro (Ψ := fun a => iprop(P ∗ Ψ a)) _),
   exists_elim fun _ => sep_mono_r (exists_intro _)⟩

theorem sep_exists_r [BI PROP] {Φ : α → PROP} {Q : PROP} : (∃ a, Φ a) ∗ Q ⊣⊢ ∃ a, Φ a ∗ Q :=
  sep_comm.trans <| sep_exists_l.trans <| exists_congr fun _ => sep_comm

theorem wand_rfl [BI PROP] {P : PROP} : ⊢ P -∗ P := wand_intro emp_sep_1

@[rw_mono_rule]
theorem wandIff_congr [BI PROP] {P P' Q Q' : PROP} (h1 : P ⊣⊢ Q) (h2 : P' ⊣⊢ Q') :
    (P ∗-∗ P') ⊣⊢ (Q ∗-∗ Q') := and_congr (wand_congr h1 h2) (wand_congr h2 h1)

theorem wandIff_congr_l [BI PROP] {P P' Q : PROP} (h : P ⊣⊢ P') : (P ∗-∗ Q) ⊣⊢ (P' ∗-∗ Q) := wandIff_congr h .rfl

theorem wandIff_congr_r [BI PROP] {P Q Q' : PROP} (h : Q ⊣⊢ Q') : (P ∗-∗ Q) ⊣⊢ (P ∗-∗ Q') := wandIff_congr .rfl h

theorem wandIff_refl [BI PROP] {P : PROP} : ⊢ P ∗-∗ P := and_intro wand_rfl wand_rfl

theorem wand_entails [BI PROP] {P Q : PROP} (h : ⊢ P -∗ Q) : P ⊢ Q :=
  emp_sep_2.trans (wand_elim h)

theorem entails_wand [BI PROP] {P Q : PROP} (h : P ⊢ Q) : ⊢ P -∗ Q :=
  wand_intro (emp_sep_1.trans h)

theorem equiv_wandIff [BI PROP] {P Q : PROP} (h : P ⊣⊢ Q) : ⊢ P ∗-∗ Q :=
  wandIff_refl.trans (wandIff_congr_l h).2

theorem wandIff_equiv [BI PROP] {P Q : PROP} (h : ⊢ P ∗-∗ Q) : P ⊣⊢ Q :=
  ⟨wand_entails (h.trans and_elim_l), wand_entails (h.trans and_elim_r)⟩

-- Pure
theorem pure_elim [BI PROP] (φ : Prop) {Q R : PROP} (h1 : Q ⊢ ⌜φ⌝) (h2 : φ → Q ⊢ R) : Q ⊢ R :=
  (and_self (PROP := PROP)).2.trans <| imp_elim <| h1.trans <| pure_elim' fun h =>
    imp_intro' <| and_elim_l.trans (h2 h)

theorem pure_mono [BI PROP] {φ1 φ2 : Prop} (h : φ1 → φ2) : ⌜φ1⌝ ⊢ (⌜φ2⌝ : PROP) :=
  pure_elim' <| pure_intro ∘ h

theorem pure_congr [BI PROP] {φ1 φ2 : Prop} (h : φ1 ↔ φ2) : ⌜φ1⌝ ⊣⊢ (⌜φ2⌝ : PROP) :=
  ⟨pure_mono h.1,pure_mono h.2⟩

theorem pure_elim_l [BI PROP] {φ : Prop} {Q R : PROP} (h : φ → Q ⊢ R) : ⌜φ⌝ ∧ Q ⊢ R :=
  pure_elim _ and_elim_l <| and_elim_r' ∘ h

theorem pure_elim_r [BI PROP] {φ : Prop} {Q R : PROP} (h : φ → Q ⊢ R) : Q ∧ ⌜φ⌝ ⊢ R :=
  and_comm.1.trans (pure_elim_l h)

theorem pure_true [BI PROP] {φ : Prop} (h : φ) : ⌜φ⌝ ⊣⊢ (True : PROP) := eq_true h ▸ .rfl

theorem pure_and [BI PROP] {φ1 φ2 : Prop} : ⌜φ1⌝ ∧ (⌜φ2⌝ : PROP) ⊣⊢ ⌜φ1 ∧ φ2⌝ :=
  ⟨pure_elim φ1 and_elim_l fun h => and_elim_r' <| pure_mono <| And.intro h,
   and_intro (pure_mono And.left) (pure_mono And.right)⟩

theorem pure_or [BI PROP] {φ1 φ2 : Prop} : ⌜φ1⌝ ∨ (⌜φ2⌝ : PROP) ⊣⊢ ⌜φ1 ∨ φ2⌝ :=
  ⟨or_elim (pure_mono Or.inl) (pure_mono Or.inr),
   pure_elim' (·.elim (or_intro_l' ∘ pure_intro) (or_intro_r' ∘ pure_intro))⟩

theorem pure_imp_2 [BI PROP] {φ1 φ2 : Prop} : ⌜φ1 → φ2⌝ ⊢ (⌜φ1⌝ → ⌜φ2⌝ : PROP) :=
  imp_intro <| pure_and.1.trans <| pure_mono (And.elim id)

theorem pure_imp [BI PROP] {φ1 φ2 : Prop} : (⌜φ1⌝ → ⌜φ2⌝ : PROP) ⊣⊢ ⌜φ1 → φ2⌝ := by
  refine ⟨?_, pure_imp_2⟩
  by_cases h : φ1 -- TODO: does this really require classical logic?
  · exact (mp .rfl (pure_intro h)).trans (pure_mono fun h _ => h)
  · exact pure_intro h.elim

theorem pure_forall_2 [BI PROP] {φ : α → Prop} : ⌜∀ x, φ x⌝ ⊢ ∀ x, (⌜φ x⌝ : PROP) :=
  forall_intro fun _ => pure_mono (· _)

theorem pure_forall [BI PROP] {φ : α → Prop} : (∀ x, (⌜φ x⌝ : PROP)) ⊣⊢ ⌜∀ x, φ x⌝ := by
  refine ⟨?_, pure_forall_2⟩
  by_cases h : ∃ x, ¬φ x
  · let ⟨x, h⟩ := h
    exact (forall_elim x).trans (pure_mono h.elim)
  · exact pure_intro fun x => Classical.not_not.1 <| mt (⟨x, ·⟩) h

theorem pure_exists [BI PROP] {φ : α → Prop} : (∃ x, ⌜φ x⌝ : PROP) ⊣⊢ ⌜∃ x, φ x⌝ :=
  ⟨exists_elim fun a => pure_mono (⟨a, ·⟩),
   pure_elim' fun ⟨x, h⟩ => (pure_intro h).trans (exists_intro' x .rfl)⟩

-- Affine
@[rw_mono_rule]
theorem affinely_congr [BI PROP] {P P' : PROP} (h : P ⊣⊢ P') :
    <affine> P ⊣⊢ <affine> P' := and_congr_r h

theorem affinely_elim_emp [BI PROP] {P : PROP} : <affine> P ⊢ emp := and_elim_l

theorem affinely_elim [BI PROP] {P : PROP} : <affine> P ⊢ P := and_elim_r

@[rw_mono_rule]
theorem affinely_mono [BI PROP] {P Q : PROP} : (P ⊢ Q) → <affine> P ⊢ <affine> Q := and_mono_r

theorem affinely_idem [BI PROP] {P : PROP} : <affine> <affine> P ⊣⊢ <affine> P :=
  and_assoc.symm.trans (and_congr_l and_self)

theorem affinely_emp [BI PROP] : <affine> emp ⊣⊢ (emp : PROP) := and_self

theorem affinely_or [BI PROP] {P Q : PROP} : <affine> (P ∨ Q) ⊣⊢ <affine> P ∨ <affine> Q := and_or_l

theorem affinely_and [BI PROP] {P Q : PROP} : <affine> (P ∧ Q) ⊣⊢ <affine> P ∧ <affine> Q :=
  (and_congr_l and_self.symm).trans <| and_assoc.trans <|
    (and_congr_r and_left_comm).trans and_assoc.symm

theorem affinely_sep_2 [BI PROP] {P Q : PROP} : <affine> P ∗ <affine> Q ⊢ <affine> (P ∗ Q) :=
  and_intro
    (sep_mono affinely_elim_emp affinely_elim_emp |>.trans sep_emp.1)
    (sep_mono affinely_elim affinely_elim)

theorem affinely_forall [BI PROP] {Φ : α → PROP} : <affine> (∀ a, Φ a) ⊢ ∀ a, <affine> (Φ a) :=
  forall_intro fun a => affinely_mono (forall_elim a)

theorem affinely_exists [BI PROP] {Φ : α → PROP} : <affine> (∃ a, Φ a) ⊣⊢ ∃ a, <affine> (Φ a) :=
  and_exists_l

theorem affinely_true [BI PROP] : <affine> True ⊣⊢ (emp : PROP) :=
  ⟨and_elim_l, and_intro .rfl true_intro⟩

theorem affinely_and_l [BI PROP] {P Q : PROP} : <affine> P ∧ Q ⊣⊢ <affine> (P ∧ Q) := and_assoc

theorem affinely_and_r [BI PROP] {P Q : PROP} : P ∧ <affine> Q ⊣⊢ <affine> (P ∧ Q) := and_left_comm

theorem affinely_and_lr [BI PROP] {P Q : PROP} : <affine> P ∧ Q ⊣⊢ P ∧ <affine> Q :=
  affinely_and_l.trans affinely_and_r.symm

-- Absorbing
@[rw_mono_rule]
theorem absorbingly_congr [BI PROP] {P P' : PROP} (h : P ⊣⊢ P') :
    <absorb> P ⊣⊢ <absorb> P' := sep_congr_r h

theorem absorbingly_intro [BI PROP] {P : PROP} : P ⊢ <absorb> P := true_sep_2

@[rw_mono_rule]
theorem absorbingly_mono [BI PROP] {P Q : PROP} : (P ⊢ Q) → <absorb> P ⊢ <absorb> Q := sep_mono_r

theorem absorbingly_idem [BI PROP] {P : PROP} : <absorb> <absorb> P ⊣⊢ <absorb> P :=
  ⟨sep_assoc.2.trans (sep_mono_l true_intro), absorbingly_intro⟩

theorem absorbingly_pure {φ : Prop} [BI PROP] : <absorb> ⌜φ⌝ ⊣⊢ (⌜φ⌝ : PROP) :=
  ⟨wand_elim' <| pure_elim' fun h => wand_intro' <| pure_intro h, absorbingly_intro⟩

instance pureAbsorbing (φ : Prop) [BI PROP] : Absorbing (PROP := PROP) iprop(⌜φ⌝) where
  absorbing := absorbingly_pure.1

theorem absorbingly_or [BI PROP] {P Q : PROP} : <absorb> (P ∨ Q) ⊣⊢ <absorb> P ∨ <absorb> Q :=
  sep_or_l

theorem absorbingly_and_1 [BI PROP] {P Q : PROP} : <absorb> (P ∧ Q) ⊢ <absorb> P ∧ <absorb> Q :=
  and_intro (absorbingly_mono and_elim_l) (absorbingly_mono and_elim_r)

theorem absorbingly_forall [BI PROP] {Φ : α → PROP} : <absorb> (∀ a, Φ a) ⊢ ∀ a, <absorb> (Φ a) :=
  forall_intro fun a => absorbingly_mono (forall_elim a)

theorem absorbingly_exists [BI PROP] {Φ : α → PROP} :
    <absorb> (∃ a, Φ a) ⊣⊢ ∃ a, <absorb> (Φ a) := by
  simp [absorbingly, sep_exists_l]

theorem absorbingly_sep [BI PROP] {P Q : PROP} : <absorb> (P ∗ Q) ⊣⊢ <absorb> P ∗ <absorb> Q :=
  absorbingly_idem.symm.trans <| (sep_congr_r sep_left_comm).trans sep_assoc.symm

theorem absorbingly_emp [BI PROP] : <absorb> (emp : PROP) ⊣⊢ True := sep_emp

theorem absorbingly_wand [BI PROP] {P Q : PROP} : <absorb> (P -∗ Q) ⊢ <absorb> P -∗ <absorb> Q :=
  wand_intro' <| absorbingly_sep.2.trans <| absorbingly_mono wand_elim_r

theorem absorbingly_sep_l [BI PROP] {P Q : PROP} : <absorb> P ∗ Q ⊣⊢ <absorb> (P ∗ Q) := sep_assoc

theorem absorbingly_sep_r [BI PROP] {P Q : PROP} : P ∗ <absorb> Q ⊣⊢ <absorb> (P ∗ Q) :=
  sep_left_comm

theorem absorbingly_sep_lr [BI PROP] {P Q : PROP} : <absorb> P ∗ Q ⊣⊢ P ∗ <absorb> Q :=
  absorbingly_sep_l.trans absorbingly_sep_r.symm

-- Affine / Absorbing Propositions
theorem affine_affinely [BI PROP] (P : PROP) [Affine P] : <affine> P ⊣⊢ P :=
  ⟨affinely_elim, and_intro affine .rfl⟩

theorem absorbing_absorbingly [BI PROP] {P : PROP} [Absorbing P] : <absorb> P ⊣⊢ P :=
  ⟨absorbing, absorbingly_intro⟩

theorem sep_elim_l [BI PROP] {P Q : PROP} : [TCOr (Affine Q) (Absorbing P)] → P ∗ Q ⊢ P
  | TCOr.l => (sep_mono_r affine).trans sep_emp.1
  | TCOr.r => (sep_mono_r true_intro).trans <| sep_comm.1.trans absorbing

theorem sep_elim_r [BI PROP] {P Q : PROP} [TCOr (Affine P) (Absorbing Q)] : P ∗ Q ⊢ Q :=
  sep_comm.1.trans sep_elim_l

theorem sep_and [BI PROP] {P Q : PROP}
    [TCOr (Affine P) (Absorbing Q)] [TCOr (Affine Q) (Absorbing P)] : P ∗ Q ⊢ P ∧ Q :=
  and_intro sep_elim_l sep_elim_r

theorem pure_sep [BI PROP] {φ1 φ2 : Prop} : ⌜φ1⌝ ∗ (⌜φ2⌝ : PROP) ⊣⊢ ⌜φ1 ∧ φ2⌝ :=
  ⟨sep_and.trans pure_and.1, pure_elim' fun ⟨a, b⟩ => by
    rw [eq_true a, eq_true b]; exact true_sep_2⟩

theorem pure_wand_2 [BI PROP] {φ1 φ2 : Prop} : ⌜φ1 → φ2⌝ ⊢ (⌜φ1⌝ -∗ (⌜φ2⌝ : PROP)) :=
  pure_elim' fun a => wand_intro <| absorbing.trans (pure_mono a)

theorem pure_wand [BI PROP] {φ1 φ2 : Prop} : (⌜φ1⌝ -∗ (⌜φ2⌝ : PROP)) ⊣⊢ ⌜φ1 → φ2⌝ := by
  refine ⟨(imp_intro' ?_).trans pure_imp.1, pure_wand_2⟩
  exact pure_elim_l fun h => true_sep_2.trans (eq_true h ▸ wand_elim_r)

-- Persistent
@[rw_mono_rule]
theorem persistently_congr [BI PROP] {P P' : PROP} (h : P ⊣⊢ P') :
    <pers> P ⊣⊢ <pers> P' := ⟨persistently_mono h.1, persistently_mono h.2⟩

theorem persistently_absorb_r [BI PROP] {P Q : PROP} : P ∗ <pers> Q ⊢ <pers> Q :=
  sep_comm.1.trans persistently_absorb_l

theorem absorbingly_persistently [BI PROP] {P : PROP} : <absorb> <pers> P ⊣⊢ <pers> P :=
  ⟨persistently_absorb_r, absorbingly_intro⟩

theorem persistently_forall_1 [BI PROP] {Ψ : α → PROP} : <pers> (∀ a, Ψ a) ⊢ ∀ a, <pers> (Ψ a) :=
  forall_intro fun x => persistently_mono (forall_elim x)

theorem persistently_exists [BI PROP] {Ψ : α → PROP} : <pers> (∃ a, Ψ a) ⊣⊢ ∃ a, <pers> (Ψ a) :=
  ⟨persistently_exists_1, exists_elim fun a => persistently_mono (exists_intro a)⟩

theorem persistently_and [BI PROP] {P Q : PROP} : <pers> (P ∧ Q) ⊣⊢ <pers> P ∧ <pers> Q :=
  ⟨and_intro (persistently_mono and_elim_l) (persistently_mono and_elim_r), persistently_and_2⟩

theorem persistently_ite {p : Bool} [BI PROP] {P Q : PROP} :
    iprop(<pers> if p then P else Q) = iprop(if p then <pers> P else <pers> Q) := by
  cases p <;> simp

theorem persistently_or [BI PROP] {P Q : PROP} : <pers> (P ∨ Q) ⊣⊢ <pers> P ∨ <pers> Q :=
  (persistently_congr or_eq_ite).trans <| persistently_exists.trans <|
    (or_eq_ite.trans <| exists_congr fun _ => persistently_ite (PROP := PROP) ▸ .rfl).symm

theorem persistently_emp_intro [BI PROP] {P : PROP} : P ⊢ <pers> emp :=
  emp_sep.2.trans <| (sep_mono_l persistently_emp_2).trans (persistently_absorb_l (Q := P))

theorem persistently_emp [BI PROP] : <pers> (emp : PROP) ⊣⊢ True :=
  ⟨true_intro, persistently_emp_intro⟩

theorem persistently_true [BI PROP] : <pers> (True : PROP) ⊣⊢ True :=
  ⟨true_intro, persistently_emp.2.trans <| persistently_mono true_intro⟩

theorem persistently_affinely [BI PROP] {P : PROP} : <pers> <affine> P ⊣⊢ <pers> P :=
  ⟨persistently_mono affinely_elim,
   (and_intro persistently_emp_intro .rfl).trans persistently_and.2⟩

theorem persistently_and_affinely_sep [BI PROP] {P Q : PROP} : <pers> P ∧ Q ⊢ <affine> P ∗ Q :=
  (and_mono_l persistently_affinely.2).trans persistently_and_l

theorem persistently_and_sep_assoc [BI PROP] {P Q R : PROP} :
    <pers> P ∧ (Q ∗ R) ⊣⊢ (<pers> P ∧ Q) ∗ R := by
  constructor
  · refine (and_mono_l persistently_idem_2).trans <| persistently_and_affinely_sep.trans <|
      sep_assoc.2.trans <| sep_mono_l <| and_intro ?_ ?_
    · exact (sep_mono_l and_elim_r).trans persistently_absorb_l
    · exact (sep_mono_l and_elim_l).trans emp_sep.1
  · exact and_intro ((sep_mono_l and_elim_l).trans persistently_absorb_l) (sep_mono_l and_elim_r)

theorem intuitionistically_elim [BI PROP] {P : PROP} : □ P ⊢ P :=
  and_comm.2.trans <| persistently_and_affinely_sep.trans <| sep_emp.1.trans affinely_elim

theorem absorbingly_of_persistently [BI PROP] {P : PROP} : <pers> P ⊢ <absorb> P :=
  and_true.2.trans <| (and_mono_r emp_sep.2).trans <| persistently_and_sep_assoc.1.trans <|
    (sep_mono_l <| and_comm.1.trans intuitionistically_elim).trans sep_comm.1

theorem persistently_elim [BI PROP] {P : PROP} [Absorbing P] : <pers> P ⊢ P :=
  absorbingly_of_persistently.trans absorbing

theorem persistently_idem [BI PROP] {P : PROP} : <pers> <pers> P ⊣⊢ <pers> P :=
  ⟨absorbingly_of_persistently.trans absorbingly_persistently.1, persistently_idem_2⟩

theorem persistently_pure {φ : Prop} [BI PROP] : <pers> ⌜φ⌝ ⊣⊢ (⌜φ⌝ : PROP) :=
  ⟨absorbingly_of_persistently.trans absorbingly_pure.1,
   pure_elim' fun h => persistently_true.2.trans <| persistently_mono <| pure_intro h⟩

theorem persistently_and_imp_sep [BI PROP] {P Q : PROP} : <pers> P ∧ Q ⊢ <pers> P ∗ Q :=
  (and_mono_r emp_sep.2).trans <| persistently_and_sep_assoc.1.trans <| sep_mono_l and_elim_l

theorem persistently_and_sep [BI PROP] {P Q : PROP} : <pers> (P ∧ Q) ⊢ <pers> (P ∗ Q) :=
  persistently_and.1.trans <| (and_mono_l persistently_idem.2).trans <|
  persistently_and.2.trans <| persistently_mono <|
  (and_mono_r emp_sep.2).trans <| persistently_and_sep_assoc.1.trans <|
  sep_mono_l <| and_comm.1.trans intuitionistically_elim

theorem persistently_and_persistently_sep [BI PROP] {P Q : PROP} :
    <pers> P ∧ <pers> Q ⊣⊢ <pers> P ∗ <pers> Q :=
  ⟨persistently_and_imp_sep, and_intro persistently_absorb_l persistently_absorb_r⟩

theorem persistently_sep_2 [BI PROP] {P Q : PROP} : <pers> P ∗ <pers> Q ⊢ <pers> (P ∗ Q) :=
  (persistently_and.trans persistently_and_persistently_sep).2.trans persistently_and_sep

-- Intuitionistic
theorem intuitionistically_emp [BI PROP] : □ emp ⊣⊢ (emp : PROP) :=
  (affinely_congr persistently_emp).trans affinely_true

theorem intuitionistically_true [BI PROP] : □ True ⊣⊢ (emp : PROP) :=
  (affinely_congr persistently_true).trans affinely_true

theorem intuitionistically_and [BI PROP] {P Q : PROP} : □ (P ∧ Q) ⊣⊢ □ P ∧ □ Q :=
  (affinely_congr persistently_and).trans affinely_and

theorem intuitionistically_forall [BI PROP] {Φ : α → PROP} : □ (∀ x, Φ x) ⊢ ∀ x, □ Φ x :=
  (affinely_mono persistently_forall_1).trans affinely_forall

theorem intuitionistically_or [BI PROP] {P Q : PROP} : □ (P ∨ Q) ⊣⊢ □ P ∨ □ Q :=
  (affinely_congr persistently_or).trans affinely_or

theorem intuitionistically_exists [BI PROP] {Φ : α → PROP} : □ (∃ x, Φ x) ⊣⊢ ∃ x, □ Φ x :=
  (affinely_congr persistently_exists).trans affinely_exists

theorem intuitionistically_sep_2 [BI PROP] {P Q : PROP} : □ P ∗ □ Q ⊢ □ (P ∗ Q) :=
  affinely_sep_2.trans (affinely_mono persistently_sep_2)

@[rw_mono_rule]
theorem intuitionistically_mono [BI PROP] {P Q : PROP} (h : P ⊢ Q) : □ P ⊢ □ Q :=
  affinely_mono <| persistently_mono h

@[rw_mono_rule]
theorem intuitionistically_congr [BI PROP] {P Q : PROP} (h : P ⊣⊢ Q) : □ P ⊣⊢ □ Q :=
  affinely_congr <| persistently_congr h

theorem intuitionistically_idem [BI PROP] {P : PROP} : □ □ P ⊣⊢ □ P :=
  (affinely_congr persistently_affinely).trans (affinely_congr persistently_idem)

theorem persistently_of_intuitionistically [BI PROP] {P : PROP} : □ P ⊢ <pers> P :=
  affinely_elim

theorem intuitionistically_persistently [BI PROP] {P : PROP} : □ <pers> P ⊣⊢ □ P :=
  affinely_congr persistently_idem

theorem intuitionistically_of_intuitionistic [BI PROP] {P : PROP} [Affine P] [Persistent P] :
    □ P ⊣⊢ P :=
  ⟨intuitionistically_elim, (affine_affinely P).2.trans (affinely_mono persistent)⟩

theorem affinely_of_intuitionistically [BI PROP] {P : PROP} : □ P ⊢ <affine> P :=
  and_intro and_elim_l intuitionistically_elim

theorem intuitionistically_affinely [BI PROP] {P : PROP} : □ <affine> P ⊣⊢ □ P :=
  affinely_congr persistently_affinely

theorem persistently_and_intuitionistically_sep_l [BI PROP] {P Q : PROP} :
    <pers> P ∧ Q ⊣⊢ □ P ∗ Q :=
  ⟨(and_mono_r emp_sep.2).trans <| persistently_and_sep_assoc.1.trans (sep_congr_l and_comm).2,
   and_intro ((sep_mono_l affinely_elim).trans persistently_absorb_l)
     ((sep_mono_l affinely_elim_emp).trans emp_sep.1)⟩

theorem persistently_and_intuitionistically_sep_r [BI PROP] {P Q : PROP} :
    P ∧ <pers> Q ⊣⊢ P ∗ □ Q :=
  and_comm.trans <| persistently_and_intuitionistically_sep_l.trans sep_comm

theorem and_sep_intuitionistically [BI PROP] {P Q : PROP} : □ P ∧ □ Q ⊣⊢ □ P ∗ □ Q :=
  (affinely_and_r.trans affinely_and).symm.trans persistently_and_intuitionistically_sep_l

theorem intuitionistically_and_sep [BI PROP] {P Q : PROP} : □ (P ∧ Q) ⊣⊢ □ P ∗ □ Q :=
  intuitionistically_and.trans and_sep_intuitionistically

theorem intuitionistically_sep_idem [BI PROP] {P : PROP} : □ P ∗ □ P ⊣⊢ □ P :=
  and_sep_intuitionistically.symm.trans and_self

-- Intuitionistic BIAffine
theorem intuitionistically_iff_persistently [BIAffine PROP] {P : PROP} : □ P ⊣⊢ <pers> P :=
  affine_affinely _

-- Conditional Affine
@[simp] theorem affinelyIf_false [BI PROP] (P : PROP) : iprop(<affine>?false P) = P := rfl
@[simp] theorem affinelyIf_true [BI PROP] (P : PROP) : iprop(<affine>?true P) = iprop(<affine> P) := rfl

@[rw_mono_rule]
theorem affinelyIf_mono {p : Bool} [BI PROP] {P Q : PROP}
    (h : P ⊢ Q) : <affine>?p P ⊢ <affine>?p Q :=
  match p with
  | true => affinely_mono h
  | false => h

@[rw_mono_rule]
theorem affinelyIf_congr {p : Bool} [BI PROP] {P Q : PROP} (h : P ⊣⊢ Q) : <affine>?p P ⊣⊢ <affine>?p Q :=
  ⟨affinelyIf_mono h.1, affinelyIf_mono h.2⟩

theorem affinelyIf_flag_mono {p q : Bool} [BI PROP] {P : PROP} (h : q → p) : <affine>?p P ⊢ <affine>?q P :=
  match p, q with
  | true, true | false, false => .rfl
  | true, false => affinely_elim
  | false, true => nomatch h rfl

theorem affinelyIf_elim {p : Bool} [BI PROP] {P : PROP} : <affine>?p P ⊢ P :=
  match p with
  | false => .rfl
  | true => affinely_elim

theorem affinely_affinelyIf {p : Bool} [BI PROP] {P : PROP} : <affine> P ⊢ <affine>?p P :=
  match p with
  | true => .rfl
  | false => affinely_elim

theorem affinelyIf_and {p : Bool} [BI PROP] {P Q : PROP} : <affine>?p (P ∧ Q) ⊣⊢ <affine>?p P ∧ <affine>?p Q :=
  match p with
  | false => .rfl
  | true => affinely_and

theorem affinelyIf_and_l {p : Bool} [BI PROP] {P Q : PROP} : <affine>?p P ∧ Q ⊣⊢ <affine>?p (P ∧ Q) :=
  match p with
  | false => .rfl
  | true => affinely_and_l

theorem affinelyIf_and_r {p : Bool} [BI PROP] {P Q : PROP} : P ∧ <affine>?p Q ⊣⊢ <affine>?p (P ∧ Q) :=
  match p with
  | false => .rfl
  | true => affinely_and_r

theorem affinelyIf_or {p : Bool} [BI PROP] {P Q : PROP} : <affine>?p (P ∨ Q) ⊣⊢ <affine>?p P ∨ <affine>?p Q :=
  match p with
  | false => .rfl
  | true => affinely_or

theorem affinelyIf_exists {p : Bool} [BI PROP] {Ψ : α → PROP} : <affine>?p (∃ a, Ψ a) ⊣⊢ ∃ a, <affine>?p (Ψ a) :=
  match p with
  | false => .rfl
  | true => affinely_exists

theorem affinelyIf_forall {p : Bool} [BI PROP] {Ψ : α → PROP} : <affine>?p (∀ a, Ψ a) ⊢ ∀ a, <affine>?p (Ψ a) :=
  match p with
  | false => .rfl
  | true => affinely_forall

-- Conditional Absorbing
@[simp] theorem absorbinglyIf_false [BI PROP] (P : PROP) : iprop(<absorb>?false P) = P := rfl
@[simp] theorem absorbinglyIf_true [BI PROP] (P : PROP) : iprop(<absorb>?true P) = iprop(<absorb> P) := rfl

@[rw_mono_rule]
theorem absorbinglyIf_mono {p : Bool} [BI PROP] {P Q : PROP} (h : P ⊢ Q) : <absorb>?p P ⊢ <absorb>?p Q :=
  match p with
  | false => h
  | true => absorbingly_mono h

@[rw_mono_rule]
theorem absorbinglyIf_congr {p : Bool} [BI PROP] {P Q : PROP} (h : P ⊣⊢ Q) : <absorb>?p P ⊣⊢ <absorb>?p Q :=
  ⟨absorbinglyIf_mono h.1, absorbinglyIf_mono h.2⟩

-- Conditional Persistent
@[simp] theorem persistentlyIf_false [BI PROP] (P : PROP) : iprop(<pers>?false P) = P := rfl
@[simp] theorem persistentlyIf_true [BI PROP] (P : PROP) : iprop(<pers>?true P) = iprop(<pers> P) := rfl

@[rw_mono_rule]
theorem persistentlyIf_mono {p : Bool} [BI PROP] {P Q : PROP} (h : P ⊢ Q) : <pers>?p P ⊢ <pers>?p Q :=
  match p with
  | false => h
  | true => persistently_mono h

@[rw_mono_rule]
theorem persistentlyIf_congr {p : Bool} [BI PROP] {P Q : PROP} (h : P ⊣⊢ Q) : <pers>?p P ⊣⊢ <pers>?p Q :=
  ⟨persistentlyIf_mono h.1, persistentlyIf_mono h.2⟩

theorem persistentlyIf_persistently {p : Bool} [BI PROP] {P : PROP} : <pers>?p <pers> P ⊣⊢ <pers> P :=
  match p with
  | false => .rfl
  | true => persistently_idem

theorem persistentlyIf_intutitionistically {p : Bool} [BI PROP] {P : PROP} : <pers>?p □ P ⊢ <pers> P :=
  match p with
  | false => persistently_of_intuitionistically
  | true => persistently_mono intuitionistically_elim

-- Conditional Intuitionistic
@[simp] theorem intuitionisticallyIf_false [BI PROP] (P : PROP) : iprop(□?false P) = P := rfl
@[simp] theorem intuitionisticallyIf_true [BI PROP] (P : PROP) : iprop(□?true P) = iprop(□ P) := rfl

@[rw_mono_rule]
theorem intuitionisticallyIf_mono {p : Bool} [BI PROP] {P Q : PROP} (h : P ⊢ Q) : □?p P ⊢ □?p Q :=
  match p with
  | false => h
  | true => intuitionistically_mono h

@[rw_mono_rule]
theorem intuitionisticallyIf_congr {p : Bool} [BI PROP] {P Q : PROP} (h : P ⊣⊢ Q) : □?p P ⊣⊢ □?p Q :=
  ⟨intuitionisticallyIf_mono h.1, intuitionisticallyIf_mono h.2⟩

theorem intuitionisticallyIf_elim {p : Bool} [BI PROP] {P : PROP} : □?p P ⊢ P :=
  match p with
  | false => .rfl
  | true => intuitionistically_elim

theorem intuitionisticallyIf_of_intuitionistically (p : Bool) [BI PROP] {P : PROP} : □ P ⊢ □?p P :=
  match p with
  | true => .rfl
  | false => intuitionistically_elim

theorem intuitionisticallyIf_intutitionistically {p : Bool} [BI PROP] {P : PROP} : □?p □ P ⊣⊢ □ P :=
  match p with
  | false => .rfl
  | true => intuitionistically_idem

theorem affinelyIf_of_intuitionisticallyIf {p : Bool} [BI PROP] {P : PROP} : □?p P ⊢ <affine>?p P :=
  match p with
  | false => .rfl
  | true => affinely_of_intuitionistically

theorem intuitionisticallyIf_and {p : Bool} [BI PROP] {P Q : PROP} : □?p (P ∧ Q) ⊣⊢ □?p P ∧ □?p Q :=
  match p with
  | false => .rfl
  | true => intuitionistically_and

theorem intuitionisticallyIf_or (p : Bool) [BI PROP] {P Q : PROP} : □?p (P ∨ Q) ⊣⊢ □?p P ∨ □?p Q :=
  match p with
  | false => .rfl
  | true => intuitionistically_or

theorem intuitionisticallyIf_exists {p : Bool} [BI PROP] {Ψ : α → PROP} : (□?p ∃ a, Ψ a) ⊣⊢ ∃ a, □?p Ψ a :=
  match p with
  | false => .rfl
  | true => intuitionistically_exists

theorem intuitionisticallyIf_sep_2 {p : Bool} [BI PROP] {P Q : PROP} : □?p P ∗ □?p Q ⊢ □?p (P ∗ Q) :=
  match p with
  | false => .rfl
  | true => intuitionistically_sep_2

theorem intuitionisticallyIf_idem {p : Bool} [BI PROP] {P : PROP} : □?p □?p P ⊣⊢ □?p P :=
  match p with
  | false => .rfl
  | true => intuitionistically_idem

theorem intuitionisticallyIf_comm {p q : Bool} [BI PROP] {P : PROP} : □?p □?q P ⊣⊢ □?q □?p P := by
  cases p <;> cases q <;> exact .rfl

theorem intuitionisticallyIf_affinely [BI PROP] {P : PROP} : □?p <affine> P ⊣⊢ <affine> □?p P :=
  match p with
  | false => .rfl
  | true =>
    ⟨(intuitionistically_mono affinely_elim).trans (and_intro affinely_elim_emp .rfl),
     affinely_elim.trans intuitionistically_affinely.2⟩

-- Persistent Propositions
theorem persistently_intro [BI PROP] {P : PROP} [Persistent P] : P ⊢ <pers> P := persistent

theorem persistent_and_affinely_sep_l_1 [BI PROP] {P Q : PROP} [Persistent P] :
    P ∧ Q ⊢ <affine> P ∗ Q :=
  (and_mono_l persistent).trans <| persistently_and_intuitionistically_sep_l.1.trans <|
    sep_mono_l affinely_of_intuitionistically

theorem persistent_and_affinely_sep_r_1 [BI PROP] {P Q : PROP} [Persistent Q] :
    P ∧ Q ⊢ P ∗ <affine> Q :=
  and_comm.1.trans <| persistent_and_affinely_sep_l_1.trans sep_comm.1

theorem persistent_and_affinely_sep_l [BI PROP] {P Q : PROP} [Persistent P] [Absorbing P] :
    P ∧ Q ⊣⊢ <affine> P ∗ Q :=
  ⟨persistent_and_affinely_sep_l_1, (sep_mono_l <| affinely_mono persistent).trans <|
    persistently_and_intuitionistically_sep_l.2.trans <| and_mono_l persistently_elim⟩

theorem persistent_and_affinely_sep_r [BI PROP] {P Q : PROP} [Persistent Q] [Absorbing Q] :
    P ∧ Q ⊣⊢ P ∗ <affine> Q :=
  and_comm.trans <| persistent_and_affinely_sep_l.trans sep_comm

theorem persistent_and_sep_1 [BI PROP] {P Q : PROP} :
    [TCOr (Persistent P) (Persistent Q)] → P ∧ Q ⊢ P ∗ Q
  | TCOr.l => persistent_and_affinely_sep_l_1.trans (sep_mono_l affinely_elim)
  | TCOr.r => persistent_and_affinely_sep_r_1.trans (sep_mono_r affinely_elim)

theorem absorbingly_intuitionistically [BI PROP] {P : PROP} : <absorb> □ P ⊣⊢ <pers> P :=
  ⟨(absorbingly_mono persistently_of_intuitionistically).trans absorbingly_persistently.1,
   and_self.2.trans <| persistently_and_intuitionistically_sep_r.1.trans <| sep_mono_l true_intro⟩

theorem absorbingly_affinely_intro_of_persistent [BI PROP] {P : PROP} [Persistent P] :
    P ⊢ <absorb> <affine> P :=
  persistent.trans <| absorbingly_intuitionistically.2.trans <|
  absorbingly_mono affinely_of_intuitionistically

theorem bigOp_sep_nil [BI PROP] : iprop([∗] []) ⊣⊢ (emp : PROP) := .rfl

theorem bigOp_and_nil [BI PROP] : iprop([∧] []) ⊣⊢ (True : PROP) := .rfl

theorem bigOp_sep_cons [BI PROP] {P : PROP} {Ps : List PROP} :
    [∗] (P :: Ps) ⊣⊢ P ∗ [∗] Ps := bigOp_cons

theorem bigOp_and_cons [BI PROP] {P : PROP} {Ps : List PROP} :
    [∧] (P :: Ps) ⊣⊢ P ∧ [∧] Ps := bigOp_cons
