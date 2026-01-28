/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Markus de Medeiros, Michael Sammler
-/
import Iris.BI.Classes
import Iris.BI.Extensions
import Iris.BI.BI
import Iris.Std.Classes
import Iris.Std.Rewrite
import Iris.Std.TC

namespace Iris.BI
open Iris.Std BI

/-! # Entails -/

instance entails_trans [BI PROP] : Trans (α := PROP) Entails Entails Entails where
  trans h1 h2 := h1.trans h2
instance entails_antisymm [BI PROP] : Antisymmetric (α := PROP) BiEntails Entails where
  antisymm h1 h2 := ⟨h1, h2⟩

instance equiv_trans [BI PROP] : Trans (α := PROP) BiEntails BiEntails BiEntails where
  trans h1 h2 := h1.trans h2

/-! # Logic -/

theorem and_elim_l' [BI PROP] {P Q R : PROP} (h : P ⊢ R) : P ∧ Q ⊢ R := and_elim_l.trans h

theorem and_elim_r' [BI PROP] {P Q R : PROP} (h : Q ⊢ R) : P ∧ Q ⊢ R := and_elim_r.trans h

theorem or_intro_l' [BI PROP] {P Q R : PROP} (h : P ⊢ Q) : P ⊢ Q ∨ R := h.trans or_intro_l

theorem or_intro_r' [BI PROP] {P Q R : PROP} (h : P ⊢ R) : P ⊢ Q ∨ R := h.trans or_intro_r

theorem and_symm [BI PROP] {P Q : PROP} : P ∧ Q ⊢ Q ∧ P := and_intro and_elim_r and_elim_l

theorem or_symm [BI PROP] {P Q : PROP} : P ∨ Q ⊢ Q ∨ P := or_elim or_intro_r or_intro_l

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
theorem imp_congr [BI PROP] {P P' Q Q' : PROP}
    (h1 : P ⊣⊢ Q) (h2 : P' ⊣⊢ Q') : (P → P') ⊣⊢ (Q → Q') :=
  ⟨imp_mono h1.2 h2.1, imp_mono h1.1 h2.2⟩

theorem imp_congr_l [BI PROP] {P P' Q : PROP} (h : P ⊣⊢ P') : (P → Q) ⊣⊢ (P' → Q) :=
  imp_congr h .rfl

theorem imp_congr_r [BI PROP] {P Q Q' : PROP} (h : Q ⊣⊢ Q') : (P → Q) ⊣⊢ (P → Q') :=
  imp_congr .rfl h

theorem forall_ne [BI PROP] {Φ Ψ : α → PROP} (h : ∀ a, Φ a ≡{n}≡ Ψ a) :
    iprop(∀ a, Φ a) ≡{n}≡ iprop(∀ a, Ψ a) := sForall_ne <| by
  constructor <;> rintro _ ⟨a, rfl⟩ <;> exact ⟨_, ⟨a, rfl⟩, h _⟩

theorem forall_intro [BI PROP] {P : PROP} {Ψ : α → PROP} (h : ∀ a, P ⊢ Ψ a) : P ⊢ ∀ a, Ψ a :=
  sForall_intro fun _ ⟨_, eq⟩ => eq ▸ h _

theorem forall_elim [BI PROP] {Ψ : α → PROP} (a : α) : (∀ a, Ψ a) ⊢ Ψ a := sForall_elim ⟨_, rfl⟩

@[rw_mono_rule]
theorem forall_mono [BI PROP] {Φ Ψ : α → PROP} (h : ∀ a, Φ a ⊢ Ψ a) : (∀ a, Φ a) ⊢ ∀ a, Ψ a :=
  forall_intro fun a => (forall_elim a).trans (h a)

@[rw_mono_rule]
theorem forall_congr [BI PROP] {Φ Ψ : α → PROP} (h : ∀ a, Φ a ⊣⊢ Ψ a) : (∀ a, Φ a) ⊣⊢ ∀ a, Ψ a :=
  ⟨forall_mono fun a => (h a).1, forall_mono fun a => (h a).2⟩

theorem exists_ne [BI PROP] {Φ Ψ : α → PROP} (h : ∀ a, Φ a ≡{n}≡ Ψ a) :
    iprop(∃ a, Φ a) ≡{n}≡ iprop(∃ a, Ψ a) := sExists_ne <| by
  constructor <;> rintro _ ⟨a, rfl⟩ <;> exact ⟨_, ⟨a, rfl⟩, h _⟩

theorem exists_intro [BI PROP] {Ψ : α → PROP} (a : α) : Ψ a ⊢ ∃ a, Ψ a :=
  sExists_intro ⟨_, rfl⟩

theorem exists_elim [BI PROP] {Φ : α → PROP} {Q : PROP} (h : ∀ a, Φ a ⊢ Q) : (∃ a, Φ a) ⊢ Q :=
  sExists_elim fun _ ⟨_, eq⟩ => eq ▸ h _

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

theorem and_comm [BI PROP] {P Q : PROP} : P ∧ Q ⊣⊢ Q ∧ P := ⟨and_symm, and_symm⟩
instance [BI PROP] : Commutative (α := PROP) BiEntails and := ⟨and_comm⟩

theorem or_comm [BI PROP] {P Q : PROP} : P ∨ Q ⊣⊢ Q ∨ P := ⟨or_symm, or_symm⟩
instance [BI PROP] : Commutative (α := PROP) BiEntails or := ⟨or_comm⟩

theorem true_and [BI PROP] {P : PROP} : True ∧ P ⊣⊢ P :=
  ⟨and_elim_r, and_intro (pure_intro trivial) .rfl⟩
instance [BI PROP] : LeftId (α := PROP) BiEntails iprop(True) and := ⟨true_and⟩

theorem and_true [BI PROP] {P : PROP} : P ∧ True ⊣⊢ P := and_comm.trans true_and
instance [BI PROP] : RightId (α := PROP) BiEntails iprop(True) and := ⟨and_true⟩

theorem false_and [BI PROP] {P : PROP} : False ∧ P ⊣⊢ False := ⟨and_elim_l, false_elim⟩

theorem and_false [BI PROP] {P : PROP} : P ∧ False ⊣⊢ False := and_comm.trans false_and

theorem true_or [BI PROP] {P : PROP} : True ∨ P ⊣⊢ True := ⟨true_intro, or_intro_l⟩

theorem or_true [BI PROP] {P : PROP} : P ∨ True ⊣⊢ True := or_comm.trans true_or

theorem false_or [BI PROP] {P : PROP} : False ∨ P ⊣⊢ P := ⟨or_elim false_elim .rfl, or_intro_r⟩
instance [BI PROP] : LeftId (α := PROP) BiEntails iprop(False) or := ⟨false_or⟩

theorem or_false [BI PROP] {P : PROP} : P ∨ False ⊣⊢ P := or_comm.trans false_or
instance [BI PROP] : RightId (α := PROP) BiEntails iprop(False) or := ⟨or_false⟩

theorem and_assoc [BI PROP] {P Q R : PROP} : (P ∧ Q) ∧ R ⊣⊢ P ∧ Q ∧ R :=
  ⟨and_intro (and_elim_l' and_elim_l) (and_mono_l and_elim_r),
   and_intro (and_mono_r and_elim_l) (and_elim_r' and_elim_r)⟩

theorem or_assoc [BI PROP] {P Q R : PROP} : (P ∨ Q) ∨ R ⊣⊢ P ∨ Q ∨ R :=
  ⟨or_elim (or_mono_r or_intro_l) (or_intro_r' or_intro_r),
   or_elim (or_intro_l' or_intro_l) (or_mono_l or_intro_r)⟩

theorem true_imp [BI PROP] {P : PROP} : (True → P) ⊣⊢ P :=
  ⟨and_true.2.trans imp_elim_l, imp_intro and_elim_l⟩
instance [BI PROP] : LeftId (α := PROP) BiEntails iprop(True) and := ⟨true_and⟩

theorem imp_self [BI PROP] {P Q : PROP} : Q ⊢ P → P := imp_intro and_elim_r

theorem imp_trans [BI PROP] {P Q R : PROP} : (P → Q) ∧ (Q → R) ⊢ P → R :=
  imp_intro' <| and_assoc.2.trans <| (and_mono_l imp_elim_r).trans imp_elim_r

theorem false_imp [BI PROP] {P : PROP} : (False → P) ⊣⊢ True :=
  ⟨true_intro, imp_intro <| and_elim_r.trans false_elim⟩

theorem exists_impl_forall [BI PROP] {Ψ : α → PROP} {P : PROP} :
    ((∃ x, Ψ x) → P) ⊣⊢ ∀ x, Ψ x → P :=
  ⟨forall_intro fun x => imp_mono (exists_intro x) .rfl,
   imp_intro <| imp_elim' <| exists_elim fun x =>
     imp_intro <| and_comm.1.trans <| (and_mono (forall_elim x) .rfl).trans imp_elim_l⟩

theorem forall_unit [BI PROP] {Ψ : Unit → PROP} : (∀ x, Ψ x) ⊣⊢ Ψ () :=
  ⟨forall_elim (), forall_intro fun () => .rfl⟩

theorem exists_unit [BI PROP] {Ψ : Unit → PROP} : (∃ x, Ψ x) ⊣⊢ Ψ () :=
  ⟨exists_elim fun () => .rfl, exists_intro ()⟩

theorem exists_exists [BI PROP] {Ψ : α → β → PROP} : (∃ x y, Ψ x y) ⊣⊢ (∃ y x, Ψ x y) :=
  ⟨exists_elim fun x => exists_elim fun y => (exists_intro (Ψ:=λ x => Ψ x y) x ).trans (exists_intro (Ψ:=λ y => (∃ x, Ψ x y)) y),
   exists_elim fun y => exists_elim fun x => (exists_intro (Ψ:=λ y => Ψ x y) y).trans (exists_intro (Ψ:=λ x => (∃ y, Ψ x y)) x)⟩

theorem forall_forall [BI PROP] {Ψ : α → β → PROP} : (∀ x y, Ψ x y) ⊣⊢ (∀ y x, Ψ x y) :=
  ⟨forall_intro fun y => forall_intro fun x => (forall_elim x).trans (forall_elim y),
   forall_intro fun x => forall_intro fun y => (forall_elim y).trans (forall_elim x)⟩

theorem exists_forall [BI PROP] {Ψ : α → β → PROP} : (∃ x, ∀ y, Ψ x y) ⊢ (∀ y, ∃ x, Ψ x y) :=
  forall_intro fun y => exists_elim fun x =>
    (forall_elim y).trans (exists_intro (Ψ := λ x => Ψ x y) x)

theorem impl_curry [BI PROP] {P Q R : PROP} : (P → Q → R) ⊣⊢ (P ∧ Q → R) :=
  ⟨imp_intro <| and_assoc.2.trans <| (and_mono_l imp_elim_l).trans imp_elim_l,
   imp_intro <| imp_intro <| and_assoc.1.trans <| imp_elim_l⟩

theorem or_and_l [BI PROP] {P Q R : PROP} : P ∨ (Q ∧ R) ⊣⊢ (P ∨ Q) ∧ (P ∨ R) :=
  ⟨or_elim (and_intro or_intro_l or_intro_l) (and_mono or_intro_r or_intro_r),
   imp_elim' <| or_elim (imp_intro <| or_intro_l' and_elim_l) <|
     imp_intro <| imp_elim' <| or_elim (imp_intro <| or_intro_l' and_elim_l)
       (imp_intro <| or_intro_r' <| and_intro and_elim_l and_elim_r)⟩

theorem or_and_r [BI PROP] {P Q R : PROP} : (P ∧ Q) ∨ R ⊣⊢ (P ∨ R) ∧ (Q ∨ R) :=
  (or_comm.trans <| or_and_l.trans <| and_congr or_comm or_comm)

theorem and_or_l [BI PROP] {P Q R : PROP} : P ∧ (Q ∨ R) ⊣⊢ P ∧ Q ∨ P ∧ R :=
  ⟨imp_elim' <| or_elim (imp_intro' or_intro_l) (imp_intro' or_intro_r),
   and_intro (or_elim and_elim_l and_elim_l)
    (or_elim (or_intro_l' and_elim_r) (or_intro_r' and_elim_r))⟩

theorem and_or_r [BI PROP] {P Q R : PROP} : (P ∨ Q) ∧ R ⊣⊢ (P ∧ R) ∨ (Q ∧ R) :=
  and_comm.trans <| and_or_l.trans <| or_congr and_comm and_comm

theorem and_exists_l [BI PROP] {P : PROP} {Ψ : α → PROP} : P ∧ (∃ a, Ψ a) ⊣⊢ ∃ a, P ∧ Ψ a :=
  ⟨imp_elim' <| exists_elim fun _ =>
    imp_intro' (exists_intro (Ψ := fun a => iprop(P ∧ Ψ a)) _),
   exists_elim fun _ => and_mono_r (exists_intro _)⟩

theorem and_exists_r [BI PROP] {Φ : α → PROP} {P : PROP} : (∃ a, Φ a) ∧ P ⊣⊢ ∃ a, Φ a ∧ P :=
  and_comm.trans <| and_exists_l.trans <| exists_congr fun _ => and_comm

theorem or_exists [BI PROP] {Φ Ψ : α → PROP} : (∃ a, Φ a ∨ Ψ a) ⊣⊢ (∃ a, Φ a) ∨ (∃ a, Ψ a) :=
  ⟨exists_elim fun a => or_elim (or_intro_l' (exists_intro a)) (or_intro_r' (exists_intro a)),
   or_elim (exists_mono fun _ => or_intro_l) (exists_mono fun _ => or_intro_r)⟩

theorem and_alt [BI PROP] {P Q : PROP} :
    P ∧ Q ⊣⊢ «forall» (fun b : Bool => if b then P else Q) :=
  ⟨forall_intro (·.casesOn and_elim_r and_elim_l),
   and_intro (forall_elim true) (forall_elim false)⟩

theorem or_alt [BI PROP] {P Q : PROP} :
    P ∨ Q ⊣⊢ «exists» (fun b : Bool => if b then P else Q) :=
  ⟨or_elim (exists_intro (Ψ:=λ b => if b then P else Q) true)
           (exists_intro (Ψ:=λ b => if b then P else Q) false),
   exists_elim (Bool.rec or_intro_r or_intro_l ·)⟩

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

theorem or_eq_ite [BI PROP] {P Q : PROP} : P ∨ Q ⊣⊢ ∃ (b : Bool), if b then P else Q := by
  constructor
  · apply or_elim
    · exact exists_intro (Ψ := fun b => if b = true then P else Q) true
    · exact exists_intro (Ψ := fun b => if b = true then P else Q) false
  · exact exists_elim fun | true => or_intro_l | false => or_intro_r

theorem exists_intro' [BI PROP] {P : PROP} {Ψ : α → PROP} (a : α) (h : P ⊢ Ψ a) : P ⊢ ∃ a, Ψ a :=
  h.trans (exists_intro a)

/-! # BI -/

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

theorem wand_congr_l [BI PROP] {P P' Q : PROP} (h : P ⊣⊢ P') : (P -∗ Q) ⊣⊢ (P' -∗ Q) :=
  wand_congr h .rfl

theorem wand_congr_r [BI PROP] {P Q Q' : PROP} (h : Q ⊣⊢ Q') : (P -∗ Q) ⊣⊢ (P -∗ Q') :=
  wand_congr .rfl h

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

theorem sep_sep_sep_comm [BI PROP] {P Q R S : PROP} : (P ∗ Q) ∗ (R ∗ S) ⊣⊢ (P ∗ R) ∗ (Q ∗ S) :=
  sep_assoc.trans <| (sep_congr_r sep_left_comm).trans sep_assoc.symm

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

theorem true_sep_2 [BI PROP] {P : PROP} : P ⊢ True ∗ P := emp_sep.2.trans (sep_mono_l true_intro)

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

theorem wand_rfl [BI PROP] {P : PROP} : ⊢ P -∗ P := wand_intro emp_sep.1

@[rw_mono_rule]
theorem wandIff_congr [BI PROP] {P P' Q Q' : PROP} (h1 : P ⊣⊢ Q) (h2 : P' ⊣⊢ Q') :
    (P ∗-∗ P') ⊣⊢ (Q ∗-∗ Q') := and_congr (wand_congr h1 h2) (wand_congr h2 h1)

theorem wandIff_congr_l [BI PROP] {P P' Q : PROP} (h : P ⊣⊢ P') : (P ∗-∗ Q) ⊣⊢ (P' ∗-∗ Q) :=
  wandIff_congr h .rfl

theorem wandIff_congr_r [BI PROP] {P Q Q' : PROP} (h : Q ⊣⊢ Q') : (P ∗-∗ Q) ⊣⊢ (P ∗-∗ Q') :=
  wandIff_congr .rfl h

theorem wandIff_refl [BI PROP] {P : PROP} : ⊢ P ∗-∗ P := and_intro wand_rfl wand_rfl

theorem wand_entails [BI PROP] {P Q : PROP} (h : ⊢ P -∗ Q) : P ⊢ Q :=
  emp_sep.2.trans (wand_elim h)

theorem entails_wand [BI PROP] {P Q : PROP} (h : P ⊢ Q) : ⊢ P -∗ Q :=
  wand_intro (emp_sep.1.trans h)

theorem equiv_wandIff [BI PROP] {P Q : PROP} (h : P ⊣⊢ Q) : ⊢ P ∗-∗ Q :=
  wandIff_refl.trans (wandIff_congr_l h).2

theorem wandIff_equiv [BI PROP] {P Q : PROP} (h : ⊢ P ∗-∗ Q) : P ⊣⊢ Q :=
  ⟨wand_entails (h.trans and_elim_l), wand_entails (h.trans and_elim_r)⟩

/-! # Pure -/

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
  by_cases h : φ1
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

/-! # Affine -/

theorem affinely_ne [BI PROP] : OFE.NonExpansive (@affinely PROP _) where
  ne _ _ _ h := and_ne.1 .rfl h

@[rw_mono_rule]
theorem affinely_congr [BI PROP] {P P' : PROP} (h : P ⊣⊢ P') :
    <affine> P ⊣⊢ <affine> P' := and_congr_r h

theorem affinely_elim_emp [BI PROP] {P : PROP} : <affine> P ⊢ emp := and_elim_l

theorem affinely_elim [BI PROP] {P : PROP} : <affine> P ⊢ P := and_elim_r

@[rw_mono_rule]
theorem affinely_mono [BI PROP] {P Q : PROP} : (P ⊢ Q) → <affine> P ⊢ <affine> Q := and_mono_r

theorem affinely_idem [BI PROP] {P : PROP} : <affine> <affine> P ⊣⊢ <affine> P :=
  and_assoc.symm.trans (and_congr_l and_self)

theorem affinely_intro' [BI PROP] {P Q : PROP} (h : P ⊢ <affine> Q) :
    <affine> P ⊢ <affine> Q := (affinely_mono h).trans affinely_idem.1

theorem affinely_false [BI PROP] : <affine> False ⊣⊢ (False : PROP) := and_false

theorem affinely_emp [BI PROP] : <affine> emp ⊣⊢ (emp : PROP) := and_self

theorem affinely_or [BI PROP] {P Q : PROP} : <affine> (P ∨ Q) ⊣⊢ <affine> P ∨ <affine> Q := and_or_l

theorem affinely_and [BI PROP] {P Q : PROP} : <affine> (P ∧ Q) ⊣⊢ <affine> P ∧ <affine> Q :=
  (and_congr_l and_self.symm).trans <| and_assoc.trans <|
    (and_congr_r and_left_comm).trans and_assoc.symm

theorem affinely_sep_2 [BI PROP] {P Q : PROP} : <affine> P ∗ <affine> Q ⊢ <affine> (P ∗ Q) :=
  and_intro
    (sep_mono affinely_elim_emp affinely_elim_emp |>.trans sep_emp.1)
    (sep_mono affinely_elim affinely_elim)

theorem affinely_sep_r [BI PROP] [BIPositive PROP] {P Q : PROP} :
    <affine> (P ∗ Q) ⊢ P ∗ <affine> Q :=
  (affinely_mono sep_symm).trans <| affinely_sep_l.trans sep_symm

theorem affinely_sep [BI PROP] [BIPositive PROP] {P Q : PROP} :
    <affine> (P ∗ Q) ⊣⊢ <affine> P ∗ <affine> Q :=
  ⟨affinely_idem.2.trans <| (affinely_mono affinely_sep_r).trans affinely_sep_l, affinely_sep_2⟩

theorem affinely_forall_1 [BI PROP] {Φ : α → PROP} : <affine> (∀ a, Φ a) ⊢ ∀ a, <affine> (Φ a) :=
  forall_intro fun a => affinely_mono (forall_elim a)

theorem affinely_exists [BI PROP] {Φ : α → PROP} : <affine> (∃ a, Φ a) ⊣⊢ ∃ a, <affine> (Φ a) :=
  and_exists_l

theorem affinely_true [BI PROP] : <affine> True ⊣⊢ (emp : PROP) :=
  ⟨and_elim_l, and_intro .rfl true_intro⟩

theorem affinely_and_l [BI PROP] {P Q : PROP} : <affine> P ∧ Q ⊣⊢ <affine> (P ∧ Q) := and_assoc

theorem affinely_and_r [BI PROP] {P Q : PROP} : P ∧ <affine> Q ⊣⊢ <affine> (P ∧ Q) := and_left_comm

theorem affinely_and_lr [BI PROP] {P Q : PROP} : <affine> P ∧ Q ⊣⊢ P ∧ <affine> Q :=
  affinely_and_l.trans affinely_and_r.symm

/-! # Affine instances -/

instance emp_affine [BI PROP] : Affine (PROP := PROP) iprop(emp) where
  affine := .rfl

theorem affine_mono [BI PROP] {P Q : PROP} (h : P ⊢ Q) [Affine Q] : Affine P where
  affine := h.trans affine

instance false_affine [BI PROP] : Affine (PROP := PROP) iprop(False) where
  affine := false_elim

instance and_affine_l [BI PROP] (P Q : PROP) [Affine P] : Affine iprop(P ∧ Q) where
  affine := and_elim_l.trans affine

instance and_affine_r [BI PROP] (P Q : PROP) [Affine Q] : Affine iprop(P ∧ Q) where
  affine := and_elim_r.trans affine

instance or_affine [BI PROP] (P Q : PROP) [Affine P] [Affine Q] : Affine iprop(P ∨ Q) where
  affine := or_elim affine affine

instance forall_affine [Inhabited α] [BI PROP] (Φ : α → PROP) [∀ x, Affine (Φ x)] :
    Affine iprop(∀ x, Φ x) where
  affine := (forall_elim default).trans affine

instance exists_affine [BI PROP] (Φ : α → PROP) [∀ x, Affine (Φ x)] : Affine iprop(∃ x, Φ x) where
  affine := exists_elim fun _ => affine

instance sep_affine [BI PROP] (P Q : PROP) [Affine P] [Affine Q] : Affine iprop(P ∗ Q) where
  affine := (sep_mono affine affine).trans sep_emp.1

instance affinely_affine [BI PROP] (P : PROP) : Affine iprop(<affine> P) where
  affine := affinely_elim_emp

instance [BIBase PROP] : Inhabited PROP where
  default := emp

/-! # Absorbing -/

theorem absorbingly_ne [BI PROP] : OFE.NonExpansive (@absorbingly PROP _) where
  ne _ _ _ h := sep_ne.1 .rfl h

@[rw_mono_rule]
theorem absorbingly_congr [BI PROP] {P P' : PROP} (h : P ⊣⊢ P') :
    <absorb> P ⊣⊢ <absorb> P' := sep_congr_r h

theorem absorbingly_intro [BI PROP] {P : PROP} : P ⊢ <absorb> P := true_sep_2

@[rw_mono_rule]
theorem absorbingly_mono [BI PROP] {P Q : PROP} : (P ⊢ Q) → <absorb> P ⊢ <absorb> Q := sep_mono_r

theorem absorbingly_idem [BI PROP] {P : PROP} : <absorb> <absorb> P ⊣⊢ <absorb> P :=
  ⟨sep_assoc.2.trans (sep_mono_l true_intro), absorbingly_intro⟩

instance absorbingly_absorbing [BI PROP] (P : PROP) : Absorbing iprop(<absorb> P) where
  absorbing := absorbingly_idem.1

theorem absorbingly_pure {φ : Prop} [BI PROP] : <absorb> ⌜φ⌝ ⊣⊢ (⌜φ⌝ : PROP) :=
  ⟨wand_elim' <| pure_elim' fun h => wand_intro' <| pure_intro h, absorbingly_intro⟩

instance pureAbsorbing (φ : Prop) [BI PROP] : Absorbing (PROP := PROP) iprop(⌜φ⌝) where
  absorbing := absorbingly_pure.1

theorem absorbingly_true [BI PROP] : <absorb> True ⊣⊢ (True : PROP) := absorbingly_pure

theorem absorbingly_or [BI PROP] {P Q : PROP} : <absorb> (P ∨ Q) ⊣⊢ <absorb> P ∨ <absorb> Q :=
  sep_or_l

theorem absorbingly_and_1 [BI PROP] {P Q : PROP} : <absorb> (P ∧ Q) ⊢ <absorb> P ∧ <absorb> Q :=
  and_intro (absorbingly_mono and_elim_l) (absorbingly_mono and_elim_r)

theorem absorbingly_forall_1 [BI PROP] {Φ : α → PROP} : <absorb> (∀ a, Φ a) ⊢ ∀ a, <absorb> (Φ a) :=
  forall_intro fun a => absorbingly_mono (forall_elim a)

theorem absorbingly_exists [BI PROP] {Φ : α → PROP} :
    <absorb> (∃ a, Φ a) ⊣⊢ ∃ a, <absorb> (Φ a) := by
  simp [absorbingly, sep_exists_l]

theorem absorbingly_sep [BI PROP] {P Q : PROP} : <absorb> (P ∗ Q) ⊣⊢ <absorb> P ∗ <absorb> Q :=
  absorbingly_idem.symm.trans <| (sep_congr_r sep_left_comm).trans sep_assoc.symm

theorem absorbingly_emp [BI PROP] : <absorb> (emp : PROP) ⊣⊢ True := sep_emp

theorem absorbingly_wand_1 [BI PROP] {P Q : PROP} : <absorb> (P -∗ Q) ⊢ <absorb> P -∗ <absorb> Q :=
  wand_intro' <| absorbingly_sep.2.trans <| absorbingly_mono wand_elim_r

theorem absorbingly_sep_l [BI PROP] {P Q : PROP} : <absorb> P ∗ Q ⊣⊢ <absorb> (P ∗ Q) := sep_assoc

theorem absorbingly_sep_r [BI PROP] {P Q : PROP} : P ∗ <absorb> Q ⊣⊢ <absorb> (P ∗ Q) :=
  sep_left_comm

theorem absorbingly_sep_lr [BI PROP] {P Q : PROP} : <absorb> P ∗ Q ⊣⊢ P ∗ <absorb> Q :=
  absorbingly_sep_l.trans absorbingly_sep_r.symm

theorem affinely_absorbingly [BI PROP] [BIPositive PROP] {P : PROP} :
    <affine> <absorb> P ⊣⊢ <affine> P :=
  affinely_sep.trans <| (sep_congr_l affinely_true).trans emp_sep

/-! # Absorbing instances -/

instance pure_absorbing [BI PROP] (φ : Prop) : Absorbing iprop(⌜φ⌝ : PROP) where
  absorbing := absorbingly_pure.1

instance and_absorbing [BI PROP] (P Q : PROP) [Absorbing P] [Absorbing Q] :
    Absorbing iprop(P ∧ Q) where
  absorbing := absorbingly_and_1.trans (and_mono absorbing absorbing)

instance or_absorbing [BI PROP] (P Q : PROP) [Absorbing P] [Absorbing Q] :
    Absorbing iprop(P ∨ Q) where
  absorbing := absorbingly_or.1.trans (or_mono absorbing absorbing)

instance forall_absorbing [BI PROP] (Φ : α → PROP) [∀ x, Absorbing (Φ x)] :
    Absorbing iprop(∀ x, Φ x) where
  absorbing := absorbingly_forall_1.trans (forall_mono fun _ => absorbing)

instance exists_absorbing [BI PROP] (Φ : α → PROP) [∀ x, Absorbing (Φ x)] :
    Absorbing iprop(∃ x, Φ x) where
  absorbing := absorbingly_exists.1.trans (exists_mono fun _ => absorbing)

instance sep_absorbing_l [BI PROP] (P Q : PROP) [Absorbing P] : Absorbing iprop(P ∗ Q) where
  absorbing := absorbingly_sep_l.2.trans (sep_mono_l absorbing)

instance sep_absorbing_r [BI PROP] (P Q : PROP) [Absorbing Q] : Absorbing iprop(P ∗ Q) where
  absorbing := absorbingly_sep_r.2.trans (sep_mono_r absorbing)

instance (priority := default + 10) biaffine_absorbing [BI PROP] [BIAffine PROP]
    (P : PROP) : Absorbing P where
  absorbing := (sep_mono_l affine).trans emp_sep.1

/-! # Affine / Absorbing Propositions -/

theorem affine_affinely [BI PROP] (P : PROP) [Affine P] : <affine> P ⊣⊢ P :=
  ⟨affinely_elim, and_intro affine .rfl⟩

theorem biaffine_iff_true_emp [BI PROP] : BIAffine PROP ↔ (True : PROP) ⊢ emp :=
  ⟨fun _ => affine, fun h => ⟨fun _ => ⟨true_intro.trans h⟩⟩⟩

theorem biaffine_of_true_affine [BI PROP] [Affine (iprop(True) : PROP)] : BIAffine PROP :=
  biaffine_iff_true_emp.2 affine

theorem absorbing_absorbingly [BI PROP] {P : PROP} [Absorbing P] : <absorb> P ⊣⊢ P :=
  ⟨absorbing, absorbingly_intro⟩

theorem absorbing_of_emp_absorbing [BI PROP] [Absorbing (emp : PROP)] (P : PROP) : Absorbing P where
  absorbing := (absorbingly_mono emp_sep.2).trans <| absorbingly_sep_l.2.trans <|
    (sep_mono_l absorbing).trans emp_sep.1

theorem sep_elim_l [BI PROP] {P Q : PROP} : [TCOr (Affine Q) (Absorbing P)] → P ∗ Q ⊢ P
  | TCOr.l => (sep_mono_r affine).trans sep_emp.1
  | TCOr.r => (sep_mono_r true_intro).trans <| sep_comm.1.trans absorbing

theorem sep_elim_r [BI PROP] {P Q : PROP} [TCOr (Affine P) (Absorbing Q)] : P ∗ Q ⊢ Q :=
  sep_comm.1.trans sep_elim_l

instance wand_absorbing_l [BI PROP] (P Q : PROP) [Absorbing P] : Absorbing iprop(P -∗ Q) where
  absorbing := wand_intro' <| sep_assoc.2.trans <| (sep_mono_l sep_elim_l).trans wand_elim_r

instance wand_absorbing_r [BI PROP] (P Q : PROP) [Absorbing Q] : Absorbing iprop(P -∗ Q) where
  absorbing := absorbingly_wand_1.trans (wand_mono absorbingly_intro absorbing)

theorem sep_and [BI PROP] {P Q : PROP}
    [TCOr (Affine P) (Absorbing Q)] [TCOr (Affine Q) (Absorbing P)] : P ∗ Q ⊢ P ∧ Q :=
  and_intro sep_elim_l sep_elim_r

theorem affinely_intro [BI PROP] {P Q : PROP} [Affine P] (h : P ⊢ Q) : P ⊢ <affine> Q :=
  (affine_affinely _).2.trans (affinely_mono h)

theorem emp_and [BI PROP] {P : PROP} [Affine P] : emp ∧ P ⊣⊢ P :=
  ⟨and_elim_r, and_intro affine .rfl⟩
instance [BI PROP] [BIAffine PROP] : LeftId (α := PROP) BiEntails emp and := ⟨emp_and⟩

theorem and_emp [BI PROP] {P : PROP} [Affine P] : P ∧ emp ⊣⊢ P := and_comm.trans emp_and
instance [BI PROP] [BIAffine PROP] : RightId (α := PROP) BiEntails emp and := ⟨and_emp⟩

theorem emp_or [BI PROP] {P : PROP} [Affine P] : emp ∨ P ⊣⊢ emp := ⟨or_elim .rfl affine, or_intro_l⟩

theorem or_emp [BI PROP] {P : PROP} [Affine P] : P ∨ emp ⊣⊢ emp := or_comm.trans emp_or

theorem true_emp [BI PROP] [h : BIAffine PROP] : (True : PROP) ⊣⊢ emp :=
  ⟨biaffine_iff_true_emp.1 h, true_intro⟩

instance [BI PROP] [BIAffine PROP] (P : PROP) : Absorbing P where
  absorbing := (sep_mono_l affine).trans emp_sep.1

theorem true_sep [BI PROP] {P : PROP} [Absorbing P] : True ∗ P ⊣⊢ P := ⟨absorbing, true_sep_2⟩
instance [BI PROP] [BIAffine PROP] : LeftId (α := PROP) BiEntails iprop(True) sep := ⟨true_sep⟩

theorem sep_true [BI PROP] {P : PROP} [Absorbing P] : P ∗ True ⊣⊢ P := sep_comm.trans true_sep
instance [BI PROP] [BIAffine PROP] : RightId (α := PROP) BiEntails iprop(True) sep := ⟨sep_true⟩

instance [BI PROP] [BIAffine PROP] : BIPositive PROP where
  affinely_sep_l := (affine_affinely _).1.trans (sep_mono_l (affine_affinely _).2)

theorem imp_wand_1 [BI PROP] [BIAffine PROP] {P Q : PROP} : (P → Q) ⊢ P -∗ Q :=
  wand_intro <| sep_and.trans imp_elim_l

theorem pure_sep [BI PROP] {φ1 φ2 : Prop} : ⌜φ1⌝ ∗ (⌜φ2⌝ : PROP) ⊣⊢ ⌜φ1 ∧ φ2⌝ :=
  ⟨sep_and.trans pure_and.1, pure_elim' fun ⟨a, b⟩ => by
    rw [eq_true a, eq_true b]; exact true_sep_2⟩

theorem pure_wand_2 [BI PROP] {φ1 φ2 : Prop} : ⌜φ1 → φ2⌝ ⊢ (⌜φ1⌝ -∗ (⌜φ2⌝ : PROP)) :=
  pure_elim' fun a => wand_intro <| absorbing.trans (pure_mono a)

theorem pure_wand [BI PROP] {φ1 φ2 : Prop} : (⌜φ1⌝ -∗ (⌜φ2⌝ : PROP)) ⊣⊢ ⌜φ1 → φ2⌝ := by
  refine ⟨(imp_intro' ?_).trans pure_imp.1, pure_wand_2⟩
  exact pure_elim_l fun h => true_sep_2.trans (eq_true h ▸ wand_elim_r)

/-! # Properties of the persistence modality -/

@[rw_mono_rule]
theorem persistently_congr [BI PROP] {P P' : PROP} (h : P ⊣⊢ P') :
    <pers> P ⊣⊢ <pers> P' := ⟨persistently_mono h.1, persistently_mono h.2⟩

instance persistently_persistent [BI PROP] (P : PROP) : Persistent iprop(<pers> P) where
  persistent := persistently_idem_2

theorem persistently_absorb_r [BI PROP] {P Q : PROP} : P ∗ <pers> Q ⊢ <pers> Q :=
  sep_comm.1.trans persistently_absorb_l

theorem absorbingly_persistently [BI PROP] {P : PROP} : <absorb> <pers> P ⊣⊢ <pers> P :=
  ⟨persistently_absorb_r, absorbingly_intro⟩

instance persistently_absorbing [BI PROP] (P : PROP) : Absorbing iprop(<pers> P) where
  absorbing := absorbingly_persistently.1

theorem persistently_forall_1 [BI PROP] {Ψ : α → PROP} : <pers> (∀ a, Ψ a) ⊢ ∀ a, <pers> (Ψ a) :=
  forall_intro fun x => persistently_mono (forall_elim x)

theorem persistently_forall [BI PROP] [h : BIPersistentlyForall PROP] {Ψ : α → PROP} :
    <pers> (∀ a, Ψ a) ⊣⊢ ∀ a, <pers> (Ψ a) := by
  refine ⟨persistently_forall_1, (forall_intro fun _ => imp_intro <| pure_elim_r ?_).trans (h.1 _)⟩
  rintro ⟨_, rfl⟩; apply forall_elim

theorem persistently_exists [BI PROP] {Ψ : α → PROP} : <pers> (∃ a, Ψ a) ⊣⊢ ∃ a, <pers> (Ψ a) := by
  refine ⟨persistently_sExists_1.trans ?_, exists_elim fun a => persistently_mono (exists_intro a)⟩
  refine exists_elim fun _ => pure_elim_l fun ⟨_, eq⟩ => eq ▸ sExists_intro ⟨_, rfl⟩

theorem persistently_and [BI PROP] {P Q : PROP} : <pers> (P ∧ Q) ⊣⊢ <pers> P ∧ <pers> Q :=
  ⟨and_intro (persistently_mono and_elim_l) (persistently_mono and_elim_r), persistently_and_2⟩

theorem persistently_ite {p : Bool} [BI PROP] {P Q : PROP} :
    iprop(<pers> if p then P else Q) = iprop(if p then <pers> P else <pers> Q) := by
  cases p <;> simp

theorem persistently_or [BI PROP] {P Q : PROP} : <pers> (P ∨ Q) ⊣⊢ <pers> P ∨ <pers> Q :=
  (persistently_congr or_eq_ite).trans <| persistently_exists.trans <|
    (or_eq_ite.trans <| exists_congr fun _ => persistently_ite (PROP := PROP) ▸ .rfl).symm

theorem persistently_imp_1 [BI PROP] {P Q : PROP} : <pers> (P → Q) ⊢ (<pers> P → <pers> Q) :=
  imp_intro <| persistently_and.2.trans (persistently_mono imp_elim_l)

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

theorem persistently_intro' [BI PROP] {P Q : PROP} (h : <pers> P ⊢ Q) : <pers> P ⊢ <pers> Q :=
 persistently_idem.2.trans (persistently_mono h)

theorem persistently_pure {φ : Prop} [BI PROP] : <pers> ⌜φ⌝ ⊣⊢ (⌜φ⌝ : PROP) :=
  ⟨absorbingly_of_persistently.trans absorbingly_pure.1,
   pure_elim' fun h => persistently_true.2.trans <| persistently_mono <| pure_intro h⟩

theorem persistently_and_imp_sep [BI PROP] {P Q : PROP} : <pers> P ∧ Q ⊢ <pers> P ∗ Q :=
  (and_mono_r emp_sep.2).trans <| persistently_and_sep_assoc.1.trans <| sep_mono_l and_elim_l

theorem and_persistently_imp_sep [BI PROP] {P Q : PROP} : P ∧ <pers> Q ⊢ P ∗ <pers> Q :=
  and_symm.trans <| persistently_and_imp_sep.trans sep_symm

theorem persistently_sep_persistently [BI PROP] {P : PROP} : <pers> P ∗ <pers> P ⊣⊢ <pers> P :=
  ⟨sep_elim_r, and_self.2.trans persistently_and_imp_sep⟩

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

theorem persistently_sep [BI PROP] [BIPositive PROP] {P Q : PROP} :
    <pers> (P ∗ Q) ⊣⊢ <pers> P ∗ <pers> Q := by
  refine ⟨persistently_affinely.2.trans ?_, persistently_sep_2⟩
  refine persistently_mono affinely_sep.1 |>.trans ?_ |>.trans persistently_and_persistently_sep.1
  exact and_intro
    (persistently_mono <| (sep_mono_r affinely_elim_emp).trans <| sep_emp.1.trans affinely_elim)
    (persistently_mono <| (sep_mono_l affinely_elim_emp).trans <| emp_sep.1.trans affinely_elim)

theorem self_sep_persistently [BI PROP] {P : PROP} : P ∗ <pers> P ⊣⊢ <pers> P :=
  ⟨sep_elim_r, and_self.2.trans persistently_and_l⟩

theorem affinely_sep_persistently [BI PROP] {P : PROP} : <affine> P ∗ <pers> P ⊣⊢ <pers> P :=
  (sep_congr_r persistently_affinely.symm).trans <|
  self_sep_persistently.trans persistently_affinely

theorem persistently_wand_1 [BI PROP] {P Q : PROP} : <pers> (P -∗ Q) ⊢ (<pers> P -∗ <pers> Q) :=
  wand_intro <| persistently_sep_2.trans <| persistently_mono wand_elim_l

theorem persistently_entails_l [BI PROP] {P Q : PROP} (h : P ⊢ <pers> Q) : P ⊢ <pers> Q ∗ P :=
  (and_intro h .rfl).trans persistently_and_imp_sep

theorem persistently_entails_r [BI PROP] {P Q : PROP} (h : P ⊢ <pers> Q) : P ⊢ P ∗ <pers> Q :=
  (persistently_entails_l h).trans sep_symm

theorem persistently_imp_wand_2 [BI PROP] {P Q : PROP} : <pers> (P -∗ Q) ⊢ <pers> (P → Q) :=
  persistently_intro' <| imp_intro <| persistently_and_affinely_sep.trans <|
  (sep_mono_l affinely_elim).trans wand_elim_l

theorem imp_wand_persistently_2 [BI PROP] {P Q : PROP} : (<pers> P -∗ Q) ⊢ (<pers> P → Q) :=
  imp_intro <| and_persistently_imp_sep.trans wand_elim_l

theorem persistently_emp' [BI PROP] [BIAffine PROP] : <pers> (emp : PROP) ⊣⊢ emp :=
  persistently_emp.trans true_emp

theorem persistently_and_iff_sep [BI PROP] [BIAffine PROP] {P Q : PROP} :
    <pers> P ∧ Q ⊣⊢ <pers> P ∗ Q := ⟨persistently_and_imp_sep, sep_and⟩

theorem and_persistently_iff_sep [BI PROP] [BIAffine PROP] {P Q : PROP} :
    P ∧ <pers> Q ⊣⊢ P ∗ <pers> Q := ⟨and_persistently_imp_sep, sep_and⟩

theorem persistently_imp_wand [BI PROP] [BIAffine PROP] {P Q : PROP} :
    <pers> (P → Q) ⊣⊢ <pers> (P -∗ Q) := by
  refine ⟨persistently_intro' (wand_intro ?_), persistently_imp_wand_2⟩
  exact persistently_and_iff_sep.2.trans <| (and_mono_l persistently_elim).trans imp_elim_l

theorem imp_wand_persistently [BI PROP] [BIAffine PROP] {P Q : PROP} :
    (<pers> P → Q) ⊣⊢ (<pers> P -∗ Q) := ⟨imp_wand_1, imp_wand_persistently_2⟩

theorem wand_iff_exists_persistently [BI PROP] [BIAffine PROP] {P Q : PROP} :
    (P -∗ Q) ⊣⊢ ∃ R, R ∗ <pers> (P ∗ R → Q) := by
  constructor
  · refine (sep_true.2.trans ?_).trans (exists_intro iprop(P -∗ Q))
    exact sep_mono_r <| persistently_pure.2.trans <| persistently_intro' <|
      imp_intro <| (and_mono persistently_pure.1 wand_elim_r).trans and_elim_r
  · exact exists_elim fun R => wand_intro' <| sep_assoc.2.trans <|
      and_persistently_iff_sep.2.trans <| (and_mono_r persistently_elim).trans imp_elim_r

theorem persistently_and_emp {P : PROP} [BI PROP] : <pers> P ⊣⊢ <pers> (emp ∧ P) :=
  ⟨(and_intro persistently_emp_intro .rfl).trans persistently_and.2,
   (persistently_mono and_elim_r).trans .rfl⟩

theorem persistently_and_sep_elim_emp {P Q : PROP} [BI PROP] : <pers> P ∧ Q ⊢ (emp ∧ P) ∗ Q :=
  (and_mono persistently_and_emp.1 BIBase.Entails.rfl).trans persistently_and_l

theorem persistently_and_emp_elim {P : PROP} [BI PROP] : emp ∧ <pers> P ⊢ P :=
  and_comm.1.trans <| persistently_and_sep_elim_emp.trans <| sep_emp.1.trans and_elim_r

/-! # Persistence instances -/

instance pure_persistent (φ : Prop) [BI PROP] : Persistent (PROP := PROP) iprop(⌜φ⌝) where
  persistent := persistently_pure.2

instance emp_persistent [BI PROP] : Persistent (PROP := PROP) iprop(emp) where
  persistent := persistently_emp_intro

instance and_persistent [BI PROP] (P Q : PROP) [Persistent P] [Persistent Q] :
    Persistent iprop(P ∧ Q) where
  persistent := (and_mono persistent persistent).trans persistently_and.2

instance or_persistent [BI PROP] (P Q : PROP) [Persistent P] [Persistent Q] :
    Persistent iprop(P ∨ Q) where
  persistent := (or_mono persistent persistent).trans persistently_or.2

theorem sForall_persistent [BI PROP] [h : BIPersistentlyForall PROP] (Ψ : PROP → Prop)
    (H : ∀ p, Ψ p → Persistent p) : Persistent iprop(sForall Ψ) where
  persistent := by
    refine (forall_intro fun _ => imp_intro ?_).trans (h.1 _)
    exact pure_elim_r fun h => (sForall_elim h).trans (H _ h).1

instance forall_persistent [BI PROP] [BIPersistentlyForall PROP] (Ψ : α → PROP)
    [h : ∀ x, Persistent (Ψ x)] : Persistent iprop(∀ x, Ψ x) :=
  sForall_persistent _ fun _ ⟨_, eq⟩ => eq ▸ h _

theorem sExists_persistent [BI PROP] (Ψ : PROP → Prop)
    (H : ∀ p, Ψ p → Persistent p) : Persistent iprop(sExists Ψ) where
  persistent := sExists_elim fun _ hp => (H _ hp).1.trans (persistently_mono <| sExists_intro hp)

instance exists_persistent [BI PROP] (Ψ : α → PROP) [h : ∀ x, Persistent (Ψ x)] :
    Persistent iprop(∃ x, Ψ x) := sExists_persistent _ fun _ ⟨_, eq⟩ => eq ▸ h _

instance sep_persistent [BI PROP] (P Q : PROP) [Persistent P] [Persistent Q] :
    Persistent iprop(P ∗ Q) where
  persistent := (sep_mono persistent persistent).trans persistently_sep_2

instance affinely_persistent [BI PROP] (P : PROP) [Persistent P] : Persistent iprop(<affine> P) :=
  inferInstanceAs (Persistent iprop(_ ∧ _))

instance absorbingly_persistent [BI PROP] (P : PROP) [Persistent P] :
    Persistent iprop(<absorb> P) :=
  inferInstanceAs (Persistent iprop(_ ∗ _))

/-! # The intuitionistic modality -/

theorem intuitionistically_ne [BI PROP] : OFE.NonExpansive (@intuitionistically PROP _) where
  ne _ _ _ h := affinely_ne.1 (persistently_ne.1 h)

@[rw_mono_rule]
theorem intuitionistically_congr [BI PROP] {P Q : PROP} (h : P ⊣⊢ Q) : □ P ⊣⊢ □ Q :=
  affinely_congr <| persistently_congr h

@[rw_mono_rule]
theorem intuitionistically_mono [BI PROP] {P Q : PROP} (h : P ⊢ Q) : □ P ⊢ □ Q :=
  affinely_mono <| persistently_mono h

instance intuitionistically_affine [BI PROP] (P : PROP) : Affine iprop(□ P) :=
  inferInstanceAs (Affine iprop(<affine> _))

instance intuitionistically_persistent [BI PROP] (P : PROP) : Persistent iprop(□ P) :=
  inferInstanceAs (Persistent iprop(<affine> _))

theorem intuitionistically_def [BI PROP] {P : PROP} : iprop(□ P) = iprop(<affine> <pers> P) := rfl

theorem intuitionistically_elim_emp [BI PROP] {P : PROP} : □ P ⊢ emp := affinely_elim_emp

theorem intuitionistically_emp [BI PROP] : □ emp ⊣⊢ (emp : PROP) :=
  (affinely_congr persistently_emp).trans affinely_true

theorem intuitionistically_false [BI PROP] : □ False ⊣⊢ (False : PROP) :=
  (affinely_congr persistently_pure).trans affinely_false

theorem intuitionistically_true [BI PROP] : □ True ⊣⊢ (emp : PROP) :=
  (affinely_congr persistently_true).trans affinely_true

theorem intuitionistically_and [BI PROP] {P Q : PROP} : □ (P ∧ Q) ⊣⊢ □ P ∧ □ Q :=
  (affinely_congr persistently_and).trans affinely_and

theorem intuitionistically_forall_1 [BI PROP] {Φ : α → PROP} : □ (∀ x, Φ x) ⊢ ∀ x, □ Φ x :=
  (affinely_mono persistently_forall_1).trans affinely_forall_1

theorem intuitionistically_or [BI PROP] {P Q : PROP} : □ (P ∨ Q) ⊣⊢ □ P ∨ □ Q :=
  (affinely_congr persistently_or).trans affinely_or

theorem intuitionistically_exists [BI PROP] {Φ : α → PROP} : □ (∃ x, Φ x) ⊣⊢ ∃ x, □ Φ x :=
  (affinely_congr persistently_exists).trans affinely_exists

theorem intuitionistically_sep_2 [BI PROP] {P Q : PROP} : □ P ∗ □ Q ⊢ □ (P ∗ Q) :=
  affinely_sep_2.trans (affinely_mono persistently_sep_2)

theorem intuitionistically_sep [BI PROP] [BIPositive PROP] {P Q : PROP} : □ (P ∗ Q) ⊣⊢ □ P ∗ □ Q :=
  (affinely_congr persistently_sep).trans affinely_sep

theorem intuitionistically_idem [BI PROP] {P : PROP} : □ □ P ⊣⊢ □ P :=
  (affinely_congr persistently_affinely).trans (affinely_congr persistently_idem)

theorem intuitionistically_intro' [BI PROP] {P Q : PROP} (h : □ P ⊢ Q) : □ P ⊢ □ Q :=
  intuitionistically_idem.2.trans (intuitionistically_mono h)

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

theorem intuitionistically_wand [BI PROP] {P Q : PROP} : (□ P -∗ Q) ⊣⊢ (<pers> P → Q) :=
  ⟨imp_intro <| persistently_and_intuitionistically_sep_r.1.trans wand_elim_l,
   wand_intro <|persistently_and_intuitionistically_sep_r.2.trans imp_elim_l⟩

theorem affinely_self_sep_intuitionistically [BI PROP] {P : PROP} :
    <affine> (P ∗ □ P) ⊣⊢ □ P :=
  ⟨affinely_mono <| (sep_mono_r persistently_of_intuitionistically).trans self_sep_persistently.1,
   and_intro affinely_elim_emp <|
   intuitionistically_sep_idem.2.trans <| sep_mono_l intuitionistically_elim⟩

theorem intuitionistically_imp_wand_2 [BI PROP] {P Q : PROP} : □ (P -∗ Q) ⊢ □ (P → Q) :=
  affinely_mono persistently_imp_wand_2

theorem imp_iff_exists_persistently [BI PROP] [BIAffine PROP] {P Q : PROP} :
    (P → Q) ⊣⊢ ∃ R, R ∧ <pers> (P ∧ R -∗ Q) := by
  constructor
  · refine (and_true.2.trans ?_).trans (exists_intro iprop(P → Q))
    exact and_mono_r <| persistently_emp.2.trans <| persistently_mono <|
      wand_intro <| emp_sep.1.trans imp_elim_r
  · exact exists_elim fun R => imp_intro' <| and_assoc.2.trans <|
      persistently_and_intuitionistically_sep_r.1.trans <|
      (sep_mono_r intuitionistically_elim).trans wand_elim_r

theorem intuitionistically_iff_persistently [BI PROP] [BIAffine PROP]
    {P : PROP} : □ P ⊣⊢ <pers> P := affine_affinely _

/-! # Conditional affinely modality -/

@[simp] theorem affinelyIf_false [BI PROP] (P : PROP) : iprop(<affine>?false P) = P := rfl
@[simp] theorem affinelyIf_true [BI PROP] (P : PROP) :
    iprop(<affine>?true P) = iprop(<affine> P) := rfl

theorem affinelyIf_ne {p : Bool} [BI PROP] : OFE.NonExpansive (affinelyIf (PROP := PROP) p) :=
  match p with
  | true => affinely_ne
  | false => OFE.id_ne

@[rw_mono_rule]
theorem affinelyIf_mono {p : Bool} [BI PROP] {P Q : PROP}
    (h : P ⊢ Q) : <affine>?p P ⊢ <affine>?p Q :=
  match p with
  | true => affinely_mono h
  | false => h

@[rw_mono_rule]
theorem affinelyIf_congr {p : Bool} [BI PROP] {P Q : PROP} (h : P ⊣⊢ Q) :
    <affine>?p P ⊣⊢ <affine>?p Q :=
  ⟨affinelyIf_mono h.1, affinelyIf_mono h.2⟩

instance affinelyIf_affine (p : Bool) [BI PROP] (P : PROP) [Affine P] :
    Affine iprop(<affine>?p P) := by
  cases p <;> simp [affinelyIf] <;> infer_instance

instance affinelyIf_persistent (p : Bool) [BI PROP] (P : PROP) [Persistent P] :
    Persistent iprop(<affine>?p P) := by
  cases p <;> simp [affinelyIf] <;> infer_instance

theorem affinelyIf_flag_mono {p q : Bool} [BI PROP] {P : PROP} (h : q → p) :
    <affine>?p P ⊢ <affine>?q P :=
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

theorem affinelyIf_intro' {p : Bool} [BI PROP] {P Q : PROP} :
    (P ⊢ <affine>?p Q) → <affine>?p P ⊢ <affine>?p Q :=
  match p with
  | true => affinely_intro'
  | false => id

theorem affinelyIf_emp {p : Bool} [BI PROP] : (<affine>?p emp : PROP) ⊣⊢ emp :=
  match p with
  | false => .rfl
  | true => affinely_emp

theorem affinelyIf_and {p : Bool} [BI PROP] {P Q : PROP} :
    <affine>?p (P ∧ Q) ⊣⊢ <affine>?p P ∧ <affine>?p Q :=
  match p with
  | false => .rfl
  | true => affinely_and

theorem affinelyIf_or {p : Bool} [BI PROP] {P Q : PROP} :
    <affine>?p (P ∨ Q) ⊣⊢ <affine>?p P ∨ <affine>?p Q :=
  match p with
  | false => .rfl
  | true => affinely_or

theorem affinelyIf_exists {p : Bool} [BI PROP] {Ψ : α → PROP} :
    <affine>?p (∃ a, Ψ a) ⊣⊢ ∃ a, <affine>?p (Ψ a) :=
  match p with
  | false => .rfl
  | true => affinely_exists

theorem affinelyIf_forall_1 {p : Bool} [BI PROP] {Ψ : α → PROP} :
    <affine>?p (∀ a, Ψ a) ⊢ ∀ a, <affine>?p (Ψ a) :=
  match p with
  | false => .rfl
  | true => affinely_forall_1

theorem affinelyIf_sep_2 {p : Bool} [BI PROP] {P Q : PROP} :
    <affine>?p P ∗ <affine>?p Q ⊢ <affine>?p (P ∗ Q) :=
  match p with
  | false => .rfl
  | true => affinely_sep_2

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

theorem affinelyIf_and_l {p : Bool} [BI PROP] {P Q : PROP} :
    <affine>?p P ∧ Q ⊣⊢ <affine>?p (P ∧ Q) :=
  match p with
  | false => .rfl
  | true => affinely_and_l

theorem affinelyIf_and_r {p : Bool} [BI PROP] {P Q : PROP} :
    P ∧ <affine>?p Q ⊣⊢ <affine>?p (P ∧ Q) :=
  match p with
  | false => .rfl
  | true => affinely_and_r

theorem affinelyIf_and_lr {p : Bool} [BI PROP] {P Q : PROP} :
    <affine>?p P ∧ Q ⊣⊢ P ∧ <affine>?p Q :=
  affinelyIf_and_l.trans affinelyIf_and_r.symm

/-! # Conditional absorbingly modality -/

@[simp] theorem absorbinglyIf_false [BI PROP] (P : PROP) : iprop(<absorb>?false P) = P := rfl
@[simp] theorem absorbinglyIf_true [BI PROP] (P : PROP) :
    iprop(<absorb>?true P) = iprop(<absorb> P) := rfl

theorem absorbinglyIf_ne {p : Bool} [BI PROP] : OFE.NonExpansive (absorbinglyIf (PROP := PROP) p) :=
  match p with
  | true => absorbingly_ne
  | false => OFE.id_ne

@[rw_mono_rule]
theorem absorbinglyIf_mono {p : Bool} [BI PROP] {P Q : PROP} (h : P ⊢ Q) :
    <absorb>?p P ⊢ <absorb>?p Q :=
  match p with
  | false => h
  | true => absorbingly_mono h

@[rw_mono_rule]
theorem absorbinglyIf_congr {p : Bool} [BI PROP] {P Q : PROP} (h : P ⊣⊢ Q) :
    <absorb>?p P ⊣⊢ <absorb>?p Q :=
  ⟨absorbinglyIf_mono h.1, absorbinglyIf_mono h.2⟩

instance absorbinglyIf_persistent (p : Bool) [BI PROP] (P : PROP) [Persistent P] :
    Persistent iprop(<absorb>?p P) := by
  cases p <;> simp [absorbinglyIf] <;> infer_instance

theorem absorbingly_of_absorbinglyIf {p : Bool} [BI PROP] {P : PROP} : <absorb>?p P ⊢ <absorb> P :=
  match p with
  | false => absorbingly_intro
  | true => .rfl

theorem absorbinglyIf_intro {p : Bool} [BI PROP] {P : PROP} : P ⊢ <absorb>?p P :=
  match p with
  | false => .rfl
  | true => absorbingly_intro

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

theorem absorbinglyIf_pure {p : Bool} [BI PROP] {φ : Prop} : (<absorb>?p ⌜φ⌝ : PROP) ⊣⊢ ⌜φ⌝ :=
  match p with
  | false => .rfl
  | true => absorbingly_pure

theorem absorbinglyIf_or {p : Bool} [BI PROP] {P Q : PROP} :
    <absorb>?p (P ∨ Q) ⊣⊢ <absorb>?p P ∨ <absorb>?p Q :=
  match p with
  | false => .rfl
  | true => absorbingly_or

theorem absorbinglyIf_and_1 {p : Bool} [BI PROP] {P Q : PROP} :
    <absorb>?p (P ∧ Q) ⊢ <absorb>?p P ∧ <absorb>?p Q :=
  match p with
  | false => .rfl
  | true => absorbingly_and_1

theorem absorbinglyIf_forall_1 {p : Bool} [BI PROP] {Φ : α → PROP} :
    <absorb>?p (∀ a, Φ a) ⊢ ∀ a, <absorb>?p (Φ a) :=
  match p with
  | false => .rfl
  | true => absorbingly_forall_1

theorem absorbinglyIf_exists {p : Bool} [BI PROP] {Φ : α → PROP} :
    <absorb>?p (∃ a, Φ a) ⊣⊢ ∃ a, <absorb>?p (Φ a) :=
  match p with
  | false => .rfl
  | true => absorbingly_exists

theorem absorbinglyIf_sep {p : Bool} [BI PROP] {P Q : PROP} :
    <absorb>?p (P ∗ Q) ⊣⊢ <absorb>?p P ∗ <absorb>?p Q :=
  match p with
  | false => .rfl
  | true => absorbingly_sep

theorem absorbinglyIf_wand_1 {p : Bool} [BI PROP] {P Q : PROP} :
    <absorb>?p (P -∗ Q) ⊢ (<absorb>?p P -∗ <absorb>?p Q) :=
  match p with
  | false => .rfl
  | true => absorbingly_wand_1

theorem absorbinglyIf_sep_l {p : Bool} [BI PROP] {P Q : PROP} :
    <absorb>?p P ∗ Q ⊣⊢ <absorb>?p (P ∗ Q) :=
  match p with
  | false => .rfl
  | true => absorbingly_sep_l

theorem absorbinglyIf_sep_r {p : Bool} [BI PROP] {P Q : PROP} :
    P ∗ <absorb>?p Q ⊣⊢ <absorb>?p (P ∗ Q) :=
  match p with
  | false => .rfl
  | true => absorbingly_sep_r

theorem absorbinglyIf_sep_lr {p : Bool} [BI PROP] {P Q : PROP} :
    <absorb>?p P ∗ Q ⊣⊢ P ∗ <absorb>?p Q :=
  absorbinglyIf_sep_l.trans absorbinglyIf_sep_r.symm

theorem affinelyIf_absorbinglyIf {p : Bool} [BI PROP] [BIPositive PROP] {P : PROP} :
    <affine>?p <absorb>?p P ⊣⊢ <affine>?p P :=
  match p with
  | false => .rfl
  | true => affinely_absorbingly

/-! # Conditional persistently -/

@[simp] theorem persistentlyIf_false [BI PROP] (P : PROP) : iprop(<pers>?false P) = P := rfl
@[simp] theorem persistentlyIf_true [BI PROP] (P : PROP) :
    iprop(<pers>?true P) = iprop(<pers> P) := rfl

theorem persistentlyIf_ne {p : Bool} [BI PROP] :
    OFE.NonExpansive (persistentlyIf (PROP := PROP) p) :=
  match p with
  | true => persistently_ne
  | false => OFE.id_ne

@[rw_mono_rule]
theorem persistentlyIf_mono {p : Bool} [BI PROP] {P Q : PROP} (h : P ⊢ Q) :
    <pers>?p P ⊢ <pers>?p Q :=
  match p with
  | false => h
  | true => persistently_mono h

@[rw_mono_rule]
theorem persistentlyIf_congr {p : Bool} [BI PROP] {P Q : PROP} (h : P ⊣⊢ Q) :
    <pers>?p P ⊣⊢ <pers>?p Q :=
  ⟨persistentlyIf_mono h.1, persistentlyIf_mono h.2⟩

instance persistentlyIf_absorbing [BI PROP] (P : PROP) (p : Bool) [Absorbing P] :
    Absorbing iprop(<pers>?p P) := by
  cases p <;> simp [persistentlyIf] <;> infer_instance

theorem persistentlyIf_pure {p : Bool} [BI PROP] {φ : Prop} : (<pers>?p ⌜φ⌝ : PROP) ⊣⊢ ⌜φ⌝ :=
  match p with
  | false => .rfl
  | true => persistently_pure

theorem persistentlyIf_and {p : Bool} [BI PROP] {P Q : PROP} :
    <pers>?p (P ∧ Q) ⊣⊢ <pers>?p P ∧ <pers>?p Q :=
  match p with
  | false => .rfl
  | true => persistently_and

theorem persistentlyIf_or {p : Bool} [BI PROP] {P Q : PROP} :
    <pers>?p (P ∨ Q) ⊣⊢ <pers>?p P ∨ <pers>?p Q :=
  match p with
  | false => .rfl
  | true => persistently_or

theorem persistentlyIf_forall_1 {p : Bool} [BI PROP] {Φ : α → PROP} :
    <pers>?p (∀ a, Φ a) ⊢ ∀ a, <pers>?p (Φ a) :=
  match p with
  | false => .rfl
  | true => persistently_forall_1

theorem persistentlyIf_exists {p : Bool} [BI PROP] {Φ : α → PROP} :
    <pers>?p (∃ a, Φ a) ⊣⊢ ∃ a, <pers>?p (Φ a) :=
  match p with
  | false => .rfl
  | true => persistently_exists

theorem persistentlyIf_sep_2 {p : Bool} [BI PROP] {P Q : PROP} :
    <pers>?p P ∗ <pers>?p Q ⊢ <pers>?p (P ∗ Q) :=
  match p with
  | false => .rfl
  | true => persistently_sep_2

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

theorem intuitionisticallyIf_ne {p : Bool} [BI PROP] :
    OFE.NonExpansive (intuitionisticallyIf (PROP := PROP) p) :=
  match p with
  | true => intuitionistically_ne
  | false => OFE.id_ne

@[rw_mono_rule]
theorem intuitionisticallyIf_mono {p : Bool} [BI PROP] {P Q : PROP} (h : P ⊢ Q) : □?p P ⊢ □?p Q :=
  match p with
  | false => h
  | true => intuitionistically_mono h

@[rw_mono_rule]
theorem intuitionisticallyIf_congr {p : Bool} [BI PROP] {P Q : PROP}
    (h : P ⊣⊢ Q) : □?p P ⊣⊢ □?p Q :=
  ⟨intuitionisticallyIf_mono h.1, intuitionisticallyIf_mono h.2⟩

instance intuitionisticallyIf_affine (p : Bool) [BI PROP] (P : PROP) [Affine P] :
    Affine iprop(□?p P) := by
  cases p <;> simp [intuitionisticallyIf] <;> infer_instance

theorem intuitionisticallyIf_flag_mono {p q : Bool} [BI PROP] {P : PROP} (h : q → p) :
    □?p P ⊢ □?q P :=
  match p, q with
  | true, true | false, false => .rfl
  | true, false => intuitionistically_elim
  | false, true => nomatch h rfl

theorem intuitionisticallyIf_elim {p : Bool} [BI PROP] {P : PROP} : □?p P ⊢ P :=
  match p with
  | false => .rfl
  | true => intuitionistically_elim

theorem intuitionisticallyIf_of_intuitionistically (p : Bool) [BI PROP] {P : PROP} : □ P ⊢ □?p P :=
  match p with
  | true => .rfl
  | false => intuitionistically_elim

theorem intuitionisticallyIf_intro' {p : Bool} [BI PROP] {P Q : PROP} :
    (□?p P ⊢ Q) → □?p P ⊢ □?p Q :=
  match p with
  | true => intuitionistically_intro'
  | false => id

theorem intuitionisticallyIf_emp {p : Bool} [BI PROP] : (□?p emp : PROP) ⊣⊢ emp :=
  match p with
  | false => .rfl
  | true => intuitionistically_emp

theorem intuitionisticallyIf_false {p : Bool} [BI PROP] : (□?p False : PROP) ⊣⊢ False :=
  match p with
  | false => .rfl
  | true => intuitionistically_false

theorem intuitionisticallyIf_and {p : Bool} [BI PROP] {P Q : PROP} : □?p (P ∧ Q) ⊣⊢ □?p P ∧ □?p Q :=
  match p with
  | false => .rfl
  | true => intuitionistically_and

theorem intuitionisticallyIf_or (p : Bool) [BI PROP] {P Q : PROP} : □?p (P ∨ Q) ⊣⊢ □?p P ∨ □?p Q :=
  match p with
  | false => .rfl
  | true => intuitionistically_or

theorem intuitionisticallyIf_exists {p : Bool} [BI PROP] {Ψ : α → PROP} :
    (□?p ∃ a, Ψ a) ⊣⊢ ∃ a, □?p Ψ a :=
  match p with
  | false => .rfl
  | true => intuitionistically_exists

theorem intuitionisticallyIf_sep_2 {p : Bool} [BI PROP] {P Q : PROP} :
    □?p P ∗ □?p Q ⊢ □?p (P ∗ Q) :=
  match p with
  | false => .rfl
  | true => intuitionistically_sep_2

theorem intuitionisticallyIf_sep {p : Bool} [BI PROP] [BIPositive PROP] {P Q : PROP} :
    □?p (P ∗ Q) ⊣⊢ □?p P ∗ □?p Q :=
  match p with
  | false => .rfl
  | true => intuitionistically_sep

theorem intuitionisticallyIf_idem {p : Bool} [BI PROP] {P : PROP} : □?p □?p P ⊣⊢ □?p P :=
  match p with
  | false => .rfl
  | true => intuitionistically_idem

theorem intuitionisticallyIf_def' {p : Bool} [BI PROP] {P : PROP} :
    iprop(□?p P) = iprop(<affine>?p <pers>?p P) := by cases p <;> rfl

theorem intuitionisticallyIf_comm {p q : Bool} [BI PROP] {P : PROP} :
    iprop(□?p □?q P) = iprop(□?q □?p P) := by cases p <;> cases q <;> rfl

theorem intuitionisticallyIf_comm' {p q : Bool} [BI PROP] {P : PROP} :
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

/-! # Properties of persistent propositions -/

theorem persistent_congr [BI PROP] {P Q : PROP} (H : P ⊣⊢ Q) : Persistent P ↔ Persistent Q :=
  ⟨fun ⟨h⟩ => ⟨H.2.trans <| h.trans (persistently_mono H.1)⟩,
   fun ⟨h⟩ => ⟨H.1.trans <| h.trans (persistently_mono H.2)⟩⟩

theorem persistently_intro [BI PROP] {P : PROP} [Persistent P] : P ⊢ <pers> P := persistent

theorem persistently_iff [BI PROP] {P : PROP} [Persistent P] [Absorbing P] :
    <pers> P ⊣⊢ P := ⟨persistently_elim, persistent⟩

theorem persistently_intro'' [BI PROP] {P : PROP} [Persistent P] (h : P ⊢ Q) : P ⊢ <pers> Q :=
  persistent.trans (persistently_mono h)

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

theorem persistent_entails_r [BI PROP] {P Q : PROP} [Persistent Q] (H : P ⊢ Q) : P ⊢ Q ∗ P :=
  (and_intro H .rfl).trans persistent_and_sep_1

theorem persistent_entails_l [BI PROP] {P Q : PROP} [Persistent Q] (H : P ⊢ Q) : P ⊢ P ∗ Q :=
  (and_intro .rfl H).trans persistent_and_sep_1

theorem absorbingly_intuitionistically [BI PROP] {P : PROP} : <absorb> □ P ⊣⊢ <pers> P :=
  ⟨(absorbingly_mono persistently_of_intuitionistically).trans absorbingly_persistently.1,
   and_self.2.trans <| persistently_and_intuitionistically_sep_r.1.trans <| sep_mono_l true_intro⟩

theorem absorbingly_affinely_intro_of_persistent [BI PROP] {P : PROP} [Persistent P] :
    P ⊢ <absorb> <affine> P :=
  persistent.trans <| absorbingly_intuitionistically.2.trans <|
  absorbingly_mono affinely_of_intuitionistically

instance imp_absorbing [BI PROP] (P Q : PROP) [Persistent P] [Absorbing P] [Absorbing Q] :
    Absorbing iprop(P → Q) where
  absorbing := imp_intro' <| persistent_and_affinely_sep_l.1.trans <| absorbingly_sep_r.1.trans <|
    (absorbingly_mono <| persistent_and_affinely_sep_l.2.trans imp_elim_r).trans absorbing

theorem bigOp_sep_nil [BI PROP] : iprop([∗] []) ⊣⊢ (emp : PROP) := .rfl

theorem bigOp_and_nil [BI PROP] : iprop([∧] []) ⊣⊢ (True : PROP) := .rfl

theorem bigOp_sep_cons [BI PROP] {P : PROP} {Ps : List PROP} :
    [∗] (P :: Ps) ⊣⊢ P ∗ [∗] Ps := bigOp_cons

theorem bigOp_and_cons [BI PROP] {P : PROP} {Ps : List PROP} :
    [∧] (P :: Ps) ⊣⊢ P ∧ [∧] Ps := bigOp_cons
