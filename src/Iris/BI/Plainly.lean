/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Fernando Leal
-/
module

public import Iris.Algebra
public import Iris.BI.Sbi
public import Iris.BI.Classes
public import Iris.BI.BigOp
public import Iris.BI.BI
public import Iris.BI.BIBase
public import Iris.BI.DerivedLaws
public import Iris.BI.DerivedLawsLater
public import Iris.BI.InternalEq
public import Iris.Std.Positives

@[expose] public section

namespace Iris
open BI

namespace BI
open Iris.Std

variable [Sbi PROP]
variable {P Q R : PROP}

section PlainlyLaws

theorem affinely_plainly_elim : <affine> ■ P ⊢ P :=
  (affinely_mono plainly_elim_persistently).trans persistently_and_emp_elim


@[rocq_alias persistently_elim_plainly]
theorem persistently_elim_plainly : <pers> ■ P ⊣⊢ ■ P :=
  ⟨absorbingly_of_persistently.trans <| sep_symm.trans plainly_absorb,
   plainly_idemp_2.trans plainly_elim_persistently⟩

@[rocq_alias persistently_if_elim_plainly]
theorem persistently_if_elim_plainly p : <pers>?p ■ P ⊣⊢ ■ P :=
  match p with
  | true => persistently_elim_plainly
  | false => .rfl

nonrec theorem plainly_forall_2 {A : Type _} {Ψ : A → PROP} : (∀ a, ■ (Ψ a)) ⊢ ■ (∀ a, Ψ a) :=
  plainly_forall_2 _

@[rocq_alias plainly_persistently_elim]
theorem plainly_persistently_elim : ■ <pers> P ⊣⊢ ■ P := by
  refine ⟨?_, plainly_idemp_2.trans <| plainly_mono plainly_elim_persistently⟩
  calc iprop(■ <pers> P)
    _ ⊢ ■ emp ∧ ■ <pers> P := true_and.2.trans <| and_mono plainly_emp_intro .rfl
    _ ⊢ ∀ (b : Bool), if b then ■ emp else ■ <pers> P := and_forall_bool.1
    _ ⊢ ∀ (b : Bool), ■ (if b then emp else <pers> P) := forall_mono (·.casesOn .rfl .rfl)
    _ ⊢ ■ ∀ (b : Bool), if b then emp else <pers> P := plainly_forall_2
    _ ⊢ ■ (emp ∧ <pers> P) := plainly_mono and_forall_bool.2
    _ ⊢ ■ P := plainly_mono persistently_and_emp_elim

theorem absorbingly_elim_plainly : <absorb> ■ P ⊣⊢ ■ P :=
  calc iprop(<absorb> ■ P)
    _ ⊣⊢ <absorb> <pers> ■ P :=
        ⟨absorbingly_mono persistently_elim_plainly.2,
         absorbingly_mono persistently_elim_plainly.1⟩
    _ ⊣⊢ <pers> ■ P := absorbingly_persistently
    _ ⊣⊢ ■ P := persistently_elim_plainly

theorem plainly_and_sep_elim : ■ P ∧ Q ⊢ (emp ∧ P) ∗ Q :=
  (and_mono plainly_elim_persistently .rfl).trans persistently_and_sep_elim_emp

theorem plainly_and_sep_assoc : ■ P ∧ (Q ∗ R) ⊣⊢ (■ P ∧ Q) ∗ R :=
  calc iprop(■ P ∧ (Q ∗ R))
    _ ⊣⊢ <pers> ■ P ∧ (Q ∗ R) := and_congr_l persistently_elim_plainly.symm
    _ ⊣⊢ (<pers> ■ P ∧ Q) ∗ R := persistently_and_sep_assoc
    _ ⊣⊢ (■ P ∧ Q) ∗ R := sep_congr_l (and_congr_l persistently_elim_plainly)

theorem plainly_and_emp_elim : emp ∧ ■ P ⊢ P :=
  (and_mono .rfl plainly_elim_persistently).trans persistently_and_emp_elim

theorem plainly_into_absorbingly : ■ P ⊢ <absorb> P :=
  plainly_elim_persistently.trans absorbingly_of_persistently

theorem plainly_elim [Absorbing P] : ■ P ⊢ P :=
  plainly_elim_persistently.trans persistently_elim

theorem plainly_idemp : ■ ■ P ⊣⊢ ■ P :=
  ⟨plainly_into_absorbingly.trans absorbingly_elim_plainly.1, plainly_idemp_2⟩

theorem plainly_intro' (H : ■ P ⊢ Q) : ■ P ⊢ ■ Q :=
  plainly_idemp.2.trans <| plainly_mono <| H

theorem plainly_pure {φ} : ■ ⌜φ⌝ ⊣⊢ (⌜φ⌝ : PROP) := by
  refine ⟨plainly_elim_persistently.trans persistently_elim, ?_⟩
  refine pure_elim' fun φ => ?_
  exact (forall_intro (Ψ := fun _ => iprop(■ True)) Empty.rec).trans <|
    plainly_forall_2.trans (plainly_mono <| true_intro.trans <| pure_intro φ)

theorem plainly_forall {A : Type _} {Ψ : A → PROP} : ■ (∀ a, Ψ a) ⊣⊢ ∀ a, ■ (Ψ a) :=
  ⟨forall_intro (plainly_mono <| forall_elim ·), plainly_forall_2⟩

@[rocq_alias plainly_exist_2]
theorem plainly_exists_2 {α : Sort _} {Ψ : α → PROP} : (∃ a, ■ (Ψ a)) ⊢ ■ (∃ a, Ψ a) :=
  exists_elim (plainly_mono <| exists_intro ·)

theorem plainly_exists_1 [SbiEmpValidExist PROP] {A : Type _} {Ψ : A → PROP} :
    ■ (∃ a, Ψ a) ⊢ ∃ a, ■ (Ψ a) :=
  plainly_exist_1 _

theorem plainly_exists [SbiEmpValidExist PROP] {A : Type _} {Ψ : A → PROP} : ■ (∃ a, Ψ a) ⊣⊢ ∃ a, ■ (Ψ a) :=
  ⟨plainly_exists_1, plainly_exists_2⟩

theorem plainly_and : ■ (P ∧ Q) ⊣⊢ ■ P ∧ ■ Q := by
  constructor
  · refine (plainly_mono and_forall_bool.mp).trans (.trans ?_ and_forall_bool.mpr)
    exact plainly_forall.mp.trans (forall_mono (·.casesOn .rfl .rfl))
  · refine (and_forall_bool.mp).trans (.trans ?_ (plainly_mono <| and_forall_bool.mpr))
    refine .trans (forall_mono ?_) plainly_forall.mpr
    exact (·.casesOn .rfl .rfl)

theorem plainly_or_2 : ■ P ∨ ■ Q ⊢ ■ (P ∨ Q) := by
  refine or_exists_bool.mp.trans (.trans ?_ (plainly_mono <| or_exists_bool.mpr))
  refine .trans (exists_mono ?_) plainly_exists_2
  exact (·.casesOn .rfl .rfl)

theorem plainly_or [SbiEmpValidExist PROP] : ■ (P ∨ Q) ⊣⊢ ■ P ∨ ■ Q := by
  refine ⟨?_, plainly_or_2⟩
  refine (plainly_mono or_exists_bool.mp).trans (.trans ?_ or_exists_bool.mpr)
  exact plainly_exists_1.trans <| exists_mono (·.casesOn .rfl .rfl)

theorem plainly_impl : ■ (P → Q) ⊢ ■ P → ■ Q := by
  refine imp_intro' <| plainly_and.mpr.trans ?_
  exact plainly_mono imp_elim_r

theorem plainly_emp_2 : (emp : PROP) ⊢ ■ emp := plainly_emp_intro

theorem plainly_sep_dup : ■ P ⊣⊢ ■ P ∗ ■ P := by
  refine ⟨?_, plainly_absorb⟩
  calc iprop(■ P)
    _ ⊢ ■ P ∧ ■ P := and_self.2
    _ ⊢ ■ P ∧ (emp ∗ ■ P) := and_mono .rfl emp_sep.2
    _ ⊢ (■ P ∧ emp) ∗ ■ P := plainly_and_sep_assoc.1
    _ ⊢ ■ P ∗ ■ P := sep_mono and_elim_l .rfl

theorem plainly_and_sep_l_1 : ■ P ∧ Q ⊢ ■ P ∗ Q :=
  calc iprop(■ P ∧ Q)
    _ ⊢ ■ P ∧ (emp ∗ Q) := and_mono .rfl emp_sep.2
    _ ⊢ (■ P ∧ emp) ∗ Q := plainly_and_sep_assoc.1
    _ ⊢ ■ P ∗ Q := sep_mono and_elim_l .rfl

theorem plainly_and_sep_r_1 : P ∧ ■ Q ⊢ P ∗ ■ Q :=
  and_comm.1.trans <| plainly_and_sep_l_1.trans sep_symm

@[rocq_alias plainly_True_emp]
theorem plainly_true_emp : ■ True ⊣⊢ ■ (emp : PROP) :=
  ⟨plainly_emp_intro, plainly_mono true_intro⟩

theorem plainly_and_sep : ■ (P ∧ Q) ⊢ ■ (P ∗ Q) :=
  calc iprop(■ (P ∧ Q))
    _ ⊢ ■ ■ P ∧ ■ Q := plainly_and.mp.trans <| and_mono plainly_idemp_2 .rfl
    _ ⊢ ■ (■ P ∧ Q) := plainly_and.mpr
    _ ⊢ ■ (■ P ∧ (emp ∗ Q)) := plainly_mono <| and_mono .rfl emp_sep.mpr
    _ ⊢ ■ ((■ P ∧ emp) ∗ Q) := plainly_mono plainly_and_sep_assoc.1
    _ ⊢ ■ ((emp ∧ ■ P) ∗ Q) := plainly_mono <| sep_mono and_comm.mp .rfl
    _ ⊢ ■ (P ∗ Q) := plainly_mono <| sep_mono plainly_and_emp_elim .rfl

theorem plainly_affinely_elim : ■ <affine> P ⊣⊢ ■ P :=
  ⟨plainly_and.mp.trans and_elim_r, (and_intro plainly_emp_intro .rfl).trans plainly_and.mpr⟩

theorem intuitionistically_plainly_elim : □ ■ P ⊢ □ P :=
  intuitionistically_affinely.mpr.trans <| intuitionistically_mono affinely_plainly_elim

theorem intuitionistically_plainly : □ ■ P ⊢ ■ □ P := by
  refine (affinely_elim.trans ?_).trans plainly_affinely_elim.mpr
  exact persistently_elim_plainly.mp.trans plainly_persistently_elim.mpr

theorem and_sep_plainly : ■ P ∧ ■ Q ⊣⊢ ■ P ∗ ■ Q :=
  ⟨plainly_and_sep_l_1, and_intro plainly_absorb (sep_symm.trans plainly_absorb)⟩

theorem plainly_sep_2 : ■ P ∗ ■ Q ⊢ ■ (P ∗ Q) :=
  and_sep_plainly.mpr.trans <| plainly_and.mpr.trans plainly_and_sep

theorem plainly_sep [BIPositive PROP] : ■ (P ∗ Q) ⊣⊢ ■ P ∗ ■ Q := by
  refine ⟨?_, plainly_sep_2⟩
  calc iprop(■ (P ∗ Q))
    _ ⊢ ■ <affine> (P ∗ Q) := plainly_affinely_elim.mpr
    _ ⊢ ■ (<affine> P ∗ <affine> Q) := (plainly_mono <| affinely_sep.mp)
    _ ⊢ ■ P ∧ ■ Q :=
        have h₁ {P Q : PROP} :=
          calc iprop(<affine> P ∗ <affine> Q)
            _ ⊢ <affine> P ∗ emp := sep_mono .rfl affinely_elim_emp
            _ ⊢ <affine> P := sep_emp.mp
            _ ⊢ P := affinely_elim
        and_intro
          (plainly_mono h₁)
          (plainly_mono (sep_symm.trans h₁))
    _ ⊢ ■ P ∗ ■ Q := and_sep_plainly.mp

theorem plainly_wand : ■ (P -∗ Q) ⊢ ■ P -∗ ■ Q :=
  wand_intro <| plainly_sep_2.trans (plainly_mono wand_elim_l)

theorem plainly_entails_l (H : P ⊢ ■ Q) : P ⊢ ■ Q ∗ P :=
  (and_intro H .rfl).trans plainly_and_sep_l_1

theorem plainly_entails_r (H : P ⊢ ■ Q) : P ⊢ P ∗ ■ Q :=
  (and_intro .rfl H).trans plainly_and_sep_r_1

theorem plainly_impl_wand_2 : ■ (P -∗ Q) ⊢ ■ (P → Q) := by
  refine plainly_intro' (imp_intro ?_)
  calc iprop(■ (P -∗ Q) ∧ P)
    _ ⊢ ■ (P -∗ Q) ∧ (emp ∗ P) := and_mono .rfl emp_sep.mpr
    _ ⊢ (■ (P -∗ Q) ∧ emp) ∗ P := plainly_and_sep_assoc.mp
    _ ⊢ (P -∗ Q) ∗ P := sep_mono (and_comm.mp.trans plainly_and_emp_elim) .rfl
    _ ⊢ Q := wand_elim_l

theorem impl_wand_plainly_2 : (■ P -∗ Q) ⊢ (■ P → Q) :=
  imp_intro' <| plainly_and_sep_l_1.trans wand_elim_r

theorem impl_wand_affinely_plainly : (■ P → Q) ⊣⊢ (<affine> ■ P -∗ Q) := by
  constructor
  · refine (imp_mono_l persistently_elim_plainly.mp).trans ?_
    refine intuitionistically_wand.mpr.trans ?_
    exact wand_mono_l <| affinely_mono persistently_elim_plainly.mpr
  · refine .trans ?_ (imp_mono_l persistently_elim_plainly.mpr)
    refine .trans ?_ intuitionistically_wand.mp
    exact wand_mono_l affinely_of_intuitionistically

theorem persistently_wand_affinely_plainly :
    (<affine> ■ P -∗ <pers> Q) ⊢ <pers> (<affine> ■ P -∗ Q) :=
  calc iprop(<affine> ■ P -∗ <pers> Q)
    _ ⊢ ■ P → <pers> Q := impl_wand_affinely_plainly.mpr
    _ ⊢ <pers> (■ P → Q) := persistently_impl_plainly
    _ ⊢ <pers> (<affine> ■ P -∗ Q) := persistently_mono impl_wand_affinely_plainly.mp

theorem plainly_wand_affinely_plainly : (<affine> ■ P -∗ ■ Q) ⊢ ■ (<affine> ■ P -∗ Q) :=
  calc iprop(<affine> ■ P -∗ ■ Q)
    _ ⊢ ■ P → ■ Q := impl_wand_affinely_plainly.mpr
    _ ⊢ ■ (■ P → Q) := plainly_impl_plainly
    _ ⊢ ■ (<affine> ■ P -∗ Q) := plainly_mono impl_wand_affinely_plainly.mp

section AffineBI

variable [BIAffine PROP]

theorem plainly_emp : ■ emp ⊣⊢ (emp : PROP) :=
  ⟨plainly_elim, plainly_emp_2⟩

theorem plainly_and_sep_l : ■ P ∧ Q ⊣⊢ ■ P ∗ Q :=
  ⟨plainly_and_sep_l_1, sep_and⟩

theorem plainly_and_sep_r : P ∧ ■ Q ⊣⊢ P ∗ ■ Q := by
  constructor
  · exact and_comm.mp.trans <| plainly_and_sep_l.mp.trans sep_symm
  · exact sep_symm.trans <| plainly_and_sep_l.mpr.trans and_comm.mpr

theorem plainly_impl_wand : ■ (P → Q) ⊣⊢ ■ (P -∗ Q) := by
  refine ⟨?_, plainly_impl_wand_2⟩
  refine plainly_intro' <| wand_intro' ?_
  refine plainly_and_sep_r.mpr.trans ?_
  exact (and_mono .rfl plainly_elim).trans imp_elim_r

theorem impl_wand_plainly : (■ P → Q) ⊣⊢ (■ P -∗ Q) :=
  ⟨imp_wand_1, impl_wand_plainly_2⟩

end AffineBI

instance plainly_absorbing (P : PROP) : Absorbing iprop(■ P) where
  absorbing := absorbingly_elim_plainly.1

@[rocq_alias plainly_si_pure]
theorem plainly_siPure {Pi : SiProp} :
    iprop(■ (<si_pure> Pi : PROP) ⊣⊢ <si_pure> Pi) :=
  ⟨siPure_mono siEmpValid_siPure.mp, siPure_mono siEmpValid_siPure.mpr⟩

local macro "build_plainly_if" p:ident "from" thm:term : term =>  `(
  match ($p) with
  | true => $thm
  | false => by (first
    | exact Iris.BI.BIBase.BiEntails.rfl
    | exact Iris.BI.BIBase.Entails.rfl
    | assumption))

@[rocq_alias plainly_if_pure]
theorem plainly_if_pure {φ} p : ■?p ⌜φ⌝ ⊣⊢ (⌜φ⌝ : PROP) :=
  build_plainly_if p from plainly_pure

@[rocq_alias plainly_if_and]
theorem plainly_if_and p : ■?p (P ∧ Q) ⊣⊢ ■?p P ∧ ■?p Q :=
  build_plainly_if p from plainly_and

@[rocq_alias plainly_if_or_2]
theorem plainly_if_or_2 p : ■?p P ∨ ■?p Q ⊢ ■?p (P ∨ Q) :=
  build_plainly_if p from plainly_or_2

@[rocq_alias plainly_if_or]
theorem plainly_if_or [SbiEmpValidExist PROP] : ■?p (P ∨ Q) ⊣⊢ ■?p P ∨ ■?p Q :=
  build_plainly_if p from plainly_or

@[rocq_alias plainly_if_exist_2]
theorem plainly_if_exists_2 p {α : Sort _} {Ψ : α → PROP} : (∃ a, ■?p (Ψ a)) ⊢ ■?p (∃ a, Ψ a) :=
  build_plainly_if p from plainly_exists_2

@[rocq_alias plainly_if_exist]
theorem plainly_if_exists p [SbiEmpValidExist PROP] {A : Type _} {Ψ : A → PROP} : ■?p (∃ a, Ψ a) ⊣⊢ ∃ a, ■?p (Ψ a) :=
  build_plainly_if p from plainly_exists

@[rocq_alias plainly_if_idemp]
theorem plainly_if_idemp p  : ■?p ■?p P ⊣⊢ ■?p P :=
  build_plainly_if p from plainly_idemp

@[rocq_alias plainly_if_absorbing]
instance plainly_if_absorbing (P : PROP)[Absorbing P] p : Absorbing iprop(■?p P) :=
  build_plainly_if p from plainly_absorbing P
end PlainlyLaws

section PlainLaws

@[rocq_alias Plain]
class Plain [BI PROP] [BIBase.Plainly PROP] (P : PROP) where
  plain : P ⊢ ■ P

@[rocq_alias plain_plainly_2]
theorem plain_plainly_2 [Plain P] : P ⊢ ■ P := Plain.plain

@[rocq_alias plain_plainly]
theorem plain_plainly [Plain P][Absorbing P] : ■ P ⊣⊢  P := ⟨plainly_elim, Plain.plain⟩

@[rocq_alias plainly_intro]
theorem plainly_intro [ι:Plain P] : iprop(P ⊢ Q) → P ⊢ ■ Q := fun h =>
  calc iprop(P)
    _ ⊢ ■ P := Plain.plain
    _ ⊢ ■ Q := plainly_mono h

@[rocq_alias plain_persistent]
theorem plain_persistent [ι : Plain P]: Persistent P where
  persistent := ι.plain.trans plainly_elim_persistently

@[rocq_alias impl_persistent]
instance impl_persistent
  [Absorbing P][Plain P][Persistent Q] : Persistent iprop(P → Q) where
  persistent := by
    calc iprop(P → Q)
      _ ⊢ (<absorb> P → Q) := imp_mono Absorbing.absorbing .rfl
      _ ⊢ (■ P → Q)        := imp_mono plainly_into_absorbingly .rfl
      _ ⊢ (■ P → <pers> Q) := imp_mono .rfl Persistent.persistent
      _ ⊢ <pers> (■ P → Q) := persistently_impl_plainly
      _ ⊢ <pers> (P → Q)   := persistently_mono (imp_mono Plain.plain .rfl)

@[rocq_alias plainly_persistent]
instance plainly_persistent : Persistent iprop(■ P) where
  persistent := persistently_elim_plainly.2

@[rocq_alias wand_persistent]
instance wand_persistent [Plain P][Persistent Q][Absorbing Q] :
  Persistent iprop(P -∗ Q) where
  persistent :=
    open Plain Persistent Absorbing in
    calc iprop(P -∗ Q)
    _ ⊢ (<affine> ■ P -∗ <pers> Q) := wand_mono affinely_plainly_elim persistent
    _ ⊢ (■ P → <pers> Q)  := impl_wand_affinely_plainly.2
    _ ⊢ <pers> (■ P → Q)  := persistently_impl_plainly
    _ ⊢ <pers> (■ P -∗ Q) := persistently_mono (wand_intro' (sep_and.trans imp_elim_r))
    _ ⊢ <pers> (P -∗ Q)   := persistently_mono (wand_mono plain .rfl)

@[rocq_alias limit_preserving_Plain]
instance limitPreserving_plain {A} [COFE A] (Φ : A → PROP) (Φne : OFE.NonExpansive Φ) :
 LimitPreserving (fun x => Plain (Φ x)) := by
   letI _ : OFE.NonExpansive fun x => iprop(■ Φ x) := .comp inferInstance Φne
   refine fun c h => ⟨?_⟩
   refine LimitPreserving.entails _ (fun x => iprop(■ (Φ x))) _ ?_
   exact (fun n => h n |>.plain)

section BigOp

theorem BiEntails_proper : ∀ {a a' b b' : PROP}, a ≡ a' → b ≡ b' → (a ⊣⊢ b ↔ a' ⊣⊢ b') :=
  fun aa' bb' =>
    ⟨ fun h => equiv_iff.1 (aa'.symm.trans (equiv_iff.2 h) |>.trans bb')
    , fun h => equiv_iff.1 (aa'.trans (equiv_iff.2 h) |>.trans bb'.symm)⟩

@[rocq_alias plainly_sep_weak_homomorphism]
instance plainly_sep_weak_homomorphism [BIPositive PROP][BIAffine PROP] :
  Algebra.WeakMonoidHomomorphism BIBase.sep BIBase.sep iprop(emp) iprop(emp) BIBase.BiEntails (BIBase.plainly (PROP := PROP)) where
  rel_refl := .rfl
  rel_trans := .trans
  rel_proper := BiEntails_proper
  op_proper aa' bb' := equiv_iff.1 (sep_ne.eqv (equiv_iff.2 aa') (equiv_iff.2 bb'))
  map_ne := inferInstance
  map_op := plainly_sep

instance plainly_and_weak_homomorphism :
  Algebra.WeakMonoidHomomorphism BIBase.and BIBase.and iprop(True) iprop(True) BIBase.BiEntails (BIBase.plainly (PROP := PROP)) where
  rel_refl := .rfl
  rel_trans := .trans
  rel_proper := BiEntails_proper
  op_proper aa' bb' := equiv_iff.1 (and_ne.eqv (equiv_iff.2 aa') (equiv_iff.2 bb'))
  map_ne := inferInstance
  map_op := plainly_and

instance plainly_or_weak_homomorphism [SbiEmpValidExist PROP] :
  Algebra.WeakMonoidHomomorphism BIBase.or BIBase.or iprop(False) iprop(False) BIBase.BiEntails (BIBase.plainly (PROP := PROP)) where
  rel_refl := .rfl
  rel_trans := .trans
  rel_proper := BiEntails_proper
  op_proper aa' bb' := equiv_iff.1 (or_ne.eqv (equiv_iff.2 aa') (equiv_iff.2 bb'))
  map_ne := inferInstance
  map_op := plainly_or

@[rocq_alias plainly_sep_homomorphism]
instance plainly_sep_homomorphism [BIAffine PROP] :
  Algebra.MonoidHomomorphism BIBase.sep BIBase.sep iprop(emp) iprop(emp) BIBase.BiEntails (BIBase.plainly (PROP := PROP)) where
  map_unit := plainly_emp

@[rocq_alias plainly_and_homomorphism]
instance plainly_and_homomorphism :
  Algebra.MonoidHomomorphism BIBase.and BIBase.and iprop(True) iprop(True) BIBase.BiEntails (BIBase.plainly (PROP := PROP)) where
  map_unit := plainly_pure

@[rocq_alias plainly_or_homomorphism]
instance plainly_or_homomorphism [SbiEmpValidExist PROP] :
  Algebra.MonoidHomomorphism BIBase.or BIBase.or iprop(False) iprop(False) BIBase.BiEntails (BIBase.plainly (PROP := PROP)) where
  map_unit := plainly_pure

@[rocq_alias big_sepL_plainly]
theorem bigSepL_plainly [BIAffine PROP] {A} (Φ : Nat → A → PROP) l :
    iprop(■ ([∗list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∗list] k ↦ x ∈ l, ■ (Φ k x)) :=
  (Algebra.BigOpL.bigOpL_hom ..)

@[rocq_alias big_andL_plainly]
theorem bigAndL_plainly {A} (Φ : Nat → A → PROP) l :
    iprop(■ ([∧list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∧list] k ↦ x ∈ l, ■ (Φ k x)) :=
  (Algebra.BigOpL.bigOpL_hom ..)

@[rocq_alias big_orL_plainly]
theorem bigOrL_plainly [SbiEmpValidExist PROP] {A} (Φ : Nat → A → PROP) l :
    iprop(■ ([∨list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∨list] k ↦ x ∈ l, ■ (Φ k x)) :=
  (Algebra.BigOpL.bigOpL_hom ..)

@[rocq_alias big_sepL2_plainly]
theorem bigSepL2_plainly [BIAffine PROP] {A B} (Φ : Nat → A → B → PROP) l₁ l₂ :
    ■ ([∗list] k↦y₁;y₂ ∈ l₁;l₂, Φ k y₁ y₂)
    ⊣⊢ [∗list] k↦y₁;y₂ ∈ l₁;l₂, ■ (Φ k y₁ y₂) :=
  calc iprop(■ ([∗list] k↦y₁;y₂ ∈ l₁;l₂, Φ k y₁ y₂))
    _ ⊣⊢ _ := .ofMono plainly_mono BigSepL2.bigSepL2_alt
    _ ⊣⊢ _ := plainly_and
    _ ⊣⊢ _ := .ofMono and_mono_l plainly_pure
    _ ⊣⊢ _ := .ofMono and_mono_r (bigSepL_plainly _ _)
    _ ⊣⊢ [∗list] k ↦ y₁;y₂ ∈ l₁;l₂, ■ (Φ k y₁ y₂) := .symm <| BigSepL2.bigSepL2_alt

@[rocq_alias big_sepM_plainly]
theorem bigSepM_plainly [BIAffine PROP] [Pos.Countable K] [LawfulFiniteMap M K]
  {A} (Φ : K → A → PROP) (m : M A) :
    ■ ([∗map] k↦x ∈ m, Φ k x) ⊣⊢ [∗map] k↦x ∈ m, ■ (Φ k x) :=
  (Algebra.BigOpM.bigOpM_hom ..)

open Algebra in
@[rocq_alias big_sepS_plainly]
theorem bigSepS_plainly [BIAffine PROP] [Pos.Countable A] [LawfulFiniteSet S A] (Φ : A → PROP) (s : S) :
    ■ ([^ sep set] y ∈ s, Φ y) ⊣⊢ [^ sep set] y ∈ s, iprop(■ (Φ y)) :=
  (BigOpS.hom (hom := inferInstance) ..)

end BigOp

section instances
open Plain

@[rocq_alias pure_plain]
instance pure_plain φ : Plain (PROP := PROP) iprop(⌜φ⌝) where
  plain := plainly_pure.2

@[rocq_alias emp_plain]
instance emp_plain : Plain (PROP := PROP) iprop(emp) where
  plain := plainly_emp_intro

@[rocq_alias and_plain]
instance and_plain (P Q : PROP)[Plain P] [Plain Q]: Plain iprop(P ∧ Q) where
  plain := .trans (and_mono plain plain) plainly_and.2

@[rocq_alias or_plain]
instance or_plain (P Q : PROP)[Plain P] [Plain Q]: Plain iprop(P ∨ Q) where
  plain := .trans (or_mono plain plain) plainly_or_2

@[rocq_alias forall_plain]
instance forall_plain {A : Type _} (Ψ : A → PROP) : [∀ x, Plain (Ψ x)] → Plain iprop(∀ x, Ψ x) where
  plain := .trans (forall_mono (fun _ => plain)) plainly_forall_2

@[rocq_alias exists_plain]
instance exists_plain {A : Type _} (Ψ : A → PROP) : [∀ x, Plain (Ψ x)] → Plain iprop(∃ x, Ψ x) where
  plain := .trans (exists_mono (fun _ => plain)) plainly_exists_2

@[rocq_alias impl_plain]
instance impl_plain (P Q : PROP) [Absorbing P] [Plain P] [Plain Q] : Plain iprop(P → Q) where
  plain := calc iprop(P → Q)
    _ ⊢ (<absorb> P → Q) := imp_mono (Absorbing.absorbing) .rfl
    _ ⊢ (■ P → ■ Q) := imp_mono (plainly_into_absorbingly) plain
    _ ⊢ ■ (■ P → Q) := plainly_impl_plainly
    _ ⊢ ■ (P → Q) := plainly_mono (imp_mono plain .rfl)

@[rocq_alias wand_plain]
instance wand_plain (P Q : PROP) [Absorbing Q] [Plain P] [Plain Q] : Plain iprop(P -∗ Q) where
  plain := calc iprop(P -∗ Q)
    _ ⊢ <affine> ■ P -∗ ■ Q := wand_mono (affinely_plainly_elim) (plain)
    _ ⊢ ■ P → ■ Q    := impl_wand_affinely_plainly.2
    _ ⊢ ■ (■ P → Q)  := plainly_impl_plainly
    _ ⊢ ■ (■ P -∗ Q) := plainly_mono (wand_intro' (sep_and.trans imp_elim_r))
    _ ⊢ ■ (P -∗ Q)   := plainly_mono (wand_mono plain .rfl)

@[rocq_alias sep_plain]
instance sep_plain (P Q : PROP)[Plain P] [Plain Q]: Plain iprop(P ∗ Q) where
  plain := .trans (sep_mono plain plain) plainly_sep_2

@[rocq_alias plainly_plain]
instance plainly_plain(P : PROP) : Plain iprop(■ P) := ⟨plainly_idemp_2⟩

@[rocq_alias persistently_plain]
instance persistently_plain (P : PROP) [ι : Plain P] : Plain iprop(<pers> P) where
  plain := persistently_mono plain |>.trans (.trans persistently_elim_plainly.1 plainly_persistently_elim.2)

@[rocq_alias affinely_plain]
instance affinely_plain (P : PROP) [Plain P] : Plain iprop(<affine> P) :=
  inferInstanceAs (Plain iprop(emp ∧ P))

@[rocq_alias intuitionistically_plain]
instance intuitionistically_plain (P : PROP) [Plain P] : Plain iprop(□ P) :=
  inferInstanceAs (Plain iprop(<affine> <pers> P))

@[rocq_alias absorbingly_plain]
instance absorbingly_plain (P : PROP) [Plain P] : Plain iprop(<absorb> P) :=
  inferInstanceAs (Plain iprop(True ∗ P))

@[rocq_alias from_option_plain]
instance from_option_plain {A : Type _} (P : PROP)  (Ψ : A → PROP) (x? : Option A)
  [hΨ : ∀ x, Plain (Ψ x)] [hP : Plain P] :
    Plain (Option.elim x? P Ψ) :=
  match x? with
  | (x : A) => hΨ x
  | .none   => hP

@[rocq_alias si_pure_plain]
instance si_pure_plain (P : SiProp) : Plain (PROP := PROP) (siPure P) where
  plain := plainly_siPure.2

@[rocq_alias si_emp_valid_plain]
instance si_emp_valid_plain (P : PROP) : Plain (siEmpValid P) where
  plain := .rfl

@[rocq_alias big_sepL_nil_plain]
instance big_sepL_nil_plain {A} (Φ : Nat → A → PROP) :
   Plain ([∗list] k ↦ x ∈ [], Φ k x) := inferInstanceAs (Plain iprop(emp))

@[rocq_alias big_sepL_plain]
instance big_sepL_plain {A} (Φ : Nat → A → PROP) l [h : ∀ k x, Plain (Φ k x)] :
   Plain ([∗list] k ↦ x ∈ l, Φ k x) where
   plain := by
    induction l generalizing Φ with
    | nil => exact plain
    | cons hd tl IH =>
      have : Plain iprop([∗list] k ↦ x ∈ tl, Φ (k + 1) x) := ⟨IH _⟩
      apply sep_plain _ _ |>.plain

@[rocq_alias big_andL_nil_plain]
instance big_andL_nil_plain {A} (Φ : Nat → A → PROP) :
   Plain ([∧list] k ↦ x ∈ [], Φ k x) := inferInstanceAs (Plain iprop(True))

@[rocq_alias big_andL_plain]
instance big_andL_plain {A} (Φ : Nat → A → PROP) l [h : ∀ k x, Plain (Φ k x)] :
   Plain ([∧list] k ↦ x ∈ l, Φ k x) where
   plain := by
    induction l generalizing Φ with
    | nil => exact plain
    | cons hd tl IH =>
      have : Plain iprop([∧list] k ↦ x ∈ tl, Φ (k + 1) x) := ⟨IH _⟩
      apply and_plain _ _ |>.plain

@[rocq_alias big_orL_nil_plain]
instance big_orL_nil_plain {A} (Φ : Nat → A → PROP) :
   Plain ([∨list] k ↦ x ∈ [], Φ k x) := inferInstanceAs (Plain iprop(False))

@[rocq_alias big_orL_plain]
instance big_orL_plain {A} (Φ : Nat → A → PROP) l [h : ∀ k x, Plain (Φ k x)] :
   Plain ([∨list] k ↦ x ∈ l, Φ k x) where
   plain := by
    induction l generalizing Φ with
    | nil => exact plain
    | cons hd tl IH =>
      have : Plain iprop([∨list] k ↦ x ∈ tl, Φ (k + 1) x) := ⟨IH _⟩
      apply or_plain _ _ |>.plain

@[rocq_alias big_sepL2_nil_plain]
instance bigSepL2_nil_plain {A B} (Φ : Nat → A → B → PROP) :
   Plain ([∗list] k ↦ x1;x2 ∈ [];[], Φ k x1 x2) := inferInstanceAs (Plain iprop(emp))

#check BigSepL2.bigSepL2_alt

@[rocq_alias big_sepL2_plain]
instance bigSepL2_plain {A B} (Φ : Nat → A → B → PROP) l1 l2 [h : ∀ k x1 x2, Plain (Φ k x1 x2)] :
   Plain ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) where
   plain := by
    apply BigSepL2.bigSepL2_alt.1.trans
    apply (and_mono Plain.plain (Plain.plain)).trans
    apply plainly_and.2.trans
    refine (plainly_mono BigSepL2.bigSepL2_alt.2)

@[rocq_alias big_sepM_empty_plain]
instance  bigSepM_empty_plain {K} [Pos.Countable K] {M A} [LawfulFiniteMap M K] (Φ : K → A → PROP) :
    Plain ([∗map] k↦x ∈ (∅ : M A), Φ k x) where
  plain := by
    simp only [Algebra.BigOpM.bigOpM_empty]
    apply plain

@[rocq_alias big_sepM_plain]
instance  bigSepM__plain {K} [DecidableEq K] {M A} [ι : LawfulFiniteMap M K] (Φ : K → A → PROP)
  (m : M A) [h : ∀ k x, Plain (Φ k x)] :
    Plain ([∗map] k↦x ∈ m, Φ k x) where
  plain := by
    induction m using Iris.Std.LawfulFiniteMap.induction_on (K := K) (M := M)
    case hequiv m₁ m₂ m₁m₂ H =>
      have h : iprop([∗map] k ↦ x ∈ m₁, Φ k x) ≡ [∗map] k ↦ x ∈ m₂, Φ k x :=
          Algebra.BigOpM.bigOpM_equiv_of_perm (M' := M) _ m₁m₂
      calc iprop([∗map] k ↦ x ∈ m₂, Φ k x)
        _ ⊣⊢ [∗map] k ↦ x ∈ m₁, Φ k x := BI.equiv_iff.1 h |>.symm
        _  ⊢ ■ [∗map] k ↦ x ∈ m₁, Φ k x := H
        _ ⊣⊢ ■ [∗map] k ↦ x ∈ m₂, Φ k x := .ofMono plainly_mono <| BI.equiv_iff.1 h
    case hemp =>
      rw [show empty (M := M) (K := K) = ∅ from rfl]
      simp only [Algebra.BigOpM.bigOpM_empty, plain]
    case hins k v m get?_m_k IH=>
      calc iprop([∗map] k ↦ x ∈ Std.insert m k v, Φ k x)
        _ ⊣⊢ Φ k v ∗ [∗map] k ↦ x ∈  m, Φ k x :=
            BI.equiv_iff.1 (Algebra.BigOpM.bigOpM_insert_equiv _ _ get?_m_k)
        _  ⊢ ■ Φ k v ∗ ■ [∗map] k ↦ x ∈  m, Φ k x :=
          sep_mono (h k v |>.plain) IH
        _  ⊢ ■ (Φ k v ∗ [∗map] k ↦ x ∈  m, Φ k x) := plainly_sep_2
        _ ⊣⊢ ■ [∗map] k ↦ x ∈ Std.insert m k v, Φ k x :=
          .ofMono plainly_mono <|
            BI.equiv_iff.1 (Algebra.BigOpM.bigOpM_insert_equiv _ _ get?_m_k) |>.symm

open Algebra in
@[rocq_alias big_sepS_empty_plain]
instance  bigSepS_empty_plain {S} [Pos.Countable S] {A} [LawfulFiniteSet S A] (Φ : A → PROP) :
    Plain ([^ sep set] x ∈ (∅ : S), Φ x) where
  plain := by
    simp only [Algebra.BigOpS.bigOpS_empty]
    apply plain

open Algebra in
@[rocq_alias big_sepS_plain]
instance  bigSepS_plain {S} [Pos.Countable S] {A} [LawfulFiniteSet S A] (Φ : A → PROP) (s : S)
  [h : ∀ x, Plain (Φ x)] :
    Plain ([^ sep set] x ∈ s, Φ x) where
  plain := by
    induction s using FiniteSet.set_ind
    case hemp =>
      simp only [BigOpS.bigOpS_empty, plain]
    case hadd x s x_s IH =>
      calc iprop([^ sep set] x ∈ insert x s, Φ x)
        _ ⊣⊢ Φ x ∗ [^ sep set] x ∈  s, Φ x :=
            BI.equiv_iff.1 (BigOpS.bigOpS_insert x_s)
        _  ⊢ ■ Φ x ∗ ■ [^ sep set] x ∈ s, Φ x :=
          sep_mono (h x |>.plain) IH
        _  ⊢ ■ (Φ x ∗ [^ sep set] x ∈ s, Φ x) := plainly_sep_2
        _ ⊣⊢ ■ [^ sep set] y ∈ insert x s, Φ y :=
          .ofMono plainly_mono <|
            BI.equiv_iff.1 (BigOpS.bigOpS_insert x_s).symm

instance plainly_timeless (P : PROP) [Timeless P] : Timeless iprop(■ P) :=
  inferInstanceAs (Timeless iprop(<si_pure> <si_emp_valid> P))

@[rocq_alias plainly_internal_eq]
theorem plainly_internalEq {A} [OFE A](a b : A) : iprop(■ (SiProp.internalEq a b) ⊣⊢ SiProp.internalEq a b) := by
  constructor
  · exact plainly_elim
  · have : OFE.NonExpansive (λ x ↦ iprop(■ (SiProp.internalEq a x))) :=  {
      ne n x x' xx' := by
        -- TODO: Try to do it without breaking the abstraction layer
        apply instPlainly_ne.ne
        intros n ih
        specialize xx'
        dsimp [SiProp.internalEq]
        constructor
        · intros ax
          exact ax.trans (xx'.le ih)
        · intros ax'
          exact ax'.trans (xx'.symm.le ih)
    }
    have := SiProp.internalEq_rewrite a b (λ x ↦ iprop(■ (SiProp.internalEq a x)))
    have := imp_elim this
    refine .trans ?_ this
    apply and_intro
    · exact .rfl
    · calc iprop(SiProp.internalEq a b)
        _ ⊢ True := true_intro
        _ ⊢ ■ (True) := plainly_pure.2
        _ ⊢ ■ (SiProp.internalEq a a) := plainly_mono (SiProp.internalEq_refl _ _)

theorem internalEq_plain {A} [OFE A](a b : A) : Plain iprop(SiProp.internalEq a b) where
  plain := plainly_internalEq _ _ |>.1

@[rocq_alias prop_ext]
theorem prop_ext (P Q : PROP) : iprop(internalEq P Q ⊣⊢ ■ (P ∗-∗ Q)) :=
  have ⟨mp, mpr⟩:= prop_ext_siEmpValid_equiv P Q
  ⟨siPure_mono mp, siPure_mono mpr⟩

@[rocq_alias plainly_alt]
theorem plainly_alt (P : PROP) : ■ P ⊣⊢ internalEq iprop(<affine> P) iprop(emp) := by
  apply plainly_affinely_elim.symm.trans
  constructor
  · refine .trans ?_ (prop_ext (affinely P) iprop(emp) |>.2)
    apply plainly_mono
    apply and_intro <;> apply wand_intro'
    · apply affinely_sep_2.trans affinely_elim_emp
    · apply emp_sep.1
  · calc iprop(internalEq _ _)
      _ ⊢ internalEq _ _                := internalEq.symm
      _ ⊢ ■ iprop(emp) → ■ (<affine> P) := internalEq.rewrite BIBase.plainly
      _ ⊢ True → ■ (<affine> P)         := imp_mono_l (plainly_pure.2.trans plainly_true_emp.1)
      _ ⊢ ■ <affine> P                  := true_imp.1

@[rocq_alias plainly_alt_absorbing]
theorem plainly_alt_absorbing (P : PROP)[Absorbing P] : ■ P ⊣⊢ internalEq iprop(P) iprop(True) := by
  constructor
  · refine .trans ?_ (prop_ext P iprop(True) |>.2)
    apply plainly_mono
    apply and_intro <;> apply wand_intro'
    · apply true_intro
    · exact true_sep.1
  · calc iprop(internalEq _ _)
      _ ⊢ internalEq _ _      := internalEq.symm
      _ ⊢ ■ True → ■ iprop(P) := internalEq.rewrite BIBase.plainly
      _ ⊢ True → ■ iprop(P)   := imp_mono_l plainly_pure.2
      _ ⊢ ■ P                 := true_imp.1

theorem plainly_True_alt (P : PROP) : ■ (True -∗ P) ⊣⊢ internalEq P iprop(True) := by
  constructor
  · refine .trans ?_ (prop_ext P iprop(True) |>.2)
    apply plainly_mono
    apply and_intro <;> apply wand_intro'
    · apply true_intro
    · exact wand_elim_r
  · calc iprop(internalEq _ _)
      _ ⊢ internalEq _ _ := internalEq.symm
      _ ⊢ ■ (True -∗ True) → (■ (True -∗ P)) :=
        let Ψ P := iprop(■ (True -∗ P))
        have : OFE.NonExpansive Ψ := OFE.NonExpansive.comp (inferInstance) (wand_ne.ne_right _ _)
        internalEq.rewrite Ψ
      _ ⊢ ■ emp → (■ (True -∗ P)) := imp_mono_l <| plainly_mono <| wand_intro <| true_intro
      _ ⊢ True → (■ (True -∗ P))  := imp_mono_l (plainly_emp_intro)
      _ ⊢ ■ (True -∗ P)           := pure_imp_elim trivial

-- TODO: Should this be here?
instance internalEq_timeless (P Q : PROP) [Timeless P] [Timeless Q] : Timeless (PROP := PROP) (internalEq P Q) where
  timeless :=
    have ⟨mp, mpr⟩:= prop_ext P Q
    calc iprop(▷ internalEq P Q)
      _ ⊢ ▷ ■ (P ∗-∗ Q) := later_mono mp
      _ ⊢ ◇ ■ (P ∗-∗ Q) := Timeless.timeless
      _ ⊢ ◇ internalEq P Q := except0_mono mpr

@[rocq_alias laterN_plainly]
theorem laterN_plainly n {P : PROP} : ▷^[n] ■ P ⊣⊢ ■ ▷^[n] P :=
  match n with
  | 0 => .rfl
  | n+1 => by
    unfold BIBase.laterN
    calc iprop(▷^[n+1] ■ P)
      _ ⊣⊢ ▷ ■ ▷^[n] P := .ofMono later_mono (laterN_plainly n)
      _ ⊣⊢ ■ ▷^[n+1] P := later_plainly

@[rocq_alias later_plainly_if]
theorem later_plainlyIf {P : PROP} p : ▷ ■?p P ⊣⊢ ■?p ▷ P :=
  match p with
  | true => later_plainly
  | false => .rfl

@[rocq_alias laterN_plainly_if]
theorem laterN_plainlyIf n {P : PROP} p : ▷^[n] ■?p P ⊣⊢ ■?p ▷^[n] P :=
  match p with
  | true => laterN_plainly n
  | false => .rfl

@[rocq_alias except_0_plainly_1]
theorem except0_plainly_1 (P : PROP) : ◇ ■ P ⊢ ■ ◇ P :=
  calc iprop(▷ False ∨ ■ P)
    _ ⊢ ▷ ■ False ∨ ■ P := or_mono_l (later_mono plainly_pure.2)
    _ ⊢ ■ ▷ False ∨ ■ P := or_mono_l later_plainly.1
    _ ⊢ ■ (▷ False ∨ P) := plainly_or_2

@[rocq_alias except_0_plainly]
theorem except0_plainly {P : PROP} : ◇ ■ P ⊣⊢ ■ ◇ P :=
  calc iprop(◇ <si_pure> <si_emp_valid> P)
    _ ⊣⊢@{PROP} <si_pure> (◇ <si_emp_valid> P)   := siPure_except0.symm
    _ ⊣⊢        <si_pure> (<si_emp_valid> (◇ P)) := .ofMono siPure_mono siEmpValid_except0.symm

@[rocq_alias later_plain]
instance later_plain (P : PROP) [Plain P] : Plain iprop(▷ P) where
  plain := later_mono Plain.plain |>.trans later_plainly.1

@[rocq_alias laterN_plain]
instance laterN_plain n (P : PROP) [Plain P] : Plain iprop(▷^[n] P) where
  plain := laterN_mono n (Plain.plain) |>.trans (laterN_plainly n).1

@[rocq_alias except_0_plain]
instance except0_plain (P : PROP) [Plain P] : Plain iprop(◇ P) where
  plain := except0_mono Plain.plain |>.trans except0_plainly.1

end instances

end PlainLaws

end Iris.BI
