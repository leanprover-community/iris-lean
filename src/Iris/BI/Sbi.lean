/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.BI.BI
import Iris.BI.Classes
import Iris.BI.DerivedLaws
import Iris.BI.DerivedLawsLater
import Iris.BI.Extensions
import Iris.BI.SIProp
import Iris.Std.RocqAlias

/-!
# Step-indexed BI (SBI)

The SBI interface describes BIs with a step-indexed structure. An SBI has an operation
`siPure : SiProp → PROP` that embeds a `SiProp` into the logic while preserving the
step-index, and `siEmpValid : PROP → SiProp` that expresses that a proposition is valid
(under assumption `emp`) at a given step-index.
-/

namespace Iris
open OFE BI

/-- Embedding of step-indexed propositions into a BI. -/
class SiPure (PROP : Type _) where
  siPure : SiProp → PROP
export SiPure (siPure)

/-- Step-indexed validity of BI propositions. -/
class SiEmpValid (PROP : Type _) where
  siEmpValid : PROP → SiProp
export SiEmpValid (siEmpValid)

section Notation

syntax "<si_pure> " term:40 : term
syntax "<si_emp_valid> " term:40 : term

macro_rules
  | `(iprop(<si_pure> $P)) => ``(SiPure.siPure iprop($P))
  | `(iprop(<si_emp_valid> $P)) => ``(SiEmpValid.siEmpValid iprop($P))

delab_rule SiPure.siPure
  | `($_ $P) => do ``(iprop(<si_pure> $(← BI.unpackIprop P)))

delab_rule SiEmpValid.siEmpValid
  | `($_ $P) => do ``(iprop(<si_emp_valid> $(← BI.unpackIprop P)))

end Notation

/-- The `Sbi` class: a BI with step-indexed structure. -/
@[rocq_alias Sbi]
class Sbi (PROP : Type _) extends BI PROP, SiPure PROP, SiEmpValid PROP where
  siPure_ne : NonExpansive (α := SiProp) (β := PROP) SiPure.siPure
  siEmpValid_ne : NonExpansive (α := PROP) (β := SiProp) SiEmpValid.siEmpValid
  siPure_mono {Pi Qi : SiProp} (H : Pi ⊢@{SiProp} Qi) : <si_pure> Pi ⊢@{PROP} <si_pure> Qi
  siEmpValid_mono {P Q : PROP} (H : P ⊢@{PROP} Q) : <si_emp_valid> P ⊢@{SiProp} <si_emp_valid> Q
  siEmpValid_siPure {Pi : SiProp} : <si_emp_valid> (<si_pure> Pi : PROP) ⊣⊢@{SiProp} Pi
  siPure_siEmpValid {P : PROP} : <si_pure> <si_emp_valid> P ⊢ <pers> P
  siPure_imp_mpr {Pi Qi : SiProp} : (<si_pure> Pi → <si_pure> Qi) ⊢@{PROP} <si_pure> (Pi → Qi)
  siPure_sForall_mpr {Ψi : SiProp → Prop} :
    (∀ q, ⌜Ψi q⌝ → <si_pure> q) ⊢@{PROP} <si_pure> @BIBase.sForall SiProp _ Ψi
  persistently_imp_siPure {Pi : SiProp} {Q : PROP} :
    (<si_pure> Pi → <pers> Q) ⊢ <pers> (<si_pure> Pi → Q)
  siPure_later {Pi : SiProp} : <si_pure> (▷ Pi) ⊣⊢@{PROP} ▷ <si_pure> Pi
  siPure_absorbing (Pi : SiProp) : Absorbing (PROP := PROP) iprop(<si_pure> Pi)
  siEmpValid_later_mp {P : PROP} : <si_emp_valid> (▷ P) ⊢@{SiProp} ▷ <si_emp_valid> P
  siEmpValid_affinely_mpr {P : PROP} : <si_emp_valid> P ⊢@{SiProp} <si_emp_valid> (<affine> P)
  prop_ext_siEmpValid {P Q : PROP} : <si_emp_valid> (P ∗-∗ Q) ⊢@{SiProp} SiProp.internalEq P Q

attribute [instance] Sbi.siPure_ne Sbi.siEmpValid_ne Sbi.siPure_absorbing

export Sbi (siPure_mono siEmpValid_mono siEmpValid_siPure siPure_siEmpValid siPure_imp_mpr
  siPure_sForall_mpr persistently_imp_siPure siPure_later siEmpValid_later_mp
  siEmpValid_affinely_mpr prop_ext_siEmpValid)

/-- `SbiEmpValidExist` generalizes that plainly commutes with existentials and disjunction. -/
@[rocq_alias SbiEmpValidExist]
class SbiEmpValidExist (PROP : Type _) [BI PROP] [SiEmpValid PROP] where
  siEmpValid_sExists_1 (Ψ : PROP → Prop) :
    iprop(<si_emp_valid> sExists Ψ ⊢@{SiProp} ∃ p, ⌜Ψ p⌝ ∧ <si_emp_valid> p)

/-! ## siProp SBI instance -/

instance : SiPure SiProp where
  siPure := id

instance : SiEmpValid SiProp where
  siEmpValid := id

@[rocq_alias siprop_sbi]
instance instSbiSiProp : Sbi SiProp where
  siPure_ne := id_ne
  siEmpValid_ne := id_ne
  siPure_mono := id
  siEmpValid_mono := id
  siEmpValid_siPure := .rfl
  siPure_siEmpValid _ := id
  siPure_imp_mpr := .rfl
  siPure_sForall_mpr := by
    refine sForall_intro fun p hp => ?_
    exact and_intro (forall_elim p) (pure_intro hp) |>.trans <| imp_elim .rfl
  persistently_imp_siPure _ := id
  siPure_later := .rfl
  siPure_absorbing _ := ⟨fun _ => (·.2)⟩
  siEmpValid_later_mp := .rfl
  siEmpValid_affinely_mpr _ := (⟨trivial, ·⟩)
  prop_ext_siEmpValid := @SiProp.prop_ext

@[rocq_alias siprop_sbi_emp_valid_exist]
instance instSbiEmpValidExistSiProp : SbiEmpValidExist SiProp where
  siEmpValid_sExists_1 _ :=
    sExists_elim fun p hp => exists_intro' p (and_intro (pure_intro hp) .rfl)

/-! ## Derived laws -/

/-! ### Persistent -/

@[rocq_alias si_pure_persistent]
instance siPure_persistent [Sbi PROP] : Persistent (PROP := PROP) iprop(<si_pure> Pi) where
  persistent :=
    calc iprop(<si_pure> Pi)
      _ ⊢ <si_pure> <si_emp_valid> <si_pure> Pi := siPure_mono siEmpValid_siPure.mpr
      _ ⊢ <pers> <si_pure> Pi := siPure_siEmpValid

/-! ### Commuting rules of `siPure` -/

@[rocq_alias si_pure_forall_2]
theorem siPure_forall_mpr [Sbi PROP] {A : Type _} {Φi : A → SiProp} :
    (∀ x, <si_pure> Φi x) ⊢@{PROP} <si_pure> (∀ x, Φi x) := by
  refine (forall_intro fun _ => imp_intro' <| pure_elim_l ?_).trans siPure_sForall_mpr
  exact fun ⟨a, ha⟩ => ha ▸ forall_elim a

@[rocq_alias si_pure_forall]
theorem siPure_forall [Sbi PROP] {A : Type _} {Φi : A → SiProp} :
    <si_pure> (∀ x, Φi x) ⊣⊢@{PROP} ∀ x, <si_pure> Φi x :=
  ⟨forall_intro (siPure_mono <| forall_elim ·), siPure_forall_mpr⟩

@[rocq_alias si_pure_exist]
theorem siPure_exist [Sbi PROP] {A : Type _} {Φi : A → SiProp} :
    <si_pure> (∃ x, Φi x) ⊣⊢@{PROP} ∃ x, <si_pure> Φi x := by
  refine ⟨?_, exists_elim (siPure_mono <| exists_intro ·)⟩
  calc iprop(<si_pure> (∃ x, Φi x))
    _ ⊢ <si_pure> (∃ x, <si_emp_valid> <si_pure> Φi x) :=
        siPure_mono <| exists_mono fun _ => (siEmpValid_siPure (PROP := PROP)).mpr
    _ ⊢ <si_pure> <si_emp_valid> (∃ x, <si_pure> Φi x) :=
        siPure_mono <|
        exists_elim fun x => siEmpValid_mono (exists_intro (Ψ := fun _ => iprop(<si_pure> _)) x)
    _ ⊢ <pers> (∃ x, <si_pure> Φi x) := siPure_siEmpValid
    _ ⊢ ∃ (x : A), <si_pure> Φi x := persistently_elim

@[rocq_alias si_pure_and]
theorem siPure_and [Sbi PROP] {Pi Qi : SiProp} :
        <si_pure> (Pi ∧ Qi) ⊣⊢@{PROP} <si_pure> Pi ∧ <si_pure> Qi := by
  refine ⟨and_intro (siPure_mono and_elim_l) (siPure_mono and_elim_r), ?_⟩
  calc iprop(<si_pure> Pi ∧ <si_pure> Qi)
    _ ⊢ ∀ (b : Bool), if b then <si_pure> Pi else <si_pure> Qi := (and_forall_bool ..).mp
    _ ⊢ ∀ (b : Bool), <si_pure> (if b then Pi else Qi) := forall_mono (·.casesOn .rfl .rfl)
    _ ⊢ <si_pure> ∀ (b : Bool), if b then Pi else Qi := siPure_forall_mpr
    _ ⊢ <si_pure> (Pi ∧ Qi) := siPure_mono and_forall_bool.mpr

@[rocq_alias si_pure_and_sep]
theorem siPure_and_sep [Sbi PROP] {Pi Qi : SiProp} :
    <si_pure> (Pi ∧ Qi) ⊣⊢@{PROP} <si_pure> Pi ∗ <si_pure> Qi :=
  siPure_and.trans ⟨persistent_and_sep_1, and_intro sep_elim_l sep_elim_r⟩

@[rocq_alias si_pure_or]
theorem siPure_or [Sbi PROP] {Pi Qi : SiProp} :
    <si_pure> (Pi ∨ Qi) ⊣⊢@{PROP} <si_pure> Pi ∨ <si_pure> Qi := by
  refine ⟨?_, or_elim (siPure_mono or_intro_l) (siPure_mono or_intro_r)⟩
  calc iprop(<si_pure> (Pi ∨ Qi))
    _ ⊢ <si_pure> (∃ b : Bool, if b then Pi else Qi) := siPure_mono or_exists_bool.mp
    _ ⊢ ∃ b : Bool, <si_pure> (if b then Pi else Qi) := siPure_exist.mp
    _ ⊢ ∃ b : Bool, if b then <si_pure> Pi else <si_pure> Qi := exists_mono (·.casesOn .rfl .rfl)
    _ ⊢ <si_pure> Pi ∨ <si_pure> Qi := or_exists_bool.mpr

theorem pure_iff_exists_PLift [BI PROP] {φ : Prop} : ⌜φ⌝ ⊣⊢@{PROP} ∃ _ : PLift φ, True :=
  ⟨pure_elim' (exists_intro (Ψ := fun _ => iprop(True)) <| .up ·), exists_elim (pure_intro ·.down)⟩

theorem true_siPure [Sbi PROP] : True ⊢@{PROP} <si_pure> True :=
  calc iprop(True)
    _ ⊢ ∀ (_ : Empty), <si_pure> ⌜True⌝ := forall_intro nofun
    _ ⊢ <si_pure> ∀ (_ : Empty), ⌜True⌝ := siPure_forall_mpr
    _ ⊢ <si_pure> True := siPure_mono true_intro

@[rocq_alias si_pure_pure]
theorem siPure_pure [Sbi PROP] {φ : Prop} : <si_pure> ⌜φ⌝ ⊣⊢@{PROP} ⌜φ⌝ := by
  constructor
  · calc iprop(<si_pure> ⌜φ⌝)
      _ ⊢ <si_pure> (∃ _ : PLift φ, True) := siPure_mono pure_iff_exists_PLift.mp
      _ ⊢ ∃ _ : PLift φ, <si_pure> True := siPure_exist.mp
      _ ⊢ ∃ _ : PLift φ, True := exists_mono fun _ => true_intro
      _ ⊢ ⌜φ⌝ := pure_iff_exists_PLift.mpr
  · calc iprop(⌜φ⌝)
      _ ⊢ ∃ _ : PLift φ, True := pure_iff_exists_PLift.mp
      _ ⊢ ∃ _ : PLift φ, <si_pure> True := exists_mono fun _ => true_siPure
      _ ⊢ <si_pure> ∃ _ : PLift φ, True := siPure_exist.mpr
      _ ⊢ <si_pure> ⌜φ⌝ := siPure_mono pure_iff_exists_PLift.mpr

@[rocq_alias si_pure_impl]
theorem siPure_imp [Sbi PROP] {Pi Qi : SiProp} :
    <si_pure> (Pi → Qi) ⊣⊢@{PROP} (<si_pure> Pi → <si_pure> Qi) :=
  ⟨imp_intro' <| siPure_and.mpr.trans <| siPure_mono imp_elim_r, siPure_imp_mpr⟩

@[rocq_alias si_pure_impl_wand]
theorem siPure_imp_wand [Sbi PROP] {Pi Qi : SiProp} :
    <si_pure> (Pi → Qi) ⊣⊢@{PROP} (<si_pure> Pi -∗ <si_pure> Qi) := by
  refine ⟨wand_intro' ?_, (imp_intro' ?_).trans siPure_imp.mpr⟩
  · calc iprop(<si_pure> Pi ∗ <si_pure> (Pi → Qi))
      _ ⊢ <si_pure> (Pi ∧ (Pi → Qi)) := siPure_and_sep.mpr
      _ ⊢ <si_pure> Qi := siPure_mono imp_elim_r
  · calc iprop(<si_pure> Pi ∧ (<si_pure> Pi -∗ <si_pure> Qi))
      _ ⊢ <affine> <si_pure> Pi ∗ (<si_pure> Pi -∗ <si_pure> Qi) := persistent_and_affinely_sep_l.mp
      _ ⊢ <si_pure> Pi ∗ (<si_pure> Pi -∗ <si_pure> Qi) := sep_mono_l affinely_elim
      _ ⊢ <si_pure> Qi := wand_elim_r

@[rocq_alias si_pure_iff]
theorem siPure_iff [Sbi PROP] {Pi Qi : SiProp} :
    <si_pure> (Pi ↔ Qi) ⊣⊢@{PROP} (<si_pure> Pi ↔ <si_pure> Qi) :=
  siPure_and.trans (and_congr siPure_imp siPure_imp)

@[rocq_alias si_pure_impl_iff_wand]
theorem siPure_iff_wandIff [Sbi PROP] {Pi Qi : SiProp} :
    <si_pure> (Pi ↔ Qi) ⊣⊢@{PROP} (<si_pure> Pi ∗-∗ <si_pure> Qi) :=
  siPure_and.trans (and_congr siPure_imp_wand siPure_imp_wand)

@[rocq_alias si_pure_laterN]
theorem siPure_laterN [Sbi PROP] {n : Nat} {Pi : SiProp} :
    <si_pure> (▷^[n] Pi) ⊣⊢@{PROP} ▷^[n] <si_pure> Pi :=
  n.casesOn .rfl (fun _ => siPure_later.trans <| later_congr siPure_laterN)

@[rocq_alias si_pure_except_0]
theorem siPure_except0 [Sbi PROP] {Pi : SiProp} :
    <si_pure> (◇ Pi) ⊣⊢@{PROP} ◇ <si_pure> Pi := by
  show iprop(<si_pure> (▷ False ∨ Pi) ⊣⊢ ▷ False ∨ <si_pure> Pi)
  exact siPure_or.trans <|
    ⟨or_mono_l <| siPure_later.mp.trans <| later_mono siPure_pure.mp,
     or_mono_l <| (later_mono siPure_pure.mpr).trans siPure_later.mpr⟩

@[rocq_alias absorbingly_si_pure]
theorem absorbingly_siPure [Sbi PROP] {Pi : SiProp} :
    <absorb> <si_pure> Pi ⊣⊢@{PROP} <si_pure> Pi :=
  absorbing_absorbingly

@[rocq_alias persistently_si_pure]
theorem persistently_siPure [Sbi PROP] {Pi : SiProp} : <pers> <si_pure> Pi ⊣⊢@{PROP} <si_pure> Pi :=
  persistently_iff

@[rocq_alias si_pure_timeless]
instance siPure_timeless [Sbi PROP] (Pi : SiProp) [Timeless Pi] :
    Timeless (PROP := PROP) iprop(<si_pure> Pi) where
  timeless :=
    calc iprop(▷ <si_pure> Pi)
      _ ⊢ <si_pure> (▷ Pi) := siPure_later.mpr
      _ ⊢ <si_pure> (◇ Pi) := siPure_mono Timeless.timeless
      _ ⊢ ◇ <si_pure> Pi := siPure_except0.mp

-- Here

/-! ### Elimination of `siPure ∘ siEmpValid` -/

@[rocq_alias si_pure_si_emp_valid_elim]
theorem siPure_siEmpValid_elim [Sbi PROP] (P : PROP) [Absorbing P] :
    iprop(<si_pure> <si_emp_valid> P ⊢ P) :=
  siPure_siEmpValid.trans persistently_elim

@[rocq_alias affinely_si_pure_si_emp_valid]
theorem affinely_siPure_siEmpValid [Sbi PROP] (P : PROP) :
    iprop(<affine> <si_pure> <si_emp_valid> P ⊢ P) :=
  (siPure_siEmpValid |> affinely_mono).trans intuitionistically_elim

/-! ### Commuting rules of `siEmpValid` -/

@[rocq_alias si_emp_valid_affinely]
theorem siEmpValid_affinely [Sbi PROP] (P : PROP) :
    iprop(<si_emp_valid> (<affine> P) ⊣⊢@{SiProp} <si_emp_valid> P) :=
  ⟨siEmpValid_mono affinely_elim, siEmpValid_affinely_mpr⟩

@[rocq_alias si_emp_valid_persistently]
theorem siEmpValid_persistently [Sbi PROP] (P : PROP) :
    iprop(<si_emp_valid> (<pers> P) ⊣⊢@{SiProp} <si_emp_valid> P) := by
  constructor
  · exact (siEmpValid_affinely iprop(<pers> P)).mpr.trans <|
      siEmpValid_mono (show iprop(<affine> <pers> P ⊢ P) from intuitionistically_elim)
  · exact (siEmpValid_siPure (PROP := PROP)).mpr.trans <|
      siEmpValid_mono (siPure_siEmpValid)

@[rocq_alias si_emp_valid_intuitionistically]
theorem siEmpValid_intuitionistically [Sbi PROP] (P : PROP) :
    iprop(<si_emp_valid> (□ P) ⊣⊢@{SiProp} <si_emp_valid> P) :=
  (siEmpValid_affinely _).trans (siEmpValid_persistently _)

@[rocq_alias si_emp_valid_pure]
theorem siEmpValid_pure [Sbi PROP] (φ : Prop) :
    iprop(<si_emp_valid> (⌜φ⌝ : PROP) ⊣⊢@{SiProp} ⌜φ⌝) :=
  ⟨siEmpValid_mono (siPure_pure (PROP := PROP)).mpr |>.trans siEmpValid_siPure.mp,
   siEmpValid_siPure.mpr.trans <| siEmpValid_mono (siPure_pure (PROP := PROP)).mp⟩

@[rocq_alias si_emp_valid_emp]
theorem siEmpValid_emp [Sbi PROP] :
    iprop(<si_emp_valid> (emp : PROP) ⊣⊢@{SiProp} True) :=
  ⟨true_intro,
   calc iprop(True)
     _ ⊢@{SiProp} <si_emp_valid> (⌜True⌝ : PROP) := (siEmpValid_pure (PROP := PROP) _).mpr
     _ ⊢@{SiProp} <si_emp_valid> (<affine> (⌜True⌝ : PROP)) := siEmpValid_affinely_mpr
     _ ⊢@{SiProp} <si_emp_valid> (emp : PROP) :=
         siEmpValid_mono (affinely_true (PROP := PROP)).mp⟩

@[rocq_alias si_emp_valid_forall]
theorem siEmpValid_forall [Sbi PROP] {A : Type _} (Φ : A → PROP) :
    iprop(<si_emp_valid> (∀ x, Φ x) ⊣⊢@{SiProp} ∀ x, <si_emp_valid> Φ x) :=
  ⟨forall_intro fun x => siEmpValid_mono (forall_elim x),
   calc iprop(∀ x, <si_emp_valid> Φ x)
     _ ⊢@{SiProp} <si_emp_valid> <si_pure> (∀ x, <si_emp_valid> Φ x) :=
         (siEmpValid_siPure (PROP := PROP)).mpr
     _ ⊢@{SiProp} <si_emp_valid> (<affine> <si_pure> (∀ x, <si_emp_valid> Φ x)) :=
         siEmpValid_affinely_mpr
     _ ⊢@{SiProp} <si_emp_valid> (∀ x, Φ x) :=
         siEmpValid_mono <|
         (affinely_mono siPure_forall.mp).trans <|
         affinely_forall_1.trans <|
         forall_mono fun _ => affinely_siPure_siEmpValid _⟩

@[rocq_alias si_emp_valid_exist_2]
theorem siEmpValid_exist_mpr [Sbi PROP] {A : Type _} (Φ : A → PROP) :
    iprop((∃ x, <si_emp_valid> Φ x) ⊢@{SiProp} <si_emp_valid> (∃ x, Φ x)) :=
  exists_elim fun x => siEmpValid_mono (exists_intro x)

@[rocq_alias si_emp_valid_exist_1]
theorem siEmpValid_exist_mp [Sbi PROP] [SbiEmpValidExist PROP] {A : Type _} (Φ : A → PROP) :
    iprop(<si_emp_valid> (∃ x, Φ x) ⊢@{SiProp} ∃ x, <si_emp_valid> Φ x) :=
  (SbiEmpValidExist.siEmpValid_sExists_1 (fun p => ∃ a, Φ a = p)).trans <|
    exists_elim fun _ => pure_elim_l fun ⟨a, ha⟩ => ha ▸ exists_intro' a .rfl

@[rocq_alias si_emp_valid_exist]
theorem siEmpValid_exist [Sbi PROP] [SbiEmpValidExist PROP] {A : Type _} (Φ : A → PROP) :
    iprop(<si_emp_valid> (∃ x, Φ x) ⊣⊢@{SiProp} ∃ x, <si_emp_valid> Φ x) :=
  ⟨siEmpValid_exist_mp Φ, siEmpValid_exist_mpr Φ⟩

@[rocq_alias si_emp_valid_and]
theorem siEmpValid_and [Sbi PROP] (P Q : PROP) :
    iprop(<si_emp_valid> (P ∧ Q) ⊣⊢@{SiProp} <si_emp_valid> P ∧ <si_emp_valid> Q) :=
  ⟨and_intro (siEmpValid_mono and_elim_l) (siEmpValid_mono and_elim_r),
   ((and_forall_bool (PROP := SiProp) ..).mp.trans <|
     (forall_mono (·.casesOn .rfl .rfl)).trans <|
     (siEmpValid_forall _).mpr.trans <|
     siEmpValid_mono and_forall_bool.mpr)⟩

@[rocq_alias si_emp_valid_or_2]
theorem siEmpValid_or_mpr [Sbi PROP] (P Q : PROP) :
    iprop(<si_emp_valid> P ∨ <si_emp_valid> Q ⊢@{SiProp} <si_emp_valid> (P ∨ Q)) :=
  or_elim (siEmpValid_mono or_intro_l) (siEmpValid_mono or_intro_r)

@[rocq_alias si_emp_valid_or]
theorem siEmpValid_or [Sbi PROP] [SbiEmpValidExist PROP] (P Q : PROP) :
    iprop(<si_emp_valid> (P ∨ Q) ⊣⊢@{SiProp} <si_emp_valid> P ∨ <si_emp_valid> Q) :=
  ⟨calc iprop(<si_emp_valid> (P ∨ Q))
     _ ⊢@{SiProp} <si_emp_valid> (∃ b : Bool, if b then P else Q) :=
         siEmpValid_mono or_exists_bool.mp
     _ ⊢@{SiProp} ∃ b : Bool, <si_emp_valid> (if b then P else Q) := (siEmpValid_exist _).mp
     _ ⊢@{SiProp} ∃ b : Bool, if b then <si_emp_valid> P else <si_emp_valid> Q :=
         exists_mono (·.casesOn .rfl .rfl)
     _ ⊢@{SiProp} <si_emp_valid> P ∨ <si_emp_valid> Q := or_exists_bool.mpr,
   siEmpValid_or_mpr P Q⟩

@[rocq_alias si_emp_valid_impl_si_pure]
theorem siEmpValid_imp_siPure [Sbi PROP] (Pi : SiProp) (Q : PROP) :
    iprop((Pi → <si_emp_valid> Q) ⊢@{SiProp} <si_emp_valid> (<si_pure> Pi → Q)) :=
  calc iprop(Pi → <si_emp_valid> Q)
    _ ⊢@{SiProp} <si_emp_valid> <si_pure> (Pi → <si_emp_valid> Q) :=
        (siEmpValid_siPure (PROP := PROP)).mpr
    _ ⊢@{SiProp} <si_emp_valid> (<affine> <si_pure> (Pi → <si_emp_valid> Q)) :=
        (siEmpValid_affinely _).mpr
    _ ⊢@{SiProp} <si_emp_valid> (<si_pure> Pi → Q) :=
        siEmpValid_mono <| imp_intro' <|
        affinely_and_r.mp.trans <|
        (affinely_mono <| siPure_and.mpr.trans <| siPure_mono imp_elim_r).trans <|
        affinely_siPure_siEmpValid _

@[rocq_alias si_emp_valid_sep]
theorem siEmpValid_sep [Sbi PROP] [BIPositive PROP] (P Q : PROP) :
    iprop(<si_emp_valid> (P ∗ Q) ⊣⊢@{SiProp} <si_emp_valid> P ∧ <si_emp_valid> Q) := by
  constructor
  · exact calc iprop(<si_emp_valid> (P ∗ Q))
      _ ⊢@{SiProp} <si_emp_valid> (□ (P ∗ Q)) := (siEmpValid_intuitionistically _).mpr
      _ ⊢@{SiProp} <si_emp_valid> (□ P ∧ □ Q) :=
          siEmpValid_mono <| intuitionistically_sep.mp.trans and_sep_intuitionistically.mpr
      _ ⊢@{SiProp} <si_emp_valid> (□ P) ∧ <si_emp_valid> (□ Q) := (siEmpValid_and _ _).mp
      _ ⊢@{SiProp} <si_emp_valid> P ∧ <si_emp_valid> Q :=
          and_mono (siEmpValid_intuitionistically _).mp (siEmpValid_intuitionistically _).mp
  · exact calc iprop(<si_emp_valid> P ∧ <si_emp_valid> Q)
      _ ⊢@{SiProp} <si_emp_valid> (□ P) ∧ <si_emp_valid> (□ Q) :=
          and_mono (siEmpValid_intuitionistically _).mpr (siEmpValid_intuitionistically _).mpr
      _ ⊢@{SiProp} <si_emp_valid> (□ P ∧ □ Q) := (siEmpValid_and _ _).mpr
      _ ⊢@{SiProp} <si_emp_valid> (□ (P ∗ Q)) :=
          siEmpValid_mono <| and_sep_intuitionistically.mp.trans intuitionistically_sep.mpr
      _ ⊢@{SiProp} <si_emp_valid> (P ∗ Q) := (siEmpValid_intuitionistically _).mp

@[rocq_alias si_emp_valid_wand_si_pure]
theorem siEmpValid_wand_siPure [Sbi PROP] (Pi : SiProp) (Q : PROP) :
    iprop((Pi → <si_emp_valid> Q) ⊢@{SiProp} <si_emp_valid> (<affine> <si_pure> Pi -∗ Q)) :=
  (siEmpValid_imp_siPure Pi Q).trans <|
    siEmpValid_mono <| wand_intro' <| persistent_and_affinely_sep_l.mpr.trans imp_elim_r

@[rocq_alias si_emp_valid_later]
theorem siEmpValid_later [Sbi PROP] (P : PROP) :
    iprop(<si_emp_valid> (▷ P) ⊣⊢@{SiProp} ▷ <si_emp_valid> P) := by
  constructor
  · exact siEmpValid_later_mp
  · exact calc iprop(▷ <si_emp_valid> P)
      _ ⊢@{SiProp} <si_emp_valid> <si_pure> (▷ <si_emp_valid> P) :=
          (siEmpValid_siPure (PROP := PROP) ).mpr
      _ ⊢@{SiProp} <si_emp_valid> (<pers> (▷ P)) :=
          siEmpValid_mono <| (siPure_later).mp.trans <|
          (later_mono (siPure_siEmpValid)).trans later_persistently.mp
      _ ⊢@{SiProp} <si_emp_valid> (▷ P) := (siEmpValid_persistently _).mp

@[rocq_alias si_emp_valid_laterN]
theorem siEmpValid_laterN [Sbi PROP] (n : Nat) (P : PROP) :
    iprop(<si_emp_valid> (▷^[n] P) ⊣⊢@{SiProp} ▷^[n] <si_emp_valid> P) := by
  induction n with
  | zero => exact .rfl
  | succ n ih => exact (siEmpValid_later _).trans (later_congr ih)

@[rocq_alias si_emp_valid_except_0]
theorem siEmpValid_except0 [Sbi PROP] (P : PROP) :
    iprop(<si_emp_valid> (◇ P) ⊣⊢@{SiProp} ◇ <si_emp_valid> P) := by
  constructor
  · -- Step 1: introduce ▷ <si_emp_valid> P ∧ <si_emp_valid> ◇ P
    refine (and_intro ((siEmpValid_mono except0_into_later).trans (siEmpValid_later _).mp) .rfl).trans ?_
    -- Step 2: apply later_false_em to first conjunct, distribute with and_or_r
    refine (and_mono_l later_false_em).trans <| and_or_r.mp.trans ?_
    -- Step 3: or_elim
    refine or_elim (or_intro_l' and_elim_l) ?_
    -- Step 4: right disjunct
    refine or_intro_r' ?_
    -- Goal: (▷ False → <si_emp_valid> P) ∧ <si_emp_valid> ◇ P ⊢ <si_emp_valid> P
    refine (and_mono_l (siEmpValid_imp_siPure _ _)).trans <| (siEmpValid_and _ _).mpr.trans ?_
    -- Goal: <si_emp_valid> ((<si_pure> ▷ False → P) ∧ ◇ P) ⊢ <si_emp_valid> P
    refine siEmpValid_mono ?_
    -- Goal: (<si_pure> ▷ False → P) ∧ ◇ P ⊢ P
    -- Replace <si_pure> ▷ False with ▷ False via siPure_later and siPure_pure
    have hrepl : iprop(<si_pure> (▷ (False : SiProp)) ⊣⊢@{PROP} ▷ False) :=
      (siPure_later).trans (later_congr siPure_pure)
    refine (and_mono_l (imp_mono_l hrepl.mpr)).trans ?_
    -- Goal: (▷ False → P) ∧ (▷ False ∨ P) ⊢ P
    exact and_or_l.mp.trans <| or_elim imp_elim_l and_elim_r
  · show iprop(▷ False ∨ <si_emp_valid> P ⊢ <si_emp_valid> (▷ False ∨ P))
    exact (or_mono_l <| (later_mono (siEmpValid_pure (PROP := PROP) _).mpr).trans
      (siEmpValid_later _).mpr).trans <| siEmpValid_or_mpr _ _

@[rocq_alias si_emp_valid_timeless]
instance siEmpValid_timeless [Sbi PROP] (P : PROP) [Timeless P] :
    Timeless iprop(<si_emp_valid> P) where
  timeless := by
    rw [show iprop(▷ <si_emp_valid> P) = iprop(▷ <si_emp_valid> P) from rfl]
    exact calc iprop(▷ <si_emp_valid> P)
      _ ⊢@{SiProp} <si_emp_valid> (▷ P) := (siEmpValid_later _).mpr
      _ ⊢@{SiProp} <si_emp_valid> (◇ P) := siEmpValid_mono Timeless.timeless
      _ ⊢@{SiProp} ◇ <si_emp_valid> P := (siEmpValid_except0 _).mp

/-! ### Relating `⊢` in `SiProp` to `⊢` in `PROP` -/

@[rocq_alias si_emp_valid_emp_valid]
theorem siEmpValid_emp_valid [Sbi PROP] (P : PROP) :
    (emp ⊢@{SiProp} iprop(<si_emp_valid> P)) ↔ (emp ⊢ P) := by
  constructor
  · intro h
    exact calc iprop(emp : PROP)
      _ ⊢@{PROP} <affine> True := (affinely_true (PROP := PROP)).mpr
      _ ⊢@{PROP} <affine> <si_pure> ⌜True⌝ := affinely_mono (siPure_pure (PROP := PROP)).mpr
      _ ⊢@{PROP} <affine> <si_pure> emp :=
          affinely_mono <| siPure_mono (true_emp (PROP := SiProp)).mp
      _ ⊢@{PROP} <affine> <si_pure> <si_emp_valid> P := affinely_mono (siPure_mono h)
      _ ⊢@{PROP} P := affinely_siPure_siEmpValid _
  · intro h
    exact (siEmpValid_emp (PROP := PROP)).mpr.trans <| siEmpValid_mono h

@[rocq_alias si_pure_emp_valid]
theorem siPure_emp_valid [Sbi PROP] (Pi : SiProp) :
    (emp ⊢@{PROP} iprop(<si_pure> Pi)) ↔ (emp ⊢@{SiProp} Pi) :=
  ⟨fun h => (siEmpValid_emp_valid (PROP := PROP) _).mpr h |>.trans
      (siEmpValid_siPure (PROP := PROP)).mp,
   fun h => (siEmpValid_emp_valid (PROP := PROP) _).mp <|
      h.trans (siEmpValid_siPure (PROP := PROP)).mpr⟩

@[rocq_alias si_pure_entails]
theorem siPure_entails [Sbi PROP] (Pi Qi : SiProp) :
    (iprop(<si_pure> Pi ⊢@{PROP} <si_pure> Qi)) ↔ (Pi ⊢@{SiProp} Qi) := by
  constructor
  · intro h
    exact calc iprop(Pi)
      _ ⊢@{SiProp} <si_emp_valid> <si_pure> Pi := (siEmpValid_siPure (PROP := PROP)).mpr
      _ ⊢@{SiProp} <si_emp_valid> <si_pure> Qi := siEmpValid_mono h
      _ ⊢@{SiProp} Qi := (siEmpValid_siPure (PROP := PROP)).mp
  · exact siPure_mono

@[rocq_alias si_pure_inj]
theorem siPure_inj [Sbi PROP] {Pi Qi : SiProp}
    (h : iprop(<si_pure> Pi ⊣⊢@{PROP} <si_pure> Qi)) : Pi ⊣⊢ Qi :=
  ⟨(siPure_entails (PROP := PROP) _ _).mp h.mp, (siPure_entails (PROP := PROP) _ _).mp h.mpr⟩

/-! ### Soundness -/

@[rocq_alias sbi_pure_soundness]
theorem pure_soundness [Sbi PROP] {φ : Prop} (h : emp ⊢@{PROP} ⌜φ⌝) : φ :=
  SiProp.pure_soundness ((siPure_emp_valid (PROP := PROP) _).mp <|
    h.trans (siPure_pure (PROP := PROP)).mpr)

@[rocq_alias sbi_later_soundness]
theorem later_soundness [Sbi PROP] {P : PROP} (h : emp ⊢ ▷ P) : emp ⊢ P :=
  (siEmpValid_emp_valid (PROP := PROP) _).mp <|
    SiProp.later_soundness <|
    (siEmpValid_emp_valid (PROP := PROP) _).mpr h |>.trans <| (siEmpValid_later _).mp

@[rocq_alias laterN_soundness]
theorem laterN_soundness [Sbi PROP] {P : PROP} (n : Nat) (h : emp ⊢ ▷^[n] P) : emp ⊢ P := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih (later_soundness h)

end Iris
