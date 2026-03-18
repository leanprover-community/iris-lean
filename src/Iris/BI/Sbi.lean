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

/-- Step-indexed validity of BI propositions. -/
class SiEmpValid (PROP : Type _) where
  siEmpValid : PROP → SiProp

export SiPure (siPure)
export SiEmpValid (siEmpValid)

syntax "<si_pure> " term:40 : term
syntax "<si_emp_valid> " term:40 : term

macro_rules
  | `(iprop(<si_pure> $P)) => ``(SiPure.siPure iprop($P))
  | `(iprop(<si_emp_valid> $P)) => ``(SiEmpValid.siEmpValid iprop($P))

delab_rule SiPure.siPure
  | `($_ $P) => do ``(iprop(<si_pure> $(← BI.unpackIprop P)))

delab_rule SiEmpValid.siEmpValid
  | `($_ $P) => do ``(iprop(<si_emp_valid> $(← BI.unpackIprop P)))

/-- The `Sbi` class: a BI with step-indexed structure. -/
@[rocq_alias Sbi]
class Sbi (PROP : Type _) extends BI PROP, SiPure PROP, SiEmpValid PROP where
  siPure_ne : NonExpansive (α := SiProp) (β := PROP) SiPure.siPure
  siEmpValid_ne : NonExpansive (α := PROP) (β := SiProp) SiEmpValid.siEmpValid
  siPure_mono {Pi Qi : SiProp} (H : Pi ⊢@{SiProp} Qi) :
    iprop(<si_pure> Pi ⊢@{PROP} <si_pure> Qi)
  siEmpValid_mono {P Q : PROP} (H : P ⊢@{PROP} Q) :
    iprop(<si_emp_valid> P ⊢@{SiProp} <si_emp_valid> Q)
  siEmpValid_siPure (Pi : SiProp) :
    iprop(<si_emp_valid> (<si_pure> Pi : PROP) ⊣⊢@{SiProp} Pi)
  siPure_siEmpValid (P : PROP) :
    iprop(<si_pure> <si_emp_valid> P ⊢ <pers> P)
  siPure_impl_2 (Pi Qi : SiProp) :
    iprop((<si_pure> Pi → <si_pure> Qi) ⊢@{PROP} <si_pure> (Pi → Qi))
  siPure_forall_2 {A : Type _} (Φi : A → SiProp) :
    iprop((∀ x, <si_pure> Φi x) ⊢@{PROP} <si_pure> (∀ x, Φi x))
  persistently_impl_siPure (Pi : SiProp) (Q : PROP) :
    iprop((<si_pure> Pi → <pers> Q) ⊢ <pers> (<si_pure> Pi → Q))
  siPure_later (Pi : SiProp) :
    iprop(<si_pure> (▷ Pi) ⊣⊢@{PROP} ▷ <si_pure> Pi)
  siPure_absorbing (Pi : SiProp) :
    Absorbing (PROP := PROP) iprop(<si_pure> Pi)
  siEmpValid_later_1 (P : PROP) :
    iprop(<si_emp_valid> (▷ P) ⊢@{SiProp} ▷ <si_emp_valid> P)
  siEmpValid_affinely_2 (P : PROP) :
    iprop(<si_emp_valid> P ⊢@{SiProp} <si_emp_valid> (<affine> P))
  prop_ext_siEmpValid_2 (P Q : PROP) :
    iprop(<si_emp_valid> (P ∗-∗ Q) ⊢@{SiProp} SiProp.internalEq P Q)

attribute [instance] Sbi.siPure_ne Sbi.siEmpValid_ne Sbi.siPure_absorbing

export Sbi (siPure_mono siEmpValid_mono siEmpValid_siPure siPure_siEmpValid siPure_impl_2
  persistently_impl_siPure siPure_later siEmpValid_later_1 siEmpValid_affinely_2
  prop_ext_siEmpValid_2)

/-- `SbiEmpValidExist` generalizes that plainly commutes with existentials and disjunction. -/
@[rocq_alias SbiEmpValidExist]
class SbiEmpValidExist (PROP : Type _) [BI PROP] [SiEmpValid PROP] where
  siEmpValid_exists_1 {A : Type _} (Φ : A → PROP) :
    iprop(<si_emp_valid> (∃ x, Φ x) ⊢@{SiProp} ∃ x, <si_emp_valid> Φ x)

/-! ## siProp SBI instance -/

@[rocq_alias siprop_sbi]
instance instSbiSiProp : Sbi SiProp where
  toSiPure := ⟨id⟩
  toSiEmpValid := ⟨id⟩
  siPure_ne := id_ne
  siEmpValid_ne := id_ne
  siPure_mono h := h
  siEmpValid_mono h := h
  siEmpValid_siPure _ := .rfl
  siPure_siEmpValid _ _ h := h
  siPure_impl_2 _ _ := .rfl
  siPure_forall_2 _ := .rfl
  persistently_impl_siPure _ _ _ h := h
  siPure_later _ := .rfl
  siPure_absorbing _ := ⟨fun _ h => h.2⟩
  siEmpValid_later_1 _ := .rfl
  siEmpValid_affinely_2 _ _ h := ⟨trivial, h⟩
  prop_ext_siEmpValid_2 P Q := SiProp.prop_ext P Q

@[rocq_alias siprop_sbi_emp_valid_exist]
instance instSbiEmpValidExistSiProp : SbiEmpValidExist SiProp where
  siEmpValid_exists_1 _ := .rfl

/-! ## Derived laws -/

/-! ### Persistent -/

@[rocq_alias si_pure_persistent]
instance siPure_persistent [Sbi PROP] (Pi : SiProp) :
    Persistent (PROP := PROP) iprop(<si_pure> Pi) where
  persistent :=
    calc   iprop(<si_pure> Pi)
      _ ⊢@{PROP} <si_pure> <si_emp_valid> <si_pure> Pi := siPure_mono (siEmpValid_siPure Pi).mpr
      _ ⊢@{PROP} <pers> <si_pure> Pi := siPure_siEmpValid _

/-! ### Commuting rules of `siPure` -/

@[rocq_alias si_pure_forall]
theorem siPure_forall [Sbi PROP] {A : Type _} (Φi : A → SiProp) :
    iprop(<si_pure> (∀ x, Φi x) ⊣⊢@{PROP} ∀ x, <si_pure> Φi x) := by
  refine ⟨forall_intro fun x => siPure_mono (forall_elim x), ?_⟩
  sorry
  -- refine @Sbi.siPure_forall_2 (PROP := PROP) _ _ _

@[rocq_alias si_pure_exist]
theorem siPure_exist [Sbi PROP] {A : Type _} (Φi : A → SiProp) :
    iprop(<si_pure> (∃ x, Φi x) ⊣⊢@{PROP} ∃ x, <si_pure> Φi x) := by
  refine ⟨?_, exists_elim fun x => siPure_mono (exists_intro x)⟩
  exact (siPure_mono <| exists_elim fun x =>
    (siEmpValid_siPure (PROP := PROP) (Φi x)).mpr.trans
      (siEmpValid_mono (exists_intro (Ψ := fun x => iprop(<si_pure> Φi x)) x))).trans <|
    (siPure_siEmpValid _).trans persistently_elim

@[rocq_alias si_pure_and]
theorem siPure_and [Sbi PROP] (Pi Qi : SiProp) :
    iprop(<si_pure> (Pi ∧ Qi) ⊣⊢@{PROP} <si_pure> Pi ∧ <si_pure> Qi) :=
  -- ⟨and_intro (siPure_mono and_elim_l) (siPure_mono and_elim_r),
  --  (and_forall_bool ...).mp.trans <|
  --    (forall_intro fun b => (forall_elim b).trans (by cases b <;> exact .rfl)).trans <|
  --    (Sbi.siPure_forall_2 (fun b : Bool => if b then Pi else Qi)).trans <|
  --    siPure_mono (and_forall_bool (P := Pi) (Q := Qi)).mpr⟩
  sorry

@[rocq_alias si_pure_and_sep]
theorem siPure_and_sep [Sbi PROP] (Pi Qi : SiProp) :
    iprop(<si_pure> (Pi ∧ Qi) ⊣⊢@{PROP} <si_pure> Pi ∗ <si_pure> Qi) :=
  (siPure_and _ _).trans ⟨persistent_and_sep_1, and_intro sep_elim_l sep_elim_r⟩

@[rocq_alias si_pure_or]
theorem siPure_or [Sbi PROP] (Pi Qi : SiProp) :
    iprop(<si_pure> (Pi ∨ Qi) ⊣⊢@{PROP} <si_pure> Pi ∨ <si_pure> Qi) :=
  ⟨(siPure_mono or_exists_bool.mp).trans <|
     (siPure_exist _).mp.trans <|
     (exists_mono (·.casesOn .rfl .rfl)).trans or_exists_bool.mpr,
   or_elim (siPure_mono or_intro_l) (siPure_mono or_intro_r)⟩

@[rocq_alias si_pure_pure]
theorem siPure_pure [Sbi PROP] (φ : Prop) :
    iprop(<si_pure> ⌜φ⌝ ⊣⊢@{PROP} ⌜φ⌝) := by
  -- have pure_alt : ∀ (PROP' : Type _) [BI PROP'] , iprop(⌜φ⌝ ⊣⊢@{PROP'} ∃ _ : φ, True) :=
  --   fun _ _ => ⟨pure_elim' fun h => (exists_intro (Ψ := fun _ : φ => True) h) true_intro,
  --    exists_elim fun h => pure_intro h⟩
  -- rw [pure_alt PROP, pure_alt SiProp]
  -- refine (siPure_exist _).trans (exists_congr fun _ => ⟨true_intro, ?_⟩)
  -- exact (forall_intro (α := Empty) nofun).trans <|
  --   (Sbi.siPure_forall_2 (fun _ : Empty => True)).trans <| siPure_mono true_intro
  sorry

@[rocq_alias si_pure_impl]
theorem siPure_impl [Sbi PROP] (Pi Qi : SiProp) :
    iprop(<si_pure> (Pi → Qi) ⊣⊢@{PROP} (<si_pure> Pi → <si_pure> Qi)) :=
  ⟨imp_intro' <| (siPure_and _ _).mpr.trans <| siPure_mono imp_elim_r,
   siPure_impl_2 Pi Qi⟩

@[rocq_alias si_pure_impl_wand]
theorem siPure_impl_wand [Sbi PROP] (Pi Qi : SiProp) :
    iprop(<si_pure> (Pi → Qi) ⊣⊢@{PROP} (<si_pure> Pi -∗ <si_pure> Qi)) :=
  ⟨wand_intro' <| (siPure_and_sep _ _).mpr.trans <| siPure_mono imp_elim_r,
   (imp_intro' <| persistent_and_affinely_sep_l.mp.trans <|
     (sep_mono_l affinely_elim).trans wand_elim_r).trans (siPure_impl _ _).mpr⟩

@[rocq_alias si_pure_iff]
theorem siPure_iff [Sbi PROP] (Pi Qi : SiProp) :
    iprop(<si_pure> (Pi ↔ Qi) ⊣⊢@{PROP} (<si_pure> Pi ↔ <si_pure> Qi)) :=
  (siPure_and _ _).trans (and_congr (siPure_impl _ _) (siPure_impl _ _))

@[rocq_alias si_pure_impl_iff_wand]
theorem siPure_impl_iff_wand [Sbi PROP] (Pi Qi : SiProp) :
    iprop(<si_pure> (Pi ↔ Qi) ⊣⊢@{PROP} (<si_pure> Pi ∗-∗ <si_pure> Qi)) :=
  (siPure_and _ _).trans (and_congr (siPure_impl_wand _ _) (siPure_impl_wand _ _))

@[rocq_alias si_pure_laterN]
theorem siPure_laterN [Sbi PROP] (n : Nat) (Pi : SiProp) :
    iprop(<si_pure> (▷^[n] Pi) ⊣⊢@{PROP} ▷^[n] <si_pure> Pi) := by
  induction n with
  | zero => exact .rfl
  | succ n ih => exact (siPure_later _).trans (later_congr ih)

@[rocq_alias si_pure_except_0]
theorem siPure_except0 [Sbi PROP] (Pi : SiProp) :
    iprop(<si_pure> (◇ Pi) ⊣⊢@{PROP} ◇ <si_pure> Pi) := by
  show iprop(<si_pure> (▷ False ∨ Pi) ⊣⊢ ▷ False ∨ <si_pure> Pi)
  exact (siPure_or _ _).trans <|
    ⟨or_mono_l <| (siPure_later _).mp.trans <| later_mono (siPure_pure _).mp,
     or_mono_l <| (later_mono (siPure_pure _).mpr).trans (siPure_later _).mpr⟩

@[rocq_alias absorbingly_si_pure]
theorem absorbingly_siPure [Sbi PROP] (Pi : SiProp) :
    iprop(<absorb> <si_pure> Pi ⊣⊢@{PROP} <si_pure> Pi) :=
  absorbing_absorbingly

@[rocq_alias persistently_si_pure]
theorem persistently_siPure [Sbi PROP] (Pi : SiProp) :
    iprop(<pers> <si_pure> Pi ⊣⊢@{PROP} <si_pure> Pi) :=
  persistently_iff

@[rocq_alias si_pure_timeless]
instance siPure_timeless [Sbi PROP] (Pi : SiProp) [Timeless Pi] :
    Timeless (PROP := PROP) iprop(<si_pure> Pi) where
  timeless := by
    rw [show iprop(▷ <si_pure> Pi) = iprop(▷ <si_pure> Pi) from rfl]
    exact (siPure_later _).mpr.trans <| (siPure_mono Timeless.timeless).trans (siPure_except0 _).mp

/-! ### Elimination of `siPure ∘ siEmpValid` -/

@[rocq_alias si_pure_si_emp_valid_elim]
theorem siPure_siEmpValid_elim [Sbi PROP] (P : PROP) [Absorbing P] :
    iprop(<si_pure> <si_emp_valid> P ⊢ P) :=
  (siPure_siEmpValid P).trans persistently_elim

@[rocq_alias affinely_si_pure_si_emp_valid]
theorem affinely_siPure_siEmpValid [Sbi PROP] (P : PROP) :
    iprop(<affine> <si_pure> <si_emp_valid> P ⊢ P) :=
  (siPure_siEmpValid P |> affinely_mono).trans intuitionistically_elim

/-! ### Commuting rules of `siEmpValid` -/

@[rocq_alias si_emp_valid_affinely]
theorem siEmpValid_affinely [Sbi PROP] (P : PROP) :
    iprop(<si_emp_valid> (<affine> P) ⊣⊢@{SiProp} <si_emp_valid> P) :=
  ⟨siEmpValid_mono affinely_elim, siEmpValid_affinely_2 P⟩

@[rocq_alias si_emp_valid_persistently]
theorem siEmpValid_persistently [Sbi PROP] (P : PROP) :
    iprop(<si_emp_valid> (<pers> P) ⊣⊢@{SiProp} <si_emp_valid> P) := by
  constructor
  · exact (siEmpValid_affinely iprop(<pers> P)).mpr.trans <|
      siEmpValid_mono (show iprop(<affine> <pers> P ⊢ P) from intuitionistically_elim)
  · exact (siEmpValid_siPure (PROP := PROP) _).mpr.trans <|
      siEmpValid_mono (siPure_siEmpValid P)

@[rocq_alias si_emp_valid_intuitionistically]
theorem siEmpValid_intuitionistically [Sbi PROP] (P : PROP) :
    iprop(<si_emp_valid> (□ P) ⊣⊢@{SiProp} <si_emp_valid> P) :=
  (siEmpValid_affinely _).trans (siEmpValid_persistently _)

@[rocq_alias si_emp_valid_pure]
theorem siEmpValid_pure [Sbi PROP] (φ : Prop) :
    iprop(<si_emp_valid> (⌜φ⌝ : PROP) ⊣⊢@{SiProp} ⌜φ⌝) :=
  ⟨siEmpValid_mono (siPure_pure (PROP := PROP) φ).mpr |>.trans (siEmpValid_siPure _).mp,
   (siEmpValid_siPure _).mpr.trans <| siEmpValid_mono (siPure_pure (PROP := PROP) φ).mp⟩

@[rocq_alias si_emp_valid_emp]
theorem siEmpValid_emp [Sbi PROP] :
    iprop(<si_emp_valid> (emp : PROP) ⊣⊢@{SiProp} True) :=
  ⟨true_intro,
   (siEmpValid_pure (PROP := PROP) _).mpr.trans <|
     (siEmpValid_affinely_2 _).trans <|
     siEmpValid_mono (affinely_true (PROP := PROP)).mp⟩

universe u_sbi₂ u_a₂ in
@[rocq_alias si_emp_valid_forall]
theorem siEmpValid_forall {PROP : Type u_sbi₂} [Sbi PROP] {A : Type u_a₂} (Φ : A → PROP) :
    iprop(<si_emp_valid> (∀ x, Φ x) ⊣⊢@{SiProp} ∀ x, <si_emp_valid> Φ x) :=
  -- ⟨forall_intro fun x => siEmpValid_mono (forall_elim x),
  --  (siEmpValid_siPure (PROP := PROP) _).mpr.trans <|
  --    (siEmpValid_mono <| (siPure_forall _).mp.trans <|
  --      forall_mono fun _ => affinely_siPure_siEmpValid _)⟩
  sorry

@[rocq_alias si_emp_valid_exist_2]
theorem siEmpValid_exist_2 [Sbi PROP] {A : Type _} (Φ : A → PROP) :
    iprop((∃ x, <si_emp_valid> Φ x) ⊢@{SiProp} <si_emp_valid> (∃ x, Φ x)) :=
  exists_elim fun x => siEmpValid_mono (exists_intro x)

universe u_sbi₃ u_a₃ in
@[rocq_alias si_emp_valid_exist]
theorem siEmpValid_exist {PROP : Type u_sbi₃} [Sbi PROP]
    [@SbiEmpValidExist.{u_sbi₃, u_a₃} PROP _ _] {A : Type u_a₃} (Φ : A → PROP) :
    iprop(<si_emp_valid> (∃ x, Φ x) ⊣⊢@{SiProp} ∃ x, <si_emp_valid> Φ x) :=
  ⟨SbiEmpValidExist.siEmpValid_exists_1 Φ, siEmpValid_exist_2 Φ⟩

@[rocq_alias si_emp_valid_and]
theorem siEmpValid_and [Sbi PROP] (P Q : PROP) :
    iprop(<si_emp_valid> (P ∧ Q) ⊣⊢@{SiProp} <si_emp_valid> P ∧ <si_emp_valid> Q) :=
  ⟨and_intro (siEmpValid_mono and_elim_l) (siEmpValid_mono and_elim_r),
   and_forall_bool (PROP := SiProp).mp.trans <|
     (forall_mono (·.casesOn .rfl .rfl)).trans <|
     (siEmpValid_forall _).mpr.trans <|
     siEmpValid_mono and_forall_bool.mpr⟩

@[rocq_alias si_emp_valid_or_2]
theorem siEmpValid_or_2 [Sbi PROP] (P Q : PROP) :
    iprop(<si_emp_valid> P ∨ <si_emp_valid> Q ⊢@{SiProp} <si_emp_valid> (P ∨ Q)) :=
  or_elim (siEmpValid_mono or_intro_l) (siEmpValid_mono or_intro_r)

universe u_sbi₄ in
@[rocq_alias si_emp_valid_or]
theorem siEmpValid_or {PROP : Type u_sbi₄} [Sbi PROP]
    [@SbiEmpValidExist.{u_sbi₄, 0} PROP _ _] (P Q : PROP) :
    iprop(<si_emp_valid> (P ∨ Q) ⊣⊢@{SiProp} <si_emp_valid> P ∨ <si_emp_valid> Q) :=
  ⟨(siEmpValid_mono or_exists_bool.mp).trans <|
     (siEmpValid_exist _).mp.trans <|
     (exists_mono (·.casesOn .rfl .rfl)).trans or_exists_bool.mpr,
   siEmpValid_or_2 P Q⟩

@[rocq_alias si_emp_valid_impl_si_pure]
theorem siEmpValid_impl_siPure [Sbi PROP] (Pi : SiProp) (Q : PROP) :
    iprop((Pi → <si_emp_valid> Q) ⊢@{SiProp} <si_emp_valid> (<si_pure> Pi → Q)) :=
  (siEmpValid_siPure (PROP := PROP) _).mpr.trans <|
    (siEmpValid_affinely _).mpr.trans <|
    siEmpValid_mono <| imp_intro' <|
    affinely_and_r.mp.trans <|
    (affinely_mono <| (siPure_and _ _).mpr.trans <| siPure_mono imp_elim_r).trans <|
    affinely_siPure_siEmpValid _

@[rocq_alias si_emp_valid_sep]
theorem siEmpValid_sep [Sbi PROP] [BIPositive PROP] (P Q : PROP) :
    iprop(<si_emp_valid> (P ∗ Q) ⊣⊢@{SiProp} <si_emp_valid> P ∧ <si_emp_valid> Q) := by
  sorry

@[rocq_alias si_emp_valid_wand_si_pure]
theorem siEmpValid_wand_siPure [Sbi PROP] (Pi : SiProp) (Q : PROP) :
    iprop((Pi → <si_emp_valid> Q) ⊢@{SiProp} <si_emp_valid> (<affine> <si_pure> Pi -∗ Q)) := by
  sorry

@[rocq_alias si_emp_valid_later]
theorem siEmpValid_later [Sbi PROP] (P : PROP) :
    iprop(<si_emp_valid> (▷ P) ⊣⊢@{SiProp} ▷ <si_emp_valid> P) := by
  constructor
  · exact siEmpValid_later_1 P
  · exact (siEmpValid_siPure (PROP := PROP) _).mpr.trans <|
      (siEmpValid_mono <| (siPure_later _).mp.trans <|
        (later_mono (siPure_siEmpValid P)).trans later_persistently.mp).trans <|
      (siEmpValid_persistently _).mp

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
  · sorry
  · show iprop(▷ False ∨ <si_emp_valid> P ⊢ <si_emp_valid> (▷ False ∨ P))
    exact (or_mono_l <| (later_mono (siEmpValid_pure (PROP := PROP) _).mpr).trans
      (siEmpValid_later _).mpr).trans <| siEmpValid_or_2 _ _

@[rocq_alias si_emp_valid_timeless]
instance siEmpValid_timeless [Sbi PROP] (P : PROP) [Timeless P] :
    Timeless iprop(<si_emp_valid> P) where
  timeless := by
    rw [show iprop(▷ <si_emp_valid> P) = iprop(▷ <si_emp_valid> P) from rfl]
    exact (siEmpValid_later _).mpr.trans <| (siEmpValid_mono Timeless.timeless).trans <|
      (siEmpValid_except0 _).mp

/-! ### Relating `⊢` in `SiProp` to `⊢` in `PROP` -/

@[rocq_alias si_emp_valid_emp_valid]
theorem siEmpValid_emp_valid [Sbi PROP] (P : PROP) :
    (emp ⊢@{SiProp} iprop(<si_emp_valid> P)) ↔ (emp ⊢ P) := by
  constructor
  · intro h
    sorry
  · intro h
    exact (siEmpValid_emp (PROP := PROP)).mpr.trans <| siEmpValid_mono h

@[rocq_alias si_pure_emp_valid]
theorem siPure_emp_valid [Sbi PROP] (Pi : SiProp) :
    (emp ⊢@{PROP} iprop(<si_pure> Pi)) ↔ (emp ⊢@{SiProp} Pi) :=
  ⟨fun h => (siEmpValid_emp_valid (PROP := PROP) _).mpr h |>.trans
      (siEmpValid_siPure (PROP := PROP) Pi).mp,
   fun h => (siEmpValid_emp_valid (PROP := PROP) _).mp <|
      h.trans (siEmpValid_siPure (PROP := PROP) Pi).mpr⟩

@[rocq_alias si_pure_entails]
theorem siPure_entails [Sbi PROP] (Pi Qi : SiProp) :
    (iprop(<si_pure> Pi ⊢@{PROP} <si_pure> Qi)) ↔ (Pi ⊢@{SiProp} Qi) := by
  constructor
  · intro h
    exact (siEmpValid_siPure (PROP := PROP) Pi).mpr.trans <|
      (siEmpValid_mono h).trans (siEmpValid_siPure (PROP := PROP) Qi).mp
  · exact siPure_mono

/-! ### Soundness -/

@[rocq_alias sbi_pure_soundness]
theorem pure_soundness [Sbi PROP] {φ : Prop} (h : emp ⊢@{PROP} ⌜φ⌝) : φ := by
  exact SiProp.pure_soundness ((siPure_emp_valid (PROP := PROP) _).mp <|
    h.trans (siPure_pure (PROP := PROP) φ).mpr)

@[rocq_alias sbi_later_soundness]
theorem later_soundness [Sbi PROP] {P : PROP} (h : emp ⊢ ▷ P) : emp ⊢ P := by
  exact (siEmpValid_emp_valid (PROP := PROP) _).mp <|
    SiProp.later_soundness <|
    (siEmpValid_emp_valid (PROP := PROP) _).mpr h |>.trans <| (siEmpValid_later _).mp

@[rocq_alias laterN_soundness]
theorem laterN_soundness [Sbi PROP] {P : PROP} (n : Nat) (h : emp ⊢ ▷^[n] P) : emp ⊢ P := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih (later_soundness h)

end Iris
