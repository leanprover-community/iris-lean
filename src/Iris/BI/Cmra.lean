/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.BI.Sbi
public import Iris.BI.Plainly
public import Iris.BI.InternalEq
public import Iris.Std.RocqAlias

@[expose] public section

/-!
# Generic CMRA validity in a BI logic

This file defines the generic internal CMRA validity for any `Sbi PROP`,
as `<si_pure> cmraValid a`.
-/

namespace Iris
open BI OFE SiProp CMRA Sbi

section CmraValid

variable [Sbi PROP] [CMRA A]

@[rocq_alias internal_cmra_valid]
def internalCmraValid (a : A) : PROP := siPure (cmraValid a)

@[rocq_alias internal_cmra_valid_ne]
instance internalCmraValid_ne : NonExpansive (internalCmraValid (PROP := PROP) (A := A)) where
  ne _ _ _ h := siPure_ne.ne (instNonExpansiveCmraValid.ne h)

@[rocq_alias internal_cmra_valid_intro]
theorem internalCmraValid_intro {P : PROP} {a : A} (h : Valid a) :
    P ⊢ internalCmraValid a :=
  calc (P : PROP)
    _ ⊢ True := true_intro
    _ ⊢ <si_pure> True := siPure_pure.mpr
    _ ⊢ internalCmraValid a := siPure_mono (cmraValid_intro h)

@[rocq_alias internal_cmra_valid_elim]
theorem internalCmraValid_elim (a : A) : internalCmraValid a ⊢@{PROP} ⌜✓{0} a⌝ :=
  calc internalCmraValid a
    _ ⊢ <si_pure> ⌜✓{0} a⌝ := siPure_mono cmraValid_elim
    _ ⊢ ⌜✓{0} a⌝ := siPure_pure.mp

@[rocq_alias internal_cmra_valid_weaken]
theorem internalCmraValid_weaken {a b : A} :
    internalCmraValid (a • b) ⊢@{PROP} internalCmraValid a :=
  siPure_mono cmraValid_weaken

@[rocq_alias internal_cmra_valid_entails]
theorem internalCmraValid_entails [CMRA B] {a : A} {b : B} :
    (internalCmraValid a ⊢@{PROP} internalCmraValid b) ↔ ∀ n, ✓{n} a → ✓{n} b :=
  siPure_entails.trans cmraValid_entails_iff

@[rocq_alias si_pure_internal_cmra_valid]
theorem siPure_internalCmraValid {a : A} : <si_pure> cmraValid a ⊣⊢@{PROP} internalCmraValid a :=
  .rfl

@[rocq_alias persistently_internal_cmra_valid]
theorem persistently_internalCmraValid {a : A} :
    <pers> internalCmraValid a ⊣⊢@{PROP} internalCmraValid a :=
  persistently_siPure

@[rocq_alias plainly_internal_cmra_valid]
theorem plainly_internalCmraValid (a : A) :
    ■ internalCmraValid a ⊣⊢@{PROP} internalCmraValid a :=
  plainly_siPure

@[rocq_alias intuitionistically_internal_cmra_valid]
theorem intuitionistically_internalCmraValid [BIAffine PROP] {a : A} :
    □ internalCmraValid a ⊣⊢@{PROP} internalCmraValid a :=
  intuitionistically_iff_persistently.trans persistently_internalCmraValid

@[rocq_alias internal_cmra_valid_discrete]
theorem internalCmraValid_discrete [CMRA.Discrete A] {a : A} :
    internalCmraValid a ⊣⊢@{PROP} ⌜✓ a⌝ :=
  ⟨(internalCmraValid_elim a).trans <| pure_mono (discrete_valid ·),
   pure_elim' internalCmraValid_intro⟩

@[rocq_alias internal_cmra_valid_persistent]
instance internalCmraValid_persistent (a : A) :
    Persistent (PROP := PROP) (internalCmraValid a) where
  persistent := persistently_internalCmraValid.mpr

@[rocq_alias internal_cmra_valid_absorbing]
instance internalCmraValid_absorbing (a : A) :
    Absorbing (PROP := PROP) (internalCmraValid a) :=
  siPure_absorbing _

@[rocq_alias internal_cmra_valid_plain]
instance internalCmraValid_plain (a : A) :
    Plain (PROP := PROP) (internalCmraValid a) where
  plain := plainly_internalCmraValid a |>.mpr

end CmraValid

section CmraIncluded

variable [Sbi PROP] [CMRA A]

@[rocq_alias internal_included]
def internalCmraIncluded (a b : A) : PROP := siPure (∃ c, internalEq b (a • c))

@[rocq_alias internal_included_ne]
instance internalCmraIncluded_ne :
    NonExpansive₂ (internalCmraIncluded (PROP := PROP) (A := A)) where
  ne n _ _ hx _ _ hy := by
    refine siPure_ne.ne ?_
    apply (exists_ne (fun a => NonExpansive₂.ne hy (op_commN.trans ((op_ne.ne hx).trans op_commN))))

@[rocq_alias internal_included_intro]
theorem internalCmraIncluded_intro {P : PROP} {a b : A} (h : a ≼ b) :
    P ⊢ internalCmraIncluded a b := by
  obtain ⟨c, hc⟩ := h
  calc (P : PROP)
    _ ⊢ True := true_intro
    _ ⊢ <si_pure> True := siPure_pure.mpr
    _ ⊢ internalCmraIncluded a b := siPure_mono (BI.exists_intro' c (internalEq.of_equiv hc))

@[rocq_alias si_pure_internal_included]
theorem siPure_internalCmraIncluded {a b : A} :
    <si_pure> internalCmraIncluded a b ⊣⊢@{PROP} internalCmraIncluded a b :=
  persistently_iff.symm.trans persistently_siPure

@[rocq_alias persistently_internal_included]
theorem persistently_internalCmraIncluded {a b : A} :
    <pers> internalCmraIncluded a b ⊣⊢@{PROP} internalCmraIncluded a b :=
  persistently_siPure

@[rocq_alias plainly_internal_included]
theorem plainly_internalCmraIncluded {a b : A} :
    ■ internalCmraIncluded a b ⊣⊢@{PROP} internalCmraIncluded a b :=
  plainly_siPure

@[rocq_alias intuitionistically_internal_included]
theorem intuitionistically_internalCmraIncluded [BIAffine PROP] {a b : A} :
    □ internalCmraIncluded a b ⊣⊢@{PROP} internalCmraIncluded a b :=
  intuitionistically_iff_persistently.trans persistently_internalCmraIncluded

@[rocq_alias internal_included_discrete]
theorem internalCmraIncluded_discrete {a b : A} [CMRA.Discrete A] :
    internalCmraIncluded a b ⊣⊢@{PROP} ⌜a ≼ b⌝ := by
  haveI : ∀ x : A, DiscreteE x := fun x => ⟨OFE.Discrete.discrete⟩
  refine ⟨?_, pure_elim' internalCmraIncluded_intro⟩
  calc internalCmraIncluded a b
    _ ⊢ <si_pure> (∃ c, internalEq b (a • c)) := siPure_internalCmraIncluded.mp
    _ ⊢ <si_pure> (∃ c, ⌜b ≡ a • c⌝) := siPure_mono <| exists_mono fun _ => discrete_eq_mp
    _ ⊢ <si_pure> ⌜∃ c, b ≡ a • c⌝ := siPure_mono pure_exists.mp
    _ ⊢ ⌜∃ c, b ≡ a • c⌝ := siPure_pure.mp
    _ ⊢ ⌜a ≼ b⌝ := pure_mono fun ⟨c, h⟩ => ⟨c, h⟩

@[rocq_alias internal_included_refl]
theorem internalCmraIncluded_refl {a : A} [IsTotal A] : ⊢@{PROP} internalCmraIncluded a a :=
  internalCmraIncluded_intro .rfl

@[rocq_alias internal_included_trans]
theorem internalCmraIncluded_trans {a b c : A} :
    ⊢@{PROP} internalCmraIncluded a b -∗ internalCmraIncluded b c -∗ internalCmraIncluded a c := by
  refine BI.entails_wand (siPure_exist.mp.trans ?_)
  refine BI.exists_elim (fun a' => ?_)
  refine BI.wand_intro ((BI.sep_mono_r siPure_exist.mp).trans (BI.sep_exists_l.mp.trans ?_))
  refine BI.exists_elim (fun b' => ?_)
  refine siPure_and_sep.mpr.trans (siPure_mono ?_)
  refine BI.exists_intro' (a' • b') ?_
  refine Entails.trans ?_ (internalEq.trans (b := (a • a') • b'))
  refine and_intro ?_ (internalEq.of_equiv assoc.symm)
  refine Entails.trans ?_ (internalEq.trans (b := (b • b')))
  exact and_intro and_elim_r (and_elim_l' (BI.internalEq_entails.mpr (fun n heq => op_left_dist _ heq)))

@[rocq_alias internal_included_timeless]
instance internalCmraIncluded_timeless {a b : A} [CMRA.Discrete A] :
    Timeless (PROP := PROP) (internalCmraIncluded a b) := by
  haveI : ∀ x : A, DiscreteE x := fun x => ⟨OFE.Discrete.discrete⟩
  unfold internalCmraIncluded
  infer_instance

@[rocq_alias internal_included_plain]
instance internalCmraIncluded_plain {a b : A} :
    Plain (PROP := PROP) (internalCmraIncluded a b) where
  plain := plainly_internalCmraIncluded.mpr

@[rocq_alias internal_included_persistent]
instance internalCmraIncluded_persistent {a b : A} :
    Persistent (PROP := PROP) (internalCmraIncluded a b) where
  persistent := persistently_internalCmraIncluded.mpr

@[rocq_alias internal_included_absorbing]
instance internalCmraIncluded_absorbing {a b : A} :
    Absorbing (PROP := PROP) (internalCmraIncluded a b) :=
  siPure_absorbing _

end CmraIncluded

end Iris
