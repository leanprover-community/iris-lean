/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.BI.Sbi
public import Iris.BI.Plainly
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

end Iris
