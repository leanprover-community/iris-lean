/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Michael Sammler
-/
module

public import Iris.BI
public import Iris.BI.DerivedLaws
public import Iris.ProofMode.Modalities
public import Iris.ProofMode.Classes

@[expose] public section

namespace Iris.ProofMode
open Iris.BI

section Modalities

variable [BI PROP]

def modality_persistently : Modality PROP PROP where
  M := persistently
  action
  | true => .id
  | false => .clear
  spec
  | true => λ _ => persistent
  | false => λ P => persistently_absorbing P
  emp := persistently_emp_2
  mono := (persistently_mono ·)
  sep := persistently_sep_2

unif_hint [BIBase PROP] (P : PROP) where |- iprop(□?false P) ≟ iprop(P)
unif_hint [BIBase PROP] (P : PROP) where |- iprop(□?true P) ≟ iprop(□ P)

def modality_affinely : Modality PROP PROP where
  M := affinely
  action
  | true => .id
  | false => .forall Affine
  spec
  | true => λ _ => affinely_intro .rfl
  | false => λ _ _ => affinely_intro .rfl
  emp := affinely_intro .rfl
  mono := (affinely_mono ·)
  sep := affinely_sep_2

def modality_intuitionistically : Modality PROP PROP where
  M := intuitionistically
  action
  | true => .id
  | false => .isEmpty
  spec
  | true => λ _ => intuitionistic
  | false => trivial
  emp := intuitionistic
  mono := (intuitionistically_mono ·)
  sep := intuitionistically_sep_2

def modality_laterN (n : Nat) : Modality PROP PROP where
  M := BIBase.laterN n
  action := λ _ => .transform (IntoLaterN false n)
  spec := λ _ _ _ h => (intuitionisticallyIf_mono (h.1)).trans (laterN_intuitionisticallyIf_2 n)
  emp := laterN_intro n
  mono := (laterN_mono n ·)
  sep := (laterN_sep n).2

end Modalities

def modality_plainly [Sbi PROP] : Modality PROP PROP where
  M := BIBase.Plainly.plainly
  action
  | true => .forall Plain
  | false => .clear
  spec
  | true => λ _ _ => (intuitionistically_mono Plain.plain).trans intuitionistically_plainly
  | false => λ _ => plainly_absorbing _
  emp := plainly_emp_2
  mono := (plainly_mono_sbi ·)
  sep := plainly_sep_2
