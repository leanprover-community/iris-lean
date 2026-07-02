/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
module

public import Iris.BI
public import Iris.ProofMode.Classes
public import Iris.ProofMode.ModalityInstances
public import Iris.Std.TC
public import Iris.Std.RocqPorting

@[expose] public section

namespace Iris.ProofMode
open Iris.BI Iris.Std

-- AsEmpValid
@[rocq_alias as_emp_valid_emp_valid]
instance (priority := default + 10) asEmpValidEmpValid
    [bi : BI PROP] d (P : PROP) :
    AsEmpValid d (⊢ P) io1 PROP io2 bi P := ⟨by simp⟩

@[rocq_alias as_emp_valid_entails]
instance asEmpValid_entails [bi : BI PROP] d (P Q : PROP)
: AsEmpValid d (P ⊢ Q) io1 PROP io2 bi iprop(P -∗ Q) where
  as_emp_valid := ⟨λ _ => entails_wand, λ _ => wand_entails⟩

instance asEmpValid_bientails [bi : BI PROP] (P Q : PROP)
: AsEmpValid d (P ⊣⊢ Q) io1 PROP io2 bi iprop(P ∗-∗ Q) where
  as_emp_valid := ⟨λ _ => equiv_wandIff, λ _ => wandIff_equiv⟩

@[rocq_alias as_emp_valid_equiv]
instance asEmpValid_equiv [bi : BI PROP] (P Q : PROP)
: AsEmpValid d (P ≡ Q) io1 PROP io2 bi iprop(P ∗-∗ Q) where
  as_emp_valid := ⟨λ _ h => equiv_wandIff (equiv_iff.1 h), λ _ h => (equiv_iff.2 (wandIff_equiv h))⟩

@[rocq_alias as_emp_valid_forall]
instance asEmpValid_forall {α} [bi : BI PROP] (Φ : α → Prop) (P : α → PROP)
  [hP : ∀ x, AsEmpValid d (Φ x) io1 PROP io2 bi iprop(P x)]
: AsEmpValid d (∀ x, Φ x) io1 PROP io2 bi iprop(∀ x, P x) where
  as_emp_valid := ⟨λ hd h => forall_intro λ x => (hP x).1.1 hd (h x),
                   λ hd h x => (hP x).1.2 hd $ h.trans (forall_elim x)⟩
