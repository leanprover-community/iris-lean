/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
module

public import Iris.BI.Classes
public import Iris.BI.BI

@[expose] public section

namespace Iris.BI

/-- Require that a separation logic with the carrier type `PROP` is an affine separation logic. -/
@[rocq_alias BiAffine]
class BIAffine (PROP : Type _) [BI PROP] where
  affine (P : PROP) : Affine P

attribute [instance (default + 100)] BIAffine.affine

@[rocq_alias BiPositive]
class BIPositive (PROP : Type _) [BI PROP] where
  affinely_sep_l {P Q : PROP} : <affine> (P ∗ Q) ⊢ <affine> P ∗ Q
export BIPositive (affinely_sep_l)

@[rocq_alias BiLöb]
class BILoeb (PROP : Type _) [BI PROP] where
  loeb_weak {P : PROP} : (▷ P ⊢ P) → True ⊢ P
export BILoeb (loeb_weak)

@[rocq_alias BiLaterContractive]
class BILaterContractive (PROP : Type _) [BI PROP] extends OFE.Contractive later (α := PROP)

#rocq_ignore BiPureForall "BIPureForall is provable for all BIs using classical logic, see pure_forall_2"

@[rocq_alias BiPersistentlyForall]
class BIPersistentlyForall (PROP : Type _) [BI PROP] where
  persistently_sForall_2 (Ψ : PROP → Prop) : (∀ p, ⌜Ψ p⌝ → <pers> p) ⊢ <pers> (sForall Ψ)

@[rocq_alias BiPersistentlyExist]
class BIPersistentlyExist (PROP : Type _) [BI PROP] where
  persistently_sExists_1 (Ψ : PROP → Prop) : <pers> (sExists Ψ) ⊢ ∃ p, ⌜Ψ p⌝ ∧ <pers> p

section PersistentlyExistDiscrete

variable {PROP : Type _} [BI PROP]
  (existential : ∀ {Ψ : PROP → Prop}, (emp ⊢ sExists Ψ) → ∃ p, Ψ p ∧ (emp ⊢ p))
  (persistently_eq : ∀ P : PROP, iprop(<pers> P) = iprop(⌜emp ⊢ P⌝))

/-
A discrete BI whose persistently modality is
`<pers> P := ⌜emp ⊢ P⌝` validates `BIPersistentlyExist` as soon as it satisfies the
"existential property" `(emp ⊢ ∃ x, Φ x) → ∃ x, emp ⊢ Φ x`.
-/
@[reducible]
def BIPersistentlyExist.ofDiscrete : BIPersistentlyExist PROP where
  persistently_sExists_1 Ψ := by
    rw [persistently_eq]
    refine pure_elim' fun h => ?_
    obtain ⟨p, hΨp, hp⟩ := existential h
    refine BI.entails_trans ?_ (sExists_intro ⟨p, rfl⟩)
    refine and_intro (pure_intro hΨp) ?_
    rw [persistently_eq]
    exact pure_intro hp

end PersistentlyExistDiscrete

end Iris.BI
