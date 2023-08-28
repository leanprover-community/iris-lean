/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.BI.Classes
import Iris.BI.BI

namespace Iris.BI

/-- Require that a separation logic with the carrier type `PROP` is an affine separation logic. -/
class BIAffine (PROP : Type) [BI PROP] : Prop where
  affine (P : PROP) : Affine P

attribute [instance (default + 100)] BIAffine.affine

class BIPositive (PROP : Type) [BI PROP] where
  affinely_sep_l {P Q : PROP} : <affine> (P ∗ Q) ⊢ <affine> P ∗ Q
export BIPositive (affinely_sep_l)

class BILoeb (PROP : Type) [BI PROP] : Prop where
  loeb_weak {P : PROP} : (▷ P ⊢ P) → True ⊢ P

class BILaterContractive (PROP : Type) [BI PROP] extends OFE.Contractive later (α := PROP) : Prop

class BIPersistentlyForall (PROP : Type) [BI PROP] where
  persistently_forall_2 (Ψ : α → PROP) : (∀ a, <pers> (Ψ a)) ⊢ <pers> (∀ a, Ψ a)

end Iris.BI
