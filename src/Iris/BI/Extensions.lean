/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.BI.Classes
import Iris.BI.BI

namespace Iris.BI

/-- Require that a separation logic with the carrier type `PROP` is an affine separation logic. -/
class BIAffine (PROP : Type _) [BI PROP] where
  affine (P : PROP) : Affine P

attribute [instance (default + 100)] BIAffine.affine

class BIPositive (PROP : Type _) [BI PROP] where
  affinely_sep_l {P Q : PROP} : <affine> (P ∗ Q) ⊢ <affine> P ∗ Q
export BIPositive (affinely_sep_l)

class BILoeb (PROP : Type _) [BI PROP] where
  loeb_weak {P : PROP} : (▷ P ⊢ P) → True ⊢ P

class BILaterContractive (PROP : Type _) [BI PROP] extends OFE.Contractive later (α := PROP)

class BIPersistentlyForall (PROP : Type _) [BI PROP] where
  persistently_sForall_2 (Ψ : PROP → Prop) : (∀ p, ⌜Ψ p⌝ → <pers> p) ⊢ <pers> (sForall Ψ)

end Iris.BI
