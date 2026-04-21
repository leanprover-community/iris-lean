/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
module

public import Iris.Std.RocqPorting
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

end Iris.BI
