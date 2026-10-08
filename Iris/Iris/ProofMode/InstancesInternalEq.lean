/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergei Stepanenko, Michael Sammler
-/
module

public import Iris.ProofMode.Classes
public import Iris.ProofMode.ModalityInstances
public import Iris.ProofMode.NatCancel

@[expose] public section


variable {SI : Type _} [Iris.SIdx SI]

namespace Iris.ProofMode
open Iris.BI Iris.Std

section InternalEq

variable {PROP} [Sbi SI PROP]

/-! ### FromPure -/

@[rocq_alias from_pure_internal_eq]
instance fromPure_internalEq [Sbi SI PROP] [OFE SI A] (a b : A) :
    FromPure (PROP := PROP) false iprop(a ≡[SI] b) io (a = b) where
  from_pure := internalEq.of_pure

/-! ### IntoPure -/

@[ipm_backtrack, rocq_alias into_pure_eq]
instance intoPure_internalEq [Sbi SI PROP] [OFE SI A] (a b : A)
    [TCOr (OFE.DiscreteE SI a) (OFE.DiscreteE SI b)] :
    IntoPure (PROP := PROP) iprop(a ≡[SI] b) (a = b) where
  into_pure := discrete_eq_mp

@[ipm_backtrack]
instance (priority := default + 10) intoPure_internalEq_leibniz [Sbi SI PROP] [OFE SI A]
    (a b : A) [TCOr (OFE.DiscreteE SI a) (OFE.DiscreteE SI b)] :
    IntoPure (PROP := PROP) iprop(a ≡[SI] b) (a = b) where
  into_pure := discrete_eq_mp

/-! ### FromModal -/

@[rocq_alias from_modal_Next]
instance fromModal_internalEq_next [Sbi SI PROP] [OFE SI A] io (x y : A) :
    FromModal (PROP1 := PROP) (PROP2 := PROP) io (modality_laterN 1) True
      iprop(▷ (x ≡[SI] y) : PROP) iprop(Later.next x ≡[SI] Later.next y) iprop(x ≡[SI] y) where
  from_modal _ := later_equivI_mpr x y

/-! ### IntoLaterN -/

@[ipm_backtrack, rocq_alias into_laterN_Next]
instance intoLaterN_internalEq_next [Sbi SI PROP] [OFE SI A] (x y : A)
    progress stuck only_head n n' [h : NatCancel n 1 n' 0 stuck] :
    IntoLaterN progress (PROP := PROP) only_head n
      iprop(Later.next x ≡[SI] Later.next y) iprop(x ≡[SI] y) where
  into_laterN := by
    refine (later_equivI_mp x y).trans ?_
    have hcancel : n' + 1 = n := by have := h.nat_cancel; omega
    rw [← hcancel]
    exact later_mono (laterN_intro n')

/-! ### IntoInternalEq -/

@[rocq_alias into_internal_eq_internal_eq]
instance intoInternalEq_internalEq [Sbi SI PROP] [OFE SI A] (x y : A) :
    IntoInternalEq SI (PROP := PROP) iprop(x ≡[SI] y) x y where
  into_internal_eq := .rfl

@[rocq_alias into_internal_eq_affinely]
instance intoInternalEq_affinely [Sbi SI PROP] [OFE SI A] (x y : A) (P : PROP)
    [h : IntoInternalEq SI P x y] :
    IntoInternalEq SI iprop(<affine> P) x y where
  into_internal_eq := affinely_elim.trans h.into_internal_eq

@[rocq_alias into_internal_eq_intuitionistically]
instance intoInternalEq_intuitionistically [Sbi SI PROP] [OFE SI A] (x y : A) (P : PROP)
    [h : IntoInternalEq SI P x y] :
    IntoInternalEq SI iprop(□ P) x y where
  into_internal_eq := intuitionistically_elim.trans h.into_internal_eq

@[rocq_alias into_internal_eq_absorbingly]
instance intoInternalEq_absorbingly [Sbi SI PROP] [OFE SI A] (x y : A) (P : PROP)
    [h : IntoInternalEq SI P x y] :
    IntoInternalEq SI iprop(<absorb> P) x y where
  into_internal_eq := (absorbingly_mono h.into_internal_eq).trans (absorbingly_internalEq x y).1

@[rocq_alias into_internal_eq_plainly]
instance intoInternalEq_plainly [Sbi SI PROP] [OFE SI A] (x y : A) (P : PROP)
    [h : IntoInternalEq SI P x y] :
    IntoInternalEq SI iprop(■ P) x y where
  into_internal_eq := (plainly_mono h.into_internal_eq).trans (plainly_internalEq).1

@[rocq_alias into_internal_eq_persistently]
instance intoInternalEq_persistently [Sbi SI PROP] [OFE SI A] (x y : A) (P : PROP)
    [h : IntoInternalEq SI P x y] :
    IntoInternalEq SI iprop(<pers> P) x y where
  into_internal_eq := (persistently_mono h.into_internal_eq).trans (persistently_internalEq x y).1

end InternalEq

end ProofMode

end Iris
