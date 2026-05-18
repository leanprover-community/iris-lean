/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergei Stepanenko, Michael Sammler
-/
module

public import Iris.ProofMode.Classes
public import Iris.ProofMode.ModalityInstances
public import Iris.Std.TC
import Iris.Std.RocqPorting

@[expose] public section

namespace Iris.ProofMode
open Iris.BI Iris.Std

section internalEq

variable {PROP} [Sbi PROP]

@[rocq_alias from_pure_internal_eq]
instance fromPure_internalEq [Sbi PROP] [OFE A] (a b : A) :
    FromPure (PROP := PROP) false (internalEq a b) io (a ≡ b) where
  from_pure := internalEq.of_pure


@[ipm_backtrack, rocq_alias into_pure_eq]
instance intoPure_internalEq [Sbi PROP] [OFE A] (a b : A)
    [TCOr (OFE.DiscreteE a) (OFE.DiscreteE b)] :
    IntoPure (PROP := PROP) (internalEq a b) (a ≡ b) where
  into_pure := discrete_eq_mp

@[ipm_backtrack]
instance (priority := default + 10) intoPure_internalEq_leibniz [Sbi PROP] [OFE A] [OFE.Leibniz A]
    (a b : A) [TCOr (OFE.DiscreteE a) (OFE.DiscreteE b)] :
    IntoPure (PROP := PROP) (internalEq a b) (a = b) where
  into_pure := discrete_eq_mp.trans (pure_mono OFE.eq_of_eqv)

@[rocq_alias from_modal_Next]
instance fromModal_internalEq_next [Sbi PROP] [OFE A] (x y : A) :
    FromModal (PROP1 := PROP) (PROP2 := PROP) True (modality_laterN 1)
      iprop(▷ internalEq x y) (internalEq (Later.next x) (Later.next y)) (internalEq x y) where
  from_modal _ := later_equivI_mpr x y

@[rocq_alias into_laterN_Next]
instance intoLaterN_internalEq_next [Sbi PROP] [OFE A] (x y : A)
    only_head n n' [h : NatCancel n 1 n' 0] :
    IntoLaterN (PROP := PROP) only_head n (internalEq (Later.next x) (Later.next y))
      (internalEq x y) where
  into_laterN := (later_equivI_mp x y).trans (by
    have hcancel : n' + 1 = n := by have := h.nat_cancel; omega
    rw [← hcancel]
    exact later_mono (laterN_intro n'))

-- IntoInternalEq
@[rocq_alias into_internal_eq_internal_eq]
instance intoInternalEq_internalEq [Sbi PROP] [OFE A] (x y : A) :
    IntoInternalEq (PROP := PROP) (internalEq x y) x y where
  into_internal_eq := .rfl

@[rocq_alias into_internal_eq_affinely]
instance intoInternalEq_affinely [Sbi PROP] [OFE A] (x y : A) (P : PROP)
    [h : IntoInternalEq P x y] :
    IntoInternalEq iprop(<affine> P) x y where
  into_internal_eq := affinely_elim.trans h.into_internal_eq

@[rocq_alias into_internal_eq_intuitionistically]
instance intoInternalEq_intuitionistically [Sbi PROP] [OFE A] (x y : A) (P : PROP)
    [h : IntoInternalEq P x y] :
    IntoInternalEq iprop(□ P) x y where
  into_internal_eq := intuitionistically_elim.trans h.into_internal_eq

@[rocq_alias into_internal_eq_absorbingly]
instance intoInternalEq_absorbingly [Sbi PROP] [OFE A] (x y : A) (P : PROP)
    [h : IntoInternalEq P x y] :
    IntoInternalEq iprop(<absorb> P) x y where
  into_internal_eq := (absorbingly_mono h.into_internal_eq).trans (absorbingly_internalEq x y).1

@[rocq_alias into_internal_eq_plainly]
instance intoInternalEq_plainly [Sbi PROP] [OFE A] (x y : A) (P : PROP)
    [h : IntoInternalEq P x y] :
    IntoInternalEq iprop(■ P) x y where
  into_internal_eq := (plainly_mono h.into_internal_eq).trans (by sorry) --(plainly_internalEq).1

@[rocq_alias into_internal_eq_persistently]
instance intoInternalEq_persistently [Sbi PROP] [OFE A] (x y : A) (P : PROP)
    [h : IntoInternalEq P x y] :
    IntoInternalEq iprop(<pers> P) x y where
  into_internal_eq := (persistently_mono h.into_internal_eq).trans (persistently_internalEq x y).1
