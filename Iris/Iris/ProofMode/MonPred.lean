/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.BI
public import Iris.BI.MonPred
public import Iris.ProofMode.Classes
public import Iris.ProofMode.ClassesMake
public import Iris.ProofMode.ModalityInstances
public import Iris.ProofMode.Instances
public import Iris.Std.TC

@[expose] public section

namespace Iris.ProofMode
open BI Std MonPred

variable {I : BiIndex} {PROP : Type _} [BI PROP]

@[ipm_class, rocq_alias MakeMonPredAt]
class MakeMonPredAt (i : I.car) (P : MonPred I PROP) (𝓟 : PROP) where
  make_monPred_at : P.monPred_at i ⊣⊢ 𝓟
export MakeMonPredAt (make_monPred_at)

@[ipm_class, rocq_alias IsBiIndexRel]
class IsBiIndexRel (i j : I.car) where
  is_bi_index_rel : I.rel.le i j
export IsBiIndexRel (is_bi_index_rel)

@[rocq_alias modality_objectively, rocq_alias modality_objectively_mixin]
def modality_objectively : Modality (MonPred I PROP) (MonPred I PROP) where
  M := MonPred.objectively
  action _ := .transform fun P Q => Objective P ∧ P = Q
  spec := by
    intro p P Q h
    have hPQ : P = Q := h.2
    subst hPQ
    haveI := h.1
    exact objective_objectively iprop(□?p P)
  emp := monPred_objectively_emp.mpr
  mono := monPred_objectively_mono
  sep := monPred_objectively_sep_2 _ _
