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
class MakeMonPredAt (i : I.car) (P : MonPred I PROP) (𝓟 : outParam PROP) where
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

/-! ### FromModal -/

@[rocq_alias from_modal_objectively]
instance (priority := default + 20) fromModal_objectively io (P : MonPred I PROP) :
    FromModal io modality_objectively True iprop(<obj> P) iprop(<obj> P) P where
  from_modal _ := .rfl

@[rocq_alias from_modal_subjectively]
instance (priority := default + 20) fromModal_subjectively io (P : MonPred I PROP) :
    FromModal io modality_id True iprop(<subj> P) iprop(<subj> P) P where
  from_modal _ := monPred_subjectively_intro P

@[ipm_backtrack, rocq_alias from_modal_affinely_monPred_at]
instance (priority := high) fromModal_affinely_monPred_at {α} (φ : Prop) io (sel : α)
    (P Q : MonPred I PROP) (𝓠 : PROP) (i : I.car)
    [h : FromModal .in modality_affinely φ sel P Q] [hm : MakeMonPredAt i Q 𝓠] :
    FromModal io modality_affinely φ sel (P.monPred_at i) 𝓠 where
  from_modal hφ := calc
    _ ⊢ <affine> (Q.monPred_at i)      := affinely_mono hm.make_monPred_at.mpr
    _ ⊢ iprop(<affine> Q).monPred_at i := (monPred_at_affinely i Q).mpr
    _ ⊢ P.monPred_at i                 := entails_at.mp (h.from_modal hφ) i

@[ipm_backtrack, rocq_alias from_modal_persistently_monPred_at]
instance (priority := high) fromModal_persistently_monPred_at {α} (φ : Prop) io (sel : α)
    (P Q : MonPred I PROP) (𝓠 : PROP) (i : I.car)
    [h : FromModal .in modality_persistently φ sel P Q] [hm : MakeMonPredAt i Q 𝓠] :
    FromModal io modality_persistently φ sel (P.monPred_at i) 𝓠 where
  from_modal hφ := calc
    _ ⊢ <pers> (Q.monPred_at i)      := persistently_mono hm.make_monPred_at.mpr
    _ ⊢ iprop(<pers> Q).monPred_at i := (monPred_at_persistently i Q).mpr
    _ ⊢ P.monPred_at i               := entails_at.mp (h.from_modal hφ) i

@[ipm_backtrack, rocq_alias from_modal_intuitionistically_monPred_at]
instance (priority := high) fromModal_intuitionistically_monPred_at {α} (φ : Prop) io (sel : α)
    (P Q : MonPred I PROP) (𝓠 : PROP) (i : I.car)
    [h : FromModal .in modality_intuitionistically φ sel P Q] [hm : MakeMonPredAt i Q 𝓠] :
    FromModal io modality_intuitionistically φ sel (P.monPred_at i) 𝓠 where
  from_modal hφ := calc
    _ ⊢ □ (Q.monPred_at i)       := intuitionistically_mono hm.make_monPred_at.mpr
    _ ⊢ iprop(□ Q).monPred_at i  := (monPred_at_intuitionistically i Q).mpr
    _ ⊢ P.monPred_at i           := entails_at.mp (h.from_modal hφ) i

@[ipm_backtrack, rocq_alias from_modal_id_monPred_at]
instance fromModal_id_monPred_at {α} (φ : Prop) io (sel : α)
    (P Q : MonPred I PROP) (𝓠 : PROP) (i : I.car)
    [h : FromModal .in modality_id φ sel P Q] [hm : MakeMonPredAt i Q 𝓠] :
    FromModal io modality_id φ sel (P.monPred_at i) 𝓠 where
  from_modal hφ := hm.make_monPred_at.mpr.trans (entails_at.mp (h.from_modal hφ) i)

@[ipm_backtrack, rocq_alias from_later_monPred_at]
instance fromLater_monPred_at {α} (φ : Prop) io (sel : α) (n : Nat)
    (P Q : MonPred I PROP) (𝓠 : PROP) (i : I.car)
    [h : FromModal .in (modality_laterN n) φ sel P Q] [hm : MakeMonPredAt i Q 𝓠] :
    FromModal io (modality_laterN n) φ sel (P.monPred_at i) 𝓠 where
  from_modal hφ := calc
    _ ⊢ ▷^[n] (Q.monPred_at i)      := laterN_mono n hm.make_monPred_at.mpr
    _ ⊢ iprop(▷^[n] Q).monPred_at i := (monPred_at_laterN n i Q).mpr
    _ ⊢ P.monPred_at  i              := entails_at.mp (h.from_modal hφ) i
