/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.BI
public import Iris.ProofMode.Classes
public import Iris.ProofMode.ClassesMake
public import Iris.ProofMode.ModalityInstances
public import Iris.ProofMode.Instances

@[expose] public section

namespace Iris.ProofMode
open BI Std MonPred

variable {I : BiIndex} {PROP : Type _} [BI PROP]

inductive MakeMonPredAt.Kind where
  -- Known index `i`, and the proposition `𝓟` is computed by evaluating `P` at `i`
  | indexToProp
  -- Known proposition `𝓟`, and the index `i` is recovered from it
  | propToIndex

meta section

@[reducible]
def MakeMonPredAt.Kind.indexIO : MakeMonPredAt.Kind → InOut
  | indexToProp => .in
  | propToIndex => .out

@[reducible]
def MakeMonPredAt.Kind.propIO : MakeMonPredAt.Kind → InOut
  | indexToProp => .out
  | propToIndex => .in

end

@[ipm_class, rocq_alias MakeMonPredAt]
class MakeMonPredAt (d : MakeMonPredAt.Kind) (i : semiOutParamIPM d.indexIO I.car)
    (P : MonPred I PROP) (𝓟 : semiOutParamIPM d.propIO PROP) where
  make_monPred_at : P.monPred_at i ⊣⊢ 𝓟
export MakeMonPredAt (make_monPred_at)

@[ipm_class, rocq_alias IsBiIndexRel]
class IsBiIndexRel (i j : I.car) where
  is_bi_index_rel : I.rel.le i j
export IsBiIndexRel (is_bi_index_rel)

@[rocq_alias is_bi_index_rel_refl]
instance (priority := high) isBiIndexRel_refl (i : I) : IsBiIndexRel i i where
  is_bi_index_rel := Std.Refl.refl i

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

/-! ### FromAssumption -/

-- @[ipm_backtrack, rocq_alias from_assumption_make_monPred_at_l]
-- instance fromAssumption_make_monPred_at_l (p : Bool) (i j : I.car)
--     (P : MonPred I PROP) (𝓟 : PROP)
--     [hm : MakeMonPredAt .propToIndex i P 𝓟] [hr : IsBiIndexRel j i] :
--     FromAssumption p .in (P.monPred_at j) 𝓟 where
--   from_assumption := intuitionisticallyIf_elim.trans <|
--     (P.monPred_mono hr.is_bi_index_rel).trans hm.make_monPred_at.mp

@[ipm_backtrack, rocq_alias from_assumption_make_monPred_at_r]
instance fromAssumption_make_monPred_at_r (p : Bool) d (i j : I.car)
    (P : MonPred I PROP) (𝓟 : PROP)
    [hm : MakeMonPredAt d i P 𝓟] [hr : IsBiIndexRel i j] :
    FromAssumption p d.propIO 𝓟 (P.monPred_at j) where
  from_assumption := calc
    _ ⊢ 𝓟              := intuitionisticallyIf_elim
    _ ⊢ P.monPred_at i := hm.make_monPred_at.mpr
    _ ⊢ P.monPred_at j := P.monPred_mono hr.is_bi_index_rel

@[rocq_alias from_assumption_make_monPred_objectively]
instance fromAssumption_monPred_objectively (p : Bool) (P Q : MonPred I PROP)
    [h : FromAssumption p .in P Q] : FromAssumption p .in iprop(<obj> P) Q where
  from_assumption :=
    (intuitionisticallyIf_mono <| monPred_objectively_elim P).trans h.from_assumption

@[rocq_alias from_assumption_make_monPred_subjectively]
instance fromAssumption_monPred_subjectively (p : Bool) ioP (P Q : MonPred I PROP)
    [h : FromAssumption p ioP P Q] : FromAssumption p ioP P iprop(<subj> Q) where
  from_assumption := h.from_assumption.trans <| monPred_subjectively_intro Q

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
    [h : FromModal .in modality_affinely φ sel P Q] [hm : MakeMonPredAt .indexToProp i Q 𝓠] :
    FromModal io modality_affinely φ sel (P.monPred_at i) 𝓠 where
  from_modal hφ := calc
    _ ⊢ <affine> (Q.monPred_at i)      := affinely_mono hm.make_monPred_at.mpr
    _ ⊢ iprop(<affine> Q).monPred_at i := (monPred_at_affinely i Q).mpr
    _ ⊢ P.monPred_at i                 := entails_at.mp (h.from_modal hφ) i

@[ipm_backtrack, rocq_alias from_modal_persistently_monPred_at]
instance (priority := high) fromModal_persistently_monPred_at {α} (φ : Prop) io (sel : α)
    (P Q : MonPred I PROP) (𝓠 : PROP) (i : I.car)
    [h : FromModal .in modality_persistently φ sel P Q] [hm : MakeMonPredAt .indexToProp i Q 𝓠] :
    FromModal io modality_persistently φ sel (P.monPred_at i) 𝓠 where
  from_modal hφ := calc
    _ ⊢ <pers> (Q.monPred_at i)      := persistently_mono hm.make_monPred_at.mpr
    _ ⊢ iprop(<pers> Q).monPred_at i := (monPred_at_persistently i Q).mpr
    _ ⊢ P.monPred_at i               := entails_at.mp (h.from_modal hφ) i

@[ipm_backtrack, rocq_alias from_modal_intuitionistically_monPred_at]
instance (priority := high) fromModal_intuitionistically_monPred_at {α} (φ : Prop) io (sel : α)
    (P Q : MonPred I PROP) (𝓠 : PROP) (i : I.car)
    [h : FromModal .in modality_intuitionistically φ sel P Q]
    [hm : MakeMonPredAt .indexToProp i Q 𝓠] :
    FromModal io modality_intuitionistically φ sel (P.monPred_at i) 𝓠 where
  from_modal hφ := calc
    _ ⊢ □ (Q.monPred_at i)       := intuitionistically_mono hm.make_monPred_at.mpr
    _ ⊢ iprop(□ Q).monPred_at i  := (monPred_at_intuitionistically i Q).mpr
    _ ⊢ P.monPred_at i           := entails_at.mp (h.from_modal hφ) i

@[ipm_backtrack, rocq_alias from_modal_id_monPred_at]
instance fromModal_id_monPred_at {α} (φ : Prop) io (sel : α)
    (P Q : MonPred I PROP) (𝓠 : PROP) (i : I.car)
    [h : FromModal .in modality_id φ sel P Q]
    [hm : MakeMonPredAt .indexToProp i Q 𝓠] :
    FromModal io modality_id φ sel (P.monPred_at i) 𝓠 where
  from_modal hφ := hm.make_monPred_at.mpr.trans (entails_at.mp (h.from_modal hφ) i)

/-! ### FromLater -/

@[ipm_backtrack, rocq_alias from_later_monPred_at]
instance fromLater_monPred_at {α} (φ : Prop) io (sel : α) (n : Nat)
    (P Q : MonPred I PROP) (𝓠 : PROP) (i : I.car)
    [h : FromModal .in (modality_laterN n) φ sel P Q]
    [hm : MakeMonPredAt .indexToProp i Q 𝓠] :
    FromModal io (modality_laterN n) φ sel (P.monPred_at i) 𝓠 where
  from_modal hφ := calc
    _ ⊢ ▷^[n] (Q.monPred_at i)      := laterN_mono n hm.make_monPred_at.mpr
    _ ⊢ iprop(▷^[n] Q).monPred_at i := (monPred_at_laterN n i Q).mpr
    _ ⊢ P.monPred_at  i              := entails_at.mp (h.from_modal hφ) i

/-! ### IntoPure -/

@[rocq_alias into_pure_monPred_in]
instance intoPure_monPred_in (i j : I.car) :
    IntoPure ((MonPred.monPred_in i : MonPred I PROP).monPred_at j) (I.rel.le i j) where
  into_pure := (monPred_at_in j i).mp

@[rocq_alias into_pure_monPred_at]
instance intoPure_monPred_at (P : MonPred I PROP) (φ : Prop) (i : I.car) [h : IntoPure P φ] :
    IntoPure (P.monPred_at i) φ where
  into_pure := (entails_at.mp h.into_pure i).trans (monPred_at_pure i φ).mp

/-! ### FromPure -/

@[rocq_alias from_pure_monPred_at]
instance fromPure_monPred_at (a : Bool) (P : MonPred I PROP) ioφ (φ : Prop) (i : I.car)
    [h : FromPure a P ioφ φ] : FromPure a (P.monPred_at i) ioφ φ where
  from_pure := (monPred_at_affinely_if i a iprop(⌜φ⌝)).mpr.trans (entails_at.mp h.from_pure i)

@[rocq_alias from_pure_monPred_in]
instance fromPure_monPred_in ioφ (i j : I.car) :
    FromPure false ((MonPred.monPred_in i : MonPred I PROP).monPred_at j) ioφ (I.rel.le i j) where
  from_pure := (monPred_at_in j i).mpr

/-! ### IntoPersistently -/

@[ipm_backtrack, rocq_alias into_persistent_monPred_at]
instance (priority := high) intoPersistently_monPred_at (p : Bool)
    (P Q : MonPred I PROP) (𝓠 : PROP) (i : I.car)
    [h : IntoPersistently p P Q] [hm : MakeMonPredAt .indexToProp i Q 𝓠] :
    IntoPersistently p (P.monPred_at i) 𝓠 where
  into_persistently := calc
    _ ⊢ iprop(<pers>?p P).monPred_at i  := (monPred_at_persistently_if i p P).mpr
    _ ⊢ iprop(<pers> Q).monPred_at i    := entails_at.mp h.into_persistently i
    _ ⊢ <pers> (Q.monPred_at i)         := (monPred_at_persistently i Q).mp
    _ ⊢ <pers> 𝓠                        := persistently_mono hm.make_monPred_at.mp

/-! ### FromAnd -/

@[rocq_alias from_and_monPred_at]
instance fromAnd_monPred_at (P Q1 Q2 : MonPred I PROP) (𝓠1 𝓠2 : PROP) (i : I.car)
    [h : FromAnd P Q1 Q2]
    [h1 : MakeMonPredAt .indexToProp i Q1 𝓠1] [h2 : MakeMonPredAt .indexToProp i Q2 𝓠2] :
    FromAnd (P.monPred_at i) 𝓠1 𝓠2 where
  from_and := (and_mono h1.make_monPred_at.mpr h2.make_monPred_at.mpr).trans
    (entails_at.mp h.from_and i)

/-! ### IntoAnd -/

@[rocq_alias into_and_monPred_at]
instance intoAnd_monPred_at (p : Bool) (P Q1 Q2 : MonPred I PROP) (𝓠1 𝓠2 : PROP) (i : I.car)
    [h : IntoAnd p P Q1 Q2]
    [h1 : MakeMonPredAt .indexToProp i Q1 𝓠1] [h2 : MakeMonPredAt .indexToProp i Q2 𝓠2] :
    IntoAnd p (P.monPred_at i) 𝓠1 𝓠2 where
  into_and := calc
    _ ⊢ (iprop(□?p P) : MonPred I PROP).monPred_at i          := (monPred_at_intuitionistically_if
                                                                   i p P).mpr
    _ ⊢ (iprop(□?p (Q1 ∧ Q2)) : MonPred I PROP).monPred_at i  := entails_at.mp h.into_and i
    _ ⊢ □?p ((iprop(Q1 ∧ Q2) : MonPred I PROP).monPred_at i)  := (monPred_at_intuitionistically_if
                                                                   i p iprop(Q1 ∧ Q2)).mp
    _ ⊢ □?p (𝓠1 ∧ 𝓠2)                                         := intuitionisticallyIf_mono
        (and_mono h1.make_monPred_at.mp h2.make_monPred_at.mp)

/-! ### FromSep -/

@[rocq_alias from_sep_monPred_at]
instance fromSep_monPred_at (P Q1 Q2 : MonPred I PROP) (𝓠1 𝓠2 : PROP) (i : I.car)
    [h : FromSep P Q1 Q2]
    [h1 : MakeMonPredAt .indexToProp i Q1 𝓠1] [h2 : MakeMonPredAt .indexToProp i Q2 𝓠2] :
    FromSep (P.monPred_at i) 𝓠1 𝓠2 where
  from_sep := (sep_mono h1.make_monPred_at.mpr h2.make_monPred_at.mpr).trans
    (entails_at.mp h.from_sep i)

/-! ### IntoSep -/

@[rocq_alias into_sep_monPred_at]
instance intoSep_monPred_at (P Q1 Q2 : MonPred I PROP) (𝓠1 𝓠2 : PROP) (i : I.car)
    [h : IntoSep P Q1 Q2]
    [h1 : MakeMonPredAt .indexToProp i Q1 𝓠1] [h2 : MakeMonPredAt .indexToProp i Q2 𝓠2] :
    IntoSep (P.monPred_at i) 𝓠1 𝓠2 where
  into_sep := (entails_at.mp h.into_sep i).trans
    (sep_mono h1.make_monPred_at.mp h2.make_monPred_at.mp)

/-! ### FromOr -/

@[rocq_alias from_or_monPred_at]
instance fromOr_monPred_at (P Q1 Q2 : MonPred I PROP) (𝓠1 𝓠2 : PROP) (i : I.car)
    [h : FromOr P Q1 Q2]
    [h1 : MakeMonPredAt .indexToProp i Q1 𝓠1] [h2 : MakeMonPredAt .indexToProp i Q2 𝓠2] :
    FromOr (P.monPred_at i) 𝓠1 𝓠2 where
  from_or := (or_mono h1.make_monPred_at.mpr h2.make_monPred_at.mpr).trans
    (entails_at.mp h.from_or i)

/-! ### IntoOr -/

@[rocq_alias into_or_monPred_at]
instance intoOr_monPred_at (P Q1 Q2 : MonPred I PROP) (𝓠1 𝓠2 : PROP) (i : I.car)
    [h : IntoOr P Q1 Q2]
    [h1 : MakeMonPredAt .indexToProp i Q1 𝓠1] [h2 : MakeMonPredAt .indexToProp i Q2 𝓠2] :
    IntoOr (P.monPred_at i) 𝓠1 𝓠2 where
  into_or := (entails_at.mp h.into_or i).trans
    (or_mono h1.make_monPred_at.mp h2.make_monPred_at.mp)

/-! ### IntoLaterN -/

@[rocq_alias maybe_into_later_monPred_at]
instance intoLaterN_monPred_at progress (n : Nat) (P Q : MonPred I PROP) (𝓠 : PROP) (i : I.car)
    [h : IntoLaterN (progress := true) (only_head := false) n P Q]
    [hm : MakeMonPredAt .indexToProp i Q 𝓠] :
    IntoLaterN progress (only_head := false) n (P.monPred_at i) 𝓠 where
  into_laterN := (entails_at.mp h.into_laterN i).trans <|
    (monPred_at_laterN n i Q).mp.trans (laterN_mono n hm.make_monPred_at.mp)

/-! ### IntoEmbed -/

@[rocq_alias into_embed_objective]
instance intoEmbed_objective (P : MonPred I PROP) [Objective P] :
    IntoEmbed (PROP1 := PROP) (PROP2 := MonPred I PROP) P iprop(∀ i, P.monPred_at i) where
  into_embed := entails_at.mpr fun i => forall_intro fun j => Objective.objective_at i j
