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

@[expose] public section

namespace Iris.ProofMode
open BI Std MonPred

section Classes

variable {I : BiIndex} {PROP : Type _} [bi : BI PROP]

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

/-! ### Modality -/

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

end Classes

section BIInstances

variable {I : BiIndex} {PROP : Type _} [bi : BI PROP]

/-! ### AsEmpValid -/

@[ipm_backtrack, rocq_alias as_emp_valid_monPred_at]
instance (priority := low) asEmpValid_monPred_at (d : AsEmpValid.Direction) (φ : Prop) io ioP
    (P : MonPred I PROP) (Φ : I.car → PROP)
    [inst : AsEmpValid0 d φ .in (MonPred I PROP) inferInstance .out P]
    [hm : ∀ i, MakeMonPredAt .indexToProp i P (Φ i)] :
    AsEmpValid d φ io PROP bi ioP iprop(∀ i, Φ i) where
  as_emp_valid := by
    constructor
    · refine fun hd hφ => forall_intro fun i => ?_
      exact ((monPred_at_emp_valid P).mp
        (inst.as_emp_valid_0.as_emp_valid.left hd hφ) i).trans (hm i).make_monPred_at.mp
    · intro hd hP
      refine inst.as_emp_valid_0.as_emp_valid.right hd ((monPred_at_emp_valid P).mpr fun i => ?_)
      calc
        _ ⊢ ∀ a, Φ a       := hP
        _ ⊢ Φ i            := forall_elim i
        _ ⊢ P.monPred_at i := (hm i).make_monPred_at.mpr

@[ipm_backtrack, rocq_alias as_emp_valid_monPred_at_wand]
instance asEmpValid_monPred_at_wand (d : AsEmpValid.Direction) (φ : Prop) io ioP
    (P Q : MonPred I PROP) (Φ Ψ : I.car → PROP)
    [inst : AsEmpValid0 d φ .in (MonPred I PROP) inferInstance .in iprop(P -∗ Q)]
    [h1 : ∀ i, MakeMonPredAt .indexToProp i P (Φ i)]
    [h2 : ∀ i, MakeMonPredAt .indexToProp i Q (Ψ i)] :
    AsEmpValid d φ io PROP bi ioP iprop(∀ i, Φ i -∗ Ψ i) where
  as_emp_valid := by
    constructor
    · refine fun hd hφ => forall_intro fun i => entails_wand ?_
      calc
        _ ⊢ P.monPred_at i := (h1 i).make_monPred_at.mpr
        _ ⊢ Q.monPred_at i := entails_at.mp (wand_entails (inst.as_emp_valid_0.as_emp_valid.left hd hφ)) i
        _ ⊢ Ψ i            := (h2 i).make_monPred_at.mp
    · intro hd hP
      refine inst.as_emp_valid_0.as_emp_valid.right hd (entails_wand <| entails_at.mpr fun i => ?_)
      calc
        _ ⊢ Φ i            := (h1 i).make_monPred_at.mp
        _ ⊢ Ψ i            := wand_entails <| hP.trans <| forall_elim i
        _ ⊢ Q.monPred_at i := (h2 i).make_monPred_at.mpr

@[ipm_backtrack, rocq_alias as_emp_valid_monPred_at_equiv]
instance asEmpValid_monPred_at_equiv (d : AsEmpValid.Direction) (φ : Prop) io ioP
    (P Q : MonPred I PROP) (Φ Ψ : I.car → PROP)
    [inst : AsEmpValid0 d φ .in (MonPred I PROP) inferInstance .in iprop(P ∗-∗ Q)]
    [h1 : ∀ i, MakeMonPredAt .indexToProp i P (Φ i)]
    [h2 : ∀ i, MakeMonPredAt .indexToProp i Q (Ψ i)] :
    AsEmpValid d φ io PROP bi ioP iprop(∀ i, Φ i ∗-∗ Ψ i) where
  as_emp_valid := by
    constructor
    · refine fun hd hφ => forall_intro fun i => equiv_wandIff ?_
      constructor
      · calc
          _ ⊢ P.monPred_at i := (h1 i).make_monPred_at.mpr
          _ ⊢ Q.monPred_at i :=
              entails_at.mp (wandIff_equiv (inst.as_emp_valid_0.as_emp_valid.left hd hφ)).mp i
          _ ⊢ Ψ i            := (h2 i).make_monPred_at.mp
      · calc
          _ ⊢ Q.monPred_at i := (h2 i).make_monPred_at.mpr
          _ ⊢ P.monPred_at i :=
              entails_at.mp (wandIff_equiv (inst.as_emp_valid_0.as_emp_valid.left hd hφ)).mpr i
          _ ⊢ Φ i            := (h1 i).make_monPred_at.mp
    · intro hd hP
      refine inst.as_emp_valid_0.as_emp_valid.right hd (equiv_wandIff ⟨?_, ?_⟩)
      · refine entails_at.mpr fun i => ?_
        calc
          _ ⊢ Φ i            := (h1 i).make_monPred_at.mp
          _ ⊢ Ψ i            := (wandIff_equiv (hP.trans (forall_elim i))).mp
          _ ⊢ Q.monPred_at i := (h2 i).make_monPred_at.mpr
      · refine entails_at.mpr fun i => ?_
        calc
          _ ⊢ Ψ i            := (h2 i).make_monPred_at.mp
          _ ⊢ Φ i            := (wandIff_equiv <| hP.trans (forall_elim i)).mpr
          _ ⊢ P.monPred_at i := (h1 i).make_monPred_at.mpr

/-! ### FromAssumption -/

/-
  The index `i` is an output in the synthesis of `MakeMonPredAt`, which is
  then used as an input argument for `IsBiIndexRel`.
-/
set_option synthInstance.checkSynthOrder false in
@[ipm_backtrack, rocq_alias from_assumption_make_monPred_at_l]
instance fromAssumption_make_monPred_at_l (p : Bool) (i j : I.car)
    (P : MonPred I PROP) (𝓟 : PROP)
    [hm : MakeMonPredAt .propToIndex i P 𝓟] [hr : IsBiIndexRel j i] :
    FromAssumption p .in (P.monPred_at j) 𝓟 where
  from_assumption := calc
    _ ⊢ P.monPred_at j := intuitionisticallyIf_elim
    _ ⊢ P.monPred_at i := P.monPred_mono hr.is_bi_index_rel
    _ ⊢ 𝓟              := hm.make_monPred_at.mp

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

/-! ### FromExists -/

@[rocq_alias from_exist_monPred_at]
instance fromExists_monPred_at {α} (P : MonPred I PROP) (Φ : α → MonPred I PROP)
    (Ψ : α → PROP) (i : I.car)
    [h : FromExists P Φ] [hm : ∀ a, MakeMonPredAt .indexToProp i (Φ a) (Ψ a)] :
    FromExists (P.monPred_at i) Ψ where
  from_exists := calc
    _ ⊢ ∃ a, (Φ a).monPred_at i      := exists_mono fun a => (hm a).make_monPred_at.mpr
    _ ⊢ iprop(∃ x, Φ x).monPred_at i := (monPred_at_exist i Φ).mpr
    _ ⊢ P.monPred_at i               := entails_at.mp h.from_exists i

@[rocq_alias from_exist_monPred_at_ex]
instance fromExists_monPred_at_ex (P : MonPred I PROP) (Φ : I.car → PROP) (i : I.car)
    [hm : ∀ j, MakeMonPredAt .indexToProp j P (Φ j)] :
    FromExists (iprop(<subj> P).monPred_at i) Φ where
  from_exists := exists_mono fun j => (hm j).make_monPred_at.mpr

/-! ### IntoExists -/

@[rocq_alias into_exist_monPred_at]
instance intoExists_monPred_at {α} (P : MonPred I PROP) (Φ : α → MonPred I PROP)
    (Ψ : α → PROP) (i : I.car)
    [h : IntoExists P Φ] [hm : ∀ a, MakeMonPredAt .indexToProp i (Φ a) (Ψ a)] :
    IntoExists (P.monPred_at i) Ψ where
  into_exists := calc
    _ ⊢ iprop(∃ x, Φ x).monPred_at i := entails_at.mp h.into_exists i
    _ ⊢ ∃ x, (Φ x).monPred_at i      := (monPred_at_exist i Φ).mp
    _ ⊢ ∃ a, Ψ a                     := exists_mono fun a => (hm a).make_monPred_at.mp

@[rocq_alias into_exist_monPred_at_ex]
instance intoExists_monPred_at_ex (P : MonPred I PROP) (Φ : I.car → PROP) (i : I.car)
    [hm : ∀ j, MakeMonPredAt .indexToProp j P (Φ j)] :
    IntoExists (iprop(<subj> P).monPred_at i) Φ where
  into_exists := exists_mono fun j => (hm j).make_monPred_at.mp

/-! ### FromForall -/

@[rocq_alias from_forall_monPred_at_wand]
instance fromForall_monPred_at_wand (P Q : MonPred I PROP) (Φ Ψ : I.car → PROP) (i : I.car)
    [h1 : ∀ j, MakeMonPredAt .indexToProp j P (Φ j)]
    [h2 : ∀ j, MakeMonPredAt .indexToProp j Q (Ψ j)] :
    FromForall (iprop(P -∗ Q).monPred_at i)
      (fun j => iprop(⌜I.rel.le i j⌝ → (Φ j -∗ Ψ j))) where
  from_forall := forall_mono fun j => imp_mono_right <|
    wand_mono (h1 j).make_monPred_at.mp (h2 j).make_monPred_at.mpr

@[rocq_alias from_forall_monPred_at_impl]
instance fromForall_monPred_at_imp (P Q : MonPred I PROP) (Φ Ψ : I.car → PROP) (i : I.car)
    [h1 : ∀ j, MakeMonPredAt .indexToProp j P (Φ j)]
    [h2 : ∀ j, MakeMonPredAt .indexToProp j Q (Ψ j)] :
    FromForall (iprop(P → Q).monPred_at i)
      (fun j => iprop(⌜I.rel.le i j⌝ → (Φ j → Ψ j))) where
  from_forall := forall_mono fun j => imp_mono_right <|
    imp_mono (h1 j).make_monPred_at.mp (h2 j).make_monPred_at.mpr

@[rocq_alias from_forall_monPred_at]
instance fromForall_monPred_at {α} (P : MonPred I PROP) (Φ : α → MonPred I PROP)
    (Ψ : α → PROP) (i : I.car)
    [h : FromForall P Φ] [hm : ∀ a, MakeMonPredAt .indexToProp i (Φ a) (Ψ a)] :
    FromForall (P.monPred_at i) Ψ where
  from_forall := calc
    _ ⊢ ∀ a, (Φ a).monPred_at i      := forall_mono fun a => (hm a).make_monPred_at.mpr
    _ ⊢ iprop(∀ x, Φ x).monPred_at i := (monPred_at_forall i Φ).mpr
    _ ⊢ P.monPred_at i               := entails_at.mp h.from_forall i

@[rocq_alias from_forall_monPred_at_objectively]
instance fromForall_monPred_at_objectively (P : MonPred I PROP) (Φ : I.car → PROP) (i : I.car)
    [hm : ∀ j, MakeMonPredAt .indexToProp j P (Φ j)] :
    FromForall (iprop(<obj> P).monPred_at i) Φ where
  from_forall := forall_mono fun j => (hm j).make_monPred_at.mpr

/-! ### IntoForall -/

@[ipm_backtrack, rocq_alias into_forall_monPred_at]
instance intoForall_monPred_at {α} (P : MonPred I PROP) (Φ : α → MonPred I PROP)
    (Ψ : α → PROP) (i : I.car)
    [h : IntoForall P Φ] [hm : ∀ a, MakeMonPredAt .indexToProp i (Φ a) (Ψ a)] :
    IntoForall (P.monPred_at i) Ψ where
  into_forall := calc
    _ ⊢ iprop(∀ x, Φ x).monPred_at i := entails_at.mp h.into_forall i
    _ ⊢ ∀ x, (Φ x).monPred_at i      := (monPred_at_forall i Φ).mp
    _ ⊢ ∀ a, Ψ a                     := forall_mono fun a => (hm a).make_monPred_at.mp

@[rocq_alias into_forall_monPred_at_index]
instance (priority := low) intoForall_monPred_at_index (P : MonPred I PROP) (i : I.car) :
    IntoForall (P.monPred_at i) (fun j => iprop(⌜I.rel.le i j⌝ → P.monPred_at j)) where
  into_forall := forall_intro fun _ => (forall_intro (P.monPred_mono ·)).trans pure_imp_forall.mpr

@[rocq_alias into_forall_monPred_at_objectively]
instance intoForall_monPred_at_objectively (P : MonPred I PROP) (Φ : I.car → PROP) (i : I.car)
    [hm : ∀ j, MakeMonPredAt .indexToProp j P (Φ j)] :
    IntoForall (iprop(<obj> P).monPred_at i) Φ where
  into_forall := forall_mono fun j => (hm j).make_monPred_at.mp

/-! ### IsExcept0 -/

@[rocq_alias is_except_0_monPred_at]
instance isExcept0_monPred_at (P : MonPred I PROP) (i : I.car) [h : IsExcept0 P] :
    IsExcept0 (P.monPred_at i) where
  is_except0 := (monPred_at_except_0 i P).mpr.trans (entails_at.mp h.is_except0 i)

/-! ### IntoExcept0 -/


set_option synthInstance.checkSynthOrder false in
/--
  `P.monPred_at i` is an input argument of `IntoExcept0`.
  Unifying the conclusion assigns the metavariables before the assumption is involved.
-/
@[rocq_alias into_except_0_monPred_at_fwd]
instance intoExcept0_monPred_at_fwd (P Q : MonPred I PROP) (𝓠 : PROP) (i : I.car)
    [h : IntoExcept0 .in P Q] [hm : MakeMonPredAt .indexToProp i Q 𝓠] :
    IntoExcept0 .in (P.monPred_at i) 𝓠 where
  into_except0 := calc
    _ ⊢ iprop(◇ Q).monPred_at i := entails_at.mp h.into_except0 i
    _ ⊢ ◇ Q.monPred_at i        := (monPred_at_except_0 i Q).mp
    _ ⊢ ◇ 𝓠                     := except0_mono hm.make_monPred_at.mp

set_option synthInstance.checkSynthOrder false in
/--
  `Q.monPred_at i` is an input argument of `IntoExcept0`.
  Unifying the conclusion assigns the metavariables before the assumption is involved.
-/
@[rocq_alias into_except_0_monPred_at_bwd]
instance intoExcept0_monPred_at_bwd (P Q : MonPred I PROP) (𝓟 : PROP) (i : I.car)
    [h : IntoExcept0 .out P Q] [hm : MakeMonPredAt .indexToProp i P 𝓟] :
    IntoExcept0 .out 𝓟 (Q.monPred_at i) where
  into_except0 := calc
    𝓟 ⊢ P.monPred_at i           := hm.make_monPred_at.mpr
    _ ⊢ iprop(◇ Q).monPred_at i  := entails_at.mp h.into_except0 i
    _ ⊢ ◇ Q.monPred_at i         := (monPred_at_except_0 i Q).mp

/-! ### IntoWand -/

private theorem intoWand_monPred_at_core {p q : Bool} {R P Q : MonPred I PROP} {𝓟 𝓠 : PROP}
    {i j : I.car} (hij : I.rel.le i j) (h : □?p R ⊢ □?q P -∗ Q)
    (h1 : 𝓟 ⊢ P.monPred_at j) (h2 : Q.monPred_at j ⊢ 𝓠) :
    □?p (R.monPred_at i) ⊢ □?q 𝓟 -∗ 𝓠 := calc
  _ ⊢ □?p (R.monPred_at j) := intuitionisticallyIf_mono (R.monPred_mono hij)
  _ ⊢ (iprop(□?p R) : MonPred I PROP).monPred_at j :=
      (monPred_at_intuitionistically_if j p R).mpr
  _ ⊢ (iprop(□?q P -∗ Q) : MonPred I PROP).monPred_at j := entails_at.mp h j
  _ ⊢ (iprop(□?q P) : MonPred I PROP).monPred_at j -∗ Q.monPred_at j :=
      monPred_wand_force j iprop(□?q P) Q
  _ ⊢ □?q 𝓟 -∗ 𝓠 := wand_mono
      ((intuitionisticallyIf_mono h1).trans (monPred_at_intuitionistically_if j q P).mpr) h2

@[rocq_alias into_wand_monPred_at_unknown_unknown]
instance intoWand_monPred_at_unknown_unknown (p q : Bool) (R P Q : MonPred I PROP)
    (𝓟 𝓠 : PROP) (i : I.car)
    [h : IntoWand p q R .unknown P Q]
    [h1 : MakeMonPredAt .indexToProp i P 𝓟] [h2 : MakeMonPredAt .indexToProp i Q 𝓠] :
    IntoWand p q (R.monPred_at i) .unknown 𝓟 𝓠 where
  into_wand := intoWand_monPred_at_core (Std.Refl.refl i) h.into_wand
    h1.make_monPred_at.mpr h2.make_monPred_at.mp

@[ipm_backtrack, rocq_alias into_wand_monPred_at_unknown_known]
instance intoWand_monPred_at_unknown_known (p q : Bool) (R P Q : MonPred I PROP)
    (𝓟 : PROP) (i j : I.car)
    [hr : IsBiIndexRel i j] [h : IntoWand p q R .unknown P Q] [hm : MakeMonPredAt .indexToProp j P 𝓟] :
    IntoWand p q (R.monPred_at i) (.matching .result) 𝓟 (Q.monPred_at j) where
  into_wand := intoWand_monPred_at_core hr.is_bi_index_rel h.into_wand
    hm.make_monPred_at.mpr .rfl

@[ipm_backtrack, rocq_alias into_wand_monPred_at_known_unknown_le]
instance intoWand_monPred_at_known_unknown_le (p q : Bool) (R P Q : MonPred I PROP)
    (𝓠 : PROP) (i j : I.car)
    [hr : IsBiIndexRel i j] [h : IntoWand p q R .unknown P Q] [hm : MakeMonPredAt .indexToProp j Q 𝓠] :
    IntoWand p q (R.monPred_at i) (.matching .argument) (P.monPred_at j) 𝓠 where
  into_wand := intoWand_monPred_at_core hr.is_bi_index_rel h.into_wand
    .rfl hm.make_monPred_at.mp

/-
  The index `i` occurs only in the `semiOutParamIPM` slot `P.monPred_at i`, which
  in this case in an input given `.matching .argument`.
-/
set_option synthInstance.checkSynthOrder false in
@[ipm_backtrack, rocq_alias into_wand_monPred_at_known_unknown_ge]
instance intoWand_monPred_at_known_unknown_ge (p q : Bool) (R P Q : MonPred I PROP)
    (𝓠 : PROP) (i j : I.car)
    [hr : IsBiIndexRel i j] [h : IntoWand p q R .unknown P Q]
    [hm : MakeMonPredAt .indexToProp j Q 𝓠] :
    IntoWand p q (R.monPred_at j) (.matching .argument) (P.monPred_at i) 𝓠 where
  into_wand := intoWand_monPred_at_core (Std.Refl.refl j) h.into_wand
    (P.monPred_mono hr.is_bi_index_rel) hm.make_monPred_at.mp

#rocq_ignore into_wand_wand'_monPred "Subsumed by the `WandMode` parameter of `IntoWand`"
#rocq_ignore into_wand_impl'_monPred "Subsumed by the `WandMode` parameter of `IntoWand`"

/-! ### ElimModal -/

@[rocq_alias elim_modal_at]
instance elimModal_at (φ : Prop) (p : Bool) io (p' : Bool) (𝓟 𝓟' : PROP)
    (P P' : MonPred I PROP) (V : I.car)
    [h : ElimModal φ p io p' iprop(⎡𝓟⎤ : MonPred I PROP) iprop(⎡𝓟'⎤) P P'] :
    ElimModal φ p io p' 𝓟 𝓟' (P.monPred_at V) (P'.monPred_at V) where
  elim_modal hφ := by
    refine .trans ?_ (entails_at.mp (h.elim_modal hφ) V)
    refine sep_mono (monPred_at_intuitionistically_if V p iprop(⎡𝓟⎤)).mpr ?_
    refine .trans (forall_intro fun j =>
      (forall_intro fun hVj => ?_).trans pure_imp_forall.mpr)
      (monPred_at_wand V iprop(□?p' ⎡𝓟'⎤) P').mpr
    exact wand_mono
      ((monPred_at_intuitionistically_if j p' iprop(⎡𝓟'⎤)).mp) (P'.monPred_mono hVj)

@[rocq_alias elim_modal_at_bupd_goal]
instance elimModal_at_bupd_goal [BIUpdate PROP] (φ : Prop) (p : Bool) io (p' : Bool)
    (𝓟 𝓟' : PROP) (Q Q' : MonPred I PROP) (i : I.car)
    [h : ElimModal φ p io p' 𝓟 𝓟' iprop(|==> Q.monPred_at i) iprop(|==> Q'.monPred_at i)] :
    ElimModal φ p io p' 𝓟 𝓟'
      (iprop(|==> Q).monPred_at i)
      (iprop(|==> Q').monPred_at i) where
  elim_modal hφ := calc
    _ ⊢ □?p 𝓟 ∗ (□?p' 𝓟' ==∗ Q'.monPred_at i) :=
        sep_mono_right <| wand_mono_right (monPred_at_bupd i Q').mp
    _ ⊢ |==> Q.monPred_at i                    := h.elim_modal hφ
    _ ⊢ iprop(|==> Q).monPred_at i             := (monPred_at_bupd i Q).mpr

@[rocq_alias elim_modal_at_bupd_hyp]
instance elimModal_at_bupd_hyp [BIUpdate PROP] (φ : Prop) (p : Bool) io (p' : Bool)
    (P : MonPred I PROP) (𝓟 𝓟' 𝓠 𝓠' : PROP) (i : I.car)
    [hm : MakeMonPredAt .indexToProp i P 𝓟]
    [h : ElimModal φ p io p' iprop(|==> 𝓟) 𝓟' 𝓠 𝓠'] :
    ElimModal φ p io p' (iprop(|==> P).monPred_at i) 𝓟' 𝓠 𝓠' where
  elim_modal hφ :=
    (sep_mono_left <| intuitionisticallyIf_mono
      ((monPred_at_bupd i P).mp.trans <| BIUpdate.mono hm.make_monPred_at.mp)).trans <|
    h.elim_modal hφ

@[rocq_alias elim_modal_at_fupd_goal]
instance elimModal_at_fupd_goal [BIFUpdate PROP] (φ : Prop) (p : Bool) io (p' : Bool)
    (E1 E2 E3 : CoPset) (𝓟 𝓟' : PROP) (Q Q' : MonPred I PROP) (i : I.car)
    [h : ElimModal φ p io p' 𝓟 𝓟'
          iprop(|={E1,E3}=> Q.monPred_at i) iprop(|={E2,E3}=> Q'.monPred_at i)] :
    ElimModal φ p io p' 𝓟 𝓟'
      (iprop(|={E1,E3}=> Q).monPred_at i)
      (iprop(|={E2,E3}=> Q').monPred_at i) where
  elim_modal hφ :=
    ((sep_mono_right <| wand_mono_right (monPred_at_fupd i E2 E3 Q').mp).trans <|
      h.elim_modal hφ).trans
    (monPred_at_fupd i E1 E3 Q).mpr

@[rocq_alias elim_modal_at_fupd_hyp]
instance elimModal_at_fupd_hyp [BIFUpdate PROP] (φ : Prop) (p : Bool) io (p' : Bool)
    (E1 E2 : CoPset) (P : MonPred I PROP) (𝓟 𝓟' 𝓠 𝓠' : PROP) (i : I.car)
    [hm : MakeMonPredAt .indexToProp i P 𝓟]
    [h : ElimModal φ p io p' iprop(|={E1,E2}=> 𝓟) 𝓟' 𝓠 𝓠'] :
    ElimModal φ p io p' (iprop(|={E1,E2}=> P).monPred_at i) 𝓟' 𝓠 𝓠' where
  elim_modal hφ :=
    (sep_mono_left <| intuitionisticallyIf_mono
      ((monPred_at_fupd i E1 E2 P).mp.trans <| BIFUpdate.mono hm.make_monPred_at.mp)).trans <|
    h.elim_modal hφ

/-! ### AddModal -/

@[rocq_alias add_modal_at_bupd_goal]
instance addModal_at_bupd_goal [BIUpdate PROP] (𝓟 𝓟' : PROP) (Q : MonPred I PROP) (i : I.car)
    [h : AddModal 𝓟 𝓟' iprop(|==> Q.monPred_at i)] :
    AddModal 𝓟 𝓟' (iprop(|==> Q).monPred_at i) where
  add_modal := calc
    _ ⊢ 𝓟 ∗ (𝓟' ==∗ Q.monPred_at i) := sep_mono_right <| wand_mono_right (monPred_at_bupd i Q).mp
    _ ⊢ |==> Q.monPred_at i         := h.add_modal
    _ ⊢ iprop(|==> Q).monPred_at i  := (monPred_at_bupd i Q).mpr

@[rocq_alias add_modal_at_fupd_goal]
instance addModal_at_fupd_goal [BIFUpdate PROP] (E1 E2 : CoPset) (𝓟 𝓟' : PROP)
    (Q : MonPred I PROP) (i : I.car)
    [h : AddModal 𝓟 𝓟' iprop(|={E1,E2}=> Q.monPred_at i)] :
    AddModal 𝓟 𝓟' (iprop(|={E1,E2}=> Q).monPred_at i) where
  add_modal := calc
    _ ⊢ 𝓟 ∗ (𝓟' ={E1,E2}=∗ Q.monPred_at i)  :=
        sep_mono_right <| wand_mono_right (monPred_at_fupd i E1 E2 Q).mp
    _ ⊢ |={E1, E2}=> Q.monPred_at i         := h.add_modal
    _ ⊢ iprop(|={E1, E2}=> Q).monPred_at i  := (monPred_at_fupd i E1 E2 Q).mpr

/-! ### ElimAcc -/

@[rocq_alias elim_acc_at_None]
instance elimAcc_at_none [BIFUpdate PROP] {X : Type} (φ : Prop) (E1 E2 E3 E4 : CoPset)
    (α β : X → PROP) (α' β' : X → MonPred I PROP)
    (P : MonPred I PROP) (P'x : X → MonPred I PROP) (i : I.car)
    [hα : ∀ x, MakeEmbed (α x) (α' x)] [hβ : ∀ x, MakeEmbed (β x) (β' x)]
    [h : ElimAcc (X := X) φ (fupd E1 E2) (fupd E3 E4) α' β'
          (fun _ => none) P P'x] :
    ElimAcc (X := X) φ (fupd E1 E2) (fupd E3 E4) α β (fun _ => none)
      (P.monPred_at i) (fun x => (P'x x).monPred_at i) where
  elim_acc := by
    refine fun hφ => entails_wand <| wand_intro <| (sep_mono ?_ ?_).trans
      (entails_at.mp ((sep_mono_left <| wand_entails <| h.elim_acc hφ).trans wand_elim_left) i)
    -- Continuation
    · refine .trans ?_ (monPred_at_forall i _).mpr
      refine forall_mono fun x => .trans ?_ (monPred_at_wand i (α' x) (P'x x)).mpr
      refine forall_intro fun j => (forall_intro fun hij => ?_).trans pure_imp_forall.mpr
      exact wand_mono (entails_at.mp (hα x).make_embed.mpr j) ((P'x x).monPred_mono hij)
    -- Accessor
    · simp only [accessor, Option.getD]
      refine .trans ?_ (monPred_at_fupd i E1 E2 _).mpr
      refine BIFUpdate.mono <| .trans ?_ (monPred_at_exist i _).mpr
      refine exists_mono fun x => sep_mono (entails_at.mp (hα x).make_embed.mp i) ?_
      exact forall_intro fun j =>
        (forall_intro fun _ => wand_mono_left <| entails_at.mp (hβ x).make_embed.mpr j).trans
        pure_imp_forall.mpr

@[rocq_alias elim_acc_at_Some]
instance elimAcc_at_some [BIFUpdate PROP] {X : Type} (φ : Prop) (E1 E2 E3 E4 : CoPset)
    (α β γ : X → PROP) (α' β' γ' : X → MonPred I PROP)
    (P : MonPred I PROP) (P'x : X → MonPred I PROP) (i : I.car)
    [hα : ∀ x, MakeEmbed (α x) (α' x)] [hβ : ∀ x, MakeEmbed (β x) (β' x)]
    [hγ : ∀ x, MakeEmbed (γ x) (γ' x)]
    [h : ElimAcc (X := X) φ (fupd E1 E2) (fupd E3 E4) α' β'
          (fun x => some (γ' x)) P P'x] :
    ElimAcc (X := X) φ (fupd E1 E2) (fupd E3 E4) α β
      (fun x => some (γ x)) (P.monPred_at i) (fun x => (P'x x).monPred_at i) where
  elim_acc := by
    refine fun hφ => entails_wand <| wand_intro <| (sep_mono ?_ ?_).trans
      (entails_at.mp ((sep_mono_left <| wand_entails <| h.elim_acc hφ).trans wand_elim_left) i)
    -- Continuation
    · refine .trans ?_ (monPred_at_forall i _).mpr
      refine forall_mono fun x => .trans ?_ (monPred_at_wand i (α' x) (P'x x)).mpr
      refine forall_intro fun j => (forall_intro fun hij => ?_).trans pure_imp_forall.mpr
      exact wand_mono (entails_at.mp (hα x).make_embed.mpr j) ((P'x x).monPred_mono hij)
    -- Accessor
    · simp only [accessor, Option.getD]
      refine .trans ?_ (monPred_at_fupd i E1 E2 _).mpr
      refine BIFUpdate.mono <| .trans ?_ (monPred_at_exist i _).mpr
      refine exists_mono fun x => sep_mono (entails_at.mp (hα x).make_embed.mp i) ?_
      refine forall_intro fun j => (forall_intro fun _ => ?_).trans pure_imp_forall.mpr
      exact wand_mono (entails_at.mp (hβ x).make_embed.mpr j)
        ((BIFUpdate.mono <| entails_at.mp (hγ x).make_embed.mp j).trans
          (monPred_at_fupd j E3 E4 (γ' x)).mpr)

/-! ### ElimInv -/

@[rocq_alias elim_inv_embed_with_close]
instance elimInv_embed_with_close {X : Type} (φ : Prop) (𝓟inv 𝓟in : PROP)
    (𝓟out 𝓟close : X → PROP) (Pin : MonPred I PROP) (Pout Pclose : X → MonPred I PROP)
    (Q Q' : MonPred I PROP)
    [h : ∀ i, ElimInv φ X 𝓟inv 𝓟in 𝓟out true (some 𝓟close)
          (Q.monPred_at i) (fun _ => Q'.monPred_at i)]
    [hin : MakeEmbed 𝓟in Pin] [hout : ∀ x, MakeEmbed (𝓟out x) (Pout x)]
    [hcl : ∀ x, MakeEmbed (𝓟close x) (Pclose x)] :
    ElimInv φ X (iprop(⎡𝓟inv⎤) : MonPred I PROP) Pin Pout true (some Pclose)
      Q (fun _ => Q') where
  elim_inv := by
    intro hφ
    refine entails_at.mpr fun j => .trans ?_ ((h j).elim_inv hφ)
    refine sep_mono_right (sep_mono (entails_at.mp hin.make_embed.mpr j) ?_)
    refine .trans (monPred_at_forall j _).mp (forall_mono fun x => ?_)
    refine .trans ((forall_elim j).trans <| pure_imp_elim <| Std.Refl.refl j) ?_
    exact wand_mono_left <|
      sep_mono (entails_at.mp (hout x).make_embed.mp j) (entails_at.mp (hcl x).make_embed.mp j)

@[rocq_alias elim_inv_embed_without_close]
instance elimInv_embed_without_close {X : Type} (φ : Prop) (𝓟inv 𝓟in : PROP)
    (𝓟out : X → PROP) (Pin : MonPred I PROP) (Pout : X → MonPred I PROP)
    (Q : MonPred I PROP) (Q' : X → MonPred I PROP)
    [h : ∀ i, ElimInv φ X 𝓟inv 𝓟in 𝓟out false none
          (Q.monPred_at i) (fun x => (Q' x).monPred_at i)]
    [hin : MakeEmbed 𝓟in Pin] [hout : ∀ x, MakeEmbed (𝓟out x) (Pout x)] :
    ElimInv φ X (iprop(⎡𝓟inv⎤) : MonPred I PROP) Pin Pout false none Q Q' where
  elim_inv := by
    intro hφ
    refine entails_at.mpr fun j => .trans ?_ ((h j).elim_inv hφ)
    refine sep_mono_right (sep_mono (entails_at.mp hin.make_embed.mpr j) ?_)
    refine .trans (monPred_at_forall j _).mp (forall_mono fun x => ?_)
    refine .trans ((forall_elim j).trans <| pure_imp_elim <| Std.Refl.refl j) ?_
    exact wand_mono_left <| sep_mono_left <| entails_at.mp (hout x).make_embed.mp j

end BIInstances

section SbiInstances

variable {I : BiIndex} {PROP : Type _} [Sbi PROP]

/-! #### IntoInternalEq -/

@[rocq_alias into_internal_eq_monPred_at]
instance intoInternalEq_monPred_at {A : Type _} [OFE A] (x y : A)
    (P : MonPred I PROP) (i : I.car) [h : IntoInternalEq P x y] :
    IntoInternalEq (P.monPred_at i) x y where
  into_internal_eq := (entails_at.mp h.into_internal_eq i).trans (monPred_at_internal_eq i x y).mp

/-! #### FromForall -/

@[rocq_alias from_forall_monPred_at_plainly]
instance fromForall_monPred_at_plainly (P : MonPred I PROP) (Φ : I.car → PROP) (i : I.car)
    [hm : ∀ j, MakeMonPredAt .indexToProp j P (Φ j)] :
    FromForall ((iprop(■ P) : MonPred I PROP).monPred_at i) (fun j => iprop(■ (Φ j))) where
  from_forall := (forall_mono fun j => plainly_mono (hm j).make_monPred_at.mpr).trans
    (monPred_at_plainly i P).mpr

/-! #### IntoForall -/

@[rocq_alias into_forall_monPred_at_plainly]
instance intoForall_monPred_at_plainly (P : MonPred I PROP) (Φ : I.car → PROP) (i : I.car)
    [hm : ∀ j, MakeMonPredAt .indexToProp j P (Φ j)] :
    IntoForall ((iprop(■ P) : MonPred I PROP).monPred_at i) (fun j => iprop(■ (Φ j))) where
  into_forall := (monPred_at_plainly i P).mp.trans
    (forall_mono fun j => plainly_mono (hm j).make_monPred_at.mp)

end SbiInstances
