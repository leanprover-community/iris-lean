/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.BI
import Iris.Algebra.OFE
import Iris.Algebra.CMRA
import Iris.Algebra.UPred
import Iris.Algebra.IProp
import Iris.Instances.UPred

namespace Iris

open COFE

/-- Apply an OFunctor at a fixed type -/
abbrev COFE.OFunctorPre.ap (F : OFunctorPre) (T : Type _) [OFE T] :=
  F T T

/-- Apply a list of OFunctors at a fixed type and index -/
abbrev BundledGFunctors.api (FF : BundledGFunctors) (τ : GType) (T : Type _) [OFE T] :=
  FF τ |>.fst |>.ap T

section ElemG

open OFE

class ElemG (FF : BundledGFunctors) (F : OFunctorPre) [RFunctorContractive F] where
  τ : GType
  transp : FF τ = ⟨F, ‹_›⟩

def ElemG.Bundle {GF F} [RFunctorContractive F] (E : ElemG GF F) [OFE T] : F.ap T → GF.api E.τ T :=
  (congrArg (OFunctorPre.ap · T) (Sigma.mk.inj E.transp).left).mpr

def ElemG.Unbundle {GF F} [RFunctorContractive F] (E : ElemG GF F) [OFE T] : GF.api E.τ T → F.ap T :=
  (congrArg (OFunctorPre.ap · T) (Sigma.mk.inj E.transp).left).mp

instance ElemG.Bundle.ne {GF F} [RFunctorContractive F] {E : ElemG GF F} [OFE T] :
    OFE.NonExpansive (E.Bundle (T := T)) where
  ne {n x1 x2} H := by
    simp [Bundle]
    let Z := Sigma.mk.inj E.transp |>.1.symm
    subst Z
    -- Not sure...
    sorry

instance ElemG.UnBundle.ne {GF F} [RFunctorContractive F] {E : ElemG GF F} [OFE T] :
    OFE.NonExpansive (E.Unbundle (T := T)) where
  ne {n x1 x2} H := sorry

end ElemG

section Fold

open Iris COFE UPred

variable {FF : BundledGFunctors}

/-- Isorecursive unfolding for each projection of FF. -/
def IProp.unfoldi : FF.api τ (IProp FF) -n> FF.api τ (IPre FF) :=
  OFunctor.map (IProp.fold FF) (IProp.unfold FF)

/-- Isorecursive folding for each projection of FF. -/
def IProp.foldi : FF.api τ (IPre FF) -n> FF.api τ (IProp FF) :=
  OFunctor.map (IProp.unfold FF) (IProp.fold FF)

theorem IProp.unfoldi_foldi (x : FF.api τ (IPre FF)) : unfoldi (foldi x) ≡ x := by
  refine .trans (OFunctor.map_comp (F := FF τ |>.fst) ..).symm ?_
  refine .trans ?_ (OFunctor.map_id (F := FF τ |>.fst) x)
  apply OFunctor.map_ne.eqv <;> intro _ <;> simp [IProp.unfold, IProp.fold]

theorem IProp.proj_fold_unfold (x : FF.api τ (IProp FF)) : foldi (unfoldi x) ≡ x := by
  refine .trans (OFunctor.map_comp (F := FF τ |>.fst) ..).symm ?_
  refine .trans ?_ (OFunctor.map_id (F := FF τ |>.fst) x)
  apply OFunctor.map_ne.eqv <;> intro _ <;> simp [IProp.unfold, IProp.fold]

end Fold

section iSingleton

open IProp OFE UPred

def iSingleton {GF} F [RFunctorContractive F] [E : ElemG GF F] (γ : GName) (v : F.ap (IProp GF)) : IResUR GF :=
  fun τ' γ' =>
    if H : (τ' = E.τ ∧ γ' = γ)
      then some (H.1 ▸ (unfoldi <| E.Bundle v))
      else none

theorem IResUR_op_eval {GF} (c1 c2 : IResUR GF) : (c1 • c2) τ' γ' = (c1 τ' γ') • (c2 τ' γ') := by
    simp [CMRA.op, optionOp]

instance {γ : GName} [RFunctorContractive F] [E : ElemG GF F] :
    OFE.NonExpansive (iSingleton F γ (GF := GF))  where
  ne {n x1 x2} H τ' γ' := by
    simp [iSingleton]
    split <;> try rfl
    simp [optionOp]
    rename_i h; rcases h with ⟨h1, h2⟩; subst h1; subst h2; simp
    exact NonExpansive.ne (NonExpansive.ne H)

theorem iSingleton_op {γ : GName} [RFunctorContractive F] [E : ElemG GF F]
    (x y : F.ap (IProp GF)) :
    (iSingleton F γ x) • iSingleton F γ y ≡ iSingleton F γ (x • y) := by
  intro τ' γ'
  unfold iSingleton
  simp [CMRA.op]
  split <;> try rfl
  simp [optionOp]
  rename_i h; rcases h with ⟨h1, h2⟩; subst h1; subst h2; simp
  simp [IProp.unfoldi]
  sorry

end iSingleton

def iOwn {GF F} [RFunctorContractive F] [ElemG GF F] (γ : GName) (v : F.ap (IProp GF)) : IProp GF :=
  UPred.ownM <| iSingleton F γ v

section iOwn

open IProp OFE UPred

variable {GF F} [RFunctorContractive F] [E : ElemG GF F]

instance iOwn_ne : NonExpansive (iOwn τ : F.ap (IProp GF) → IProp GF) where
  ne {n x1 x2} H := by unfold iOwn; exact NonExpansive.ne (NonExpansive.ne H)

theorem iOwn_op {a1 a2 : F.ap (IProp GF)} : iOwn γ (a1 • a2) ⊣⊢ iOwn γ a1 ∗ iOwn γ a2 :=
  UPred.ownM_eqv (iSingleton_op _ _).symm |>.trans (UPred.ownM_op _ _)

theorem iOwn_mono {a1 a2 : F.ap (IProp GF)} (H : a2 ≼ a1) : iOwn γ a1 ⊢ iOwn γ a2 := by
  rcases H with ⟨ac, Hac⟩
  rintro n x Hv ⟨clos, Hclos⟩
  -- Basically the heaps proof, want some other lemmas
  refine ⟨iSingleton F γ ac • clos, Hclos.trans ?_⟩
  intros τ' γ'
  refine .trans ?_ CMRA.op_assocN.symm
  rw [IResUR_op_eval]
  unfold iSingleton
  split
  · refine Dist.op_l ?_
    simp [CMRA.op, optionOp]
    -- Somehow use Hac
    sorry
  · simp [CMRA.op, optionOp]

-- Lemma own_mono γ a1 a2 : a2 ≼ a1 → own γ a1 ⊢ own γ a2.
-- Proof. move=> [c ->]. by rewrite own_op sep_elim_l. Qed.

theorem iOwn_cmraValid {a : F.ap (IProp GF)} : iOwn γ a ⊢ UPred.cmraValid a := by
  sorry
-- Lemma own_valid γ a : own γ a ⊢ ✓ a.
-- Proof. by rewrite !own_eq /own_def ownM_valid iRes_singleton_validI. Qed.


-- Lemma own_valid_2 γ a1 a2 : own γ a1 -∗ own γ a2 -∗ ✓ (a1 ⋅ a2).
-- Proof. apply entails_wand, wand_intro_r. by rewrite -own_op own_valid. Qed.
-- Lemma own_valid_3 γ a1 a2 a3 : own γ a1 -∗ own γ a2 -∗ own γ a3 -∗ ✓ (a1 ⋅ a2 ⋅ a3).
-- Proof. apply entails_wand. do 2 apply wand_intro_r. by rewrite -!own_op own_valid. Qed.


-- Lemma own_valid_r γ a : own γ a ⊢ own γ a ∗ ✓ a.
-- Proof. apply: bi.persistent_entails_r. apply own_valid. Qed.
-- Lemma own_valid_l γ a : own γ a ⊢ ✓ a ∗ own γ a.
-- Proof. by rewrite comm -own_valid_r. Qed.

-- Global Instance own_timeless γ a : Discrete a → Timeless (own γ a).
-- Proof. rewrite !own_eq /own_def. apply _. Qed.
-- Global Instance own_core_persistent γ a : CoreId a → Persistent (own γ a).
-- Proof. rewrite !own_eq /own_def; apply _. Qed.



end iOwn





end Iris


/-

def ElemG.api [OFE T] (E : ElemG FF τ F) (v : FF.api τ T) : F.ap T :=
  E.transp ▸ v

def ElemG.ap [OFE T] (E : ElemG FF τ F) (v : F.ap T) : FF.api τ T := by
  unfold Iris.GFunctors.api
  rw [E.transp]
  exact v

-- NB. I'm not sure if this instance is going to be a problem yet.
set_option synthInstance.checkSynthOrder false
instance instCMRAElemG [GF : IsGFunctors FF] {τ : outParam GType} [E : ElemG FF τ F] : CMRA (F.ap (IProp FF)) :=
  E.transp ▸ (GF τ).cmra

section ElemGTest
-- Test: The CMRA inferred by this is the same as the CMRA you get from the GFunctors instance

variable [GF : IsGFunctors FF] [E : ElemG FF τ (constOF Unit)]

def Inst1 : CMRA ((constOF Unit).ap (IProp FF)) :=
  COFE.OFunctor.constOF_RFunctor (B := Unit) |>.cmra
def Inst2 : CMRA ((constOF Unit).ap (IProp FF)) :=
  @instCMRAElemG FF (constOF Unit) GF τ E

-- #check Inst1
-- #check Inst2

-- example : @Inst1 FF GF = @Inst2 FF τ GF E := by
--   unfold Inst1
--   unfold Inst2
--   rfl

end ElemGTest

end ElemG


section iOwn

open Iris COFE UPred IProp

variable [GF : IsGFunctors FF]

-- MARKUSDE: NB. To avoid CMRA transports, we will define all of the core theorems
-- in terms of projections out of GFunctors  (eg. FF.api ..). These should be wrapped
-- using ElemG at the user level.







end iOwn
-/



/-




-- #check cmraValid
-- cmraValid for the singleton








-/
