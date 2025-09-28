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

/-- Apply an OFunctor at a fixed type -/
abbrev Iris.COFE.OFunctorPre.ap (F : Iris.COFE.OFunctorPre) (T : Type _) [OFE T] :=
  F T T

/-- Apply a list of OFunctors at a fixed type and index -/
abbrev Iris.GFunctors.api (FF : Iris.GFunctors) (τ : GType) (T : Type _) [OFE T] :=
  FF τ |>.ap T

section ElemG

open Iris COFE

class ElemG (FF : GFunctors) (τ : GType) (F : OFunctorPre) : Prop where
  transp : FF τ = F

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

section Fold

open Iris COFE UPred

variable [IsGFunctors FF]

/-- Isorecursive unfolding for each projection of FF. -/
def IProp.unfoldi : FF.api τ (IProp FF) -n> FF.api τ (IPre FF) :=
  OFunctor.map (IProp.fold FF) (IProp.unfold FF)

/-- Isorecursive folding for each projection of FF. -/
def IProp.foldi : FF.api τ (IPre FF) -n> FF.api τ (IProp FF) :=
  OFunctor.map (IProp.unfold FF) (IProp.fold FF)

theorem IProp.unfoldi_foldi (x : FF τ (IPre FF) (IPre FF)) : unfoldi (foldi x) ≡ x := by
  refine .trans (OFunctor.map_comp (F := FF τ) ..).symm ?_
  refine .trans ?_ (OFunctor.map_id (F := FF τ) x)
  apply OFunctor.map_ne.eqv <;> intro _ <;> simp [IProp.unfold, IProp.fold]

theorem IProp.proj_fold_unfold (x : FF τ (IProp FF) (IProp FF)) : foldi (unfoldi x) ≡ x := by
  refine .trans (OFunctor.map_comp (F := FF τ) ..).symm ?_
  refine .trans ?_ (OFunctor.map_id (F := FF τ) x)
  apply OFunctor.map_ne.eqv <;> intro _ <;> simp [IProp.unfold, IProp.fold]

end Fold

section iOwn

open Iris COFE UPred IProp

variable [GF : IsGFunctors FF]

-- MARKUSDE: NB. To avoid CMRA transports, we will define all of the core theorems
-- in terms of projections out of GFunctors  (eg. FF.api ..). These should be wrapped
-- using ElemG at the user level.


def iSingleton τ (γ : GName) (v : FF.api τ (IProp FF)) : IResUR FF :=
  fun τ' γ' =>
    if H : (τ' = τ ∧ γ' = γ)
      then some (H.1 ▸ (unfoldi <| v))
      else none

instance {γ : GName} : OFE.NonExpansive (iSingleton τ γ (FF := FF))  where
  ne {n x1 x2} H τ' γ' := by
    simp [iSingleton]
    split <;> try rfl
    simp [optionOp]
    rename_i h; rcases h with ⟨h1, h2⟩; subst h1; subst h2; simp
    apply OFE.NonExpansive.ne H

theorem iSingleton_op [IsGFunctors FF] (x y : FF τ (IProp FF) (IProp FF)):
    (iSingleton τ γ x) • iSingleton τ γ y ≡ iSingleton τ γ (x • y) := by
  intro τ' γ'
  unfold iSingleton
  simp [CMRA.op]
  split <;> try rfl
  simp [optionOp]
  rename_i h; rcases h with ⟨h1, h2⟩; subst h1; subst h2; simp
  simp [IProp.unfoldi]
  sorry

def iOwn (τ  : GType) (γ : GName) (v : FF τ (IProp FF) (IProp FF)) : IProp FF :=
  UPred.ownM <| iSingleton τ γ v

instance iOwn_ne : OFE.NonExpansive (iOwn τ γ : FF τ (IProp FF) (IProp FF) → IProp FF) where
  ne {n x1 x2} H := by
    unfold iOwn
    apply OFE.NonExpansive.ne
    apply OFE.NonExpansive.ne
    exact H

theorem iOwn_op {a1 a2 : FF.api τ (IProp FF)} :
    iOwn τ γ (a1 • a2) ⊣⊢ iOwn τ γ a1 ∗ iOwn τ γ a2 :=
  ownM_eqv (iSingleton_op _ _).symm |>.trans (ownM_op _ _)

theorem iOwn_mono {a1 a2 : FF.api τ (IProp FF)} (H : a2 ≼ a1) :
  iOwn τ γ a1 ⊢ iOwn τ γ a2 := sorry


end iOwn



/-




-- #check cmraValid
-- cmraValid for the singleton







-- Lemma own_mono γ a1 a2 : a2 ≼ a1 → own γ a1 ⊢ own γ a2.
-- Proof. move=> [c ->]. by rewrite own_op sep_elim_l. Qed.

-- Internal validity
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
--
-- Lemma later_own γ a : ▷ own γ a ⊢ ◇ ∃ b, own γ b ∧ ▷ (a ≡ b).
-- Proof.
--   rewrite own_eq /own_def later_ownM. apply exist_elim=> r.
--   assert (NonExpansive (λ r : iResUR Σ, r (inG_id i) !! γ)).
--   { intros n r1 r2 Hr. f_equiv. by specialize (Hr (inG_id i)). }
--   rewrite internal_eq_sym later_internal_eq_iRes_singleton.
--   rewrite (except_0_intro (uPred_ownM r)) -except_0_and. f_equiv.
--   rewrite and_exist_l. f_equiv=> b. rewrite and_exist_l. apply exist_elim=> r'.
--   rewrite assoc. apply and_mono_l.
--   etrans; [|apply ownM_mono, (cmra_included_l _ r')].
--   eapply (internal_eq_rewrite' _ _ uPred_ownM _); [apply and_elim_r|].
--   apply and_elim_l.
-- Qed.

-/
