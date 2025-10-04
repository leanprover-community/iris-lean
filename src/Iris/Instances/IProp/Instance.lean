/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

-- import Iris.Std.DepRewrite
import Iris.BI
import Iris.Algebra
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

theorem ElemG.transp_OFE {GF F} [RFunctorContractive F] (E : ElemG GF F) [OFE T] : F.ap T = GF.api E.τ T := by
  unfold OFunctorPre.ap
  unfold BundledGFunctors.api
  rw [E.transp]


theorem LemX {x y : Sort _} (H : x = y) : (Eq.symm (Eq.symm H)) = H := rfl

theorem OFE.cast_dist' [Iα : OFE α] [Iβ : OFE β] {x y : α}
    (Ht : α = β) (HIt : Ht.symm ▸ Iα = Iβ)  (H : x ≡{n}≡ y) :
    (Ht ▸ x) ≡{n}≡ (Ht ▸ y) := by
  subst Ht; subst HIt; exact H

-- set_option pp.deepTerms true
-- set_option pp.proofs true
-- set_option pp.all true
-- set_option pp.universes false

instance ElemG.Bundle.ne {GF F} [RFunctorContractive F] {E : ElemG GF F} [OFE T] :
    OFE.NonExpansive (E.Bundle (T := T)) where
  ne {n x1 x2} H := by
    rename_i IF IO
    have A1 := (@Iris.COFE.OFunctorPre.ap F T IO)
    have B1 := (@Iris.BundledGFunctors.api GF (@Iris.ElemG.τ GF F IF E) T IO)
    unfold Bundle
    unfold _proof_1
    simp
    apply (OFE.cast_dist' _ _ H)
    rw [LemX (@Iris.ElemG.transp_OFE T GF F IF E IO)]
    -- Reduce it to the problem of proving the RFunctors are equal?
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
  fun τ' => ⟨fun γ' =>
    if H : (τ' = E.τ ∧ γ' = γ)
      then some (H.1 ▸ (unfoldi <| E.Bundle v))
      else none⟩

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
  -- I believe it
  sorry

end iSingleton

def iOwn {GF F} [RFunctorContractive F] [E : ElemG GF F] (γ : GName) (v : F.ap (IProp GF)) : IProp GF :=
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
  simp
  split
  · refine Dist.op_l ?_
    simp [CMRA.op, optionOp]
    -- Should hold
    -- Somehow use Hac
    sorry
  · simp [CMRA.op, optionOp]

theorem iOwn_cmraValid {a : F.ap (IProp GF)} : iOwn γ a ⊢ UPred.cmraValid a := by
  refine .trans (UPred.ownM_valid _) ?_
  refine UPred.valid_entails (fun n H => ?_)
  specialize H E.τ
  sorry
  -- specialize H γ
  -- simp [iSingleton, CMRA.ValidN, optionValidN] at H
  -- -- Should hold
  -- sorry

theorem iOwn_cmraValid_op {a1 a2 : F.ap (IProp GF)} : iOwn γ a1 ∗ iOwn γ a2 ⊢ UPred.cmraValid (a1 • a2) :=
  iOwn_op.mpr.trans iOwn_cmraValid

theorem iOwn_valid_r {a : F.ap (IProp GF)} : iOwn γ a ⊢ iOwn γ a ∗ UPred.cmraValid a :=
  BI.persistent_entails_l iOwn_cmraValid

theorem iOwn_valid_l {a : F.ap (IProp GF)} : iOwn γ a ⊢ UPred.cmraValid a ∗ iOwn γ a :=
  BI.persistent_entails_r iOwn_cmraValid

instance {a : F.ap (IProp GF)} [CMRA.CoreId a] : BI.Persistent (iOwn γ a) where
  persistent := by
    simp [iOwn]
    refine .trans (UPred.persistently_ownM_core _) ?_
    refine BI.persistently_mono ?_
    refine BI.equiv_iff.mp ?_ |>.mp
    refine OFE.NonExpansive.eqv ?_
    -- Core is element-wise, then use CoreId inst
    sorry

theorem iOwn_alloc_strong_dep {f : GName → F.ap (IProp GF)} {P : GName → Prop}
    (HI : Infinite P) (Hv : ∀ γ, P γ → ✓ (f γ)) :
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ iOwn γ (f γ) := by
  refine .trans (Q := iprop(|==> ∃ m : IResUR GF, ⌜∃ γ, P γ ∧ m = iSingleton _ γ (f γ)⌝ ∧ UPred.ownM m)) ?_ ?_
  · refine .trans (UPred.ownM_unit _) <| BI.intuitionistically_elim.trans ?_
    refine UPred.ownM_updateP _ (fun n mz Hv => ?_)
    rcases HI with ⟨PE, HPE⟩
    refine ⟨iSingleton F (PE 0) (f (PE 0)), ⟨_, HPE.inc, rfl⟩, ?_⟩
    refine fun γ => ⟨fun γ' => ?_, ?_⟩
    · simp [CMRA.ValidN, optionValidN, CMRA.op?]
      rcases mz with (_|z) <;> simp only []
      · simp [iSingleton]
        rcases Classical.em (γ = ElemG.τ GF F ∧ γ' = PE 0) with (h | h)
        · simp_all
          -- By specialization of Hv, getting P from the Enum, and casting
          sorry
        · simp_all only [↓reduceDIte]
      · simp [CMRA.op, optionOp]
        -- ?
        sorry
    · exists (Poke PE 0)
      -- Remove the 0th term from the enum, it is still infinite
      sorry
  · refine BIUpdate.mono ?_
    refine BI.exists_elim (fun m => ?_)
    refine BI.pure_elim (φ := ∃ γ, P γ ∧ m = iSingleton F γ (f γ)) BI.and_elim_l ?_
    refine fun ⟨γ, HP, Hm⟩ => BI.and_elim_r' ?_
    refine BI.exists_intro' γ ?_
    refine BI.emp_sep.mpr.trans (BI.sep_mono ?_ ?_)
    · exact BI.pure_intro HP
    · rw [Hm]; exact .rfl

theorem iOwn_alloc_dep (f : GName → F.ap (IProp GF)) (Ha : ∀ γ, ✓ (f γ)) :
    ⊢ |==> ∃ γ, iOwn γ (f γ) :=
  (iOwn_alloc_strong_dep .Nat_True (fun _ => Ha ·)).trans <|
  BIUpdate.mono <| BI.exists_mono fun _ => BI.sep_elim_r

theorem iOwn_alloc (a : F.ap (IProp GF)) : ✓ a → ⊢ |==> ∃ γ, iOwn γ a :=
  fun Ha => iOwn_alloc_dep _ (fun _ => Ha)

theorem iOwn_updateP {P γ a} (Hupd : a ~~>: P) :
    iOwn γ a ⊢ |==> ∃ a' : F.ap (IProp GF), ⌜P a'⌝ ∗ iOwn γ a' := by
  refine .trans (Q := iprop(|==> ∃ m, ⌜ ∃ a', m = (iSingleton F γ a') ∧ P a' ⌝ ∧ UPred.ownM m)) ?_ ?_
  · apply UPred.ownM_updateP
    sorry
  · refine BIUpdate.mono ?_
    refine BI.exists_elim (fun m => ?_)
    refine BI.pure_elim_l (fun ⟨a', Hm, HP⟩ => ?_)
    refine BI.exists_intro' a' ?_
    subst Hm
    refine BI.persistent_entails_r ?_
    exact BI.pure_intro HP

theorem iOwn_update {γ} {a a' : F.ap (IProp GF)} (Hupd : a ~~> a') : iOwn γ a ⊢ |==> iOwn γ a' := by
  refine .trans (iOwn_updateP <| UpdateP.of_update Hupd) ?_
  refine BIUpdate.mono ?_
  refine BI.exists_elim (fun m => ?_)
  refine BI.pure_elim (a' = m) BI.sep_elim_l ?_
  rintro rfl
  exact BI.sep_elim_r

theorem iOwn_unit {γ} {ε : F.ap (IProp GF)} [IsUnit ε] : ⊢ |==> iOwn γ ε := by
  intro n x Hv He
  simp [bupd, UPred.bupd, iOwn, UPred.ownM]
  intro k yf Hk Hx
  refine ⟨x, ⟨Hx, ⟨x, ?_⟩⟩⟩
  -- At each coordinate they're equal due to optionOp, or equiv due to IsUnit (ie. coordinate γ)
  intro i j
  simp [CMRA.op, optionOp]
  sorry


/-
(** ** Allocation *)
(* TODO: This also holds if we just have ✓ a at the current step-idx, as Iris
   assertion. However, the map_updateP_alloc does not suffice to show this. *)
Lemma own_alloc_strong_dep (f : gname → A) (P : gname → Prop) :
  pred_infinite P →
  (∀ γ, P γ → ✓ (f γ)) →
  ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ own γ (f γ).
Proof.
  intros HPinf Hf.
  rewrite -(bupd_mono (∃ m, ⌜∃ γ, P γ ∧ m = iRes_singleton γ (f γ)⌝ ∧ uPred_ownM m)%I).
  - rewrite /bi_emp_valid (ownM_unit emp).
    apply bupd_ownM_updateP, (discrete_fun_singleton_updateP_empty _ (λ m, ∃ γ,
      m = {[ γ := inG_unfold (cmra_transport inG_prf (f γ)) ]} ∧ P γ));
      [|naive_solver].
    apply (alloc_updateP_strong_dep _ P _ (λ γ,
      inG_unfold (cmra_transport inG_prf (f γ)))); [done| |naive_solver].
    intros γ _ ?.
    by apply (cmra_morphism_valid inG_unfold), cmra_transport_valid, Hf.
  - apply exist_elim=>m; apply pure_elim_l=>-[γ [Hfresh ->]].
    by rewrite !own_eq /own_def -(exist_intro γ) pure_True // left_id.
Qed.
Lemma own_alloc_cofinite_dep (f : gname → A) (G : gset gname) :
  (∀ γ, γ ∉ G → ✓ (f γ)) → ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ own γ (f γ).
Proof.
  intros Ha.
  apply (own_alloc_strong_dep f (λ γ, γ ∉ G))=> //.
  apply (pred_infinite_set (C:=gset gname)).
  intros E. set (γ := fresh (G ∪ E)).
  exists γ. apply not_elem_of_union, is_fresh.
Qed.
Lemma own_alloc_dep (f : gname → A) :
  (∀ γ, ✓ (f γ)) → ⊢ |==> ∃ γ, own γ (f γ).
Proof.
  intros Ha. rewrite /bi_emp_valid (own_alloc_cofinite_dep f ∅) //; [].
  apply bupd_mono, exist_mono=>?. apply: sep_elim_r.
Qed.

Lemma own_alloc_strong a (P : gname → Prop) :
  pred_infinite P →
  ✓ a → ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ own γ a.
Proof. intros HP Ha. eapply (own_alloc_strong_dep (λ _, a)); eauto. Qed.
Lemma own_alloc_cofinite a (G : gset gname) :
  ✓ a → ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ own γ a.
Proof. intros Ha. eapply (own_alloc_cofinite_dep (λ _, a)); eauto. Qed.
Lemma own_alloc a : ✓ a → ⊢ |==> ∃ γ, own γ a.
Proof. intros Ha. eapply (own_alloc_dep (λ _, a)); eauto. Qed.
-/

instance {a : F.ap (IProp GF)} [CMRA.CoreId a] : BI.Persistent (iOwn γ a) where
  persistent := by
    simp [iOwn]
    refine .trans (UPred.persistently_ownM_core _) ?_
    refine BI.persistently_mono ?_
    refine BI.equiv_iff.mp ?_ |>.mp
    refine OFE.NonExpansive.eqv ?_
    -- Core is element-wise, then use CoreId inst
    sorry

end iOwn
end Iris
