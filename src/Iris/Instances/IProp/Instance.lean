/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Zongyuan Liu
-/

import Iris.BI
import Iris.Algebra
import Iris.Instances.UPred
namespace Iris

-- TODO: Cleanup namespaces and variables for each section

open COFE

/-- Apply an OFunctor at a fixed type -/
abbrev COFE.OFunctorPre.ap (F : OFunctorPre) (T : Type _) [OFE T] :=
  F T T

/-- Apply a list of OFunctors at a fixed type and index -/
abbrev BundledGFunctors.api (FF : BundledGFunctors) (τ : GType) (T : Type _) [OFE T] :=
  FF τ |>.fst |>.ap T

/-- Transport an OFunctorPre application along equality of the OFunctorPre.  -/
def TranspAp {F1 F2 : OFunctorPre} (H : F1 = F2) {T} [OFE T] : F1.ap T = F2.ap T :=
  congrArg (OFunctorPre.ap · T) H

section TranspAp

variable [RF₁ : RFunctorContractive F₁] [RF₂ : RFunctorContractive F₂] [OFE T]

theorem OFE.transpAp_eqv_mp (h_fun : F₁ = F₂) (h_inst : HEq RF₁ RF₂) {x y : F₁.ap T} (H : x ≡{n}≡ y) :
    (TranspAp h_fun).mp x ≡{n}≡ (TranspAp h_fun).mp y := by
  cases h_fun; cases eq_of_heq h_inst; exact H

theorem OFE.transpAp_op_mp (h_fun : F₁ = F₂) (h_inst : HEq RF₁ RF₂) {x y : F₁ T T} :
    (TranspAp h_fun).mp (x • y) ≡ (TranspAp h_fun).mp x • (TranspAp h_fun).mp y := by
  cases h_fun; cases eq_of_heq h_inst; rfl

theorem OFE.transpAp_pcore_mp (h_fun : F₁ = F₂) (h_inst : HEq RF₁ RF₂) {x : F₁ T T} :
    (CMRA.pcore x).map (TranspAp h_fun).mp ≡ CMRA.pcore ((TranspAp h_fun).mp x) := by
  cases h_fun; cases eq_of_heq h_inst
  simp [Equiv, Option.Forall₂]
  cases CMRA.pcore x <;> simp [Equiv.rfl]

theorem OFE.transpAp_validN_mp (h_fun : F₁ = F₂) (h_inst : HEq RF₁ RF₂) {x : F₁ T T} (H : ✓{n} x) :
    ✓{n} ((TranspAp h_fun).mp x) := by
  cases h_fun; cases eq_of_heq h_inst; exact H

theorem OFE.validN_transpAp_mp (h_fun : F₁ = F₂) (h_inst : HEq RF₁ RF₂) {x : F₁ T T}
    (H : ✓{n} ((TranspAp h_fun).mp x)) : ✓{n} x := by
  cases h_fun; cases eq_of_heq h_inst; exact H

end TranspAp

section ElemG

class ElemG (FF : BundledGFunctors) (F : OFunctorPre) [RFunctorContractive F] where
  τ : GType
  transp : FF τ = ⟨F, ‹_›⟩

open OFE

variable [I : RFunctorContractive F]

def ElemG.TranspMap  (E : ElemG GF F) T [OFE T] : (GF E.τ).fst = F :=
  Sigma.mk.inj E.transp |>.1

def ElemG.TranspClass (E : ElemG GF F) T [OFE T] : HEq (GF E.τ).snd I :=
  Sigma.mk.inj E.transp |>.2

def ElemG.Bundle  (E : ElemG GF F) [OFE T] : F.ap T → GF.api E.τ T :=
  TranspAp (E.TranspMap T) |>.mpr

def ElemG.Unbundle  (E : ElemG GF F) [OFE T] : GF.api E.τ T → F.ap T :=
  TranspAp (E.TranspMap T) |>.mp

theorem ElemG.Bundle_Unbundle  (E : ElemG GF F) [OFE T] (x : GF.api E.τ T) :
    E.Bundle (E.Unbundle x) ≡ x := by simp [Bundle, Unbundle, Equiv]

theorem ElemG.Unbundle_Bundle (E : ElemG GF F) [OFE T] (x : F.ap T) :
    E.Unbundle (E.Bundle x) ≡ x := by simp [Bundle, Unbundle, Equiv]

instance ElemG.Bundle.ne {E : ElemG GF F} [OFE T] :
    OFE.NonExpansive (E.Bundle (T := T)) where
  ne {_ _ _} := OFE.transpAp_eqv_mp (E.TranspMap T).symm (E.TranspClass T).symm

instance ElemG.Unbundle.ne {E : ElemG GF F} [OFE T] :
    OFE.NonExpansive (E.Unbundle (T := T)) where
  ne {_ _ _} H := OFE.transpAp_eqv_mp (E.TranspMap T) (E.TranspClass T) H

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

theorem IProp.foldi_unfoldi (x : FF.api τ (IProp FF)) : foldi (unfoldi x) ≡ x := by
  refine .trans (OFunctor.map_comp (F := FF τ |>.fst) ..).symm ?_
  refine .trans ?_ (OFunctor.map_id (F := FF τ |>.fst) x)
  apply OFunctor.map_ne.eqv <;> intro _ <;> simp [IProp.unfold, IProp.fold]

theorem IProp.foldi_op (x y : FF.api τ (IPre FF)) : foldi (x • y) ≡ foldi x • foldi y :=
  RFunctor.map (IProp.unfold FF) (IProp.fold FF) |>.op _ _

theorem IProp.foldi_validN {n : Nat} (x : FF.api τ (IPre FF)) (H : ✓{n} x) : ✓{n} (foldi x) :=
  RFunctor.map (IProp.unfold FF) (IProp.fold FF) |>.validN H

theorem IProp.unfoldi_validN {n : Nat} (x : FF.api τ (IProp FF)) (H : ✓{n} x) : ✓{n} (unfoldi x) :=
  RFunctor.map (IProp.fold FF) (IProp.unfold FF) |>.validN H

theorem IProp.validN_foldi {n : Nat} (x : FF.api τ (IPre FF)) (H : ✓{n} (foldi x)) : ✓{n} x :=
  CMRA.validN_ne (IProp.unfoldi_foldi x).dist (IProp.unfoldi_validN _ H)

theorem IProp.validN_unfoldi {n : Nat} (x : FF.api τ (IProp FF)) (H : ✓{n} (unfoldi x)) : ✓{n} x :=
  CMRA.validN_ne (IProp.foldi_unfoldi x).dist (IProp.foldi_validN _ H)

end Fold

section iSingleton

open IProp OFE UPred

def iSingleton {GF} F [RFunctorContractive F] [E : ElemG GF F] (γ : GName) (v : F.ap (IProp GF)) : IResUR GF :=
  fun τ' => ⟨fun γ' => if H : (τ' = E.τ ∧ γ' = γ) then some (H.1 ▸ (unfoldi (E.Bundle v))) else none⟩

variable {GF F} [RFunctorContractive F] [E : ElemG GF F]

theorem IResUR_op_eval (c1 c2 : IResUR GF) : (c1 • c2) τ' γ' = (c1 τ' γ') • (c2 τ' γ') := by
  simp [CMRA.op, optionOp]

instance : OFE.NonExpansive (iSingleton F γ (GF := GF))  where
  ne {n x1 x2} H τ' γ' := by
    simp [iSingleton]
    split <;> try rfl
    rename_i h; rcases h with ⟨h1, h2⟩; subst h1; subst h2; simp
    exact NonExpansive.ne (NonExpansive.ne H)

theorem iSingleton_op  (x y : F.ap (IProp GF)) : (iSingleton F γ x) • iSingleton F γ y ≡ iSingleton F γ (x • y) := by
  intro τ' γ'
  simp [iSingleton, CMRA.op]
  split <;> simp [optionOp]
  rename_i h; rcases h with ⟨h1, h2⟩; subst h1 h2; simp [unfoldi]
  refine ((RFunctor.map (fold GF) (unfold GF)).op (E.Bundle x) (E.Bundle y)).symm.trans ?_
  refine NonExpansive.eqv (.symm ?_)
  exact transpAp_op_mp (E.TranspMap <| F.ap (IProp GF)).symm (E.TranspClass <| F.ap (IProp GF)).symm

-- Helper lemmas for iSingleton validity and freedom properties

-- iSingleton is free at all keys except γ
theorem iSingleton_free_at_ne (γ : GName) (v : F.ap (IProp GF)) (γ' : GName) (h : γ' ≠ γ) :
    (iSingleton F γ v E.τ).car γ' = none := by
  simp [iSingleton, h]

-- TODO: One use
-- iSingleton at a single key has infinitely many free keys
theorem iSingleton_infinite_free (γ : GName) (v : F.ap (IProp GF)) :
    Infinite (IsFree (iSingleton F γ v E.τ).car) := by
  refine ⟨Poke id γ, ?_, ?_⟩
  · intro n
    simp [IsFree, Poke]
    split
    · rename_i h; exact iSingleton_free_at_ne γ v n (Nat.ne_of_lt h)
    · rename_i h; exact iSingleton_free_at_ne γ v (n + 1) (Nat.ne_of_gt (Nat.lt_succ_of_le (Nat.ge_of_not_lt h)))
  · intro n m; simp [Poke]; split <;> split <;> omega

-- TODO: One use
-- iSingleton at τ' ≠ E.τ is the unit
theorem iSingleton_ne_eq_unit  (γ : GName) (v : F.ap (IProp GF)) (τ' : GType) (h : τ' ≠ E.τ) :
    (iSingleton F γ v τ').car = (UCMRA.unit : GenMap Nat _).car := by
  ext γ'; simp [iSingleton, h]

-- Composing with iSingleton preserves freedom at keys ≠ γ
theorem iSingleton_op_ne_free  (γ : GName) (v : F.ap (IProp GF))
    (m : GenMap GName (GF.api E.τ (IPre GF))) (γ' : GName) (h_ne : γ' ≠ γ) (h_free : m.car γ' = none) :
    ((iSingleton F γ v E.τ) • m).car γ' = none := by
  simp [CMRA.op, optionOp, iSingleton, h_ne, h_free]

-- TODO: Single use
-- Composing with iSingleton preserves infinite free keys
theorem iSingleton_op_isFree_infinite (γ : GName) (v : F.ap (IProp GF))
    (m : GenMap GName (GF.api E.τ (IPre GF))) (h_inf : Infinite (IsFree m.car)) :
    Infinite (IsFree ((iSingleton F γ v E.τ) • m).car) := by
  rcases h_inf with ⟨enum, h_enum_free, h_enum_inj⟩
  by_cases h_gamma_in : ∃ n₀, enum n₀ = γ
  · -- If γ appears in enum, use Poke to skip it
    rcases h_gamma_in with ⟨n₀, h_n₀⟩
    refine ⟨Poke enum n₀, ?_, ?_⟩
    · intro n
      simp [Poke]
      apply iSingleton_op_ne_free
      · split <;> intro H' <;> have _ := h_enum_inj (h_n₀ ▸ H') <;> omega
      · split <;> apply h_enum_free
    · intro n m h_eq; simp [Poke] at h_eq
      split at h_eq <;> split at h_eq
      all_goals have _ := h_enum_inj h_eq; omega
  · -- If γ not in enum, all enumerated keys remain free
    refine ⟨enum, ?_, h_enum_inj⟩
    intro n; simp [IsFree]
    apply iSingleton_op_ne_free
    · intro heq; exact h_gamma_in ⟨n, heq⟩
    · exact h_enum_free

-- TODO: Single use
-- Helper lemma: unfoldi ∘ E.Bundle preserves CoreId
theorem unfoldi_Bundle_coreId {a : F.ap (IProp GF)} [CMRA.CoreId a] :
    CMRA.CoreId (unfoldi (E.Bundle a)) := by
  constructor
  -- Strategy: Use that both Bundle and RFunctor.map preserve pcore
  simp only [unfoldi, OFunctor.map]
  letI : RFunctor (GF E.τ).fst := (GF E.τ).snd.toRFunctor
  have bundle_coreId : CMRA.CoreId (E.Bundle a) := by
    constructor
    calc CMRA.pcore (E.Bundle a)
      ≡ (CMRA.pcore a).map E.Bundle := by
          apply OFE.Equiv.symm
          apply OFE.transpAp_pcore_mp (E.TranspMap (F.ap (IProp GF))).symm (E.TranspClass (F.ap (IProp GF))).symm
      _ ≡ (some a).map E.Bundle := by
        have : CMRA.pcore a ≡ some a := CMRA.CoreId.core_id
        rcases h : CMRA.pcore a with (_ | ca)
        · rw [h] at this; simp [Option.Forall₂] at this
        · rw [h] at this; simp [Option.Forall₂, Option.map] at this ⊢
          exact OFE.NonExpansive.eqv this
      _ ≡ some (E.Bundle a) := by simp [Option.map, Option.Forall₂, OFE.Equiv.rfl]
  calc CMRA.pcore ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f (E.Bundle a))
    ≡ (CMRA.pcore (E.Bundle a)).map (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f :=
      (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).pcore (E.Bundle a) |>.symm
    _ ≡ (some (E.Bundle a)).map (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f := by
      have : CMRA.pcore (E.Bundle a) ≡ some (E.Bundle a) := bundle_coreId.core_id
      rcases h : CMRA.pcore (E.Bundle a) with (_ | c)
      · rw [h] at this; simp [Option.Forall₂] at this
      · rw [h] at this; simp [Option.Forall₂, Option.map] at this ⊢
        exact OFE.NonExpansive.eqv this
    _ ≡ some ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f (E.Bundle a)) := by
      simp [Option.map, Option.Forall₂, OFE.Equiv.rfl]

instance {a : F.ap (IProp GF)} [CMRA.CoreId a] : CMRA.CoreId (iSingleton F γ a) where
  core_id τ' γ' := by
    simp only [iSingleton, CMRA.core, CMRA.pcore, Option.getD, Option.map]
    split
    · rename_i h; cases h.1
      exact unfoldi_Bundle_coreId.core_id
    · rfl

end iSingleton


def iOwn {GF F} [RFunctorContractive F] [E : ElemG GF F] (γ : GName) (v : F.ap (IProp GF)) : IProp GF :=
  UPred.ownM <| iSingleton F γ v

section iOwn

open IProp OFE UPred BI

variable {GF F} [RFunctorContractive F] [E : ElemG GF F]

instance iOwn_ne : NonExpansive (iOwn τ : F.ap (IProp GF) → IProp GF) where
  ne {n x1 x2} H := by unfold iOwn; exact NonExpansive.ne (NonExpansive.ne H)

theorem iOwn_op {a1 a2 : F.ap (IProp GF)} : iOwn γ (a1 • a2) ⊣⊢ iOwn γ a1 ∗ iOwn γ a2 :=
  UPred.ownM_eqv (iSingleton_op _ _).symm |>.trans (UPred.ownM_op _ _)

theorem iOwn_mono {a1 a2 : F.ap (IProp GF)} (H : a2 ≼ a1) : iOwn γ a1 ⊢ iOwn γ a2 := by
  rcases H with ⟨ac, Hac⟩
  rintro n x Hv ⟨clos, Hclos⟩
  -- Basically the heaps proof, want some other lemmas
  refine ⟨iSingleton F γ ac • clos, Hclos.trans <| fun τ' γ' => ?_⟩
  refine .trans ?_ CMRA.op_assocN.symm
  rw [IResUR_op_eval]
  unfold iSingleton
  simp
  split
  · rename_i h; rcases h with ⟨rfl, rfl⟩
    refine Dist.op_l ?_
    have h3 : E.Bundle a1 ≡{n}≡ E.Bundle a2 • E.Bundle ac := by
      refine (NonExpansive.ne Hac.dist).trans ?_
      exact transpAp_op_mp (E.TranspMap (F.ap (IProp GF))).symm (E.TranspClass (F.ap (IProp GF))).symm |>.dist
    refine (NonExpansive.ne h3).trans ?_
    exact (RFunctor.map (fold GF) (unfold GF)).op _ _ |>.dist
  · simp [CMRA.op, optionOp]

theorem iOwn_cmraValid {a : F.ap (IProp GF)} : iOwn γ a ⊢ UPred.cmraValid a := by
  refine (UPred.ownM_valid _).trans ?_
  refine UPred.valid_entails (fun n H => ?_)
  rcases H E.τ with ⟨h_valid, _⟩
  apply validN_transpAp_mp (E.TranspMap (F.ap (IProp GF))).symm (E.TranspClass (F.ap (IProp GF))).symm
  apply validN_unfoldi
  have h_at_γ := h_valid γ
  simp [iSingleton] at h_at_γ; trivial

theorem iOwn_cmraValid_op {a1 a2 : F.ap (IProp GF)} : iOwn γ a1 ∗ iOwn γ a2 ⊢ UPred.cmraValid (a1 • a2) :=
  iOwn_op.mpr.trans iOwn_cmraValid

theorem iOwn_valid_r {a : F.ap (IProp GF)} : iOwn γ a ⊢ iOwn γ a ∗ UPred.cmraValid a :=
  BI.persistent_entails_l iOwn_cmraValid

theorem iOwn_valid_l {a : F.ap (IProp GF)} : iOwn γ a ⊢ UPred.cmraValid a ∗ iOwn γ a :=
  BI.persistent_entails_r iOwn_cmraValid

instance {a : F.ap (IProp GF)} [CMRA.CoreId a] : BI.Persistent (iOwn γ a) where
  persistent := by
    simp [iOwn]
    refine (UPred.persistently_ownM_core _).trans ?_
    refine persistently_mono ?_
    refine equiv_iff.mp ?_ |>.mp
    refine NonExpansive.eqv ?_
    apply CMRA.core_eqv_self

theorem iOwn_alloc_strong_dep {f : GName → F.ap (IProp GF)} {P : GName → Prop}
    (HI : Infinite P) (Hv : ∀ γ, P γ → ✓ (f γ)) :
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ iOwn γ (f γ) := by
  sorry
/-
theorem iOwn_alloc_strong_dep {f : GName → F.ap (IProp GF)} {P : GName → Prop}
    (HI : Infinite P) (Hv : ∀ γ, P γ → ✓ (f γ)) :
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ iOwn γ (f γ) := by
  refine .trans (Q := iprop(|==> ∃ m : IResUR GF, ⌜∃ γ, P γ ∧ m = iSingleton _ γ (f γ)⌝ ∧ UPred.ownM m)) ?_ ?_
  · refine .trans (UPred.ownM_unit _) <| BI.intuitionistically_elim.trans ?_
    refine UPred.ownM_updateP _ (fun n mz Hvalid => ?_)
    -- Key insight: pick γ based on the frame mz
    -- For each frame, we need γ ∈ P such that γ is free in that frame
    cases mz with
    | none =>
      -- No frame: any element from P works
      rcases HI with ⟨PE, HPE⟩
      refine ⟨iSingleton F (PE 0) (f (PE 0)), ⟨_, HPE.inc, rfl⟩, ?_⟩
      -- Validity is trivial for empty frame
      intro γ; constructor
      · intro γ'
        simp [CMRA.ValidN, optionValidN, CMRA.op?, iSingleton]
        rcases Classical.em (γ = ElemG.τ GF F ∧ γ' = PE 0) with (⟨h1, h2⟩ | h)
        · subst h1 h2
          simp [iSingleton]
          have hvn : ✓{n} (f (PE 0)) := (Hv (PE 0) HPE.inc).validN
          have hb : ✓{n} (E.Bundle (f (PE 0))) := ElemG.Bundle_validN E (f (PE 0)) hvn
          exact IProp.unfoldi_validN (E.Bundle (f (PE 0))) hb
        · simp_all only [↓reduceDIte]
      · -- IsFree: show that after allocating at PE 0, infinitely many remain free
        -- Use Poke to shift the enumeration, skipping PE 0
        refine ⟨Poke PE 0, ?_, ?_⟩
        · intro n'
          -- After allocation at PE 0, Poke PE 0 enumerates the remaining free positions
          simp [IsFree, iSingleton, CMRA.op?]
          intro h hcontra
          -- Poke PE 0 n' = PE (n' + 1) ≠ PE 0 by injectivity
          simp only [Poke] at hcontra
          split at hcontra
          · next hn => have := HPE.inj hcontra; omega
          · next hn => have := HPE.inj hcontra; omega
        · intro n' m' h
          -- Poke is injective when the base enumeration is injective
          simp only [Poke] at h
          by_cases hn : n' < 0 <;> by_cases hm : m' < 0
          · rw [if_pos hn, if_pos hm] at h; exact HPE.inj h
          · rw [if_pos hn, if_neg hm] at h; have := HPE.inj h; omega
          · rw [if_neg hn, if_pos hm] at h; have := HPE.inj h; omega
          · rw [if_neg hn, if_neg hm] at h; have := HPE.inj h; omega
    | some z =>
      -- Have frame z: pick γ ∈ P that's free in z
      -- Use Infinite.inter_nonempty_nat to find such a γ
      have Hvalid_z : ✓{n} ((UCMRA.unit : IResUR GF) • z) := by
        simp [CMRA.op?] at Hvalid; exact Hvalid
      have Hinf_free : Infinite (IsFree (z E.τ).car) := by
        -- Extract the infinity condition from validity of the GenMap at type E.τ
        have h := Hvalid_z E.τ
        -- The validity of a GenMap includes Infinite (IsFree ...)
        rcases h with ⟨_, Hinf⟩
        -- Now show (unit • z) E.τ has the same IsFree as z E.τ
        refine Infinite.mono Hinf (fun a => ?_)
        simp [IsFree, CMRA.op]
        have : ((UCMRA.unit : IResUR GF) E.τ).car a = none := by simp [UCMRA.unit]
        simp [this, optionOp]
      have h_inter : ∃ n, P n ∧ IsFree (z E.τ).car n := by
        -- FIXME: unprovable
        sorry
      rcases h_inter with ⟨γ_fresh, Hγ_P, Hγ_free⟩
      refine ⟨iSingleton F γ_fresh (f γ_fresh), ⟨γ_fresh, Hγ_P, rfl⟩, ?_⟩
      -- Now prove validity with γ_fresh which is free in the frame
      intro γ; constructor
      · intro γ'
        simp [CMRA.ValidN, optionValidN, CMRA.op?, iSingleton]
        rcases Classical.em (γ = ElemG.τ GF F ∧ γ' = γ_fresh) with (⟨h1, h2⟩ | h)
        · -- At the allocated position: γ = E.τ and γ' = γ_fresh
          subst h1 h2
          -- After subst, γ_fresh becomes γ'
          simp [iSingleton, CMRA.op, optionOp]
          -- γ' is free in z, so z E.τ γ' = none
          simp [IsFree] at Hγ_free
          rw [Hγ_free]
          simp [optionOp]
          -- Now show validity of unfoldi (E.Bundle (f γ'))
          have hvn : ✓{n} (f γ') := (Hv γ' Hγ_P).validN
          have hb : ✓{n} (E.Bundle (f γ')) := ElemG.Bundle_validN E (f γ') hvn
          exact IProp.unfoldi_validN (E.Bundle (f γ')) hb
        · -- Away from allocated position: use validity of z
          -- Since h : ¬(γ = E.τ ∧ γ' = γ_fresh), iSingleton at (γ, γ') is none
          have h_if_false : ¬(γ = ElemG.τ GF F ∧ γ' = γ_fresh) := h
          simp [CMRA.op, iSingleton]
          rw [dif_neg h_if_false]
          simp [optionOp]
          -- Now just the validity from z
          -- Note: (unit • z) γ = z γ since unit is left identity
          have h_unit_z : (((UCMRA.unit : IResUR GF) • z) γ).car = (z γ).car := by
            simp [CMRA.op, UCMRA.unit, optionOp]
          have := Hvalid_z γ
          rcases this with ⟨Hv_z, _⟩
          simp [CMRA.ValidN] at Hv_z
          rw [h_unit_z] at Hv_z
          exact Hv_z γ'
      · -- IsFree: show infinitely many remain free after allocation
        rcases Classical.em (γ = ElemG.τ GF F) with (h_eq | h_ne)
        · -- Case: γ = E.τ, use alter_isFree_infinite
          subst h_eq
          simp [CMRA.op?, CMRA.op, iSingleton]
          -- The goal is: Infinite (IsFree (fun x => optionOp (if x = γ_fresh then ... else none) ((z E.τ).car x)))
          -- We know γ_fresh is free in (z E.τ).car, i.e., (z E.τ).car γ_fresh = none
          simp [IsFree] at Hγ_free
          -- Now show this matches alter pattern
          suffices h : (fun x => optionOp (if x = γ_fresh then some (unfoldi (E.Bundle (f γ_fresh))) else none) ((z (ElemG.τ GF F)).car x)) =
                       alter (z (ElemG.τ GF F)).car γ_fresh (some (unfoldi (E.Bundle (f γ_fresh)))) by
            rw [h]; exact alter_isFree_infinite Hinf_free
          funext x
          simp only [alter, optionOp]
          by_cases h : x = γ_fresh
          · subst h
            rw [if_pos rfl, if_pos rfl]
            rw [Hγ_free]
          · rw [if_neg h, if_neg (Ne.symm h)]
            cases (z (ElemG.τ GF F)).car x <;> rfl
        · -- Case: γ ≠ E.τ, iSingleton doesn't affect this type
          simp [CMRA.op?, CMRA.op, iSingleton]
          -- The dif_neg applies because γ ≠ E.τ
          have : ∀ x, ¬(γ = ElemG.τ GF F ∧ x = γ_fresh) := fun x ⟨h1, _⟩ => h_ne h1
          simp [this]
          -- Now (z γ).car still has infinite free elements
          have := Hvalid_z γ
          exact this.2
  · refine BIUpdate.mono ?_
    refine BI.exists_elim (fun m => ?_)
    refine BI.pure_elim (φ := ∃ γ, P γ ∧ m = iSingleton F γ (f γ)) BI.and_elim_l ?_
    refine fun ⟨γ, HP, Hm⟩ => BI.and_elim_r' ?_
    refine BI.exists_intro' γ ?_
    refine BI.emp_sep.mpr.trans (BI.sep_mono ?_ ?_)
    · exact BI.pure_intro HP
    · rw [Hm]; exact .rfl
-/

theorem iOwn_alloc_dep (f : GName → F.ap (IProp GF)) (Ha : ∀ γ, ✓ (f γ)) :
    ⊢ |==> ∃ γ, iOwn γ (f γ) :=
  (iOwn_alloc_strong_dep .Nat_True (fun _ => Ha ·)).trans <|
  BIUpdate.mono <| BI.exists_mono fun _ => BI.sep_elim_r

theorem iOwn_alloc (a : F.ap (IProp GF)) : ✓ a → ⊢ |==> ∃ γ, iOwn γ a :=
  fun Ha => iOwn_alloc_dep _ (fun _ => Ha)

--  MARKUSDE: Here

theorem iOwn_updateP {P γ a} (Hupd : a ~~>: P) : iOwn γ a ⊢ |==> ∃ a' : F.ap (IProp GF), ⌜P a'⌝ ∗ iOwn γ a' := by
  refine .trans (Q := iprop(|==> ∃ m, ⌜ ∃ a', m = (iSingleton F γ a') ∧ P a' ⌝ ∧ UPred.ownM m)) ?_ ?_
  · apply UPred.ownM_updateP
    intro n mz Hv
    cases mz with
    | none =>
      have h_a_valid : ✓{n} a := by
        refine CMRA.validN_ne (ElemG.Unbundle_Bundle E a).dist ?_
        refine transpAp_validN_mp (E.TranspMap <| F.ap (IProp GF)) (E.TranspClass <| F.ap (IProp GF)) ?_
        refine CMRA.validN_ne (foldi_unfoldi (E.Bundle a)).dist ?_
        refine foldi_validN (unfoldi (E.Bundle a)) ?_
        have h_at_gamma : ✓{n} (((iSingleton F γ a) E.τ).car γ) := (Hv E.τ).1 γ
        simp [iSingleton] at h_at_gamma
        exact h_at_gamma
      obtain ⟨a', Ha'_P, Ha'_valid⟩ := Hupd n none (by simp [CMRA.op?]; exact h_a_valid)
      refine ⟨iSingleton F γ a', ⟨a', rfl, Ha'_P⟩, fun τ' => ?_⟩
      simp [CMRA.op?]
      by_cases h_tau : τ' = E.τ
      · subst h_tau
        refine ⟨fun γ' => ?_, ?_⟩
        · simp [iSingleton]
          by_cases h_gamma : γ' = γ <;> simp [h_gamma, CMRA.ValidN, optionValidN]
          refine unfoldi_validN (E.Bundle a') ?_
          apply transpAp_validN_mp (E.TranspMap <| F.ap (IProp GF)).symm (E.TranspClass <| F.ap (IProp GF)).symm
          exact Ha'_valid
        · refine ⟨Poke id γ, ?_, ?_⟩
          · intro _; simp [IsFree, iSingleton, Poke]; split <;> omega
          · intro _ _; simp [Poke]; split <;> split <;> omega
      · simp [iSingleton, h_tau]
        apply UCMRA.unit_valid.validN

    | some mz' =>
      -- With frame case
      cases h_mz_gamma : (mz' E.τ).car γ with
      | none =>
        have h_a_valid : ✓{n} a := by
          apply CMRA.validN_ne (ElemG.Unbundle_Bundle E a).dist
          apply transpAp_validN_mp (E.TranspMap <| F.ap (IProp GF)) (E.TranspClass <| F.ap (IProp GF))
          refine CMRA.validN_ne (foldi_unfoldi (E.Bundle a)).dist ?_
          refine foldi_validN (unfoldi (E.Bundle a)) ?_
          have h_at_gamma : ✓{n} ((((iSingleton F γ a) • mz') E.τ).car γ) := (Hv E.τ).1 γ
          simp [iSingleton, CMRA.op, h_mz_gamma] at h_at_gamma
          exact h_at_gamma
        obtain ⟨a', Ha'_P, Ha'_valid⟩ := Hupd n none (by simp [CMRA.op?]; exact h_a_valid)
        refine ⟨iSingleton F γ a', ⟨a', rfl, Ha'_P⟩, ?_⟩
        simp [CMRA.op?]
        intro τ'
        by_cases h_tau : τ' = E.τ
        · subst h_tau
          refine ⟨?_, ?_⟩
          · intro γ'
            simp [CMRA.op]
            by_cases h_gamma : γ' = γ
            · simp [h_gamma, iSingleton, h_mz_gamma]
              refine IProp.unfoldi_validN (E.Bundle a') ?_
              apply OFE.transpAp_validN_mp (E.TranspMap <| F.ap (IProp GF)).symm (E.TranspClass <| F.ap (IProp GF)).symm
              exact Ha'_valid
            · simp [h_gamma, iSingleton, optionOp]
              have h := (Hv E.τ).1 γ'
              simp [CMRA.op, iSingleton, h_gamma, optionOp, CMRA.op?] at h
              exact h
          · have h_frame_inf := Hv E.τ
            simp [CMRA.op?] at h_frame_inf
            rcases h_frame_inf with ⟨_, h_inf⟩
            apply Infinite.mono h_inf (fun k h_free => ?_)
            simp [IsFree, CMRA.op, iSingleton, optionOp] at h_free ⊢
            by_cases h_k : k = γ <;> simp_all [h_k, h_mz_gamma, optionOp]
        · have h_frame_valid := Hv τ'
          simp [CMRA.op?, CMRA.op, iSingleton, h_tau] at h_frame_valid ⊢
          exact h_frame_valid
      | some v =>
        have h_a_valid : ✓{n} (a • E.Unbundle (IProp.foldi v)) := by
          have h_valid_at_tau : ✓{n} ((iSingleton F γ a •? some mz') E.τ) := Hv E.τ
          simp [CMRA.op?] at h_valid_at_tau
          rcases h_valid_at_tau with ⟨h_pointwise, _⟩
          have h_at_gamma : ✓{n} ((((iSingleton F γ a) • mz') E.τ).car γ) := h_pointwise γ
          simp [iSingleton, CMRA.op, h_mz_gamma]  at h_at_gamma
          have h_foldi_hom := (RFunctor.map (IProp.unfold GF) (IProp.fold GF)).op
              ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f (E.Bundle a)) v
          have h_comp : (RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f
              ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f (E.Bundle a)) ≡ E.Bundle a := by
            refine .trans (OFunctor.map_comp (F := GF E.τ |>.fst) ..).symm ?_
            refine .trans ?_ (OFunctor.map_id (F := GF E.τ |>.fst) (E.Bundle a))
            apply OFunctor.map_ne.eqv <;> intro _ <;> simp [IProp.unfold, IProp.fold]
          apply CMRA.validN_ne (ElemG.Unbundle_Bundle E a).op_l.dist
          apply CMRA.validN_ne (OFE.transpAp_op_mp (E.TranspMap ((GF (ElemG.τ GF F)).fst.ap (IPre GF))) (E.TranspClass ((GF (ElemG.τ GF F)).fst.ap (IPre GF)))).dist
          apply OFE.transpAp_validN_mp (E.TranspMap (F.ap (IProp GF))) (E.TranspClass (F.ap (IProp GF)))
          apply CMRA.validN_ne (h_comp.op_l).dist
          apply CMRA.validN_ne h_foldi_hom.dist
          apply IProp.foldi_validN _ h_at_gamma
        obtain ⟨a', Ha'_P, Ha'_valid⟩ := Hupd n (some (E.Unbundle (IProp.foldi v))) (by simp [CMRA.op?]; exact h_a_valid)
        refine ⟨iSingleton F γ a', ⟨a', rfl, Ha'_P⟩, ?_⟩
        simp [CMRA.op?]
        intro τ'
        by_cases h_tau : τ' = E.τ
        · subst h_tau
          refine ⟨?_, ?_⟩
          · intro γ'
            simp [CMRA.op]
            by_cases h_gamma : γ' = γ
            · simp [h_gamma, iSingleton, optionOp, h_mz_gamma, CMRA.ValidN, optionValidN]
              simp [CMRA.op?] at Ha'_valid
              have h_bundle_foldi_v : ✓{n} (E.Bundle a' • foldi v) := by
                apply CMRA.validN_ne (ElemG.Bundle_Unbundle E (foldi v)).op_r.dist
                apply CMRA.validN_ne (OFE.transpAp_op_mp (E.TranspMap (F.ap (IProp GF))).symm (E.TranspClass (F.ap (IProp GF))).symm |>.dist)
                apply OFE.transpAp_validN_mp (E.TranspMap (F.ap (IProp GF))).symm (E.TranspClass (F.ap (IProp GF))).symm
                apply Ha'_valid
              simp [IProp.unfoldi, IProp.foldi] at h_bundle_foldi_v ⊢
              have h_unfoldi_op := (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).op (E.Bundle a') ((RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f v)
              have h_after_unfoldi : ✓{n} ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f (E.Bundle a') •
                  (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f ((RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f v)) := by
                apply CMRA.validN_ne h_unfoldi_op.dist
                exact IProp.unfoldi_validN _ h_bundle_foldi_v
              have h_unfoldi_foldi := IProp.unfoldi_foldi v
              apply CMRA.validN_ne (h_unfoldi_foldi.op_r).dist
              exact h_after_unfoldi
            · simp [h_gamma, iSingleton, optionOp]
              have h_frame_valid := Hv E.τ
              simp [CMRA.op?] at h_frame_valid
              rcases h_frame_valid with ⟨h_pointwise, _⟩
              have h_at_gamma' := h_pointwise γ'
              simp [CMRA.op, iSingleton, h_gamma, optionOp] at h_at_gamma'
              exact h_at_gamma'
          · have h_frame_inf := Hv E.τ
            simp [CMRA.op?] at h_frame_inf
            rcases h_frame_inf with ⟨_, h_inf⟩
            apply Infinite.mono h_inf
            intro k h_free
            simp [IsFree, CMRA.op, iSingleton, optionOp] at h_free ⊢
            by_cases h_k : k = γ <;> simp_all [h_k, h_mz_gamma, optionOp, h_free]
        · have h_frame_valid := Hv τ'
          simp [CMRA.op?, CMRA.op, iSingleton, h_tau] at h_frame_valid ⊢
          exact h_frame_valid
  · refine BIUpdate.mono (BI.exists_elim (fun m => BI.pure_elim_l (fun ⟨a', Hm, HP⟩ => ?_)))
    subst Hm
    exact BI.exists_intro' a' (BI.persistent_entails_r (BI.pure_intro HP))

theorem iOwn_update {γ} {a a' : F.ap (IProp GF)} (Hupd : a ~~> a') : iOwn γ a ⊢ |==> iOwn γ a' := by
  refine .trans (iOwn_updateP <| UpdateP.of_update Hupd) ?_
  refine BIUpdate.mono ?_
  refine BI.exists_elim (fun m => ?_)
  refine BI.pure_elim (a' = m) BI.sep_elim_l ?_
  rintro rfl
  exact BI.sep_elim_r

-- Helper lemmas for iOwn_unit

-- Bundle preserves unit structure
theorem ElemG.Bundle_unit {GF F} [RFunctorContractive F] (E : ElemG GF F)
    {ε : F.ap (IProp GF)} [IsUnit ε] :
    IsUnit (E.Bundle ε) := by
  refine { unit_valid := ?_, unit_left_id := ?_, pcore_unit := ?_ }
  · -- Validity: use Bundle_validN
    refine CMRA.valid_iff_validN.mpr fun n => ?_
    apply transpAp_validN_mp (E.TranspMap <| F.ap (IProp GF)).symm (E.TranspClass <| F.ap (IProp GF)).symm
    apply IsUnit.unit_valid.validN
  · -- Left identity: Strategy: apply Unbundle to both sides, use that ε is unit, then Bundle back
    intro x
    have h1 : E.Unbundle (E.Bundle ε • x) ≡ E.Unbundle x := by
      calc E.Unbundle (E.Bundle ε • x)
        _ ≡ E.Unbundle (E.Bundle ε) • E.Unbundle x := by
          apply transpAp_op_mp (E.TranspMap <| F.ap (IProp GF)) (E.TranspClass <| F.ap (IProp GF))
        _ ≡ ε • E.Unbundle x := (ElemG.Unbundle_Bundle E ε).op_l
        _ ≡ E.Unbundle x := IsUnit.unit_left_id
    calc E.Bundle ε • x
      ≡ E.Bundle (E.Unbundle (E.Bundle ε • x)) := (ElemG.Bundle_Unbundle E _).symm
      _ ≡ E.Bundle (E.Unbundle x) := OFE.NonExpansive.eqv h1
      _ ≡ x := ElemG.Bundle_Unbundle E x
  · -- Pcore
    calc CMRA.pcore (E.Bundle ε)
      ≡ (CMRA.pcore ε).map E.Bundle := by
            symm
            apply transpAp_pcore_mp (E.TranspMap <| F.ap (IProp GF)).symm (E.TranspClass <| F.ap (IProp GF)).symm
      _ ≡ Option.map E.Bundle (some ε) := by
         rename_i unit
         have := unit.pcore_unit
         rcases eqn: CMRA.pcore ε
         · rw [eqn] at this; simp [Option.Forall₂] at this
         · rw [eqn] at this; simp [Option.Forall₂, Option.map] at this ⊢
           exact NonExpansive.eqv this
      _ ≡ E.Bundle ε := by rfl

-- unfoldi preserves unit structure
theorem IProp.unfoldi_unit {τ : GType} {x : GF.api τ (IProp GF)} [IsUnit x] :
IsUnit (unfoldi x) := by
  refine { unit_valid := ?_, unit_left_id := ?_, pcore_unit := ?_ }
  · -- Validity
    refine CMRA.valid_iff_validN.mpr fun n => IProp.unfoldi_validN x IsUnit.unit_valid.validN
  · -- Left identity: unfoldi x • y ≡ y
    intro y
    have h : foldi (unfoldi x • y) ≡ foldi y := by
      calc foldi (unfoldi x • y)
        _ ≡ foldi (unfoldi x) • foldi y := foldi_op _ _
        _ ≡ x • foldi y := (foldi_unfoldi x).op_l
        _ ≡ foldi y := IsUnit.unit_left_id
    calc unfoldi x • y
      _ ≡ unfoldi (foldi (unfoldi x • y)) := (IProp.unfoldi_foldi _).symm
      _ ≡ unfoldi (foldi y) := OFE.NonExpansive.eqv h
      _ ≡ y := IProp.unfoldi_foldi y
  · -- pcore_unit
    simp only [unfoldi, OFunctor.map]
    letI : RFunctor (GF τ).fst := (GF τ).snd.toRFunctor
    calc CMRA.pcore ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f x)
      _ ≡ (CMRA.pcore x).map (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f :=
        (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).pcore x |>.symm
      _ ≡ (some x).map (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f :=
        Option.map_forall₂ _ IsUnit.pcore_unit
      _ ≡ some ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f x) := by
        simp [Option.map, Option.Forall₂, OFE.Equiv.rfl]

theorem unit_op_eq {GF : BundledGFunctors} (τ : GType) (m : GenMap GName (GF.api τ (IPre GF))) :
    ((UCMRA.unit : IResUR GF) τ) • m ≡ m := by
  simp [OFE.Equiv, CMRA.op, UCMRA.unit, optionOp, Option.Forall₂]
  intro k; cases m.car k <;> simp [OFE.Equiv.rfl]

theorem unfoldi_bundle_unit {GF F} [RFunctorContractive F] (E : ElemG GF F)
    {ε : F.ap (IProp GF)} [IsUnit ε] : IsUnit (IProp.unfoldi (E.Bundle ε)) :=
  haveI : IsUnit (E.Bundle ε) := ElemG.Bundle_unit E
  IProp.unfoldi_unit

-- Helper: validity of unfoldi (Bundle ε) at level n
theorem unfoldi_bundle_validN {GF F} [RFunctorContractive F] (E : ElemG GF F)
    {ε : F.ap (IProp GF)} [IsUnit ε] (n : Nat) : ✓{n} (IProp.unfoldi (E.Bundle ε)) := by
  simp [IProp.unfoldi]
  refine (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).validN ?_
  apply OFE.transpAp_validN_mp (E.TranspMap <| F.ap (IProp GF)).symm (E.TranspClass <| F.ap (IProp GF)).symm
  apply IsUnit.unit_valid.validN

-- Helper: extract validity of element at key from unit-composed frame
theorem extract_frame_validN {GF : BundledGFunctors} (τ : GType) (n : Nat)
    (mz' : IResUR GF)
    (h_valid : ✓{n} ((UCMRA.unit : IResUR GF) τ • mz' τ).car)
    (γ : GName) (v : GF.api τ (IPre GF)) (h_at : (mz' τ).car γ = some v) :
    ✓{n} v := by
  have := h_valid γ
  simp [CMRA.op, UCMRA.unit, optionOp, CMRA.ValidN, optionValidN, h_at] at this
  exact this

theorem iOwn_unit {γ} {ε : F.ap (IProp GF)} [Hε : IsUnit ε] : ⊢ |==> iOwn γ ε := by
  unfold iOwn
  refine .trans (UPred.ownM_unit _) ?_
  refine BI.intuitionistically_elim.trans ?_
  have Hupd : (UCMRA.unit : IResUR GF) ~~>: (iSingleton F γ ε = ·) := by
    intro n mz Hv
    refine ⟨iSingleton F γ ε, rfl, ?_⟩
    -- Show ✓{n} (iSingleton F γ ε •? mz)
    intro τ'
    by_cases Heq : τ' = E.τ
    ·
      subst Heq
      refine ⟨?_, ?_⟩
      ·
        intro γ'
        unfold iSingleton
        simp [CMRA.op?, CMRA.ValidN, optionValidN]
        cases mz with
        | none =>
          simp [CMRA.op, optionOp]
          by_cases h_key : γ' = γ
          · simp [h_key]; exact unfoldi_bundle_validN E n
          · simp [h_key]
        | some mz' =>
          simp [CMRA.op, optionOp]
          have Hv' := Hv E.τ
          simp [CMRA.op?] at Hv'
          rcases Hv' with ⟨h_valid, _⟩
          by_cases h_key : γ' = γ
          ·
            simp [h_key]
            rcases h_at : (mz' E.τ).car γ with (⟨⟩ | v)
            · simp [optionOp]; exact unfoldi_bundle_validN E n
            · simp [optionOp]
              haveI h_unit : IsUnit (IProp.unfoldi (E.Bundle ε)) := unfoldi_bundle_unit E
              have h_v_valid := extract_frame_validN E.τ n mz' h_valid γ v h_at
              exact CMRA.validN_ne h_unit.unit_left_id.dist.symm h_v_valid
          ·
            simp [h_key]
            rcases h_at : (mz' E.τ).car γ' with (⟨⟩ | v)
            · trivial
            · simp [optionOp]; exact extract_frame_validN E.τ n mz' h_valid γ' v h_at
      ·
        cases mz with
        | none => exact iSingleton_infinite_free γ ε
        | some mz' =>
          have ⟨_, h_inf⟩ := Hv E.τ; simp [CMRA.op?] at h_inf
          have h_inf_mz : Infinite (IsFree (mz' E.τ).car) := by
            apply Infinite.mono h_inf
            intro k h_free; simp [IsFree, CMRA.op, UCMRA.unit, optionOp] at h_free ⊢; exact h_free
          exact iSingleton_op_isFree_infinite γ ε (mz' E.τ) h_inf_mz
    ·
      have h_is_unit := iSingleton_ne_eq_unit γ ε τ' Heq
      cases mz with
      | none =>
        simp [CMRA.op?, CMRA.op, h_is_unit]
        show ✓{n} (⟨fun γ' => if _ : τ' = E.τ ∧ γ' = γ then _ else none⟩ : GenMap Nat _)
        simp [Heq]
        exact (UCMRA.unit_valid : ✓ (UCMRA.unit : GenMap Nat ((GF τ').fst (IPre GF) (IPre GF)))).validN
      | some mz' =>
        have Hv' := Hv τ'; simp [CMRA.op?] at Hv'
        have h_eq : ((UCMRA.unit : IResUR GF) • mz') τ' ≡ (iSingleton F γ ε •? some mz') τ' := by
          simp only [CMRA.op?, CMRA.op, h_is_unit, OFE.Equiv]
          intro k
          simp [UCMRA.unit, optionOp, Option.Forall₂]
          cases (mz' τ').car k <;> simp [OFE.Equiv.rfl]
        exact CMRA.validN_ne h_eq.dist Hv'

  refine .trans (UPred.ownM_updateP _ Hupd) ?_
  refine BIUpdate.mono ?_
  refine BI.exists_elim (fun y => ?_)
  refine BI.pure_elim (iSingleton F γ ε = y) BI.and_elim_l ?_
  rintro rfl
  exact BI.and_elim_r



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



end iOwn
end Iris
