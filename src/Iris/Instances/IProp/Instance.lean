/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Zongyuan Liu
-/

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

/-- Transport an OFunctorPre application along equality of the OFunctorPre.  -/
def TranspAp {F1 F2 : OFunctorPre} (H : F1 = F2) {T} [OFE T] :
    F1.ap T = F2.ap T := congrArg (OFunctorPre.ap · T) H

section TranspAp

variable [RF₁ : RFunctorContractive F₁] [RF₂ : RFunctorContractive F₂] [OFE T]

theorem OFE.transpAp_eqv_mp (h_fun : F₁ = F₂) (h_inst : HEq RF₁ RF₂) {x y : F₁.ap T} (H : x ≡{n}≡ y) :
    (TranspAp h_fun).mp x ≡{n}≡ (TranspAp h_fun).mp y := by
  cases h_fun; cases eq_of_heq h_inst; exact H

theorem OFE.transpAp_eqv_mpr (h_fun : F₁ = F₂) (h_inst : HEq RF₁ RF₂) {x y : F₂.ap T} (H : x ≡{n}≡ y) :
    (TranspAp h_fun).mpr x ≡{n}≡ (TranspAp h_fun).mpr y := by
  cases h_fun; cases eq_of_heq h_inst; exact H

theorem OFE.transpAp_op_mp (h_fun : F₁ = F₂) (h_inst : HEq RF₁ RF₂) {x y : F₁ T T} :
    (TranspAp h_fun).mp (x • y) ≡ (TranspAp h_fun).mp x • (TranspAp h_fun).mp y := by
  cases h_fun; cases eq_of_heq h_inst; rfl

theorem OFE.transpAp_op_mpr (h_fun : F₁ = F₂) (h_inst : HEq RF₁ RF₂) {x y : F₂ T T} :
    (TranspAp h_fun).mpr (x • y) ≡ (TranspAp h_fun).mpr x • (TranspAp h_fun).mpr y := by
  cases h_fun; cases eq_of_heq h_inst; rfl

theorem OFE.transpAp_pcore_mpr (h_fun : F₁ = F₂) (h_inst : HEq RF₁ RF₂) {x : F₂ T T} :
    (CMRA.pcore x).map (TranspAp h_fun).mpr ≡ CMRA.pcore ((TranspAp h_fun).mpr x) := by
  cases h_fun; cases eq_of_heq h_inst
  simp [Equiv, Option.Forall₂]
  cases CMRA.pcore x <;> simp [Equiv.rfl]

theorem OFE.transpAp_validN_mp (h_fun : F₁ = F₂) (h_inst : HEq RF₁ RF₂) {x : F₁ T T} (H : ✓{n} x) :
    ✓{n} ((TranspAp h_fun).mp x) := by
  cases h_fun; cases eq_of_heq h_inst; exact H

theorem OFE.transpAp_validN_mpr (h_fun : F₁ = F₂) (h_inst : HEq RF₁ RF₂) {x : F₂ T T} (H : ✓{n} x) :
    ✓{n} ((TranspAp h_fun).mpr x) := by
  cases h_fun; cases eq_of_heq h_inst; exact H

end TranspAp

section ElemG

open OFE

class ElemG (FF : BundledGFunctors) (F : OFunctorPre) [RFunctorContractive F] where
  τ : GType
  transp : FF τ = ⟨F, ‹_›⟩

def ElemG.TranspMap {GF F} [RFunctorContractive F] (E : ElemG GF F) T [OFE T] : (GF E.τ).fst = F :=
  Sigma.mk.inj E.transp |>.1

def ElemG.TranspClass {GF F} [I : RFunctorContractive F] (E : ElemG GF F) T [OFE T] : HEq (GF E.τ).snd I :=
  Sigma.mk.inj E.transp |>.2

def ElemG.Bundle {GF F} [RFunctorContractive F] (E : ElemG GF F) [OFE T] : F.ap T → GF.api E.τ T :=
  TranspAp (E.TranspMap T) |>.mpr

def ElemG.Unbundle {GF F} [RFunctorContractive F] (E : ElemG GF F) [OFE T] : GF.api E.τ T → F.ap T :=
  TranspAp (E.TranspMap T) |>.mp

theorem ElemG.Bundle_Unbundle {GF F} [RFunctorContractive F] (E : ElemG GF F) [OFE T] (x : GF.api E.τ T) :
    E.Bundle (E.Unbundle x) ≡ x := by simp [Bundle, Unbundle, Equiv]

theorem ElemG.Unbundle_Bundle {GF F} [RFunctorContractive F] (E : ElemG GF F) [OFE T] (x : F.ap T) :
    E.Unbundle (E.Bundle x) ≡ x := by simp [Bundle, Unbundle, Equiv]

instance ElemG.Bundle.ne {GF F} [RFunctorContractive F] {E : ElemG GF F} [OFE T] :
    OFE.NonExpansive (E.Bundle (T := T)) where
  ne {_ _ _} := OFE.transpAp_eqv_mpr (E.TranspMap T) (E.TranspClass T)

instance ElemG.Unbundle.ne {GF F} [RFunctorContractive F] {E : ElemG GF F} [OFE T] :
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

theorem IProp.foldi_op (x y : FF.api τ (IPre FF)) : foldi (x • y) ≡ foldi x • foldi y := by
  letI : RFunctor (FF τ).fst := (FF τ).snd.toRFunctor
  exact (RFunctor.map (IProp.unfold FF) (IProp.fold FF)).op _ _

theorem IProp.foldi_validN {n : Nat} (x : FF.api τ (IPre FF)) (H : ✓{n} x) : ✓{n} (foldi x) := by
  letI : RFunctor (FF τ).fst := (FF τ).snd.toRFunctor
  exact (RFunctor.map (IProp.unfold FF) (IProp.fold FF)).validN H

theorem IProp.unfoldi_validN {n : Nat} (x : FF.api τ (IProp FF)) (H : ✓{n} x) : ✓{n} (unfoldi x) := by
  letI : RFunctor (FF τ).fst := (FF τ).snd.toRFunctor
  exact (RFunctor.map (IProp.fold FF) (IProp.unfold FF)).validN H

theorem Option.map_forall₂ {α β : Type _} [OFE α] [OFE β] (f : α → β) [hf : OFE.NonExpansive f]
    {o1 o2 : Option α} (h : o1 ≡ o2) : o1.map f ≡ o2.map f := by
  cases o1 <;> cases o2 <;> simp_all [Option.Forall₂]
  exact hf.eqv h

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
  split <;> try rfl
  simp [optionOp]
  rename_i h; rcases h with ⟨h1, h2⟩; subst h1 h2; simp [IProp.unfoldi]
  -- Strategy: Use Bundle_op and map.op (CMRA homomorphism)
  have h_map : ∀ (a b : GF.api E.τ (IProp GF)),
      OFunctor.map (IProp.fold GF) (IProp.unfold GF) (a • b) ≡
      OFunctor.map (IProp.fold GF) (IProp.unfold GF) a •
      OFunctor.map (IProp.fold GF) (IProp.unfold GF) b :=
    fun a b => (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).op a b
  symm
  refine .trans ?_ (h_map (E.Bundle x) (E.Bundle y))
  apply OFE.NonExpansive.eqv
  apply OFE.transpAp_op_mp (E.TranspMap <|  F.ap (IProp GF)).symm (E.TranspClass <| F.ap (IProp GF)).symm

-- Helper lemmas for iSingleton validity and freedom properties

-- iSingleton is free at all keys except γ
theorem iSingleton_free_at_ne {GF F} [RFunctorContractive F] [E : ElemG GF F]
    (γ : GName) (v : F.ap (IProp GF)) (γ' : GName) (h : γ' ≠ γ) :
    (iSingleton F γ v E.τ).car γ' = none := by
  simp [iSingleton, h]

-- iSingleton at a single key has infinitely many free keys
theorem iSingleton_infinite_free {GF F} [RFunctorContractive F] [E : ElemG GF F]
    (γ : GName) (v : F.ap (IProp GF)) :
    Infinite (IsFree (iSingleton F γ v E.τ).car) := by
  refine ⟨Poke id γ, ?_, ?_⟩
  · intro n
    simp [IsFree, Poke]
    split
    · rename_i h; exact iSingleton_free_at_ne γ v n (Nat.ne_of_lt h)
    · rename_i h; exact iSingleton_free_at_ne γ v (n + 1) (Nat.ne_of_gt (Nat.lt_succ_of_le (Nat.ge_of_not_lt h)))
  · intro n m; simp [Poke]; split <;> split <;> omega

-- iSingleton at τ' ≠ E.τ is the unit
theorem iSingleton_ne_eq_unit {GF F} [RFunctorContractive F] [E : ElemG GF F]
    (γ : GName) (v : F.ap (IProp GF)) (τ' : GType) (h : τ' ≠ E.τ) :
    (iSingleton F γ v τ').car = (UCMRA.unit : GenMap Nat _).car := by
  ext γ'; simp [iSingleton, h]

-- Composing with iSingleton preserves freedom at keys ≠ γ
theorem iSingleton_op_free_at_ne {GF F} [RFunctorContractive F] [E : ElemG GF F]
    (γ : GName) (v : F.ap (IProp GF)) (m : GenMap GName (GF.api E.τ (IPre GF)))
    (γ' : GName) (h_ne : γ' ≠ γ) (h_free : m.car γ' = none) :
    ((iSingleton F γ v E.τ) • m).car γ' = none := by
  simp [CMRA.op, optionOp, iSingleton, h_ne, h_free]

-- Composing with iSingleton preserves infinite free keys
theorem iSingleton_preserves_infinite_free {GF F} [RFunctorContractive F] [E : ElemG GF F]
    (γ : GName) (v : F.ap (IProp GF)) (m : GenMap GName (GF.api E.τ (IPre GF)))
    (h_inf : Infinite (IsFree m.car)) :
    Infinite (IsFree ((iSingleton F γ v E.τ) • m).car) := by
  rcases h_inf with ⟨enum, h_enum_free, h_enum_inj⟩
  by_cases h_gamma_in : ∃ n₀, enum n₀ = γ
  · -- If γ appears in enum, use Poke to skip it
    rcases h_gamma_in with ⟨n₀, h_n₀⟩
    refine ⟨Poke enum n₀, ?_, ?_⟩
    · intro n; simp [IsFree, Poke]; split
      · rename_i h; apply iSingleton_op_free_at_ne
        · intro heq; exact absurd (h_enum_inj (heq.trans h_n₀.symm)) (Nat.ne_of_lt h)
        · exact h_enum_free
      · rename_i h; apply iSingleton_op_free_at_ne
        · intro heq; exact absurd (h_enum_inj (heq.trans h_n₀.symm)) (by omega)
        · exact h_enum_free
    · intro n m h_eq; simp [Poke] at h_eq
      split at h_eq <;> split at h_eq <;> rename_i hn hm
      · exact h_enum_inj h_eq
      · have : n = m + 1 := h_enum_inj h_eq; omega
      · have : n + 1 = m := h_enum_inj h_eq; omega
      · have : n + 1 = m + 1 := h_enum_inj h_eq; omega
  · -- If γ not in enum, all enumerated keys remain free
    refine ⟨enum, ?_, h_enum_inj⟩
    intro n; simp [IsFree]
    apply iSingleton_op_free_at_ne
    · intro heq; exact h_gamma_in ⟨n, heq⟩
    · exact h_enum_free

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
  · rename_i h
    rcases h with ⟨h_τ, h_γ⟩
    subst h_τ h_γ
    refine Dist.op_l ?_
    simp [CMRA.op, optionOp]
    -- Need to show unfoldi (E.Bundle a1) ≡{n}≡ unfoldi (E.Bundle a2) • unfoldi (E.Bundle ac)
    -- This should follow from Hac and the fact that unfoldi and E.Bundle are morphisms
    have h1 : E.Bundle a1 ≡{n}≡ E.Bundle (a2 • ac) := by
      apply NonExpansive.ne
      exact Hac.dist
    -- Use Bundle_op: Bundle (a2 • ac) ≡ Bundle a2 • Bundle ac
    -- have h2 : E.Bundle (a2 • ac) ≡ E.Bundle a2 • E.Bundle ac := ElemG.Bundle_op E a2 ac
    -- Combine h1 and h2
    have h3 : E.Bundle a1 ≡{n}≡ E.Bundle a2 • E.Bundle ac := by
      refine Dist.trans h1 ?_
      apply OFE.transpAp_op_mpr (E.TranspMap (F.ap (IProp GF))) (E.TranspClass (F.ap (IProp GF))) |>.dist
    -- Apply unfoldi (which is OFunctor.map, a CMRA homomorphism)
    have h4 : IProp.unfoldi (E.Bundle a2 • E.Bundle ac) ≡{n}≡
              IProp.unfoldi (E.Bundle a2) • IProp.unfoldi (E.Bundle ac) := by
      simp [IProp.unfoldi]
      exact (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).op _ _ |>.dist
    -- Apply unfoldi to both sides of h3
    have h5 : IProp.unfoldi (E.Bundle a1) ≡{n}≡ IProp.unfoldi (E.Bundle a2 • E.Bundle ac) := by
      apply NonExpansive.ne
      exact h3
    exact Dist.trans h5 h4
  · simp [CMRA.op, optionOp]

theorem iOwn_cmraValid {a : F.ap (IProp GF)} : iOwn γ a ⊢ UPred.cmraValid a := by
  refine .trans (UPred.ownM_valid _) ?_
  refine UPred.valid_entails (fun n H => ?_)
  -- H : ✓{n} iSingleton F γ a
  -- iSingleton is a function (τ' : GType) → GenMap GName (...)
  -- For it to be valid, each GenMap must be valid
  -- At τ' = E.τ, the GenMap has (some (unfoldi (Bundle a))) at key γ
  -- GenMap validity means pointwise validity of the underlying function
  -- So we get ✓{n} (some (unfoldi (Bundle a)))
  -- Which gives us ✓{n} (unfoldi (Bundle a))
  -- We need to work backwards through Bundle and unfoldi
  have h_genmap : ✓{n} ((iSingleton F γ a) E.τ) := H E.τ
  rcases h_genmap with ⟨h_valid, h_inf⟩
  -- h_valid : ✓{n} ((iSingleton F γ a) E.τ).car
  -- This is pointwise validity of the function GName → Option (...)
  have h_at_γ : ✓{n} (((iSingleton F γ a) E.τ).car γ) := h_valid γ
  -- Unfold iSingleton
  simp [iSingleton] at h_at_γ
  -- h_at_γ : ✓{n} some (unfoldi.f (E.Bundle a))
  -- Since ✓{n} some x = ✓{n} x, we have:
  simp [CMRA.ValidN, optionValidN] at h_at_γ
  -- h_at_γ : ✓{n} (unfoldi.f (E.Bundle a))
  -- Strategy: Use that foldi ∘ unfoldi ≡ id to transfer validity
  -- foldi (unfoldi (E.Bundle a)) ≡ E.Bundle a
  have h_fold_unfold : IProp.foldi (IProp.unfoldi (E.Bundle a)) ≡ E.Bundle a :=
    IProp.foldi_unfoldi (E.Bundle a)
  -- Use validN_ne to transfer from unfoldi to foldi ∘ unfoldi
  -- But we need ✓{n} (foldi (unfoldi (E.Bundle a))) from ✓{n} (unfoldi (E.Bundle a))
  -- This needs foldi to preserve validity - but foldi is non-expansive (morphism)
  -- Actually, we need to show that non-expansive maps preserve validity
  -- For now, use sorry for the morphism validity preservation
  have h_bundle_valid : ✓{n} (E.Bundle a) := by
    -- We have h_fold_unfold : foldi (unfoldi (E.Bundle a)) ≡ E.Bundle a
    -- Use validN_ne to transfer validity along this equivalence
    apply CMRA.validN_ne h_fold_unfold.dist
    -- Now need ✓{n} (foldi (unfoldi (E.Bundle a)))
    -- Use foldi_validN to preserve validity through foldi
    exact IProp.foldi_validN (IProp.unfoldi (E.Bundle a)) h_at_γ
  -- Now we have ✓{n} (E.Bundle a)
  -- Use that E.Unbundle (E.Bundle a) ≡ a
  have h_unbundle_bundle : E.Unbundle (E.Bundle a) ≡ a := ElemG.Unbundle_Bundle E a
  -- Use validN_ne to conclude
  apply CMRA.validN_ne h_unbundle_bundle.dist
  -- Now need ✓{n} (E.Unbundle (E.Bundle a))
  apply OFE.transpAp_validN_mp (E.TranspMap (F.ap (IProp GF))) (E.TranspClass (F.ap (IProp GF)))
  exact h_bundle_valid

theorem iOwn_cmraValid_op {a1 a2 : F.ap (IProp GF)} : iOwn γ a1 ∗ iOwn γ a2 ⊢ UPred.cmraValid (a1 • a2) :=
  iOwn_op.mpr.trans iOwn_cmraValid

theorem iOwn_valid_r {a : F.ap (IProp GF)} : iOwn γ a ⊢ iOwn γ a ∗ UPred.cmraValid a :=
  BI.persistent_entails_l iOwn_cmraValid

theorem iOwn_valid_l {a : F.ap (IProp GF)} : iOwn γ a ⊢ UPred.cmraValid a ∗ iOwn γ a :=
  BI.persistent_entails_r iOwn_cmraValid

-- Helper lemma: unfoldi ∘ E.Bundle preserves CoreId
theorem unfoldi_Bundle_coreId {a : F.ap (IProp GF)} [CMRA.CoreId a] :
    CMRA.CoreId (unfoldi (E.Bundle a)) := by
  constructor
  -- unfoldi is OFunctor.map, which is (RFunctor.map ...).toHom
  -- RFunctor.map is a CMRA.Hom, which preserves pcore
  simp only [unfoldi, OFunctor.map]
  letI : RFunctor (GF E.τ).fst := (GF E.τ).snd.toRFunctor
  have bundle_coreId : CMRA.CoreId (E.Bundle a) := by
    constructor
    calc
      CMRA.pcore (E.Bundle a)
      ≡ (CMRA.pcore a).map E.Bundle := by
        apply OFE.Equiv.symm
        apply OFE.transpAp_pcore_mpr (E.TranspMap (F.ap (IProp GF))) (E.TranspClass (F.ap (IProp GF)))
      _ ≡ (some a).map E.Bundle := by
        have : CMRA.pcore a ≡ some a := CMRA.CoreId.core_id
        rcases h : CMRA.pcore a with (_ | ca)
        · rw [h] at this; simp [Option.Forall₂] at this
        · rw [h] at this
          simp [Option.Forall₂] at this
          simp [Option.map, Option.Forall₂]
          exact OFE.NonExpansive.eqv this
      _ ≡ some (E.Bundle a) := by simp [Option.map, Option.Forall₂, OFE.Equiv.rfl]
  -- Now use that RFunctor.map preserves pcore
  calc
    CMRA.pcore ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f (E.Bundle a))
    ≡ (CMRA.pcore (E.Bundle a)).map (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f :=
      (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).pcore (E.Bundle a) |>.symm
    _ ≡ (some (E.Bundle a)).map (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f := by
      have : CMRA.pcore (E.Bundle a) ≡ some (E.Bundle a) := bundle_coreId.core_id
      rcases h : CMRA.pcore (E.Bundle a) with (_ | c)
      · rw [h] at this; simp [Option.Forall₂] at this
      · rw [h] at this
        simp [Option.Forall₂] at this
        simp [Option.map, Option.Forall₂]
        exact OFE.NonExpansive.eqv this
    _ ≡ some ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f (E.Bundle a)) := by
      simp [Option.map, Option.Forall₂, OFE.Equiv.rfl]

instance {a : F.ap (IProp GF)} [CMRA.CoreId a] : BI.Persistent (iOwn γ a) where
  persistent := by
    simp [iOwn]
    refine .trans (UPred.persistently_ownM_core _) ?_
    refine BI.persistently_mono ?_
    refine BI.equiv_iff.mp ?_ |>.mp
    refine OFE.NonExpansive.eqv ?_
    -- Need: CMRA.core (iSingleton F γ a) ≡ iSingleton F γ a
    haveI : CMRA.CoreId (iSingleton F γ a) := by
      constructor
      unfold iSingleton
      -- pcore of outer function (GType → ...)
      simp only [CMRA.pcore, cmraDiscreteFunO]
      intro τ'
      -- pcore of GenMap: pcore x = Option.map GenMap.mk <| CMRA.pcore x.car
      simp only [instCMRA_GenMap, Option.map]
      -- GenMap equivalence is pointwise equivalence of car functions
      intro γ'
      -- Simplify .car projections
      simp only [GenMap.mk]
      -- For functions: core f = fun x => core (f x)
      simp only [CMRA.core, CMRA.pcore, cmraDiscreteFunO, Option.getD, Option.map]
      -- Now: optionCore (if ... then some (unfoldi (E.Bundle a)) else none) ≡ if ... then some (unfoldi (E.Bundle a)) else none
      split
      · -- Case: τ' = E.τ ∧ γ' = γ
        -- Need: optionCore (some (cast (unfoldi (E.Bundle a)))) ≡ some (cast (unfoldi (E.Bundle a)))
        -- where cast = ⋯ ▸ ...
        rename_i h
        simp only [CMRA.core, optionCore]
        -- Goal is now: (some (cast x)).bind pcore ≡ some (cast x)
        -- This follows from CoreId of the casted value
        -- The cast comes from h.1 : τ' = E.τ
        simp only [Option.bind]
        -- Need: pcore (cast x) ≡ some (cast x)
        -- Use that cast preserves CoreId
        have bundle_coreId : CMRA.CoreId (unfoldi (E.Bundle a)) := unfoldi_Bundle_coreId
        -- The casted value also has CoreId
        have : CMRA.CoreId (h.1 ▸ unfoldi (E.Bundle a)) := by
          cases h.1
          exact bundle_coreId
        exact this.core_id
      · -- Case: ¬(τ' = E.τ ∧ γ' = γ), so none
        -- core none = none
        rfl
    apply CMRA.core_eqv_self

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
          have hb : ✓{n} (E.Bundle (f (PE 0))) := by
            apply OFE.transpAp_validN_mpr (E.TranspMap (F.ap (IProp GF))) (E.TranspClass (F.ap (IProp GF)))
            exact hvn
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
      -- Use the intersection lemma to find γ ∈ P ∩ IsFree
      -- Since both P and IsFree (z E.τ).car are infinite predicates on Nat,
      -- their intersection must be nonempty (this is Infinite.inter_nonempty_nat)
      have h_inter : ∃ n, P n ∧ IsFree (z E.τ).car n := by
        apply Infinite.inter_nonempty_nat HI Hinf_free
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
          have hb : ✓{n} (E.Bundle (f γ')) := by
            apply OFE.transpAp_validN_mpr (E.TranspMap (F.ap (IProp GF))) (E.TranspClass (F.ap (IProp GF)))
            apply hvn
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
    -- Need to prove: iSingleton F γ a ~~>: fun y => ∃ a', y = iSingleton F γ a' ∧ P a'
    intro n mz Hv
    -- The frame mz is optional, and Hv tells us that iSingleton F γ a •? mz is valid
    -- The iSingleton at E.τ, γ contains unfoldi (E.Bundle a)
    -- We need to extract the frame's value at E.τ, γ and "unwrap" it to get the frame for a

    -- Derive validity and apply the update by case analysis on mz
    cases mz with
    | none =>
      -- No frame case
      -- First derive ✓{n} a from Hv
      have h_a_valid : ✓{n} a := by
        -- From Hv, at position E.τ and key γ, we have ✓{n} some (unfoldi (E.Bundle a))
        have h_valid_at_tau : ✓{n} ((iSingleton F γ a) E.τ) := Hv E.τ
        rcases h_valid_at_tau with ⟨h_pointwise, _⟩
        have h_at_gamma : ✓{n} (((iSingleton F γ a) E.τ).car γ) := h_pointwise γ
        simp [iSingleton] at h_at_gamma
        simp [CMRA.ValidN, optionValidN] at h_at_gamma
        -- h_at_gamma : ✓{n} (unfoldi (E.Bundle a))
        -- Use foldi to go back: foldi (unfoldi (E.Bundle a)) ≡ E.Bundle a
        have h_fold_unfold := IProp.foldi_unfoldi (E.Bundle a)
        have h_bundle_valid : ✓{n} (E.Bundle a) := by
          apply CMRA.validN_ne h_fold_unfold.dist
          exact IProp.foldi_validN (IProp.unfoldi (E.Bundle a)) h_at_gamma
        -- Use Unbundle to go back: Unbundle (Bundle a) ≡ a
        have h_unbundle_bundle := ElemG.Unbundle_Bundle E a
        apply CMRA.validN_ne h_unbundle_bundle.dist
        apply OFE.transpAp_validN_mp (E.TranspMap (F.ap (IProp GF))) (E.TranspClass (F.ap (IProp GF)))
        exact h_bundle_valid

      -- Apply update with none frame
      obtain ⟨a', Ha'_P, Ha'_valid⟩ := Hupd n none (by simp [CMRA.op?]; exact h_a_valid)

      refine ⟨iSingleton F γ a', ⟨a', rfl, Ha'_P⟩, ?_⟩
      -- Show ✓{n} (iSingleton F γ a')
      simp [CMRA.op?]
      intro τ'
      by_cases h_tau : τ' = E.τ
      · -- At τ' = E.τ: need to show the GenMap is valid
        subst h_tau
        refine ⟨?_, ?_⟩
        · -- Pointwise validity
          intro γ'
          simp [iSingleton]
          by_cases h_gamma : γ' = γ
          · -- At key γ: need ✓{n} (some (unfoldi (E.Bundle a')))
            simp [h_gamma, CMRA.ValidN, optionValidN]
            -- From Ha'_valid : ✓{n} a', we need ✓{n} (unfoldi (E.Bundle a'))
            simp [CMRA.op?] at Ha'_valid
            -- Apply Bundle
            have h_bundle_valid : ✓{n} (E.Bundle a') := by
              apply OFE.transpAp_validN_mpr (E.TranspMap (F.ap (IProp GF))) (E.TranspClass (F.ap (IProp GF)))
              apply Ha'_valid
            -- Apply unfoldi
            exact IProp.unfoldi_validN (E.Bundle a') h_bundle_valid
          · -- At other keys: none is always valid
            simp [h_gamma, CMRA.ValidN, optionValidN]
        · -- Infinite free keys: all keys except γ are free
          refine ⟨Poke id γ, ?_, ?_⟩
          · intro n; simp [IsFree, iSingleton, Poke]; split <;> omega
          · intro n m; simp [Poke]; split <;> split <;> omega
      · -- At τ' ≠ E.τ: iSingleton is the unit
        simp [iSingleton, h_tau]
        exact (UCMRA.unit_valid : ✓ (UCMRA.unit : GenMap Nat ((GF τ').fst (IPre GF) (IPre GF)))).validN

    | some mz' =>
      -- With frame case
      cases h_mz_gamma : (mz' E.τ).car γ with
      | none =>
        -- Frame has none at γ, similar to none case
        have h_a_valid : ✓{n} a := by
          have h_valid_at_tau : ✓{n} ((iSingleton F γ a •? some mz') E.τ) := Hv E.τ
          simp [CMRA.op?] at h_valid_at_tau
          rcases h_valid_at_tau with ⟨h_pointwise, _⟩
          have h_at_gamma : ✓{n} ((((iSingleton F γ a) • mz') E.τ).car γ) := h_pointwise γ
          simp [iSingleton, CMRA.op, optionOp, h_mz_gamma] at h_at_gamma
          simp [CMRA.ValidN, optionValidN] at h_at_gamma
          have h_fold_unfold := IProp.foldi_unfoldi (E.Bundle a)
          have h_bundle_valid : ✓{n} (E.Bundle a) := by
            apply CMRA.validN_ne h_fold_unfold.dist
            exact IProp.foldi_validN (IProp.unfoldi (E.Bundle a)) h_at_gamma
          have h_unbundle_bundle := ElemG.Unbundle_Bundle E a
          apply CMRA.validN_ne h_unbundle_bundle.dist
          apply OFE.transpAp_validN_mp (E.TranspMap (F.ap (IProp GF))) (E.TranspClass (F.ap (IProp GF)))
          exact h_bundle_valid

        obtain ⟨a', Ha'_P, Ha'_valid⟩ := Hupd n none (by simp [CMRA.op?]; exact h_a_valid)

        refine ⟨iSingleton F γ a', ⟨a', rfl, Ha'_P⟩, ?_⟩
        -- Show ✓{n} (iSingleton F γ a' •? some mz')
        simp [CMRA.op?]
        intro τ'
        by_cases h_tau : τ' = E.τ
        · -- At τ' = E.τ
          subst h_tau
          refine ⟨?_, ?_⟩
          · -- Pointwise validity
            intro γ'
            simp [CMRA.op]
            by_cases h_gamma : γ' = γ
            · -- At key γ: frame has none, so just need validity of singleton
              simp [h_gamma, iSingleton, optionOp, h_mz_gamma, CMRA.ValidN, optionValidN]
              simp [CMRA.op?] at Ha'_valid
              have h_bundle_valid : ✓{n} (E.Bundle a') := by
                apply OFE.transpAp_validN_mpr (E.TranspMap (F.ap (IProp GF))) (E.TranspClass (F.ap (IProp GF)))
                apply Ha'_valid
              exact IProp.unfoldi_validN (E.Bundle a') h_bundle_valid
            · -- At other keys: just propagate frame validity
              simp [h_gamma, iSingleton, optionOp]
              have h_frame_valid := Hv E.τ
              simp [CMRA.op?] at h_frame_valid
              rcases h_frame_valid with ⟨h_pointwise, _⟩
              have h_at_gamma' := h_pointwise γ'
              simp [CMRA.op, iSingleton, h_gamma, optionOp] at h_at_gamma'
              exact h_at_gamma'
          · -- Infinite free keys
            have h_frame_inf := Hv E.τ
            simp [CMRA.op?] at h_frame_inf
            rcases h_frame_inf with ⟨_, h_inf⟩
            -- The frame has infinite free keys when composed with the old singleton
            -- We need to show it still has infinite free keys with the new singleton
            -- Since both singletons only occupy key γ, the free keys are the same
            apply Infinite.mono h_inf
            intro k h_free
            simp [IsFree, CMRA.op, iSingleton, optionOp] at h_free ⊢
            by_cases h_k : k = γ
            · simp [h_k, h_mz_gamma, optionOp] at h_free
            · simp [h_k, optionOp] at h_free ⊢
              exact h_free
        · -- At τ' ≠ E.τ: both singleton and composition are well-behaved
          have h_frame_valid := Hv τ'
          simp [CMRA.op?, CMRA.op, iSingleton, h_tau] at h_frame_valid ⊢
          exact h_frame_valid

      | some v =>
        -- Frame has some v at γ
        have h_a_valid : ✓{n} (a • E.Unbundle (IProp.foldi v)) := by
          have h_valid_at_tau : ✓{n} ((iSingleton F γ a •? some mz') E.τ) := Hv E.τ
          simp [CMRA.op?] at h_valid_at_tau
          rcases h_valid_at_tau with ⟨h_pointwise, _⟩
          have h_at_gamma : ✓{n} ((((iSingleton F γ a) • mz') E.τ).car γ) := h_pointwise γ
          simp [iSingleton, CMRA.op, optionOp, h_mz_gamma] at h_at_gamma
          simp [CMRA.ValidN, optionValidN] at h_at_gamma
          -- h_at_gamma : ✓{n} (unfoldi (E.Bundle a) • v)
          -- Need: ✓{n} (a • E.Unbundle (foldi v))
          -- Strategy: Apply foldi (which is a CMRA homomorphism)
          simp [IProp.foldi, IProp.unfoldi] at h_at_gamma ⊢
          letI : RFunctor (GF E.τ).fst := (GF E.τ).snd.toRFunctor
          -- foldi preserves validity
          have h_foldi_valid : ✓{n} ((RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f
              ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f (E.Bundle a) • v)) := by
            exact IProp.foldi_validN _ h_at_gamma
          -- foldi is a homomorphism
          have h_foldi_hom := (RFunctor.map (IProp.unfold GF) (IProp.fold GF)).op
              ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f (E.Bundle a)) v
          have h_after_hom : ✓{n} ((RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f
              ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f (E.Bundle a)) •
              (RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f v) := by
            apply CMRA.validN_ne h_foldi_hom.dist
            exact h_foldi_valid
          -- Use proj_fold_unfold
          have h_comp : (RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f
              ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f (E.Bundle a)) ≡ E.Bundle a := by
            refine .trans (OFunctor.map_comp (F := GF E.τ |>.fst) ..).symm ?_
            refine .trans ?_ (OFunctor.map_id (F := GF E.τ |>.fst) (E.Bundle a))
            apply OFunctor.map_ne.eqv <;> intro _ <;> simp [IProp.unfold, IProp.fold]
          have h_bundle_foldi_v : ✓{n} (E.Bundle a • (RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f v) := by
            apply CMRA.validN_ne (h_comp.op_l).dist
            exact h_after_hom
          -- Apply Unbundle
          have h_unbundle_hom : E.Unbundle (E.Bundle a • (RFunctor.map (unfold GF) (fold GF)).f v) ≡ E.Unbundle (E.Bundle a) • E.Unbundle ((RFunctor.map (unfold GF) (fold GF)).f v) := by
            apply OFE.transpAp_op_mp (E.TranspMap ((GF (ElemG.τ GF F)).fst.ap (IPre GF))) (E.TranspClass ((GF (ElemG.τ GF F)).fst.ap (IPre GF)))
            -- ElemG.Unbundle_op E (E.Bundle a) ((RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f v)
          have h_after_unbundle : ✓{n} (E.Unbundle (E.Bundle a) • E.Unbundle ((RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f v)) := by
            apply CMRA.validN_ne h_unbundle_hom.dist
            apply OFE.transpAp_validN_mp (E.TranspMap (F.ap (IProp GF))) (E.TranspClass (F.ap (IProp GF)))
            apply h_bundle_foldi_v
          -- Use Unbundle_Bundle
          have h_unbundle_bundle := ElemG.Unbundle_Bundle E a
          apply CMRA.validN_ne (h_unbundle_bundle.op_l).dist
          exact h_after_unbundle

        obtain ⟨a', Ha'_P, Ha'_valid⟩ := Hupd n (some (E.Unbundle (IProp.foldi v))) (by simp [CMRA.op?]; exact h_a_valid)

        refine ⟨iSingleton F γ a', ⟨a', rfl, Ha'_P⟩, ?_⟩
        -- Show ✓{n} (iSingleton F γ a' •? some mz')
        -- This is the reverse of extracting h_a_valid from Hv
        simp [CMRA.op?]
        intro τ'
        by_cases h_tau : τ' = E.τ
        · -- At τ' = E.τ
          subst h_tau
          refine ⟨?_, ?_⟩
          · -- Pointwise validity
            intro γ'
            simp [CMRA.op]
            by_cases h_gamma : γ' = γ
            · -- At key γ: need to go from Ha'_valid to validity of singleton • frame
              simp [h_gamma, iSingleton, optionOp, h_mz_gamma, CMRA.ValidN, optionValidN]
              -- Ha'_valid : ✓{n} (a' • E.Unbundle (foldi v))
              -- Need: ✓{n} (unfoldi (E.Bundle a') • v)
              simp [CMRA.op?] at Ha'_valid
              -- Reverse of what we did before
              letI : RFunctor (GF E.τ).fst := (GF E.τ).snd.toRFunctor
              -- From ✓{n} (a' • E.Unbundle (foldi v))
              -- Apply Bundle
              have h_bundle_valid : ✓{n} (E.Bundle a' • E.Bundle (E.Unbundle (foldi v))) := by
                apply CMRA.validN_ne (OFE.transpAp_op_mpr (E.TranspMap (F.ap (IProp GF))) (E.TranspClass (F.ap (IProp GF))) |>.dist)
                apply OFE.transpAp_validN_mpr (E.TranspMap (F.ap (IProp GF))) (E.TranspClass (F.ap (IProp GF)))
                apply Ha'_valid
              -- Use Bundle_Unbundle
              have h_bundle_unbundle := ElemG.Bundle_Unbundle E (foldi v)
              have h_bundle_foldi_v : ✓{n} (E.Bundle a' • foldi v) := by
                apply CMRA.validN_ne (h_bundle_unbundle.op_r).dist
                exact h_bundle_valid
              -- Apply unfoldi
              simp [IProp.unfoldi, IProp.foldi] at h_bundle_foldi_v ⊢
              have h_unfoldi_op := (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).op (E.Bundle a') ((RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f v)
              have h_after_unfoldi : ✓{n} ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f (E.Bundle a') •
                  (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f ((RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f v)) := by
                apply CMRA.validN_ne h_unfoldi_op.dist
                exact IProp.unfoldi_validN _ h_bundle_foldi_v
              -- Use unfoldi_foldi
              have h_unfoldi_foldi := IProp.unfoldi_foldi v
              apply CMRA.validN_ne (h_unfoldi_foldi.op_r).dist
              exact h_after_unfoldi
            · -- At other keys: propagate frame validity
              simp [h_gamma, iSingleton, optionOp]
              have h_frame_valid := Hv E.τ
              simp [CMRA.op?] at h_frame_valid
              rcases h_frame_valid with ⟨h_pointwise, _⟩
              have h_at_gamma' := h_pointwise γ'
              simp [CMRA.op, iSingleton, h_gamma, optionOp] at h_at_gamma'
              exact h_at_gamma'
          · -- Infinite free keys
            have h_frame_inf := Hv E.τ
            simp [CMRA.op?] at h_frame_inf
            rcases h_frame_inf with ⟨_, h_inf⟩
            apply Infinite.mono h_inf
            intro k h_free
            simp [IsFree, CMRA.op, iSingleton, optionOp] at h_free ⊢
            by_cases h_k : k = γ
            · simp [h_k, h_mz_gamma, optionOp] at h_free
            · simp [h_k, optionOp] at h_free ⊢
              exact h_free
        · -- At τ' ≠ E.τ
          have h_frame_valid := Hv τ'
          simp [CMRA.op?, CMRA.op, iSingleton, h_tau] at h_frame_valid ⊢
          exact h_frame_valid
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

-- Helper lemmas for iOwn_unit

-- Bundle preserves unit structure
theorem ElemG.Bundle_unit {GF F} [RFunctorContractive F] (E : ElemG GF F)
    {ε : F.ap (IProp GF)} [IsUnit ε] :
    IsUnit (E.Bundle ε) := by
  refine { unit_valid := ?_, unit_left_id := ?_, pcore_unit := ?_ }
  · -- Validity: ✓ (E.Bundle ε)
    -- Use Bundle_validN which we already have
    refine CMRA.valid_iff_validN.mpr fun n => ?_
    apply OFE.transpAp_validN_mpr (E.TranspMap (F.ap (IProp GF))) (E.TranspClass (F.ap (IProp GF)))
    apply IsUnit.unit_valid.validN
  · -- Left identity: E.Bundle ε • x ≡ x
    intro x
    -- Key insight: Bundle and Unbundle are essentially identity after accounting for the cast
    -- Strategy: Apply Unbundle to both sides, show they're equal, then use that Unbundle is injective
    -- (in the sense that if Unbundle a ≡ Unbundle b, then a ≡ b)
    have h1 : E.Unbundle (E.Bundle ε • x) ≡ E.Unbundle x := by
      -- Use the fact that Unbundle is non-expansive and Bundle/Unbundle compose to identity
      calc
        E.Unbundle (E.Bundle ε • x)
          ≡ E.Unbundle (E.Bundle ε) • E.Unbundle x := by
            -- We need Unbundle to be a CMRA morphism (preserves op)
            -- Use the new lemma OFE.cast_op_from_RFunctor_mp
            unfold Bundle Unbundle
            have h_fun : (GF E.τ).fst = F := (Sigma.mk.inj E.transp).left
            have h_inst : HEq (GF E.τ).snd ‹RFunctorContractive F› := (Sigma.mk.inj E.transp).right
            -- After unfolding, the goal is:
            -- .mp ((.mpr ε) • x) ≡ .mp (.mpr ε) • .mp x
            -- where .mpr ε : (GF E.τ).fst.ap (IProp GF)
            -- This is exactly OFE.cast_op_from_RFunctor_mp
            apply OFE.transpAp_op_mp h_fun h_inst
        _ ≡ ε • E.Unbundle x := by
            have := ElemG.Unbundle_Bundle E ε
            exact this.op_l
        _ ≡ E.Unbundle x := IsUnit.unit_left_id
    -- Now use that Bundle ∘ Unbundle ≡ id
    calc
      E.Bundle ε • x
        ≡ E.Bundle (E.Unbundle (E.Bundle ε • x)) := by
          have := ElemG.Bundle_Unbundle E (E.Bundle ε • x)
          exact this.symm
        _ ≡ E.Bundle (E.Unbundle x) := by exact OFE.NonExpansive.eqv h1
        _ ≡ x := ElemG.Bundle_Unbundle E x
  · -- Pcore: CMRA.pcore (E.Bundle ε) ≡ some (E.Bundle ε)
    calc
      CMRA.pcore (E.Bundle ε)
      ≡ (CMRA.pcore ε).map E.Bundle := by
        symm
        apply OFE.transpAp_pcore_mpr (E.TranspMap (F.ap (IProp GF))) (E.TranspClass (F.ap (IProp GF)))
      _ ≡ Option.map E.Bundle (some ε) := by
         rename_i unit
         have := (unit.pcore_unit)
         rcases eqn: CMRA.pcore ε
         · simp
           rw [eqn] at this
           simp [Option.Forall₂] at this
         · simp
           rw [eqn] at this
           simp [Option.Forall₂] at this
           exact NonExpansive.eqv this
      _ ≡ E.Bundle ε := by rfl

-- unfoldi preserves unit structure
theorem IProp.unfoldi_unit {GF : BundledGFunctors} {τ : GType}
    {x : GF.api τ (IProp GF)} [IsUnit x] :
    IsUnit (unfoldi x) := by
  refine { unit_valid := ?_, unit_left_id := ?_, pcore_unit := ?_ }
  · -- Validity: ✓ (E.Bundle ε)
    -- Use Bundle_validN which we already have
    refine CMRA.valid_iff_validN.mpr fun n => ?_
    apply IProp.unfoldi_validN
    apply IsUnit.unit_valid.validN
  · intro y
    -- x is a unit in GF.api τ (IProp GF), need to show unfoldi x is a unit
    -- Strategy: apply foldi to both sides, use that x is a unit, then use unfoldi_foldi
    have h : foldi (unfoldi x • y) ≡ foldi y := by
      -- foldi is a CMRA homomorphism, so it preserves op
      simp only [foldi, unfoldi, OFunctor.map]
      letI : RFunctor (GF τ).fst := (GF τ).snd.toRFunctor
      calc
        (RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f
          ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f x • y)
          ≡ (RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f
              ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f x) •
            (RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f y := by
            exact (RFunctor.map (IProp.unfold GF) (IProp.fold GF)).op _ _
        _ ≡ (RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f y := by
          -- Use that composing the two maps gives id on x, following proj_fold_unfold pattern
          have h_comp : (RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f
                          ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f x) ≡ x := by
            refine .trans (OFunctor.map_comp (F := GF τ |>.fst) ..).symm ?_
            refine .trans ?_ (OFunctor.map_id (F := GF τ |>.fst) x)
            apply OFunctor.map_ne.eqv <;> intro _ <;> simp [IProp.unfold, IProp.fold]
          -- Use that x is a unit
          calc
            (RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f
              ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f x) •
            (RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f y
              ≡ x • (RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f y := h_comp.op_l
            _ ≡ (RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f y := IsUnit.unit_left_id
    -- Now apply unfoldi to both sides
    calc
      unfoldi x • y
        ≡ unfoldi (foldi (unfoldi x • y)) := by
          have := IProp.unfoldi_foldi (unfoldi x • y)
          exact this.symm
        _ ≡ unfoldi (foldi y) := by exact OFE.NonExpansive.eqv h
        _ ≡ y := IProp.unfoldi_foldi y
  · -- pcore_unit: CMRA.pcore (unfoldi x) ≡ some (unfoldi x)
    -- Since unfoldi is a CMRA homomorphism, it preserves pcore
    simp only [unfoldi, OFunctor.map]
    letI : RFunctor (GF τ).fst := (GF τ).snd.toRFunctor
    calc
      CMRA.pcore ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f x)
        ≡ (CMRA.pcore x).map (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f := by
          -- CMRA.Hom preserves pcore (in reverse direction)
          exact (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).pcore x |>.symm
      _ ≡ (some x).map (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f := by
          -- Use that x is a unit, so pcore x ≡ some x
          have h_pcore_unit : CMRA.pcore x ≡ some x := IsUnit.pcore_unit
          -- Apply Option.map to both sides
          have h_map : (CMRA.pcore x).map (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f ≡
                       (some x).map (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f := by
            rcases h : CMRA.pcore x with (_ | cx)
            · -- pcore x = none, contradiction
              rw [h] at h_pcore_unit
              simp [Option.Forall₂] at h_pcore_unit
            · -- pcore x = some cx
              rw [h] at h_pcore_unit
              simp [Option.Forall₂] at h_pcore_unit
              simp [Option.map, Option.Forall₂]
              exact OFE.NonExpansive.eqv h_pcore_unit
          exact h_map
      _ ≡ some ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f x) := by
          simp [Option.map, Option.Forall₂, OFE.Equiv.rfl]


theorem iOwn_unit {γ} {ε : F.ap (IProp GF)} [Hε : IsUnit ε] : ⊢ |==> iOwn γ ε := by
  -- Strategy based on Rocq proof:
  -- 1. Use ownM_unit to get ownM ε
  -- 2. Show ε ~~> iSingleton F γ ε via an allocation update
  -- 3. Use ownM_updateP to lift this to the assertion level

  unfold iOwn

  -- First, use ownM_unit to get emp ⊢ □ ownM ε
  refine .trans (UPred.ownM_unit _) ?_
  refine BI.intuitionistically_elim.trans ?_

  -- Now we need to show: ownM (UCMRA.unit : IResUR GF) ⊢ |==> ownM (iSingleton F γ ε)
  -- This requires a CMRA update: UCMRA.unit ~~> iSingleton F γ ε

  -- The update follows from alloc_unit_singleton_update pattern:
  -- If ✓ u, LeftId u (•), and u ~~>: P, then ∅ ~~>: {[i := y]} where P y

  -- In our setting:
  -- - u is the unit at each τ' (the empty GenMap)
  -- - We want to allocate at position E.τ, key γ
  -- - The value should be unfoldi (E.Bundle ε)

  have Hupd : (UCMRA.unit : IResUR GF) ~~>: (iSingleton F γ ε = ·) := by
    -- Prove the update: UCMRA.unit ~~>: (iSingleton F γ ε = ·)
    -- This follows the Rocq proof's use of alloc_unit_singleton_update
    -- Key insight: Since ε is a unit with ε • x ≡ x (left identity),
    -- we can allocate it at ANY key γ, even if the frame has something there
    -- because ε composes neutrally with everything
    intro n mz Hv
    refine ⟨iSingleton F γ ε, rfl, ?_⟩
    -- Show ✓{n} (iSingleton F γ ε •? mz)
    intro τ'
    by_cases Heq : τ' = E.τ
    · -- At τ' = E.τ: need to show validity at the allocated index
      subst Heq
      refine ⟨?_, ?_⟩
      · -- Pointwise validity at each key
        intro γ'
        unfold iSingleton
        simp [CMRA.op?, CMRA.ValidN, optionValidN]
        cases mz with
        | none =>
          -- No frame: just need validity of the singleton
          simp [CMRA.op, optionOp]
          by_cases h_key : γ' = γ
          · simp [h_key]
            have h1 : ✓{n} (E.Bundle ε) := by
              apply OFE.transpAp_validN_mpr (E.TranspMap (F.ap (IProp GF))) (E.TranspClass (F.ap (IProp GF)))
              apply IsUnit.unit_valid.validN
            simp [IProp.unfoldi]
            letI : RFunctor (GF E.τ).fst := (GF E.τ).snd.toRFunctor
            exact (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).validN h1
          · simp [h_key]
        | some mz' =>
          -- With frame: use that ε is a unit so ε • x ≡ x
          simp [CMRA.op, optionOp]
          have Hv' := Hv E.τ
          simp [CMRA.op?] at Hv'
          rcases Hv' with ⟨h_valid, _⟩
          by_cases h_key : γ' = γ
          · -- At the key γ where we're allocating
            simp [h_key]
            rcases h_mz_at_gamma : (mz' E.τ).car γ with (⟨⟩ | v)
            · -- Frame has none: just need validity of ε
              simp [optionOp]
              have h1 : ✓{n} (E.Bundle ε) := by
                apply OFE.transpAp_validN_mpr (E.TranspMap (F.ap (IProp GF))) (E.TranspClass (F.ap (IProp GF)))
                apply IsUnit.unit_valid.validN
              simp [IProp.unfoldi]
              letI : RFunctor (GF E.τ).fst := (GF E.τ).snd.toRFunctor
              exact (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).validN h1
            · -- Frame has some v: need ✓{n} (unfoldi (E.Bundle ε) • v)
              -- Key insight: ε is a unit, so unfoldi (E.Bundle ε) should also act like a unit
              -- We need: unfoldi (E.Bundle ε) • v ≡ v
              -- Then validity follows from h_valid
              simp [optionOp]
              -- First, we need to know what v's validity is from the frame
              -- We have h_valid : ✓{n} ((UCMRA.unit • mz') E.τ).car
              -- At key γ where (mz' E.τ).car γ = some v
              -- Since UCMRA.unit has none everywhere, (UCMRA.unit • mz') E.τ = mz' E.τ
              -- So h_valid γ gives us validity of v
              have h_unit_at_tau : ((UCMRA.unit : IResUR GF) E.τ).car = (UCMRA.unit : GenMap Nat _).car := rfl
              have h_v_valid : ✓{n} v := by
                have := h_valid γ
                simp [CMRA.op, h_unit_at_tau, optionOp, UCMRA.unit, CMRA.ValidN, optionValidN, h_mz_at_gamma] at this
                exact this
              -- Now we need: ✓{n} (unfoldi (E.Bundle ε) • v)
              -- Strategy: show unfoldi (E.Bundle ε) • v ≡{n}≡ v, then use validN_ne
              -- This requires showing E.Bundle ε and unfoldi of it act as left units
              haveI h_bundle_unit : IsUnit (E.Bundle ε) := ElemG.Bundle_unit E
              haveI h_unfold_unit : IsUnit (IProp.unfoldi (E.Bundle ε)) := IProp.unfoldi_unit
              -- Since unfoldi (E.Bundle ε) is a unit, unfoldi (E.Bundle ε) • v ≡ v
              have h_unit_compose : v ≡{n}≡ IProp.unfoldi (E.Bundle ε) • v := by
                exact h_unfold_unit.unit_left_id.dist.symm
              -- Use validN_ne to transfer validity along the equivalence
              exact CMRA.validN_ne h_unit_compose h_v_valid
          · -- At other keys: just propagate frame validity
            simp [h_key]
            rcases h_mz : (mz' E.τ).car γ' with (⟨⟩ | v)
            · trivial
            · simp [optionOp]
              -- At key γ' where mz' has some v
              -- UCMRA.unit E.τ has none at all keys
              -- So ((UCMRA.unit • mz') E.τ).car γ' = optionOp none (some v) = some v
              have h_unit_none : ((UCMRA.unit : IResUR GF) E.τ).car γ' = none := by
                simp [UCMRA.unit]
              have h_comp : (((UCMRA.unit : IResUR GF) • mz') E.τ).car γ' = some v := by
                simp [CMRA.op, h_unit_none, optionOp, h_mz]
              have := h_valid γ'
              rw [h_comp] at this
              simp [CMRA.ValidN, optionValidN] at this
              exact this
      · -- Infinite free keys: allocation doesn't consume free keys
        cases mz with
        | none =>
          -- No frame: all keys except γ are free
          -- iSingleton at a single key leaves infinitely many keys free
          exact iSingleton_infinite_free γ ε
        | some mz' =>
          -- With frame: free keys are preserved
          have Hv' := Hv E.τ
          simp [CMRA.op?] at Hv'
          rcases Hv' with ⟨_, h_inf⟩
          -- h_inf : Infinite (IsFree ((UCMRA.unit • mz') E.τ).car)
          -- But unit has none everywhere, so (unit • mz') E.τ = mz' E.τ
          -- Therefore the infinite free keys are from mz' E.τ
          have h_unit_mz_eq : ((UCMRA.unit : IResUR GF) • mz') E.τ ≡ mz' E.τ := by
            simp [CMRA.op, OFE.Equiv]
            intro k
            simp [UCMRA.unit, optionOp, Option.Forall₂]
            cases (mz' E.τ).car k <;> simp [OFE.Equiv.rfl]
          have h_inf_mz : Infinite (IsFree (mz' E.τ).car) := by
            -- If (unit • mz') has infinite free keys and unit • mz' ≡ mz',
            -- then mz' has infinite free keys
            apply Infinite.mono h_inf
            intro k h_free
            simp [IsFree] at h_free ⊢
            -- h_free: ((unit • mz') E.τ).car k = none
            -- We know (unit • mz') E.τ = unit E.τ • mz' E.τ
            -- And unit E.τ has none everywhere
            -- So ((unit • mz') E.τ).car k = optionOp none ((mz' E.τ).car k) = (mz' E.τ).car k
            have : ((UCMRA.unit : IResUR GF) E.τ).car k = none := by simp [UCMRA.unit]
            simp [CMRA.op, this, optionOp] at h_free
            exact h_free
          -- Composing with iSingleton preserves infinite free keys
          exact iSingleton_preserves_infinite_free γ ε (mz' E.τ) h_inf_mz
    · -- At τ' ≠ E.τ: iSingleton is unit, so it composes neutrally
      have h_is_unit : (iSingleton F γ ε τ').car = (UCMRA.unit : GenMap Nat _).car := by
        unfold iSingleton
        ext γ'
        simp [Heq]
      cases mz with
      | none =>
        rw [CMRA.op?]
        simp [h_is_unit]
        show ✓{n} (⟨fun γ' => if _ : τ' = E.τ ∧ γ' = γ then _ else none⟩ : GenMap Nat _)
        simp [Heq]
        exact (UCMRA.unit_valid : ✓ (UCMRA.unit : GenMap Nat ((GF τ').fst (IPre GF) (IPre GF)))).validN
      | some mz' =>
        rw [CMRA.op?]
        simp only [CMRA.op, h_is_unit]
        have Hv' := Hv τ'
        simp at Hv'
        have h_eq_struct : (⟨fun x => optionOp ((UCMRA.unit : GenMap Nat _).car x) ((mz' τ').car x)⟩ : GenMap Nat _) ≡ mz' τ' := by
          simp [OFE.Equiv]
          intro γ'
          simp [UCMRA.unit, GenMap.mk, optionOp, Option.Forall₂]
          cases (mz' τ').car γ' <;> simp [OFE.Equiv.rfl]
        have h_unfold : (UCMRA.unit •? some mz') τ' ≡ (⟨fun x => optionOp ((UCMRA.unit : GenMap Nat _).car x) ((mz' τ').car x)⟩ : GenMap Nat _) := by
          simp [CMRA.op?, CMRA.op, h_is_unit]
          rfl
        exact CMRA.validN_ne h_unfold.symm.dist Hv'

  refine .trans (UPred.ownM_updateP _ Hupd) ?_

  -- Clean up the assertion
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
