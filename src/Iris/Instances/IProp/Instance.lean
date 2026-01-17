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
def transpAp {F1 F2 : OFunctorPre} (H : F1 = F2) {T} [OFE T] : F1.ap T = F2.ap T :=
  congrArg (OFunctorPre.ap · T) H

section transpAp

variable [RF₁ : RFunctorContractive F₁] [RF₂ : RFunctorContractive F₂] [OFE T]

theorem OFE.transpAp_eqv_mp (h_fun : F₁ = F₂) (h_inst : HEq RF₁ RF₂) {x y : F₁.ap T} (H : x ≡{n}≡ y) :
    (transpAp h_fun).mp x ≡{n}≡ (transpAp h_fun).mp y := by
  cases h_fun; cases eq_of_heq h_inst; exact H

theorem OFE.transpAp_op_mp (h_fun : F₁ = F₂) (h_inst : HEq RF₁ RF₂) {x y : F₁ T T} :
    (transpAp h_fun).mp (x • y) ≡ (transpAp h_fun).mp x • (transpAp h_fun).mp y := by
  cases h_fun; cases eq_of_heq h_inst; rfl

theorem OFE.transpAp_pcore_mp (h_fun : F₁ = F₂) (h_inst : HEq RF₁ RF₂) {x : F₁ T T} :
    (CMRA.pcore x).map (transpAp h_fun).mp ≡ CMRA.pcore ((transpAp h_fun).mp x) := by
  cases h_fun; cases eq_of_heq h_inst
  simp [Equiv, Option.Forall₂]
  cases CMRA.pcore x <;> simp [Equiv.rfl]

theorem OFE.transpAp_validN_mp (h_fun : F₁ = F₂) (h_inst : HEq RF₁ RF₂) {x : F₁ T T} (H : ✓{n} x) :
    ✓{n} ((transpAp h_fun).mp x) := by
  cases h_fun; cases eq_of_heq h_inst; exact H

theorem OFE.validN_transpAp_mp (h_fun : F₁ = F₂) (h_inst : HEq RF₁ RF₂) {x : F₁ T T}
    (H : ✓{n} ((transpAp h_fun).mp x)) : ✓{n} x := by
  cases h_fun; cases eq_of_heq h_inst; exact H

end transpAp

section ElemG

class ElemG (FF : BundledGFunctors) (F : OFunctorPre) [RFunctorContractive F] where
  τ : GType
  transp : FF τ = ⟨F, ‹_›⟩

open OFE

variable [I : RFunctorContractive F]

def ElemG.transpMap (E : ElemG GF F) T [OFE T] : (GF E.τ).fst = F :=
  Sigma.mk.inj E.transp |>.1

def ElemG.transpClass (E : ElemG GF F) T [OFE T] : HEq (GF E.τ).snd I :=
  Sigma.mk.inj E.transp |>.2

def ElemG.bundle (E : ElemG GF F) [OFE T] : F.ap T → GF.api E.τ T :=
  transpAp (E.transpMap T) |>.mpr

def ElemG.unbundle (E : ElemG GF F) [OFE T] : GF.api E.τ T → F.ap T :=
  transpAp (E.transpMap T) |>.mp

theorem ElemG.bundle_unbundle (E : ElemG GF F) [OFE T] (x : GF.api E.τ T) :
    E.bundle (E.unbundle x) ≡ x := by simp [bundle, unbundle]

theorem ElemG.unbundle_bundle (E : ElemG GF F) [OFE T] (x : F.ap T) :
    E.unbundle (E.bundle x) ≡ x := by simp [bundle, unbundle]

instance ElemG.bundle.ne {E : ElemG GF F} [OFE T] :
    OFE.NonExpansive (E.bundle (T := T)) where
  ne {_ _ _} := OFE.transpAp_eqv_mp (E.transpMap T).symm (E.transpClass T).symm

instance ElemG.unbundle.ne {E : ElemG GF F} [OFE T] :
    OFE.NonExpansive (E.unbundle (T := T)) where
  ne {_ _ _} H := OFE.transpAp_eqv_mp (E.transpMap T) (E.transpClass T) H

theorem bundle_op {GF : BundledGFunctors} [E : ElemG GF F] (a2 ac : F.ap (IProp GF)) :
  E.bundle (a2 • ac) ≡ E.bundle a2 • E.bundle ac := by
  apply Equiv.symm
  apply Equiv.trans (ElemG.bundle_unbundle E _).symm
  refine NonExpansive.eqv ?_
  have h_fun := E.transpMap <| F.ap (IProp GF)
  have h_inst := E.transpClass <| F.ap (IProp GF)
  apply Equiv.trans (transpAp_op_mp h_fun h_inst)
  apply (ElemG.unbundle_bundle E a2).op_l.trans
  apply (ElemG.unbundle_bundle E ac).op_r

theorem unbundle_op {GF : BundledGFunctors} [E : ElemG GF F] (a2 ac : GF.api (ElemG.τ GF F) (IProp GF)) :
  E.unbundle (a2 • ac) ≡ E.unbundle a2 • E.unbundle ac :=
  OFE.transpAp_op_mp (E.transpMap ((GF (ElemG.τ GF F)).fst.ap (IPre GF))) (E.transpClass ((GF (ElemG.τ GF F)).fst.ap (IPre GF)))

-- bundle preserves unit structure
theorem ElemG.bundle_unit {GF F} [RFunctorContractive F] (E : ElemG GF F)
    {ε : F.ap (IProp GF)} [IsUnit ε] :
    IsUnit (E.bundle ε) := by
  refine { unit_valid := ?_, unit_left_id := ?_, pcore_unit := ?_ }
  · -- Validity: use ElemG.bundle_validN
    refine CMRA.valid_iff_validN.mpr fun n => ?_
    apply transpAp_validN_mp (E.transpMap <| F.ap (IProp GF)).symm (E.transpClass <| F.ap (IProp GF)).symm
    apply IsUnit.unit_valid.validN
  · -- Left identity: Strategy: apply unbundle to both sides, use that ε is unit, then bundle back
    intro x
    have h1 : E.unbundle (E.bundle ε • x) ≡ E.unbundle x := by
      calc E.unbundle (E.bundle ε • x)
        _ ≡ E.unbundle (E.bundle ε) • E.unbundle x := by
          apply transpAp_op_mp (E.transpMap <| F.ap (IProp GF)) (E.transpClass <| F.ap (IProp GF))
        _ ≡ ε • E.unbundle x := (ElemG.unbundle_bundle E ε).op_l
        _ ≡ E.unbundle x := IsUnit.unit_left_id
    calc E.bundle ε • x
      ≡ E.bundle (E.unbundle (E.bundle ε • x)) := (ElemG.bundle_unbundle E _).symm
      _ ≡ E.bundle (E.unbundle x) := OFE.NonExpansive.eqv h1
      _ ≡ x := ElemG.bundle_unbundle E x
  · -- Pcore
    calc CMRA.pcore (E.bundle ε)
      ≡ (CMRA.pcore ε).map E.bundle := by
            symm
            apply transpAp_pcore_mp (E.transpMap <| F.ap (IProp GF)).symm (E.transpClass <| F.ap (IProp GF)).symm
      _ ≡ Option.map E.bundle (some ε) := by
         rename_i unit
         have := unit.pcore_unit
         rcases eqn: CMRA.pcore ε
         · rw [eqn] at this; simp [] at this
         · rw [eqn] at this; simp [Option.map] at this ⊢
           exact NonExpansive.eqv this
      _ ≡ E.bundle ε := by rfl

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

-- unfoldi preserves unit structure
theorem IProp.unfoldi_unit {τ : GType} {x : FF.api τ (IProp FF)} [IsUnit x] :
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
    letI : RFunctor (FF τ).fst := (FF τ).snd.toRFunctor
    calc CMRA.pcore (unfoldi.f x)
      _ ≡ (CMRA.pcore x).map unfoldi.f :=
        (RFunctor.map (IProp.fold FF) (IProp.unfold FF)).pcore x |>.symm
      _ ≡ (some x).map unfoldi.f :=
        Option.map_forall₂ _ IsUnit.pcore_unit
      _ ≡ some (unfoldi.f x) := by
        simp [Option.map, OFE.Equiv.rfl]

end Fold

section iSingleton

open IProp OFE UPred

def iSingleton {GF} F [RFunctorContractive F] [E : ElemG GF F] (γ : GName) (v : F.ap (IProp GF)) : IResUR GF :=
  fun τ' =>
    if H : τ' = E.τ then GenMap.singleton γ (H ▸ (unfoldi (E.bundle v)))
    else GenMap.empty

variable {GF F} [RFunctorContractive F] [E : ElemG GF F]

theorem iResUR_op_eval (c1 c2 : IResUR GF) : (c1 • c2) τ' γ' = (c1 τ' γ') • (c2 τ' γ') := by
  simp [CMRA.op, optionOp]

instance : OFE.NonExpansive (iSingleton F γ (GF := GF))  where
  ne {n x1 x2} H τ' γ' := by
    simp [iSingleton]
    split
    · rename_i h; subst h
      by_cases heq : γ' = γ
      · simp [heq, singleton_map_in]
        have h1 : E.bundle x1 ≡{n}≡ E.bundle x2 := NonExpansive.ne H
        have h2 : unfoldi (E.bundle x1) ≡{n}≡ unfoldi (E.bundle x2) := NonExpansive.ne h1
        exact h2
      · simp [singleton_map_ne heq]
    · rfl

theorem iSingleton_op (x y : F.ap (IProp GF)) : (iSingleton F γ x) • iSingleton F γ y ≡ iSingleton F γ (x • y) := by
  intro τ' γ'
  simp only [iSingleton]
  split
  · rename_i h; subst h
    simp only [CMRA.op, optionOp]
    by_cases heq : γ' = γ
    · subst heq
      simp only [iSingleton, ↓reduceDIte, singleton_map_in, some_eqv_some]
      apply ((RFunctor.map (fold GF) (unfold GF)).op _ _).symm.trans
      exact NonExpansive.eqv (bundle_op x y).symm
    · simp only [iSingleton, ↓reduceDIte, singleton_map_ne heq]
      rfl
  · rename_i h
    simp [iSingleton, h, CMRA.op, empty_map_lookup]

-- Helper lemmas for iSingleton validity and freedom properties

-- iSingleton is free at all keys except γ
theorem iSingleton_free_at_ne {γ : GName} {v : F.ap (IProp GF)} {γ' : GName} (h : γ' ≠ γ) :
    (iSingleton F γ v E.τ).car γ' = none := by
  simp [iSingleton]
  exact singleton_map_ne h

-- iSingleton at a single key has infinitely many free keys
theorem iSingleton_infinite_free {γ : GName} {v : F.ap (IProp GF)} :
    Infinite (IsFree (iSingleton F γ v E.τ).car) := by
  refine ⟨poke id γ, ?_, ?_⟩
  · intro n
    simp [IsFree, poke]
    split
    · rename_i h; exact iSingleton_free_at_ne (Nat.ne_of_lt h)
    · rename_i h; exact iSingleton_free_at_ne (Nat.ne_of_gt (Nat.lt_succ_of_le (Nat.ge_of_not_lt h)))
  · intro n m; simp [poke]; split <;> split <;> omega

-- iSingleton at τ' ≠ E.τ is the unit
theorem iSingleton_ne_eq_unit {γ : GName} {v : F.ap (IProp GF)} {τ' : GType} (h : τ' ≠ E.τ) :
    (iSingleton F γ v τ').car = (UCMRA.unit : GenMap Nat _).car := by
  funext γ'
  simp only [iSingleton, UCMRA.unit]
  split
  · rename_i heq; subst heq; contradiction
  · apply empty_map_lookup

-- Composing with iSingleton preserves freedom at keys ≠ γ
theorem iSingleton_op_ne_free {γ : GName} {v : F.ap (IProp GF)}
    {m : GenMap GName (GF.api E.τ (IPre GF))} {γ' : GName} (h_ne : γ' ≠ γ) (h_free : m.car γ' = none) :
    ((iSingleton F γ v E.τ) • m).car γ' = none := by
  simp [CMRA.op, optionOp, iSingleton, h_free]
  rw [singleton_map_ne h_ne]

-- Composing with iSingleton preserves infinite free keys
theorem iSingleton_op_isFree_infinite {γ : GName} {v : F.ap (IProp GF)}
    {m : GenMap GName (GF.api E.τ (IPre GF))} (h_inf : Infinite (IsFree m.car)) :
    Infinite (IsFree ((iSingleton F γ v E.τ) • m).car) := by
  rcases h_inf with ⟨enum, h_enum_free, h_enum_inj⟩
  by_cases h_gamma_in : ∃ n₀, enum n₀ = γ
  · -- If γ appears in enum, use poke to skip it
    rcases h_gamma_in with ⟨n₀, h_n₀⟩
    refine ⟨poke enum n₀, ?_, ?_⟩
    · intro n
      simp [poke]
      apply iSingleton_op_ne_free
      · split <;> intro H' <;> have _ := h_enum_inj (h_n₀ ▸ H') <;> omega
      · split <;> apply h_enum_free
    · intro n m h_eq; simp [poke] at h_eq
      split at h_eq <;> split at h_eq
      all_goals have _ := h_enum_inj h_eq; omega
  · -- If γ not in enum, all enumerated keys remain free
    refine ⟨enum, ?_, h_enum_inj⟩
    intro n; simp [IsFree]
    apply iSingleton_op_ne_free
    · intro heq; exact h_gamma_in ⟨n, heq⟩
    · exact h_enum_free

-- Helper lemma: unfoldi ∘ E.bundle preserves CoreId
theorem unfoldi_bundle_coreId {a : F.ap (IProp GF)} [CMRA.CoreId a] :
    CMRA.CoreId (unfoldi (E.bundle a)) := by
  constructor
  -- Strategy: Use that both bundle and RFunctor.map preserve pcore
  simp only [unfoldi, OFunctor.map]
  letI : RFunctor (GF E.τ).fst := (GF E.τ).snd.toRFunctor
  have bundle_coreId : CMRA.CoreId (E.bundle a) := by
    constructor
    calc CMRA.pcore (E.bundle a)
      ≡ (CMRA.pcore a).map E.bundle := by
          apply OFE.Equiv.symm
          apply OFE.transpAp_pcore_mp (E.transpMap (F.ap (IProp GF))).symm (E.transpClass (F.ap (IProp GF))).symm
      _ ≡ (some a).map E.bundle := by
        have : CMRA.pcore a ≡ some a := CMRA.CoreId.core_id
        rcases h : CMRA.pcore a with (_ | ca)
        · rw [h] at this; simp [] at this
        · rw [h] at this; simp [Option.map] at this ⊢
          exact OFE.NonExpansive.eqv this
      _ ≡ some (E.bundle a) := by simp [Option.map, OFE.Equiv.rfl]
  calc CMRA.pcore ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f (E.bundle a))
    ≡ (CMRA.pcore (E.bundle a)).map (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f :=
      (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).pcore (E.bundle a) |>.symm
    _ ≡ (some (E.bundle a)).map (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f := by
      have : CMRA.pcore (E.bundle a) ≡ some (E.bundle a) := bundle_coreId.core_id
      rcases h : CMRA.pcore (E.bundle a) with (_ | c)
      · rw [h] at this; simp [] at this
      · rw [h] at this; simp [Option.map] at this ⊢
        exact OFE.NonExpansive.eqv this
    _ ≡ some ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f (E.bundle a)) := by
      simp [Option.map, OFE.Equiv.rfl]

instance {a : F.ap (IProp GF)} [CMRA.CoreId a] : CMRA.CoreId (iSingleton F γ a) where
  core_id τ' γ' := by
    simp only [iSingleton, CMRA.core, CMRA.pcore, Option.getD, Option.map]
    split
    · rename_i h; subst h
      by_cases heq : γ' = γ
      · subst heq
        simp only [singleton_map_in, optionCore]
        unfold CMRA.pcore
        simp
        exact unfoldi_bundle_coreId.core_id
      · simp [singleton_map_ne heq]
    · rfl

theorem ElemG.bundle_validN {a : F.ap (IProp GF)} (H : ✓{n} a) :
  ✓{n} (E.bundle a) := by
  apply transpAp_validN_mp (E.transpMap <| F.ap (IProp GF)).symm (E.transpClass <| F.ap (IProp GF)).symm
  exact H

theorem ElemG.unbundle_validN {a : GF.api (ElemG.τ GF F) (IProp GF)} (H : ✓{n} a) :
  ✓{n} (E.unbundle a) := by
  apply transpAp_validN_mp (E.transpMap <| F.ap (IProp GF)) (E.transpClass <| F.ap (IProp GF))
  exact H

theorem IProp.unfoldi_bundle_validN {a : F.ap (IProp GF)} (Hv : ✓{n} a) :
    ✓{n} (IProp.unfoldi (E.bundle a)) :=
  unfoldi_validN _ (ElemG.bundle_validN Hv)

theorem IProp.unfoldi_bundle_unit {ε : F.ap (IProp GF)} [IsUnit ε] :
    IsUnit (IProp.unfoldi (E.bundle ε)) :=
  haveI : IsUnit (E.bundle ε) := ElemG.bundle_unit E
  IProp.unfoldi_unit

-- Auxiliary lemmas for iSingleton validity

/-- Extract the validity of the underlying element from a valid iSingleton. -/
theorem validN_of_iSingleton {a : F.ap (IProp GF)} (Hv : ✓{n} iSingleton F γ a) : ✓{n} a := by
  -- The singleton stores `unfoldi (E.bundle a)` at key γ in type E.τ
  have h_at_gamma : ✓{n} (((iSingleton F γ a) E.τ).car γ) := (Hv E.τ).1 γ
  simp [iSingleton, singleton_map_in] at h_at_gamma
  -- Reverse the transformations: foldi → unbundle → transpAp
  apply CMRA.validN_ne (ElemG.unbundle_bundle E a).dist
  apply ElemG.unbundle_validN
  apply CMRA.validN_ne (foldi_unfoldi (E.bundle a)).dist
  exact foldi_validN (unfoldi (E.bundle a)) h_at_gamma

/-- Build iSingleton validity at type E.τ from validity of the underlying element. -/
theorem iSingleton_validN_at_E_τ {a : F.ap (IProp GF)} (a_valid : ✓{n} a) :
    ✓{n} (iSingleton F γ a E.τ) := by
  refine ⟨fun γ' => ?_, ?_⟩
  · -- Pointwise validity
    simp [iSingleton]
    by_cases h_gamma : γ' = γ <;> simp [h_gamma, CMRA.ValidN, optionValidN, singleton_map_in]
    · exact IProp.unfoldi_bundle_validN a_valid
    · simp [singleton_map_ne h_gamma]
  · -- Infinite free keys (using poke to skip γ)
    refine ⟨poke id γ, ?_, ?_⟩
    · intro γ'; simp [IsFree, iSingleton, poke]
      have : ¬ (if γ' < γ then γ' else γ' + 1) = γ := by grind only [cases Or]
      simp [singleton_map_ne this]
    · intro _ _; simp [poke]; split <;> split <;> omega

/-- iSingleton validity at types τ' ≠ E.τ follows from unit validity. -/
theorem iSingleton_validN_at_ne {a : F.ap (IProp GF)} {τ' : GType} (h : τ' ≠ E.τ) :
    ✓{n} (iSingleton F γ a τ') := by
  simp [iSingleton, h]
  apply UCMRA.unit_valid.validN

theorem unfoldi_op {a b : GF.api (ElemG.τ GF F) (IProp GF)} :
  unfoldi.f (a • b) ≡ (unfoldi.f a • unfoldi.f b) := by
  refine (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).op a ?_

/-- Validity of bundled element composed with folded element. -/
theorem validN_bundle_op_foldi {a' : F.ap (IProp GF)} {v : GF.api E.τ (IPre GF)}
    (h : ✓{n} (a' • E.unbundle (foldi v))) :
    ✓{n} (unfoldi (E.bundle a') • v) := by
  -- Simplify using unfoldi_foldi
  have h_unfoldi_foldi := IProp.unfoldi_foldi v
  apply CMRA.validN_ne (h_unfoldi_foldi.op_r).dist
  apply CMRA.validN_ne unfoldi_op.dist
  apply IProp.unfoldi_validN
  have h_unbundle_bundle := ElemG.bundle_unbundle E (foldi v)
  apply CMRA.validN_ne (h_unbundle_bundle.op_r).dist
  apply CMRA.validN_ne (bundle_op _ _).dist
  apply ElemG.bundle_validN h

/-- Extract validity of `y` from `iSingleton F γ y • mf` when γ is free in mf. -/
theorem validN_of_iSingleton_op_free {mf : IResUR GF} {y : F.ap (IProp GF)}
    (Hv : ✓{n} iSingleton F γ y • mf) (Hfree : IsFree (mf E.τ).car γ) : ✓{n} y := by
  -- Extract validity at key γ from the composition
  have h_at_gamma : ✓{n} ((((iSingleton F γ y) • mf) E.τ).car γ) := (Hv E.τ).1 γ
  simp [IsFree] at Hfree
  simp [iSingleton, CMRA.op, Hfree, singleton_map_in] at h_at_gamma
  -- Reverse the transformations: foldi → unbundle → transpAp
  apply CMRA.validN_ne (ElemG.unbundle_bundle E y).dist
  apply ElemG.unbundle_validN
  apply CMRA.validN_ne (foldi_unfoldi (E.bundle y)).dist
  exact foldi_validN (unfoldi (E.bundle y)) h_at_gamma

/-- Extract validity of `mf` at type E.τ from `iSingleton F γ y • mf` when γ is free in mf. -/
theorem validN_mf_at_E_τ_of_iSingleton_op_free {mf : IResUR GF} {y : F.ap (IProp GF)}
    (Hv : ✓{n} iSingleton F γ y • mf) (Hfree : IsFree (mf E.τ).car γ) :
    ✓{n} (mf E.τ) := by
  simp [IsFree] at Hfree
  constructor
  · -- Pointwise validity
    intro γ'
    by_cases h_gamma : γ' = γ
    · simp [h_gamma, Hfree, CMRA.ValidN]
    · have h := (Hv E.τ).1 γ'
      simp [CMRA.op, iSingleton, singleton_map_ne h_gamma, optionOp] at h
      exact h
  · -- Infinite free keys: extract from composition
    rcases Hv E.τ with ⟨_, h_inf⟩
    apply Infinite.mono h_inf (fun k h_free => ?_)
    simp [IsFree, CMRA.op, iSingleton, optionOp] at h_free ⊢
    by_cases h_k : k = γ
    · simp_all [singleton_map_in]
    · simp_all [singleton_map_ne h_k]

/-- Extract validity of `mf` at types τ' ≠ E.τ from `iSingleton F γ y • mf`. -/
theorem validN_mf_at_ne_of_iSingleton_op {mf : IResUR GF} {y : F.ap (IProp GF)}
    (Hv : ✓{n} iSingleton F γ y • mf) {τ' : GType} (h : τ' ≠ E.τ) :
    ✓{n} (mf τ') := by
  have h_frame_valid := Hv τ'
  simp [CMRA.op, iSingleton, h, GenMap.empty] at h_frame_valid ⊢
  exact h_frame_valid

-- Helper: extract validity of element at key from frame
theorem extract_frame_validN {τ : GType} {n : Nat}
    {mz' : IResUR GF}
    (h_valid : ✓{n} (mz' τ).car)
    {γ : GName} {v : GF.api τ (IPre GF)} (h_at : (mz' τ).car γ = some v) :
    ✓{n} v := by
  have := h_valid γ
  simp [CMRA.ValidN, optionValidN, h_at] at this
  exact this

theorem iSingleton_op_validN_at_E {a : F.ap (IProp GF)} (Hv : ✓{n} mf) :
  ✓{n} (iSingleton F γ a • mf) (ElemG.τ GF F) →
  ✓{n} iSingleton F γ a • mf := by
  intros Hv_a τ'
  by_cases Heq : τ' = E.τ
  · subst τ'
    apply Hv_a
  · -- when [τ' ≠ E.τ] we have [iSingleton F γ a ≡ UCMRA.unit]
    refine CMRA.validN_ne (n := n) (x := mf τ') ?_ (Hv τ')
    simp only [CMRA.op, iSingleton_ne_eq_unit Heq]
    simp [UCMRA.unit, GenMap.empty, optionOp]

theorem iSingleton_op_validN_at_γ {a : F.ap (IProp GF)} (Hv : ✓{n} mf) :
    ✓{n} ((iSingleton F γ a • mf) (ElemG.τ GF F)).car γ →
    ✓{n} iSingleton F γ a • mf := by
  intros Hv_a
  apply iSingleton_op_validN_at_E Hv
  constructor
  · intros γ'
    by_cases h_key : γ' = γ
    · subst γ'; exact Hv_a
    · simp [CMRA.ValidN, CMRA.op, iSingleton, singleton_map_ne h_key]
      rcases h_at : (mf E.τ).car γ' with (⟨⟩ | v)
      · trivial
      · simp []; exact extract_frame_validN (Hv E.τ).1 h_at
  · apply iSingleton_op_isFree_infinite
    obtain ⟨_, H_inf⟩ := Hv E.τ
    apply H_inf

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
  refine ⟨iSingleton F γ ac • clos, Hclos.trans <| fun τ' γ' => ?_⟩
  refine .trans ?_ CMRA.op_assocN.symm
  rw [iResUR_op_eval]
  simp [iSingleton]
  split
  · rename_i h; rcases h with ⟨rfl, rfl⟩
    refine Dist.op_l ?_
    by_cases heq : γ' = γ
    · simp only [heq, singleton_map_in]
      apply some_dist_some.mpr
      apply Equiv.dist
      apply (NonExpansive.eqv (NonExpansive.eqv Hac)).trans
      apply (NonExpansive.eqv (bundle_op a2 ac)).trans
      exact (RFunctor.map (fold GF) (unfold GF)).op _ _
    · simp only [singleton_map_ne heq]
      simp only [CMRA.op, optionOp, Dist.rfl]
  · simp [empty_map_lookup]; apply Dist.op_l
    rfl

theorem iOwn_cmraValid {a : F.ap (IProp GF)} : iOwn γ a ⊢ UPred.cmraValid a :=
  (UPred.ownM_valid _).trans (UPred.valid_entails fun _ => validN_of_iSingleton)

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

theorem validN_iSingleton_op {mf : IResUR GF} {y} :
  ✓{n} mf →
  ✓{n} y →
  IsFree (mf (ElemG.τ GF F)).car γ →
  ✓{n} iSingleton F γ y • mf := by
  intro Hvalid_mf Hvalid H_free τ
  by_cases h : τ = E.τ
  · -- Case: τ = E.τ
    subst h
    -- Simplify to get GenMap.singleton composed with mf
    change ✓{n} ((iSingleton F γ y) E.τ • mf E.τ)
    simp [iSingleton]
    let v := unfoldi (E.bundle y)
    -- GenMap.singleton γ v • mf ≡ mf.alter γ v (since mf.car γ = none)
    have Hsingleton_comm := op_singleton_comm Nat _ v H_free
    apply Hsingleton_comm.dist.validN.mpr
    apply GenMap.alter_valid _ _ _ (Hvalid_mf E.τ)
    -- Show ✓{n} (some v) where v = unfoldi (E.bundle (f γ))
    apply IProp.unfoldi_validN _
    -- Show ✓{n} (E.bundle (f γ))
    have h_fun := E.transpMap <| F.ap (IProp GF)
    have h_inst := E.transpClass <| F.ap (IProp GF)
    apply OFE.transpAp_validN_mp h_fun.symm h_inst.symm
    exact Hvalid
  · -- Case: τ ≠ E.τ - iSingleton is unit here
    -- iSingleton τ = empty when τ ≠ E.τ
    simp only [iSingleton, dif_neg h, CMRA.op, GenMap.empty]
    -- Now we have (empty • mf τ) ≡{n}≡ mf τ, and need to show ✓{n} (empty • mf τ)
    apply Dist.validN (CMRA.unit_left_id_dist (mf τ)) |>.mpr
    apply Hvalid_mf

theorem iSingleton_op_validN_free {mf : IResUR GF} {y : F.ap (IProp GF)} :
  ✓{n} iSingleton F γ y • mf →
  IsFree (mf (ElemG.τ GF F)).car γ →
  ✓{n} y ∧ ✓{n} mf := by
  intros Hv Hfree
  constructor
  · -- Validity of y: use extraction lemma
    exact validN_of_iSingleton_op_free Hv Hfree
  · -- Validity of mf: case split on type
    intro τ'
    by_cases h_tau : τ' = E.τ
    · subst h_tau; exact validN_mf_at_E_τ_of_iSingleton_op_free Hv Hfree
    · exact validN_mf_at_ne_of_iSingleton_op Hv h_tau

theorem iSingleton_op_validN_notfree {mf : IResUR GF} {y : F.ap (IProp GF)} :
  ✓{n} iSingleton F γ y • mf →
  (mf (ElemG.τ GF F)).car γ = some v →
  ✓{n} (y • E.unbundle (IProp.foldi v)) := by
  intros Hv Hnfree
  have h_valid_at_tau : ✓{n} ((iSingleton F γ y • mf) E.τ) := Hv E.τ
  rcases h_valid_at_tau with ⟨h_pointwise, _⟩
  have h_at_gamma : ✓{n} ((((iSingleton F γ y) • mf) E.τ).car γ) := h_pointwise γ
  simp [iSingleton, CMRA.op, Hnfree, singleton_map_in]  at h_at_gamma
  apply CMRA.validN_ne (ElemG.unbundle_bundle E y).op_l.dist
  apply CMRA.validN_ne (unbundle_op (E.bundle y) (foldi.f v)).dist
  apply ElemG.unbundle_validN
  apply CMRA.validN_ne (foldi_unfoldi _).op_l.dist
  apply CMRA.validN_ne (foldi_op _ _).dist
  apply IProp.foldi_validN _ h_at_gamma

theorem IResUR.valid_exists_fresh {mf : IResUR GF} (Hv : ✓{n} mf) : ∃ a : Nat, (mf (ElemG.τ GF F)).car a = none := by
  simp [CMRA.ValidN] at Hv
  specialize Hv (ElemG.τ GF F)
  rcases Hv with ⟨_, e, He_inc, _⟩
  exact ⟨e 0, He_inc⟩

theorem alloc_update_unit {f : GName → F.ap (IProp GF)} :
  (∀ (γ : GName), ✓ f γ) ->
  UCMRA.unit ~~>: fun (y : IResUR GF) => ∃ γ, y = iSingleton F γ (f γ) := by
  intros Hf_valid
  apply UpdateP.total.mpr
  intros n mf Hvalid
  have : (UCMRA.unit • mf = mf) := by simp [CMRA.op, UCMRA.unit, GenMap.empty]
  rw [this] at Hvalid
  obtain ⟨γ, Hfresh⟩ := @IResUR.valid_exists_fresh GF F _ E n mf Hvalid
  refine ⟨iSingleton F γ (f γ), ⟨γ, rfl⟩, ?_⟩
  apply validN_iSingleton_op Hvalid (Hf_valid _).validN Hfresh

theorem iOwn_alloc_dep (f : GName → F.ap (IProp GF)) (Ha : ∀ γ, ✓ (f γ)) :
    ⊢ |==> ∃ γ, iOwn γ (f γ) := by
  unfold iOwn
  refine .trans (Q := iprop(|==> ∃ m, ⌜∃ γ, m = iSingleton F γ (f γ)⌝ ∧ UPred.ownM m)) ?_ (BIUpdate.mono ?_)
  · refine .trans (@UPred.ownM_unit (IResUR GF) _ iprop(emp)) ?_
    refine .trans intuitionistically_elim ?_
    apply UPred.bupd_ownM_updateP
    apply alloc_update_unit Ha
  · refine BI.exists_elim (fun m => BI.pure_elim_l (fun ⟨γ, Hm⟩ => ?_))
    subst Hm
    exact BI.exists_intro' γ .rfl

theorem iOwn_alloc (a : F.ap (IProp GF)) : ✓ a → ⊢ |==> ∃ γ, iOwn γ a :=
  fun Ha => iOwn_alloc_dep _ (fun _ => Ha)

theorem validN_iSingleton {a : F.ap (IProp GF)} :
  ✓{n} iSingleton F γ a ↔ ✓{n} a := by
  constructor
  · exact validN_of_iSingleton
  · intro a_valid τ'
    by_cases h_tau : τ' = E.τ
    · subst h_tau; exact iSingleton_validN_at_E_τ a_valid
    · exact iSingleton_validN_at_ne h_tau

theorem validN_iSingleton_op_notfree {mz' : IResUR GF} :
  ✓{n} iSingleton F γ a • mz' →
  (mz' (ElemG.τ GF F)).car γ = some v →
  ✓{n} a' • E.unbundle (foldi.f v) →
  ✓{n} (iSingleton F γ a' • mz') (ElemG.τ GF F) := by
  intros Hv Hnotfree Ha'_valid
  refine ⟨?_, ?_⟩
  · -- Pointwise validity
    intro γ'
    simp [CMRA.op]
    by_cases h_gamma : γ' = γ
    · -- At γ: use validN_bundle_op_foldi
      simp [h_gamma, iSingleton, Hnotfree, CMRA.ValidN, optionValidN, singleton_map_in]
      exact validN_bundle_op_foldi Ha'_valid
    · -- At γ' ≠ γ: extract from original composition
      have h_at_gamma' := (Hv E.τ).1 γ'
      simp [CMRA.op, iSingleton, singleton_map_ne h_gamma, optionOp] at h_at_gamma' ⊢
      exact h_at_gamma'
  · -- Infinite free keys: monotonicity from original composition
    obtain ⟨_, h_inf⟩ := Hv E.τ
    apply Infinite.mono h_inf
    intro k h_free
    by_cases h_k : k = γ
    · subst h_k; simp [IsFree, CMRA.op, iSingleton, singleton_map_in, Hnotfree] at h_free
    · simp [IsFree, CMRA.op, iSingleton, singleton_map_ne h_k] at h_free ⊢; exact h_free

theorem singleton_updateP {a : F.ap (IProp GF)} :
  (a ~~>: P) →
  iSingleton F γ a ~~>: fun y => ∃ a', y = iSingleton F γ a' ∧ P a' := by
  intro Hupd
  apply UpdateP.total.mpr
  intros n mf Hv
  cases h_mf_gamma : (mf E.τ).car γ with
  | none =>
    have ⟨a_valid, mz'_valid⟩ : ✓{n} a ∧ ✓{n} mf := iSingleton_op_validN_free Hv h_mf_gamma
    obtain ⟨a', Ha'_P, Ha'_valid : ✓{n} a'⟩ := Hupd n none (by simp [CMRA.op?]; exact a_valid)
    refine ⟨iSingleton F γ a', ⟨a', rfl, Ha'_P⟩, ?_⟩
    apply validN_iSingleton_op mz'_valid Ha'_valid h_mf_gamma
  | some v =>
    have a_valid : ✓{n} (a • E.unbundle (IProp.foldi v)) := iSingleton_op_validN_notfree Hv h_mf_gamma
    obtain ⟨a', Ha'_P, a'_valid : ✓{n} a' • _⟩ := Hupd n (some (E.unbundle (IProp.foldi v))) (by simp [CMRA.op?]; exact a_valid)
    refine ⟨iSingleton F γ a', ⟨a', rfl, Ha'_P⟩, ?_⟩
    intro τ'
    by_cases h_tau : τ' = E.τ
    · subst h_tau
      apply validN_iSingleton_op_notfree Hv h_mf_gamma a'_valid
    · -- if [τ' ≠ ElemG.τ GF F], then
      -- [✓{n} iSingleton F γ a • mf ↔ ✓{n} iSingleton F a' • mf]
      have h_frame_valid := Hv τ'
      simp [CMRA.op, iSingleton, h_tau] at h_frame_valid ⊢
      exact h_frame_valid

theorem iOwn_updateP {P γ a} (Hupd : a ~~>: P) : iOwn γ a ⊢ |==> ∃ a' : F.ap (IProp GF), ⌜P a'⌝ ∗ iOwn γ a' := by
  refine .trans (Q := iprop(|==> ∃ m, ⌜ ∃ a', m = (iSingleton F γ a') ∧ P a' ⌝ ∧ UPred.ownM m)) ?_ ?_
  · apply UPred.bupd_ownM_updateP
    apply singleton_updateP Hupd
  · refine BIUpdate.mono (BI.exists_elim (fun m => BI.pure_elim_l (fun ⟨a', Hm, HP⟩ => ?_)))
    subst Hm
    exact BI.exists_intro' a' (BI.persistent_entails_r (BI.pure_intro HP))

theorem iOwn_update {γ} {a a' : F.ap (IProp GF)} (Hupd : a ~~> a') : iOwn γ a ⊢ |==> iOwn γ a' := by
  apply (iOwn_updateP <| UpdateP.of_update Hupd).trans
  apply BIUpdate.mono
  refine BI.exists_elim (fun m => ?_)
  apply BI.pure_elim (a' = m) BI.sep_elim_l
  rintro rfl
  exact BI.sep_elim_r

theorem iOwn_unit {γ} {ε : F.ap (IProp GF)} [Hε : IsUnit ε] : ⊢ |==> iOwn γ ε := by
  unfold iOwn
  apply (UPred.ownM_unit _).trans
  apply BI.intuitionistically_elim.trans
  refine .trans (UPred.bupd_ownM_updateP UCMRA.unit (iSingleton F γ ε = ·) ?_) ?_
  · -- show UCMRA.unit ~~>: fun x => iSingleton F γ ε = x
    apply UpdateP.total.mpr
    intros n mf Hv
    refine ⟨iSingleton F γ ε, rfl, ?_⟩
    replace Hv := CMRA.validN_ne UCMRA.unit_left_id.dist Hv
    apply iSingleton_op_validN_at_γ Hv
    unfold iSingleton; simp [CMRA.ValidN, CMRA.op, singleton_map_in]
    -- case analysis on [γ ∈ (mf E.τ)]
    rcases h_at : (mf E.τ).car γ with (⟨⟩ | v) <;> simp []
    · exact IProp.unfoldi_bundle_validN Hε.unit_valid.validN
    · haveI h_unit : IsUnit (IProp.unfoldi (E.bundle ε)) := IProp.unfoldi_bundle_unit
      apply CMRA.validN_ne h_unit.unit_left_id.dist.symm
      apply extract_frame_validN (Hv E.τ).1 h_at

  · apply BIUpdate.mono
    refine BI.exists_elim (fun y => ?_)
    apply BI.pure_elim (iSingleton F γ ε = y) BI.and_elim_l
    rintro rfl
    exact BI.and_elim_r

end iOwn
end Iris
