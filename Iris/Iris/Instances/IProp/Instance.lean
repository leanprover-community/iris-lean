/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Zongyuan Liu, Remy Seassau
-/
module


public import Iris.BI
public import Iris.BI.BigOp
public import Iris.Algebra
public import Iris.Instances.UPred
public import Iris.ProofMode

@[expose] public section
namespace Iris

open COFE Std CMRA

/-- Apply an OFunctor at a fixed type -/
abbrev COFE.OFunctorPre.ap (F : OFunctorPre) (T : Type _) [COFE T] :=
  F T T

/-- Apply a list of OFunctors at a fixed type and index -/
abbrev BundledGFunctors.api (FF : BundledGFunctors) (τ : GType) (T : Type _) [COFE T] :=
  FF τ |>.fst |>.ap T

/-- Transport an OFunctorPre application along equality of the OFunctorPre.  -/
theorem transpAp {F1 F2 : OFunctorPre} (H : F1 = F2) {T} [COFE T] : F1.ap T = F2.ap T :=
  congrArg (OFunctorPre.ap · T) H

section TranspAp

variable [RF₁ : RFunctorContractive F₁] [RF₂ : RFunctorContractive F₂] [COFE T]

theorem OFE.transpAp_eqv_mp (h_fun : F₁ = F₂) (h_inst : HEq RF₁ RF₂) {x y : F₁.ap T} (H : x ≡{n}≡ y) :
    (transpAp h_fun).mp x ≡{n}≡ (transpAp h_fun).mp y := by
  cases h_fun; cases eq_of_heq h_inst; exact H

theorem OFE.transpAp_op_mp (h_fun : F₁ = F₂) (h_inst : HEq RF₁ RF₂) {x y : F₁ T T} :
    (transpAp h_fun).mp (x • y) = (transpAp h_fun).mp x • (transpAp h_fun).mp y := by
  cases h_fun; cases eq_of_heq h_inst; rfl

theorem OFE.transpAp_pcore_mp (h_fun : F₁ = F₂) (h_inst : HEq RF₁ RF₂) {x : F₁ T T} :
    (CMRA.pcore x).map (transpAp h_fun).mp = CMRA.pcore ((transpAp h_fun).mp x) := by
  cases h_fun; cases eq_of_heq h_inst
  show (CMRA.pcore x).map _ = CMRA.pcore x
  cases CMRA.pcore x <;> rfl

theorem OFE.transpAp_validN_mp (h_fun : F₁ = F₂) (h_inst : HEq RF₁ RF₂) {x : F₁ T T} (H : ✓{n} x) :
    ✓{n} ((transpAp h_fun).mp x) := by
  cases h_fun; cases eq_of_heq h_inst; exact H

theorem OFE.validN_transpAp_mp (h_fun : F₁ = F₂) (h_inst : HEq RF₁ RF₂) {x : F₁ T T}
    (H : ✓{n} ((transpAp h_fun).mp x)) : ✓{n} x := by
  cases h_fun; cases eq_of_heq h_inst; exact H

end TranspAp

section ElemG

/-- `ElemG` takes functors instead of CMRAs -/
@[rocq_alias inG]
class ElemG (FF : BundledGFunctors) (F : OFunctorPre) [RFunctorContractive F] where
  τ : GType
  transp : FF τ = ⟨F, ‹_›⟩

#rocq_ignore subG_inG "Superseded by Lean's direct `ElemG` typeclass synthesis."

open OFE

variable [I : RFunctorContractive F]

theorem ElemG.transpMap (E : ElemG GF F) T [OFE T] : (GF E.τ).fst = F :=
  Sigma.mk.inj E.transp |>.1

theorem ElemG.transpClass (E : ElemG GF F) T [OFE T] : (GF E.τ).snd ≍ I :=
  Sigma.mk.inj E.transp |>.2

def ElemG.bundle (E : ElemG GF F) [COFE T] : F.ap T → GF.api E.τ T :=
  transpAp (E.transpMap T) |>.mpr

def ElemG.unbundle (E : ElemG GF F) [COFE T] : GF.api E.τ T → F.ap T :=
  transpAp (E.transpMap T) |>.mp

theorem ElemG.bundle_unbundle (E : ElemG GF F) [COFE T] (x : GF.api E.τ T) :
    E.bundle (E.unbundle x) = x := by simp [bundle, unbundle]

theorem ElemG.unbundle_bundle (E : ElemG GF F) [COFE T] (x : F.ap T) :
    E.unbundle (E.bundle x) = x := by simp [bundle, unbundle]

instance ElemG.bundle.ne {E : ElemG GF F} [COFE T] :
    OFE.NonExpansive (E.bundle (T := T)) where
  ne {_ _ _} := OFE.transpAp_eqv_mp (E.transpMap T).symm (E.transpClass T).symm

instance ElemG.unbundle.ne {E : ElemG GF F} [COFE T] :
    OFE.NonExpansive (E.unbundle (T := T)) where
  ne {_ _ _} H := OFE.transpAp_eqv_mp (E.transpMap T) (E.transpClass T) H

omit I in
theorem ElemG.bundle_discreteE {GF : BundledGFunctors} [RFunctorContractive F] (E : ElemG GF F)
    {v : F.ap (IProp GF)} [DiscreteE v] : DiscreteE (E.bundle v) where
  discrete hz := (congrArg (E.bundle (T := IProp GF))
    (DiscreteE.discrete ((E.unbundle_bundle v).dist.symm.trans
      ((ElemG.unbundle.ne (T := IProp GF)).ne hz)))).trans (E.bundle_unbundle _)

theorem bundle_op {GF : BundledGFunctors} [E : ElemG GF F] (a2 ac : F.ap (IProp GF)) :
  E.bundle (a2 • ac) = E.bundle a2 • E.bundle ac := by
  apply Eq.symm
  apply Eq.trans (ElemG.bundle_unbundle E _).symm
  refine congrArg E.bundle ?_
  have h_fun := E.transpMap <| F.ap (IProp GF)
  have h_inst := E.transpClass <| F.ap (IProp GF)
  apply Eq.trans (transpAp_op_mp h_fun h_inst)
  apply (congrArg (CMRA.op · _) (ElemG.unbundle_bundle E a2)).trans
  apply congrArg (CMRA.op _ ·) (ElemG.unbundle_bundle E ac)

theorem unbundle_op {GF : BundledGFunctors} [E : ElemG GF F] (a2 ac : GF.api (ElemG.τ GF F) (IProp GF)) :
  E.unbundle (a2 • ac) = E.unbundle a2 • E.unbundle ac :=
  OFE.transpAp_op_mp (E.transpMap ((GF (ElemG.τ GF F)).fst.ap (IPre GF)))
    (E.transpClass ((GF (ElemG.τ GF F)).fst.ap (IPre GF)))

theorem ElemG.bundle_unit {GF F} [RFunctorContractive F] (E : ElemG GF F) {ε : F.ap (IProp GF)} [IsUnit ε] :
    IsUnit (E.bundle ε) := by
  refine { unit_valid := ?_, unit_left_id := ?_, pcore_unit := ?_ }
  · refine CMRA.valid_iff_validN.mpr fun n => ?_
    apply transpAp_validN_mp (E.transpMap <| F.ap (IProp GF)).symm (E.transpClass <| F.ap (IProp GF)).symm
    apply IsUnit.unit_valid.validN
  · intro x
    have h1 : E.unbundle (E.bundle ε • x) = E.unbundle x := by
      calc E.unbundle (E.bundle ε • x)
        _ = E.unbundle (E.bundle ε) • E.unbundle x :=
            transpAp_op_mp (E.transpMap <| F.ap (IProp GF)) (E.transpClass <| F.ap (IProp GF))
        _ = ε • E.unbundle x := congrArg (CMRA.op · _) (ElemG.unbundle_bundle E ε)
        _ = E.unbundle x := IsUnit.unit_left_id
    calc E.bundle ε • x
       = E.bundle (E.unbundle (E.bundle ε • x)) := (ElemG.bundle_unbundle E _).symm
     _ = E.bundle (E.unbundle x) := congrArg E.bundle h1
     _ = x := ElemG.bundle_unbundle E x
  · calc CMRA.pcore (E.bundle ε)
       = (CMRA.pcore ε).map E.bundle :=
             (transpAp_pcore_mp
               (E.transpMap <| F.ap (IProp GF)).symm
               (E.transpClass <| F.ap (IProp GF)).symm).symm
     _ = Option.map E.bundle (some ε) := by
        have h_pcore := ‹IsUnit ε›.pcore_unit
        rcases eqn : CMRA.pcore ε with (_ | c)
        · exact absurd (eqn ▸ h_pcore) OFE.not_none_eqv_some
        · simp only [Option.map]
          exact congrArg (fun z => some (E.bundle z)) (Option.some.inj (eqn ▸ h_pcore))
     _ = E.bundle ε := by rfl

end ElemG

section Fold

open Iris COFE UPred

variable {FF : BundledGFunctors}

/-- Isorecursive unfolding for each projection of FF. -/
@[rocq_alias inG_unfold]
def IProp.unfoldi : FF.api τ (IProp FF) -n> FF.api τ (IPre FF) :=
  OFunctor.map (IProp.fold FF) (IProp.unfold FF)

/-- Isorecursive folding for each projection of FF. -/
@[rocq_alias inG_fold]
def IProp.foldi : FF.api τ (IPre FF) -n> FF.api τ (IProp FF) :=
  OFunctor.map (IProp.unfold FF) (IProp.fold FF)

@[rocq_alias inG_unfold_fold]
theorem IProp.unfoldi_foldi (x : FF.api τ (IPre FF)) : unfoldi (foldi x) = x := by
  refine OFE.eq_dist.mpr fun n => ?_
  refine .trans (OFunctor.map_comp (F := FF τ |>.fst) ..).symm.dist ?_
  refine .trans ?_ (OFunctor.map_id (F := FF τ |>.fst) x).dist
  apply OFunctor.map_ne.ne <;> intro _ <;> simp [IProp.unfold, IProp.fold]

@[rocq_alias inG_fold_unfold]
theorem IProp.foldi_unfoldi (x : FF.api τ (IProp FF)) : foldi (unfoldi x) = x := by
  refine OFE.eq_dist.mpr fun n => ?_
  refine .trans (OFunctor.map_comp (F := FF τ |>.fst) ..).symm.dist ?_
  refine .trans ?_ (OFunctor.map_id (F := FF τ |>.fst) x).dist
  apply OFunctor.map_ne.ne <;> intro _ <;> simp [IProp.unfold, IProp.fold]

@[rocq_alias iProp_unfold_equivI]
theorem IProp.unfold_equivI (P Q : IProp FF) :
    (IProp.unfold FF P ≡ IProp.unfold FF Q) ⊢@{IProp FF} P ≡ Q := by
  have h := BI.internalEq.of_internalEquiv_ne (PROP := IProp FF) (IProp.fold FF)
    (x := IProp.unfold FF P) (y := IProp.unfold FF Q)
  rw [IProp.fold_unfold, IProp.fold_unfold] at h
  exact h

theorem IProp.unfoldi_discreteE {v : FF.api τ (IProp FF)} (hv : OFE.DiscreteE v) :
    OFE.DiscreteE (unfoldi.f v) where
  discrete h := (congrArg unfoldi.f (hv.discrete
    ((foldi_unfoldi v).dist.symm.trans (OFE.NonExpansive.ne h)))).trans (unfoldi_foldi _)

theorem IProp.foldi_op (x y : FF.api τ (IPre FF)) : foldi (x • y) = foldi x • foldi y :=
  (RFunctor.map (IProp.unfold FF) (IProp.fold FF) |>.op _ _)

theorem IProp.foldi_validN {n : Nat} (x : FF.api τ (IPre FF)) (H : ✓{n} x) : ✓{n} (foldi x) :=
  RFunctor.map (IProp.unfold FF) (IProp.fold FF) |>.validN H

theorem IProp.unfoldi_validN {n : Nat} (x : FF.api τ (IProp FF)) (H : ✓{n} x) : ✓{n} (unfoldi x) :=
  RFunctor.map (IProp.fold FF) (IProp.unfold FF) |>.validN H

theorem IProp.validN_foldi {n : Nat} (x : FF.api τ (IPre FF)) (H : ✓{n} (foldi x)) : ✓{n} x :=
  CMRA.validN_ne (IProp.unfoldi_foldi x).dist (IProp.unfoldi_validN _ H)

theorem IProp.validN_unfoldi_mp {n : Nat} (x : FF.api τ (IProp FF)) (H : ✓{n} (unfoldi x)) : ✓{n} x :=
  CMRA.validN_ne (IProp.foldi_unfoldi x).dist (IProp.foldi_validN _ H)

@[rocq_alias inG_unfold_validN]
theorem IProp.validN_unfoldi {n : Nat} (x : FF.api τ (IProp FF)) : ✓{n} (unfoldi x) ↔ ✓{n} x :=
  ⟨IProp.validN_unfoldi_mp x,IProp.unfoldi_validN x⟩

/-- unfoldi preserves unit structure -/
theorem IProp.unfoldi_unit {τ : GType} {x : FF.api τ (IProp FF)} [IsUnit x] :
    IsUnit (unfoldi x) := by
  refine { unit_valid := ?_, unit_left_id := ?_, pcore_unit := ?_ }
  · exact CMRA.valid_iff_validN.mpr fun n => IProp.unfoldi_validN x IsUnit.unit_valid.validN
  · intro y
    have h : foldi (unfoldi x • y) = foldi y := by
      calc foldi (unfoldi x • y)
        _ = foldi (unfoldi x) • foldi y := foldi_op _ _
        _ = x • foldi y := congrArg (CMRA.op · _) (foldi_unfoldi x)
        _ = foldi y := IsUnit.unit_left_id
    calc unfoldi x • y
      _ = unfoldi (foldi (unfoldi x • y)) := (IProp.unfoldi_foldi _).symm
      _ = unfoldi (foldi y) := congrArg unfoldi.f h
      _ = y := IProp.unfoldi_foldi y
  · letI : RFunctor (FF τ).fst := (FF τ).snd.toRFunctor
    calc CMRA.pcore (unfoldi.f x)
      _ = (CMRA.pcore x).map unfoldi.f :=
        ((RFunctor.map (IProp.fold FF) (IProp.unfold FF)).pcore x).symm
      _ = (some x).map unfoldi.f :=
        Option.map_forall₂ _ IsUnit.pcore_unit
      _ = some (unfoldi.f x) := by
        simp [Option.map]

end Fold

section iSingleton

open IProp OFE UPred GenMap

@[rocq_alias iRes_singleton]
def iSingleton {GF} F [RFunctorContractive F] [E : ElemG GF F] (γ : GName) (v : F.ap (IProp GF)) : IResUR GF :=
  fun τ' =>
    if H : τ' = E.τ then GenMap.singleton γ (H ▸ (unfoldi (E.bundle v)))
    else GenMap.empty

variable {GF F} [RFunctorContractive F] [E : ElemG GF F]

theorem iResUR_op_eval (c1 c2 : IResUR GF) : (c1 • c2) τ' γ' = (c1 τ' γ') • (c2 τ' γ') := by
  simp [CMRA.op, optionOp]

instance IResUR.lookup.ne {τ : GType} {γ : GName} :
    NonExpansive (fun r : IResUR GF => (r τ).car γ) where
  ne {_ _ _} H := H τ γ

instance ElemG.unbundle_foldi.ne :
    NonExpansive (fun v : GF.api E.τ (IPre GF) => E.unbundle (foldi v)) where
  ne {_ _ _} H := ElemG.unbundle.ne.ne (foldi.ne.ne H)

@[rocq_alias iRes_singleton_ne]
instance : OFE.NonExpansive (iSingleton F γ (GF := GF)) where
  ne {n x1 x2} H τ' γ' := by
    simp [iSingleton]
    split
    next h =>
      subst h
      by_cases heq : γ' = γ
      · simp [heq, singleton_map_in]; exact NonExpansive.ne (NonExpansive.ne H)
      · simp [singleton_map_none heq]
    next => rfl

@[rocq_alias iRes_singleton_op]
theorem iSingleton_op (x y : F.ap (IProp GF)) : (iSingleton F γ x) • iSingleton F γ y = iSingleton F γ (x • y) := by
  refine OFE.eq_dist.mpr fun n => ?_
  intro τ' γ'
  simp only [iSingleton]
  split
  next h =>
    subst h; simp only [CMRA.op, optionOp]
    by_cases heq : γ' = γ
    · subst heq
      simp only [iSingleton, ↓reduceDIte, GenMap.singleton_map_in, some_dist_some]
      exact (((RFunctor.map (fold GF) (unfold GF)).op _ _).symm.trans
        (congrArg (RFunctor.map (fold GF) (unfold GF)) (bundle_op x y).symm)).dist
    · simp only [iSingleton, ↓reduceDIte, singleton_map_none heq]; rfl
  next h => simp [iSingleton, h, CMRA.op, GenMap.empty_map_lookup]

theorem iSingleton_free_at_ne {γ : GName} {v : F.ap (IProp GF)} {γ' : GName} (h : γ' ≠ γ) :
    (iSingleton F γ v E.τ).car γ' = none := by
  simp [iSingleton]
  exact singleton_map_none h

theorem iSingleton_ne_eq_unit {γ : GName} {v : F.ap (IProp GF)} {τ' : GType} (h : τ' ≠ E.τ) :
    (iSingleton F γ v τ').car = (UCMRA.unit : GenMap _).car := by
  funext γ'; simp only [iSingleton, UCMRA.unit]
  split
  next heq => subst heq; contradiction
  next => apply GenMap.empty_map_lookup

theorem iSingleton_op_ne_free {γ : GName} {v : F.ap (IProp GF)}
    {m : GenMap (GF.api E.τ (IPre GF))} {γ' : GName} (h_ne : γ' ≠ γ) (h_free : m.car γ' = none) :
    ((iSingleton F γ v E.τ) • m).car γ' = none := by
  simp [CMRA.op, optionOp, iSingleton, h_free]
  rw [singleton_map_none h_ne]

theorem unfoldi_bundle_coreId {a : F.ap (IProp GF)} [CMRA.CoreId a] :
    CMRA.CoreId (unfoldi (E.bundle a)) := by
  constructor
  simp only [unfoldi, OFunctor.map]
  letI : RFunctor (GF E.τ).fst := (GF E.τ).snd.toRFunctor
  have bundle_coreId : CMRA.CoreId (E.bundle a) := by
    constructor
    calc CMRA.pcore (E.bundle a)
      = (CMRA.pcore a).map E.bundle :=
          (OFE.transpAp_pcore_mp (E.transpMap (F.ap (IProp GF))).symm (E.transpClass (F.ap (IProp GF))).symm).symm
    _ = (some a).map E.bundle := Option.map_forall₂ _ CMRA.CoreId.core_id
    _ = some (E.bundle a) := by rfl
  calc CMRA.pcore ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f (E.bundle a))
    = (CMRA.pcore (E.bundle a)).map (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f :=
      ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).pcore (E.bundle a)).symm
  _ = (some (E.bundle a)).map (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f :=
    Option.map_forall₂ _ bundle_coreId.core_id
  _ = some ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f (E.bundle a)) := by rfl

@[rocq_alias iRes_singleton_core_id]
instance {a : F.ap (IProp GF)} [CMRA.CoreId a] : CMRA.CoreId (iSingleton F γ a) where
  core_id := OFE.eq_dist.mpr fun n τ' γ' => by
    show CMRA.core ((iSingleton F γ a τ').car γ') ≡{n}≡ (iSingleton F γ a τ').car γ'
    simp only [iSingleton]
    split
    next h =>
      subst h
      by_cases heq : γ' = γ
      · subst heq
        simp only [GenMap.singleton_map_in, CMRA.core, optionCore, CMRA.pcore, Option.bind]
        exact unfoldi_bundle_coreId.core_id.dist
      · simp [singleton_map_none heq, CMRA.core, optionCore, CMRA.pcore]
    next => simp [GenMap.empty_map_lookup, CMRA.core, optionCore, CMRA.pcore]

theorem ElemG.bundle_validN {a : F.ap (IProp GF)} (H : ✓{n} a) :
    ✓{n} (E.bundle a) :=
  transpAp_validN_mp (E.transpMap <| F.ap (IProp GF)).symm (E.transpClass <| F.ap (IProp GF)).symm H

theorem ElemG.unbundle_validN {a : GF.api (ElemG.τ GF F) (IProp GF)} (H : ✓{n} a) :
    ✓{n} (E.unbundle a) :=
  transpAp_validN_mp (E.transpMap <| F.ap (IProp GF)) (E.transpClass <| F.ap (IProp GF)) H

theorem IProp.unfoldi_bundle_validN {a : F.ap (IProp GF)} (Hv : ✓{n} a) :
    ✓{n} (IProp.unfoldi (E.bundle a)) :=
  unfoldi_validN _ (ElemG.bundle_validN Hv)

theorem IProp.unfoldi_bundle_unit {ε : F.ap (IProp GF)} [IsUnit ε] :
    IsUnit (IProp.unfoldi (E.bundle ε)) :=
  letI : IsUnit (E.bundle ε) := ElemG.bundle_unit E
  IProp.unfoldi_unit

theorem validN_of_iSingleton {a : F.ap (IProp GF)} (Hv : ✓{n} iSingleton F γ a) : ✓{n} a := by
  have h_at_gamma : ✓{n} (((iSingleton F γ a) E.τ).car γ) := Hv E.τ γ
  simp [iSingleton, GenMap.singleton_map_in] at h_at_gamma
  apply CMRA.validN_ne (ElemG.unbundle_bundle E a).dist
  apply ElemG.unbundle_validN
  apply CMRA.validN_ne (foldi_unfoldi (E.bundle a)).dist
  exact foldi_validN (unfoldi (E.bundle a)) h_at_gamma

@[rocq_alias iRes_singleton_validI]
theorem iSingleton_cmraValid {a : F.ap (IProp GF)} :
    ✓ iSingleton F γ a ⊢@{IProp GF} ✓ a :=
  internalCmraValid_entails.mpr fun _ => validN_of_iSingleton

theorem iSingleton_validN_at_E_τ {a : F.ap (IProp GF)} (a_valid : ✓{n} a) :
    ✓{n} (iSingleton F γ a E.τ) := by
  intro γ'
  simp [iSingleton]
  by_cases h_gamma : γ' = γ <;> simp [h_gamma, CMRA.ValidN, optionValidN, GenMap.singleton_map_in]
  · exact IProp.unfoldi_bundle_validN a_valid
  · simp [singleton_map_none h_gamma]

theorem iSingleton_validN_at_ne {a : F.ap (IProp GF)} {τ' : GType} (h : τ' ≠ E.τ) :
    ✓{n} (iSingleton F γ a τ') := by
  simp [iSingleton, h]
  apply UCMRA.unit_valid.validN

theorem unfoldi_op {a b : GF.api (ElemG.τ GF F) (IProp GF)} :
  unfoldi.f (a • b) = (unfoldi.f a • unfoldi.f b) :=
  (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).op a b

theorem validN_bundle_op_foldi {a' : F.ap (IProp GF)} {v : GF.api E.τ (IPre GF)}
    (h : ✓{n} (a' • E.unbundle (foldi v))) :
    ✓{n} (unfoldi (E.bundle a') • v) := by
  have h_unfoldi_foldi := IProp.unfoldi_foldi v
  apply CMRA.validN_ne (congrArg (CMRA.op _ ·) h_unfoldi_foldi).dist
  apply CMRA.validN_ne unfoldi_op.dist
  apply IProp.unfoldi_validN
  have h_unbundle_bundle := ElemG.bundle_unbundle E (foldi v)
  apply CMRA.validN_ne (congrArg (CMRA.op _ ·) h_unbundle_bundle).dist
  apply CMRA.validN_ne (bundle_op _ _).dist
  apply ElemG.bundle_validN h

theorem validN_of_iSingleton_op_free {mf : IResUR GF} {y : F.ap (IProp GF)}
    (Hv : ✓{n} iSingleton F γ y • mf) (Hfree : IsFree (mf E.τ).car γ) : ✓{n} y := by
  have h_at_gamma : ✓{n} ((((iSingleton F γ y) • mf) E.τ).car γ) := Hv E.τ γ
  simp [IsFree] at Hfree
  simp [iSingleton, CMRA.op, Hfree, GenMap.singleton_map_in] at h_at_gamma
  apply CMRA.validN_ne (ElemG.unbundle_bundle E y).dist
  apply ElemG.unbundle_validN
  apply CMRA.validN_ne (foldi_unfoldi (E.bundle y)).dist
  exact foldi_validN (unfoldi (E.bundle y)) h_at_gamma

theorem validN_mf_at_E_τ_of_iSingleton_op_free {mf : IResUR GF} {y : F.ap (IProp GF)}
    (Hv : ✓{n} iSingleton F γ y • mf) (Hfree : IsFree (mf E.τ).car γ) :
    ✓{n} (mf E.τ) := by
  simp [IsFree] at Hfree
  intro γ'
  by_cases h_gamma : γ' = γ
  · simp [h_gamma, Hfree, CMRA.ValidN]
  · have h := Hv E.τ γ'
    simp [CMRA.op, iSingleton, singleton_map_none h_gamma, optionOp] at h
    exact h

theorem validN_mf_at_ne_of_iSingleton_op {mf : IResUR GF} {y : F.ap (IProp GF)}
    (Hv : ✓{n} iSingleton F γ y • mf) {τ' : GType} (h : τ' ≠ E.τ) :
    ✓{n} (mf τ') := by
  have h_frame_valid := Hv τ'
  simp [CMRA.op, iSingleton, h, GenMap.empty] at h_frame_valid ⊢
  exact h_frame_valid

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
  · refine CMRA.validN_ne (n := n) (x := mf τ') ?_ (Hv τ')
    simp only [CMRA.op, iSingleton_ne_eq_unit Heq]
    simp [UCMRA.unit, GenMap.empty, optionOp]

theorem iSingleton_op_validN_at_γ {a : F.ap (IProp GF)} (Hv : ✓{n} mf) :
    ✓{n} ((iSingleton F γ a • mf) (ElemG.τ GF F)).car γ →
    ✓{n} iSingleton F γ a • mf := by
  intros Hv_a
  apply iSingleton_op_validN_at_E Hv
  intro γ'
  by_cases h_key : γ' = γ
  · subst γ'; exact Hv_a
  · simp [CMRA.ValidN, CMRA.op, iSingleton, singleton_map_none h_key]
    rcases h_at : (mf E.τ).car γ' with (⟨⟩ | v)
    · trivial
    · simp; exact extract_frame_validN (Hv E.τ) h_at

@[rocq_alias iRes_singleton_discrete]
instance iSingleton_discreteE {v : F.ap (IProp GF)} [OFE.DiscreteE v] :
    OFE.DiscreteE (iSingleton F γ v) where
  discrete {w} H := by
    refine OFE.eq_dist.mpr fun n τ => ?_
    simp only [iSingleton] at ⊢
    split
    next h =>
      subst h; intro k; have Hk := (H E.τ) k
      simp only [iSingleton, ↓reduceDIte] at Hk
      by_cases hk : k = γ
      · subst hk
        rw [GenMap.singleton_map_in] at Hk ⊢
        rcases hw : (w E.τ).car k with _ | x <;> rw [hw] at Hk
        · exact Hk
        · refine some_dist_some.mpr (Eq.dist ?_)
          refine (congrArg unfoldi.f ?_).trans (IProp.unfoldi_foldi x)
          refine (congrArg E.bundle ?_).trans (ElemG.bundle_unbundle E _)
          refine OFE.DiscreteE.discrete ?_
          refine (ElemG.unbundle_bundle E v).dist.symm.trans ?_
          refine NonExpansive.ne <| (IProp.foldi_unfoldi _).dist.symm.trans (NonExpansive.ne Hk)
      · rw [GenMap.singleton_map_none hk] at Hk ⊢
        exact (Option.none_is_discrete.discrete Hk).dist
    next h =>
      intro k; have Hk := (H τ) k
      simp [iSingleton, dif_neg h, GenMap.empty_map_lookup] at Hk ⊢
      exact (Option.none_is_discrete.discrete Hk).dist

theorem iSingleton_eq_discreteFunSingleton {v : F.ap (IProp GF)} :
    iSingleton F γ v = discreteFunSingleton E.τ (GenMap.singleton γ (unfoldi (E.bundle v))) :=
  funext fun τ' => by
    by_cases h : τ' = E.τ
    · subst h; simp only [iSingleton, ↓reduceDIte, discreteFunSingleton_self]
    · simp only [iSingleton, h, ↓reduceDIte, discreteFunSingleton_of_ne _ (Ne.symm h)]
      rfl

theorem iSingleton_op_alter {r : IResUR GF} {v : GF.api E.τ (IPre GF)}
    (h : (r E.τ).car γ = some v) :
    iSingleton F γ (E.unbundle (foldi v)) • discreteFunInsert E.τ ((r E.τ).alter γ none) r = r := by
  rw [iSingleton_eq_discreteFunSingleton, ElemG.bundle_unbundle, IProp.unfoldi_foldi]
  exact discreteFunSingleton_op_insert (GenMap.singleton_op_alter_none _ h)

open BI in
@[rocq_alias later_internal_eq_iRes_singleton]
theorem later_internalEq_iSingleton {a : F.ap (IProp GF)} {r : IResUR GF} :
    ▷ (r ≡ iSingleton F γ a) ⊢@{IProp GF} ◇ ∃ b r', r ≡ iSingleton F γ b • r' ∧ ▷ (a ≡ b) := by
  refine (later_mono (internalEq.of_internalEquiv_ne fun r : IResUR GF => (r E.τ).car γ)).trans ?_
  rw [show (iSingleton F γ a E.τ).car γ = some (unfoldi (E.bundle a)) by
    simp [iSingleton, GenMap.singleton_map_in]]
  rcases hb : (r E.τ).car γ with _ | b
  · refine .trans (later_mono ?_) or_intro_l
    exact internalEq.symm.trans (option_some_none_equivI _).mp
  · rw [(option_some_equivI _ _).to_eq]
    refine .trans ?_ except0_intro
    refine exists_intro_trans (E.unbundle (foldi b)) ?_
    refine exists_intro_trans (discreteFunInsert E.τ ((r E.τ).alter γ none) r) ?_
    refine and_intro (internalEq.of_equiv (iSingleton_op_alter hb).symm) (later_mono ?_)
    refine .trans (internalEq.of_internalEquiv_ne fun v => E.unbundle (foldi v)) ?_
    rw [IProp.foldi_unfoldi, ElemG.unbundle_bundle]
    exact internalEq.symm

end iSingleton

@[rocq_alias own]
def iOwn {GF F} [RFunctorContractive F] [E : ElemG GF F] (γ : GName) (v : F.ap (IProp GF)) : IProp GF :=
  UPred.ownM <| iSingleton F γ v

#rocq_ignore own_def "`iOwn` is defined directly without `seal`/`unseal`."
#rocq_ignore own_aux "`iOwn` is defined directly without `seal`/`unseal`."
#rocq_ignore own_eq "`iOwn` is defined directly without `seal`/`unseal`."

section iOwn

open IProp OFE UPred BI GenMap ProofMode

variable {GF F} [RFunctorContractive F] [E : ElemG GF F]

@[rocq_alias own_ne]
instance iOwn_ne : NonExpansive (iOwn τ : F.ap (IProp GF) → IProp GF) where
  ne {n x1 x2} H := by unfold iOwn; exact NonExpansive.ne (NonExpansive.ne H)

#rocq_ignore own_proper "OFE is Leibniz; use equality"
#rocq_ignore own_mono' "Use iOwn_mono."

@[rocq_alias own_op]
theorem iOwn_op {a1 a2 : F.ap (IProp GF)} : iOwn γ (a1 • a2) ⊣⊢ iOwn γ a1 ∗ iOwn γ a2 := by
  unfold iOwn
  rw [← iSingleton_op]
  exact UPred.ownM_op _ _

@[rocq_alias own_mono]
theorem iOwn_mono {a1 a2 : F.ap (IProp GF)} (H : a2 ≼ a1) : iOwn γ a1 ⊢ iOwn γ a2 := by
  obtain ⟨c, rfl⟩ := H
  exact iOwn_op.mp.trans BI.sep_elim_left

@[rocq_alias own_valid]
theorem iOwn_cmraValid {a : F.ap (IProp GF)} : iOwn γ a ⊢ ✓ a :=
  (UPred.ownM_valid _).trans iSingleton_cmraValid

@[rocq_alias own_valid_2]
theorem iOwn_cmraValid_op {a1 a2 : F.ap (IProp GF)} :
    iOwn γ a1 ∗ iOwn γ a2 ⊢ ✓ (a1 • a2) :=
  iOwn_op.mpr.trans iOwn_cmraValid

@[rocq_alias own_valid_r]
theorem iOwn_valid_r {a : F.ap (IProp GF)} : iOwn γ a ⊢ iOwn γ a ∗ ✓ a :=
  BI.persistent_entails_left iOwn_cmraValid
@[rocq_alias own_valid_l]
theorem iOwn_valid_l {a : F.ap (IProp GF)} : iOwn γ a ⊢ ✓ a ∗ iOwn γ a :=
  BI.persistent_entails_right iOwn_cmraValid

@[rocq_alias own_core_persistent]
instance {a : F.ap (IProp GF)} [CMRA.CoreId a] : BI.Persistent (iOwn γ a) where
  persistent := by
    simp [iOwn]
    refine (UPred.persistently_ownM_core _).trans ?_
    refine persistently_mono ?_
    rw [CMRA.core_eqv_self]

@[rocq_alias own_timeless]
instance iOwn_timeless {a : F.ap (IProp GF)} [OFE.DiscreteE a] : BI.Timeless (iOwn γ a) :=
  _root_.UPred.ownM_timeless (iSingleton F γ a)

@[rocq_alias later_own]
theorem later_iOwn {a : F.ap (IProp GF)} : ▷ iOwn γ a ⊢ ◇ ∃ b, iOwn γ b ∧ ▷ (a ≡ b) := by
  unfold iOwn
  iintro Hlater
  icases UPred.later_ownM _ $$ Hlater with ⟨%r, Hown, Heq⟩
  imod (later_mono internalEq.symm).trans later_internalEq_iSingleton $$ Heq with ⟨%b, %r', Hr, Hab⟩
  irewrite [Hr] at Hown
  imodintro
  iexists b
  isplit
  · iapply UPred.ownM_mono (CMRA.inc_op_left _ r')
    iexact Hown
  · iexact Hab

theorem validN_iSingleton_op {mf : IResUR GF} {y} :
    ✓{n} mf →
    ✓{n} y →
    IsFree (mf (ElemG.τ GF F)).car γ →
    ✓{n} iSingleton F γ y • mf := by
  intro Hvalid_mf Hvalid H_free τ
  by_cases h : τ = E.τ
  · subst h
    change ✓{n} ((iSingleton F γ y) E.τ • mf E.τ)
    simp [iSingleton]
    apply op_singleton_comm _ (unfoldi.f (E.bundle y)) H_free |>.dist.validN.mpr
    exact GenMap.alter_valid _ (IProp.unfoldi_bundle_validN Hvalid) (Hvalid_mf E.τ)
  · show ✓{n} (iSingleton F γ y τ • mf τ)
    simp only [iSingleton, dif_neg h]
    exact Dist.validN (CMRA.unit_left_id_dist (n := n) (x := mf τ)) |>.mpr (Hvalid_mf τ)

theorem iSingleton_op_validN_free {mf : IResUR GF} {y : F.ap (IProp GF)} :
    ✓{n} iSingleton F γ y • mf →
    IsFree (mf (ElemG.τ GF F)).car γ →
    ✓{n} y ∧ ✓{n} mf := by
  intros Hv Hfree
  refine ⟨validN_of_iSingleton_op_free Hv Hfree, fun τ' => ?_⟩
  by_cases h_tau : τ' = E.τ
  · subst h_tau; exact validN_mf_at_E_τ_of_iSingleton_op_free Hv Hfree
  · exact validN_mf_at_ne_of_iSingleton_op Hv h_tau

theorem iSingleton_op_validN_notfree {mf : IResUR GF} {y : F.ap (IProp GF)} :
    ✓{n} iSingleton F γ y • mf →
    (mf (ElemG.τ GF F)).car γ = some v →
    ✓{n} (y • E.unbundle (IProp.foldi v)) := by
  intros Hv Hnfree
  have h_at_gamma : ✓{n} ((((iSingleton F γ y) • mf) E.τ).car γ) := Hv E.τ γ
  simp [iSingleton, CMRA.op, Hnfree, GenMap.singleton_map_in] at h_at_gamma
  apply CMRA.validN_ne (congrArg (CMRA.op · _) (ElemG.unbundle_bundle E y)).dist
  apply CMRA.validN_ne (unbundle_op (E.bundle y) (foldi.f v)).dist
  apply ElemG.unbundle_validN
  apply CMRA.validN_ne (congrArg (CMRA.op · _) (foldi_unfoldi _)).dist
  apply CMRA.validN_ne (foldi_op _ _).dist
  apply IProp.foldi_validN _ h_at_gamma

theorem IResUR.valid_exists_fresh {mf : IResUR GF} (_Hv : ✓{n} mf) : ∃ a : Nat, (mf (ElemG.τ GF F)).car a = none :=
  (mf (ElemG.τ GF F)).exists_fresh

theorem alloc_update_unit {f : GName → F.ap (IProp GF)} :
    (∀ (γ : GName), ✓ f γ) →
    UCMRA.unit ~~>: fun (y : IResUR GF) => ∃ γ, y = iSingleton F γ (f γ) := by
  intros Hf_valid
  apply UpdateP.total.mpr
  intros n mf Hvalid
  replace Hvalid : ✓{n} mf := CMRA.validN_ne UCMRA.unit_left_id.dist Hvalid
  obtain ⟨γ, Hfresh⟩ := @IResUR.valid_exists_fresh GF F _ E n mf Hvalid
  refine ⟨iSingleton F γ (f γ), ⟨γ, rfl⟩, ?_⟩
  apply validN_iSingleton_op Hvalid (Hf_valid _).validN Hfresh

@[rocq_alias own_alloc_dep]
theorem iOwn_alloc_dep (f : GName → F.ap (IProp GF)) (Ha : ∀ γ, ✓ (f γ)) :
    ⊢ |==> ∃ γ, iOwn γ (f γ) := by
  unfold iOwn
  refine .trans (Q := iprop(|==> ∃ m, ⌜∃ γ, m = iSingleton F γ (f γ)⌝ ∧ UPred.ownM m)) ?_ (BIUpdate.mono ?_)
  · refine .trans (@UPred.ownM_unit (IResUR GF) _ iprop(emp)) ?_
    refine .trans intuitionistically_elim ?_
    apply UPred.bupd_ownM_updateP
    apply alloc_update_unit Ha
  · refine BI.exists_elim (fun m => BI.pure_elim_left (fun ⟨γ, Hm⟩ => ?_))
    subst Hm
    exact BI.exists_intro_trans γ .rfl

@[rocq_alias own_alloc]
theorem iOwn_alloc (a : F.ap (IProp GF)) : ✓ a → ⊢ |==> ∃ γ, iOwn γ a :=
  fun Ha => iOwn_alloc_dep _ (fun _ => Ha)

/-- Allocation with a dependent function and a predicate on the ghost name.
The predicate P must be satisfied by arbitrarily large naturals. -/
@[rocq_alias own_alloc_strong_dep]
theorem iOwn_alloc_strong_dep (f : GName → F.ap (IProp GF)) (P : GName → Prop)
    (HP : ∀ N, ∃ k, N ≤ k ∧ P k)
    (Hf : ∀ γ, P γ → ✓ (f γ)) :
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ iOwn γ (f γ) := by
  unfold iOwn
  refine .trans (Q := iprop(|==> ∃ m, ⌜∃ γ, P γ ∧ m = iSingleton F γ (f γ)⌝ ∧ UPred.ownM m)) ?_ (BIUpdate.mono ?_)
  · refine .trans (@UPred.ownM_unit (IResUR GF) _ iprop(emp)) ?_
    refine .trans intuitionistically_elim ?_
    apply UPred.bupd_ownM_updateP
    apply UpdateP.total.mpr
    intros n mf Hvalid
    replace Hvalid : ✓{n} mf := CMRA.validN_ne UCMRA.unit_left_id.dist Hvalid
    obtain ⟨γ, Hfresh, HPγ⟩ := (mf (ElemG.τ GF F)).exists_fresh_sat HP
    refine ⟨iSingleton F γ (f γ), ⟨γ, HPγ, rfl⟩, ?_⟩
    apply validN_iSingleton_op Hvalid (Hf γ HPγ).validN Hfresh
  · refine BI.exists_elim (fun m => BI.pure_elim_left (fun ⟨γ, HPγ, Hm⟩ => ?_))
    subst Hm
    exact BI.exists_intro_trans γ (BI.persistent_entails_right (BI.pure_intro HPγ))

private theorem list_not_mem_of_gt_max (G : List Nat) (k : Nat) (hk : G.foldr max 0 < k) :
    k ∉ G := by
  intro hmem
  induction G with
  | nil => simp at hmem
  | cons x xs ih =>
    simp [List.foldr] at hk
    rcases List.mem_cons.mp hmem with rfl | hmem
    · omega
    · exact ih (by omega) hmem

private theorem list_fresh_above (G : List Nat) (N : Nat) :
    ∃ k, N ≤ k ∧ k ∉ G :=
  ⟨max N (G.foldr max 0 + 1), Nat.le_max_left ..,
    list_not_mem_of_gt_max G _ (by omega)⟩

@[rocq_alias own_alloc_cofinite_dep]
theorem iOwn_alloc_cofinite_dep (f : GName → F.ap (IProp GF)) (G : List GName)
    (Hf : ∀ γ, γ ∉ G → ✓ (f γ)) :
    ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ iOwn γ (f γ) :=
  iOwn_alloc_strong_dep f (· ∉ G) (list_fresh_above G) Hf

@[rocq_alias own_alloc_strong]
theorem iOwn_alloc_strong (a : F.ap (IProp GF)) (P : GName → Prop)
    (HP : ∀ N, ∃ k, N ≤ k ∧ P k) (Ha : ✓ a) :
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ iOwn γ a :=
  iOwn_alloc_strong_dep (fun _ => a) P HP (fun _ _ => Ha)

@[rocq_alias own_alloc_cofinite]
theorem iOwn_alloc_cofinite (a : F.ap (IProp GF)) (G : List GName) (Ha : ✓ a) :
    ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ iOwn γ a :=
  iOwn_alloc_cofinite_dep (fun _ => a) G (fun _ _ => Ha)

theorem validN_iSingleton {a : F.ap (IProp GF)} :
    ✓{n} iSingleton F γ a ↔ ✓{n} a := by
  refine ⟨validN_of_iSingleton, fun a_valid τ' => ?_⟩
  by_cases h_tau : τ' = E.τ
  · subst h_tau; exact iSingleton_validN_at_E_τ a_valid
  · exact iSingleton_validN_at_ne h_tau

theorem validN_iSingleton_op_notfree {mz' : IResUR GF} :
    ✓{n} iSingleton F γ a • mz' →
    (mz' (ElemG.τ GF F)).car γ = some v →
    ✓{n} a' • E.unbundle (foldi.f v) →
    ✓{n} (iSingleton F γ a' • mz') (ElemG.τ GF F) := by
  intros Hv Hnotfree Ha'_valid
  intro γ'
  simp [CMRA.op]
  by_cases h_gamma : γ' = γ
  · simp [h_gamma, iSingleton, Hnotfree, CMRA.ValidN, optionValidN, GenMap.singleton_map_in]
    exact validN_bundle_op_foldi Ha'_valid
  · have h_at_gamma' := Hv E.τ γ'
    simp [CMRA.op, iSingleton, singleton_map_none h_gamma, optionOp] at h_at_gamma' ⊢
    exact h_at_gamma'

theorem singleton_updateP {a : F.ap (IProp GF)} (Hupd : a ~~>: P) :
    iSingleton F γ a ~~>: fun y => ∃ a', y = iSingleton F γ a' ∧ P a' := by
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
    · have h_frame_valid := Hv τ'
      simp [CMRA.op, iSingleton, h_tau] at h_frame_valid ⊢
      exact h_frame_valid

@[rocq_alias own_updateP]
theorem iOwn_updateP {P γ a} (Hupd : a ~~>: P) : iOwn γ a ⊢ |==> ∃ a' : F.ap (IProp GF), ⌜P a'⌝ ∗ iOwn γ a' := by
  refine .trans (Q := iprop(|==> ∃ m, ⌜ ∃ a', m = (iSingleton F γ a') ∧ P a' ⌝ ∧ UPred.ownM m)) ?_ ?_
  · apply UPred.bupd_ownM_updateP
    apply singleton_updateP Hupd
  · refine BIUpdate.mono (BI.exists_elim (fun m => BI.pure_elim_left (fun ⟨a', Hm, HP⟩ => ?_)))
    subst Hm
    exact BI.exists_intro_trans a' (BI.persistent_entails_right (BI.pure_intro HP))

@[rocq_alias own_update]
theorem iOwn_update {γ} {a a' : F.ap (IProp GF)} (Hupd : a ~~> a') : iOwn γ a ⊢ |==> iOwn γ a' := by
  refine (iOwn_updateP <| UpdateP.of_update Hupd).trans (BIUpdate.mono ?_)
  iintro ⟨%m, %hm, Hown⟩
  subst hm
  iexact Hown

@[rocq_alias own_valid_3]
theorem iOwn_cmraValid_op_op {a1 a2 a3 : F.ap (IProp GF)} :
    iOwn γ a1 ∗ iOwn γ a2 ∗ iOwn γ a3 ⊢ UPred.cmraValid ((a1 • a2) • a3) :=
  BI.sep_assoc.symm.1.trans ((BI.sep_mono_left iOwn_op.mpr).trans iOwn_cmraValid_op)

@[rocq_alias own_update_2]
theorem iOwn_update_op {γ} {a1 a2 a' : F.ap (IProp GF)} (Hupd : a1 • a2 ~~> a') :
    iOwn γ a1 ∗ iOwn γ a2 ⊢ |==> iOwn γ a' :=
  iOwn_op.mpr.trans (iOwn_update Hupd)

@[rocq_alias own_update_3]
theorem iOwn_update_op_op {γ} {a1 a2 a3 a' : F.ap (IProp GF)} (Hupd : (a1 • a2) • a3 ~~> a') :
    iOwn γ a1 ∗ iOwn γ a2 ∗ iOwn γ a3 ⊢ |==> iOwn γ a' :=
  BI.sep_assoc.symm.1.trans ((BI.sep_mono_left iOwn_op.mpr).trans (iOwn_update_op Hupd))

@[rocq_alias own_unit]
theorem iOwn_unit {γ} {ε : F.ap (IProp GF)} [Hε : IsUnit ε] : ⊢ |==> iOwn γ ε := by
  unfold iOwn
  apply (UPred.ownM_unit _).trans
  apply BI.intuitionistically_elim.trans
  refine .trans (UPred.bupd_ownM_updateP UCMRA.unit (iSingleton F γ ε = ·) ?_) ?_
  · apply UpdateP.total.mpr
    intros n mf Hv
    refine ⟨iSingleton F γ ε, rfl, ?_⟩
    replace Hv := CMRA.validN_ne UCMRA.unit_left_id.dist Hv
    apply iSingleton_op_validN_at_γ Hv
    unfold iSingleton; simp [CMRA.ValidN, CMRA.op, GenMap.singleton_map_in]
    rcases h_at : (mf E.τ).car γ with (⟨⟩ | v) <;> simp
    · exact IProp.unfoldi_bundle_validN Hε.unit_valid.validN
    · have h_unit : IsUnit (IProp.unfoldi (E.bundle ε)) := IProp.unfoldi_bundle_unit
      apply CMRA.validN_ne h_unit.unit_left_id.dist.symm
      apply extract_frame_validN (Hv E.τ) h_at
  · refine BIUpdate.mono ?_
    iintro ⟨%y, %hy, Hown⟩
    subst hy
    iexact Hown

set_option synthInstance.checkSynthOrder false in
@[rocq_alias into_sep_own]
instance intoSep_own {γ} {a : F.ap (IProp GF)} [h : IsOp .split a b1 b2] :
    IntoSep (iOwn γ a) (iOwn γ b1) (iOwn γ b2) where
  into_sep := by rw [h.is_op]; exact iOwn_op.mp

set_option synthInstance.checkSynthOrder false in
@[rocq_alias into_and_own]
instance intoAnd_own {γ} {a b1 b2 : F.ap (IProp GF)} [h : IsOp .split a b1 b2] :
    IntoAnd false (iOwn γ a) (iOwn γ b1) (iOwn γ b2) where
  into_and := by
    rw [h.is_op]
    exact and_intro (iOwn_mono ⟨b2, rfl⟩) (iOwn_mono ⟨b1, CMRA.comm⟩)

set_option synthInstance.checkSynthOrder false in
@[rocq_alias from_sep_own]
instance fromSep_own {γ} {a b1 b2 : F.ap (IProp GF)} [h : IsOp .split a b1 b2] :
    FromSep (iOwn γ a) (iOwn γ b1) (iOwn γ b2) where
  from_sep := by rw [h.is_op]; exact iOwn_op.mpr

set_option synthInstance.checkSynthOrder false in
@[rocq_alias combine_sep_as_own]
instance combineSepAs_iOwn {γ} {a b1 b2 : F.ap (IProp GF)} [h : IsOp .merge a b1 b2] :
    CombineSepAs (iOwn γ b1) (iOwn γ b2) (iOwn γ a) where
  combine_sep_as := by rw [h.is_op]; exact iOwn_op.mpr

@[rocq_alias combine_sep_gives_own]
instance combineSepGives_iOwn {γ} {a1 a2 : F.ap (IProp GF)} :
    CombineSepGives (iOwn γ a1) (iOwn γ a2) iprop(✓ a1 • a2) where
  combine_sep_gives := iOwn_cmraValid_op

set_option synthInstance.checkSynthOrder false in
@[rocq_alias from_and_own_persistent]
instance fromAndOwn_persistent {γ} {a b1 b2 : F.ap (IProp GF)} [h : IsOp .split a b1 b2]
    [TCOr (CoreId b1) (CoreId b2)] : FromAnd (iOwn γ a) (iOwn γ b1) (iOwn γ b2) where
  from_and := by
    -- Infer from `CoreId b1` that `iOwn γ b1` is persistent, likewise for `b2`
    have _ : TCOr (Persistent (iOwn γ b1)) (Persistent (iOwn γ b2)) := by
      cases (inferInstance : TCOr (CoreId b1) (CoreId b2))
      · infer_instance
      · infer_instance
    calc
      _ ⊢ iOwn γ b1 ∗ iOwn γ b2 := persistent_and_sep_mp
      _ ⊢ iOwn γ (b1 • b2)      := iOwn_op.mpr
      _ ⊢ iOwn γ a              := by rw [h.is_op]

end iOwn

section big_op_instances

open IProp OFE UPred BI GenMap ProofMode Algebra Std
open scoped Iris.Std.PartialMap

variable {GF F} [URFunctorContractive F] [E : ElemG GF F]

@[rocq_alias own_cmra_sep_homomorphism]
instance iOwn_cmra_sep_homomorphism (γ : GName) :
    WeakMonoidHomomorphism (CMRA.op (α := F.ap (IProp GF))) sep
      UCMRA.unit iprop(emp) BiEntails (iOwn γ) where
  rel_refl := .rfl
  rel_trans := .trans
  op_proper aa' bb' := sep_congr aa' bb'
  map_ne := iOwn_ne
  map_op := iOwn_op

@[rocq_alias big_opL_own]
theorem bigOpL_iOwn {B : Type _} (γ : GName) (f : Nat → B → F.ap (IProp GF)) (l : List B) :
    l ≠ [] →
    iOwn γ ([^ CMRA.op list] k ↦ x ∈ l, f k x) ⊣⊢ [∗list] k ↦ x ∈ l, iOwn γ (f k x) :=
  BigOpL.bigOpL_hom_weak f

@[rocq_alias big_opM_own]
theorem bigOpM_iOwn {K : Type _} {M : Type _ → Type _} {B : Type _} [LawfulFiniteMap M K]
    [DecidableEq K] (γ : GName) (g : K → B → F.ap (IProp GF)) (m : M B) :
    ¬ m = (∅ : M B) →
    iOwn γ ([^ CMRA.op map] k ↦ x ∈ m, g k x) ⊣⊢ [∗map] k ↦ x ∈ m, iOwn γ (g k x) :=
  fun h => BigOpM.bigOpM_weak_hom g m (fun he => h he)

@[rocq_alias big_opS_own]
theorem bigOpS_iOwn {B : Type _} {S : Type _} [LawfulFiniteSet S B] (γ : GName)
    (g : B → F.ap (IProp GF)) (X : S) :
    X ≠ ∅ →
    iOwn γ ([^ CMRA.op set] x ∈ X, g x) ⊣⊢ [∗set] x ∈ X, iOwn γ (g x) :=
  BigOpS.hom_weak (iOwn_cmra_sep_homomorphism γ) g X

@[rocq_alias big_opMS_own]
theorem bigOpMS_iOwn {B : Type _} {MS : Type _} [LawfulFiniteMultiSet MS B] (γ : GName)
    (g : B → F.ap (IProp GF)) (X : MS) :
    X ≠ ∅ →
    iOwn γ ([^ CMRA.op mset] x ∈ X, g x) ⊣⊢ [∗mset] x ∈ X, iOwn γ (g x) :=
  BigOpMS.hom_weak (iOwn_cmra_sep_homomorphism γ) g X

@[rocq_alias own_cmra_sep_entails_homomorphism]
instance iOwn_cmra_sep_entails_homomorphism (γ : GName) :
    MonoidHomomorphism (CMRA.op (α := F.ap (IProp GF))) sep
      UCMRA.unit iprop(emp) Entails (iOwn γ) where
  rel_refl := .rfl
  rel_trans := .trans
  op_proper := sep_mono
  map_ne := iOwn_ne
  map_op := iOwn_op.mp
  map_unit := affine

@[rocq_alias big_opL_own_1]
theorem bigOpL_iOwn_entail {B : Type _} (γ : GName) (f : Nat → B → F.ap (IProp GF)) (l : List B) :
    iOwn γ ([^ CMRA.op list] k ↦ x ∈ l, f k x) ⊢ [∗list] k ↦ x ∈ l, iOwn γ (f k x) :=
  BigOpL.bigOpL_hom f l

@[rocq_alias big_opM_own_1]
theorem bigOpM_iOwn_entail {K : Type _} {M : Type _ → Type _} {B : Type _} [LawfulFiniteMap M K]
    (γ : GName) (g : K → B → F.ap (IProp GF)) (m : M B) :
    iOwn γ ([^ CMRA.op map] k ↦ x ∈ m, g k x) ⊢ [∗map] k ↦ x ∈ m, iOwn γ (g k x) :=
  BigOpM.bigOpM_hom g m

@[rocq_alias big_opS_own_1]
theorem bigOpS_iOwn_entail {B : Type _} {S : Type _} [LawfulFiniteSet S B] (γ : GName)
    (g : B → F.ap (IProp GF)) (X : S) :
    iOwn γ ([^ CMRA.op set] x ∈ X, g x) ⊢ [∗set] x ∈ X, iOwn γ (g x) :=
  BigOpS.hom (iOwn_cmra_sep_entails_homomorphism γ) g X

@[rocq_alias big_opMS_own_1]
theorem bigOpMS_iOwn_entail {B : Type _} {MS : Type _} [LawfulFiniteMultiSet MS B] (γ : GName)
    (g : B → F.ap (IProp GF)) (X : MS) :
    iOwn γ ([^ CMRA.op mset] x ∈ X, g x) ⊢ [∗mset] x ∈ X, iOwn γ (g x) :=
  BigOpMS.hom (iOwn_cmra_sep_entails_homomorphism γ) g X

end big_op_instances

section own_forall

open IProp OFE BI

@[rocq_alias iRes_project]
def iResProject {GF} F [RFunctorContractive F] [E : ElemG GF F] (γ : GName) (x : IResUR GF) :
    Option (F.ap (IProp GF)) :=
  ((x E.τ).car γ).map fun v => E.unbundle (foldi v)

variable {GF F} [RFunctorContractive F] [E : ElemG GF F]

@[rocq_alias iRes_project_op]
theorem iResProject_op (x y : IResUR GF) :
    iResProject F γ (x • y) = iResProject F γ x • iResProject F γ y := by
  simp only [iResProject, iResUR_op_eval]
  rcases (x E.τ).car γ with _ | x1 <;> rcases (y E.τ).car γ with _ | y1 <;>
    simp [CMRA.op, optionOp]
  rw [foldi_op, unbundle_op]

@[rocq_alias iRes_project_ne]
instance iResProject_ne : NonExpansive (iResProject F γ (GF := GF)) where
  ne {_ _ _} H := Option.map_ne (fun _ _ h => ElemG.unbundle.ne.ne (foldi.ne.ne h)) (H E.τ γ)

@[rocq_alias iRes_project_singleton]
theorem iResProject_iSingleton (a : F.ap (IProp GF)) :
    iResProject F γ (iSingleton F γ a) = some a := by
  simp [iResProject, iSingleton, GenMap.singleton_map_in, foldi_unfoldi, ElemG.unbundle_bundle]

@[rocq_alias iRes_project_below]
theorem iResProject_below {z : IResUR GF} {c : F.ap (IProp GF)}
    (h : iResProject F γ z = some c) : iSingleton F γ c ≼ z := by
  simp only [iResProject, Option.map_eq_some_iff] at h
  obtain ⟨v, hv, rfl⟩ := h
  exact ⟨_, (iSingleton_op_alter hv).symm⟩

@[rocq_alias iRes_project_above]
theorem iResProject_above {z : IResUR GF} {c : F.ap (IProp GF)} :
    iSingleton F γ c ≼ z ⊢@{IProp GF} some c ≼ iResProject F γ z := by
  refine (internalCmraIncluded_map (iResProject F γ) iResProject_op).trans ?_
  rw [iResProject_iSingleton]

/-- Nothing is owned at `γ` when the projection there is `none`. -/
theorem iResProject_none_incl_false {z : IResUR GF} (a : F.ap (IProp GF))
    (hz : iResProject F γ z = none) : iSingleton F γ a ≼ z ⊢@{IProp GF} False := by
  refine iResProject_above.trans ?_
  rw [hz]
  exact option_includedI.mp

@[rocq_alias own_forall]
theorem iOwn_forall {B : Type _} [hB : Inhabited B] (γ : GName) (f : B → F.ap (IProp GF)) :
    (∀ b, iOwn γ (f b)) ⊢ ∃ c, iOwn γ c ∗ ∀ b, some (f b) ≼ some c := by
  have hforall : (∀ b, UPred.ownM (iSingleton F γ (f b))) ⊢@{IProp GF}
      ∃ z, UPred.ownM z ∧ ∀ b, iSingleton F γ (f b) ≼ z :=
    (UPred.ownM_forall _).trans <|
      exists_mono fun _ => and_mono_right (forall_mono fun _ => siPure_exist.mpr)
  unfold iOwn
  iintro Hown
  icases hforall $$ Hown with ⟨%z, Hown, #Hincl⟩
  rcases hc : iResProject F γ z with _ | c
  · iexfalso
    iapply iResProject_none_incl_false (f default) hc
    iexact Hincl
  · iexists c
    isplitl [Hown]
    · iapply UPred.ownM_mono (iResProject_below hc)
      iexact Hown
    · iintro %b
      rw [← hc]
      iapply iResProject_above
      iexact Hincl

@[rocq_alias own_forall_total]
theorem iOwn_forall_total [CMRA.IsTotal (F.ap (IProp GF))] {B : Type _} [Inhabited B]
    (γ : GName) (f : B → F.ap (IProp GF)) :
    (∀ b, iOwn γ (f b)) ⊢ ∃ c, iOwn γ c ∗ ∀ b, f b ≼ c :=
  (iOwn_forall γ f).trans <|
    exists_mono fun _ => sep_mono_right (forall_mono fun _ => Some_included_totalI.mp)

@[rocq_alias own_and]
theorem iOwn_and {a1 a2 : F.ap (IProp GF)} :
    (iOwn γ a1 ∧ iOwn γ a2) ⊢ ∃ c, iOwn γ c ∗ some a1 ≼ some c ∗ some a2 ≼ some c := by
  refine and_forall_ite.mp.trans ?_
  refine (forall_mono fun b => ?_).trans
    ((iOwn_forall γ fun b : Bool => if b then a1 else a2).trans ?_)
  · cases b <;> exact .rfl
  · refine exists_mono fun _ => sep_mono_right ?_
    exact (and_intro (forall_elim true) (forall_elim false)).trans persistent_and_sep_mp

@[rocq_alias own_and_total]
theorem iOwn_and_total [CMRA.IsTotal (F.ap (IProp GF))] {a1 a2 : F.ap (IProp GF)} :
    (iOwn γ a1 ∧ iOwn γ a2) ⊢ ∃ c, iOwn γ c ∗ a1 ≼ c ∗ a2 ≼ c :=
  iOwn_and.trans <| exists_mono fun _ =>
    sep_mono_right (sep_mono Some_included_totalI.mp Some_included_totalI.mp)

@[rocq_alias own_forall_pred]
theorem iOwn_forall_pred {B : Type _} (γ : GName) (φ : B → Prop) (f : B → F.ap (IProp GF))
    (h : ∃ b, φ b) :
    (∀ b, ⌜φ b⌝ -∗ iOwn γ (f b)) ⊢ ∃ c, iOwn γ c ∗ ∀ b, ⌜φ b⌝ -∗ some (f b) ≼ some c := by
  obtain ⟨b₀, hb₀⟩ := h
  iintro Hown
  ihave ⟨%c, Hown, #Hincl⟩ :=
    iOwn_forall (hB := ⟨⟨b₀, hb₀⟩⟩) γ (fun b : Subtype φ => f b.val) $$ [Hown]
  · iintro %b
    iapply Hown
    ipureintro
    exact b.property
  · iexists c
    isplitl [Hown]
    · iexact Hown
    · iintro %b %hb
      iapply Hincl $$ %(⟨b, hb⟩ : Subtype φ)

@[rocq_alias own_forall_pred_total]
theorem iOwn_forall_pred_total [CMRA.IsTotal (F.ap (IProp GF))] {B : Type _} (γ : GName)
    (φ : B → Prop) (f : B → F.ap (IProp GF)) (h : ∃ b, φ b) :
    (∀ b, ⌜φ b⌝ -∗ iOwn γ (f b)) ⊢ ∃ c, iOwn γ c ∗ ∀ b, ⌜φ b⌝ -∗ f b ≼ c :=
  (iOwn_forall_pred γ φ f h).trans <| exists_mono fun _ =>
    sep_mono_right (forall_mono fun _ => wand_mono_right Some_included_totalI.mp)

@[rocq_alias own_and_discrete_total]
theorem iOwn_and_discrete_total [CMRA.Discrete (F.ap (IProp GF))]
    [CMRA.IsTotal (F.ap (IProp GF))] {a1 a2 c : F.ap (IProp GF)}
    (h : ∀ c', ✓ c' → a1 ≼ c' → a2 ≼ c' → c ≼ c') :
    (iOwn γ a1 ∧ iOwn γ a2) ⊢ iOwn γ c := by
  iintro Hown
  icases iOwn_and_total $$ Hown with ⟨%c', Hown, %Ha1, %Ha2⟩
  ihave %hv := iOwn_cmraValid $$ Hown
  iapply iOwn_mono (h c' hv Ha1 Ha2)
  iexact Hown

@[rocq_alias own_and_discrete_total_False]
theorem iOwn_and_discrete_total_false [CMRA.Discrete (F.ap (IProp GF))]
    [CMRA.IsTotal (F.ap (IProp GF))] {a1 a2 : F.ap (IProp GF)}
    (h : ∀ c', ✓ c' → a1 ≼ c' → a2 ≼ c' → False) :
    (iOwn γ a1 ∧ iOwn γ a2) ⊢ False := by
  iintro Hown
  icases iOwn_and_total $$ Hown with ⟨%c', Hown, %Ha1, %Ha2⟩
  ihave %hv := iOwn_cmraValid $$ Hown
  exact (h c' hv Ha1 Ha2).elim

end own_forall

end Iris
