/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE
import Iris.Algebra.UPred
import Iris.Algebra.COFESolver
import Init.Data.Vector

namespace Iris

-- MARKUSDE: The number of types of ghost state being finite is not necessary
-- for any of the ghost state constructions so we can remove it and simplify
-- the types.

/-- GType: Each type of ghost state in the global context of ghost states is
referenced by its index (GType) in a GFunctors list. -/
abbrev GType := Nat

def GFunctors := GType → COFE.OFunctorPre

-- MARKUSDE: Abbreviation so synthesis of IsGFunctors works
abbrev GFunctors.default : GFunctors := fun _ => COFE.constOF Unit

def GFunctors.set (GF : GFunctors) (i : Nat) (F : COFE.OFunctorPre) : GFunctors :=
  fun j => if j == i then F else GF j

abbrev IsGFunctors (G : GFunctors) := ∀ i, RFunctorContractive (G i)

instance [IsGFunctors GF] [RFunctorContractive F] : IsGFunctors (GF.set i F) :=
  fun _ => by unfold GFunctors.set; split <;> infer_instance

def SubG (FF₁ FF₂ : GFunctors) : Prop := ∀ i, ∃ j, FF₁ i = FF₂ j


/-- GName: Ghost variable name. In iProp, there are an unlimited amount of names for
each GType .-/
abbrev GName := Nat

abbrev IResF (FF : GFunctors) : COFE.OFunctorPre :=
  DiscreteFunOF (fun i => GenMapOF GName (FF i))

section IProp
open COFE

variable (FF : GFunctors) [IsGFunctors FF]

def iPrePropO : Type _ := OFunctor.Fix (UPredOF (IResF FF))

instance : COFE (iPrePropO FF) := inferInstanceAs (COFE (OFunctor.Fix _))

def IResUR : Type := (i : GType) → GName → Option (FF i (iPrePropO FF) (iPrePropO FF))

instance : UCMRA (IResUR FF) :=
  ucmraDiscreteFunO (β := fun (i : GType) => GName → Option (FF i (iPrePropO FF) (iPrePropO FF)))

abbrev IProp := UPred (IResUR FF)








end IProp


class InG (FF : GFunctors) [IsGFunctors FF] (A : Type _) where
  typ : GType
  lookup : A = FF typ (iPrePropO FF) (iPrePropO FF) := by rfl

instance : InG GFunctors.default Unit where typ := 0

def ap (F : COFE.OFunctorPre) (T : Type _) [OFE T] := F T T

-- #check Iris.COFE.OFunctor.Fix.unfold

-- nonrec def InG.unfold (FF : GFunctors) [IsGFunctors FF] [I : InG FF A] :=
--     -- (FF I.typ (IProp FF) (IProp FF)) -n> (FF I.typ (iPrePropO FF) (iPrePropO FF)) :=
--   (COFE.OFunctor.map (Iris.COFE.OFunctor.Fix.unfold (F := FF I.typ)) _)
-- -- (Iris.COFE.OFunctor.Fix.fold)

def OwnR (FF : GFunctors) [IsGFunctors FF] [I : InG FF A] (a : A) : IResUR FF :=
  fun τ' _ => if H : τ' = I.typ then H▸I.lookup |>.mp a else none

-- Issue: Not necessarily true that the CMRA instance for B is the same as the tranasport
-- of the CMRA instance for A.
-- Solutions: Bundle CMRA instance in GFunctors & add constraint to InG
-- Internalize CMRA data?
-- theorem CMRA.Valid_transport {A B : Type _} [CMRA A] [CMRA B] {a : A} {b : B}
--     (H : A = B) : (✓ a) = (✓ (H ▸ a)) := by
--   subst H
--   congr 1
--   sorry

section OwnR

/-
variable (FF : GFunctors) [IsGFunctors FF]

theorem valid_iff [CMRA A] [InG FF A] (a : A) : ✓ a ↔ ✓ (OwnR FF γ a) := by
  refine ⟨fun Hv τ' γ' => ?_, ?_⟩
  · simp only [CMRA.Valid, optionValid, OwnR]
    split <;> try trivial
    rename_i x y He; revert He
    split
    · rintro ⟨H⟩
      sorry
    · rintro ⟨⟩
  · sorry
-/
end OwnR

attribute [irreducible] OwnR -- OwnR should be manipulated using equations only


/-
noncomputable section DynCMRA

universe u

open Classical

-- CMRA which we can choose at the point where it is allocated
inductive Dyn : Type (u+1) where
| bundled (T : Type u) (C : CMRA T) (v : T)
| invalid

@[simp] def Dyn.Equiv : Dyn → Dyn → Prop
| .invalid, .invalid => True
| .bundled T1 C1 v1, .bundled T2 C2 v2 =>
    if h : T1 = T2 then if C1 = h ▸ C2 then C1.toOFE.Equiv v1 (h ▸ v2) else False else False
| _, _ => False

@[simp] def Dyn.Dist (n : Nat) : Dyn → Dyn → Prop
| .invalid, .invalid => True
| .bundled T1 C1 v1, .bundled T2 C2 v2 =>
    if h : T1 = T2 then if C1 = h ▸ C2 then C1.toOFE.Dist n v1 (h ▸ v2) else False else False
| _, _ => False

theorem Dyn.dist_eqv {n} : Equivalence (Dyn.Dist n) where
  refl x := by cases x <;> simp [Dist]
  symm {x y} := by
    cases x <;> cases y <;> simp [Dist]
    rintro rfl rfl H
    refine ⟨rfl, rfl, H.symm⟩
  trans {x y z} := by
    cases x <;> cases y <;> cases z <;> simp [Dist]
    rintro rfl rfl H1 rfl rfl H2
    refine ⟨rfl, rfl, H1.trans H2⟩

-- def X : CMRA Unit := by infer_instance
-- def Y : CMRA Unit := by infer_instance
-- example : X = Y := rfl

-- example : ∀ (x y : A) (H1 H2 : x = y), H1 = H2 := by intros _ _ _ _; rfl

theorem Dyn.equiv_dist {x y : Dyn} : x.Equiv y ↔ ∀ (n : Nat), Dyn.Dist n x y := by
  rcases x <;> rcases y <;> simp [Dist]
  refine ⟨?_, ?_⟩
  · rintro ⟨rfl, rfl, H⟩  _
    refine ⟨rfl, rfl, OFE.Equiv.dist H⟩
  · rintro H
    rename_i T1 C1 v1 T2 C2 v2
    obtain ⟨Heq, HCeq, _⟩ := H 0
    refine ⟨Heq, HCeq, ?_⟩
    refine C1.equiv_dist.mpr (fun n => ?_)
    obtain ⟨_, _, _⟩ := H n
    trivial

theorem Dyn.dist_lt {n} {x y : Dyn} {m} : Dyn.Dist n x y → m < n → Dyn.Dist m x y := by
  rcases x <;> rcases y <;> simp [Dist]
  rintro rfl rfl H Hlt
  refine ⟨rfl, rfl, ?_⟩
  exact OFE.Dist.lt H Hlt

instance : OFE Dyn where
  Equiv := Dyn.Equiv
  Dist := Dyn.Dist
  dist_eqv := Dyn.dist_eqv
  equiv_dist := Dyn.equiv_dist
  dist_lt := Dyn.dist_lt

@[simp] def Dyn.pcore : Dyn → Option Dyn
| .bundled T C v => C.pcore v |>.map (.bundled T C ·)
| .invalid => none

@[simp] def Dyn.op : Dyn → Dyn → Dyn
| .bundled T1 C1 v1, .bundled T2 C2 v2 =>
  if h : T1 = T2 then if C1 = h ▸ C2 then .bundled T1 C1 (C1.op v1 (h▸v2)) else invalid else invalid
| _, _ => .invalid

@[simp] def Dyn.ValidN (n : Nat) : Dyn → Prop
| .bundled _ C1 v1 => C1.ValidN n v1
| .invalid => False

@[simp] def Dyn.Valid : Dyn → Prop
| .bundled _ C1 v1 => C1.Valid v1
| .invalid => False

theorem Dyn.op_ne {x : Dyn} : OFE.NonExpansive x.op where
  ne n x1 x2 := by
    rcases x with (⟨T1, C1, v1⟩|_) <;> rcases x1 with (⟨T2, C2, v2⟩|_) <;>
      rcases x2 with (⟨T3, C3, v3⟩|_) <;> simp [OFE.Dist]
    rintro HEt HEc He
    rcases em (T1 = T2) with (h1|h1) <;> simp [h1]
    · have HEt' := HEt
      subst HEt
      rcases em (C1 = h1 ▸ C2)  with (h2|h2) <;> simp [h2]
      · rcases em (C2 = C3) with (h3|h3) <;> simp_all
        -- have X := C1.op_ne (x := v1) |>.ne (n := n) (x₁ := h1 ▸ v2) (x₂ := v3)
        sorry
      · sorry
    · sorry
    -- all_goals rcases em (T2 = T3) with (h2|h2) <;> simp [h2]

instance : CMRA Dyn where
  pcore := Dyn.pcore
  op := Dyn.op
  ValidN := Dyn.ValidN
  Valid := Dyn.Valid
  op_ne := sorry
  pcore_ne := sorry
  validN_ne := sorry
  valid_iff_validN := sorry
  validN_succ := sorry
  validN_op_left := sorry
  assoc := sorry
  comm := sorry
  pcore_op_left := sorry
  pcore_idem := sorry
  pcore_op_mono := sorry
  extend := sorry

end DynCMRA
-/



end Iris
