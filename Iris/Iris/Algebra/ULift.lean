/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.Updates

/-! # Cameras on `ULift`

`ULift α` inherits the camera structure of `α`. This is used to lift ghost state living in `Type`
(e.g. masks) to the universe of the resources of `IProp`, which for step-index types in higher
universes (e.g. ordinals) is not `Type`.
-/

@[expose] public section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris

open OFE CMRA

instance ULift.instCMRA [CMRA α] : CMRA (ULift α) where
  pcore x := (pcore x.down).map ULift.up
  op x y := ⟨x.down • y.down⟩
  ValidN n x := ✓{n} x.down
  Valid x := ✓ x.down
  op_ne {x} := ⟨fun _ _ _ h => (op_ne (x := x.down)).ne h⟩
  pcore_ne {n x y cx} h e := by
    cases hx : pcore x.down with
    | none => simp [hx] at e
    | some cx' =>
      simp only [hx, Option.map_some, Option.some.injEq] at e
      subst e
      obtain ⟨cy, hy, hc⟩ := pcore_ne (x := x.down) h hx
      exact ⟨⟨cy⟩, by simp [hy], hc⟩
  validN_ne h hv := validN_ne (x := _) h hv
  valid_iff_validN := valid_iff_validN
  validN_le := validN_le
  validN_op_left := validN_op_left
  assoc {x y z} := congrArg ULift.up (assoc (x := x.down) (y := y.down) (z := z.down))
  comm {x y} := congrArg ULift.up (comm (x := x.down) (y := y.down))
  pcore_op_left {x cx} e := by
    cases hx : pcore x.down with
    | none => simp [hx] at e
    | some cx' =>
      simp only [hx, Option.map_some, Option.some.injEq] at e
      subst e
      exact congrArg ULift.up (pcore_op_left hx)
  pcore_idem {x cx} e := by
    cases hx : pcore x.down with
    | none => simp [hx] at e
    | some cx' =>
      simp only [hx, Option.map_some, Option.some.injEq] at e
      subst e
      change Option.map ULift.up (pcore cx') = _
      rw [pcore_idem hx]
      rfl
  pcore_op_mono {x cx} e y := by
    cases hx : pcore x.down with
    | none => simp [hx] at e
    | some cx' =>
      simp only [hx, Option.map_some, Option.some.injEq] at e
      subst e
      obtain ⟨cy, hcy⟩ := pcore_op_mono hx y.down
      exact ⟨⟨cy⟩, by simp only [Option.map, hcy]⟩
  extend {n x y₁ y₂} hv h :=
    let ⟨z₁, z₂, hx, h₁, h₂⟩ := extend (x := x.down) hv h
    ⟨⟨z₁⟩, ⟨z₂⟩, congrArg ULift.up hx, h₁, h₂⟩

theorem ULift.up_op [CMRA α] (a b : α) : (ULift.up (a • b) : ULift α) = ⟨a⟩ • ⟨b⟩ := rfl

theorem ULift.valid_up [CMRA α] {a : α} : ✓ (ULift.up a : ULift α) ↔ ✓ a := Iff.rfl

theorem ULift.validN_up [CMRA α] {n : SI} {a : α} : ✓{n} (ULift.up a : ULift α) ↔ ✓{n} a :=
  Iff.rfl

theorem ULift.updateP [CMRA α] {a : α} {P : α → Prop} (h : a ~~>: P) :
    (ULift.up a : ULift α) ~~>: fun y => P y.down := by
  intro n mz hv
  obtain ⟨y, hy, hvy⟩ := h n (mz.map ULift.down) (by cases mz <;> exact hv)
  exact ⟨⟨y⟩, hy, by cases mz <;> exact hvy⟩

theorem ULift.update [CMRA α] {a b : α} (h : a ~~> b) :
    (ULift.up a : ULift α) ~~> ULift.up b := by
  intro n mz hv
  have := h n (mz.map ULift.down) (by cases mz <;> exact hv)
  cases mz <;> exact this

instance ULift.instUCMRA [UCMRA α] : UCMRA (ULift α) where
  unit := ⟨UCMRA.unit⟩
  unit_valid := UCMRA.unit_valid (α := α)
  unit_left_id {x} := congrArg ULift.up (UCMRA.unit_left_id (x := x.down))
  pcore_unit := by
    change Option.map ULift.up (pcore (UCMRA.unit : α)) = _
    rw [UCMRA.pcore_unit]
    rfl

instance ULift.instOFEDiscrete [OFE α] [OFE.Discrete α] : OFE.Discrete (ULift α) where
  discrete_0 h := congrArg ULift.up (OFE.Discrete.discrete_0 h)

instance ULift.instCMRADiscrete [CMRA α] [CMRA.Discrete α] : CMRA.Discrete (ULift α) where
  discrete_valid h := CMRA.Discrete.discrete_valid (α := α) h

instance ULift.instDiscreteE [OFE α] {a : α} [OFE.DiscreteE a] : OFE.DiscreteE (ULift.up a) where
  discrete h := congrArg ULift.up (OFE.DiscreteE.discrete h)

instance ULift.instCoreId [CMRA α] {a : α} [h : CMRA.CoreId a] : CMRA.CoreId (ULift.up a) where
  core_id := by
    change Option.map ULift.up (pcore a) = _
    rw [h.core_id]
    rfl

open COFE in
instance COFE.OFunctor.constOFU_RFunctor [CMRA B] : RFunctor (constOFU.{w} B) where
  cmra := inferInstance
  map _ _ := (CMRA.Hom.id : ULift.{w} B -C> ULift.{w} B)
  map_ne.ne _ _ _ _ _ _ _ := .rfl
  map_id _ := rfl
  map_comp _ _ _ _ _ := rfl

instance OFunctor.constOFU_RFunctorContractive [CMRA B] :
    RFunctorContractive (constOFU.{w} B) where
  map_contractive.1 := fun _ => .rfl

open COFE in
instance COFE.OFunctor.constOFU_URFunctor [UCMRA B] : URFunctor (constOFU.{w} B) where
  cmra := inferInstance
  map _ _ := (CMRA.Hom.id : ULift.{w} B -C> ULift.{w} B)
  map_ne.ne _ _ _ _ _ _ _ := .rfl
  map_id _ := rfl
  map_comp _ _ _ _ _ := rfl

instance OFunctor.constOFU_URFunctorContractive [UCMRA B] :
    URFunctorContractive (constOFU.{w} B) where
  map_contractive.1 _ := .rfl

end Iris
