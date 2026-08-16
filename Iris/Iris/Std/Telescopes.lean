/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

/-!
# Telescopes

A telescope is a list of types in which every type may depend on the values of the preceding
ones. Telescopes let a single binder stand for an arbitrary, statically unknown number of
dependent binders; `Iris.BI.tforall` and `Iris.BI.texist` use them to express `∀`/`∃` over such
a block of binders.
-/

@[expose] public section

namespace Iris.Std

universe u v

/-- A telescope: a list of types where every type may depend on the values of the preceding
ones. -/
inductive Tele : Type (u + 1) where
  | nil : Tele
  | cons {X : Type u} (binder : X → Tele) : Tele

namespace Tele

/-- Conversion between a telescope and a nested dependent pair -/
def Arg : Tele.{u} → Type u
  | .nil => PUnit
  | .cons b => (x : _) × (b x).Arg

@[match_pattern] abbrev Arg.nil : Arg.{u} .nil := ⟨⟩

@[match_pattern] abbrev Arg.cons {b : X → Tele.{u}} (x : X) (xs : (b x).Arg) :
    (Tele.cons b).Arg := ⟨x, xs⟩

def Fun : (TT : Tele.{u}) → (TT.Arg → Type v) → Type (max u v)
  | .nil, T => ULift (T .nil)
  | .cons b, T => (x : _) → (b x).Fun fun xs => T (.cons x xs)

/-- The type of non-dependent telescopic functions from `TT` to `T`. -/
notation:25 TT:26 " -t> " T:25 => Tele.Fun TT fun _ => T

/-- Apply a telescopic function to a telescope argument. -/
def app : {TT : Tele.{u}} → {T : TT.Arg → Type v} → TT.Fun T → (xs : TT.Arg) → T xs
  | .nil, _, F, _ => ULift.down F
  | .cons _, _, F, .cons x xs => app (F x) xs

/-- Turn a function on telescope arguments into a telescopic function. -/
def bind : {TT : Tele.{u}} → {T : TT.Arg → Type v} → ((xs : TT.Arg) → T xs) → TT.Fun T
  | .nil, _, F => .up (F .nil)
  | .cons _, _, F => fun x => bind fun xs => F (.cons x xs)

theorem app_bind {TT : Tele.{u}} {T : TT.Arg → Type v} (F : (xs : TT.Arg) → T xs)
    (xs : TT.Arg) : app (bind F) xs = F xs := by
  induction TT with | nil => rfl | cons b ih => exact ih xs.1 _ xs.2

/-- Collapse a non-dependent telescopic function into a single value, using `step` to introduce
one binder at a time. -/
def fold {B : Type v} (step : (A : Type u) → (A → B) → B) : {TT : Tele.{u}} → (TT -t> B) → B
  | .nil, f => ULift.down f
  | .cons _, f => step _ fun x => fold step (f x)

end Tele

end Iris.Std
