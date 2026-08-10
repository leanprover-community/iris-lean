/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

/-!
# Telescopes

A telescope is a list of types in which every type may depend on the values of the preceding
ones. Telescopes let a single binder stand for an arbitrary, statically unknown number of
dependent binders; `Iris.BI.tforall` and `Iris.BI.texist` use them to express `∀`/`∃` over such
a block of binders.

This is a port of the part of stdpp's `telescopes.v` that Iris needs. Rocq relies on
cumulativity to place `Tele.Fun TT (fun _ => T)` and `T` in the same universe; Lean has no
cumulativity, so the empty telescope is interpreted by `ULift` instead.
-/

@[expose] public section

namespace Iris.Std

universe u v

/-- A telescope: a list of types where every type may depend on the values of the preceding
ones. -/
inductive Tele : Type (u + 1) where
  /-- The empty telescope. -/
  | nil : Tele
  /-- The telescope binding an `X`, followed by the telescope `binder x` for the bound `x`. -/
  | cons {X : Type u} (binder : X → Tele) : Tele

namespace Tele

/-- The type of arguments of a telescope: a nested dependent pair, with one component per
binder of the telescope. -/
def Arg : Tele.{u} → Type u
  | .nil => PUnit
  | .cons b => (x : _) × (b x).Arg

/-- The unique argument of the empty telescope. -/
@[match_pattern] abbrev Arg.nil : Arg.{u} .nil := ⟨⟩

/-- The argument of `Tele.cons b` binding `x` first and `xs` for the remaining telescope. -/
@[match_pattern] abbrev Arg.cons {b : X → Tele.{u}} (x : X) (xs : (b x).Arg) :
    (Tele.cons b).Arg := ⟨x, xs⟩

/-- The type of dependent telescopic functions: functions taking the arguments of the telescope
`TT` one at a time, returning a `T xs` for the arguments `xs` received. -/
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
  induction TT with
  | nil => rfl
  | cons b ih => exact ih xs.1 _ xs.2

/-- Collapse a non-dependent telescopic function into a single value, using `step` to introduce
one binder at a time. -/
def fold {B : Type v} (step : (A : Type u) → (A → B) → B) : {TT : Tele.{u}} → (TT -t> B) → B
  | .nil, f => ULift.down f
  | .cons _, f => step _ fun x => fold step (f x)

end Tele

end Iris.Std
