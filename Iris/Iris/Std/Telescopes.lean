/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Init

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

/-- Telescopic universal quantification at `Prop`. -/
def tforall : {TT : Tele.{u}} → (TT.Arg → Prop) → Prop
  | .nil,    Ψ => Ψ .nil
  | .cons _, Ψ => ∀ x, tforall fun xs => Ψ (.cons x xs)

/-- Telescopic existential quantification at `Prop`. -/
def texist : {TT : Tele.{u}} → (TT.Arg → Prop) → Prop
  | .nil,    Ψ => Ψ .nil
  | .cons _, Ψ => ∃ x, texist fun xs => Ψ (.cons x xs)

theorem tforall_forall {TT : Tele} (Ψ : TT.Arg → Prop) : tforall Ψ ↔ ∀ x, Ψ x := by
  induction TT with
  | nil =>
    constructor
    · exact fun h _ => h
    · exact fun h => h .nil
  | cons b ih =>
    constructor
    · exact fun h x => (ih x.fst _).mp (h x.fst) x.snd
    · exact fun h x => (ih x _).mpr fun xs => h ⟨x, xs⟩

theorem texist_exist {TT : Tele} (Ψ : TT.Arg → Prop) : texist Ψ ↔ ∃ x, Ψ x := by
  induction TT with
  | nil =>
    constructor
    · exact fun h => ⟨.nil, h⟩
    · exact fun ⟨_, h⟩ => h
  | cons b ih =>
    constructor
    · exact fun ⟨x, h⟩ => let ⟨xs, h⟩ := (ih x _).mp h; ⟨⟨x, xs⟩, h⟩
    · exact fun ⟨x, h⟩ => ⟨x.fst, (ih x.fst _).mpr ⟨x.snd, h⟩⟩

end Tele

end Iris.Std
