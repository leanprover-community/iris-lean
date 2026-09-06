/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
module

public import Iris.Init

@[expose] public section

namespace Iris.Std

set_option checkBinderAnnotations false

/-- Type class version of `False`, i.e. a type class with no instances. -/
class inductive TCFalse


/-- Type class version of `True`, i.e. a type class with a trivial instance without arguments. -/
class inductive TCTrue
  | t

instance : TCTrue := TCTrue.t


/-- Type class version of `Or`, i.e. a type class for which an instance exists if an instance of any
of the listed type classes is present. -/
class inductive TCOr (T U : Sort _)
  | l [t : T] : TCOr T U
  | r [u : U] : TCOr T U

instance [t : T] : TCOr T U := @TCOr.l T U t
instance [u : U] : TCOr T U := @TCOr.r T U u


/-- Type class version of `Eq`. `TCEq a b` has an instance exactly when `a = b`. -/
class inductive TCEq {α : Sort _} (a : α) : α → Prop
  | refl : TCEq a a

instance {α : Sort _} {a : α} : TCEq a a := TCEq.refl

theorem TCEq.to_eq {α : Sort _} {a b : α} : TCEq a b → a = b
  | .refl => rfl

/-- Type class version of `Ite`, i.e. a type class for which an instance exists if the boolean
condition is `true` and an instance of `T` is present or the condition is `false` and an instance
of `U` is present.

Note that type class instance search requires the condition to be fully reduced. -/
class inductive TCIte : Bool → Sort u → Sort v → Sort (max (u + 1) (v + 1))
  | t [t : T] : TCIte true T U
  | e [u : U] : TCIte false T U

-- `no_index` and the `unif_hint`s are a workaround for non-reducible boolean operations
instance [t : T] : TCIte (no_index true) T U := TCIte.t (t := t)
instance [u : U] : TCIte (no_index false) T U := TCIte.e (u := u)

unif_hint (b : Bool) where
  |- false || b ≟ b
unif_hint (b : Bool) where
  |- true || b ≟ true
unif_hint (b : Bool) where
  |- false && b ≟ false
unif_hint (b : Bool) where
  |- true && b ≟ b

/--
  This type class corresponds to `TCForall` in Rocq's stdpp.

  The core Lean libraries only provide `List.Forall₂` while `List.Forall` is
  available in Mathlib (`Mathlib.Data.List.Defs`) as a definition.
  The proposition `∀ x ∈ xs, p x` is typically directly used as an assertion,
  but `TCForall` as a type class is useful for automatic inference, e.g.,
  instances that involve `[∗]`.
-/
class inductive TCForall (p : α → Prop) : List α → Prop
  | nil : TCForall p []
  | cons {x : α} {xs : List α} : p x → TCForall p xs → TCForall p (x :: xs)

/-- Corresponding to `TCForall_Forall` in Rocq's stdpp. -/
theorem forall_TCForall {α} {p : α → Prop} {xs : List α} : TCForall p xs ↔ ∀ x ∈ xs, p x := by
  constructor
  · intro h
    induction h with
    | nil => intro _ _; contradiction
    | cons hx _ ih =>
      intro y hy
      cases hy with
      | head => exact hx
      | tail _ hy => exact ih _ hy
  · intro h
    induction xs with
    | nil => exact .nil
    | cons x xs ih =>
      constructor
      · exact h x (.head _)
      · apply ih
        intro y hy
        exact h y (.tail _ hy)

end Iris.Std
