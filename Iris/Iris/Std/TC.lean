/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
module

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

class MakeNatAdd (n1 n2 : Nat) (m : outParam Nat) where
  make_nat_add : m = n1 + n2

instance (n : Nat) : MakeNatAdd 0 n n where
  make_nat_add := (Nat.zero_add n).symm

instance (n : Nat) : MakeNatAdd n 0 n where
  make_nat_add := (Nat.add_zero n).symm

instance (priority := low) make_nat_add_default n1 n2 : MakeNatAdd n1 n2 (n1 + n2) where
  make_nat_add := rfl

class MakeNatS (n1 n2 : Nat) (m : outParam Nat) : Prop where
  make_nat_S : m = n1 + n2

instance (n : Nat) : MakeNatS 0 n n where
  make_nat_S := (Nat.zero_add n).symm

instance (priority := high) make_nat_S_1_0 : MakeNatS 1 0 1 where
  make_nat_S := rfl

instance (n : Nat) : MakeNatS 1 n (n + 1) where
  make_nat_S := by omega

/-- Type class for natural number cancellation. Given a number `n` and a number `m` that should
be cancelled (subtracted) from `n`, compute a new `n'` and a remainder `m'` that could not be cancelled. -/
class NatCancel (n m : Nat) (n' m' : outParam Nat) : Prop where
  nat_cancel : n' + m = n + m'
export NatCancel (nat_cancel)

instance (priority := low) : NatCancel n m n m where
  nat_cancel := by simp

instance (priority := high) : NatCancel 0 m 0 m where
  nat_cancel := rfl

instance (priority := high) : NatCancel n 0 n 0 where
  nat_cancel := Nat.add_zero n

instance (priority := high) : NatCancel n n 0 0 where
  nat_cancel := by simp

instance [h : NatCancel n m n' m'] : NatCancel (n + 1) (m + 1) n' m' where
  nat_cancel := by have := h.nat_cancel; grind

instance (priority := high) : NatCancel (n + m) n m 0 where
  nat_cancel := by omega

instance (priority := high) : NatCancel (n + m) m n 0 where
  nat_cancel := by simp

instance (priority := high) : NatCancel n (n + m) 0 m where
  nat_cancel := by omega

instance (priority := high) : NatCancel m (n + m) 0 n where
  nat_cancel := by omega

class NatCancelL (n m : Nat) (n' m' : outParam Nat) : Prop where
  nat_cancel_l : n' + m = n + m'
export NatCancelL (nat_cancel_l)

class NatCancelR (n m : Nat) (n' m' : outParam Nat) : Prop where
  nat_cancel_r : NatCancelL n m n' m'
export NatCancelR (nat_cancel_r)

instance (priority := low) [inst : NatCancelR n m n' m'] :
    NatCancelL n m n' m' where
  nat_cancel_l := inst.nat_cancel_r.nat_cancel_l

instance (priority := default - 100) (n : Nat) : NatCancelR n n 0 0 where
  nat_cancel_r := by constructor; simp

instance (priority := default - 300)
    [h1 : NatCancelR n m1 n' m1'] [h2 : NatCancelR n' m2 n'' m2']
    [h3 : MakeNatAdd m1' m2' m1'm2'] :
    NatCancelR n (m1 + m2) n'' m1'm2' where
  nat_cancel_r := by
    constructor
    let h1 := h1.nat_cancel_r.nat_cancel_l
    let h2 := h2.nat_cancel_r.nat_cancel_l
    let h3 := h3.make_nat_add
    omega

instance (priority := default - 400) [h : NatCancelR n m n' m'] :
    NatCancelR (n + 1) (m + 1) n' m' where
  nat_cancel_r := by
    constructor
    let h := h.nat_cancel_r.nat_cancel_l
    omega

instance (priority := 500)
    [h1 : NatCancelR n m n' m'] [h2 : MakeNatS 1 m' Sm'] :
    NatCancelR n (m + 1) n' Sm' where
  nat_cancel_r := by
    constructor
    let h1 := h1.nat_cancel_r.nat_cancel_l
    let h2 := h2.make_nat_S
    omega

instance (priority := low) (n m : Nat) : NatCancelR n m n m where
  nat_cancel_r := ⟨rfl⟩

instance (priority := default - 50) (n : Nat) : NatCancelL n 0 n 0 where
  nat_cancel_l := rfl

instance (priority := default - 100) [h : NatCancelL n m n' m'] :
    NatCancelL (n + 1) (m + 1) n' m' where
  nat_cancel_l := by have := h.nat_cancel_l; omega

instance (priority := default - 200)
    [h1 : NatCancelL n1 m n1' m'] [h2 : NatCancelL n2 m' n2' m'']
    [h3 : MakeNatAdd n1' n2' n1'n2'] :
    NatCancelL (n1 + n2) m n1'n2' m'' where
  nat_cancel_l := by
    let h1 := h1.nat_cancel_l
    let h2 := h2.nat_cancel_l
    let h3 := h3.make_nat_add
    omega

instance (priority := default - 300)
    [h1 : NatCancelL n m n' m'] [h2 : NatCancelR 1 m' n'' m'']
    [h3 : MakeNatS n'' n' Sn'] :
    NatCancelL (n + 1) m Sn' m'' where
  nat_cancel_l := by
    let h1 := h1.nat_cancel_l
    let h2 := h2.nat_cancel_r.nat_cancel_l
    let h3 := h3.make_nat_S
    omega

instance [inst : NatCancelL n m n' m'] : NatCancel n m n' m' where
  nat_cancel := inst.nat_cancel_l

end Iris.Std
