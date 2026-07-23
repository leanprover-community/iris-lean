module

public import Std.Data.ExtTreeMap
public import Std.Data.ExtTreeSet

/-!
# Prelude shims for `IrisDoNightly`

This experimental project ports the HeapLang syntax and operational semantics onto a
bleeding-edge Lean nightly so that we can play with the `Std.Do` weakest-precondition
machinery, *without* dragging in the whole Iris algebra/BI stack (which is pinned to an
older stable toolchain).

Rather than importing `Iris.ProgramLogic.Language`, `Iris.Std.BitOp`,
`Iris.Std.Infinite`, `Iris.Std.PartialMap`, `Iris.Std.HeapInstances`, … (which transitively
pull in the entire library), we reproduce here the *small* pieces those files provide that
the syntax and semantics actually depend on:

* the `Int` bit-wise / shift instances (from `Iris.Std.BitOp`, originally copied from Mathlib);
* the `InfiniteType` class (from `Iris.Std.Infinite`);
* the `ToVal` class (from `Iris.ProgramLogic.Language`);
* a minimal `PartialMap` class together with the `Std.ExtTreeMap` instance
  (from `Iris.Std.PartialMap` / `Iris.Std.HeapInstances`).
-/

@[expose] public section

/-! ## Integer bit-wise operations

Copied from `Iris.Std.BitOp` (itself copied from Mathlib). Lean core does not provide
`AndOp`/`OrOp`/`XorOp`/`ShiftLeft`/`ShiftRight` instances for `Int`, so `BinOp.eval` needs
them. -/

namespace IrisDoNightly.BitOp

namespace Nat

/-- `ldiff` computes the bitwise "and not" of two natural numbers. -/
def ldiff : Nat → Nat → Nat :=
  Nat.bitwise fun a b => a && not b

/-- `bit b` appends the digit `b` to the little end of the binary representation of `n`. -/
def bit (b : Bool) (n : Nat) : Nat :=
  cond b (2 * n + 1) (2 * n)

/-- `shiftLeft' b m n` left-shifts `m` `n` times, inserting bit `b` each step. -/
def shiftLeft' (b : Bool) (m : Nat) : Nat → Nat
  | 0 => m
  | n + 1 => bit b (shiftLeft' b m n)

end Nat

namespace Int

open _root_.IrisDoNightly.BitOp.Nat _root_.Int

/-- Bitwise `or` on integers. -/
def lor : Int → Int → Int
  | (m : Nat), (n : Nat) => m ||| n
  | (m : Nat), -[n+1] => -[ldiff n m+1]
  | -[m+1], (n : Nat) => -[ldiff m n+1]
  | -[m+1], -[n+1] => -[m &&& n+1]

instance : OrOp Int := ⟨lor⟩

/-- Bitwise `and` on integers. -/
def land : Int → Int → Int
  | (m : Nat), (n : Nat) => m &&& n
  | (m : Nat), -[n+1] => ldiff m n
  | -[m+1], (n : Nat) => ldiff n m
  | -[m+1], -[n+1] => -[m ||| n+1]

instance : AndOp Int := ⟨land⟩

/-- Bitwise `xor` on integers. -/
def xor : Int → Int → Int
  | (m : Nat), (n : Nat) => (m ^^^ n)
  | (m : Nat), -[n+1] => -[(m ^^^ n)+1]
  | -[m+1], (n : Nat) => -[(m ^^^ n)+1]
  | -[m+1], -[n+1] => (m ^^^ n)

instance : XorOp Int := ⟨xor⟩

/-- Left shift on integers. -/
instance : ShiftLeft Int where
  shiftLeft
  | (m : Nat), (n : Nat) => Nat.shiftLeft' false m n
  | (m : Nat), -[n+1] => m >>> (Nat.succ n)
  | -[m+1], (n : Nat) => -[Nat.shiftLeft' true m n+1]
  | -[m+1], -[n+1] => -[m >>> (Nat.succ n)+1]

/-- Right shift on integers. -/
instance : ShiftRight Int where
  shiftRight m n := m <<< (-n)

end Int

end IrisDoNightly.BitOp

-- Bring the `Int` instances into scope everywhere.
open IrisDoNightly.BitOp.Int

/-! ## Infinite types

Copied from `Iris.Std.Infinite`. -/

/-- A type is *infinite* if there is an injection `Nat → T`. -/
class InfiniteType (T : Type _) where
  enum : Nat → T
  enum_inj : ∀ n m : Nat, enum n = enum m → n = m

instance : InfiniteType Nat where
  enum := id
  enum_inj _ _ H := H

/-! ## `ToVal`

Copied from `Iris.ProgramLogic.Language`, minus the `rocq_alias` bookkeeping. -/

namespace Iris.ProgramLogic

class ToVal (Expr : Type _) (Val : outParam (Type _)) where
  toVal : Expr → Option Val
  ofVal : Val → Expr
  /-- If `toVal` is defined for an expression, `ofVal` is its inverse. -/
  coe_of_toVal_eq_some {e : Expr} {v : Val} : toVal e = some v → ofVal v = e
  /-- `toVal` is the inverse of `ofVal`. -/
  toVal_coe (v : Val) : toVal (ofVal v) = some v
export ToVal (toVal coe_of_toVal_eq_some toVal_coe)

attribute [simp, grind =] ToVal.toVal_coe
attribute [coe] ToVal.ofVal

namespace ToVal

variable {Expr Val : Type _} [ι : ToVal Expr Val]

instance : Coe Val Expr where coe := ofVal

@[grind! .]
theorem toVal_eq_iff_coe (e : Expr) (v : Val) : v = e ↔ toVal e = some v :=
  ⟨(· ▸ toVal_coe v), coe_of_toVal_eq_some⟩

theorem ofVal_inj : ι.ofVal.Injective := by
  intro x y h
  simpa [toVal_coe] using congrArg (toVal) h

end ToVal
end Iris.ProgramLogic

/-! ## Partial maps

A minimal version of `Iris.Std.PartialMap` providing just the `get?`/`insert` operations,
together with the `Std.ExtTreeMap` instance from `Iris.Std.HeapInstances`, which is all the
HeapLang semantics needs to model its heap. -/

namespace Iris.Std

class PartialMap (M : Type _ → Type _) (K : outParam (Type _)) where
  get? : M V → K → Option V
  insert : M V → K → V → M V
export PartialMap (get? insert)

instance {K : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K] :
    PartialMap (Std.ExtTreeMap K · compare) K where
  get? t k := t[k]?
  insert t k v := t.alter k (fun _ => some v)

end Iris.Std
