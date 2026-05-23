/-
Copyright (c) 2026 Iris-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.SetTheory.Cardinal.Basic
public import Iris

@[expose] public section

/-!
# Cardinal CMRAs

Mathlib's `Cardinal` carries both a (commutative, associative) `max` and an
ordinary `+`, both with `0` as left identity (because `0 ≤ a` for every
cardinal). This file exposes both as UCMRAs on top of the wrapper
`LeibnizO Cardinal`, illustrating the two flavours of recipe from
`Iris/Algebra/Numbers.lean`:

* `CardinalMaxCMRA`: cardinals under `max`. The operation is idempotent
  (`max a a = a`), so we use the **universal-core** `OrdCommMonoidLike`
  recipe — every cardinal is its own core. Composition is monotone in both
  arguments (`a ≤ max a b`, `b ≤ max a b`), so the CMRA `≼` order coincides
  with the cardinal `≤` order.
* `CardinalAddCMRA`: cardinals under `+`. Cardinal addition is *not*
  idempotent (`1 + 1 = 2 ≠ 1`), so we use the **constant-core**
  `CommMonoidLike` recipe — only `0` is a `CoreId` and `pcore` is the constant
  function `some 0`.

Concretely, the two flavours sit on the same carrier `LeibnizO Cardinal` but
disagree on `+`/`pcore`/`CoreId`. Sister files are `LatticeCMRAs.lean`
(idempotent flavour) and `Multiset.lean` (constant-core flavour); we follow
their convention of referencing the recipe's `scoped` instances directly by
their generated names, since the ambient `inferInstance` machinery does not
see those `scoped` instances through a top-level `open`.

Because `Cardinal` is wrapped in `LeibnizO` it is discrete and Leibniz: `≡`,
`≡{n}≡` and `=` all coincide, which makes any function into either CMRA
trivially non-expansive.
-/

open Iris OFE CMRA Std

namespace IrisMath.Cardinal

/-! ## (A) Cardinals under `max` (idempotent, universal core) -/

/-- Cardinals as a UCMRA under `max`, with unit `0`. Idempotent; uses the
universal-core `OrdCommMonoidLike` recipe, so every cardinal is its own core. -/
noncomputable def _root_.IrisMath.CardinalMaxCMRA : Type _ := LeibnizO Cardinal

namespace _root_.IrisMath.CardinalMaxCMRA

instance : COFE CardinalMaxCMRA := inferInstanceAs (COFE (LeibnizO _))
instance : OFE.Discrete CardinalMaxCMRA := inferInstanceAs (OFE.Discrete (LeibnizO _))
instance : OFE.Leibniz CardinalMaxCMRA := inferInstanceAs (OFE.Leibniz (LeibnizO _))

/-- The CMRA operation: cardinal `max`. -/
noncomputable instance : Add CardinalMaxCMRA := ⟨fun a b ↦ ⟨max a.car b.car⟩⟩

/-- The CMRA unit: the zero cardinal. -/
instance : Zero CardinalMaxCMRA := ⟨⟨0⟩⟩

/-- Unfolding lemma for the operation. -/
theorem add_def (a b : CardinalMaxCMRA) : a + b = ⟨max a.car b.car⟩ := rfl

/-- Unfolding lemma for the unit. -/
theorem zero_def : (0 : CardinalMaxCMRA) = ⟨0⟩ := rfl

instance : Std.Associative (Add.add (α := CardinalMaxCMRA)) where
  assoc a b c :=
    show (⟨max (max a.car b.car) c.car⟩ : CardinalMaxCMRA)
        = ⟨max a.car (max b.car c.car)⟩ by
      rw [max_assoc]

instance : Std.Commutative (Add.add (α := CardinalMaxCMRA)) where
  comm a b :=
    show (⟨max a.car b.car⟩ : CardinalMaxCMRA) = ⟨max b.car a.car⟩ by
      rw [max_comm]

instance : Std.IdempotentOp (Add.add (α := CardinalMaxCMRA)) where
  idempotent a :=
    show (⟨max a.car a.car⟩ : CardinalMaxCMRA) = a by
      cases a with
      | mk x => exact congrArg _ (max_self x)

instance :
    Std.LawfulLeftIdentity (Add.add (α := CardinalMaxCMRA)) (0 : CardinalMaxCMRA) where
  left_id a :=
    show (⟨max (0 : Cardinal) a.car⟩ : CardinalMaxCMRA) = a by
      cases a with
      | mk x => exact congrArg _ (max_eq_right (Cardinal.zero_le x))

noncomputable instance : CMRA CardinalMaxCMRA := OrdCommMonoidLike.instCMRA
noncomputable instance : CMRA.Discrete CardinalMaxCMRA := OrdCommMonoidLike.instDiscrete
noncomputable instance : UCMRA CardinalMaxCMRA :=
  OrdCommMonoidLike.instUCMRAOfLawfulLeftIdentityAddZero

/-- Every cardinal is its own core (the `max` operation is idempotent). -/
example (a : CardinalMaxCMRA) : CMRA.CoreId a := OrdCommMonoidLike.instCoreId _

/-- A cardinal is below the `max` of itself with anything: `a ≤ max a b`. -/
theorem le_op_left (a b : CardinalMaxCMRA) : a.car ≤ (a + b).car := le_max_left _ _

/-- Symmetric companion to `le_op_left`. -/
theorem le_op_right (a b : CardinalMaxCMRA) : b.car ≤ (a + b).car := le_max_right _ _

/-- Every cardinal is its own core under `max` (witnessed by the operation
itself being idempotent). -/
theorem op_self (a : CardinalMaxCMRA) : a + a = a :=
  show (⟨max a.car a.car⟩ : CardinalMaxCMRA) = a by
    cases a with
    | mk x => exact congrArg _ (max_self x)

/-- Concrete idempotency example: `max ℵ₀ ℵ₀ = ℵ₀` inside the CMRA. -/
example :
    let a : CardinalMaxCMRA := ⟨Cardinal.aleph0⟩
    a + a = a := op_self _

end _root_.IrisMath.CardinalMaxCMRA

/-! ## (B) Cardinals under `+` (constant core) -/

/-- Cardinals as a UCMRA under ordinary addition `+`, with unit `0`. Not
idempotent (`1 + 1 = 2`); uses the constant-core `CommMonoidLike` recipe, so
only `0` is a `CoreId`. -/
def _root_.IrisMath.CardinalAddCMRA : Type _ := LeibnizO Cardinal

namespace _root_.IrisMath.CardinalAddCMRA

instance : COFE CardinalAddCMRA := inferInstanceAs (COFE (LeibnizO _))
instance : OFE.Discrete CardinalAddCMRA := inferInstanceAs (OFE.Discrete (LeibnizO _))
instance : OFE.Leibniz CardinalAddCMRA := inferInstanceAs (OFE.Leibniz (LeibnizO _))

/-- The CMRA operation: cardinal addition. -/
instance : Add CardinalAddCMRA := ⟨fun a b ↦ ⟨a.car + b.car⟩⟩

/-- The CMRA unit: the zero cardinal. -/
instance : Zero CardinalAddCMRA := ⟨⟨0⟩⟩

/-- Unfolding lemma for the operation. -/
theorem add_def (a b : CardinalAddCMRA) : a + b = ⟨a.car + b.car⟩ := rfl

/-- Unfolding lemma for the unit. -/
theorem zero_def : (0 : CardinalAddCMRA) = ⟨0⟩ := rfl

instance : Std.Associative (Add.add (α := CardinalAddCMRA)) where
  assoc a b c :=
    show (⟨(a.car + b.car) + c.car⟩ : CardinalAddCMRA)
        = ⟨a.car + (b.car + c.car)⟩ by
      rw [add_assoc]

instance : Std.Commutative (Add.add (α := CardinalAddCMRA)) where
  comm a b :=
    show (⟨a.car + b.car⟩ : CardinalAddCMRA) = ⟨b.car + a.car⟩ by
      rw [add_comm]

instance :
    Std.LawfulLeftIdentity (Add.add (α := CardinalAddCMRA)) (0 : CardinalAddCMRA) where
  left_id a :=
    show (⟨(0 : Cardinal) + a.car⟩ : CardinalAddCMRA) = a by
      cases a with
      | mk x => exact congrArg _ (zero_add x)

instance : CMRA CardinalAddCMRA := CommMonoidLike.instCMRA
instance : CMRA.Discrete CardinalAddCMRA := CommMonoidLike.instDiscrete
instance : UCMRA CardinalAddCMRA := CommMonoidLike.instUCMRA

/-- The unit `0` is a `CoreId` under cardinal addition. -/
example : CMRA.CoreId (0 : CardinalAddCMRA) :=
  open CommMonoidLike in inferInstance

/-- Concrete example: the CMRA operation on `CardinalAddCMRA` recovers
ordinary cardinal addition, e.g. `1 + 1 = 2`. -/
example :
    let a : CardinalAddCMRA := ⟨(1 : Cardinal)⟩
    let b : CardinalAddCMRA := ⟨(2 : Cardinal)⟩
    a + a = b := by
  simp only [add_def]
  exact congrArg _ one_add_one_eq_two

end _root_.IrisMath.CardinalAddCMRA

/-! ## (C) Sanity examples at the top level -/

#check (inferInstance : UCMRA IrisMath.CardinalMaxCMRA)
#check (inferInstance : UCMRA IrisMath.CardinalAddCMRA)

/-- The cardinality function `Cardinal.mk : Type u → Cardinal` lifts to a
non-expansive map from `LeibnizO (Type u)` to `CardinalMaxCMRA`. Because both
sides are Leibniz OFEs, this is just `congrArg`. -/
example :
    NonExpansive (fun (A : LeibnizO (Type u)) ↦
      (⟨Cardinal.mk A.car⟩ : IrisMath.CardinalMaxCMRA)) :=
  ⟨fun _ _ _ h ↦ by cases h; rfl⟩

/-- Same statement targeting `CardinalAddCMRA`; both carriers are the same
underlying `LeibnizO Cardinal`, so the proof is identical. -/
example :
    NonExpansive (fun (A : LeibnizO (Type u)) ↦
      (⟨Cardinal.mk A.car⟩ : IrisMath.CardinalAddCMRA)) :=
  ⟨fun _ _ _ h ↦ by cases h; rfl⟩

end IrisMath.Cardinal
