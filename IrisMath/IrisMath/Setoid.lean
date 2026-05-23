/-
Copyright (c) 2026 Iris-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Setoid.Basic
public import Iris

@[expose] public section

/-!
# Setoids as an idempotent UCMRA

A `Setoid α` is an equivalence relation on `α` — a reflexive, symmetric, and
transitive binary relation, equivalently a partition of `α` into equivalence
classes. The collection of setoids on `α` is ordered by *refinement*: `r₁ ≤ r₂`
iff every `r₁`-equivalence class is contained in some `r₂`-equivalence class,
i.e. `r₂` is a *coarsening* of `r₁`. Under this order Mathlib equips `Setoid α`
with a `CompleteLattice` structure: the bottom element is equality, the top
element identifies all of `α`, and finite suprema combine identifications.

We expose this lattice as an idempotent UCMRA `SetoidCMRA α` whose operation is
supremum (`⊔`) and whose unit is `⊥` (the finest setoid, namely equality).
Concretely, `r₁ ⊔ r₂` is the smallest equivalence relation containing both
`r₁` and `r₂` — see `Setoid.sup_def`, which describes it as the equivalence
closure of the pointwise union `⇑r₁ ⊔ ⇑r₂`.

The intuition for the operation is **information merger** in a knowledge-style
separation logic. Reading a setoid as "the set of identifications I currently
know to hold", `r₁ + r₂` records *the union of what both parties know*: every
fact `r₁ x y` or `r₂ x y` still holds, plus any identifications forced by
transitivity. Idempotence (`r + r = r`) reflects the fact that merging
knowledge with itself yields nothing new, which in turn makes every setoid its
own CMRA core. The unit `⊥` is equality: it identifies nothing beyond
syntactic equality, so combining it with any `r` yields `r`.

Quotients tie the picture together: for `a : SetoidCMRA α`, the type
`Quotient a.car` is the type of equivalence classes under the carried setoid.
Refinement of setoids corresponds to a canonical surjection between the
associated quotient types — `r₁ ≤ r₂` means there is a well-defined map
`Quotient r₁ → Quotient r₂`. Combining two setoids via the CMRA operation
therefore yields the *coarsest* quotient that both parties can still talk
about; see `Quotient.factor_le`.

This is the setoid analogue of `IrisMath.Lattice.SubmoduleCMRA` and
`IrisMath.SigmaAlgebra.SigmaAlgebraCMRA`. As for those, the carrier is wrapped
in `LeibnizO` (discrete + Leibniz OFE) and the UCMRA structure comes from the
`OrdCommMonoidLike` recipe, surfaced by directly referencing the underlying
scoped instance names (`OrdCommMonoidLike.instCMRA` etc.).
-/

open Iris OFE CMRA Std

namespace IrisMath.Setoid

/-- Equivalence relations on `α` as a UCMRA under supremum (`⊔`), with unit
`⊥` (equality). The operation `r₁ + r₂` is the smallest equivalence relation
containing both `r₁` and `r₂`, and every setoid is its own core. -/
def SetoidCMRA (α : Type _) : Type _ := LeibnizO (_root_.Setoid α)

namespace SetoidCMRA

variable {α : Type _}

/-- The discrete COFE structure on `SetoidCMRA α`, inherited from `LeibnizO`. -/
instance : COFE (SetoidCMRA α) := inferInstanceAs (COFE (LeibnizO _))

/-- `SetoidCMRA α` is a discrete OFE. -/
instance : OFE.Discrete (SetoidCMRA α) := inferInstanceAs (OFE.Discrete (LeibnizO _))

/-- `SetoidCMRA α` is a Leibniz OFE: OFE equivalence coincides with `=`. -/
instance : OFE.Leibniz (SetoidCMRA α) := inferInstanceAs (OFE.Leibniz (LeibnizO _))

/-- The CMRA operation: setoid supremum, i.e. the smallest equivalence relation
containing both arguments. -/
instance : Add (SetoidCMRA α) := ⟨fun a b ↦ ⟨a.car ⊔ b.car⟩⟩

/-- The CMRA unit: the finest setoid `⊥`, i.e. equality. -/
instance : Zero (SetoidCMRA α) := ⟨⟨⊥⟩⟩

/-- Unfolding lemma for the operation: addition is the supremum of carriers. -/
theorem add_def (a b : SetoidCMRA α) : a + b = ⟨a.car ⊔ b.car⟩ := rfl

/-- Unfolding lemma for the unit: zero is the bottom setoid (equality). -/
theorem zero_def : (0 : SetoidCMRA α) = ⟨⊥⟩ := rfl

/-- The carrier-level shape of the operation: `(a + b).car = a.car ⊔ b.car`. -/
@[simp] theorem add_car (a b : SetoidCMRA α) : (a + b).car = a.car ⊔ b.car := rfl

/-- The relation underlying `a + b` is the equivalence closure of the pointwise
union of the relations underlying `a` and `b`; see `Setoid.sup_def` in Mathlib
for the full description of `⊔` on setoids. -/
theorem op_rel (a b : SetoidCMRA α) :
    (a + b).car = Relation.EqvGen.setoid (⇑a.car ⊔ ⇑b.car) := by
  rw [add_car, _root_.Setoid.sup_def]

/-- Associativity of the CMRA operation, lifted from `sup_assoc`. -/
instance : Std.Associative (Add.add (α := SetoidCMRA α)) where
  assoc a b c :=
    show (⟨(a.car ⊔ b.car) ⊔ c.car⟩ : SetoidCMRA α)
        = ⟨a.car ⊔ (b.car ⊔ c.car)⟩ by
      rw [sup_assoc]

/-- Commutativity of the CMRA operation, lifted from `sup_comm`. -/
instance : Std.Commutative (Add.add (α := SetoidCMRA α)) where
  comm a b :=
    show (⟨a.car ⊔ b.car⟩ : SetoidCMRA α) = ⟨b.car ⊔ a.car⟩ by
      rw [sup_comm]

/-- Idempotence of the CMRA operation, lifted from `sup_idem`. -/
instance : Std.IdempotentOp (Add.add (α := SetoidCMRA α)) where
  idempotent a :=
    show (⟨a.car ⊔ a.car⟩ : SetoidCMRA α) = a by
      cases a
      simp

/-- The unit `⊥` is a left identity for `+`, lifted from `bot_sup_eq`. -/
instance : Std.LawfulLeftIdentity (Add.add (α := SetoidCMRA α)) (0 : SetoidCMRA α) where
  left_id a :=
    show (⟨(⊥ : _root_.Setoid α) ⊔ a.car⟩ : SetoidCMRA α) = a by
      cases a
      simp

/-- The CMRA structure on `SetoidCMRA α`, obtained from the
`OrdCommMonoidLike` recipe. -/
instance : CMRA (SetoidCMRA α) := OrdCommMonoidLike.instCMRA

/-- `SetoidCMRA α` is a discrete CMRA. -/
instance : CMRA.Discrete (SetoidCMRA α) := OrdCommMonoidLike.instDiscrete

/-- `SetoidCMRA α` is a UCMRA, with unit `⊥`. -/
instance : UCMRA (SetoidCMRA α) := OrdCommMonoidLike.instUCMRAOfLawfulLeftIdentityAddZero

/-- Every setoid is its own core. -/
example (a : SetoidCMRA α) : CMRA.CoreId a := OrdCommMonoidLike.instCoreId _

/-- Sup of setoids is idempotent: every setoid is its own operation. This is
the elementary witness that the CMRA is idempotent, before any wrapping through
`CoreId`. -/
theorem op_self (a : SetoidCMRA α) : a + a = a :=
  Std.IdempotentOp.idempotent (op := Add.add (α := SetoidCMRA α)) a

/-- The CMRA operation dominates the left argument in the setoid lattice: the
combined setoid is a coarsening of `a`. -/
theorem le_op_left (a b : SetoidCMRA α) : a.car ≤ (a + b).car := le_sup_left

/-- Symmetric companion to `le_op_left`: the combined setoid is a coarsening
of `b`. -/
theorem le_op_right (a b : SetoidCMRA α) : b.car ≤ (a + b).car := le_sup_right

/-- Sanity example: two setoids combine via `+` to their supremum. -/
example (r₁ r₂ : _root_.Setoid α) :
    let a : SetoidCMRA α := ⟨r₁⟩
    let b : SetoidCMRA α := ⟨r₂⟩
    a + b = ⟨r₁ ⊔ r₂⟩ := rfl

/-- Sanity example: combining the finest setoid `⊥` (equality) with the
coarsest setoid `⊤` (one equivalence class) recovers `⊤`, i.e. `⊥` is absorbed
by any coarser setoid (it is the unit of the operation). -/
example :
    let a : SetoidCMRA α := ⟨⊥⟩
    let b : SetoidCMRA α := ⟨⊤⟩
    a + b = ⟨⊤⟩ := by
  change (⟨(⊥ : _root_.Setoid α) ⊔ ⊤⟩ : SetoidCMRA α) = ⟨⊤⟩
  rw [bot_sup_eq]

/-! ## Connection to quotient types

Each `a : SetoidCMRA α` packages a setoid `a.car`, and `Quotient a.car` is the
corresponding type of equivalence classes. Refinement of setoids — the CMRA
order direction — induces a canonical surjection between quotient types,
witnessing that combining two setoids via `+` yields a *coarser* quotient than
either factor. -/

/-- The quotient of `α` by the setoid carried by `a : SetoidCMRA α`. -/
abbrev Quot (a : SetoidCMRA α) : Type _ := Quotient a.car

/-- The canonical projection sending `x : α` to its equivalence class in
`Quot a`. -/
def mk (a : SetoidCMRA α) (x : α) : Quot a := Quotient.mk a.car x

/-- Refinement of setoids yields a well-defined map between quotient types:
if `a.car ≤ b.car`, every `a`-equivalence class is contained in a unique
`b`-equivalence class, giving a surjection `Quot a → Quot b`. -/
def factor {a b : SetoidCMRA α} (h : a.car ≤ b.car) (x : Quot a) : Quot b :=
  Quotient.liftOn x (Quotient.mk b.car) fun _ _ hxy ↦ Quotient.sound (h hxy)

/-- `factor` commutes with the canonical projection: factoring the class of
`x` through `a ≤ b` is the class of `x` in `Quot b`. -/
@[simp] theorem factor_mk {a b : SetoidCMRA α} (h : a.car ≤ b.car) (x : α) :
    factor h (mk a x) = mk b x := rfl

/-- Combining two setoids via `+` produces a coarser quotient than either
factor: there is a canonical surjection `Quot a → Quot (a + b)` obtained from
`le_op_left`. -/
def factorLeft (a b : SetoidCMRA α) : Quot a → Quot (a + b) :=
  factor (le_op_left a b)

/-- Symmetric companion to `factorLeft`. -/
def factorRight (a b : SetoidCMRA α) : Quot b → Quot (a + b) :=
  factor (le_op_right a b)

end SetoidCMRA

end IrisMath.Setoid
