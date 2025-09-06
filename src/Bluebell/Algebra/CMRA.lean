import Mathlib.Tactic.TypeStar
import Iris.Algebra.CMRA

namespace Bluebell

open Iris
open Iris.CMRA

/-! ## Predicated product CMRA

We package a product `α × β` together with a compatibility predicate `Φ : α → β → Prop`.
The carrier is the subtype `{ (x,y) // Φ x y }`. We equip it with componentwise op and
product-style validity (`✓ (x,y) ↔ ✓ x ∧ ✓ y`).

Design choice: we make the partial core constantly `none` on this construction. This keeps
requirements on `Φ` minimal (we only need closure under op and stability under Dist for `extend`).
If a core is needed later, this construction can be refined to a core-preserving variant.
-/

variable {α β : Type*} [CMRA α] [CMRA β]

namespace CMRA

/-- Use CMRA inclusion `≼` as the order on `M` so `UpperSet M` matches upward-closed predicates.

NOTE: when combined with `cmraFun`, this would cause a diamond with `Set.hasLe` (instances are
prop'eq but not def'eq). We have chosen to go with the CMRA instance for now. -/
instance instLE : LE α := ⟨CMRA.Included⟩

/-- Compatibility of a predicate with the CMRA structure on `α` and `β`.
Requires closure under componentwise op and stability under Dist in both arguments. -/
class CompatibleRel (Φ : α → β → Prop) : Prop where
  op_closed : ∀ {x₁ x₂ y₁ y₂}, Φ x₁ y₁ → Φ x₂ y₂ → Φ (x₁ • x₂) (y₁ • y₂)
  dist_closed : ∀ {n x₁ x₂ y₁ y₂}, x₁ ≡{n}≡ x₂ → y₁ ≡{n}≡ y₂ → Φ x₁ y₁ → Φ x₂ y₂

/-- Predicated product carrier. -/
abbrev ProdRel (Φ : α → β → Prop) := { xy : α × β // Φ xy.1 xy.2 }

end CMRA

variable {Φ : α → β → Prop}

open CMRA

instance : OFE (ProdRel (α := α) (β := β) Φ) where
  Equiv x y := x.1 ≡ y.1
  Dist n x y := x.1 ≡{n}≡ y.1
  dist_eqv := {
    refl _ := OFE.Dist.rfl
    symm h := OFE.Dist.symm h
    trans h₁ h₂ := OFE.Dist.trans h₁ h₂
  }
  equiv_dist := OFE.equiv_dist
  dist_lt := OFE.dist_lt

noncomputable instance cmraProdRel (Φ : α → β → Prop) [CompatibleRel (α := α) (β := β) Φ]
    : CMRA (ProdRel (α := α) (β := β) Φ) where
  pcore _ := none
  op x y := ⟨(x.1.1 • y.1.1, x.1.2 • y.1.2), CompatibleRel.op_closed (x₁ := x.1.1) (y₁ := x.1.2)
      (x₂ := y.1.1) (y₂ := y.1.2) x.2 y.2⟩
  ValidN n x := ✓{n} x.1.1 ∧ ✓{n} x.1.2
  Valid x := ✓ x.1.1 ∧ ✓ x.1.2
  op_ne {x} :=
    { ne n y z h :=
        -- Build product Dist from component Dist
        OFE.dist_prod_ext (CMRA.op_right_dist _ (OFE.dist_fst h))
                          (CMRA.op_right_dist _ (OFE.dist_snd h)) }
  pcore_ne {_} := by intro _ x y cx hpc; cases hpc
  validN_ne {n x y} H Hx := ⟨validN_ne (OFE.dist_fst H) Hx.left,
                             validN_ne (OFE.dist_snd H) Hx.right⟩
  valid_iff_validN {x} := by
    constructor
    · intro h n; exact ⟨(valid_iff_validN.mp h.left n), (valid_iff_validN.mp h.right n)⟩
    · intro h; exact ⟨(valid_iff_validN.mpr (fun n => (h n).left)),
                     (valid_iff_validN.mpr (fun n => (h n).right))⟩
  validN_succ {x n} := by intro h; exact ⟨validN_succ h.left, validN_succ h.right⟩
  validN_op_left {n x y} := by intro h; exact ⟨validN_op_left h.left, validN_op_left h.right⟩
  assoc {x y z} := ⟨assoc, assoc⟩
  comm {x y} := ⟨comm, comm⟩
  pcore_op_left {x cx} h := by cases h
  pcore_idem {x cx} h := by cases h
  pcore_op_mono {x cx} h y := by cases h
  extend {n x y₁ y₂} Hv He := by
    -- Componentwise extend, then close the predicate using Dist-closure
    let E₁ := extend (x := x.1.1) (y₁ := y₁.1.1) (y₂ := y₂.1.1) (Hv.left) (OFE.dist_fst He)
    let E₂ := extend (x := x.1.2) (y₁ := y₁.1.2) (y₂ := y₂.1.2) (Hv.right) (OFE.dist_snd He)
    refine ⟨⟨(E₁.1, E₂.1), ?_⟩, ⟨(E₁.2.1, E₂.2.1), ?_⟩, ?_, ?_, ?_⟩
    · -- Close Φ for z₁ using y₁ ≡{n}≡ z₁ componentwise (note symmetry)
      exact CompatibleRel.dist_closed (n := n) (E₁.2.2.2.1).symm (E₂.2.2.2.1).symm y₁.2
    · -- Close Φ for z₂ using y₂ ≡{n}≡ z₂ componentwise (note symmetry)
      exact CompatibleRel.dist_closed (n := n) (E₁.2.2.2.2).symm (E₂.2.2.2.2).symm y₂.2
    · -- x ≡ op z₁ z₂
      exact OFE.equiv_prod_ext (E₁.2.2.1) (E₂.2.2.1)
    · -- z₁ ≡{n}≡ y₁
      exact OFE.dist_prod_ext (E₁.2.2.2.1) (E₂.2.2.2.1)
    · -- z₂ ≡{n}≡ y₂
      exact OFE.dist_prod_ext (E₁.2.2.2.2) (E₂.2.2.2.2)

/-- A generic dependent function-space CMRA instance that does not assume total cores.
Operation and validity are pointwise; the partial core is constantly `none`.
This is sufficient for indexed products where the component CMRA might be non-total
(e.g., DFrac-based permissions). -/
noncomputable instance cmraFun {ι : Type*} {β : ι → Type*} [∀ i, CMRA (β i)] :
    CMRA ((i : ι) → β i) where
  -- No cores for function elements
  pcore _ := none
  -- Pointwise op
  op f g i := f i • g i
  -- Pointwise validity
  ValidN n f := ∀ i, ✓{n} f i
  Valid f := ∀ i, ✓ f i

  -- Non-expansiveness of op: pointwise
  op_ne.ne n f g H i := (H i).op_r

  -- pcore_ne: vacuous, since pcore is always none
  pcore_ne {n x y cx} _ hx := by
    have : (none : Option ((i : ι) → β i)) = some cx := by simp at hx
    cases this

  -- Validity respects equivalence pointwise
  validN_ne {n x y} H Hx i := (validN_ne (H i) (Hx i))
  valid_iff_validN {f} := by
    constructor
    · intro hv n i; exact (valid_iff_validN.mp (hv i)) n
    · intro h i; exact (valid_iff_validN.mpr (fun n => h n i))
  validN_succ {x n} H i := validN_succ (H i)
  validN_op_left {n x y} H i := validN_op_left (H i)

  -- Algebraic laws pointwise
  assoc {x y z} := by intro i; exact assoc
  comm {x y} := by intro i; exact comm

  -- Core laws are vacuous (pcore never returns some)
  pcore_op_left {x cx} hx := by
    have : (none : Option ((i : ι) → β i)) = some cx := by simp at hx
    cases this
  pcore_idem {x cx} hx := by
    have : (none : Option ((i : ι) → β i)) = some cx := by simp at hx
    cases this
  pcore_op_mono {x cx} hx y := by
    have : (none : Option ((i : ι) → β i)) = some cx := by simp at hx
    cases this

  -- Extend is done pointwise using the component extend
  extend {n f f1 f2} Hv He := by
    classical
    let F i := extend (Hv i) (He i)
    exact ⟨(fun i => (F i).1), (fun i => (F i).2.1),
      by intro i; exact (F i).2.2.1,
      by intro i; exact (F i).2.2.2.1,
      by intro i; exact (F i).2.2.2.2⟩

end Bluebell
