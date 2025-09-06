import Bluebell.Algebra.CMRA
import Bluebell.Algebra.Probability

namespace Bluebell

open Iris ProbabilityTheory MeasureTheory

/-! ## ProbabilitySpace × Permission skeleton (predicated product)

We use the generic predicated-product CMRA over `PSp (α → V)` and
`Permission α F`, with the predicate `PSp.compatiblePerm` declared in
`Bluebell/Algebra/Probability.lean`. -/

variable {α V F : Type*} [UFraction F]

/-! ### CompatibleRel instance for `compatiblePerm`

This lets us use the generic predicated-product CMRA on `PSp × Permission`.
-/
instance compatiblePerm_CompatibleRel {α V F : Type*} [Nonempty V] [UFraction F] :
    CMRA.CompatibleRel (α := PSp (α → V)) (β := Permission α F)
      (fun P p => PSp.compatiblePerm (α := α) (V := V) (F := F) P p) where
  op_closed {x₁ x₂ y₁ y₂} hx hy := by
    -- Case split on the `PSp` operands
    cases x₁ <;> cases x₂ <;> simp [PSp.indepMul, PSp.compatiblePerm] at hx hy ⊢
    · trivial
    · trivial
    · trivial
    · -- both are `some`; delegate to Probability-space lemma when product exists
      rename_i P1 P2
      cases hprod : ProbabilityTheory.ProbabilitySpace.indepProduct P1 P2 with
      | none =>
        split <;>
          simp [PSp.indepMul, PSp.compatiblePerm, hprod,
                ProbabilityTheory.ProbabilitySpace.compatiblePerm,
                MeasurableSpace.insensitive]
        sorry
      | some z =>
        split
        · trivial
        · have eqz : PSp.indepMul (Ω := α → V) (WithTop.some P1) (WithTop.some P2) = WithTop.some z := by
            simp [PSp.indepMul, hprod]
          -- simp [PSp.indepMul, hprod] at eqz
          rename_i P'' P' heq
          have := PSp.compatiblePerm_indepMul (α := α) (V := V) (F := F)
            (x := WithTop.some P1) (y := WithTop.some P2) (z := z)
            (p₁ := y₁) (p₂ := y₂) (by simp [eqz, Option.bind]) hx hy
          convert this
          simp [instCMRAPSpOfNonempty] at heq
          simp [WithTop.some] at eqz ⊢
          simp_all only
          rfl
  dist_closed {n x₁ x₂ y₁ y₂} hx hy h := by
    -- With discrete OFEs here, Dist collapses to equality, so we can rewrite
    cases hx
    have : y₁ = y₂ := funext_iff.mpr hy
    rw [← this]; exact h

abbrev PSpPm (α V F : Type*) [UFraction F] :=
  CMRA.ProdRel (α := PSp (α → V)) (β := Permission α F)
    (Φ := fun P p => PSp.compatiblePerm (α := α) (V := V) (F := F) P p)

namespace PSpPm

variable {α V F : Type*} [UFraction F]

/-- Lift a probability space to a `PSpPm` by pairing with the all-one permission. -/
def liftProb (μ : ProbabilityTheory.ProbabilitySpace (α → V)) : PSpPm α V F :=
  ⟨⟨WithTop.some μ, Permission.one (α := α) (F := F)⟩, by
    -- `{a | 1 = discard} = ∅`, then `insensitive_empty` gives compatibility
    have hS : {a | (Permission.one (α := α) (F := F)) a = DFrac.discard} = (∅ : _root_.Set α) := by
      ext a; simp [Permission.one]
    simp [CMRA.ProdRel, hS, PSp.compatiblePerm,
          ProbabilityTheory.ProbabilitySpace.compatiblePerm,
          MeasurableSpace.insensitive]
    sorry
  ⟩

end PSpPm

-- CMRA and OFE for `PSpPm` now derive from the generic `ProdRel` construction
-- once a `CMRA.CompatibleRel` instance for `compatiblePerm` is available.

-- No additional probability logic in this module; we use the
-- wrappers defined in `Bluebell/Algebra/Probability.lean`.

/-- The main model as indexed tuples of `PSpPm`.
We keep this as an abbreviation to functions; CMRA instances arise from the
dependent function-space instance once `CMRA (PSpPm α V F)` is available. -/
def IndexedPSpPm (I α V F : Type*) [UFraction F] := I → PSpPm α V F

namespace IndexedPSpPm

variable {I α V F : Type*} [UFraction F]

/-- Lift an indexed family of probability spaces to indexed `PSpPm`. -/
def liftProb (μ : I → ProbabilityTheory.ProbabilitySpace (α → V)) : IndexedPSpPm I α V F :=
  fun i => PSpPm.liftProb (α := α) (V := V) (F := F) (μ i)

-- Don't think we want this? Would lead to non-defeq diamond
-- with `Pi.hasLe`
noncomputable instance [Nonempty V] : CMRA (IndexedPSpPm I α V F) :=
  inferInstanceAs (CMRA (I → PSpPm α V F))

end IndexedPSpPm

end Bluebell
