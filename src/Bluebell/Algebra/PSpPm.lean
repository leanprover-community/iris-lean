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
    cases x₁ <;> cases x₂ <;> simp [PSp.compatiblePerm] at hx hy ⊢
    · trivial
    · trivial
    · trivial
    · -- both are `some`; delegate to Probability-space lemma when product exists
      rename_i P1 P2
      cases hprod : ProbabilityTheory.ProbabilitySpace.indepProduct P1 P2 with
      | none =>
        -- When indepProduct fails, PSp.indepMul returns none (⊤), which is compatible with any perm
        simp only [CMRA.op, PSp.indepMul, hprod]
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
    simp only [PSp.compatiblePerm, ProbabilityTheory.ProbabilitySpace.compatiblePerm, hS]
    exact MeasurableSpace.insensitive_empty μ.σAlg
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

/-! ## ProbabilitySpace × PermissionRat (paper-style, with UCMRA)

We define the predicated product using `PermissionRat α` instead of `Permission α F`.
This gives us a UCMRA instance since both `PSp` and `PermissionRat` have units. -/

/-! ### CompatibleRel instance for `compatiblePermRat` -/

instance compatiblePermRat_CompatibleRel {α V : Type*} [Nonempty V] :
    CMRA.CompatibleRel (α := PSp (α → V)) (β := PermissionRat α)
      (fun P p => PSp.compatiblePermRat (α := α) (V := V) P p) where
  op_closed {x₁ x₂ y₁ y₂} hx hy := by
    cases x₁ <;> cases x₂ <;> simp [PSp.compatiblePermRat] at hx hy ⊢
    · trivial
    · trivial
    · trivial
    · rename_i P1 P2
      cases hprod : ProbabilityTheory.ProbabilitySpace.indepProduct P1 P2 with
      | none =>
        -- When indepProduct fails, PSp.indepMul returns none (⊤), which is compatible with any perm
        simp only [CMRA.op, PSp.indepMul, hprod]
      | some z =>
        split
        · trivial
        · have eqz : PSp.indepMul (Ω := α → V) (WithTop.some P1) (WithTop.some P2) = WithTop.some z := by
            simp [PSp.indepMul, hprod]
          rename_i P'' P' heq
          have := PSp.compatiblePermRat_indepMul (α := α) (V := V)
            (x := WithTop.some P1) (y := WithTop.some P2) (z := z)
            (p₁ := y₁) (p₂ := y₂) (by simp [eqz, Option.bind]) hx hy
          convert this
          simp [instCMRAPSpOfNonempty] at heq
          simp [WithTop.some] at eqz ⊢
          simp_all only
          rfl
  dist_closed {n x₁ x₂ y₁ y₂} hx hy h := by
    cases hx
    have : y₁ = y₂ := OFE.eq_of_eqv (OFE.discrete hy)
    rw [← this]; exact h

/-- `PSpPmRat` as a structure for paper-style permissions with UCMRA instance.

This is a pair of `PSp (α → V)` and `PermissionRat α` satisfying compatibility.
Unlike `ProdRel`, this has a proper pcore for UCMRA. -/
structure PSpPmRat (α V : Type*) where
  psp : PSp (α → V)
  perm : PermissionRat α
  compat : PSp.compatiblePermRat (α := α) (V := V) psp perm

/-- The compatibility predicate holds at the units: the trivial probability space
(unit of PSp) is compatible with zero permissions (unit of PermissionRat). -/
theorem compatiblePermRat_unit_compat {α V : Type*} [Nonempty V] :
    PSp.compatiblePermRat (α := α) (V := V)
      (UCMRA.unit : PSp (α → V))
      (UCMRA.unit : PermissionRat α) := by
  -- UCMRA.unit for PSp is the trivial probability space with σ-algebra ⊥
  -- UCMRA.unit for PermissionRat is the zero function
  -- The trivial σ-algebra ⊥ is insensitive to any set (insensitive_bot)
  simp only [PSp.compatiblePermRat, ProbabilityTheory.ProbabilitySpace.compatiblePermRat]
  exact MeasurableSpace.insensitive_bot _

namespace PSpPmRat

variable {α V : Type*}

/-- Lift a probability space to a `PSpPmRat` by pairing with the all-one permission. -/
def liftProb (μ : ProbabilityTheory.ProbabilitySpace (α → V)) : PSpPmRat α V :=
  ⟨WithTop.some μ, PermissionRat.one (α := α), by
    have hS : {a | (PermissionRat.one (α := α)) a = 0} = (∅ : _root_.Set α) := by
      ext a; simp [PermissionRat.one]
    simp only [PSp.compatiblePermRat, ProbabilityTheory.ProbabilitySpace.compatiblePermRat, hS]
    exact MeasurableSpace.insensitive_empty μ.σAlg
  ⟩

/-- OFE instance for PSpPmRat (product OFE). -/
instance [Nonempty V] : OFE (PSpPmRat α V) where
  Equiv x y := OFE.Equiv x.psp y.psp ∧ OFE.Equiv x.perm y.perm
  Dist n x y := OFE.Dist n x.psp y.psp ∧ OFE.Dist n x.perm y.perm
  dist_eqv := {
    refl _ := ⟨OFE.Dist.rfl, OFE.Dist.rfl⟩
    symm h := ⟨OFE.Dist.symm h.1, OFE.Dist.symm h.2⟩
    trans h₁ h₂ := ⟨OFE.Dist.trans h₁.1 h₂.1, OFE.Dist.trans h₁.2 h₂.2⟩
  }
  equiv_dist := by
    intro x y
    constructor
    · intro h n; exact ⟨OFE.equiv_dist.mp h.1 n, OFE.equiv_dist.mp h.2 n⟩
    · intro h; exact ⟨OFE.equiv_dist.mpr (fun n => (h n).1), OFE.equiv_dist.mpr (fun n => (h n).2)⟩
  dist_lt := by
    intro n m x y h hnm
    exact ⟨OFE.dist_lt h.1 hnm, OFE.dist_lt h.2 hnm⟩

/-- CMRA instance for PSpPmRat with proper pcore for UCMRA. -/
noncomputable instance [Nonempty V] : CMRA (PSpPmRat α V) where
  pcore _ := some ⟨UCMRA.unit, UCMRA.unit, compatiblePermRat_unit_compat⟩
  op x y := ⟨x.psp • y.psp, x.perm • y.perm, CMRA.CompatibleRel.op_closed x.compat y.compat⟩
  ValidN n x := ✓{n} x.psp ∧ ✓{n} x.perm
  Valid x := ✓ x.psp ∧ ✓ x.perm
  op_ne {x} := {
    ne n y z h := ⟨h.1.op_r, h.2.op_r⟩
  }
  pcore_ne {n x y cx} _heq hpc := by
    -- pcore is constant, so pcore y = pcore x = some cx
    exact ⟨cx, hpc, OFE.Dist.rfl⟩
  validN_ne {n x y} H Hx := ⟨CMRA.validN_ne H.1 Hx.1, CMRA.validN_ne H.2 Hx.2⟩
  valid_iff_validN {x} := by
    constructor
    · intro h n; exact ⟨CMRA.valid_iff_validN.mp h.1 n, CMRA.valid_iff_validN.mp h.2 n⟩
    · intro h; exact ⟨CMRA.valid_iff_validN.mpr (fun n => (h n).1),
                      CMRA.valid_iff_validN.mpr (fun n => (h n).2)⟩
  validN_succ {x n} := by intro h; exact ⟨CMRA.validN_succ h.1, CMRA.validN_succ h.2⟩
  validN_op_left {n x y} := by intro h; exact ⟨CMRA.validN_op_left h.1, CMRA.validN_op_left h.2⟩
  assoc {x y z} := ⟨CMRA.assoc, CMRA.assoc⟩
  comm {x y} := ⟨CMRA.comm, CMRA.comm⟩
  pcore_op_left {x cx} hpc := by
    -- From hpc : pcore x = some cx, we get cx = the constant unit
    have hcx : cx = ⟨UCMRA.unit, UCMRA.unit, compatiblePermRat_unit_compat⟩ := Option.some.inj hpc.symm
    simp only [hcx]
    exact ⟨UCMRA.unit_left_id, UCMRA.unit_left_id⟩
  pcore_idem {x cx} hpc := by
    have hcx : cx = ⟨UCMRA.unit, UCMRA.unit, compatiblePermRat_unit_compat⟩ := Option.some.inj hpc.symm
    simp only [hcx]
    -- pcore cx = pcore x = some cx, so cx ≡ cx
    exact ⟨OFE.Equiv.rfl, OFE.Equiv.rfl⟩
  pcore_op_mono {x cx} hpc y := by
    have hcx : cx = ⟨UCMRA.unit, UCMRA.unit, compatiblePermRat_unit_compat⟩ := Option.some.inj hpc.symm
    -- pcore (x • y) = some unit, and cx = unit, so we take cy := cx
    refine ⟨cx, ?_⟩
    simp only [hcx]
    exact ⟨UCMRA.unit_left_id.symm, UCMRA.unit_left_id.symm⟩
  extend {n x y₁ y₂} Hv He := by
    -- Componentwise extend, then close the compatibility using dist_closed
    let E₁ := CMRA.extend (x := x.psp) (y₁ := y₁.psp) (y₂ := y₂.psp) Hv.1 He.1
    let E₂ := CMRA.extend (x := x.perm) (y₁ := y₁.perm) (y₂ := y₂.perm) Hv.2 He.2
    refine ⟨⟨E₁.1, E₂.1, ?_⟩, ⟨E₁.2.1, E₂.2.1, ?_⟩, ?_, ?_, ?_⟩
    · -- Compatibility for z₁: use dist_closed with y₁ ≡{n}≡ z₁
      exact CMRA.CompatibleRel.dist_closed E₁.2.2.2.1.symm E₂.2.2.2.1.symm y₁.compat
    · -- Compatibility for z₂: use dist_closed with y₂ ≡{n}≡ z₂
      exact CMRA.CompatibleRel.dist_closed E₁.2.2.2.2.symm E₂.2.2.2.2.symm y₂.compat
    · -- x ≡ z₁ • z₂
      exact ⟨E₁.2.2.1, E₂.2.2.1⟩
    · -- z₁ ≡{n}≡ y₁
      exact ⟨E₁.2.2.2.1, E₂.2.2.2.1⟩
    · -- z₂ ≡{n}≡ y₂
      exact ⟨E₁.2.2.2.2, E₂.2.2.2.2⟩

/-- UCMRA instance for PSpPmRat. -/
noncomputable instance [Nonempty V] : UCMRA (PSpPmRat α V) where
  unit := ⟨UCMRA.unit, UCMRA.unit, compatiblePermRat_unit_compat⟩
  unit_valid := ⟨UCMRA.unit_valid, UCMRA.unit_valid⟩
  unit_left_id {_} := ⟨UCMRA.unit_left_id, UCMRA.unit_left_id⟩
  pcore_unit := OFE.Equiv.rfl

end PSpPmRat

/-- The main model as indexed tuples of `PSpPmRat`.
This has a UCMRA instance since both components have units. -/
def IndexedPSpPmRat (I α V : Type*) := I → PSpPmRat α V

namespace IndexedPSpPmRat

variable {I α V : Type*}

/-- Lift an indexed family of probability spaces to indexed `PSpPmRat`. -/
def liftProb (μ : I → ProbabilityTheory.ProbabilitySpace (α → V)) : IndexedPSpPmRat I α V :=
  fun i => PSpPmRat.liftProb (α := α) (V := V) (μ i)

noncomputable instance [Nonempty V] : CMRA (IndexedPSpPmRat I α V) :=
  Bluebell.cmraFunUCMRA

noncomputable instance [Nonempty V] : UCMRA (IndexedPSpPmRat I α V) :=
  Bluebell.ucmraFun

end IndexedPSpPmRat

end Bluebell
