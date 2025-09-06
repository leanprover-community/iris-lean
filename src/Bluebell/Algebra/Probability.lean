import Bluebell.Algebra.Permission
import Bluebell.ProbabilityTheory.IndepProduct

namespace Bluebell

open ProbabilityTheory Iris MeasureTheory

/-! ## Base compatibility predicate (moved from PSpPm)

We define insensitivity of measurable spaces to changes on a set of coordinates,
and the compatibility predicate between a probability space over stores and a
permission map. -/

/-- Two stores `s t : α → V` are equal outside a set `S` of variables. -/
def setEqOutside {α V : Type*} (S : _root_.Set α) (s t : α → V) : Prop :=
  ∀ a, a ∉ S → s a = t a

/-- A measurable space on stores `(α → V)` is insensitive to changes on `S` if
every measurable set has the same membership for stores that are equal outside
`S`. This captures that the σ-algebra carries no information about variables in
`S`. -/
def MeasurableSpace.insensitive {α V : Type*} (m : MeasurableSpace (α → V)) (S : _root_.Set α) : Prop :=
  ∀ A, MeasurableSet[m] A → ∀ s t, setEqOutside (α := α) (V := V) S s t → (s ∈ A ↔ t ∈ A)

namespace MeasurableSpace

/-- Any measurable space is insensitive to changes on the empty set, since
`setEqOutside ∅ s t` implies `s = t`. -/
theorem insensitive_empty {α V : Type*} (m : MeasurableSpace (α → V)) :
    insensitive (α := α) (V := V) m (∅ : _root_.Set α) := by
  intro A _ s t h
  have hst : s = t := by
    funext a; exact h a (by simp)
  simp [hst]

/-- Antitonicity in the set: if `S ⊆ T` and the space is insensitive to `T`, it is insensitive to `S`. -/
theorem insensitive_anti {α V : Type*} (m : MeasurableSpace (α → V))
    {S T : _root_.Set α} (hST : S ⊆ T) :
    insensitive (α := α) (V := V) m T → insensitive (α := α) (V := V) m S := by
  intro _; sorry

/-- Closure under measurable-space sum: insensitivity combines by intersecting the sets. -/
theorem insensitive_sum_inter {α V : Type*}
    (m₁ m₂ : MeasurableSpace (α → V)) (S₁ S₂ : _root_.Set α) :
    insensitive (α := α) (V := V) m₁ S₁ →
    insensitive (α := α) (V := V) m₂ S₂ →
    insensitive (α := α) (V := V) (MeasurableSpace.sum m₁ m₂) (S₁ ∩ S₂) := by
  intro _ _; sorry

end MeasurableSpace

namespace ProbabilityTheory
namespace ProbabilitySpace

/-- Compatibility predicate at the `ProbabilitySpace` level.
It holds when the σ-algebra of `P` is insensitive to the set of variables where
`p` has zero permission (`DFrac.discard`). This corresponds to the paper’s
requirement that the probability space factorizes with a trivial component on
those variables. -/
def compatiblePerm {α V F : Type*} [UFraction F]
    (P : ProbabilitySpace (α → V)) (p : Permission α F) : Prop :=
  MeasurableSpace.insensitive (α := α) (V := V) (P.σAlg) {a | p a = DFrac.discard}

/-- If the independent product exists and the factors are compatible with `p₁,p₂`,
then the product is compatible with the pointwise permission op `p₁ • p₂`. -/
theorem compatiblePerm_indepProduct {α V F : Type*} [UFraction F]
    (P₁ P₂ : ProbabilitySpace (α → V)) (p₁ p₂ : Permission α F)
    (P : ProbabilitySpace (α → V)) :
    ProbabilityTheory.ProbabilitySpace.indepProduct P₁ P₂ = some P →
    compatiblePerm P₁ p₁ → compatiblePerm P₂ p₂ →
    compatiblePerm P (fun a => p₁ a • p₂ a) := by
  intro _ _ _; sorry

end ProbabilitySpace
end ProbabilityTheory

/-! ## Probability algebra wrappers (skeleton)

We will add lightweight wrappers like `PSp` here without committing to CMRA structure yet. -/

abbrev PSp (Ω : Type*) := WithTop (ProbabilityTheory.ProbabilitySpace Ω)

namespace PSp

variable {Ω : Type*}

/-- Combine two probability spaces using independent product lifted to `PSp` (partial). -/
noncomputable def indepMul (x y : PSp Ω) : PSp Ω :=
  match x, y with
  | WithTop.some x, WithTop.some y =>
      match ProbabilityTheory.ProbabilitySpace.indepProduct x y with
      | some z => WithTop.some z
      | none => none
  | _, _ => none

@[simp] theorem indepMul_none_left (y : PSp Ω) : indepMul (x := none) y = none := by
  cases y <;> rfl

@[simp] theorem indepMul_none_right (x : PSp Ω) : indepMul (y := none) x = none := by
  cases x <;> rfl

/-- Commutativity (API): `PSp.indepMul` is commutative. -/
theorem indepMul_comm (x y : PSp Ω) : indepMul x y = indepMul y x := by
  -- Delegates to `ProbabilitySpace.indepProduct_comm` case-wise.
  -- Proof deferred.
  cases x <;> cases y <;> simp [indepMul]
  · simp [ProbabilitySpace.indepProduct_comm]

/-- Associativity (API): `PSp.indepMul` is associative. -/
theorem indepMul_assoc (x y z : PSp Ω) :
    indepMul (indepMul x y) z = indepMul x (indepMul y z) := by
  -- Delegates to `ProbabilitySpace.indepProduct_assoc` case-wise.
  -- Proof deferred.
  cases x <;> cases y <;> cases z <;> simp [indepMul]
  · sorry

/-- Left unit (API): `1` acts as a left identity for `PSp.indepMul`. -/
@[simp]
theorem indepMul_one_left [Nonempty Ω] (x : PSp Ω) :
    indepMul (WithTop.some (1 : ProbabilityTheory.ProbabilitySpace Ω)) x = x := by
  -- Delegates to `ProbabilitySpace.indepProduct_one_left`.
  cases x <;> simp [indepMul]
  · rfl

/-- Right unit (API): `1` acts as a right identity for `PSp.indepMul`. -/
@[simp]
theorem indepMul_one_right [Nonempty Ω] (x : PSp Ω) :
    indepMul x (WithTop.some (1 : ProbabilityTheory.ProbabilitySpace Ω)) = x := by
  -- Delegates to `ProbabilitySpace.indepProduct_one_right`.
  cases x <;> simp [indepMul]
  · rfl

end PSp

/-! ### PSp-level compatibility wrapper and indepMul lemma -/

namespace PSp

open ProbabilityTheory ProbabilityTheory.ProbabilitySpace

variable {α V F : Type*} [UFraction F]

/-- Compatibility on `PSp` delegates to the `ProbabilitySpace` predicate. -/
def compatiblePerm (P : PSp (α → V)) (p : Permission α F) : Prop :=
  match P with
  | none => True
  | WithTop.some P => ProbabilityTheory.ProbabilitySpace.compatiblePerm P p

@[simp] lemma compatiblePerm_none (p : Permission α F) :
    compatiblePerm (α := α) (V := V) (F := F) (none) p := by
  simp [compatiblePerm]

@[simp] lemma compatiblePerm_some (P : ProbabilitySpace (α → V)) (p : Permission α F)
    (h : ProbabilitySpace.compatiblePerm P p) :
    compatiblePerm (α := α) (V := V) (F := F) (WithTop.some P) p := by
  simp [compatiblePerm, h]

/-- If `indepMul x y = some z` and the factors are compatible with `p₁,p₂`, then the product
is compatible with `p₁ • p₂`. -/
theorem compatiblePerm_indepMul (x y z : PSp (α → V)) (p₁ p₂ : Permission α F) :
    PSp.indepMul (Ω := α → V) x y = some z →
    compatiblePerm (α := α) (V := V) (F := F) x p₁ →
    compatiblePerm (α := α) (V := V) (F := F) y p₂ →
    compatiblePerm (α := α) (V := V) (F := F) z (fun a => p₁ a • p₂ a) := by
  -- case split on x,y; delegate to ProbabilitySpace.compatiblePerm_indepProduct on some/some
  intro hxy hx hy
  cases x <;> cases y <;> cases z <;> simp [PSp.indepMul, compatiblePerm] at hxy hx hy ⊢
  · rename_i P1 P2 Z
    -- Use the base lemma when the independent product exists
    rcases hprod : ProbabilityTheory.ProbabilitySpace.indepProduct P1 P2 with _|P
    · simp [PSp.indepMul, hprod] at hxy
    · simp [PSp.indepMul, hprod] at hxy; cases hxy
      exact ProbabilityTheory.ProbabilitySpace.compatiblePerm_indepProduct
        (α := α) (V := V) (F := F) P1 P2 p₁ p₂ Z hprod hx hy

end PSp

/-! ### Discrete OFE and CMRA/UCMRA instances for `PSp` -/

open Iris

variable {Ω : Type*}

@[simp] instance : COFE (PSp Ω) := COFE.ofDiscrete _ Eq_Equivalence

/--
CMRA instance for `PSp Ω` using independent product as the op.

We choose a unit-core (the core is always the trivial space), which requires the
existence of a trivial `ProbabilitySpace Ω`. This holds under `[Nonempty Ω]`.

The algebraic laws (assoc/comm/units) are delegated to the `PSp.indepMul_*`
lemmas in this file, which in turn will be proved from the `ProbabilitySpace`
API. For now, proofs can remain as statements where marked.
-/
noncomputable instance [Nonempty Ω] : CMRA (PSp Ω) where
  pcore _ := some (WithTop.some (1 : ProbabilityTheory.ProbabilitySpace Ω))
  op := PSp.indepMul
  ValidN _ _ := True
  Valid _ := True
  op_ne := by
    refine ⟨?_⟩
    intro _ _ y h
    cases h
    rfl
  pcore_ne := by
    intro _ _ _ _ cx hx
    cases hx
    refine ⟨WithTop.some (1 : ProbabilityTheory.ProbabilitySpace Ω), rfl, rfl⟩
  validN_ne _ := id
  valid_iff_validN := ⟨fun _ _ => True.intro, fun _ => True.intro⟩
  validN_succ := id
  validN_op_left := id
  assoc := by
    intro x y z
    -- discrete OFE: equivalence is equality
    simpa [CMRA.op] using (PSp.indepMul_assoc x y z).symm
  comm := by
    intro x y
    simpa [CMRA.op] using PSp.indepMul_comm x y
  pcore_op_left := by
    intro x cx hx
    cases hx
    -- left identity for indepMul
    simpa [CMRA.op] using PSp.indepMul_one_left x
  pcore_idem := by
    intro _ cx hx
    -- core of core is the same (unit core)
    cases hx
    rfl
  pcore_op_mono := by
    intro x cx hx y
    -- unit core monotonicity: choose cy = 1 and use indepMul_one_left on 1
    cases hx
    refine ⟨WithTop.some (1 : ProbabilityTheory.ProbabilitySpace Ω), ?_⟩
    -- pcore (x • y) = some 1 and op cx cy = 1 • 1 = 1
    have h11 : PSp.indepMul (WithTop.some (1 : ProbabilityTheory.ProbabilitySpace Ω))
        (WithTop.some (1 : ProbabilityTheory.ProbabilitySpace Ω))
        = WithTop.some (1 : ProbabilityTheory.ProbabilitySpace Ω) := by
      simpa using PSp.indepMul_one_left (WithTop.some (1 : ProbabilityTheory.ProbabilitySpace Ω))
    simp [PSp.indepMul]
  extend := by
    intro n x y₁ y₂ _ hxy
    -- trivial witnesses (discrete, validity = True)
    exact ⟨y₁, y₂, by cases hxy; rfl, rfl, rfl⟩

/-- UCMRA instance for `PSp Ω` (requires a unit), gated by `[Nonempty Ω]`. -/
noncomputable instance [Nonempty Ω] : UCMRA (PSp Ω) where
  unit := WithTop.some (1 : ProbabilityTheory.ProbabilitySpace Ω)
  unit_valid := True.intro
  unit_left_id := by
    intro x
    -- discrete OFE: equivalence is equality
    simpa [CMRA.op] using PSp.indepMul_one_left x
  pcore_unit := rfl

end Bluebell
