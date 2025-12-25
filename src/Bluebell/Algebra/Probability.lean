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

/-- The trivial σ-algebra `⊥` is insensitive to any set, since only `∅` and `univ` are measurable,
and membership in these sets is independent of the function values. -/
theorem insensitive_bot {α V : Type*} (S : _root_.Set α) :
    insensitive (α := α) (V := V) ⊥ S := by
  intro A hA s t _
  -- In ⊥, only ∅ and univ are measurable
  simp only [MeasurableSpace.measurableSet_bot_iff] at hA
  cases hA with
  | inl h => simp [h]  -- A = ∅
  | inr h => simp [h]  -- A = univ

/-- Antitonicity in the set: if `S ⊆ T` and the space is insensitive to `T`, it is insensitive to `S`. -/
theorem insensitive_anti {α V : Type*} (m : MeasurableSpace (α → V))
    {S T : _root_.Set α} (hST : S ⊆ T) :
    insensitive (α := α) (V := V) m T → insensitive (α := α) (V := V) m S := by
  intro hT A hA s t hst
  apply hT A hA s t
  -- Need: setEqOutside T s t, i.e., ∀ a, a ∉ T → s a = t a
  -- From hst: setEqOutside S s t, i.e., ∀ a, a ∉ S → s a = t a
  -- Since S ⊆ T, we have T^c ⊆ S^c, so a ∉ T → a ∉ S
  intro a ha
  exact hst a (fun hs => ha (hST hs))

/-- Closure under measurable-space sum: insensitivity combines by intersecting the sets. -/
theorem insensitive_sum_inter {α V : Type*}
    (m₁ m₂ : MeasurableSpace (α → V)) (S₁ S₂ : _root_.Set α) :
    insensitive (α := α) (V := V) m₁ S₁ →
    insensitive (α := α) (V := V) m₂ S₂ →
    insensitive (α := α) (V := V) (MeasurableSpace.sum m₁ m₂) (S₁ ∩ S₂) := by
  intro h₁ h₂
  -- Get insensitivity to the intersection from each factor
  have h₁' : insensitive m₁ (S₁ ∩ S₂) := insensitive_anti m₁ _root_.Set.inter_subset_left h₁
  have h₂' : insensitive m₂ (S₁ ∩ S₂) := insensitive_anti m₂ _root_.Set.inter_subset_right h₂
  intro A hA s t hst
  -- Use generateFrom_induction on the sum σ-algebra
  simp only [MeasurableSpace.sum] at hA
  induction A, hA using MeasurableSpace.generateFrom_induction with
  | hC B hB _ =>
    -- B is in the generating set: MeasurableSet[m₁] ∪ MeasurableSet[m₂]
    cases hB with
    | inl hm₁ => exact h₁' B hm₁ s t hst
    | inr hm₂ => exact h₂' B hm₂ s t hst
  | empty => simp
  | compl B _ ih =>
    simp only [_root_.Set.mem_compl_iff]
    exact not_iff_not.mpr ih
  | iUnion f _ ih =>
    simp only [_root_.Set.mem_iUnion]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, (ih n).mp hn⟩
    · rintro ⟨n, hn⟩; exact ⟨n, (ih n).mpr hn⟩

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

/-- The op of two DFrac values is `discard` iff both are `discard`. -/
theorem DFrac.op_eq_discard_iff {F : Type*} [UFraction F] (x y : Iris.DFrac F) :
    x • y = Iris.DFrac.discard ↔ x = Iris.DFrac.discard ∧ y = Iris.DFrac.discard := by
  cases x <;> cases y <;> simp [Iris.DFrac_CMRA, Iris.op]

/-- If the independent product exists and the factors are compatible with `p₁,p₂`,
then the product is compatible with the pointwise permission op `p₁ • p₂`. -/
theorem compatiblePerm_indepProduct {α V F : Type*} [UFraction F]
    (P₁ P₂ : ProbabilitySpace (α → V)) (p₁ p₂ : Permission α F)
    (P : ProbabilitySpace (α → V)) :
    ProbabilityTheory.ProbabilitySpace.indepProduct P₁ P₂ = some P →
    compatiblePerm P₁ p₁ → compatiblePerm P₂ p₂ →
    compatiblePerm P (fun a => p₁ a • p₂ a) := by
  intro hprod h₁ h₂
  -- The zero-permission set of p₁ • p₂ is the intersection of zero-permission sets
  have hset : {a | p₁ a • p₂ a = Iris.DFrac.discard} =
      {a | p₁ a = Iris.DFrac.discard} ∩ {a | p₂ a = Iris.DFrac.discard} := by
    ext a
    simp only [_root_.Set.mem_setOf_eq, _root_.Set.mem_inter_iff, DFrac.op_eq_discard_iff]
  simp only [compatiblePerm, hset]
  -- Need to show: P.σAlg is insensitive to S₁ ∩ S₂
  -- where S₁ = {a | p₁ a = discard}, S₂ = {a | p₂ a = discard}
  -- and P.σAlg = P₁.σAlg.sum P₂.σAlg (from the indepProduct definition)
  -- Extract that indepProduct gives P₁.σAlg.sum P₂.σAlg
  simp only [ProbabilitySpace.indepProduct] at hprod
  split at hprod
  · -- The case where independent product exists
    cases hprod
    -- P.σAlg = P₁.σAlg.sum P₂.σAlg by construction
    simp only [ProbabilitySpace.σAlg]
    exact MeasurableSpace.insensitive_sum_inter P₁.σAlg P₂.σAlg _ _ h₁ h₂
  · -- The case where independent product doesn't exist - contradiction
    cases hprod

/-- Compatibility predicate for `PermissionRat` (paper-style rational permissions).
It holds when the σ-algebra of `P` is insensitive to the set of variables where
`p` has zero permission. -/
def compatiblePermRat {α V : Type*}
    (P : ProbabilitySpace (α → V)) (p : PermissionRat α) : Prop :=
  MeasurableSpace.insensitive (α := α) (V := V) (P.σAlg) {a | p a = 0}

/-- For non-negative rationals, sum is zero iff both summands are zero. -/
theorem NNRat.add_eq_zero_iff (a b : ℚ≥0) : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have ha : a ≤ a + b := le_add_of_nonneg_right b.coe_nonneg
    have hb : b ≤ a + b := le_add_of_nonneg_left a.coe_nonneg
    rw [h] at ha hb
    exact ⟨le_antisymm ha a.coe_nonneg, le_antisymm hb b.coe_nonneg⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- If the independent product exists and the factors are compatible with `p₁,p₂`,
then the product is compatible with the pointwise permission op `p₁ + p₂`. -/
theorem compatiblePermRat_indepProduct {α V : Type*}
    (P₁ P₂ : ProbabilitySpace (α → V)) (p₁ p₂ : PermissionRat α)
    (P : ProbabilitySpace (α → V)) :
    ProbabilityTheory.ProbabilitySpace.indepProduct P₁ P₂ = some P →
    compatiblePermRat P₁ p₁ → compatiblePermRat P₂ p₂ →
    compatiblePermRat P (PermissionRat.op p₁ p₂) := by
  intro hprod h₁ h₂
  -- The zero-permission set of p₁ + p₂ is the intersection of zero-permission sets
  have hset : {a | PermissionRat.op p₁ p₂ a = 0} = {a | p₁ a = 0} ∩ {a | p₂ a = 0} := by
    ext a
    simp only [_root_.Set.mem_setOf_eq, _root_.Set.mem_inter_iff, PermissionRat.op,
      NNRat.add_eq_zero_iff]
  simp only [compatiblePermRat, hset]
  -- Extract that indepProduct gives P₁.σAlg.sum P₂.σAlg
  simp only [ProbabilitySpace.indepProduct] at hprod
  split at hprod
  · cases hprod
    simp only [ProbabilitySpace.σAlg]
    exact MeasurableSpace.insensitive_sum_inter P₁.σAlg P₂.σAlg _ _ h₁ h₂
  · cases hprod

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
  cases x <;> cases y <;> cases z <;> simp [indepMul]
  · rename_i P₁ P₂ P₃
    -- Use indepProduct_assoc directly
    have assoc := ProbabilityTheory.ProbabilitySpace.indepProduct_assoc P₁ P₂ P₃
    -- Case split to handle the do-notation
    rcases h12 : P₁.indepProduct P₂ with _|P12
    · -- P₁.indepProduct P₂ = none
      simp [h12] at assoc ⊢
      rcases h23 : P₂.indepProduct P₃ with _|P23
      · rfl
      · simp [h23] at assoc ⊢
        rw [← assoc]
    · -- P₁.indepProduct P₂ = some P12
      simp [h12] at assoc ⊢
      rcases h23 : P₂.indepProduct P₃ with _|P23
      · simp [h23] at assoc ⊢
        rw [assoc]
      · simp [h23] at assoc ⊢
        rw [assoc]

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
    · simp [hprod] at hxy
    · simp [hprod] at hxy; cases hxy
      exact ProbabilityTheory.ProbabilitySpace.compatiblePerm_indepProduct
        (α := α) (V := V) (F := F) P1 P2 p₁ p₂ Z hprod hx hy

end PSp

/-! ### PSp-level compatibility wrapper for PermissionRat -/

namespace PSp

open ProbabilityTheory ProbabilityTheory.ProbabilitySpace

variable {α V : Type*}

/-- Compatibility on `PSp` for `PermissionRat`, delegates to the `ProbabilitySpace` predicate. -/
def compatiblePermRat (P : PSp (α → V)) (p : PermissionRat α) : Prop :=
  match P with
  | none => True
  | WithTop.some P => ProbabilityTheory.ProbabilitySpace.compatiblePermRat P p

@[simp] lemma compatiblePermRat_none (p : PermissionRat α) :
    compatiblePermRat (α := α) (V := V) (none) p := by
  simp [compatiblePermRat]

@[simp] lemma compatiblePermRat_some (P : ProbabilitySpace (α → V)) (p : PermissionRat α)
    (h : ProbabilitySpace.compatiblePermRat P p) :
    compatiblePermRat (α := α) (V := V) (WithTop.some P) p := by
  simp [compatiblePermRat, h]

/-- If `indepMul x y = some z` and the factors are compatible with `p₁,p₂`, then the product
is compatible with `p₁ + p₂` (pointwise addition via `PermissionRat.op`). -/
theorem compatiblePermRat_indepMul (x y z : PSp (α → V)) (p₁ p₂ : PermissionRat α) :
    PSp.indepMul (Ω := α → V) x y = some z →
    compatiblePermRat (α := α) (V := V) x p₁ →
    compatiblePermRat (α := α) (V := V) y p₂ →
    compatiblePermRat (α := α) (V := V) z (PermissionRat.op p₁ p₂) := by
  intro hxy hx hy
  cases x <;> cases y <;> cases z <;> simp [PSp.indepMul, compatiblePermRat] at hxy hx hy ⊢
  · rename_i P1 P2 Z
    rcases hprod : ProbabilityTheory.ProbabilitySpace.indepProduct P1 P2 with _|P
    · simp [hprod] at hxy
    · simp [hprod] at hxy; cases hxy
      exact ProbabilityTheory.ProbabilitySpace.compatiblePermRat_indepProduct
        (α := α) (V := V) P1 P2 p₁ p₂ Z hprod hx hy

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
