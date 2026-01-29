/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.Algebra.CMRA
import Iris.Algebra.OFE
import Iris.Algebra.Updates
import Iris.Algebra.LocalUpdates
import Iris.Std.CoPset
import Iris.Std.GSet

/-! # CoPset and GSet Resource Algebras

Reference: `iris/algebra/coPset.v`, `iris/algebra/gset.v`

Resource algebra (CMRA) instances for invariant mask sets, used by world
satisfaction to track enabled and disabled invariants.

Three CMRAs are defined:

- **`CoPset` union CMRA** — composition is set union, everything is valid, and every
  element is its own core. Used where masks combine freely (e.g. `ownI` tokens).
- **`CoPsetDisj` disjoint union CMRA** — composition requires disjointness and
  produces `invalid` otherwise. Used for `ownE` (enabled invariant tokens) where
  double-opening must be prevented: `ownE {[i]} ∗ ownE {[i]}` is invalid.
- **`GSetDisj` disjoint union CMRA** — same disjointness-enforcing pattern for
  finite sets. Used for `ownD` (disabled invariant tokens).
-/

namespace Iris

open OFE CMRA

/-! ## CoPset OFE + Union CMRA -/

instance : OFE CoPset := OFE.ofDiscrete (· = ·) ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
instance : OFE.Discrete CoPset where discrete_0 := id
instance : OFE.Leibniz CoPset where eq_of_eqv := id

/-- Union-based CMRA on `CoPset`. Always valid, idempotent core, unit is `∅`. -/
instance : CMRA CoPset where
  pcore := some
  op := (· ∪ ·)
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne _ _ _ h := Dist.of_eq (eq_of_eqv (discrete h) ▸ rfl)
  pcore_ne {_ y _ _} h := by
    -- core respects discrete equality
    rintro ⟨rfl⟩
    exact ⟨y, congrArg _ (eq_of_eqv (discrete h.symm)), .rfl⟩
  validN_ne _ _ := .intro
  valid_iff_validN := .symm <| forall_const Nat
  validN_succ := (·)
  validN_op_left := id
  assoc {x y z} := .of_eq (CoPset.union_assoc x y z).symm
  comm {x y} := .of_eq (CoPset.union_comm x y)
  pcore_op_left {_ _} := by
    -- core of union collapses by idempotence
    rintro ⟨rfl⟩
    exact .of_eq (CoPset.union_idem _)
  pcore_idem := by
    -- core is identity for union CMRA
    simp
  pcore_op_mono {_ _} := by
    -- monotonicity follows from unit core
    rintro ⟨rfl⟩ z
    exact ⟨z, .rfl⟩
  extend _ h := ⟨_, _, discrete h, .rfl, .rfl⟩

instance : CMRA.Discrete CoPset where discrete_valid := id

instance : UCMRA CoPset where
  unit := ∅
  unit_valid := trivial
  unit_left_id {x} := .of_eq (CoPset.empty_union x)
  pcore_unit := .symm .rfl

/-- CMRA inclusion coincides with subset for the union-based `CoPset` CMRA. -/
theorem coPset_included {x y : CoPset} : x ≼ y ↔ x ⊆ y := by
  -- inclusion matches subset for union-based CMRA
  constructor
  · rintro ⟨z, hz⟩; have := eq_of_eqv hz
    intro n hn; rw [this]; exact Or.inl hn
  · intro h
    obtain ⟨z, hz, _⟩ := CoPset.subseteq_disjoint_union h
    exact ⟨z, .of_eq hz⟩

/-- All frame-preserving updates are valid since `CoPset` validity is trivial. -/
theorem coPset_update (x y : CoPset) : x ~~> y := by
  -- all updates are valid since validity is trivial
  intro _ _ _; trivial

instance (x : CoPset) : CMRA.CoreId x where
  core_id := by
    -- core is identity for coPset
    simp [pcore]

/-! ## CoPset Disjoint Union CMRA -/

/-- Disjoint union wrapper for `CoPset`. Composing overlapping sets yields `invalid`. -/
inductive CoPsetDisj where
  | coPset : CoPset → CoPsetDisj
  | invalid : CoPsetDisj

instance : OFE CoPsetDisj := OFE.ofDiscrete (· = ·) ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
instance : OFE.Discrete CoPsetDisj where discrete_0 := id
instance : OFE.Leibniz CoPsetDisj where eq_of_eqv := id

/-- Helper: the disjoint op on CoPsetDisj. -/
noncomputable def CoPsetDisj.op' : CoPsetDisj → CoPsetDisj → CoPsetDisj
  | .coPset x, .coPset y =>
    if CoPset.Disjoint x y then .coPset (x ∪ y) else .invalid
  | _, _ => .invalid

private theorem CoPsetDisj.assoc_aux (x y z : CoPsetDisj) :
    op' (op' x y) z = op' x (op' y z) := by
  -- case split on validity and disjointness
  cases x <;> cases y <;> cases z <;> simp [op']
  rename_i x y z
  by_cases hxy : CoPset.Disjoint x y
  · by_cases hyz : CoPset.Disjoint y z
    · -- both disjoint, reduce to associativity of union
      by_cases hxyz : CoPset.Disjoint (x ∪ y) z
      · have hxyz' : CoPset.Disjoint x (y ∪ z) :=
          fun n ⟨hx, hyz'⟩ => hyz'.elim (hxy n ⟨hx, ·⟩) (hxyz n ⟨.inl hx, ·⟩)
        simp [hxy, hyz, hxyz, hxyz', CoPset.union_assoc]
      · have hxyz' : ¬CoPset.Disjoint x (y ∪ z) := by
          -- contradiction from disjointness transfer
          intro h; exact hxyz fun n ⟨hxy', hz⟩ =>
            hxy'.elim (fun hx => h n ⟨hx, .inr hz⟩) (hyz n ⟨·, hz⟩)
        simp [hxy, hyz, hxyz, hxyz']
    · -- right side is invalid; show left side invalid using subset
      have hxyz : ¬CoPset.Disjoint (x ∪ y) z := by
        -- if (x ∪ y) disjoint z, then y disjoint z
        intro h; apply hyz; intro n hn
        exact h n ⟨Or.inr hn.1, hn.2⟩
      simp [hxy, hyz, hxyz]
  · by_cases hyz : CoPset.Disjoint y z
    · -- left side invalid; show right side invalid using subset
      have hxyz : ¬CoPset.Disjoint x (y ∪ z) := by
        -- if x disjoint (y ∪ z), then x disjoint y
        intro h; apply hxy; intro n hn
        exact h n ⟨hn.1, Or.inl hn.2⟩
      simp [hxy, hyz, hxyz]
    · -- both sides are invalid
      simp [hxy, hyz]

private theorem CoPsetDisj.comm_aux (x y : CoPsetDisj) : op' x y = op' y x := by
  -- symmetry of disjoint union
  cases x <;> cases y <;> simp [op']
  rename_i x y
  by_cases hxy : CoPset.Disjoint x y
  · simp [hxy, CoPset.disjoint_comm.mp hxy, CoPset.union_comm]
  · have hyx : ¬CoPset.Disjoint y x := by
      -- disjointness is symmetric
      intro h; exact hxy (CoPset.disjoint_comm.mp h)
    simp [hxy, hyx]

/-- Disjoint union CMRA on `CoPsetDisj`. Valid when the composed sets are disjoint. -/
noncomputable instance : CMRA CoPsetDisj where
  pcore _ := some (.coPset ∅)
  op := CoPsetDisj.op'
  ValidN _ x := match x with | .coPset _ => True | .invalid => False
  Valid x := match x with | .coPset _ => True | .invalid => False
  op_ne.ne _ _ _ h := Dist.of_eq (eq_of_eqv (discrete h) ▸ rfl)
  pcore_ne _ := by
    -- core is the unit element
    rintro ⟨rfl⟩
    exact ⟨_, rfl, .rfl⟩
  validN_ne {_ x y} h hv := by
    -- validity respects discrete equality
    have := eq_of_eqv (discrete h); subst this; exact hv
  valid_iff_validN := .symm <| forall_const Nat
  validN_succ := (·)
  validN_op_left {x y} h := by
    -- op validity implies left validity by case analysis
    cases x <;> cases y <;> simp [CoPsetDisj.op'] at h ⊢
  assoc {x y z} := .of_eq (CoPsetDisj.assoc_aux x y z).symm
  comm {x y} := .of_eq (CoPsetDisj.comm_aux x y)
  pcore_op_left {x _} := by
    -- unit core acts as left identity
    rintro ⟨rfl⟩
    cases x with
    | coPset x =>
      -- disjoint union with empty yields the original element
      exact .of_eq (by
        -- reduce op' with empty and union identity
        simp [CoPsetDisj.op', CoPset.disjoint_empty_left, CoPset.empty_union])
    | invalid =>
      -- invalid absorbs the operation
      exact .of_eq (by
        -- op' with invalid collapses to invalid
        simp [CoPsetDisj.op'])
  pcore_idem := by
    -- idempotence of the core
    simp
  pcore_op_mono {_ _} := by
    -- core monotonicity follows from unit core
    rintro ⟨rfl⟩ _
    refine ⟨.coPset ∅, ?_⟩
    -- compute the core of the op and the op of cores
    apply Equiv.of_eq
    simp [CoPsetDisj.op', CoPset.disjoint_empty_left, CoPset.empty_union]
  extend _ h := ⟨_, _, discrete h, .rfl, .rfl⟩

instance : CMRA.Discrete CoPsetDisj where discrete_valid := id

noncomputable instance : UCMRA CoPsetDisj where
  unit := .coPset ∅
  unit_valid := trivial
  unit_left_id {x} := by
    -- unit acts as left identity
    change CoPsetDisj.op' (.coPset ∅) x ≡ x
    cases x with
    | coPset x =>
      -- disjoint union with empty yields the original element
      exact .of_eq (by
        -- simplify by disjointness with empty
        have hdisj : CoPset.Disjoint ∅ x := CoPset.disjoint_empty_left x
        simp [CoPsetDisj.op', hdisj, CoPset.empty_union])
    | invalid =>
      -- invalid absorbs the operation
      exact .of_eq (by
        -- op' with invalid collapses to invalid
        simp [CoPsetDisj.op'])
  pcore_unit := .symm .rfl

/-! ### CoPsetDisj Key Lemmas -/

/-- Composing disjoint sets produces their union. -/
theorem coPset_disj_union {x y : CoPset} (h : CoPset.Disjoint x y) :
    (CoPsetDisj.coPset x : CoPsetDisj) • CoPsetDisj.coPset y = CoPsetDisj.coPset (x ∪ y) := by
  -- unfold the disjoint op
  show CoPsetDisj.op' _ _ = _
  simp [CoPsetDisj.op', h]

/-- A composition of two `CoPsetDisj` values is valid iff the underlying sets are disjoint. -/
theorem coPset_disj_valid_op {x y : CoPset} :
    ✓ ((CoPsetDisj.coPset x : CoPsetDisj) • CoPsetDisj.coPset y) ↔ CoPset.Disjoint x y := by
  -- validity reduces to disjointness by case split
  change ✓ (CoPsetDisj.op' (CoPsetDisj.coPset x) (CoPsetDisj.coPset y)) ↔ _
  by_cases h : CoPset.Disjoint x y <;> simp [CoPsetDisj.op', h, CMRA.Valid]

/-- CMRA inclusion coincides with subset for the disjoint `CoPsetDisj` CMRA. -/
theorem coPset_disj_included {x y : CoPset} :
    (CoPsetDisj.coPset x : CoPsetDisj) ≼ CoPsetDisj.coPset y ↔ x ⊆ y := by
  -- inclusion matches subset for disjoint union CMRA
  constructor
  · rintro ⟨z, hz⟩
    have heq := eq_of_eqv hz
    -- heq : .coPset y = CoPsetDisj.op' (.coPset x) z
    change CoPsetDisj.coPset y = CoPsetDisj.op' (CoPsetDisj.coPset x) z at heq
    cases z with
    | coPset z =>
      -- reduce the op' equation by disjointness
      by_cases hd : CoPset.Disjoint x z
      · simp [CoPsetDisj.op', hd] at heq
        cases heq
        intro n hn; exact Or.inl hn
      · have : False := by
          -- contradiction: op' becomes invalid
          simp [CoPsetDisj.op', hd] at heq
        exact False.elim this
    | invalid =>
      -- invalid case contradicts the constructor equation
      have : False := by
        -- simplify to impossible constructor equality
        simp [CoPsetDisj.op'] at heq
      exact False.elim this
  · intro h
    obtain ⟨z, hz, hdisj⟩ := CoPset.subseteq_disjoint_union h
    exact ⟨.coPset z, .of_eq (by
      -- rewrite with the disjoint union decomposition
      rw [hz]; exact (coPset_disj_union hdisj).symm)⟩

/-! ## GSet Disjoint Union CMRA -/

/-- Disjoint union wrapper for `GSet`. Composing overlapping sets yields `invalid`. -/
inductive GSetDisj where
  | gset : GSet → GSetDisj
  | invalid : GSetDisj

instance : OFE GSetDisj := OFE.ofDiscrete (· = ·) ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
instance : OFE.Discrete GSetDisj where discrete_0 := id
instance : OFE.Leibniz GSetDisj where eq_of_eqv := id

/-- Helper: the disjoint op on GSetDisj. -/
noncomputable def GSetDisj.op' : GSetDisj → GSetDisj → GSetDisj
  | .gset x, .gset y =>
    if GSet.Disjoint x y then .gset (x ∪ y) else .invalid
  | _, _ => .invalid

private theorem GSetDisj.assoc_aux (x y z : GSetDisj) :
    op' (op' x y) z = op' x (op' y z) := by
  -- case split on disjointness flags
  cases x <;> cases y <;> cases z <;> simp [op']
  rename_i x y z
  by_cases hxy : GSet.Disjoint x y
  · by_cases hyz : GSet.Disjoint y z
    · -- both disjoint, reduce to associativity of union
      by_cases hxyz : GSet.Disjoint (x ∪ y) z
      · have hxyz' : GSet.Disjoint x (y ∪ z) :=
          fun n ⟨hx, hyz'⟩ => hyz'.elim (hxy n ⟨hx, ·⟩) (hxyz n ⟨.inl hx, ·⟩)
        simp [hxy, hyz, hxyz, hxyz', GSet.union_assoc]
      · have hxyz' : ¬GSet.Disjoint x (y ∪ z) := by
          -- contradiction from disjointness transfer
          intro h; exact hxyz fun n ⟨hxy', hz⟩ =>
            hxy'.elim (fun hx => h n ⟨hx, .inr hz⟩) (hyz n ⟨·, hz⟩)
        simp [hxy, hyz, hxyz, hxyz']
    · -- right side is invalid; show left side invalid using subset
      have hxyz : ¬GSet.Disjoint (x ∪ y) z := by
        -- if (x ∪ y) disjoint z, then y disjoint z
        intro h; apply hyz; intro n hn
        exact h n ⟨Or.inr hn.1, hn.2⟩
      simp [hxy, hyz, hxyz]
  · by_cases hyz : GSet.Disjoint y z
    · -- left side invalid; show right side invalid using subset
      have hxyz : ¬GSet.Disjoint x (y ∪ z) := by
        -- if x disjoint (y ∪ z), then x disjoint y
        intro h; apply hxy; intro n hn
        exact h n ⟨hn.1, Or.inl hn.2⟩
      simp [hxy, hyz, hxyz]
    · -- both sides are invalid
      simp [hxy, hyz]

private theorem GSetDisj.comm_aux (x y : GSetDisj) : op' x y = op' y x := by
  -- symmetry of disjoint union on GSet
  cases x <;> cases y <;> simp [op']
  rename_i x y
  by_cases hxy : GSet.Disjoint x y
  · simp [hxy, GSet.disjoint_comm.mp hxy, GSet.union_comm]
  · have hyx : ¬GSet.Disjoint y x := by
      -- disjointness is symmetric
      intro h; exact hxy (GSet.disjoint_comm.mp h)
    simp [hxy, hyx]

/-- Disjoint union CMRA on `GSetDisj`. Valid when the composed sets are disjoint. -/
noncomputable instance : CMRA GSetDisj where
  pcore _ := some (.gset ∅)
  op := GSetDisj.op'
  ValidN _ x := match x with | .gset _ => True | .invalid => False
  Valid x := match x with | .gset _ => True | .invalid => False
  op_ne.ne _ _ _ h := Dist.of_eq (eq_of_eqv (discrete h) ▸ rfl)
  pcore_ne _ := by
    -- core is the unit element
    rintro ⟨rfl⟩
    exact ⟨_, rfl, .rfl⟩
  validN_ne {_ x y} h hv := by
    -- validity respects discrete equality
    have := eq_of_eqv (discrete h); subst this; exact hv
  valid_iff_validN := .symm <| forall_const Nat
  validN_succ := (·)
  validN_op_left {x y} h := by
    -- op validity implies left validity by case analysis
    cases x <;> cases y <;> simp [GSetDisj.op'] at h ⊢
  assoc {x y z} := .of_eq (GSetDisj.assoc_aux x y z).symm
  comm {x y} := .of_eq (GSetDisj.comm_aux x y)
  pcore_op_left {x _} := by
    -- unit core acts as left identity
    rintro ⟨rfl⟩
    cases x with
    | gset x =>
      -- disjoint union with empty yields the original element
      exact .of_eq (by
        -- reduce op' with empty and union identity
        simp [GSetDisj.op', GSet.disjoint_empty_left, GSet.empty_union])
    | invalid =>
      -- invalid absorbs the operation
      exact .of_eq (by
        -- op' with invalid collapses to invalid
        simp [GSetDisj.op'])
  pcore_idem := by
    -- idempotence of the core
    simp
  pcore_op_mono {_ _} := by
    -- core monotonicity follows from unit core
    rintro ⟨rfl⟩ _
    refine ⟨.gset ∅, ?_⟩
    -- compute the core of the op and the op of cores
    apply Equiv.of_eq
    simp [GSetDisj.op', GSet.disjoint_empty_left, GSet.empty_union]
  extend _ h := ⟨_, _, discrete h, .rfl, .rfl⟩

instance : CMRA.Discrete GSetDisj where discrete_valid := id

noncomputable instance : UCMRA GSetDisj where
  unit := .gset ∅
  unit_valid := trivial
  unit_left_id {x} := by
    -- unit acts as left identity
    change GSetDisj.op' (.gset ∅) x ≡ x
    cases x with
    | gset x =>
      -- disjoint union with empty yields the original element
      exact .of_eq (by
        -- simplify by disjointness with empty
        have hdisj : GSet.Disjoint ∅ x := GSet.disjoint_empty_left x
        simp [GSetDisj.op', hdisj, GSet.empty_union])
    | invalid =>
      -- invalid absorbs the operation
      exact .of_eq (by
        -- op' with invalid collapses to invalid
        simp [GSetDisj.op'])
  pcore_unit := .symm .rfl

/-! ### GSetDisj Key Lemmas -/

/-- Composing disjoint sets produces their union. -/
theorem gset_disj_union {x y : GSet} (h : GSet.Disjoint x y) :
    (GSetDisj.gset x : GSetDisj) • GSetDisj.gset y = GSetDisj.gset (x ∪ y) := by
  -- unfold the disjoint op
  show GSetDisj.op' _ _ = _
  simp [GSetDisj.op', h]

/-- A composition of two `GSetDisj` values is valid iff the underlying sets are disjoint. -/
theorem gset_disj_valid_op {x y : GSet} :
    ✓ ((GSetDisj.gset x : GSetDisj) • GSetDisj.gset y) ↔ GSet.Disjoint x y := by
  -- validity reduces to disjointness by case split
  change ✓ (GSetDisj.op' (GSetDisj.gset x) (GSetDisj.gset y)) ↔ _
  by_cases h : GSet.Disjoint x y <;> simp [GSetDisj.op', h, CMRA.Valid]

/-- CMRA inclusion coincides with subset for the disjoint `GSetDisj` CMRA. -/
theorem gset_disj_included {x y : GSet} :
    (GSetDisj.gset x : GSetDisj) ≼ GSetDisj.gset y ↔ x ⊆ y := by
  -- inclusion matches subset for disjoint union CMRA
  constructor
  · rintro ⟨z, hz⟩
    have heq := eq_of_eqv hz
    -- rewrite the op in the equality to the disjoint op'
    change GSetDisj.gset y = GSetDisj.op' (GSetDisj.gset x) z at heq
    cases z with
    | gset z =>
      -- reduce the op' equation by disjointness
      by_cases hd : GSet.Disjoint x z
      · simp [GSetDisj.op', hd] at heq
        cases heq
        intro n hn; exact Or.inl hn
      · have : False := by
          -- contradiction: op' becomes invalid
          simp [GSetDisj.op', hd] at heq
        exact False.elim this
    | invalid =>
      -- invalid case contradicts the constructor equation
      have : False := by
        -- simplify to impossible constructor equality
        simp [GSetDisj.op'] at heq
      exact False.elim this
  · intro h
    obtain ⟨z, hz, hdisj⟩ := GSet.subseteq_disjoint_union h
    exact ⟨.gset z, .of_eq (by
      -- rewrite with the disjoint union decomposition
      rw [hz]; exact (gset_disj_union hdisj).symm)⟩

end Iris
