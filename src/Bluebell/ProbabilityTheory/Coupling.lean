/-
Copyright (c) 2025 Verified zkEVM contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Coupling for probability distributions

-/

universe u

noncomputable section

namespace PMF

variable {α β : Type*}

class IsCoupling (c : PMF (α × β)) (p : PMF α) (q : PMF β) where
  map_fst : c.map Prod.fst = p
  map_snd : c.map Prod.snd = q

def Coupling (p : PMF α) (q : PMF β) :=
  { c : PMF (α × β) // IsCoupling c p q }

end PMF

/-- Subprobability distribution. -/
@[reducible]
def SPMF : Type u → Type u := OptionT PMF

namespace SPMF

variable {α β : Type u}

instance : Monad SPMF := inferInstance

instance : LawfulMonad SPMF := inferInstance

-- instance : Alternative SPMF := inferInstance

instance : FunLike (SPMF α) (Option α) ENNReal :=
  inferInstanceAs (FunLike (PMF (Option α)) (Option α) ENNReal)

-- instance : MonadLift PMF SPMF := inferInstance

-- instance : LawfulMonadLift PMF SPMF := inferInstance

-- instance : LawfulFailure SPMF := inferInstance

theorem pure_eq_pmf_pure {a : α} : (pure a : SPMF α) = PMF.pure a := by
  simp [pure, liftM, OptionT.pure, monadLift, MonadLift.monadLift, OptionT.lift, PMF.instMonad]

theorem bind_eq_pmf_bind {p : SPMF α} {f : α → SPMF β} :
    (p >>= f) = PMF.bind p (fun a => match a with | some a' => f a' | none => PMF.pure none) := by
  simp [bind, OptionT.bind, PMF.instMonad, OptionT.mk]
  rfl

@[ext]
class IsCoupling (c : SPMF (α × β)) (p : SPMF α) (q : SPMF β) : Prop where
  map_fst : Prod.fst <$> c = p
  map_snd : Prod.snd <$> c = q

def Coupling (p : SPMF α) (q : SPMF β) :=
  { c : SPMF (α × β) // IsCoupling c p q }

-- Interaction between `Coupling` and `pure` / `bind`

example (f g : α → β) (h : f = g) : ∀ x, f x = g x := by exact fun x ↦ congrFun h x

/-- The coupling of two pure values must be the pure pair of those values -/
theorem IsCoupling.pure_iff {α β : Type u} {a : α} {b : β} {c : SPMF (α × β)} :
    IsCoupling c (pure a) (pure b) ↔ c = pure (a, b) := by
  constructor
  · intro ⟨h1, h2⟩
    have h1r := congrArg OptionT.run h1
    have h2r := congrArg OptionT.run h2
    rw [OptionT.run_map] at h1r
    rw [OptionT.run_map] at h2r
    simp only [OptionT.run_pure] at h1r h2r
    rw [PMF.monad_map_eq_map] at h1r h2r
    -- h1r : PMF.map (Option.map Prod.fst) (OptionT.run c) = PMF.pure (some a)
    -- h2r : PMF.map (Option.map Prod.snd) (OptionT.run c) = PMF.pure (some b)
    -- Support of c must be {some (a, b)}
    have hsupp : (OptionT.run c).support ⊆ {some (a, b)} := by
      intro x hx
      simp only [Set.mem_singleton_iff]
      have hfst_supp : Option.map Prod.fst x ∈ (PMF.map (Option.map Prod.fst) (OptionT.run c)).support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨x, hx, rfl⟩
      rw [h1r] at hfst_supp
      have hsnd_supp : Option.map Prod.snd x ∈ (PMF.map (Option.map Prod.snd) (OptionT.run c)).support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨x, hx, rfl⟩
      rw [h2r] at hsnd_supp
      have hfst_eq : Option.map Prod.fst x = some a :=
        (PMF.mem_support_pure_iff (some a) (Option.map Prod.fst x)).mp hfst_supp
      have hsnd_eq : Option.map Prod.snd x = some b :=
        (PMF.mem_support_pure_iff (some b) (Option.map Prod.snd x)).mp hsnd_supp
      cases x with
      | none => simp at hfst_eq
      | some p =>
        simp at hfst_eq hsnd_eq
        exact congr_arg some (Prod.ext hfst_eq hsnd_eq)
    -- c.support is nonempty, so c.support = {some (a, b)}
    have hsupp_eq : (OptionT.run c).support = {some (a, b)} := by
      apply Set.Subset.antisymm hsupp
      intro x hx; simp at hx; subst hx
      rcases (OptionT.run c).support_nonempty with ⟨y, hy⟩
      have := hsupp hy; simp at this; subst this; exact hy
    have hval : (OptionT.run c) (some (a, b)) = 1 := (PMF.apply_eq_one_iff _ _).mpr hsupp_eq
    -- Conclude by ext
    show OptionT.run c = OptionT.run (pure (a, b))
    rw [OptionT.run_pure]
    ext x
    change (OptionT.run c) x = (PMF.pure (some (a, b))) x
    rw [PMF.pure_apply]
    cases x with
    | none =>
      simp only [reduceCtorEq, ↓reduceIte]
      have : none ∉ (OptionT.run c).support := by rw [hsupp_eq]; simp
      rwa [PMF.mem_support_iff, not_not] at this
    | some p =>
      by_cases h : p = (a, b)
      · subst h; simp [hval]
      · simp only [Option.some.injEq, h, ↓reduceIte]
        have : some p ∉ (OptionT.run c).support := by rw [hsupp_eq]; simp [h]
        rwa [PMF.mem_support_iff, not_not] at this
  · intro h; constructor <;> simp [h]

theorem IsCoupling.none_iff {α β : Type u} {c : SPMF (α × β)} :
    IsCoupling c (failure : SPMF α) (failure : SPMF β) ↔ c = failure := by
  simp [failure]
  constructor
  · intro ⟨h1, _⟩
    -- h1 : Prod.fst <$> c = OptionT.fail, suffices to show c = OptionT.fail
    have h1r := congrArg OptionT.run h1
    rw [OptionT.run_map] at h1r
    -- h1r : PMF.map (Option.map Prod.fst) (OptionT.run c) = OptionT.run OptionT.fail
    rw [PMF.monad_map_eq_map] at h1r
    -- Support of c must be {none}
    have hsupp : (OptionT.run c).support ⊆ {none} := by
      intro x hx
      simp only [Set.mem_singleton_iff]
      have hfst_supp : Option.map Prod.fst x ∈ (PMF.map (Option.map Prod.fst) (OptionT.run c)).support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨x, hx, rfl⟩
      rw [h1r] at hfst_supp
      have := (PMF.mem_support_pure_iff _ _).mp hfst_supp
      cases x with
      | none => rfl
      | some _ => simp at this
    have hsupp_eq : (OptionT.run c).support = {none} := by
      apply Set.Subset.antisymm hsupp
      intro x hx; simp at hx; subst hx
      rcases (OptionT.run c).support_nonempty with ⟨y, hy⟩
      have := hsupp hy; simp at this; subst this; exact hy
    show OptionT.run c = OptionT.run OptionT.fail
    ext x
    change (OptionT.run c) x = (PMF.pure none) x
    rw [PMF.pure_apply]
    cases x with
    | none =>
      have := (PMF.apply_eq_one_iff _ _).mpr hsupp_eq
      simp [this]
    | some p =>
      have : some p ∉ (OptionT.run c).support := by rw [hsupp_eq]; simp
      rw [PMF.mem_support_iff, not_not] at this
      simp [this]
  · intro h; subst h; constructor <;> { ext x; simp [OptionT.fail] }

/-- Main theorem about coupling and bind operations -/
theorem IsCoupling.bind {α₁ α₂ β₁ β₂ : Type u}
    {p : SPMF α₁} {q : SPMF α₂} {f : α₁ → SPMF β₁} {g : α₂ → SPMF β₂}
    (c : Coupling p q) (d : (a₁ : α₁) → (a₂ : α₂) → SPMF (β₁ × β₂))
    (h : ∀ (a₁ : α₁) (a₂ : α₂), c.1.1 (some (a₁, a₂)) ≠ 0 → IsCoupling (d a₁ a₂) (f a₁) (g a₂)) :
    IsCoupling (c.1 >>= λ (p : α₁ × α₂) => d p.1 p.2) (p >>= f) (q >>= g) := by
  obtain ⟨hc₁, hc₂⟩ := c.2
  -- Helper: bind on SPMF is determined by values on support
  have bind_eq_of_support : ∀ {γ : Type u} (m : SPMF (α₁ × α₂)) (k₁ k₂ : α₁ × α₂ → SPMF γ),
      (∀ a₁ a₂, m.1 (some (a₁, a₂)) ≠ 0 → k₁ (a₁, a₂) = k₂ (a₁, a₂)) →
      (m >>= k₁) = (m >>= k₂) := by
    intro γ m k₁ k₂ hk
    show OptionT.run (m >>= k₁) = OptionT.run (m >>= k₂)
    simp only [OptionT.run_bind]
    -- Goal: Option.elimM m.run (pure none) (OptionT.run ∘ k₁) = ... k₂
    -- Show the continuations fed to Option.elimM agree on support
    suffices h : ∀ x, m.1 x ≠ 0 →
        x.elim (pure none) (fun ab => OptionT.run (k₁ ab)) =
        x.elim (pure none) (fun ab => OptionT.run (k₂ ab)) by
      simp only [Option.elimM]
      ext y
      show (PMF.bind (OptionT.run m) fun opt => opt.elim (pure none) fun x => OptionT.run (k₁ x)) y =
           (PMF.bind (OptionT.run m) fun opt => opt.elim (pure none) fun x => OptionT.run (k₂ x)) y
      simp only [PMF.bind_apply]
      congr 1; ext x
      by_cases hx : m.1 x = 0
      · rw [show (OptionT.run m) x = 0 from hx]; simp
      · congr 1; exact congrFun (congrArg DFunLike.coe (h x hx)) y
    intro x hx
    cases x with
    | none => rfl
    | some ab => exact congrArg OptionT.run (hk ab.1 ab.2 hx)
  constructor
  · rw [map_bind]
    conv_rhs => rw [← hc₁, seq_bind_eq]
    apply bind_eq_of_support
    intro a₁ a₂ hne
    simp only [Function.comp]
    exact (h a₁ a₂ hne).map_fst
  · rw [map_bind]
    conv_rhs => rw [← hc₂, seq_bind_eq]
    apply bind_eq_of_support
    intro a₁ a₂ hne
    simp only [Function.comp]
    exact (h a₁ a₂ hne).map_snd

/-- Existential version of `IsCoupling.bind` -/
theorem IsCoupling.exists_bind {α₁ α₂ β₁ β₂ : Type u}
    {p : SPMF α₁} {q : SPMF α₂} {f : α₁ → SPMF β₁} {g : α₂ → SPMF β₂}
    (c : Coupling p q)
    (h : ∀ (a₁ : α₁) (a₂ : α₂), ∃ (d : SPMF (β₁ × β₂)), IsCoupling d (f a₁) (g a₂)) :
    ∃ (d : SPMF (β₁ × β₂)), IsCoupling d (p >>= f) (q >>= g) :=
  let d : (a₁ : α₁) → (a₂ : α₂) → SPMF (β₁ × β₂) :=
    fun a₁ a₂ => Classical.choose (h a₁ a₂)
  let hd : ∀ (a₁ : α₁) (a₂ : α₂), c.1.1 (some (a₁, a₂)) ≠ 0 → IsCoupling (d a₁ a₂) (f a₁) (g a₂) :=
    fun a₁ a₂ _ => Classical.choose_spec (h a₁ a₂)
  ⟨c.1 >>= λ (p : α₁ × α₂) => d p.1 p.2, IsCoupling.bind c d hd⟩

end SPMF

end

/-! ## Coupling API for program logics (PMF and SPMF)

This section provides a usable coupling/lifting API for discrete distributions (PMF)
and subprobabilities (SPMF). The API is meant to support relational program logics
such as PRHL and Bluebell. Where proofs are nontrivial, we provide lemma statements
with `sorry` placeholders and clear docstrings to guide future completion. -/

namespace PMF

variable {α β γ δ : Type u}

/-- A coupling `c` supports a relation `R` if all pairs with nonzero mass lie in `R`. -/
def IsCoupling.supports (c : PMF (α × β)) (R : Set (α × β)) : Prop :=
  ∀ x, c x ≠ 0 → x ∈ R

/-- Relational lifting: there exists a coupling supported in `R`. -/
def Lift (p : PMF α) (R : Set (α × β)) (q : PMF β) : Prop :=
  ∃ c, IsCoupling c p q ∧ IsCoupling.supports c R

/-- Map a coupling through functions on both sides. -/
theorem IsCoupling.map
    {c : PMF (α × β)} {p : PMF α} {q : PMF β}
    (hc : IsCoupling c p q) (f : α → γ) (g : β → δ) :
    IsCoupling (c.map (fun x => (f x.1, g x.2))) (p.map f) (q.map g) := by
  exact {
    map_fst := by
      rw [PMF.map_comp]
      have : Prod.fst ∘ (fun x => (f x.1, g x.2)) = f ∘ Prod.fst := by ext ⟨a, b⟩; rfl
      rw [this, ← PMF.map_comp]; congr 1; exact hc.map_fst
    map_snd := by
      rw [PMF.map_comp]
      have : Prod.snd ∘ (fun x => (f x.1, g x.2)) = g ∘ Prod.snd := by ext ⟨a, b⟩; rfl
      rw [this, ← PMF.map_comp]; congr 1; exact hc.map_snd
  }

/-- Lifting is preserved by post-processing functions, under relational image. -/
theorem Lift.map {p : PMF α} {q : PMF β} {R : Set (α × β)}
    (hpq : Lift p R q) (f : α → γ) (g : β → δ)
    (hR : ∀ a b, (a, b) ∈ R → (f a, g b) ∈ (Set.image (fun x : α × β => (f x.1, g x.2)) R)) :
    Lift (p.map f)
      (Set.image (fun x : α × β => (f x.1, g x.2)) R)
      (q.map g) := by
  rcases hpq with ⟨c, hc, hsupp⟩
  refine ⟨_, IsCoupling.map (hc) f g, ?_⟩
  intro y hy
  have hmem : y ∈ (PMF.map (fun x => (f x.1, g x.2)) c).support := (PMF.mem_support_iff _ y).mpr hy
  obtain ⟨⟨a, b⟩, hab, hfg⟩ := (PMF.mem_support_map_iff _ c y).mp hmem
  subst hfg
  exact hR a b (hsupp _ ((PMF.mem_support_iff c (a, b)).mp hab))

/-- Symmetry: swap a coupling. -/
theorem IsCoupling.symm {c : PMF (α × β)} {p : PMF α} {q : PMF β}
    (hc : IsCoupling c p q) :
    IsCoupling (c.map Prod.swap) q p := by
  exact {
    map_fst := by
      rw [PMF.map_comp]
      have : Prod.fst ∘ Prod.swap = @Prod.snd α β := by ext ⟨a, b⟩; rfl
      rw [this]; exact hc.map_snd
    map_snd := by
      rw [PMF.map_comp]
      have : Prod.snd ∘ Prod.swap = @Prod.fst α β := by ext ⟨a, b⟩; rfl
      rw [this]; exact hc.map_fst
  }

/-- Symmetry for relational lifting. -/
theorem Lift.symm {p : PMF α} {q : PMF β} {R : Set (α × β)}
    (hpq : Lift p R q) : Lift q (Prod.swap ⁻¹' R) p := by
  rcases hpq with ⟨c, hc, hsupp⟩
  refine ⟨_, (IsCoupling.symm hc), ?_⟩
  intro y hy
  simp only [Set.mem_preimage]
  have hmem : y ∈ (PMF.map Prod.swap c).support := (PMF.mem_support_iff _ y).mpr hy
  obtain ⟨⟨a, b⟩, hab, hswap⟩ := (PMF.mem_support_map_iff Prod.swap c y).mp hmem
  simp only [Prod.swap_prod_mk] at hswap
  obtain ⟨rfl, rfl⟩ := hswap
  exact hsupp _ ((PMF.mem_support_iff c (a, b)).mp hab)

/-- Product (independent) coupling: pair samples of `p` and `q`. -/
noncomputable def prodMap (p : PMF α) (q : PMF β) : PMF (α × β) :=
  p.bind (fun a => (q.map (fun b => (a, b))))

theorem IsCoupling.prod (p : PMF α) (q : PMF β) :
    IsCoupling (prodMap p q) p q := by
  constructor
  · simp [prodMap, PMF.map_bind, PMF.map_comp]
  · simp [prodMap, PMF.map_bind, PMF.map_comp, PMF.map_id]

/-- Top lifting: every pair is allowed. -/
theorem Lift.top (p : PMF α) (q : PMF β) : Lift p (Set.univ : Set (α × β)) q := by
  refine ⟨_, IsCoupling.prod p q, ?_⟩
  intro x hx; simp

/-- Graph lifting for a deterministic post-processing `f`. -/
theorem Lift.graph (p : PMF α) (f : α → β) :
    Lift p {x : α × β | x.2 = f x.1} (p.map f) := by
  refine ⟨p.map (fun a => (a, f a)), ?_, ?_⟩
  · constructor
    · rw [PMF.map_comp]
      have : Prod.fst ∘ (fun a => (a, f a)) = id := by ext a; rfl
      rw [this, PMF.map_id]
    · rw [PMF.map_comp]; congr 1
  · intro ⟨a, b⟩ hx
    simp only [Set.mem_setOf_eq]
    have hmem : (a, b) ∈ (PMF.map (fun a => (a, f a)) p).support := (PMF.mem_support_iff _ _).mpr hx
    obtain ⟨a', ha', heq⟩ := (PMF.mem_support_map_iff _ p _).mp hmem
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rfl

/-- Pure/pure coupling under a relation. -/
theorem Lift.pure_pure {a : α} {b : β} {R : Set (α × β)}
    (h : (a, b) ∈ R) : Lift (PMF.pure a) R (PMF.pure b) := by
  refine ⟨PMF.pure (a, b), ?_, ?_⟩
  · constructor <;> simp [PMF.map]
  · intro x hx; simp_all

/-- Monotonicity of lifting in the relation. -/
theorem Lift.mono {p : PMF α} {q : PMF β} {R S : Set (α × β)}
    (hpq : Lift p R q) (hRS : R ⊆ S) : Lift p S q := by
  rcases hpq with ⟨c, hc, hR⟩
  exact ⟨c, hc, fun x hx => hRS (hR x hx)⟩

end PMF

namespace SPMF

variable {α β γ δ : Type u}

/-- A coupling `c` supports a relation `R` if all nonzero `some (a,b)` mass lies in `R`.
We ignore the `none` mass (failure). -/
def IsCoupling.supports (c : SPMF (α × β)) (R : Set (α × β)) : Prop :=
  ∀ x, c (some x) ≠ 0 → x ∈ R

/-- Relational lifting for subprobabilities. -/
def Lift (p : SPMF α) (R : Set (α × β)) (q : SPMF β) : Prop :=
  ∃ c, IsCoupling c p q ∧ IsCoupling.supports c R

/-- Map a coupling through functions on both sides. -/
theorem IsCoupling.map
    {c : SPMF (α × β)} {p : SPMF α} {q : SPMF β}
    (hc : IsCoupling c p q) (f : α → γ) (g : β → δ) :
    IsCoupling (Prod.map f g <$> c) (f <$> p) (g <$> q) := by
  constructor
  · simp only [← comp_map]
    have : Prod.fst ∘ Prod.map f g = f ∘ Prod.fst := by ext ⟨a, b⟩; rfl
    rw [this, comp_map]; congr 1; exact hc.map_fst
  · simp only [← comp_map]
    have : Prod.snd ∘ Prod.map f g = g ∘ Prod.snd := by ext ⟨a, b⟩; rfl
    rw [this, comp_map]; congr 1; exact hc.map_snd

/-- Symmetry for SPMF couplings. -/
theorem IsCoupling.symm {c : SPMF (α × β)} {p : SPMF α} {q : SPMF β}
    (hc : IsCoupling c p q) :
    IsCoupling (Prod.swap.{u, u} <$> c) q p := by
  constructor
  · simp only [← comp_map]
    have : Prod.fst ∘ @Prod.swap α β = Prod.snd := by ext ⟨a, b⟩; rfl
    rw [this]; exact hc.map_snd
  · simp only [← comp_map]
    have : Prod.snd ∘ @Prod.swap α β = Prod.fst := by ext ⟨a, b⟩; rfl
    rw [this]; exact hc.map_fst

/-- Monadic bind rule for relational lifting (PRHL bind). -/
theorem Lift.bind {p : SPMF α} {q : SPMF β} {R : Set (α × β)}
    (hpq : Lift p R q)
    (F : α → SPMF γ) (G : β → SPMF δ)
    (hpt : ∀ a b, (a, b) ∈ R → Lift (F a) (Set.univ : Set (γ × δ)) (G b)) :
    Lift (p >>= F) (Set.univ : Set (γ × δ)) (q >>= G) := by
  rcases hpq with ⟨c, hc, hR⟩
  -- Build pointwise couplings using Classical.choose
  classical
  let d : α → β → SPMF (γ × δ) := fun a b =>
    if hab : (a, b) ∈ R then Classical.choose (hpt a b hab)
    else failure  -- dummy; never used since c (some (a, b)) = 0 for (a, b) ∉ R
  have hd : ∀ a b, (⟨c, hc⟩ : Coupling p q).1.1 (some (a, b)) ≠ 0 →
      IsCoupling (d a b) (F a) (G b) := by
    intro a b hne
    have hab : (a, b) ∈ R := hR (a, b) hne
    simp only [d, dif_pos hab]
    exact (Classical.choose_spec (hpt a b hab)).1
  exact ⟨(⟨c, hc⟩ : Coupling p q).1 >>= (fun ab => d ab.1 ab.2),
    IsCoupling.bind ⟨c, hc⟩ d hd, fun _ _ => Set.mem_univ _⟩

end SPMF
