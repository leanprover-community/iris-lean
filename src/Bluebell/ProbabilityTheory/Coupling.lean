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
    simp [pure_eq_pmf_pure, liftM, monadLift, OptionT.instMonadLift, OptionT.lift, OptionT.mk] at h1 h2
    have : (x : Option α) → (Prod.fst <$> c) x = (some <$> PMF.pure a) x := by
      rw [h1]; intro x; congr
    sorry
  · intro h; constructor <;> simp [h]

theorem IsCoupling.none_iff {α β : Type u} {c : SPMF (α × β)} :
    IsCoupling c (failure : SPMF α) (failure : SPMF β) ↔ c = failure := by
  simp [failure]
  constructor
  · intro h; sorry
  · intro h; constructor <;> simp [h] <;> sorry

/-- Main theorem about coupling and bind operations -/
theorem IsCoupling.bind {α₁ α₂ β₁ β₂ : Type u}
    {p : SPMF α₁} {q : SPMF α₂} {f : α₁ → SPMF β₁} {g : α₂ → SPMF β₂}
    (c : Coupling p q) (d : (a₁ : α₁) → (a₂ : α₂) → SPMF (β₁ × β₂))
    (h : ∀ (a₁ : α₁) (a₂ : α₂), c.1.1 (some (a₁, a₂)) ≠ 0 → IsCoupling (d a₁ a₂) (f a₁) (g a₂)) :
    IsCoupling (c.1 >>= λ (p : α₁ × α₂) => d p.1 p.2) (p >>= f) (q >>= g) := by
  obtain ⟨hc₁, hc₂⟩ := c.2
  constructor
  · simp [← hc₁]; congr; funext ⟨a₁, a₂⟩; have := h a₁ a₂; sorry
  · simp [← hc₂]; sorry

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
  /- Stub: pushforward preserves marginals. -/
  -- Proof outline: `map_fst` rewrites via `map_map` and `Prod.fst ∘ (f×g) = f ∘ fst`.
  -- Similarly for `map_snd`.
  constructor <;> sorry

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
  -- y = (f a, g b) for some (a,b) ∈ R by support transport; details deferred.
  -- One can use preimage witness on `map` mass; we leave as stub.
  sorry

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
  -- If `(b,a)` has nonzero mass under `c.map swap`, then `(a,b)` has nonzero mass under `c`.
  -- Transport membership through `swap`.
  sorry

/-- Product (independent) coupling: pair samples of `p` and `q`. -/
noncomputable def prodMap (p : PMF α) (q : PMF β) : PMF (α × β) :=
  p.bind (fun a => (q.map (fun b => (a, b))))

theorem IsCoupling.prod (p : PMF α) (q : PMF β) :
    IsCoupling (prodMap p q) p q := by
  constructor <;> sorry

/-- Top lifting: every pair is allowed. -/
theorem Lift.top (p : PMF α) (q : PMF β) : Lift p (Set.univ : Set (α × β)) q := by
  refine ⟨_, IsCoupling.prod p q, ?_⟩
  intro x hx; simp

/-- Graph lifting for a deterministic post-processing `f`. -/
theorem Lift.graph (p : PMF α) (f : α → β) :
    Lift p {x : α × β | x.2 = f x.1} (p.map f) := by
  -- Use the image of `p` via pairing `(a, f a)` as a coupling witness.
  -- Details deferred.
  refine ⟨p.map (fun a => (a, f a)), ?_, ?_⟩
  · constructor <;> sorry
  · intro x hx; rcases x with ⟨a,b⟩; sorry

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
  -- Follows from functoriality of `OptionT PMF` and coupling extensionality.
  constructor <;> sorry

/-- Symmetry for SPMF couplings. -/
theorem IsCoupling.symm {c : SPMF (α × β)} {p : SPMF α} {q : SPMF β}
    (hc : IsCoupling c p q) :
    IsCoupling (Prod.swap.{u, u} <$> c) q p := by
  constructor <;> sorry

/-- Monadic bind rule for relational lifting (PRHL bind). -/
theorem Lift.bind {p : SPMF α} {q : SPMF β} {R : Set (α × β)}
    (hpq : Lift p R q)
    (F : α → SPMF γ) (G : β → SPMF δ)
    (hpt : ∀ a b, (a, b) ∈ R → Lift (F a) (Set.univ : Set (γ × δ)) (G b)) :
    Lift (p >>= F) (Set.univ : Set (γ × δ)) (q >>= G) := by
  -- Build pointwise couplings via `IsCoupling.exists_bind` and combine them.
  rcases hpq with ⟨c, hc, hR⟩
  rcases (IsCoupling.exists_bind (c := ⟨c, hc⟩)
    (f := F) (g := G)
    (h := fun a b => by
      classical
      rcases hpt a b (by simp [IsCoupling.supports] at hR; apply hR; sorry) with ⟨d, hd, _⟩
      exact ⟨d, hd⟩)) with ⟨d, hd⟩
  refine ⟨d, hd, ?_⟩
  intro z hz; exact Set.mem_univ _

end SPMF
