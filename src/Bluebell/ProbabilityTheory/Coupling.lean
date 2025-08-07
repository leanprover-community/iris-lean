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
  simp [bind, liftM, OptionT.bind, monadLift, MonadLift.monadLift, OptionT.lift,
    PMF.instMonad, OptionT.mk]
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
  · intro h; constructor <;> simp [h, ← liftM_map]

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
