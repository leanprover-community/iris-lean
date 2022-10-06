import Iris.BI
import Iris.Instances.Data

namespace Iris.Examples
open Iris.BI Iris.Instances.Data

abbrev HeapProp (Val : Type) := State Val → Prop

instance heapPropSetoid (Val : Type) : Setoid (HeapProp Val) where
  r P Q := ∀ σ, P σ ↔ Q σ
  iseqv := {
    refl := by
      intro _ _
      exact Iff.refl _
    symm := by
      intro _ _ h σ
      apply Iff.symm
      exact h σ
    trans := by
      intro _ _ _ h_xy h_yz σ
      exact Iff.trans (h_xy σ) (h_yz σ)
  }

instance (Val : Type) : BIBase (Quotient (heapPropSetoid Val)) where
  entails P Q := Quotient.liftOn₂ P Q (fun P Q => ∀ σ, P σ → Q σ) (by
    simp only [HasEquiv.Equiv, Setoid.r]
    intro _ _ _ _ h₁ h₂
    apply forall_congr
    intro σ
    rw [h₁ σ, h₂ σ])
  emp := Quotient.mk _ fun σ => σ = ∅
  pure φ := Quotient.mk _ fun _ => φ
  and P Q := Quotient.mk _ fun σ => Quotient.liftOn₂ P Q (fun P Q => P σ ∧ Q σ) (by
    simp only [HasEquiv.Equiv, Setoid.r]
    intro _ _ _ _ h₁ h₂
    rw [h₁ σ, h₂ σ])
  or P Q := Quotient.mk _ fun σ => Quotient.liftOn₂ P Q (fun P Q => P σ ∨ Q σ) (by
    simp only [HasEquiv.Equiv, Setoid.r]
    intro _ _ _ _ h₁ h₂
    rw [h₁ σ, h₂ σ])
  impl P Q := Quotient.mk _ fun σ => Quotient.liftOn₂ P Q (fun P Q => P σ → Q σ) (by
    simp only [HasEquiv.Equiv, Setoid.r]
    intro _ _ _ _ h₁ h₂
    rw [h₁ σ, h₂ σ])
  «forall» Ψ := Quotient.mk _ fun σ => ∀ a, Quotient.liftOn (Ψ a) (fun P => P σ) (by
    simp only [HasEquiv.Equiv, Setoid.r]
    intro _ _ h
    rw [h σ])
  exist Ψ := Quotient.mk _ fun σ => ∃ a, Quotient.liftOn (Ψ a) (fun P => P σ) (by
    simp only [HasEquiv.Equiv, Setoid.r]
    intro _ _ h
    rw [h σ])
  sep P Q := Quotient.mk _ fun σ => Quotient.liftOn₂ P Q (fun P Q => ∃ σ₁ σ₂ , σ = σ₁ ∪ σ₂ ∧ σ₁ || σ₂ ∧ P σ₁ ∧ Q σ₂) (by
    simp only [HasEquiv.Equiv, Setoid.r]
    intro _ _ _ _ h₁ h₂
    apply propext ?_
    constructor
    case' mp =>
      intro ⟨σ₁, σ₂, h⟩
      rw [h₁ σ₁, h₂ σ₂] at h
    case' mpr =>
      intro ⟨σ₁, σ₂, h⟩
      rw [← h₁ σ₁, ← h₂ σ₂] at h
    all_goals
      apply Exists.intro σ₁
      apply Exists.intro σ₂
      exact h)
  wand P Q := Quotient.mk _ fun σ => Quotient.liftOn₂ P Q (fun P Q => ∀ σ', σ || σ' → P σ' → Q (σ ∪ σ')) (by
    simp only [HasEquiv.Equiv, Setoid.r]
    intro _ _ _ _ h₁ h₂
    apply forall_congr
    intro σ'
    rw [h₁ σ', h₂ (σ ∪ σ')])
  persistently P := Quotient.mk _ fun _ => Quotient.liftOn P (fun P => P ∅) (by
    simp only [HasEquiv.Equiv, Setoid.r]
    intro _ _ h
    rw [h ∅])

end Iris.Examples
