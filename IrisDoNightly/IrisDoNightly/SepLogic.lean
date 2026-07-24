module

public import IrisDoNightly.SepAlgebra
public import Std.Internal
public import Std.Tactic.Do

@[expose] public section

open Lean.Order Std Std.Internal.Do Std.Internal.Do.CompleteLattice
open Iris.HeapLang

namespace Iris.HeapLang

/-! ## Heap assertions -/

def HProp : Type := State → Prop

instance : CompleteLattice HProp := inferInstanceAs (CompleteLattice (State → Prop))

/-! ## The separation-logic connectives -/

def emp : HProp := fun σ => σ = State.emp
def pointsTo (l : Loc) (w : Val) : HProp := fun σ => σ = State.single l (some w)
def sepConj (P Q : HProp) : HProp :=
  fun σ => ∃ σ₁ σ₂, σ₁ #ₕ σ₂ ∧ σ = σ₁ ⊎ₕ σ₂ ∧ P σ₁ ∧ Q σ₂
def wand (P Q : HProp) : HProp :=
  fun σ => ∀ σ', σ #ₕ σ' → P σ' → Q (σ ⊎ₕ σ')

scoped notation:70 l:max " ↦ " v:max => pointsTo l v
scoped infixr:65 " ∗ " => sepConj
scoped infixr:60 " -∗ " => wand

theorem emp_sepConj (a : HProp) : (sepConj emp a) = a := by
  funext σ
  apply propext
  constructor
  · rintro ⟨σ₁, σ₂, _, rfl, rfl, ha⟩
    rwa [State.emp_union]
  · intro ha
    exact ⟨State.emp, σ, State.emp_disjoint σ, (State.emp_union σ).symm, rfl, ha⟩

theorem sepConj_assoc (a b c : HProp) :
    (sepConj (sepConj a b) c) = (sepConj a (sepConj b c)) := by
  funext σ
  apply propext
  constructor
  · rintro ⟨_, σ₃, hd, rfl, ⟨σ₁, σ₂, hd12, rfl, ha, hb⟩, hc⟩
    obtain ⟨hd13, hd23⟩ := State.disjoint_union_left.mp hd
    exact ⟨σ₁, σ₂ ⊎ₕ σ₃, State.disjoint_union_right.mpr ⟨hd12, hd13⟩,
      State.union_assoc σ₁ σ₂ σ₃, ha, σ₂, σ₃, hd23, rfl, hb, hc⟩
  · rintro ⟨σ₁, _, hd, rfl, ha, ⟨σ₂, σ₃, hd23, rfl, hb, hc⟩⟩
    obtain ⟨hd12, hd13⟩ := State.disjoint_union_right.mp hd
    exact ⟨σ₁ ⊎ₕ σ₂, σ₃, State.disjoint_union_left.mpr ⟨hd13, hd23⟩,
      (State.union_assoc σ₁ σ₂ σ₃).symm, ⟨σ₁, σ₂, hd12, rfl, ha, hb⟩, hc⟩

theorem sepConj_comm (a b : HProp) : (sepConj a b) = (sepConj b a) := by
  funext σ; apply propext
  constructor <;>
    · rintro ⟨σ₁, σ₂, hd, rfl, hp, hq⟩
      exact ⟨σ₂, σ₁, State.disjoint_comm hd, State.union_comm hd, hq, hp⟩

/-! ## `∗` preserves sups and its upper adjoint is the wand -/

/-- Pointwise characterization of the sup on `HProp`. -/
theorem hprop_sup_apply (s : HProp → Prop) (σ : State) :
    CompleteLattice.sup s σ = ∃ f, s f ∧ f σ := by
  apply propext
  constructor
  · exact fun hh => sup_le s (x := fun σ => ∃ f, s f ∧ f σ)
      (fun f hf σ' hfσ' => ⟨f, hf, hfσ'⟩) σ hh
  · rintro ⟨f, hf, hfσ⟩; exact le_sup (c := s) hf σ hfσ

instance (F : HProp) : PreservesSup (sepConj F) where
  map_sup s := by
    funext σ
    apply propext
    simp only [sepConj, hprop_sup_apply]
    constructor
    · rintro ⟨σ₁, σ₂, hd, rfl, hF, x, hx, hxσ₂⟩
      exact ⟨sepConj F x, ⟨x, hx, rfl⟩, σ₁, σ₂, hd, rfl, hF, hxσ₂⟩
    · rintro ⟨f, ⟨x, hx, rfl⟩, σ₁, σ₂, hd, rfl, hF, hxσ₂⟩
      exact ⟨σ₁, σ₂, hd, rfl, hF, x, hx, hxσ₂⟩

/-- The counit of the adjunction `F ∗ · ⊣ F -∗ ·`. -/
theorem sepConj_wand_le (F b : HProp) : (sepConj F (wand F b)) ⊑ b := by
  rintro σ ⟨σ₁, σ₂, hd, rfl, hF, hw⟩
  have := hw σ₁ (State.disjoint_comm hd) hF
  rwa [State.union_comm (State.disjoint_comm hd)] at this

/-- The upper adjoint of `F ∗ ·` is the magic wand `F -∗ ·`. -/
theorem sepConj_upperAdjoint (F b : HProp) :
    PreservesSup.upperAdjoint (sepConj F) b = (wand F b) := by
  apply PartialOrder.rel_antisymm
  · unfold PreservesSup.upperAdjoint
    apply sup_le
    intro x hx σ hxσ σ' hdisj hF
    apply hx (σ ⊎ₕ σ')
    exact ⟨σ', σ, State.disjoint_comm hdisj, State.union_comm hdisj, hF, hxσ⟩
  · exact PreservesSup.le_upperAdjoint (sepConj F) (sepConj_wand_le F b)

end Iris.HeapLang
