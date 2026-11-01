/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.BI.Lib.Monotone
import all Init.Internal.Order.Basic

/-! # Lattice-based Iris Fixpoints

Two orders on `PROP` let `partial_fixpoint` define Iris fixpoints: entailment gives least
fixpoints, and reverse entailment gives greatest ones. Curried predicates are ordered pointwise,
so a `BIMono` body is monotone, and its fixpoint satisfies Iris (co)induction. -/

@[expose] public section

namespace Iris
open BI Lean.Order Curried

local bi PROP

/-- The order on curried predicates is pointwise. -/
class Curried.Pointwise (τ : Type _) (PROP : Type _) [BI PROP] [Curried τ PROP]
    [CCPO PROP] [CCPO τ] : Prop where
  app_le {Φ Ψ : τ} : Φ ⊑ Ψ ↔ ∀ a : Args τ PROP, app Φ a ⊑ app Ψ a
  csup_le {c : τ → Prop} (hc : chain c) (a : Args τ PROP) {P : PROP} :
    app (CCPO.csup hc) a ⊑ P ↔ ∀ Φ, c Φ → app Φ a ⊑ P

namespace Curried.Pointwise
variable {PROP : Type _} [BI PROP] [CCPO PROP]

instance : Pointwise PROP PROP where
  app_le := ⟨fun h _ => h, fun h => h ()⟩
  csup_le hc _ := CCPO.csup_spec hc _

instance {α : Type _} {β : α → Type _} [∀ a, Curried (β a) PROP] [∀ a, CCPO (β a)]
    [∀ a, Pointwise (β a) PROP] : Pointwise ((a : α) → β a) PROP where
  app_le := ⟨fun h a => app_le.mp (h a.1) a.2, fun h x => app_le.mpr fun r => h ⟨x, r⟩⟩
  csup_le hc a := by
    intro P
    change app ((CCPO.csup hc) a.1) a.2 ⊑ P ↔ _
    rw [← fun_csup_eq]
    refine (csup_le (chain_apply hc a.1) a.2).trans ⟨fun h Φ hΦ => h _ ⟨Φ, hΦ, rfl⟩, ?_⟩
    rintro h _ ⟨Φ, hΦ, rfl⟩
    exact h Φ hΦ

end Curried.Pointwise

variable {PROP : Type _} [BI PROP] {τ : Type _} [Curried τ PROP]

namespace MonotoneFixpoint

scoped instance instPartialOrderMonoProp : PartialOrder PROP where
  rel Φ Ψ := Φ ⊢ Ψ
  rel_refl := .rfl
  rel_trans := .trans
  rel_antisymm := (equiv_iff.mpr ⟨·, ·⟩)

theorem sExists_is_sup (c : PROP → Prop) :
      is_sup c (sExists c) := by
    refine fun x => ⟨fun h y hy => ?_, fun h => ?_⟩
    · exact (sExists_intro hy).trans h
    · exact sExists_elim h

scoped instance instCCPOMonoProp : CCPO PROP where
  has_csup {c} _ := ⟨_, sExists_is_sup c⟩

variable [CCPO τ] [Pointwise τ PROP]

theorem monotone_of_bimono {F : τ → τ} (h : BIMono (PROP := PROP) F) : monotone F :=
  fun Φ Ψ hle => by
  have hΦΨ : ⊢ wandAll Φ Ψ := wandAll_intro fun a => emp_sep.1.trans (Pointwise.app_le.mp hle a)
  have hF : ⊢ wandAll (F Φ) (F Ψ) := by iapply (h _ _); iintro !>; iapply hΦΨ
  exact Pointwise.app_le.mpr fun a => emp_sep.2.trans <| (sep_mono_left hF).trans (wandAll_elim a)

/-- Iris induction for the least fixpoint of a `BIMono` body `F`. -/
theorem fix_iter {F : τ → τ} (h : BIMono (PROP := PROP) F) (Φ : τ) :
    ⊢ □ wandAll (F Φ) Φ -∗ wandAll (fix F (monotone_of_bimono h)) Φ := by
  suffices hfix : iprop(□ wandAll (F Φ) Φ) ⊢ wandAll (fix F (monotone_of_bimono h)) Φ by
    iintro #H; iapply hfix; iexact H
  refine fix_induct _ (fun f => iprop(□ wandAll (F Φ) Φ) ⊢ wandAll f Φ) ?_ fun f ih => ?_
  · intro c hc hall
    refine wandAll_intro fun a => sep_symm.trans <| wand_elim ?_
    exact (Pointwise.csup_le hc a).mpr fun f hf =>
      wand_intro <| sep_symm.trans <| (sep_mono_left (hall f hf)).trans (wandAll_elim a)
  · iintro #H
    iapply wandAll_trans
    isplitl
    · iapply (h _ _)
      iintro !>
      iapply ih $$ H
    · iexact H

end MonotoneFixpoint

namespace CoMonotoneFixpoint

scoped instance instPartialOrderAntiProp : PartialOrder PROP where
  rel Φ Ψ := Ψ ⊢ Φ
  rel_refl := .rfl
  rel_trans h1 h2 := h2.trans h1
  rel_antisymm h1 h2 := equiv_iff.mpr ⟨h2, h1⟩

theorem sForall_is_sup (c : PROP → Prop) :
      is_sup c (sForall c) := by
    refine fun x => ⟨fun h y hy => ?_, fun h => ?_⟩
    · exact h.trans (sForall_elim hy)
    · exact sForall_intro h

scoped instance instCCPOAntiProp : CCPO PROP where
  has_csup {c} _ := ⟨_, sForall_is_sup c⟩

variable [CCPO τ] [Pointwise τ PROP]

theorem monotone_of_bimono {F : τ → τ} (h : BIMono (PROP := PROP) F) : monotone F :=
  fun Φ Ψ hle => by
  have hΨΦ : ⊢ wandAll Ψ Φ := wandAll_intro fun a => emp_sep.1.trans (Pointwise.app_le.mp hle a)
  have hF : ⊢ wandAll (F Ψ) (F Φ) := by iapply (h _ _); iintro !>; iapply hΨΦ
  exact Pointwise.app_le.mpr fun a => emp_sep.2.trans <| (sep_mono_left hF).trans (wandAll_elim a)

/-- Iris coinduction for the greatest fixpoint of a `BIMono` body `F`. -/
theorem fix_coiter {F : τ → τ} (h : BIMono (PROP := PROP) F) (Φ : τ) :
    ⊢ □ wandAll Φ (F Φ) -∗ wandAll Φ (fix F (monotone_of_bimono h)) := by
  suffices hfix : iprop(□ wandAll Φ (F Φ)) ⊢ wandAll Φ (fix F (monotone_of_bimono h)) by
    iintro #H; iapply hfix; iexact H
  refine fix_induct _ (fun f => iprop(□ wandAll Φ (F Φ)) ⊢ wandAll Φ f) ?_ fun f ih => ?_
  · intro c hc hall
    exact wandAll_intro fun a => (Pointwise.csup_le hc a).mpr fun f hf =>
      (sep_mono_left (hall f hf)).trans (wandAll_elim a)
  · iintro #H
    iapply wandAll_trans
    isplitl
    · iexact H
    · iintro !>
      iapply (h _ _)
      iintro !>
      iapply ih $$ H

end CoMonotoneFixpoint

end Iris
