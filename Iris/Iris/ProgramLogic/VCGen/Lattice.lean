/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

public import Iris.BI
public import Std.WP

@[expose] public section

/-!
# Every BI is an assertion lattice

`Std.WP` interprets programs into a complete lattice of assertions (`Lean.Order.CompleteLattice`).
An iris `BI` carries such a lattice: entailment `⊢` is the order, `BIBase.sExists` is the
supremum, and `BI.equiv_iff` (`P = Q ↔ P ⊣⊢ Q`) makes entailment antisymmetric.

The lattice connectives coincide with the BI connectives:

* `P ⊓ Q = iprop(P ∧ Q)`, `⊤ = iprop(True)`, `⊥ = iprop(False)`
* `CompleteLattice.ofProp φ = BIBase.pure φ`
* `iSup Ψ = iprop(∃ a, Ψ a)`, `iInf Ψ = iprop(∀ a, Ψ a)`

Separating conjunction `F ∗ ·` preserves suprema, and its upper adjoint is the magic wand
`F -∗ ·`. This is the frame operator that `vcgen` uses for every iris program logic.
-/

open Iris Iris.BI Lean.Order

namespace Iris.VCGen

variable {PROP : Type _} [BI PROP]

instance : CompleteLattice PROP where
  rel P Q := P ⊢ Q
  rel_refl := BIBase.Entails.rfl
  rel_trans h₁ h₂ := BIBase.Entails.trans h₁ h₂
  rel_antisymm h₁ h₂ := BIBase.BiEntails.to_eq ⟨h₁, h₂⟩
  has_sup c := ⟨BIBase.sExists c, fun _ =>
    ⟨fun h _ hy => BIBase.Entails.trans (BI.sExists_intro hy) h,
     fun h => BI.sExists_elim h⟩⟩

theorem rel_iff {P Q : PROP} : (P ⊑ Q) ↔ (P ⊢ Q) := .rfl

theorem sup_eq (c : PROP → Prop) : CompleteLattice.sup c = BIBase.sExists c :=
  PartialOrder.rel_antisymm (sup_le c fun _ hy => BI.sExists_intro hy)
    (BI.sExists_elim fun _ hp => le_sup c hp)

theorem iSup_eq {α : Sort _} (Ψ : α → PROP) : iSup Ψ = iprop(∃ a, Ψ a) := by
  simp only [iSup, sup_eq]; rfl

theorem iInf_eq {ι : Type _} (Ψ : ι → PROP) : iInf Ψ = iprop(∀ a, Ψ a) :=
  PartialOrder.rel_antisymm
    (BI.sForall_intro fun _ ⟨a, h⟩ => h ▸ iInf_le Ψ a)
    (le_iInf Ψ _ fun a => BI.sForall_elim ⟨a, rfl⟩)

theorem top_eq : (⊤ : PROP) = iprop(True) :=
  PartialOrder.rel_antisymm true_intro (le_top _)

theorem bot_eq : (⊥ : PROP) = iprop(False) :=
  PartialOrder.rel_antisymm (bot_le _) false_elim

theorem meet_eq (P Q : PROP) : P ⊓ Q = iprop(P ∧ Q) :=
  PartialOrder.rel_antisymm
    (BI.and_intro (meet_le_left P Q) (meet_le_right P Q))
    (le_meet _ P Q BI.and_elim_l BI.and_elim_r)

theorem ofProp_eq (φ : Prop) : (CompleteLattice.ofProp φ : PROP) = BIBase.pure φ := by
  by_cases h : φ
  · apply PartialOrder.rel_antisymm (BI.pure_intro h) (CompleteLattice.le_ofProp _ _ h)
  · apply PartialOrder.rel_antisymm
    · exact CompleteLattice.ofProp_le _ _ (fun hφ => absurd hφ h)
    · exact BI.pure_elim' fun hφ => absurd hφ h

instance (F : PROP) : PreservesSup (BIBase.sep F) where
  map_sup s := by
    simp only [sup_eq]
    apply BIBase.BiEntails.to_eq
    constructor
    · refine wand_elim_swap (BI.sExists_elim fun p hp => wand_intro_left ?_)
      exact BI.sExists_intro ⟨p, hp, rfl⟩
    · exact BI.sExists_elim fun _ ⟨p, hp, h⟩ => h ▸ sep_mono_right (BI.sExists_intro hp)

theorem upperAdjoint_sep_eq (F Q : PROP) :
    PreservesSup.upperAdjoint (BIBase.sep F) Q = iprop(F -∗ Q) := by
  apply PartialOrder.rel_antisymm
  · exact wand_intro_left (PreservesSup.upperAdjoint_le (BIBase.sep F) Q)
  · exact PreservesSup.le_upperAdjoint _ wand_elim_right

instance : _root_.Std.Associative (α := PROP) BIBase.sep := ⟨fun _ _ _ => sep_assoc.to_eq⟩
instance : _root_.Std.Commutative (α := PROP) BIBase.sep := ⟨fun _ _ => sep_comm.to_eq⟩
instance : _root_.Std.LawfulIdentity (α := PROP) BIBase.sep BIBase.emp where
  left_id _ := BI.emp_sep.to_eq
  right_id _ := sep_emp.to_eq

end Iris.VCGen
