/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.BI
public import Iris.ProofMode
public import Lean.Meta.Order

/-! # Lattice-based Iris Fixpoints

These lattices over Iris types let us define Iris fixpoints using `partial_fixpoint`.
-/

@[expose] public section

namespace Iris
open Iris.Std BI OFE Lean.Order

namespace MonotoneFixpoint

scoped instance instPartialOrderMonoProp [BI PROP] : PartialOrder PROP where
  rel Φ Ψ := Φ ⊢ Ψ
  rel_refl := .rfl
  rel_trans := .trans
  rel_antisymm := (equiv_iff.mpr ⟨·, ·⟩)

scoped instance instCCPOMonoProp [BI PROP] : CCPO PROP where
  has_csup {c} hc := by
    exists (sExists c)
    refine fun x => ⟨fun h y hy => ?_, fun h => ?_⟩
    · exact (sExists_intro hy).trans h
    · exact sExists_elim h

section Monotone
variable [BI PROP] [PartialOrder α]

@[partial_fixpoint_monotone]
theorem monotone_sep (f g : α → PROP) (hf : monotone f) (hg : monotone g) :
    monotone (fun x => iprop(f x ∗ g x)) :=
  fun _ _ h => sep_mono (hf _ _ h) (hg _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_and (f g : α → PROP) (hf : monotone f) (hg : monotone g) :
    monotone (fun x => iprop(f x ∧ g x)) :=
  fun _ _ h => and_mono (hf _ _ h) (hg _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_or (f g : α → PROP) (hf : monotone f) (hg : monotone g) :
    monotone (fun x => iprop(f x ∨ g x)) :=
  fun _ _ h => or_mono (hf _ _ h) (hg _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_wand (P : PROP) (g : α → PROP) (hg : monotone g) :
    monotone (fun x => iprop(P -∗ g x)) :=
  fun _ _ h => wand_mono_right (hg _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_imp (P : PROP) (g : α → PROP) (hg : monotone g) :
    monotone (fun x => iprop(P → g x)) :=
  fun _ _ h => imp_mono_right (hg _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_exists {β : Sort _} (f : α → β → PROP) (hf : monotone f) :
    monotone (fun x => iprop(∃ b, f x b)) :=
  fun _ _ h => exists_mono fun b => monotone_apply b f hf _ _ h

@[partial_fixpoint_monotone]
theorem monotone_forall {β : Sort _} (f : α → β → PROP) (hf : monotone f) :
    monotone (fun x => iprop(∀ b, f x b)) :=
  fun _ _ h => forall_mono fun b => monotone_apply b f hf _ _ h

@[partial_fixpoint_monotone]
theorem monotone_later (f : α → PROP) (hf : monotone f) : monotone (fun x => iprop(▷ f x)) :=
  fun _ _ h => later_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_laterN (n : Nat) (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(▷^[n] f x)) :=
  fun _ _ h => laterN_mono n (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_except0 (f : α → PROP) (hf : monotone f) : monotone (fun x => iprop(◇ f x)) :=
  fun _ _ h => except0_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_persistently (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(<pers> f x)) :=
  fun _ _ h => persistently_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_affinely (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(<affine> f x)) :=
  fun _ _ h => affinely_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_absorbingly (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(<absorb> f x)) :=
  fun _ _ h => absorbingly_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_intuitionistically (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(□ f x)) :=
  fun _ _ h => intuitionistically_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_bupd [BIUpdate PROP] (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(|==> f x)) :=
  fun _ _ h => bupd_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_fupd [BIFUpdate PROP] (E1 E2 : CoPset) (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(|={E1,E2}=> f x)) :=
  fun _ _ h => fupd_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_step_fupd [BIFUpdate PROP] (Eo Ei : CoPset) (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(|={Eo}[Ei]▷=> f x)) :=
  fun _ _ h => step_fupd_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_step_fupdN [BIFUpdate PROP] (n : Nat) (Eo Ei : CoPset) (f : α → PROP)
    (hf : monotone f) : monotone (fun x => iprop(|={Eo}[Ei]▷=>^[n] f x)) :=
  fun _ _ h => step_fupdN_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_bigSepL {A : Type _} (l : List A) (f : α → Nat → A → PROP) (hf : monotone f) :
    monotone (fun x => iprop([∗list] k ↦ a ∈ l, f x k a)) :=
  fun _ _ h => BigSepL.bigSepL_mono_of_forall fun {k a} => hf _ _ h k a

@[partial_fixpoint_monotone]
theorem monotone_bigAndL {A : Type _} (l : List A) (f : α → Nat → A → PROP) (hf : monotone f) :
    monotone (fun x => iprop([∧list] k ↦ a ∈ l, f x k a)) :=
  fun _ _ h => BigAndL.bigAndL_mono fun k a _ => hf _ _ h k a

@[partial_fixpoint_monotone]
theorem monotone_bigOrL {A : Type _} (l : List A) (f : α → Nat → A → PROP) (hf : monotone f) :
    monotone (fun x => iprop([∨list] k ↦ a ∈ l, f x k a)) :=
  fun _ _ h => BigOrL.bigOrL_mono fun {k a} _ => hf _ _ h k a

@[partial_fixpoint_monotone]
theorem monotone_bigSepL2 {A B : Type _} (l1 : List A) (l2 : List B)
    (f : α → Nat → A → B → PROP) (hf : monotone f) :
    monotone (fun x => iprop([∗list] k ↦ a;b ∈ l1;l2, f x k a b)) :=
  fun _ _ h => BigSepL2.bigSepL2_mono fun {k a b} _ _ => hf _ _ h k a b

@[partial_fixpoint_monotone]
theorem monotone_bigSepM {K V : Type _} {M : Type _ → Type _} [LawfulFiniteMap M K] (m : M V)
    (f : α → K → V → PROP) (hf : monotone f) :
    monotone (fun x => iprop([∗map] k ↦ v ∈ m, f x k v)) :=
  fun _ _ h => BigSepM.bigSepM_mono_of_forall fun {k v} => hf _ _ h k v

@[partial_fixpoint_monotone]
theorem monotone_bigSepS {S A : Type _} [LawfulFiniteSet S A] (X : S) (f : α → A → PROP)
    (hf : monotone f) : monotone (fun x => iprop([∗set] a ∈ X, f x a)) :=
  fun _ _ h => BigSepS.bigSepS_mono_of_forall fun a => hf _ _ h a

end Monotone

end MonotoneFixpoint

namespace CoMonotoneFixpoint

scoped instance instPartialOrderAntiProp [BI PROP] : PartialOrder PROP where
  rel Φ Ψ := Ψ ⊢ Φ
  rel_refl := .rfl
  rel_trans h1 h2 := h2.trans h1
  rel_antisymm h1 h2 := equiv_iff.mpr ⟨h2, h1⟩

scoped instance instCCPOAntiProp [BI PROP] : CCPO PROP where
  has_csup {c} hc := by
    exists (sForall c)
    refine fun x => ⟨fun h y hy => ?_, fun h => ?_⟩
    · exact h.trans (sForall_elim hy)
    · exact sForall_intro h

section Monotone
variable [BI PROP] [PartialOrder α]

@[partial_fixpoint_monotone]
theorem monotone_sep (f g : α → PROP) (hf : monotone f) (hg : monotone g) :
    monotone (fun x => iprop(f x ∗ g x)) :=
  fun _ _ h => sep_mono (hf _ _ h) (hg _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_and (f g : α → PROP) (hf : monotone f) (hg : monotone g) :
    monotone (fun x => iprop(f x ∧ g x)) :=
  fun _ _ h => and_mono (hf _ _ h) (hg _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_or (f g : α → PROP) (hf : monotone f) (hg : monotone g) :
    monotone (fun x => iprop(f x ∨ g x)) :=
  fun _ _ h => or_mono (hf _ _ h) (hg _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_wand (P : PROP) (g : α → PROP) (hg : monotone g) :
    monotone (fun x => iprop(P -∗ g x)) :=
  fun _ _ h => wand_mono_right (hg _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_imp (P : PROP) (g : α → PROP) (hg : monotone g) :
    monotone (fun x => iprop(P → g x)) :=
  fun _ _ h => imp_mono_right (hg _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_exists {β : Sort _} (f : α → β → PROP) (hf : monotone f) :
    monotone (fun x => iprop(∃ b, f x b)) :=
  fun _ _ h => exists_mono fun b => monotone_apply b f hf _ _ h

@[partial_fixpoint_monotone]
theorem monotone_forall {β : Sort _} (f : α → β → PROP) (hf : monotone f) :
    monotone (fun x => iprop(∀ b, f x b)) :=
  fun _ _ h => forall_mono fun b => monotone_apply b f hf _ _ h

@[partial_fixpoint_monotone]
theorem monotone_later (f : α → PROP) (hf : monotone f) : monotone (fun x => iprop(▷ f x)) :=
  fun _ _ h => later_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_laterN (n : Nat) (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(▷^[n] f x)) :=
  fun _ _ h => laterN_mono n (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_except0 (f : α → PROP) (hf : monotone f) : monotone (fun x => iprop(◇ f x)) :=
  fun _ _ h => except0_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_persistently (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(<pers> f x)) :=
  fun _ _ h => persistently_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_affinely (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(<affine> f x)) :=
  fun _ _ h => affinely_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_absorbingly (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(<absorb> f x)) :=
  fun _ _ h => absorbingly_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_intuitionistically (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(□ f x)) :=
  fun _ _ h => intuitionistically_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_bupd [BIUpdate PROP] (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(|==> f x)) :=
  fun _ _ h => bupd_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_fupd [BIFUpdate PROP] (E1 E2 : CoPset) (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(|={E1,E2}=> f x)) :=
  fun _ _ h => fupd_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_step_fupd [BIFUpdate PROP] (Eo Ei : CoPset) (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(|={Eo}[Ei]▷=> f x)) :=
  fun _ _ h => step_fupd_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_step_fupdN [BIFUpdate PROP] (n : Nat) (Eo Ei : CoPset) (f : α → PROP)
    (hf : monotone f) : monotone (fun x => iprop(|={Eo}[Ei]▷=>^[n] f x)) :=
  fun _ _ h => step_fupdN_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_bigSepL {A : Type _} (l : List A) (f : α → Nat → A → PROP) (hf : monotone f) :
    monotone (fun x => iprop([∗list] k ↦ a ∈ l, f x k a)) :=
  fun _ _ h => BigSepL.bigSepL_mono_of_forall fun {k a} => hf _ _ h k a

@[partial_fixpoint_monotone]
theorem monotone_bigAndL {A : Type _} (l : List A) (f : α → Nat → A → PROP) (hf : monotone f) :
    monotone (fun x => iprop([∧list] k ↦ a ∈ l, f x k a)) :=
  fun _ _ h => BigAndL.bigAndL_mono fun k a _ => hf _ _ h k a

@[partial_fixpoint_monotone]
theorem monotone_bigOrL {A : Type _} (l : List A) (f : α → Nat → A → PROP) (hf : monotone f) :
    monotone (fun x => iprop([∨list] k ↦ a ∈ l, f x k a)) :=
  fun _ _ h => BigOrL.bigOrL_mono fun {k a} _ => hf _ _ h k a

@[partial_fixpoint_monotone]
theorem monotone_bigSepL2 {A B : Type _} (l1 : List A) (l2 : List B)
    (f : α → Nat → A → B → PROP) (hf : monotone f) :
    monotone (fun x => iprop([∗list] k ↦ a;b ∈ l1;l2, f x k a b)) :=
  fun _ _ h => BigSepL2.bigSepL2_mono fun {k a b} _ _ => hf _ _ h k a b

@[partial_fixpoint_monotone]
theorem monotone_bigSepM {K V : Type _} {M : Type _ → Type _} [LawfulFiniteMap M K] (m : M V)
    (f : α → K → V → PROP) (hf : monotone f) :
    monotone (fun x => iprop([∗map] k ↦ v ∈ m, f x k v)) :=
  fun _ _ h => BigSepM.bigSepM_mono_of_forall fun {k v} => hf _ _ h k v

@[partial_fixpoint_monotone]
theorem monotone_bigSepS {S A : Type _} [LawfulFiniteSet S A] (X : S) (f : α → A → PROP)
    (hf : monotone f) : monotone (fun x => iprop([∗set] a ∈ X, f x a)) :=
  fun _ _ h => BigSepS.bigSepS_mono_of_forall fun a => hf _ _ h a

end Monotone

end CoMonotoneFixpoint

end Iris
