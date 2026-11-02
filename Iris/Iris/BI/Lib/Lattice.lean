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
fixpoints, and reverse entailment gives greatest ones. Predicates `A → PROP` are ordered pointwise,
so a `BIMono` body is monotone, and its fixpoint satisfies Iris (co)induction.

`partial_fixpoint` defines a function of several arguments on its curried type. `fix_iso` moves
the fixpoint across currying, or any other order isomorphism. -/

@[expose] public section

namespace Iris
open BI Lean.Order

/-! ## Order theory -/

section Order
variable {α β : Sort _}

theorem monotone_conj [PartialOrder α] [PartialOrder β] {F : α → α} {G : β → β}
    (e : α → β) (e' : β → α) (he : monotone e) (he' : monotone e') (hG : monotone G)
    (h : ∀ a, F a = e' (G (e a))) : monotone F :=
  fun a b hab => by rw [h, h]; exact he' _ _ (hG _ _ (he _ _ hab))

/-- A fixpoint moves across an order isomorphism. -/
theorem fix_iso [CCPO α] [CCPO β] {F : α → α} {G : β → β} (hF : monotone F) (hG : monotone G)
    (e : α → β) (e' : β → α) (he : monotone e)
    (h1 : ∀ b, e (e' b) = b) (h2 : ∀ a, e' (e a) = a) (hcomm : ∀ a, e (F a) = G (e a)) :
    e (fix F hF) = fix G hG := by
  have hF' : fix F hF ⊑ e' (fix G hG) := by
    refine fix_induct hF (· ⊑ e' (fix G hG)) (fun c hc h => csup_le hc h) fun a ha => ?_
    refine PartialOrder.rel_trans (hF _ _ ha) (PartialOrder.rel_of_eq ?_)
    rw [← h2 (F _), hcomm, h1, ← fix_eq hG]
  have hG' : fix G hG ⊑ e (fix F hF) := by
    refine fix_induct hG (· ⊑ e (fix F hF)) (fun c hc h => csup_le hc h) fun b hb => ?_
    refine PartialOrder.rel_trans (hG _ _ hb) (PartialOrder.rel_of_eq ?_)
    rw [← hcomm, ← fix_eq hF]
  have := he _ _ hF'
  rw [h1] at this
  exact PartialOrder.rel_antisymm this hG'

/-- The sup of a chain of functions is below `P` at `x` when every function is. -/
theorem csup_apply_le [CCPO β] {c : (α → β) → Prop} (hc : chain c) (x : α) {P : β}
    (h : ∀ f, c f → f x ⊑ P) : CCPO.csup hc x ⊑ P := by
  rw [← fun_csup_eq]
  exact csup_le (chain_apply hc x) fun _ ⟨f, hf, e⟩ => e ▸ h f hf

/-! The quantifier rewrites that turn statements about predicates on tuples into curried ones. -/

theorem forall_iso (e : α → β) (e' : β → α) (h : ∀ b, e (e' b) = b) {P : β → Prop} :
    (∀ b, P b) ↔ ∀ a, P (e a) :=
  ⟨fun hP _ => hP _, fun hP b => h b ▸ hP (e' b)⟩

theorem forall_psigma {β : α → Sort _} {P : PSigma β → Prop} :
    (∀ p, P p) ↔ ∀ x x', P ⟨x, x'⟩ :=
  ⟨fun h _ _ => h _, fun h p => h p.1 p.2⟩

theorem forall_punit {P : PUnit → Prop} : (∀ p, P p) ↔ P ⟨⟩ := ⟨fun h => h _, fun h _ => h⟩

end Order

local bi PROP

variable {PROP : Type _} [BI PROP] {A : Sort _}

section Tuples
variable {α β : Sort _}

theorem bi_forall_iso (e : α → β) (e' : β → α) (h : ∀ b, e (e' b) = b) {P : β → PROP} :
    iprop(∀ b, P b) = iprop(∀ a, P (e a)) :=
  BIBase.BiEntails.to_eq ⟨forall_intro fun a => forall_elim (e a),
    forall_intro fun b => h b ▸ forall_elim (e' b)⟩

theorem bi_forall_psigma {β : α → Sort _} {P : PSigma β → PROP} :
    iprop(∀ p, P p) = iprop(∀ x x', P ⟨x, x'⟩) :=
  BIBase.BiEntails.to_eq ⟨forall_intro fun _ => forall_intro fun _ => forall_elim _,
    forall_intro fun p => (forall_elim p.1).trans (forall_elim p.2)⟩

theorem bi_forall_punit {P : PUnit → PROP} : iprop(∀ p, P p) = P ⟨⟩ :=
  BIBase.BiEntails.to_eq ⟨forall_elim _, forall_intro fun _ => .rfl⟩

theorem bimono_def {F : (A → PROP) → A → PROP} :
    BIMono F ↔ ∀ Φ Ψ, ⊢ □ (∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Φ x -∗ F Ψ x := .rfl

end Tuples

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

theorem monotone_of_bimono {F : (A → PROP) → A → PROP} (h : BIMono F) : monotone F :=
  fun Φ Ψ hle x => by
  have hw : ⊢ ∀ x, Φ x -∗ Ψ x := forall_intro fun x => wand_intro (emp_sep.1.trans (hle x))
  change F Φ x ⊢ F Ψ x
  iintro H
  iapply (h Φ Ψ) $$ [] %x H
  iintro !>
  iapply hw

/-- The least fixpoint of a `BIMono` body. -/
noncomputable abbrev lfp (F : (A → PROP) → A → PROP) (h : BIMono F) : A → PROP :=
  fix F (monotone_of_bimono h)

variable {F : (A → PROP) → A → PROP} (h : BIMono F)

theorem fix_unfold_mp (x : A) : lfp F h x ⊢ F (lfp F h) x :=
  .of_eq (congrFun (fix_eq _) x)

theorem fix_unfold_mpr (x : A) : F (lfp F h) x ⊢ lfp F h x :=
  .of_eq (congrFun (fix_eq _) x).symm

/-- Iris induction for the least fixpoint of a `BIMono` body `F`. -/
theorem fix_iter (Φ : A → PROP) : ⊢ □ (∀ x, F Φ x -∗ Φ x) -∗ ∀ x, lfp F h x -∗ Φ x := by
  suffices hfix : iprop(□ (∀ x, F Φ x -∗ Φ x)) ⊢ ∀ x, lfp F h x -∗ Φ x by
    iintro #H; iapply hfix; iexact H
  refine fix_induct _ (fun (f : A → PROP) => iprop(□ (∀ x, F Φ x -∗ Φ x)) ⊢ ∀ x, f x -∗ Φ x) ?_ fun f ih => ?_
  · intro c hc hall
    refine forall_intro fun x => wand_intro <| sep_symm.trans <| wand_elim ?_
    exact csup_apply_le hc x fun f hf => wand_intro <| sep_symm.trans <|
      (sep_mono_left ((hall f hf).trans (forall_elim x))).trans wand_elim_left
  · iintro #H %x Hf
    iapply H
    iapply (h f Φ) $$ [] %x Hf
    iintro !>
    iapply ih $$ H

/-- Strong induction: the induction hypothesis also knows that the fixpoint holds. -/
theorem fix_ind (Φ : A → PROP) :
    ⊢ □ (∀ x, F (fun y => iprop(Φ y ∧ lfp F h y)) x -∗ Φ x) -∗ ∀ x, lfp F h x -∗ Φ x := by
  iintro #HM %x Hx
  iapply (and_elim_l (Q := lfp F h x))
  iapply (fix_iter h fun y => iprop(Φ y ∧ lfp F h y)) $$ [] %x Hx
  iintro !> %y Hy
  isplit
  · iapply HM $$ %y Hy
  · iapply fix_unfold_mpr h y
    iapply (h _ _) $$ [] %y Hy
    iintro !> %z Hz
    icases Hz with ⟨-, Hz⟩
    iexact Hz

/-- Well-founded induction: the hypothesis sees a prefixpoint `W` of `fun Ψ x => Φ x ∧ F Ψ x`,
such as its least fixpoint. -/
theorem fix_ind_wf (Φ W : A → PROP) (hW : ∀ x, iprop(Φ x ∧ F W x) ⊢ W x) :
    ⊢ □ (∀ x, F W x -∗ Φ x) -∗ ∀ x, lfp F h x -∗ Φ x := by
  iintro #HM %x Hx
  iapply HM
  iapply (h (lfp F h) W) $$ [] %x [Hx]
  · iintro !>
    iapply (fix_iter h W)
    iintro !> %y Hy
    iapply hW
    isplit
    · iapply HM $$ %y Hy
    · iexact Hy
  · iapply fix_unfold_mp h x $$ Hx

theorem fix_strong_mono {G : (A → PROP) → A → PROP} (hG : BIMono G) :
    ⊢ □ (∀ Φ x, F Φ x -∗ G Φ x) -∗ ∀ x, lfp F h x -∗ lfp G hG x := by
  iintro #H
  iapply fix_iter h
  iintro !> %x Hx
  iapply fix_unfold_mpr hG x
  iapply H $$ %(lfp G hG) %x Hx

theorem fix_affine (hF : ∀ x, Affine (F (fun _ => iprop(emp)) x)) (x : A) :
    Affine (lfp F h x) := by
  constructor
  revert x
  iapply (fix_iter h fun _ => iprop(emp))
  iintro !> %y Hy
  iapply (hF y).affine $$ Hy

theorem fix_absorbing (hF : ∀ Φ : A → PROP, (∀ x, Absorbing (Φ x)) → ∀ x, Absorbing (F Φ x))
    (x : A) : Absorbing (lfp F h x) := by
  have : ∀ y, Absorbing (F (fun y => iprop(True -∗ lfp F h y)) y) := hF _ fun _ => inferInstance
  constructor
  iapply wand_elim_swap
  revert x
  iapply (fix_iter h fun y => iprop(True -∗ lfp F h y))
  iintro !> %y HF HT
  iapply fix_unfold_mpr h y
  iapply (h (fun y => iprop(True -∗ lfp F h y)) (lfp F h)) $$ [] %y [HF HT]
  · iintro !> %z Hz
    iapply Hz
    ipureintro
    trivial
  · iclear HT
    iexact HF

theorem fix_persistent_affine
    (hA : ∀ Φ : A → PROP, (∀ x, Affine (Φ x)) → ∀ x, Affine (F Φ x))
    (hP : ∀ Φ : A → PROP, (∀ x, Persistent (Φ x)) → ∀ x, Persistent (F Φ x))
    (x : A) : Persistent (lfp F h x) := by
  have : ∀ y, Affine (F (fun y => iprop(□ lfp F h y)) y) := hA _ fun _ => inferInstance
  have : ∀ y, Persistent (F (fun y => iprop(□ lfp F h y)) y) := hP _ fun _ => inferInstance
  constructor
  refine .trans ?_ persistently_of_intuitionistically
  revert x
  iapply (fix_iter h fun y => iprop(□ lfp F h y))
  iintro !> %y #HF !>
  iapply fix_unfold_mpr h y
  iapply (h _ _) $$ [] %y HF
  iintro !> %z #Hz
  iexact Hz

theorem fix_persistent_absorbing
    (hA : ∀ Φ : A → PROP, (∀ x, Absorbing (Φ x)) → ∀ x, Absorbing (F Φ x))
    (hP : ∀ Φ : A → PROP, (∀ x, Persistent (Φ x)) → ∀ x, Persistent (F Φ x))
    (x : A) : Persistent (lfp F h x) := by
  have : ∀ y, Absorbing (lfp F h y) := fix_absorbing h hA
  have : ∀ y, Persistent (F (fun y => iprop(<pers> lfp F h y)) y) := hP _ fun _ => inferInstance
  constructor
  revert x
  iapply (fix_iter h fun y => iprop(<pers> lfp F h y))
  iintro !> %y #HF !>
  iapply fix_unfold_mpr h y
  iapply (h _ _) $$ [] %y HF
  iintro !> %z #Hz
  iexact Hz

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

theorem monotone_of_bimono {F : (A → PROP) → A → PROP} (h : BIMono F) : monotone F :=
  fun Φ Ψ hle x => by
  have hw : ⊢ ∀ x, Ψ x -∗ Φ x := forall_intro fun x => wand_intro (emp_sep.1.trans (hle x))
  change F Ψ x ⊢ F Φ x
  iintro H
  iapply (h Ψ Φ) $$ [] %x H
  iintro !>
  iapply hw

/-- The greatest fixpoint of a `BIMono` body. -/
noncomputable abbrev gfp (F : (A → PROP) → A → PROP) (h : BIMono F) : A → PROP :=
  fix F (monotone_of_bimono h)

variable {F : (A → PROP) → A → PROP} (h : BIMono F)

theorem fix_unfold_mp (x : A) : gfp F h x ⊢ F (gfp F h) x :=
  .of_eq (congrFun (fix_eq _) x)

theorem fix_unfold_mpr (x : A) : F (gfp F h) x ⊢ gfp F h x :=
  .of_eq (congrFun (fix_eq _) x).symm

/-- Iris coinduction for the greatest fixpoint of a `BIMono` body `F`. -/
theorem fix_coiter (Φ : A → PROP) : ⊢ □ (∀ x, Φ x -∗ F Φ x) -∗ ∀ x, Φ x -∗ gfp F h x := by
  suffices hfix : iprop(□ (∀ x, Φ x -∗ F Φ x)) ⊢ ∀ x, Φ x -∗ gfp F h x by
    iintro #H; iapply hfix; iexact H
  refine fix_induct _ (fun (f : A → PROP) => iprop(□ (∀ x, Φ x -∗ F Φ x)) ⊢ ∀ x, Φ x -∗ f x) ?_ fun f ih => ?_
  · intro c hc hall
    refine forall_intro fun x => wand_intro ?_
    exact csup_apply_le hc x fun f hf =>
      (sep_mono_left ((hall f hf).trans (forall_elim x))).trans wand_elim_left
  · iintro #H %x HΦ
    iapply (h Φ f) $$ [] %x [HΦ]
    · iintro !>
      iapply ih $$ H
    · iapply H $$ %x HΦ

/-- Strong coinduction: the coinduction hypothesis may also conclude the fixpoint itself. -/
theorem fix_coind (Φ : A → PROP) :
    ⊢ □ (∀ x, Φ x -∗ F (fun y => iprop(Φ y ∨ gfp F h y)) x) -∗ ∀ x, Φ x -∗ gfp F h x := by
  iintro #HM %x HΦ
  iapply (fix_coiter h fun y => iprop(Φ y ∨ gfp F h y)) $$ [] %x [HΦ]
  · iintro !> %y (HΦ | HG)
    · iapply HM $$ %y HΦ
    · iapply (h _ _) $$ [] %y [HG]
      · iintro !> %z Hz
        iright
        iexact Hz
      · iapply fix_unfold_mp h y $$ HG
  · ileft
    iexact HΦ

/-- Parameterized coinduction: the hypothesis may conclude a postfixpoint `W` of
`fun Ψ x => Φ x ∨ F Ψ x`, such as its greatest fixpoint. -/
theorem fix_paco (Φ W : A → PROP) (hW : ∀ x, W x ⊢ iprop(Φ x ∨ F W x)) :
    ⊢ □ (∀ x, Φ x -∗ F W x) -∗ ∀ x, Φ x -∗ gfp F h x := by
  iintro #HM %x HΦ
  iapply fix_unfold_mpr h x
  iapply (h W (gfp F h)) $$ [] %x [HΦ]
  · iintro !> %y Hy
    iapply (fix_coiter h W) $$ [] %y Hy
    iintro !> %z Hz
    ihave Hcase : iprop(Φ z ∨ F W z) $$ [Hz]
    · iapply hW $$ Hz
    icases Hcase with (H | H)
    · iapply HM $$ %z H
    · iexact H
  · iapply HM $$ %x HΦ

theorem fix_strong_mono {G : (A → PROP) → A → PROP} (hG : BIMono G) :
    ⊢ □ (∀ Φ x, F Φ x -∗ G Φ x) -∗ ∀ x, gfp F h x -∗ gfp G hG x := by
  iintro #H
  iapply fix_coiter hG
  iintro !> %x Hx
  iapply H
  iapply fix_unfold_mp h x $$ Hx

theorem fix_absorbing (hF : ∀ Φ : A → PROP, (∀ x, Absorbing (Φ x)) → ∀ x, Absorbing (F Φ x))
    (x : A) : Absorbing (gfp F h x) := by
  have : ∀ y, Absorbing (F (fun y => iprop(<absorb> gfp F h y)) y) := hF _ fun _ => inferInstance
  constructor
  revert x
  iapply (fix_coiter h fun y => iprop(<absorb> gfp F h y))
  iintro !> %y >HG
  iapply (h _ _) $$ [] %y [HG]
  · iintro !> %z Hz
    iapply absorbingly_intro
    iexact Hz
  · iapply fix_unfold_mp h y $$ HG

end CoMonotoneFixpoint

end Iris
