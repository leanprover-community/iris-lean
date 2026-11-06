/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.BI.Lib.Monotone
public import Iris.Std.Order
import all Init.Internal.Order.Basic

/-! # Lattice-based Iris Fixpoints

Entailment (`MonotoneFixpoint`) and reverse entailment (`CoMonotoneFixpoint`) make `PROP` a CCPO,
so `partial_fixpoint` defines least and greatest fixpoints of `BIMono` bodies, which satisfy Iris
(co)induction. -/

@[expose] public section

namespace Iris
open BI Lean.Order OFE

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

/-- A chain of predicates that respect `R` gives related sets of values at related points. -/
theorem sup_ne {R : Nat → A → A → Prop} {c : (A → PROP) → Prop}
    (hall : ∀ f, c f → ∀ n x y, R n x y → f x ≡{n}≡ f y) {n : Nat} {x y : A} (hxy : R n x y) :
    liftRel (· ≡{n}≡ ·) (fun P => ∃ f, c f ∧ f x = P) (fun P => ∃ f, c f ∧ f y = P) :=
  ⟨fun _ ⟨f, hf, e⟩ => ⟨f y, ⟨f, hf, rfl⟩, e ▸ hall f hf _ _ _ hxy⟩,
   fun _ ⟨f, hf, e⟩ => ⟨f x, ⟨f, hf, rfl⟩, e ▸ hall f hf _ _ _ hxy⟩⟩

namespace MonotoneFixpoint

scoped instance instPartialOrderMonoProp : PartialOrder PROP where
  rel Φ Ψ := Φ ⊢ Ψ
  rel_refl := .rfl
  rel_trans := .trans
  rel_antisymm := (equiv_iff.mpr ⟨·, ·⟩)

theorem sExists_is_sup (c : PROP → Prop) : is_sup c (sExists c) :=
  fun _ => ⟨fun h _ hy => (sExists_intro hy).trans h, sExists_elim⟩

scoped instance instCCPOMonoProp : CCPO PROP where
  has_csup {c} _ := ⟨_, sExists_is_sup c⟩

theorem monotone_of_bimono {F : (A → PROP) → A → PROP} (h : BIMono F) : monotone F :=
  fun Φ Ψ hle x => by
  change F Φ x ⊢ F Ψ x
  iintro H
  iapply (h Φ Ψ) $$ [] %x H
  iintro !> %x H
  have hw : ⊢ Φ x -∗ Ψ x := wand_intro (emp_sep.1.trans (hle x))
  iapply hw $$ [$]

/-- The least fixpoint of a `BIMono` body. -/
noncomputable abbrev lfp (F : (A → PROP) → A → PROP) (h : BIMono F) : A → PROP :=
  fix F (monotone_of_bimono h)

variable {F : (A → PROP) → A → PROP} (h : BIMono F)

theorem fix_unfold : lfp F h = F (lfp F h) := fix_eq _

theorem fix_unfold_mp (x : A) : lfp F h x ⊢ F (lfp F h) x :=
  .of_eq (congrFun (fix_eq _) x)

theorem fix_unfold_mpr (x : A) : F (lfp F h) x ⊢ lfp F h x :=
  .of_eq (congrFun (fix_eq _) x).symm

/-- Iris induction for the least fixpoint of a `BIMono` body `F`. -/
theorem fix_iter (Φ : A → PROP) : ⊢ □ (∀ x, F Φ x -∗ Φ x) -∗ ∀ x, lfp F h x -∗ Φ x := by
  suffices hfix : iprop(□ (∀ x, F Φ x -∗ Φ x)) ⊢ ∀ x, lfp F h x -∗ Φ x by
    iintro #H; iapply hfix; iexact H
  refine fix_induct _ (fun (f : A → PROP) => iprop(□ (∀ x, F Φ x -∗ Φ x)) ⊢ ∀ x, f x -∗ Φ x) ?_
    fun f ih => ?_
  · intro c hc hall
    refine forall_intro fun x => wand_intro <| sep_symm.trans <| wand_elim ?_
    exact csup_apply_le hc x fun f hf => wand_intro <| sep_symm.trans <|
      (sep_mono_left ((hall f hf).trans (forall_elim x))).trans wand_elim_left
  · iintro #H %x Hf
    iapply H
    iapply (h f Φ) $$ [] %x Hf
    iintro !>
    iapply ih $$ H

/-- Strong induction: the hypothesis also gets the fixpoint. -/
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

/-- Well-founded induction, for a prefixpoint `W` of `fun Ψ x => Φ x ∧ F Ψ x`. -/
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

/-- The least fixpoint is below every prefixpoint `g` of a larger body `G`. -/
theorem fix_strong_mono (G : (A → PROP) → A → PROP) (g : A → PROP) (hg : ∀ x, G g x ⊢ g x) :
    ⊢ □ (∀ Φ x, F Φ x -∗ G Φ x) -∗ ∀ x, lfp F h x -∗ g x := by
  iintro #H
  iapply fix_iter h
  iintro !> %x Hx
  iapply hg
  iapply H $$ %g %x Hx

/-- Affine if the body is, at `fun _ => emp`. -/
instance fix_affine [∀ x, Affine (F (fun _ => iprop(emp)) x)] (x : A) : Affine (lfp F h x) := by
  constructor
  revert x
  iapply (fix_iter h fun _ => iprop(emp))
  iintro !> %y Hy
  iapply Affine.affine $$ Hy

/-- Absorbing if the body is, at `fun y => True -∗ lfp F h y`. -/
instance fix_absorbing [∀ x, Absorbing (F (fun y => iprop(True -∗ lfp F h y)) x)] (x : A) :
    Absorbing (lfp F h x) := by
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

/-- Persistent if the body is affine and persistent, at `fun y => □ lfp F h y`. -/
instance fix_persistent_affine [∀ x, Affine (F (fun y => iprop(□ lfp F h y)) x)]
    [∀ x, Persistent (F (fun y => iprop(□ lfp F h y)) x)] (x : A) : Persistent (lfp F h x) := by
  constructor
  refine .trans ?_ persistently_of_intuitionistically
  revert x
  iapply (fix_iter h fun y => iprop(□ lfp F h y))
  iintro !> %y #HF !>
  iapply fix_unfold_mpr h y
  iapply (h _ _) $$ [] %y HF
  iintro !> %z #Hz
  iexact Hz

/-- Persistent if absorbing and the body is persistent at `fun y => <pers> lfp F h y`. -/
instance fix_persistent_absorbing [∀ x, Absorbing (lfp F h x)]
    [∀ x, Persistent (F (fun y => iprop(<pers> lfp F h y)) x)] (x : A) :
    Persistent (lfp F h x) := by
  constructor
  revert x
  iapply (fix_iter h fun y => iprop(<pers> lfp F h y))
  iintro !> %y #HF !>
  iapply fix_unfold_mpr h y
  iapply (h _ _) $$ [] %y HF
  iintro !> %z #Hz
  iexact Hz

/-- The least fixpoint respects any relations `R n` that `F` respects, such as `≡{n}≡`. -/
theorem fix_ne_rel (R : Nat → A → A → Prop)
    (hF : ∀ Φ : A → PROP, (∀ n x y, R n x y → Φ x ≡{n}≡ Φ y) →
      ∀ n x y, R n x y → F Φ x ≡{n}≡ F Φ y) :
    ∀ n x y, R n x y → lfp F h x ≡{n}≡ lfp F h y := by
  refine fix_induct _ (fun g => ∀ n x y, R n x y → g x ≡{n}≡ g y) ?_ fun g hg => hF g hg
  intro c hc hall n x y hxy
  rw [csup_apply_eq hc sExists_is_sup, csup_apply_eq hc sExists_is_sup]
  exact sExists_ne (sup_ne hall hxy)

/-- Non-expansive if `F` preserves non-expansiveness. -/
theorem fix_ne [OFE A] (hF : ∀ Φ : A → PROP, NonExpansive Φ → NonExpansive (F Φ)) :
    NonExpansive (lfp F h) :=
  ⟨fun _ _ _ => fix_ne_rel h (fun n x y => x ≡{n}≡ y)
    (fun Φ hΦ _ _ _ h => (hF Φ ⟨fun _ _ _ => hΦ _ _ _⟩).ne h) _ _ _⟩

/-- Non-expansive in the body, if `F₂` preserves pointwise `≡{n}≡`. -/
theorem fix_ne_outer {F₁ F₂ : (A → PROP) → A → PROP} (h₁ : BIMono F₁) (h₂ : BIMono F₂) {n : Nat}
    (hF₂ : ∀ Φ Ψ : A → PROP, (∀ x, Φ x ≡{n}≡ Ψ x) → ∀ x, F₂ Φ x ≡{n}≡ F₂ Ψ x)
    (hF : ∀ Φ x, F₁ Φ x ≡{n}≡ F₂ Φ x) (x : A) : lfp F₁ h₁ x ≡{n}≡ lfp F₂ h₂ x := by
  have hFG : monotone fun p : (A → PROP) ×' (A → PROP) => (⟨F₁ p.1, F₂ p.2⟩ : _ ×' _) :=
    fun _ _ hpq => show _ ∧ _ from ⟨monotone_of_bimono h₁ _ _ (show _ ∧ _ from hpq).1,
      monotone_of_bimono h₂ _ _ (show _ ∧ _ from hpq).2⟩
  -- Induct on the fixpoint of the pair.
  suffices ∀ x, (fix _ hFG).1 x ≡{n}≡ (fix _ hFG).2 x by
    rw [fix_pprod (monotone_of_bimono h₁) (monotone_of_bimono h₂) hFG] at this
    exact this x
  refine fix_induct hFG (fun q => ∀ x, q.1 x ≡{n}≡ q.2 x) ?_
    fun q hq x => (hF q.1 x).trans (hF₂ _ _ hq x)
  intro c hc hall x
  rw [← prod_csup_eq]
  change CCPO.csup (PProd.chain.chain_fst hc) x ≡{n}≡ CCPO.csup (PProd.chain.chain_snd hc) x
  rw [csup_apply_eq _ sExists_is_sup, csup_apply_eq _ sExists_is_sup]
  exact sExists_ne ⟨fun _ ⟨f, ⟨g, hfg⟩, e⟩ => ⟨g x, ⟨g, ⟨f, hfg⟩, rfl⟩, e ▸ hall _ hfg x⟩,
    fun _ ⟨g, ⟨f, hfg⟩, e⟩ => ⟨f x, ⟨f, ⟨g, hfg⟩, rfl⟩, e ▸ hall _ hfg x⟩⟩

end MonotoneFixpoint

namespace CoMonotoneFixpoint

scoped instance instPartialOrderAntiProp : PartialOrder PROP where
  rel Φ Ψ := Ψ ⊢ Φ
  rel_refl := .rfl
  rel_trans h1 h2 := h2.trans h1
  rel_antisymm h1 h2 := equiv_iff.mpr ⟨h2, h1⟩

theorem sForall_is_sup (c : PROP → Prop) : is_sup c (sForall c) :=
  fun _ => ⟨fun h _ hy => h.trans (sForall_elim hy), sForall_intro⟩

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

theorem fix_unfold : gfp F h = F (gfp F h) := fix_eq _

theorem fix_unfold_mp (x : A) : gfp F h x ⊢ F (gfp F h) x :=
  .of_eq (congrFun (fix_eq _) x)

theorem fix_unfold_mpr (x : A) : F (gfp F h) x ⊢ gfp F h x :=
  .of_eq (congrFun (fix_eq _) x).symm

/-- Iris coinduction for the greatest fixpoint of a `BIMono` body `F`. -/
theorem fix_coiter (Φ : A → PROP) : ⊢ □ (∀ x, Φ x -∗ F Φ x) -∗ ∀ x, Φ x -∗ gfp F h x := by
  suffices hfix : iprop(□ (∀ x, Φ x -∗ F Φ x)) ⊢ ∀ x, Φ x -∗ gfp F h x by
    iintro #H; iapply hfix; iexact H
  refine fix_induct _ (fun (f : A → PROP) => iprop(□ (∀ x, Φ x -∗ F Φ x)) ⊢ ∀ x, Φ x -∗ f x) ?_
    fun f ih => ?_
  · intro c hc hall
    refine forall_intro fun x => wand_intro ?_
    exact csup_apply_le hc x fun f hf =>
      (sep_mono_left ((hall f hf).trans (forall_elim x))).trans wand_elim_left
  · iintro #H %x HΦ
    iapply (h Φ f) $$ [] %x [HΦ]
    · iintro !>
      iapply ih $$ H
    · iapply H $$ %x HΦ

/-- Strong coinduction: the hypothesis may also conclude the fixpoint. -/
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

/-- Parameterized coinduction, for a postfixpoint `W` of `fun Ψ x => Φ x ∨ F Ψ x`. -/
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

/-- Every postfixpoint `g` of a smaller body `G` is below the greatest fixpoint. -/
theorem fix_strong_mono (G : (A → PROP) → A → PROP) (g : A → PROP) (hg : ∀ x, g x ⊢ G g x) :
    ⊢ □ (∀ Φ x, G Φ x -∗ F Φ x) -∗ ∀ x, g x -∗ gfp F h x := by
  iintro #H
  iapply fix_coiter h
  iintro !> %x Hx
  iapply H
  iapply hg $$ Hx

/-- Absorbing if the body is, at `fun y => <absorb> gfp F h y`. -/
instance fix_absorbing [∀ x, Absorbing (F (fun y => iprop(<absorb> gfp F h y)) x)] (x : A) :
    Absorbing (gfp F h x) := by
  constructor
  revert x
  iapply (fix_coiter h fun y => iprop(<absorb> gfp F h y))
  iintro !> %y >HG
  iapply (h _ _) $$ [] %y [HG]
  · iintro !> %z Hz
    iapply absorbingly_intro
    iexact Hz
  · iapply fix_unfold_mp h y $$ HG

/-- The greatest fixpoint respects any relations `R n` that `F` respects, such as `≡{n}≡`. -/
theorem fix_ne_rel (R : Nat → A → A → Prop)
    (hF : ∀ Φ : A → PROP, (∀ n x y, R n x y → Φ x ≡{n}≡ Φ y) →
      ∀ n x y, R n x y → F Φ x ≡{n}≡ F Φ y) :
    ∀ n x y, R n x y → gfp F h x ≡{n}≡ gfp F h y := by
  refine fix_induct _ (fun g => ∀ n x y, R n x y → g x ≡{n}≡ g y) ?_ fun g hg => hF g hg
  intro c hc hall n x y hxy
  rw [csup_apply_eq hc sForall_is_sup, csup_apply_eq hc sForall_is_sup]
  exact sForall_ne (sup_ne hall hxy)

/-- Non-expansive if `F` preserves non-expansiveness. -/
theorem fix_ne [OFE A] (hF : ∀ Φ : A → PROP, NonExpansive Φ → NonExpansive (F Φ)) :
    NonExpansive (gfp F h) :=
  ⟨fun _ _ _ => fix_ne_rel h (fun n x y => x ≡{n}≡ y)
    (fun Φ hΦ _ _ _ h => (hF Φ ⟨fun _ _ _ => hΦ _ _ _⟩).ne h) _ _ _⟩

/-- Non-expansive in the body, if `F₂` preserves pointwise `≡{n}≡`. -/
theorem fix_ne_outer {F₁ F₂ : (A → PROP) → A → PROP} (h₁ : BIMono F₁) (h₂ : BIMono F₂) {n : Nat}
    (hF₂ : ∀ Φ Ψ : A → PROP, (∀ x, Φ x ≡{n}≡ Ψ x) → ∀ x, F₂ Φ x ≡{n}≡ F₂ Ψ x)
    (hF : ∀ Φ x, F₁ Φ x ≡{n}≡ F₂ Φ x) (x : A) : gfp F₁ h₁ x ≡{n}≡ gfp F₂ h₂ x := by
  have hFG : monotone fun p : (A → PROP) ×' (A → PROP) => (⟨F₁ p.1, F₂ p.2⟩ : _ ×' _) :=
    fun _ _ hpq => show _ ∧ _ from ⟨monotone_of_bimono h₁ _ _ (show _ ∧ _ from hpq).1,
      monotone_of_bimono h₂ _ _ (show _ ∧ _ from hpq).2⟩
  -- Induct on the fixpoint of the pair.
  suffices ∀ x, (fix _ hFG).1 x ≡{n}≡ (fix _ hFG).2 x by
    rw [fix_pprod (monotone_of_bimono h₁) (monotone_of_bimono h₂) hFG] at this
    exact this x
  refine fix_induct hFG (fun q => ∀ x, q.1 x ≡{n}≡ q.2 x) ?_
    fun q hq x => (hF q.1 x).trans (hF₂ _ _ hq x)
  intro c hc hall x
  rw [← prod_csup_eq]
  change CCPO.csup (PProd.chain.chain_fst hc) x ≡{n}≡ CCPO.csup (PProd.chain.chain_snd hc) x
  rw [csup_apply_eq _ sForall_is_sup, csup_apply_eq _ sForall_is_sup]
  exact sForall_ne ⟨fun _ ⟨f, ⟨g, hfg⟩, e⟩ => ⟨g x, ⟨g, ⟨f, hfg⟩, rfl⟩, e ▸ hall _ hfg x⟩,
    fun _ ⟨g, ⟨f, hfg⟩, e⟩ => ⟨f x, ⟨f, ⟨g, hfg⟩, rfl⟩, e ▸ hall _ hfg x⟩⟩

end CoMonotoneFixpoint

end Iris
