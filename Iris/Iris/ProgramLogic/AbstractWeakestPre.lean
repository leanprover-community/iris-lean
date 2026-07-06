/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra
public import Iris.Instances.Lib.FUpd
public import Iris.Instances.Lib.Invariants
public import Iris.BI
public import Iris.BI.WeakestPre
public import Iris.ProofMode
public import Iris.ProgramLogic.Language
public import Iris.ProgramLogic.EctxLanguage
public import Iris.Std.CoPset
public import Iris.ProgramLogic.WeakestPre

namespace Iris

open ProgramLogic Language Language.Notation Std

@[expose] public section

abbrev AbstractWP (Expr Val : Type _) (GF : BundledGFunctors) :=
  CoPset → Expr → (Val → IProp GF) → IProp GF

section AbstractWP

variable {Expr State Obs Val : Type _} [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} {HLC : HasLC} [IrisGS_gen HLC Expr GF]

class InvOpenAbstractWP (wp : AbstractWP Expr Val GF) where
  inv_open_maybe (e : Expr) (E₁ E₂) Φ (Hsub : E₂ ⊆ E₁) :
    (|={E₁, E₂}=>
      (∃ K e', ⌜Context K⌝ ∗ ⌜e = K e'⌝ ∗ ⌜Atomic .WeaklyAtomic e'⌝
        ∗ wp E₂ e' (fun v' => iprop% |={E₂, E₁}=> wp E₁ (K v') Φ)) ∨
      (|={E₂, E₁}=> wp E₁ e Φ))
    ⊢ wp E₁ e Φ

class LawfulAbstractWP (wp : AbstractWP Expr Val GF) where
  fupd_wp : (|={E}=> wp E e Φ) ⊢ wp E e Φ
  wp_fupd {Φ : Val → IProp GF} : (wp E e (iprop% |={E}=> Φ ·)) ⊢ wp E e Φ
  wp_value {v : Val} : wp E v Φ ⊣⊢ |={E}=> Φ v
  wp_wand : wp E e Φ ⊢ (∀ v, Φ v -∗ Ψ v) -∗ wp E e Ψ
  wp_atomic {e : Expr} (Hatom : Atomic .WeaklyAtomic e) :
    (|={E₁, E₂}=> wp E₂ e (iprop% |={E₂, E₁}=> Φ ·)) ⊢ wp E₁ e Φ

class BindAbstractWP (wp : AbstractWP Expr Val GF) extends LawfulAbstractWP wp where
  wp_bind [Context K] : wp E e (fun (v : Val) => iprop% wp E (K v) Φ) ⊣⊢ wp E (K e) Φ

end AbstractWP

noncomputable section EctxLanguage

open Classical

variable {Expr State Obs Val Ectx : Type _} [EctxLanguage Expr Ectx State Obs Val]
variable {GF : BundledGFunctors} {HLC : HasLC} [IrisGS_gen HLC Expr GF]
variable {wp : AbstractWP Expr Val GF} [IWP : BindAbstractWP wp]

theorem inv_open_maybe_ectxlang {e : Expr} {E₁ E₂ : CoPset} {Φ : Val → IProp GF}
    (Hsub : E₂ ⊆ E₁) (Hred : ∃ σ, PrimStep.Reducible (e, σ)) :
    (|={E₁, E₂}=>
      (∃ (K : Ectx) (e' : Expr),
        ⌜e = fill K e'⌝ ∗ ⌜Atomic .WeaklyAtomic e'⌝ ∗ ⌜∃ σ, BaseStep.Reducible (e', σ)⌝
        ∗ wp E₂ e' (fun v => iprop% |={E₂, E₁}=> wp E₁ (fill K v) Φ)) ∨
      (|={E₂, E₁}=> wp E₁ e Φ))
    ⊢ wp E₁ e Φ := by
  iintro H
  obtain ⟨σ, ⟨obs, e', σ', eₜ, @⟨e₁', e₂', K, Hbase⟩⟩⟩ := Hred
  iapply (IWP.wp_bind (K := fill K)).mp
  by_cases Atomic .WeaklyAtomic e₁'
  next Hatomic =>
    iapply IWP.toLawfulAbstractWP.wp_atomic Hatomic (E₂ := E₂)
    imod H with (⟨%K₁, %e', %Hf, %Hat, %Hred, Hwp⟩| H')
    · imodintro
      obtain ⟨σ'', Hred⟩ := Hred
      have Hred' : BaseStep.Reducible (e₁', σ) := ⟨_, _, _, _, Hbase⟩
      obtain ⟨rfl, rfl⟩ := EctxLanguage.base_redex_unique Hf Hred' Hred
      simp only [← EvContext.fill_comp, EvContext.fill_empty]
      iapply IWP.toLawfulAbstractWP.wp_wand $$ Hwp
      iintro %v >Hwp2
      itrivial
    · imodintro
      iapply IWP.toLawfulAbstractWP.wp_atomic Hatomic (E₂ := E₁)
      imod H'
      imodintro
      ihave H' := (IWP.wp_bind (K := fill K)).mpr $$ H'
      iapply IWP.wp_wand $$ H' []
      iintro %v Hwp
      iapply fupd_mask_intro_subseteq Hsub $$ [$]
  next Hnonatomic =>
    iapply IWP.toLawfulAbstractWP.fupd_wp
    imod H with (⟨%K₁, %e', %Hf, %Hat, %Hred, Hwp⟩| H')
    · obtain ⟨σ'', Hred⟩ := Hred
      have Hred' : BaseStep.Reducible (e₁', σ) := ⟨_, _, _, _, Hbase⟩
      obtain ⟨_, rfl⟩ := EctxLanguage.base_redex_unique Hf Hred' Hred
      exact Hnonatomic Hat |>.elim
    · imod H'
      ihave H' := (IWP.wp_bind (K := fill K)).mpr $$ H'
      itrivial

theorem inv_open_maybe_ectxlang_inv (e : Expr) (E : CoPset) (N : Namespace)
    (P : IProp GF) (Φ : Val → IProp GF)
    (Hsub : ↑N ⊆ E) (Hred : ∃ σ, PrimStep.Reducible (e, σ)) :
    (inv N P ∗
      ((▷ P) ={E \ ↑N}=∗
        (∃ (K : Ectx) (e' : Expr),
          ⌜e = fill K e'⌝ ∗ ⌜Atomic .WeaklyAtomic e'⌝ ∗ ⌜∃ σ, BaseStep.Reducible (e', σ)⌝
          ∗ wp (E \ ↑N) e' (fun v => iprop% P ∗ wp E (fill K v) Φ)) ∨
        (P ∗ wp E e Φ)))
    ⊢ wp E e Φ := by
  iintro ⟨#Hinv, H⟩
  iapply inv_open_maybe_ectxlang (E₂ := E \ nclose N) LawfulSet.diff_subset_left Hred
  imod inv_acc Hsub $$ Hinv with ⟨HP, Hclose⟩
  imod H $$ HP with (⟨%K, %e', %He, %Hat, %Hred, H⟩|⟨HP, H⟩)
  · imodintro
    ileft
    iexists K, e'
    iframe %He %Hat %Hred
    iapply IWP.wp_wand $$ H
    iintro %v ⟨HP, Hwp⟩
    imod Hclose $$ HP with -
    itrivial
  · iright
    imod Hclose $$ HP with -
    iapply fupd_mask_intro_subseteq LawfulSet.diff_subset_left $$ [$]

end EctxLanguage

/-! ### Instances of the abstract classes for iris-lean's generic `Wp`. -/

section IrisWP

variable {Expr State Obs Val : Type _} [Language Expr State Obs Val]
variable {GF : BundledGFunctors} {HLC : HasLC} [IrisGS_gen HLC Expr GF]

instance WP_lawful_abstract :
    LawfulAbstractWP (Expr := Expr) (Val := Val) (Wp.wp (PROP := IProp GF) Stuckness.NotStuck) where
  fupd_wp := fupd_wp
  wp_fupd := wp_fupd
  wp_value := wp_value_fupd'
  wp_wand := wp_wand
  wp_atomic _ := wp_atomic

instance WP_bind_abstract : BindAbstractWP (Expr := Expr) (Val := Val)
      (Wp.wp (PROP := IProp GF) Stuckness.NotStuck) where
  wp_bind := ⟨wp_bind _, wp_bind_inv _⟩

-- TODO: Any idea how to get rid of the istops?

theorem wp_inv_open_maybe_of_not_val {e : Expr} {E₁ E₂ : CoPset} {Φ : Val → IProp GF}
    (Hnv : ToVal.toVal e = none) :
    (|={E₁, E₂}=>
      (∃ K e', ⌜Context K⌝ ∗ ⌜e = K e'⌝ ∗ ⌜Atomic .WeaklyAtomic e'⌝ ∗
        Wp.wp (Val := Val) Stuckness.NotStuck E₂ e'
          (fun v' => iprop% |={E₂, E₁}=> Wp.wp (Val := Val) Stuckness.NotStuck E₁ (K v') Φ)) ∨
      (|={E₂, E₁}=> Wp.wp (Val := Val) Stuckness.NotStuck E₁ e Φ))
    ⊢ Wp.wp (Val := Val) Stuckness.NotStuck E₁ e Φ := by
  iintro H
  rw [IProp.ext wp_unfold, wp.pre, Hnv]
  simp only
  imod H with (⟨%K, %e', %Hctx, %Haux, %hato, Hwp⟩| >$)
  subst Haux
  -- FIXME: Why does this exit the proofmode?
  refine .trans wp_unfold.mp ?_
  rw (occs := [1]) [wp.pre]
  iintro Hwp
  rcases He' : toVal e' with (_|v'); rotate_left
  · imod Hwp; imod Hwp
    istop
    refine .trans wp_unfold.mp ?_
    rw (occs := [1]) [wp.pre]
    simp [coe_of_toVal_eq_some He', Hnv]
  · dsimp only
    iintro %σ %n %κ %κs %n₂ Hσ
    imod Hwp $$ Hσ with ⟨%Hred, Hc⟩
    imodintro
    have aux := Context.reducible_fill K Hred
    iframe %aux; clear aux
    iintro %e₂ %σ₂ %efs %H Hlc
    obtain ⟨e₂, rfl, Hprim⟩ := Context.primStep_fill_inv (toVal_none_of_reducible Hred) H
    ispecialize Hc $$ %e₂ %σ₂ %efs %Hprim Hlc
    iapply step_fupdN_mono $$ Hc
    iintro Hc
    imod Hc with ⟨Hst, Hwp, $⟩
    replace Hprim : PrimStep.Irreducible (e₂, σ₂) := hato.atomic Hprim
    -- FIXME: Why does this exit the proofmode?
    istop
    refine .trans (BI.sep_mono .rfl wp_unfold.mp) ?_
    rw (occs := [1]) [wp.pre]
    iintro ⟨Hst, Hwp⟩
    rcases He₂' : toVal e₂ with (_|v₂) <;> dsimp only
    · imod Hwp $$ %_ %_ %κs %.nil [Hst] with ⟨%Hredu, H⟩
      · rw [List.append_nil κs]; iframe
      grind
    · imod Hwp with >Hwp
      rw [coe_of_toVal_eq_some He₂']
      iframe

theorem wp_inv_open_maybe (e : Expr) (E₁ E₂ : CoPset) (Φ : Val → IProp GF) :
    (|={E₁, E₂}=>
      (∃ K e', ⌜Context K⌝ ∗ ⌜e = K e'⌝ ∗ ⌜Atomic .WeaklyAtomic e'⌝ ∗
          Wp.wp (PROP := IProp GF) (Val := Val) Stuckness.NotStuck E₂ e'
          (fun v' => iprop% |={E₂, E₁}=> Wp.wp (Val := Val) Stuckness.NotStuck E₁ (K v') Φ)) ∨
      (|={E₂, E₁}=> Wp.wp (Val := Val) Stuckness.NotStuck E₁ e Φ))
    ⊢ Wp.wp (Val := Val) Stuckness.NotStuck E₁ e Φ := by
  iintro H
  rcases Hv : toVal e with (_|v);
    iapply wp_inv_open_maybe_of_not_val Hv $$ [$]
  rw [← coe_of_toVal_eq_some Hv]
  iapply wp_atomic (E2 := E₂)
  imod H with (⟨%K, %e', %Hctx, %He, %Hato, H⟩| H);
  · rcases Hv' : toVal e' with (_|v')
    · exfalso
      have h1 := He.symm ▸ Hctx.toVal_eq_none_fill Hv'
      simp at h1
    · rw [← coe_of_toVal_eq_some Hv']
      have hKv : K (↑v' : Expr) = ↑v := by rw [coe_of_toVal_eq_some Hv']; exact He.symm
      imodintro
      iapply wp_value_fupd (v := v) ⟨rfl⟩
      imodintro
      imod (wp_value_fupd (v := v') ⟨rfl⟩).mp $$ H with H
      imod H
      ihave H := (wp_value_fupd (v := v) ⟨hKv.symm⟩).mp $$ H
      iframe
  · imodintro
    iapply wp_value_fupd (v := v) ⟨rfl⟩
    imodintro
    imod H
    ihave _ := (wp_value_fupd (v := v) ⟨rfl⟩).mp $$ H
    iframe

instance WP_inv_open_abstract :
    InvOpenAbstractWP (Expr := Expr) (Val := Val) (Wp.wp (PROP := IProp GF) Stuckness.NotStuck) where
  inv_open_maybe e E₁ E₂ Φ _ := wp_inv_open_maybe e E₁ E₂ Φ

end IrisWP
