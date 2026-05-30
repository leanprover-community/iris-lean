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
  wp_wand : ⊢ wp E e Φ -∗ (∀ v, Φ v -∗ Ψ v) -∗ wp E e Ψ
  wp_atomic {e : Expr} (Hatom : Atomic WeaklyAtomic e) :
    (|={E₁, E₂}=> wp E₂ e (iprop% |={E₂, E₁}=> Φ ·)) ⊢ wp E₁ e Φ

class BindAbstractWP (wp : AbstractWP Expr Val GF) extends LawfulAbstractWP wp where
  wp_bind [Context K] : wp E e (fun (v : Val) => iprop% wp E (K v) Φ) ⊣⊢ wp E (K e) Φ

end AbstractWP

noncomputable section EctxLanguage

open Classical

variable {Expr State Obs Val Ectx : Type _} [EctxLanguage Expr Ectx State Obs Val]
variable {GF : BundledGFunctors} {HLC : HasLC} [IrisGS_gen HLC Expr GF]
variable {wp : AbstractWP Expr Val GF} [BindAbstractWP wp]

-- wp_inv_open_maybe_ectxlang
theorem inv_open_maybe_ectxlang (e : Expr) (E₁ E₂ : CoPset) (Φ : Val → IProp GF)
    (Hsub : E₂ ⊆ E₁) (Hred : ∃ σ, PrimStep.Reducible (e, σ)) :
    (|={E₁, E₂}=>
      (∃ (K : Ectx) (e' : Expr),
        ⌜e = fill K e'⌝ ∗ ⌜Atomic .WeaklyAtomic e'⌝ ∗ ⌜∃ σ, BaseStep.Reducible (e', σ)⌝
        ∗ wp E₂ e' (fun v => iprop% |={E₂, E₁}=> wp E₁ (fill K v) Φ)) ∨
      (|={E₂, E₁}=> wp E₁ e Φ))
    ⊢ wp E₁ e Φ := by
  sorry

-- wp_inv_open_maybe_ectxlang_inv
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
  sorry

end EctxLanguage

/-! ### Instances of the abstract classes for iris-lean's real `Wp`.

Mirrors `WP_abstract_weakestpre_gen` and `WP_abstract_ectx_weakestpre_gen`
from `framework/wpre_instantiation.v`. The intuitionistic magic-rule
instance (`WP_abstract_weakestpre_gen_magic_intuitionistic`) is intentionally
omitted — the classical chain uses `wp_inv_open_maybe_ectxlang` instead. -/

section IrisWP

variable {Expr State Obs Val : Type _} [Language Expr State Obs Val]
variable {GF : BundledGFunctors} {HLC : HasLC} [IrisGS_gen HLC Expr GF]

/-- iris-lean's standard `WP` satisfies the abstract 5-law class. -/
instance WP_lawful_abstract :
    LawfulAbstractWP (Expr := Expr) (Val := Val)
      (Wp.wp (PROP := IProp GF) Stuckness.NotStuck) where
  fupd_wp := by sorry
  wp_fupd := by sorry
  wp_value := by sorry
  wp_wand := by sorry
  wp_atomic := by sorry

/-- iris-lean's standard `WP` also satisfies the bind class for ectx
languages. -/
instance WP_bind_abstract :
    BindAbstractWP (Expr := Expr) (Val := Val)
      (Wp.wp (PROP := IProp GF) Stuckness.NotStuck) where
  wp_bind := by sorry

end IrisWP
