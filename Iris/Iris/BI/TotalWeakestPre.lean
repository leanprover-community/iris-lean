/-
Copyright (c) 2026 Fernando Leal, Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.ProgramLogic.WeakestPre
public import Iris.Instances.Lib.Monotone

namespace Iris

open ProgramLogic Language.Notation Std

@[expose] public section

export StateInterp (stateInterp)

variable {hlc : outParam HasLC} {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]

abbrev Stuckness.MaybeReducibleNoObs : Stuckness → Expr × State → Prop
| .NotStuck, (e₁, σ₁) => PrimStep.ReducibleNoObs (e₁, σ₁)
| _, _ => True

@[rocq_alias twp_pre]
def twp.pre (s : Stuckness) (wp : CoPset -> Expr -> (Val -> IProp GF) -> IProp GF) (E : CoPset)
    (e₁ : Expr) (Φ : Val -> IProp GF) : IProp GF :=
  match toVal e₁ with
  | some v => iprop(|={E}=> Φ v)
  | none => iprop(∀ (σ₁ : State) (ns : Nat) (obs' : List Obs) (nt : Nat),
    stateInterp σ₁ ns obs' nt ={E,∅}=∗
    ⌜s.MaybeReducibleNoObs (e₁, σ₁)⌝ ∗
    ∀ obs e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ)⌝ ={E,∅}=∗
      ⌜obs = []⌝ ∗ stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
      wp E e₂ Φ ∗ [∗list] e' ∈ eₜ, wp ⊤ e' ι.forkPost)

open Function in
@[rocq_alias twp_pre']
def twp.pre' (s : Stuckness) (wp : (CoPset × Expr) × (Val -> IProp GF) -> IProp GF) :=
    uncurry <| uncurry <| @twp.pre hlc Expr State Obs Val Λ GF ι s (curry <| curry wp)

instance twp.pre_mono' [OFE Expr] [OFE CoPset] (s : Stuckness) : BIMonoPred (@twp.pre' hlc Expr State Obs Val Λ GF ι s) where
  mono_pred := by
    intros
    iintro #H %x
    rewrite [← Prod.eta x]
    rewrite [← Prod.eta x.fst]
    unfold pre'
    simp
    unfold pre
    simp
    cases toVal x.fst.snd
    · irevert H %x
      simp
      apply monotone_forall; intro
      apply monotone_forall; intro
      apply monotone_forall; intro
      apply monotone_forall; intro
      apply monotone_wand
      · exact antitone_const
      · apply monotone_fupd
        apply monotone_sep
        · exact monotone_const
        · apply monotone_forall; intro
          apply monotone_forall; intro
          apply monotone_forall; intro
          apply monotone_forall; intro
          apply monotone_wand
          · exact monotone_const
          · apply monotone_fupd
            apply monotone_sep
            · exact monotone_const
            · apply monotone_sep
              · exact monotone_const
              · apply monotone_sep
                · apply monotone_id'
                · apply monotone_bigSepL_mono
                  intros
                  apply monotone_const'
    · irevert H %x
      apply monotone_const
  mono_pred_ne := sorry
