/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

public import Iris.HeapLang.VCGen.Call

@[expose] public section

/-!
# Recursive functions by Löb induction

A call `rec f x := body` applied to `v` has the specification `rec_inv_nn_spec` or
`rec_inv_na_spec` when `f` occurs in `body`. The user states an invariant `inv : RecInvariant GF`
in continuation form: `inv w Φ` is the precondition of the call `f w` whose continuation is `Φ`.
The premise `step` verifies `body` once, under the resource `loebHyp clo inv` and with the
recursive closure marked as `loebSelf clo`. At a recursive call, `loebSelf_spec` lends
`loebHyp clo inv` to the callee and returns it through the continuation.

For the divergent `loop := rec loop n := loop n` and `inv := fun _ _ => emp`, the step goal
`loebHyp clo inv ∗ emp ⊑ wp (loebSelf clo w) Φ` closes by `loebSelf_spec`, so
`hl⦃ emp ⦄ loop #n ⦃ fun _ => ⌜False⌝ ⦄` holds although no measure decreases.

A closure in which `f` does not occur, among them every `λ` and `let`, β-reduces with the
specifications of `Iris.HeapLang.VCGen`.
-/

open Iris Iris.BI Iris.ProgramLogic Iris.HeapLang Iris.VCGen Lean.Order Std.WP

namespace Iris.HeapLang.VCGen

/-- The variable `x` occurs in the expression. Binders that shadow `x` are not taken into
account, so the class can hold for an expression in which `x` occurs only bound. -/
class Mentions (x : String) (e : Exp) : Prop

instance : Mentions x (.var x) := ⟨⟩
instance [Mentions x e] : Mentions x (.rec_ f y e) := ⟨⟩
instance [Mentions x e] : Mentions x (.app e e1) := ⟨⟩
instance [Mentions x e] : Mentions x (.app e0 e) := ⟨⟩
instance [Mentions x e] : Mentions x (.unop op e) := ⟨⟩
instance [Mentions x e] : Mentions x (.binop op e e1) := ⟨⟩
instance [Mentions x e] : Mentions x (.binop op e0 e) := ⟨⟩
instance [Mentions x e] : Mentions x (.if e e1 e2) := ⟨⟩
instance [Mentions x e] : Mentions x (.if e0 e e2) := ⟨⟩
instance [Mentions x e] : Mentions x (.if e0 e1 e) := ⟨⟩
instance [Mentions x e] : Mentions x (.pair e e1) := ⟨⟩
instance [Mentions x e] : Mentions x (.pair e0 e) := ⟨⟩
instance [Mentions x e] : Mentions x (.fst e) := ⟨⟩
instance [Mentions x e] : Mentions x (.snd e) := ⟨⟩
instance [Mentions x e] : Mentions x (.injL e) := ⟨⟩
instance [Mentions x e] : Mentions x (.injR e) := ⟨⟩
instance [Mentions x e] : Mentions x (.case e e1 e2) := ⟨⟩
instance [Mentions x e] : Mentions x (.case e0 e e2) := ⟨⟩
instance [Mentions x e] : Mentions x (.case e0 e1 e) := ⟨⟩
instance [Mentions x e] : Mentions x (.allocN e e1) := ⟨⟩
instance [Mentions x e] : Mentions x (.allocN e0 e) := ⟨⟩
instance [Mentions x e] : Mentions x (.free e) := ⟨⟩
instance [Mentions x e] : Mentions x (.load e) := ⟨⟩
instance [Mentions x e] : Mentions x (.store e e1) := ⟨⟩
instance [Mentions x e] : Mentions x (.store e0 e) := ⟨⟩
instance [Mentions x e] : Mentions x (.cmpXchg e e1 e2) := ⟨⟩
instance [Mentions x e] : Mentions x (.cmpXchg e0 e e2) := ⟨⟩
instance [Mentions x e] : Mentions x (.cmpXchg e0 e1 e) := ⟨⟩
instance [Mentions x e] : Mentions x (.xchg e e1) := ⟨⟩
instance [Mentions x e] : Mentions x (.xchg e0 e) := ⟨⟩
instance [Mentions x e] : Mentions x (.faa e e1) := ⟨⟩
instance [Mentions x e] : Mentions x (.faa e0 e) := ⟨⟩
instance [Mentions x e] : Mentions x (.fork e) := ⟨⟩
instance [Mentions x e] : Mentions x (.resolve e e1 e2) := ⟨⟩
instance [Mentions x e] : Mentions x (.resolve e0 e e2) := ⟨⟩
instance [Mentions x e] : Mentions x (.resolve e0 e1 e) := ⟨⟩

/-- The invariant of a recursive function: `inv w Φ` is the precondition of the call with
argument `w` and continuation `Φ`. -/
@[spec_invariant_type]
def RecInvariant (GF : BundledGFunctors) := Val → (Val → IProp GF) → IProp GF

variable {hlc : HasLC} {GF : BundledGFunctors} [HeapLangGS hlc GF] {s : Stuckness} {E : CoPset}
  {Q : Val → IProp GF} {ε : EStack⟨⟩}

local notation "ov " v:max => (ToVal.ofVal (Expr := Exp) v)

theorem beta_later (f y : Binder) (e : Exp) (v : Val) (Φ : Val → IProp GF) :
    iprop(▷ Wp.wp (PROP := IProp GF) s E (msubst (consB f (.rec_ f y e) (consB y v [])) e) Φ) ⊢
      Wp.wp (PROP := IProp GF) s E (Exp.app (ov (Val.rec_ f y e)) (ov v)) Φ := by
  rw [← beta_eq]
  refine BIBase.Entails.trans ?_ (wp_pure_step_later (e₁ := Exp.app (ov (Val.rec_ f y e)) (ov v)) trivial)
  exact later_mono (wand_intro sep_elim_left)

/-- The recursive closure `clo` inside its own body. It is `clo`, kept opaque so that only
`loebSelf_spec` applies to a recursive call. -/
def loebSelf (clo : Val) : Val := clo

/-- The Löb resource of the recursive closure `clo`: every call that meets the invariant has the
weakest precondition of its continuation. -/
def loebHyp (s : Stuckness) (E : CoPset) (clo : Val) (inv : RecInvariant GF) : IProp GF :=
  iprop(□ ∀ u, ∀ Ψ : Val → IProp GF, inv u Ψ -∗
    Wp.wp (PROP := IProp GF) s E (Exp.app (ov clo) (ov u)) Ψ)

instance {clo : Val} {I : RecInvariant GF} : Persistent (loebHyp s E clo I) := by
  unfold loebHyp
  infer_instance

@[spec] theorem loebSelf_spec (clo : Val) (inv : RecInvariant GF) (u : Val) :
    htriple (Exp.app (ov (loebSelf clo)) (ov u))
      (iprop(loebHyp s E clo inv ∗
        inv u (fun r => PreservesSup.upperAdjoint (BIBase.sep (loebHyp s E clo inv)) (Q r)))) Q := by
  apply triple_of_entails
  simp only [upperAdjoint_sep_eq, loebSelf]
  unfold loebHyp
  iintro ⟨#HG, Hinv⟩
  ihave Hwp := HG $$ %u %_ Hinv
  iapply wp_wand $$ Hwp
  iintro %r Hr
  iapply Hr
  iexact HG

theorem rec_inv_triple (f : String) (x : Binder) (body : Exp) (inv : RecInvariant GF) (v : Val)
    (step : ∀ (w : Val) (Φ : Val → IProp GF),
      htriple (msubst (consB (.named f) (loebSelf (.rec_ (.named f) x body)) (consB x w [])) body) (iprop(loebHyp s E (.rec_ (.named f) x body) inv ∗ inv w Φ)) Φ) :
    htriple (Exp.app (ov (Val.rec_ (.named f) x body)) (ov v)) (inv v Q) Q := by
  have hall : (BIBase.emp : IProp GF) ⊢ iprop(∀ u, ∀ Ψ : Val → IProp GF,
      inv u Ψ -∗ Wp.wp (PROP := IProp GF) s E (Exp.app (ov (.rec_ (.named f) x body)) (ov u)) Ψ) := by
    iloeb as IH
    iintro _ %u %Ψ Hinv
    iapply beta_later
    inext
    have hb : iprop(loebHyp s E (.rec_ (.named f) x body) inv ∗ inv u Ψ) ⊢ Wp.wp (PROP := IProp GF) s E
        (msubst (consB (.named f) (.rec_ (.named f) x body) (consB x u [])) body) Ψ :=
      (step u Ψ).le_wp
    iapply hb
    isplitr [Hinv]
    · unfold loebHyp
      imodintro
      iintro %u' %Ψ'
      iapply IH $$ []
      itrivial
    · iexact Hinv
  apply triple_of_entails
  refine BIBase.Entails.trans (BI.emp_sep.2) (BIBase.Entails.trans (sep_mono_left hall) ?_)
  iintro ⟨H, Hinv⟩
  iapply H $$ %v %Q Hinv

@[spec high] theorem rec_inv_nn_spec (f y : String) (body : Exp) [Mentions f body]
    (inv : RecInvariant GF) (v : Val)
    (step : ∀ (w : Val) (Φ : Val → IProp GF),
      htriple (msubst [(f, loebSelf (.rec_ (.named f) (.named y) body)), (y, w)] body) (iprop(loebHyp s E (.rec_ (.named f) (.named y) body) inv ∗ inv w Φ)) Φ) :
    htriple (Exp.app (ov (Val.rec_ (.named f) (.named y) body)) (ov v)) (inv v Q) Q :=
  rec_inv_triple f (.named y) body inv v step

@[spec high] theorem rec_inv_na_spec (f : String) (body : Exp) [Mentions f body]
    (inv : RecInvariant GF) (v : Val)
    (step : ∀ (w : Val) (Φ : Val → IProp GF),
      htriple (msubst [(f, loebSelf (.rec_ (.named f) .anon body))] body) (iprop(loebHyp s E (.rec_ (.named f) .anon body) inv ∗ inv w Φ)) Φ) :
    htriple (Exp.app (ov (Val.rec_ (.named f) .anon body)) (ov v)) (inv v Q) Q :=
  rec_inv_triple f .anon body inv v step

end Iris.HeapLang.VCGen
