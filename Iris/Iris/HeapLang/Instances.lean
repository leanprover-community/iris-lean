/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.HeapLang.Syntax
public import Iris.HeapLang.Semantics
public import Iris.ProgramLogic.EctxiLanguage
public import Std.Data.ExtTreeMap
public import Std.Data.ExtTreeSet
public import Iris.Std.FromMathlib

@[expose] public section
namespace Iris.HeapLang

open ProgramLogic

@[reducible]
def expToVal : Exp → Option Val
  | .val v => some v
  | _      => none

instance : EctxItemLanguage Exp ECtxItem State Observation Val where
  toVal    := expToVal
  ofVal    := .val
  coe_of_toVal_eq_some {e v} h := by
    cases e <;> simp_all [expToVal]
  toVal_coe _ := rfl
  baseStep := fun ⟨e, σ⟩ obs ⟨e', σ', eps⟩ => BaseStep e σ obs e' σ' eps
  fillItem := ECtxItem.fill
  fillItem_inj {Ki} := by
    induction Ki with
    | resolveL K _ _ IH =>
      intro e1 e2 h
      simp only [ECtxItem.fill, Exp.resolve.injEq] at h
      exact IH h.1
    | _ =>
      intro e1 e2 h
      simp only [ECtxItem.fill] at h
      simp_all
  fillItem_val e Ki h := by
    cases Ki <;> simp_all [ECtxItem.fill, expToVal]
  fillItem_no_val_inj Ki₁ Ki₂ hv1 hv2 heq := by
    induction Ki₁ generalizing Ki₂ <;> induction Ki₂ <;> simp only [ECtxItem.fill] at heq <;> grind only
  val_stuck h := by cases h <;> rfl
  base_ctx_step_val {Ki} {e} := by
    induction Ki generalizing e with
    | resolveL K _ _ IH =>
      intro σ obs e' σ' eps h
      simp only [ECtxItem.fill] at h
      cases h with
      | resolveS _ _ _ _ _ _ _ _ inner _ => exact IH inner
    | _ =>
      intro σ obs e' σ' eps h
      simp only [ECtxItem.fill] at h
      cases h <;> simp [expToVal, Option.isSome_some]

/-! ### Metatheory about `BaseStep` / `PrimStep` for heap_lang.

Mirrors `case_studies/heaplang/heap_lang_commons.v`. Prophecy lemmas
(`base_step_more_proph_ids`, `prim_step_more_proph_ids`) are intentionally
skipped — see `PORTING_NOTES.md`. -/

open ProgramLogic ProgramLogic.Language

/-- `Resolve` weirdness lemma: if one base step reaches a value, every base
step from the same expression reaches a value too. -/
theorem base_step_to_val_always_to_val
    {e₁ : Exp} {σ₁ₐ : State} {κsₐ : List Observation} {v₂ₐ : Val} {σ₂ₐ : State}
    {efsₐ : List Exp} {σ₁ᵦ : State} {κsᵦ : List Observation}
    {e₂ᵦ : Exp} {σ₂ᵦ : State} {efsᵦ : List Exp}
    (h₁ : BaseStep e₁ σ₁ₐ κsₐ (Exp.val v₂ₐ) σ₂ₐ efsₐ)
    (h₂ : BaseStep e₁ σ₁ᵦ κsᵦ e₂ᵦ σ₂ᵦ efsᵦ) :
    (expToVal e₂ᵦ).isSome := by
  sorry

/-- `Resolve` weirdness lemma lifted to `PrimStep`. -/
theorem prim_step_to_val_always_to_val
    {e₁ : Exp} {σ₁ₐ : State} {κsₐ : List Observation} {v₂ₐ : Val} {σ₂ₐ : State}
    {efsₐ : List Exp} {σ₁ᵦ : State} {κsᵦ : List Observation}
    {e₂ᵦ : Exp} {σ₂ᵦ : State} {efsᵦ : List Exp}
    (h₁ : PrimStep.primStep (e₁, σ₁ₐ) κsₐ (Exp.val v₂ₐ, σ₂ₐ, efsₐ))
    (h₂ : PrimStep.primStep (e₁, σ₁ᵦ) κsᵦ (e₂ᵦ, σ₂ᵦ, efsᵦ)) :
    (expToVal e₂ᵦ).isSome := by
  sorry

/-- A base step that reaches a value witnesses atomicity of the source. -/
theorem base_step_to_val_atomic
    {e₁ : Exp} {σ₁ₐ : State} {κsₐ : List Observation} {v₂ₐ : Val}
    {σ₂ₐ : State} {efsₐ : List Exp} (a : Atomicity)
    (h : BaseStep e₁ σ₁ₐ κsₐ (Exp.val v₂ₐ) σ₂ₐ efsₐ) :
    Atomic (State := State) a e₁ := by
  sorry

/- TODO: Coq has a `Hint Extern (Atomic _ _) => by eapply base_step_to_val_atomic`.
   No Lean equivalent — `BaseStep` is not a typeclass, so we can't make this
   a real instance. At use sites, manually apply `base_step_to_val_atomic`. -/

end Iris.HeapLang
