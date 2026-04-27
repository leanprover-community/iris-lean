/-
Copyright (c) 2026 Fernando Leal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

meta import Iris.Std.RocqPorting
public import Iris.ProgramLogic.Language
public import Iris.ProgramLogic.EctxLanguage

namespace Iris.ProgramLogic

open Language.Notation EctxLanguage.Notation FromMathlib

@[expose] public section

variable {Expr : Type e}{Val : Type v}{State : Type σ}{Obs : Type o}
variable {EctxItem : Type i}

class EctxItemLanguage
    (Expr     : Type e)
    (EctxItem : outParam <| Type i)
    (State    : outParam <| Type σ)
    (Obs      : outParam <| Type o)
    (Val      : outParam <| Type v)
  extends
    ToVal Expr Val,
    BaseStep Expr State Obs where
  fillItem : EctxItem → Expr → Expr
  fillItem_inj {K} : Function.Injective (fillItem K)

  fillItem_val (e : Expr) (K : EctxItem) :
    (toVal (fillItem K e)).isSome →
    (toVal e).isSome

  fillItem_no_val_inj {e₁ e₂ : Expr} (Ki₁ Ki₂ : EctxItem) :
    toVal e₁ = none → toVal e₂ = none →
    fillItem Ki₁ e₁ = fillItem Ki₂ e₂ →
    Ki₁ = Ki₂

  val_stuck : ∀ {e} {σ : State} {obs e' σ' eₜ},
    (e, σ) -<obs>->ᵇ (e', σ', eₜ) → toVal e = none

  -- base_ctx_step_val
  base_ctx_step_val {Ki : EctxItem} : ∀ {e} {σ : State} {obs e' σ' eₜ},
    (fillItem Ki e, σ) -<obs>->ᵇ (e', σ', eₜ) →
    (toVal e).isSome

attribute [rocq_alias fill_item] EctxItemLanguage.fillItem
attribute [rocq_alias fill_item_inj] EctxItemLanguage.fillItem_inj
attribute [rocq_alias fill_item_val] EctxItemLanguage.fillItem
attribute [rocq_alias fill_item_no_val_inj] EctxItemLanguage.fillItem_no_val_inj

attribute [simp] EctxItemLanguage.fillItem_inj
attribute [grind →] EctxItemLanguage.fillItem_val
attribute [grind →] EctxItemLanguage.val_stuck
attribute [grind →] EctxItemLanguage.base_ctx_step_val

namespace EctxItemLanguage

variable [Λ : EctxItemLanguage Expr EctxItem State Obs Val]

abbrev Ectx [EctxItemLanguage Expr EctxItem State Obs Val] := List EctxItem

@[grind, rocq_alias ectxi_lang_ctx_item]
instance [Λ : EctxItemLanguage Expr EctxItem State Obs Val] :
    EvContext Expr Λ.Ectx where
  comp x y := y ++ x
  empty := []
  fill K e := K.foldl (fun x y => fillItem y x) e
  fill_empty (e : Expr) := List.foldl_nil
  fill_comp K₁ K₂ (e : Expr) := Eq.symm List.foldl_append
  fill_inj {K} x y := by
    induction K generalizing x y <;> grind only [= List.foldl_nil, = List.foldl_cons, !fillItem_inj]

export EvContext (fill)

section SelectedGrindRflLemmas

@[grind =, simp]
theorem fill_cons Ki K (e : Expr) : fill (Ki :: K) e = fill K (fillItem Ki e) := rfl

@[grind =, simp]
theorem fill_nil (e : Expr) : fill [] e = e := rfl

end SelectedGrindRflLemmas

@[rocq_alias fill_app, grind =, simp]
theorem fill_append (K1 K2 : Λ.Ectx) (e : Expr) :
    fill (K1 ++ K2) e = fill K2 (fill K1 e) :=
  EvContext.fill_comp K2 K1 e |>.symm

@[grind →]
theorem fill_val K (e : Expr) :
    (toVal (fill K e)).isSome = true → (toVal e).isSome = true := by
  induction K generalizing e <;> grind [fillItem_val]

-- NOTE: Would it be worth having an `isVal` predicate for `Expr`, basically defined
-- as `toVal e |>.isSome`, so that we could rephrase all instances of `(toVal e).isSome`
-- as `isVal e` and `toVal e = none` as `¬ isVal e`. That way tactics like `grind` would
-- be able to match on `toVal`, since as it stands `grind` patterns cannot include `=`,
-- which means `toVal e = none` is not as well supported.

@[rocq_alias EctxLanguageOfEctxi]
instance : EctxLanguage Expr Λ.Ectx State Obs Val where
  fill_val K e := fill_val K e
  step_by_val := by
    intros K K' e₁ e₁' σ₁ obs e₂ σ₂ eₜ hfill hred hstep
    induction K using List.reverseRec generalizing K' e₁ e₂ with
    | nil =>
      simp only [comp, List.append_nil, exists_eq']
    | append_singleton Ks Ki IH =>
      simp only [comp]
      cases K' using List.reverseCases with
      | nil =>
        simp only [fill_append, fill_cons, fill_nil] at hfill
        subst hfill
        replace hstep := base_ctx_step_val hstep |> fill_val _ _
        grind
      | append_singleton Ks' Ki' =>
        simp only [fill_append, fill_cons, fill_nil] at hfill
        obtain rfl : Ki = Ki' := by
          apply fillItem_no_val_inj Ki Ki' _ _ hfill <;> grind [fill_val, Option.isSome_iff_ne_none]
        simp only [fillItem_inj, Function.Injective.eq_iff] at hfill
        obtain ⟨K'', rfl⟩ := IH hfill hred hstep
        exists K''
        simp [comp]
  val_stuck {e σ obs e' σ' eₜ} := val_stuck
  base_ctx_step_val {K e σ₁ obs e₂ σ₂ eₜ} := by
    cases K using List.reverseRec <;> grind

theorem fill_not_val K (e : Expr) :
    toVal e = none →
    toVal (fill K e) = none := by
  grind only [=> EctxLanguage.fill_not_val]

@[rocq_alias ectxi_language_sub_redexes_are_values]
theorem subredexes_are_values (e : Expr) :
    (∀ Ki e', e = fillItem Ki e' → (toVal e').isSome) →
    EctxLanguage.SubredexesAreValues e := by
  rintro hsub K e' rfl
  cases K using List.reverseRec
  case nil => simp [empty]
  case append_singleton init last IH =>
    simp only [empty, List.append_eq_nil_iff, List.cons_ne_self, and_false, imp_false]
    simp only [Option.ne_none_iff_exists', ←Option.isSome_iff_exists]
    simp only [fill_append, fill_cons, fill_nil] at hsub
    grind only [→ fill_val]

end EctxItemLanguage
