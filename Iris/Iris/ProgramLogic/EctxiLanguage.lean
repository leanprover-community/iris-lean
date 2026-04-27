module

meta import Iris.Std.RocqPorting
public import Iris.ProgramLogic.Language
public import Iris.ProgramLogic.EctxLanguage

namespace Iris.ProgramLogic

open Language.Notation EctxLanguage.Notation FromMathlib

@[expose] public section

variable {Expr : Type e}{Val : Type v}{State : Type σ}{Obs : Type o}
variable {EctxItem : Type i}

class EvContextItem
    (Expr : Type e)
    (EctxItem : outParam (Type i)) where
  fillItem : EctxItem → Expr → Expr
  fillItem_inj {K} : Function.Injective (fillItem K)
export EvContextItem (fillItem)

attribute [simp] EvContextItem.fillItem_inj

class EctxItemLanguage
    (Expr     : Type e)
    (EctxItem : outParam <| Type i)
    (State    : outParam <| Type σ)
    (Obs      : outParam <| Type o)
    (Val      : outParam <| Type v)
  extends
    ToVal Expr Val,
    EvContextItem Expr EctxItem,
    BaseStep Expr State Obs where

  fillItem_val (e : Expr) (K : EctxItem) :
    (toVal (fillItem K e)).isSome →
    (toVal e).isSome

  fillItem_no_val_inj (Ki₁ Ki₂ : EctxItem) :
    toVal e₁ = none → toVal e₂ = none →
    fillItem Ki₁ e₁ = fillItem Ki₂ e₂ →
    Ki₁ = Ki₂

  val_stuck : ∀ {e} {σ : State} {obs e' σ' eₜ},
    (e, σ) -<obs>->ᵇ (e', σ', eₜ) → toVal e = none

  -- base_ctx_step_val
  base_ctx_step_val : ∀ {e} {σ : State} {obs e' σ' eₜ},
    (fillItem Ki e, σ) -<obs>->ᵇ (e', σ', eₜ) →
    (toVal e).isSome



namespace EctxItemLanguage

variable [Λ : EctxItemLanguage Expr EctxItem State Obs Val]

abbrev Ectx [EvContext Expr EctxItem] := List EctxItem

instance [EctxItemLanguage Expr EctxItem State Obs Val]:  EvContext Expr (List EctxItem) where
  comp x y := y ++ x
  empty := []
  fill K e := K.foldl (fun x y => fillItem y x) e
  fill_empty (e : Expr) := List.foldl_nil
  fill_comp K₁ K₂ (e : Expr) := Eq.symm List.foldl_append
  fill_inj {K} x y := by
    induction K generalizing x y with
    | nil => simp only [List.foldl_nil, imp_self]
    | cons hd tl IH =>
      simp at IH ⊢
      intro sh
      replace sh := IH _ _ sh
      simpa only [EvContextItem.fillItem_inj, Function.Injective.eq_iff] using sh

export EvContext (fill)

@[rocq_alias fill_app]
theorem fill_append (K1 K2 : List EctxItem) (e : Expr) :
    fill (K1 ++ K2) e = fill K2 (fill K1 e) := by
  dsimp [fill]
  grind

@[elab_as_elim] -- TODO: Properly more this from mathlib
def reverseRec {motive : List α → Sort _} (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) : ∀ l, motive l
  | [] => nil
  | x :: xs => by
    have := List.eq_nil_or_concat (x :: xs)
    cases this
    case inl h => simp at h
    case inr h =>
      obtain ⟨init, l, h⟩ := h
      rw [h]
      have := reverseRec nil append_singleton init
      have := append_singleton init l this
      simpa
termination_by l => l.length
decreasing_by
  simp at h
  calc init.length
    _ < (init ++ [l]).length := by grind
    _ = (x :: xs).length := by grind

theorem fill_val K (e : Expr) :
    (toVal (fill K e)).isSome = true → (toVal e).isSome = true := by
  induction K generalizing e with
  | nil =>
    dsimp [fill]
    grind only
  | cons init last IH =>
    simp only [fill, List.foldl_cons] at IH ⊢
    grind [fill, fillItem_val]

theorem fill_not_val K (e : Expr) :
     (toVal e) = none → (toVal (fill K e)) = none := by
  grind [fill_val, Option.isSome_iff_ne_none]

instance : EctxLanguage Expr (List EctxItem) State Obs Val where
  fill_val K e := fill_val K e
  step_by_val := by
    intros K K' e₁ e₁' σ₁ obs e₂ σ₂ eₜ hfill hred hstep
    induction K using reverseRec generalizing K' e₁ e₂ with
    | nil =>
      simp only [comp, List.append_nil, exists_eq']
    | append_singleton Ks Ki IH =>
      simp [comp]
      simp [fill] at hfill
      cases K' using reverseRec
      · simp at hfill
        subst hfill
        replace hstep := base_ctx_step_val hstep |> fill_val _ _
        grind
      case append_singleton Ks' Ki' trash =>
      simp at *
      have heq : Ki = Ki' := by
        apply Λ.fillItem_no_val_inj Ki Ki' _ _ hfill
        · apply fill_not_val
          assumption
        · apply fill_not_val
          apply val_stuck
          assumption
      subst heq
      simp [Function.Injective.eq_iff] at hfill
      simp [fill] at IH
      obtain ⟨K'', rfl⟩ := IH hfill hred hstep
      exists K''
      simp [comp]
  val_stuck {e σ obs e' σ' eₜ} := val_stuck
  base_ctx_step_val {K e σ₁ obs e₂ σ₂ eₜ} := by
    cases K using reverseRec
    case nil =>
      simp [empty]
    case append_singleton init last IH =>
      intro bstep
      left
      simp [fill_append] at *
      apply fill_val
      apply base_ctx_step_val
      assumption

theorem fill_no_val K (e : Expr) :
    toVal e = none →
    toVal (fill K e) = none := by
  grind [fill_val]

theorem subredexesAreValues (e : Expr) :
    (∀ Ki e', e = fillItem Ki e' → (toVal e').isSome) →
    EctxLanguage.subredexesAreValues e := by
  rintro hsub K e' rfl
  cases K using reverseRec
  case nil => simp [empty]
  case append_singleton init last IH =>
    simp [empty, Option.ne_none_iff_exists]
    suffices isSome : (toVal e').isSome from by
      grind [Option.isSome_iff_exists]
    apply fill_val
    apply hsub
    simp [fill]
    rfl

end EctxItemLanguage
