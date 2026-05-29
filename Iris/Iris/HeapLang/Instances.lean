/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.HeapLang.Syntax
public import Iris.HeapLang.Notation
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

instance : Language.PureExec True 1 hl(if #true then {e1} else {e2}) e1 where
  pureExec _ := by
    refine Relation.Iterate.head ?_ (.rfl _)
    constructor
    · intro σ
      exists e1, σ, []
      refine BaseStep.ContextStep.intro (K := []) ?_
      constructor
    · intro σ1 σ2 κs e2' efs Hstep
      have hsr : EctxLanguage.SubredexesAreValues (Exp.if (.val (.lit (.bool true))) e1 e2) := by
        apply EctxItemLanguage.subredexes_are_values
        intro Ki e_inner heq
        cases Ki <;> try (cases heq; done)
        cases heq
        simp [toVal]
      cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
      exact ⟨rfl, rfl, rfl, rfl⟩

instance : Language.PureExec True 1 hl(if #false then {e1} else {e2}) e2 where
  pureExec _ := by
    refine Relation.Iterate.head ?_ (.rfl _)
    constructor
    · intro σ
      exists e2, σ, []
      refine BaseStep.ContextStep.intro (K := []) ?_
      constructor
    · intro σ1 σ2 κs e2' efs Hstep
      have hsr : EctxLanguage.SubredexesAreValues (Exp.if (.val (.lit (.bool false))) e1 e2) := by
        apply EctxItemLanguage.subredexes_are_values
        intro Ki e_inner heq
        cases Ki <;> try (cases heq; done)
        cases heq
        simp [toVal]
      cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
      exact ⟨rfl, rfl, rfl, rfl⟩

instance {f x : Binder} {e : Exp} {v : Val} : Language.PureExec True 1 (.app (.val (.rec_ f x e)) v) ((e.subst f (.rec_ f x e)).subst x v) where
  pureExec _ := by
    refine Relation.Iterate.head ?_ (.rfl _)
    constructor
    · intro σ
      exists ((e.subst f (.rec_ f x e))).subst x v, σ, []
      refine BaseStep.ContextStep.intro (e₂ := (e.subst f (.rec_ f x e)).subst x v) (K := []) ?_
      apply BaseStep.betaS
      rfl
    · intro σ1 σ2 κs e2' efs Hstep
      have hsr : EctxLanguage.SubredexesAreValues (Exp.app (.val (.rec_ f x e)) v) := by
        apply EctxItemLanguage.subredexes_are_values
        intro Ki e_inner heq
        cases Ki <;> try (cases heq; done)
        · cases heq; simp [toVal, expToVal]
        · cases heq; simp
      cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
      rename_i H
      refine ⟨rfl, rfl, H.symm, rfl⟩

end Iris.HeapLang
