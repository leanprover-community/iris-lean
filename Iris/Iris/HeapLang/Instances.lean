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

instance instEctxItemLanguageExp : EctxItemLanguage Exp ECtxItem State Observation Val where
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
      simp_all [ECtxItem.fill]
  fillItem_val e Ki h := by
    cases Ki <;> simp_all [ECtxItem.fill, toVal]
  fillItem_no_val_inj Ki₁ Ki₂ hv1 hv2 heq := by
    induction Ki₁ generalizing Ki₂ <;> induction Ki₂
    all_goals simp [ECtxItem.fill] at heq
    all_goals
      repeat' (rcases heq with ⟨_, _⟩)
      simp_all only [toVal, Exp.ofVal]
    all_goals
      grind only
  val_stuck h := by cases h <;> rfl
  base_ctx_step_val {Ki} {e} := by
    induction Ki generalizing e with
    | resolveL K _ _ IH =>
      intro σ obs e' σ' eps h
      cases h with | resolveS _ _ _ _ _ _ _ _ inner _ => exact IH inner
    | _ =>
      intro σ obs e' σ' eps h
      cases h <;> simp [Option.isSome_some, toVal]

instance instPureExecIfTrue: Language.PureExec True 1 hl(if #true then ?e1 else ?e2) e1 where
  pureExec _ := by
    refine Relation.Iterate.once ?_
    constructor
    · intro σ
      exists e1, σ, []
      refine BaseStep.ContextStep.intro (K := []) ?_
      constructor
    · intro σ1 σ2 κs e2' efs Hstep
      have hsr : EctxLanguage.SubredexesAreValues (Exp.if (.ofVal (.lit (.bool true))) e1 e2) := by
        apply EctxItemLanguage.subredexes_are_values
        intro Ki e_inner heq
        cases Ki <;> try (cases heq; done)
        cases heq
        simp [toVal]
      cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
      exact ⟨rfl, rfl, rfl, rfl⟩

instance instPureExecIfFalse : Language.PureExec True 1 hl(if #false then ?e1 else ?e2) e2 where
  pureExec _ := by
    refine Relation.Iterate.once ?_
    constructor
    · intro σ
      exists e2, σ, []
      refine BaseStep.ContextStep.intro (K := []) (by constructor)
    · intro σ1 σ2 κs e2' efs Hstep
      have hsr : EctxLanguage.SubredexesAreValues (Exp.if (.ofVal (.lit (.bool false))) e1 e2) := by
        apply EctxItemLanguage.subredexes_are_values
        intro Ki e_inner heq
        cases Ki <;> try (cases heq; done)
        cases heq
        simp [toVal]
      cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
      exact ⟨rfl, rfl, rfl, rfl⟩

instance instPureExecCaseInjl {v e1 e2} : Language.PureExec True 1 (Exp.case hl(v(injl(?v))) e1 e2) (.app e1 (.ofVal v)) where
  pureExec _ := by
    refine Relation.Iterate.head ?_ (.rfl _)
    refine ⟨fun σ => ?_, @fun σ1 σ2 κs e2' efs Hstep => ?_⟩
    · exists (.app e1 (.ofVal v)), σ, []
      refine BaseStep.ContextStep.intro (K := []) ?_
      constructor
    · have hsr : EctxLanguage.SubredexesAreValues (Exp.case hl(v(injl(?v))) e1 e2) := by
        apply EctxItemLanguage.subredexes_are_values
        intro Ki e_inner heq
        cases Ki <;> try (cases heq; done)
        cases heq
        simp [toVal]
      cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
      exact ⟨rfl, rfl, rfl, rfl⟩

instance instPureExecCaseInjr {v e1 e2} : Language.PureExec True 1 (Exp.case hl(v(injr(?v))) e1 e2) (.app e2 (.ofVal v)) where
  pureExec _ := by
    refine Relation.Iterate.head ?_ (.rfl _)
    refine ⟨fun σ => ?_, @fun σ1 σ2 κs e2' efs Hstep => ?_⟩
    · exists (.app e2 (.ofVal v)), σ, []
      refine BaseStep.ContextStep.intro (K := []) ?_
      constructor
    · have hsr : EctxLanguage.SubredexesAreValues (Exp.case hl(v(injr(?v))) e1 e2) := by
        apply EctxItemLanguage.subredexes_are_values
        intro Ki e_inner heq
        cases Ki <;> try (cases heq; done)
        cases heq
        simp [toVal]
      cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
      exact ⟨rfl, rfl, rfl, rfl⟩

instance instPureExecBeta {f x : Binder} {e : Exp} {v : Val} :
    Language.PureExec True 1 (.app (.ofVal (.rec_ f x e)) (.ofVal v)) ((e.subst f (.rec_ f x e)).subst x v) where
  pureExec _ := by
    refine Relation.Iterate.once ?_
    constructor
    · intro σ
      exists ((e.subst f (.rec_ f x e))).subst x v, σ, []
      refine BaseStep.ContextStep.intro (e₂ := (e.subst f (.rec_ f x e)).subst x v) (K := [])
        (by constructor; rfl)
    · intro σ1 σ2 κs e2' efs Hstep
      have hsr : EctxLanguage.SubredexesAreValues (Exp.app (.ofVal (.rec_ f x e)) v) := by
        apply EctxItemLanguage.subredexes_are_values
        intro Ki e_inner heq
        cases Ki <;> try (cases heq; done)
        · cases heq; simp [toVal]
        · cases heq; simp
      cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
      rename_i H
      refine ⟨rfl, rfl, H.symm, rfl⟩

instance instPureExecRec {f x e} : Language.PureExec True 1 (Exp.rec_ f x e) (.ofVal (.rec_ f x e)) where
  pureExec _ := by
    refine Relation.Iterate.head ?_ (.rfl _)
    refine ⟨fun σ => ?_, @fun σ1 σ2 κs e2' efs Hstep => ?_⟩
    · exists (.ofVal (.rec_ f x e)), σ, []
      refine BaseStep.ContextStep.intro (K := []) ?_
      constructor
    · have hsr : EctxLanguage.SubredexesAreValues (Exp.rec_ f x e) := by
        apply EctxItemLanguage.subredexes_are_values
        intro Ki e_inner heq
        cases Ki <;> try (cases heq; done)
      cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
      exact ⟨rfl, rfl, rfl, rfl⟩


instance PureExec_fst {v1 v2 : Val} : Language.PureExec True 1 hl(fst(v((?v1, ?v2)))) v1 where
  pureExec _ := by
    refine Relation.Iterate.head ?_ (.rfl _)
    constructor
    · intro σ
      exists v1, σ, []
      refine BaseStep.ContextStep.intro (K := []) (by constructor)
    · intro σ1 σ2 κs e2' efs Hstep
      have hsr : EctxLanguage.SubredexesAreValues (Exp.fst (Val.pair v1 v2)) := by
        apply EctxItemLanguage.subredexes_are_values
        intro Ki e_inner heq
        cases Ki <;> try (cases heq; done)
        cases heq; simp [toVal]
      cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
      refine ⟨rfl, rfl, rfl, rfl⟩

instance PureExec_snd {v1 v2 : Val} : Language.PureExec True 1 hl(snd(v((?v1, ?v2)))) v2 where
  pureExec _ := by
    refine Relation.Iterate.once ?_
    constructor
    · intro σ
      exists v2, σ, []
      refine BaseStep.ContextStep.intro (K := []) (by constructor)
    · intro σ1 σ2 κs e2' efs Hstep
      have hsr : EctxLanguage.SubredexesAreValues (Exp.snd (Val.pair v1 v2)) := by
        apply EctxItemLanguage.subredexes_are_values
        intro Ki e_inner heq
        cases Ki <;> try (cases heq; done)
        cases heq; simp [toVal]
      cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
      refine ⟨rfl, rfl, rfl, rfl⟩

instance PureExec_pair {v1 v2 : Val} : Language.PureExec True 1 hl((?v1, ?v2)) hl(v((?v1, ?v2)))  where
  pureExec _ := by
    refine Relation.Iterate.head ?_ (.rfl _)
    constructor
    · intro σ
      exists hl(v(({v1}, {v2}))), σ, []
      refine BaseStep.ContextStep.intro (K := []) (by constructor)
    · intro σ1 σ2 κs e2' efs Hstep
      have hsr : EctxLanguage.SubredexesAreValues hl((?v1, ?v2)) := by
        apply EctxItemLanguage.subredexes_are_values
        intro Ki e_inner heq
        cases Ki <;> try (cases heq; done)
        all_goals cases heq; simp [toVal]
      cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
      refine ⟨rfl, rfl, rfl, rfl⟩


instance instAtomicStore {s} {v1 v2 : Val} : Language.Atomic s hl(?v1 ← ?v2) where
  atomic {σ obs e' σ' eₜ} Hstep := by
    have hsr : EctxLanguage.SubredexesAreValues hl(?v1 ← ?v2) := by
      apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> try (cases heq; done)
      all_goals (cases heq; simp [toVal])
    cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
    rename_i l v Heq
    cases s <;> simp [toVal, Language.val_irreducible]

instance instAtomicSnd {s} {v1 : Val} : Language.Atomic s hl(snd(?v1)) where
  atomic {σ obs e' σ' eₜ} Hstep := by
    have hsr : EctxLanguage.SubredexesAreValues hl(snd(?v1)) := by
      apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> try (cases heq; done)
      · cases heq; simp [toVal]
    cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
    cases s <;> simp [toVal, Language.val_irreducible]

instance instAtomicCmpXChg {s} {v1 v2 v3 : Val} : Language.Atomic s hl(cmpXchg(?v1, ?v2, ?v3)) where
  atomic {σ obs e' σ' eₜ} Hstep := by
    have hsr : EctxLanguage.SubredexesAreValues hl(cmpXchg(?v1, ?v2, ?v3)) := by
      apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> try (cases heq; done)
      all_goals (cases heq; simp [toVal])
    cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
    cases s <;> simp [toVal, Language.val_irreducible]

instance instContextSnd : Language.Context fun x => hl(snd({x})) where
  toVal_eq_none_fill _ := by simp [toVal]
  primStep_fill {e σ obs e' σ' eₜ} Hstep := by
    obtain ⟨Hbase⟩ := Hstep
    rename_i e₁ e₂ K
    have Hstep' := EctxLanguage.fill_primStep (K ++ [ECtxItem.snd]) (eₜ := eₜ) (σ' := σ')
      (e' := e₂) (obs := obs) (σ := σ) (e := e₁)
    simp only [EctxItemLanguage.fill_append, EctxItemLanguage.fill_cons, EctxItemLanguage.fillItem,
      ECtxItem.fill, EctxItemLanguage.fill_nil] at Hstep'
    exact Hstep' $ EctxLanguage.primStep_of_baseStep Hbase
  primStep_fill_inv {e σ obs K_e' σ' eₜ} Heq Hstep := by
    revert Hstep
    generalize Heq' : hl(snd({e})) = e_snd
    intro Hstep
    obtain ⟨Hbase⟩ := Hstep
    rename_i e₁ e₂ K
    revert Heq'
    rw [show K = K.reverse.reverse by simp]
    cases K.reverse with
    | nil =>
      simp only [fill, List.reverse_nil, List.foldl]
      rintro ⟨⟩
      cases Hbase with
      | sndS => simp [toVal] at Heq
      | _ => simp [ECtxItem.fill]
    | cons Ki Ks =>
      cases Ki with
      | snd =>
        simp only [List.reverse_cons, EctxItemLanguage.fill_append, EctxItemLanguage.fill_cons,
          EctxItemLanguage.fillItem, ECtxItem.fill, EctxItemLanguage.fill_nil, Exp.snd.injEq,
          exists_eq_left']
        rintro ⟨⟩
        have Hstep' := EctxLanguage.fill_primStep (Ks.reverse) (eₜ := eₜ) (σ' := σ')
          (e' := e₂) (obs := obs) (σ := σ) (e := e₁)
        exact Hstep' $ EctxLanguage.primStep_of_baseStep Hbase
      | _ =>
        simp [fill, EctxItemLanguage.fillItem, List.reverse_cons, List.foldl_append,
          List.foldl, ECtxItem.fill, List.foldl_reverse, reduceCtorEq, false_and, exists_const,
          imp_self]

instance instContextIfConditional : Language.Context fun x => hl(if ?x then ?e1 else ?e2) where
  toVal_eq_none_fill _ := by simp [toVal]
  primStep_fill {e σ obs e' σ' eₜ} Hstep := by
    obtain ⟨Hbase⟩ := Hstep
    rename_i e₁ e₂ K
    have Hstep' := EctxLanguage.fill_primStep (Expr := Exp) (K ++ [ECtxItem.if e1 e2]) (eₜ := eₜ) (σ' := σ')
      (e' := e₂) (obs := obs) (σ := σ) (e := e₁)
    simp only [EctxItemLanguage.fill_append, EctxItemLanguage.fill_cons, EctxItemLanguage.fillItem,
      ECtxItem.fill, EctxItemLanguage.fill_nil] at Hstep'
    exact Hstep' $ EctxLanguage.primStep_of_baseStep Hbase
  primStep_fill_inv {e σ obs K_e' σ' eₜ} Heq Hstep := by
    revert Hstep
    generalize Heq' : hl(if {e} then {e1} else {e2}) = e_if
    intro Hstep
    obtain ⟨Hbase⟩ := Hstep
    rename_i e₁ e₂ K
    revert Heq'
    rw [show K = K.reverse.reverse by simp]
    cases K.reverse with
    | nil =>
      simp only [fill, List.reverse_nil, List.foldl]
      rintro ⟨⟩
      cases Hbase with
      | ifFalseS => simp [toVal] at Heq
      | ifTrueS => simp [toVal] at Heq
      | _ => simp [ECtxItem.fill]
    | cons Ki Ks =>
      cases Ki with
      | «if» e1 e2 =>
        simp only [List.reverse_cons, EctxItemLanguage.fill_append, EctxItemLanguage.fill_cons,
          EctxItemLanguage.fillItem, ECtxItem.fill, EctxItemLanguage.fill_nil, Exp.if.injEq,
          and_imp]
        rintro ⟨⟩ ⟨⟩ ⟨⟩
        have Hstep' := EctxLanguage.fill_primStep (Expr := Exp) (Ks.reverse) (eₜ := eₜ) (σ' := σ')
          (e' := e₂) (obs := obs) (σ := σ) (e := e₁)
        exact ⟨fill Ks.reverse e₂, by simp, Hstep' $ EctxLanguage.primStep_of_baseStep Hbase⟩
      | _ =>
        simp [fill, EctxItemLanguage.fillItem, List.reverse_cons, List.foldl_append,
          List.foldl, ECtxItem.fill, List.foldl_reverse, reduceCtorEq, false_and, exists_const,
          imp_self]

end Iris.HeapLang
