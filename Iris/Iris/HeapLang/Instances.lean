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
      cases h <;> rfl

theorem mk_pure_prim_step {e1 e2 : Exp}
  (hstep : ∀ σ, BaseStep e1 σ [] e2 σ [])
  (hpure : ∀ σ1 κs e2' σ2 efs, BaseStep e1 σ1 κs e2' σ2 efs → κs = [] ∧ σ1 = σ2 ∧ e2 = e2' ∧ efs = [])
  (hsub : EctxLanguage.SubredexesAreValues e1) :
  Language.PurePrimStep e1 e2 := by
    constructor
    · intro σ
      exists e2, σ, []
      refine BaseStep.ContextStep.intro (K := []) (hstep _)
    · intro σ1 σ2 κs e2' efs Hstep
      have h := (EctxLanguage.baseStep_of_primStep Hstep hsub)
      apply hpure; apply h

instance instPureExecIfTrue: Language.PureExec True 1 hl(if #true then &e1 else &e2) e1 where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor
    · cases hs <;> simp
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq
      rfl

instance instPureExecIfFalse : Language.PureExec True 1 hl(if #false then &e1 else &e2) e2 where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor
    · cases hs <;> simp
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq
      rfl

instance instPureExecCaseInjl {v e1 e2} :
    Language.PureExec True 1 (Exp.case hl(v(injl(&v))) e1 e2) (.app e1 (.ofVal v)) where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor
    · cases hs <;> simp
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq
      rfl

instance instPureExecCaseInjr {v e1 e2} :
    Language.PureExec True 1 (Exp.case hl(v(injr(&v))) e1 e2) (.app e2 (.ofVal v)) where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor
    · cases hs <;> simp
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq
      rfl

instance PureExec_injl {v : Val} : Language.PureExec True 1 hl(injl(&v)) hl(v(injl(&v)))  where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor
    · cases hs <;> simp
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq
      rfl

instance PureExec_injr {v : Val} : Language.PureExec True 1 hl(injr(&v)) hl(v(injr(&v)))  where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor
    · cases hs <;> simp
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq
      rfl

instance instPureExecBeta {f x : Binder} {e : Exp} {v : Val} :
    Language.PureExec True 1 hl(v(rec &f &x := &e) &v) ((e.subst f (.rec_ f x e)).subst x v) where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor <;> simp
    · cases hs <;> simp [*]
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq <;> rfl

instance instPureExecRec {f x e} : Language.PureExec True 1 hl(rec &f &x := &e) hl(v(rec &f &x := &e)) where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor <;> simp
    · cases hs <;> simp [*]
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq <;> rfl

instance PureExec_fst {v1 v2 : Val} : Language.PureExec True 1 hl(fst(v((&v1, &v2)))) v1 where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor <;> simp
    · cases hs <;> simp [*]
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq <;> rfl

instance PureExec_snd {v1 v2 : Val} : Language.PureExec True 1 hl(snd(v((&v1, &v2)))) v2 where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor <;> simp
    · cases hs <;> simp [*]
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq <;> rfl

instance PureExec_pair {v1 v2 : Val} : Language.PureExec True 1 hl((&v1, &v2)) hl(v((&v1, &v2)))  where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor <;> simp
    · cases hs <;> simp [*]
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq <;> rfl

set_option synthInstance.checkSynthOrder false in
instance instPureExecUnOp {op : UnOp} {v v' : Val} :
    Language.PureExec (op.eval v = some v') 1 (Exp.unop op (.ofVal v)) (.ofVal v') where
  pureExec h := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor <;> simp [*]
    · cases hs <;> simp_all [UnOp.eval]
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq <;> rfl

set_option synthInstance.checkSynthOrder false in
instance instPureExecBinOp {op : BinOp} {v1 v2 v' : Val} :
    Language.PureExec (op.eval v1 v2 = some v') 1
      (Exp.binop op (.ofVal v1) (.ofVal v2)) (.ofVal v') where
  pureExec h := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor <;> simp [*]
    · cases hs <;> simp_all [BinOp.eval]
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq <;> rfl

-- higher priority than the generic binop instance
instance (priority := default + 10) instPureExecEqOp {v1 v2 : Val} :
    Language.PureExec (v1.compareSafe v2) 1
      (Exp.binop .eq (.ofVal v1) (.ofVal v2)) (.ofVal (.lit (.bool (v1 == v2)))) where
  pureExec h := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor <;> simp [BinOp.eval, *]
    · cases hs <;> simp_all [BinOp.eval]
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq <;> rfl

instance instAtomicLoad {s} {v : Val} : Language.Atomic s hl(!&v) where
  atomic {σ obs e' σ' eₜ} Hstep := by
    have hsr : EctxLanguage.SubredexesAreValues hl(!&v) := by
      apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> try (cases heq; done)
      all_goals (cases heq; rfl)
    cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
    cases s
    · exact Language.val_irreducible rfl _
    · rfl


instance instAtomicStore {s} {v1 v2 : Val} : Language.Atomic s hl(&v1 ← &v2) where
  atomic {σ obs e' σ' eₜ} Hstep := by
    have hsr : EctxLanguage.SubredexesAreValues hl(&v1 ← &v2) := by
      apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> try (cases heq; done)
      all_goals (cases heq; rfl)
    cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
    rename_i l v Heq
    cases s
    · exact Language.val_irreducible rfl _
    · rfl

instance instAtomicSnd {s} {v1 : Val} : Language.Atomic s hl(snd(&v1)) where
  atomic {σ obs e' σ' eₜ} Hstep := by
    have hsr : EctxLanguage.SubredexesAreValues hl(snd(&v1)) := by
      apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> try (cases heq; done)
      · cases heq; rfl
    cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
    cases s
    · exact Language.val_irreducible rfl _
    · rfl

instance instAtomicCmpXChg {s} {v1 v2 v3 : Val} : Language.Atomic s hl(cmpXchg(&v1, &v2, &v3)) where
  atomic {σ obs e' σ' eₜ} Hstep := by
    have hsr : EctxLanguage.SubredexesAreValues hl(cmpXchg(&v1, &v2, &v3)) := by
      apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> try (cases heq; done)
      all_goals (cases heq; rfl)
    cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
    cases s
    · exact Language.val_irreducible rfl _
    · rfl

end Iris.HeapLang
