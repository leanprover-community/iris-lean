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
public import Iris.Std.GenSetsInstances

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
      simp [toVal]

instance instPureExecIfFalse : Language.PureExec True 1 hl(if #false then &e1 else &e2) e2 where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor
    · cases hs <;> simp
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq
      simp [toVal]

instance instPureExecCaseInjl {v e1 e2} :
    Language.PureExec True 1 (Exp.case hl(v(injl(&v))) e1 e2) (.app e1 (.ofVal v)) where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor
    · cases hs <;> simp
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq
      simp [toVal]

instance instPureExecCaseInjr {v e1 e2} :
    Language.PureExec True 1 (Exp.case hl(v(injr(&v))) e1 e2) (.app e2 (.ofVal v)) where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor
    · cases hs <;> simp
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq
      simp [toVal]

instance PureExec_injl {v : Val} : Language.PureExec True 1 hl(injl(&v)) hl(v(injl(&v)))  where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor
    · cases hs <;> simp
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq
      simp [toVal]

instance PureExec_injr {v : Val} : Language.PureExec True 1 hl(injr(&v)) hl(v(injr(&v)))  where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor
    · cases hs <;> simp
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq
      simp [toVal]

instance instPureExecBeta {f x : Binder} {e : Exp} {v : Val} :
    Language.PureExec True 1 hl(v(rec &f &x := &e) &v) ((e.subst f (.rec_ f x e)).subst x v) where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor <;> simp
    · cases hs <;> simp [*]
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq <;> simp [toVal]

instance instPureExecRec {f x e} : Language.PureExec True 1 hl(rec &f &x := &e) hl(v(rec &f &x := &e)) where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor <;> simp
    · cases hs <;> simp [*]
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq <;> simp [toVal]

-- Not an `instance`: the reduct `v'` is not syntactically determined by the
-- redex `Exp.unop op (.val v)` (it depends on `op.eval`), so it cannot provide
-- the (semi-)out-params required of a `PureExec` instance. Applied explicitly.
@[reducible] def PureExec_unop {op : UnOp} {v v' : Val} :
    Language.PureExec (op.eval v = some v') 1 (Exp.unop op (.val v)) (.val v') where
  pureExec hφ := by
    -- TODO: Stamp
    sorry
    -- refine Relation.Iterate.head ?_ (.rfl _)
    -- constructor
    -- · intro σ
    --   exists (.val v'), σ, []
    --   exact BaseStep.ContextStep.intro (K := []) (BaseStep.unOpS op v v' σ hφ)
    -- · intro σ1 σ2 κs e2' efs Hstep
    --   have hsr : EctxLanguage.SubredexesAreValues (Exp.unop op (.val v)) := by
    --     apply EctxItemLanguage.subredexes_are_values
    --     intro Ki e_inner heq
    --     cases Ki <;> try (cases heq; done)
    --     all_goals (cases heq; simp [toVal, expToVal])
    --   cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
    --   rename_i v'' H
    --   obtain rfl : v' = v'' := by rw [hφ] at H; simp_all
    --   exact ⟨rfl, rfl, rfl, rfl⟩

-- Not an `instance` (see `PureExec_unop`): the reduct `v'` is not syntactically
-- determined by the redex, so it cannot provide the `PureExec` out-params.
@[reducible] def PureExec_binop {op : BinOp} {v1 v2 v' : Val} :
    Language.PureExec (op.eval v1 v2 = some v') 1 (Exp.binop op (.val v1) (.val v2)) (.val v') where
  pureExec hφ := by
    -- TODO: Stamp
    sorry
    -- refine Relation.Iterate.head ?_ (.rfl _)
    -- constructor
    -- · intro σ
    --   exists (.val v'), σ, []
    --   exact BaseStep.ContextStep.intro (K := []) (BaseStep.binOpS op v1 v2 v' σ hφ)
    -- · intro σ1 σ2 κs e2' efs Hstep
    --   have hsr : EctxLanguage.SubredexesAreValues (Exp.binop op (.val v1) (.val v2)) := by
    --     apply EctxItemLanguage.subredexes_are_values
    --     intro Ki e_inner heq
    --     cases Ki <;> try (cases heq; done)
    --     all_goals (cases heq; simp [toVal, expToVal])
    --   cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
    --   rename_i v'' H
    --   obtain rfl : v' = v'' := by rw [hφ] at H; simp_all
    --   exact ⟨rfl, rfl, rfl, rfl⟩

instance PureExec_fst {v1 v2 : Val} : Language.PureExec True 1 hl(fst(v((&v1, &v2)))) v1 where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor <;> simp
    · cases hs <;> simp [*]
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq <;> simp [toVal]

instance PureExec_snd {v1 v2 : Val} : Language.PureExec True 1 hl(snd(v((&v1, &v2)))) v2 where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor <;> simp
    · cases hs <;> simp [*]
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq <;> simp [toVal]

instance PureExec_pair {v1 v2 : Val} : Language.PureExec True 1 hl((&v1, &v2)) hl(v((&v1, &v2)))  where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor <;> simp
    · cases hs <;> simp [*]
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq <;> simp [toVal]

instance PureExec_le_int {n1 n2 : Int} : Language.PureExec True 1 hl(#(.int n1) ≤ #(.int n2)) hl(#(.bool (n1 ≤ n2)))  where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun _ _ _ _ _ hs => ?_) ?_
    · constructor <;> simp [BinOp.eval]
    · cases hs <;> simp_all [BinOp.eval]
    · apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> cases heq <;> simp [toVal]

instance instAtomicLoad {s} {v1 : Val} : Language.Atomic s hl(!&v1) where
  atomic {σ obs e' σ' eₜ} Hstep := by
    have hsr : EctxLanguage.SubredexesAreValues hl(!&v1) := by
      apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> try (cases heq; done)
      all_goals (cases heq; simp [toVal])
    cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
    cases s <;> simp [toVal, Language.val_irreducible]

instance instAtomicStore {s} {v1 v2 : Val} : Language.Atomic s hl(&v1 ← &v2) where
  atomic {σ obs e' σ' eₜ} Hstep := by
    have hsr : EctxLanguage.SubredexesAreValues hl(&v1 ← &v2) := by
      apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> try (cases heq; done)
      all_goals (cases heq; simp [toVal])
    cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
    rename_i l v Heq
    cases s <;> simp [toVal, Language.val_irreducible]

instance instAtomicSnd {s} {v1 : Val} : Language.Atomic s hl(snd(&v1)) where
  atomic {σ obs e' σ' eₜ} Hstep := by
    have hsr : EctxLanguage.SubredexesAreValues hl(snd(&v1)) := by
      apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> try (cases heq; done)
      · cases heq; simp [toVal]
    cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
    cases s <;> simp [toVal, Language.val_irreducible]

instance instAtomicCmpXChg {s} {v1 v2 v3 : Val} : Language.Atomic s hl(cmpXchg(&v1, &v2, &v3)) where
  atomic {σ obs e' σ' eₜ} Hstep := by
    have hsr : EctxLanguage.SubredexesAreValues hl(cmpXchg(&v1, &v2, &v3)) := by
      apply EctxItemLanguage.subredexes_are_values
      intro Ki e_inner heq
      cases Ki <;> try (cases heq; done)
      all_goals (cases heq; simp [toVal])
    cases (EctxLanguage.baseStep_of_primStep Hstep hsr)
    cases s <;> simp [toVal, Language.val_irreducible]

instance instContextSnd : Language.Context fun x => hl(snd(&x)) where
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
    generalize Heq' : hl(snd(&e)) = e_snd
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
      | sndS => simp [toVal ] at Heq
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

instance instContextIfConditional : Language.Context fun x => hl(if &x then &e1 else &e2) where
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
    generalize Heq' : hl(if &e then &e1 else &e2) = e_if
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

/-! ### Metatheory about `BaseStep` / `PrimStep` for heap_lang.

Mirrors `case_studies/heaplang/heap_lang_commons.v`. Prophecy lemmas
(`base_step_more_proph_ids`, `prim_step_more_proph_ids`) are intentionally
skipped — see `PORTING_NOTES.md`. -/

open ProgramLogic ProgramLogic.Language FromMathlib

/-- Every heap_lang evaluation-context item produces a non-value. -/
private theorem fillItem_expToVal_none (Ki : ECtxItem) (e : Exp) :
    toVal (EctxItemLanguage.fillItem Ki e) = none := by
  cases Ki <;> rfl

/-- A heap_lang evaluation context whose fill is a value must be empty: only the
empty context can produce a value, since every context item is a non-value. -/
private theorem fill_isSome_empty {K : List ECtxItem} {e : Exp}
    (h : (toVal (EvContext.fill K e)).isSome) : K = [] := by
  cases K with
  | nil => rfl
  | cons Ki K' =>
    rw [EctxItemLanguage.fill_cons] at h
    have h2 : (toVal (EctxItemLanguage.fillItem Ki e)).isSome = true :=
      EctxItemLanguage.fill_val (K := K') (e := EctxItemLanguage.fillItem Ki e) h
    rw [fillItem_expToVal_none] at h2
    simp at h2

/-- A primitive step reaching a value is a base step (the evaluation context is
forced to be empty). -/
@[rocq_alias prim_step_to_val_is_base_step]
theorem primStep_val_baseStep {e : Exp} {σ : State} {obs : List Observation}
    {v : Val} {σ' : State} {efs : List Exp}
    (h : PrimStep.primStep (e, σ) obs (Exp.val v, σ', efs)) :
    BaseStep e σ obs (Exp.val v) σ' efs := by
  generalize hg : (Exp.val v : Exp) = g at h
  obtain ⟨Hbase⟩ := h
  rename_i a b K
  obtain rfl : K = [] := fill_isSome_empty (e := b) (by simp [← hg])
  simp only [EvContext.fill, List.foldl_nil] at hg ⊢
  subst hg
  exact Hbase

/-- `Resolve` weirdness lemma: if one base step reaches a value, every base
step from the same expression reaches a value too. -/
theorem base_step_to_val_always_to_val
    {e₁ : Exp} {σ₁ₐ : State} {κsₐ : List Observation} {v₂ₐ : Val} {σ₂ₐ : State}
    {efsₐ : List Exp} {σ₁ᵦ : State} {κsᵦ : List Observation}
    {e₂ᵦ : Exp} {σ₂ᵦ : State} {efsᵦ : List Exp}
    (h₁ : BaseStep e₁ σ₁ₐ κsₐ (Exp.val v₂ₐ) σ₂ₐ efsₐ)
    (h₂ : BaseStep e₁ σ₁ᵦ κsᵦ e₂ᵦ σ₂ᵦ efsᵦ) :
    (toVal e₂ᵦ).isSome := by
  cases h₁ <;> cases h₂ <;> simp_all [] <;> grind

/-- `Resolve` weirdness lemma lifted to `PrimStep`. -/
theorem prim_step_to_val_always_to_val
    {e₁ : Exp} {σ₁ₐ : State} {κsₐ : List Observation} {v₂ₐ : Val} {σ₂ₐ : State}
    {efsₐ : List Exp} {σ₁ᵦ : State} {κsᵦ : List Observation}
    {e₂ᵦ : Exp} {σ₂ᵦ : State} {efsᵦ : List Exp}
    (h₁ : PrimStep.primStep (e₁, σ₁ₐ) κsₐ (Exp.val v₂ₐ, σ₂ₐ, efsₐ))
    (h₂ : PrimStep.primStep (e₁, σ₁ᵦ) κsᵦ (e₂ᵦ, σ₂ᵦ, efsᵦ)) :
    (toVal e₂ᵦ).isSome := by
  have Hbase₁ := primStep_val_baseStep h₁
  have hsr : EctxLanguage.SubredexesAreValues e₁ := by
    intro K e' heq hnv
    rcases EctxLanguage.base_ctx_step_val (K := K) (e := e') (heq ▸ Hbase₁) with h | h
    · rw [hnv] at h; simp at h
    · exact h
  exact base_step_to_val_always_to_val Hbase₁ (EctxLanguage.baseStep_of_primStep h₂ hsr)

/-- A base step that reaches a value witnesses atomicity of the source. -/
theorem base_step_to_val_atomic
    {e₁ : Exp} {σ₁ₐ : State} {κsₐ : List Observation} {v₂ₐ : Val}
    {σ₂ₐ : State} {efsₐ : List Exp} (a : Atomicity)
    (h : BaseStep e₁ σ₁ₐ κsₐ (Exp.val v₂ₐ) σ₂ₐ efsₐ) :
    Atomic (State := State) a e₁ := by
  apply stronglyAtomic_atomic
  refine ⟨fun hprim => ?_⟩
  exact prim_step_to_val_always_to_val (EctxLanguage.primStep_of_baseStep h) hprim

/- TODO: Coq has a `Hint Extern (Atomic _ _) => by eapply base_step_to_val_atomic`.
   No Lean equivalent — `BaseStep` is not a typeclass, so we can't make this
   a real instance. At use sites, manually apply `base_step_to_val_atomic`. -/

/-- One cannot deallocate prophecy variables: any base step preserves
`usedProphId` modulo extension. Mirrors Rocq's `base_step_more_proph_ids`. -/
@[rocq_alias base_step_more_proph_ids]
theorem base_step_more_proph_ids
    {e : Exp} {σ : State} {κs : List Observation}
    {e' : Exp} {σ' : State} {efs : List Exp}
    (h : BaseStep e σ κs e' σ' efs) :
    σ.usedProphId ⊆ σ'.usedProphId := by
  induction h with
  | newProphS _ p _ => intro x hx; rw [Std.ExtTreeSet.mem_insert]; right; exact hx
  | resolveS _ _ _ _ _ _ _ _ _ _ IH => exact IH
  | cmpXchgS _ _ _ _ _ b _ _ _ => cases b <;> intro _ hx <;> exact hx
  | _ => intro _ hx; exact hx

/-- Any prim-step of `Resolve e (Val vp) (Val vt)` whose inner expression is
strongly atomic is in fact a base step. The eval-context for the prim-step is
forced to be empty: if it ended in a `ResolveL` item, atomicity would force the
context to be empty (contradicting its non-emptiness); the `ResolveM`/`ResolveR`
sub-shapes would force `vp` / `vt` to take a base step from a value, which is
also impossible. Mirrors Rocq's `step_resolve`. -/
@[rocq_alias step_resolve]
theorem step_resolve {e : Exp} {vp vt : Val} {σ₁ σ₂ : State}
    {κ : List Observation} {e₂ : Exp} {efs : List Exp}
    (hatom : Language.Atomic (State := State) (Obs := Observation)
      Language.Atomicity.StronglyAtomic e)
    (hprim : PrimStep.primStep
              (Exp.resolve e (.val vp) (.val vt), σ₁) κ (e₂, σ₂, efs)) :
    BaseStep (Exp.resolve e (.val vp) (.val vt)) σ₁ κ e₂ σ₂ efs := by
  generalize hsrc : Exp.resolve e (.val vp) (.val vt) = src at hprim
  obtain ⟨Hbase⟩ := hprim
  rename_i e₁' e₂' K
  -- hsrc : Exp.resolve e (Val vp) (Val vt) = fill K e₁'
  -- goal : BaseStep (Exp.resolve e (Val vp) (Val vt)) σ₁ κ (fill K e₂') σ₂ efs
  cases K using List.reverseRec with
  | nil =>
    simp only [EctxItemLanguage.fill_nil] at hsrc ⊢
    subst hsrc
    exact Hbase
  | append_singleton K' Ki _ =>
    simp only [EctxItemLanguage.fill_append, EctxItemLanguage.fill_cons,
        EctxItemLanguage.fill_nil] at hsrc ⊢
    -- hsrc : Exp.resolve e (Val vp) (Val vt) = fillItem Ki (fill K' e₁')
    -- goal : BaseStep ... σ₁ κ (fillItem Ki (fill K' e₂')) σ₂ efs
    cases Ki with
    | resolveL K_inner v1 v2 =>
      simp only [EctxItemLanguage.fillItem, ECtxItem.fill, Exp.resolve.injEq] at hsrc
      obtain ⟨h_e_eq, _, _⟩ := hsrc
      -- Build the prim-step `(e, σ₁) → (fillItem K_inner (fill K' e₂'), σ₂, efs)`
      -- by lifting `Hbase` through `K' ++ [K_inner]`. Then atomicity forces the
      -- result to be a value, contradicting `fillItem_expToVal_none`.
      have hprim_e : PrimStep.primStep (e, σ₁) κ
          (EctxItemLanguage.fillItem K_inner (fill K' e₂'), σ₂, efs) := h_e_eq ▸ by
        simpa using EctxLanguage.fill_primStep (K' ++ [K_inner])
          (EctxLanguage.primStep_of_baseStep Hbase)
      have hval : (toVal (EctxItemLanguage.fillItem K_inner (fill K' e₂'))).isSome :=
        hatom.atomic hprim_e
      rw [fillItem_expToVal_none] at hval
      simp at hval
    | resolveM e0 v2 =>
      simp only [EctxItemLanguage.fillItem, ECtxItem.fill, Exp.resolve.injEq] at hsrc
      exact (EctxItemLanguage.baseStep_fill_eq_val_absurd Hbase hsrc.2.1).elim
    | resolveR e0 e1 =>
      simp only [EctxItemLanguage.fillItem, ECtxItem.fill, Exp.resolve.injEq] at hsrc
      exact (EctxItemLanguage.baseStep_fill_eq_val_absurd Hbase hsrc.2.2).elim
    | _ => simp [EctxItemLanguage.fillItem, ECtxItem.fill] at hsrc

/-- Construct a `Resolve` prim-step from an inner base-step ending at a value:
the outer observation list is the inner one with `(p, (v_e, w))` appended. -/
theorem prim_step_resolve_of_inner {e : Exp} {σ σ_e : State} {κ_e : List Observation}
    {v_e w : Val} {efs_e : List Exp} {p : ProphId}
    (Hbase_e : BaseStep e σ κ_e (.val v_e) σ_e efs_e)
    (hp_contains : σ.usedProphId.contains p) :
    PrimStep.primStep (Exp.resolve e (.val (.lit (.prophecy p))) (.val w), σ)
        (κ_e ++ [(p, (v_e, w))]) (Exp.val v_e, σ_e, efs_e) :=
  EctxLanguage.primStep_of_baseStep
    (BaseStep.resolveS p v_e e σ w σ_e κ_e efs_e Hbase_e hp_contains)

/-- Inversion lemma for `Resolve` prim-steps: any prim-step of
`Resolve e (Val (LitProphecy p)) (Val w)` with `e` atomic decomposes into an
inner base-step of `e` to a value, with the trailing observation
`(p, (v_inner, w))` tacked onto the inner observation list. Packages the
constructor-level destructuring that `cases` on `step_resolve` would expose. -/
theorem step_resolve_decompose {e : Exp} {p : ProphId} {w : Val}
    {σ₁ σ₂ : State} {κ : List Observation} {e₂ : Exp} {efs : List Exp}
    (hatom : Language.Atomic (State := State) (Obs := Observation)
      Language.Atomicity.StronglyAtomic e)
    (hstep : PrimStep.primStep
        (Exp.resolve e (.val (.lit (.prophecy p))) (.val w), σ₁) κ (e₂, σ₂, efs)) :
    ∃ (κ_inner : List Observation) (v_inner : Val),
      κ = κ_inner ++ [(p, (v_inner, w))] ∧
      e₂ = Exp.val v_inner ∧
      BaseStep e σ₁ κ_inner (.val v_inner) σ₂ efs := by
  cases step_resolve hatom hstep with
  | resolveS _ v_n _ _ _ _ κs_n _ hb _ => exact ⟨κs_n, v_n, rfl, rfl, hb⟩

/-- An atomic, reducible `e` whose prophecy id `p` is live can be wrapped in
`Resolve _ (proph p) v` while remaining reducible: tack a fresh observation
`(p, (v_e, v))` onto the inner step's observation list. Mirrors Rocq's
`resolve_reducible`. -/
@[rocq_alias resolve_reducible]
theorem resolve_reducible
    {e : Exp} {σ : State} {p : ProphId} {v : Val}
    (hatom : Language.Atomic (State := State) (Obs := Observation)
      Language.Atomicity.StronglyAtomic e)
    (hred : BaseStep.Reducible (e, σ))
    (hin : σ.usedProphId.contains p) :
    BaseStep.Reducible
      (Exp.resolve e (.val (.lit (.prophecy p))) (.val v), σ) := by
  obtain ⟨κ, e', σ', efs, hstep⟩ := hred
  have hprim : PrimStep.primStep (e, σ) κ (e', σ', efs) :=
    EctxLanguage.primStep_of_baseStep hstep
  have hval : (toVal e').isSome := hatom.atomic hprim
  obtain ⟨w', rfl⟩ : ∃ w', e' = Exp.val w' := by
    cases e' with
    | val w' => exact ⟨w', rfl⟩
    | _ => simp [toVal] at hval
  refine ⟨κ ++ [(p, (w', v))], Exp.val w', σ', efs, ?_⟩
  exact BaseStep.resolveS p w' e σ v σ' κ efs hstep hin

/-- `Resolve`-lifted version of `resolve_reducible` for prim-step reducibility:
if `e` is strongly atomic, prim-step reducible, and `p ∈ σ.usedProphId`, then
`Resolve e (proph p) v` is prim-step reducible. -/
theorem prim_step_reducible_resolve {e : Exp} {σ : State} {p : ProphId} {w : Val}
    (hatom : Language.Atomic (State := State) (Obs := Observation)
      Language.Atomicity.StronglyAtomic e)
    (hp_contains : σ.usedProphId.contains p)
    (hred : PrimStep.Reducible (e, σ)) :
    PrimStep.Reducible
      (Exp.resolve e (.val (.lit (.prophecy p))) (.val w), σ) := by
  obtain ⟨κ, e', σ', efs, hprim⟩ := hred
  have hval : (toVal e').isSome := hatom.atomic hprim
  obtain ⟨v, rfl⟩ : ∃ v, e' = Exp.val v := by
    match e', hval with | .val v, _ => exact ⟨v, rfl⟩
  exact EctxLanguage.primStep_reducible_of_baseStep_reducible
    (resolve_reducible hatom ⟨κ, _, σ', efs, primStep_val_baseStep hprim⟩ hp_contains)

/-- Lifted to `PrimStep`. Mirrors Rocq's `prim_step_more_proph_ids`. -/
@[rocq_alias prim_step_more_proph_ids]
theorem prim_step_more_proph_ids
    {e : Exp} {σ : State} {κs : List Observation}
    {e' : Exp} {σ' : State} {efs : List Exp}
    (h : PrimStep.primStep (e, σ) κs (e', σ', efs)) :
    σ.usedProphId ⊆ σ'.usedProphId := by
  obtain ⟨hbase⟩ := h
  exact base_step_more_proph_ids hbase

end Iris.HeapLang
