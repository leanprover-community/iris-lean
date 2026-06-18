/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergei Stepanenko, Markus de Medeiros
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

open ProgramLogic ProgramLogic.Language FromMathlib EctxItemLanguage EctxLanguage

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

@[simp]
theorem fillItem_expToVal_none (Ki : ECtxItem) (e : Exp) : toVal (fillItem Ki e) = none := by
  cases Ki <;> rfl

theorem fill_isSome_empty {K : List ECtxItem} {e : Exp}
    (h : (toVal (fill K e)).isSome) : K = [] := by
  cases K with
  | nil => rfl
  | cons Ki K' =>
    rw [fill_cons] at h
    have h2 := EctxLanguage.fill_val (K := K') (e := fillItem Ki e) h
    simp [fillItem_expToVal_none] at h2

macro "solve_subredex_values" : tactic =>
  `(tactic|
    (apply subredexes_are_values
     intro Ki e_inner heq
     cases Ki <;> cases heq <;> try rfl <;> try done))

theorem mk_pure_prim_step {e1 e2 : Exp} (hstep : ∀ σ, BaseStep e1 σ [] e2 σ [])
    (hpure : ∀ {σ1 κs e2' σ2 efs}, BaseStep e1 σ1 κs e2' σ2 efs → κs = [] ∧ σ1 = σ2 ∧ e2 = e2' ∧ efs = [])
    (hsub : SubredexesAreValues e1) : PurePrimStep e1 e2 := by
  refine ⟨fun σ => ?_, fun Hstep => ?_⟩
  · exact ⟨e2, σ, [], BaseStep.ContextStep.intro (K := []) (hstep _)⟩
  · exact hpure (baseStep_of_primStep Hstep hsub)

instance instPureExecIfTrue: PureExec True 1 hl(if #true then &e1 else &e2) e1 where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun hs => ?_) ?_
    · constructor
    · cases hs <;> simp
    · solve_subredex_values

instance instPureExecIfFalse : PureExec True 1 hl(if #false then &e1 else &e2) e2 where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun hs => ?_) ?_
    · constructor
    · cases hs <;> simp
    · solve_subredex_values

instance instPureExecCaseInjl {v e1 e2} :
    PureExec True 1 (Exp.case hl(v(injl(&v))) e1 e2) (.app e1 (.ofVal v)) where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun hs => ?_) ?_
    · constructor
    · cases hs <;> simp
    · solve_subredex_values

instance instPureExecCaseInjr {v e1 e2} :
    PureExec True 1 (Exp.case hl(v(injr(&v))) e1 e2) (.app e2 (.ofVal v)) where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun hs => ?_) ?_
    · constructor
    · cases hs <;> simp
    · solve_subredex_values

instance instPureExecInjl {v : Val} : PureExec True 1 hl(injl(&v)) hl(v(injl(&v)))  where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun hs => ?_) ?_
    · constructor
    · cases hs <;> simp
    · solve_subredex_values

instance instPureExecInjr {v : Val} : PureExec True 1 hl(injr(&v)) hl(v(injr(&v)))  where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun hs => ?_) ?_
    · constructor
    · cases hs <;> simp
    · solve_subredex_values

instance instPureExecBeta {f x : Binder} {e : Exp} {v : Val} :
    PureExec True 1 hl(v(rec &f &x := &e) &v) ((e.subst f (.rec_ f x e)).subst x v) where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun hs => ?_) ?_
    · constructor <;> simp
    · cases hs <;> simp [*]
    · solve_subredex_values

instance instPureExecRec {f x e} :
    PureExec True 1 hl(rec &f &x := &e) hl(v(rec &f &x := &e)) where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun hs => ?_) ?_
    · constructor <;> simp
    · cases hs <;> simp [*]
    · solve_subredex_values

instance instPureExecFst {v1 v2 : Val} : PureExec True 1 hl(fst(v((&v1, &v2)))) v1 where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun hs => ?_) ?_
    · constructor <;> simp
    · cases hs <;> simp [*]
    · solve_subredex_values

instance instPureExecSnd {v1 v2 : Val} : PureExec True 1 hl(snd(v((&v1, &v2)))) v2 where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun hs => ?_) ?_
    · constructor <;> simp
    · cases hs <;> simp [*]
    · solve_subredex_values

instance instPureExecPair {v1 v2 : Val} : PureExec True 1 hl((&v1, &v2)) hl(v((&v1, &v2)))  where
  pureExec _ := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun hs => ?_) ?_
    · constructor <;> simp
    · cases hs <;> simp [*]
    · solve_subredex_values

set_option synthInstance.checkSynthOrder false in
instance instPureExecUnOp {op : UnOp} {v v' : Val} :
    PureExec (op.eval v = some v') 1 (Exp.unop op (.ofVal v)) (.ofVal v') where
  pureExec h := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun hs => ?_) ?_
    · constructor <;> simp [*]
    · cases hs <;> simp_all [UnOp.eval]
    · solve_subredex_values

set_option synthInstance.checkSynthOrder false in
instance instPureExecBinOp {op : BinOp} {v1 v2 v' : Val} :
    PureExec (op.eval v1 v2 = some v') 1
      (Exp.binop op (.ofVal v1) (.ofVal v2)) (.ofVal v') where
  pureExec h := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun hs => ?_) ?_
    · constructor <;> simp [*]
    · cases hs <;> simp_all [BinOp.eval]
    · solve_subredex_values

-- higher priority than the generic binop instance
instance (priority := default + 10) instPureExecEqOp {v1 v2 : Val} :
    PureExec (v1.compareSafe v2) 1
      (Exp.binop .eq (.ofVal v1) (.ofVal v2)) (.ofVal (.lit (.bool (v1 == v2)))) where
  pureExec h := by
    refine .once <| mk_pure_prim_step (fun _ => ?_) (fun hs => ?_) ?_
    · constructor <;> simp [BinOp.eval, *]
    · cases hs <;> simp_all [BinOp.eval]
    · solve_subredex_values

instance instAtomicLoad {s} {v : Val} : Atomic s hl(!&v) where
  atomic {σ obs e' σ' eₜ} Hstep := by
    cases baseStep_of_primStep Hstep (by solve_subredex_values)
    cases s
    · exact val_irreducible rfl _
    · rfl

instance instAtomicStore {s} {v1 v2 : Val} : Atomic s hl(&v1 ← &v2) where
  atomic {σ obs e' σ' eₜ} Hstep := by
    cases baseStep_of_primStep Hstep (by solve_subredex_values)
    rename_i l v Heq
    cases s
    · exact val_irreducible rfl _
    · rfl

instance instAtomicFst {s} {v1 : Val} : Atomic s hl(fst(&v1)) where
  atomic {σ obs e' σ' eₜ} Hstep := by
    cases baseStep_of_primStep Hstep (by solve_subredex_values)
    cases s
    · exact val_irreducible rfl _
    · rfl

instance instAtomicSnd {s} {v1 : Val} : Atomic s hl(snd(&v1)) where
  atomic {σ obs e' σ' eₜ} Hstep := by
    cases baseStep_of_primStep Hstep (by solve_subredex_values)
    cases s
    · exact val_irreducible rfl _
    · rfl

instance instAtomicAllocN {s} {v1 v2 : Val} : Atomic s hl(allocn(&v1, &v2)) where
  atomic {σ obs e' σ' eₜ} Hstep := by
    cases baseStep_of_primStep Hstep (by solve_subredex_values)
    cases s
    · exact val_irreducible rfl _
    · rfl

instance instAtomicFree {s} {v : Val} : Atomic s hl(free(&v)) where
  atomic {σ obs e' σ' eₜ} Hstep := by
    cases baseStep_of_primStep Hstep (by solve_subredex_values)
    cases s
    · exact val_irreducible rfl _
    · rfl

instance instAtomicXchg {s} {v1 v2 : Val} : Atomic s hl(xchg(&v1, &v2)) where
  atomic {σ obs e' σ' eₜ} Hstep := by
    cases baseStep_of_primStep Hstep (by solve_subredex_values)
    cases s
    · exact val_irreducible rfl _
    · rfl

instance instAtomicFaa {s} {v1 v2 : Val} : Atomic s hl(faa(&v1, &v2)) where
  atomic {σ obs e' σ' eₜ} Hstep := by
    cases baseStep_of_primStep Hstep (by solve_subredex_values)
    cases s
    · exact val_irreducible rfl _
    · rfl

instance instAtomicFork {s} {e : Exp} : Atomic s hl(fork(&e)) where
  atomic {σ obs e' σ' eₜ} Hstep := by
    cases baseStep_of_primStep Hstep (by solve_subredex_values)
    cases s
    · exact val_irreducible rfl _
    · rfl

instance instAtomicNewProph {s} : Atomic s (State := State) Exp.newProph where
  atomic {σ obs e' σ' eₜ} Hstep := by
    cases baseStep_of_primStep Hstep (by solve_subredex_values)
    cases s
    · exact val_irreducible rfl _
    · rfl

instance instAtomicCmpXChg {s} {v1 v2 v3 : Val} : Atomic s hl(cmpXchg(&v1, &v2, &v3)) where
  atomic {σ obs e' σ' eₜ} Hstep := by
    cases baseStep_of_primStep Hstep (by solve_subredex_values)
    cases s
    · exact val_irreducible rfl _
    · rfl

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

theorem base_step_to_val_always_to_val
    {e₁ : Exp} {σ₁ₐ : State} {κsₐ : List Observation} {v₂ₐ : Val} {σ₂ₐ : State}
    {efsₐ : List Exp} {σ₁ᵦ : State} {κsᵦ : List Observation}
    {e₂ᵦ : Exp} {σ₂ᵦ : State} {efsᵦ : List Exp}
    (h₁ : BaseStep e₁ σ₁ₐ κsₐ (Exp.val v₂ₐ) σ₂ₐ efsₐ)
    (h₂ : BaseStep e₁ σ₁ᵦ κsᵦ e₂ᵦ σ₂ᵦ efsᵦ) :
    (toVal e₂ᵦ).isSome := by
  cases h₁ <;> cases h₂ <;> simp_all [] <;> grind

theorem prim_step_to_val_always_to_val
    {e₁ : Exp} {σ₁ₐ : State} {κsₐ : List Observation} {v₂ₐ : Val} {σ₂ₐ : State}
    {efsₐ : List Exp} {σ₁ᵦ : State} {κsᵦ : List Observation}
    {e₂ᵦ : Exp} {σ₂ᵦ : State} {efsᵦ : List Exp}
    (h₁ : PrimStep.primStep (e₁, σ₁ₐ) κsₐ (Exp.val v₂ₐ, σ₂ₐ, efsₐ))
    (h₂ : PrimStep.primStep (e₁, σ₁ᵦ) κsᵦ (e₂ᵦ, σ₂ᵦ, efsᵦ)) :
    (toVal e₂ᵦ).isSome := by
  refine base_step_to_val_always_to_val (primStep_val_baseStep h₁) (baseStep_of_primStep h₂ ?_)
  intro K e' heq hnv
  rcases base_ctx_step_val (K := K) (e := e') (heq ▸primStep_val_baseStep h₁) with h | h
  · rw [hnv] at h; simp at h
  · exact h

theorem base_step_to_val_atomic {e₁ : Exp} {σ₁ₐ : State} {κsₐ : List Observation} {v₂ₐ : Val}
    {σ₂ₐ : State} {efsₐ : List Exp} (a : Atomicity) (h : BaseStep e₁ σ₁ₐ κsₐ (Exp.val v₂ₐ) σ₂ₐ efsₐ) :
    Atomic (State := State) a e₁ :=
  stronglyAtomic_atomic ⟨prim_step_to_val_always_to_val (primStep_of_baseStep h)⟩

/- TODO: Coq has a `Hint Extern (Atomic _ _) => by eapply base_step_to_val_atomic`.
   No Lean equivalent — `BaseStep` is not a typeclass, so we can't make this
   a real instance. At use sites, manually apply `base_step_to_val_atomic`. -/

theorem base_step_more_proph_ids {e : Exp} {σ : State} {κs : List Observation}
    {e' : Exp} {σ' : State} {efs : List Exp} (h : BaseStep e σ κs e' σ' efs) :
    σ.usedProphId ⊆ σ'.usedProphId := by
  induction h with
  | newProphS _ p _ => intro x hx; rw [Std.ExtTreeSet.mem_insert]; right; exact hx
  | resolveS _ _ _ _ _ _ _ _ _ _ IH => exact IH
  | cmpXchgS _ _ _ _ _ b _ _ _ => cases b <;> intro _ hx <;> exact hx
  | _ => intro _ hx; exact hx

theorem step_resolve {e : Exp} {vp vt : Val} {σ₁ σ₂ : State} {κ : List Observation} {e₂ : Exp} {efs : List Exp}
    [hatom : Atomic .StronglyAtomic e]
    (hprim : PrimStep.primStep (Exp.resolve e (.val vp) (.val vt), σ₁) κ (e₂, σ₂, efs)) :
    BaseStep (Exp.resolve e (.val vp) (.val vt)) σ₁ κ e₂ σ₂ efs := by
  generalize hsrc : Exp.resolve e (.val vp) (.val vt) = src at hprim
  obtain ⟨Hbase⟩ := hprim
  rename_i e₁' e₂' K
  cases K using List.reverseRec with
  | nil => simp only [fill_nil] at hsrc ⊢; subst hsrc; exact Hbase
  | append_singleton K' Ki ih =>
    clear ih
    exfalso
    cases Ki <;>
      simp only [fillItem, ECtxItem.fill, fill_append, fill_cons, fill_nil,
        Exp.resolve.injEq, reduceCtorEq] at hsrc
    case resolveL K_inner _ _ =>
      suffices hp : PrimStep.primStep (e, σ₁) κ (fillItem K_inner (fill K' e₂'), σ₂, efs) by
        exact absurd (hatom.atomic hp) (by simp [fillItem_expToVal_none])
      rw [hsrc.1]
      exact fill_primStep [K_inner] (fill_primStep K' (primStep_of_baseStep Hbase))
    case resolveM => exact baseStep_fill_eq_val_absurd Hbase hsrc.2.1
    case resolveR => exact baseStep_fill_eq_val_absurd Hbase hsrc.2.2

theorem prim_step_resolve_of_inner {e : Exp} {σ σ_e : State} {κ_e : List Observation}
    {v_e w : Val} {efs_e : List Exp} {p : ProphId} (Hbase_e : BaseStep e σ κ_e (.val v_e) σ_e efs_e)
    (hp_contains : σ.usedProphId.contains p) :
    PrimStep.primStep (Exp.resolve e (.val (.lit (.prophecy p))) (.val w), σ)
        (κ_e ++ [(p, (v_e, w))]) (Exp.val v_e, σ_e, efs_e) :=
  primStep_of_baseStep (BaseStep.resolveS p v_e e σ w σ_e κ_e efs_e Hbase_e hp_contains)

theorem step_resolve_decompose {e : Exp} {p : ProphId} {w : Val} {σ₁ σ₂ : State} {κ : List Observation}
    {e₂ : Exp} {efs : List Exp} [hatom : Atomic .StronglyAtomic e]
    (hstep : PrimStep.primStep (Exp.resolve e (.val (.lit (.prophecy p))) (.val w), σ₁) κ (e₂, σ₂, efs)) :
    ∃ (κ_inner : List Observation) (v_inner : Val),
      κ = κ_inner ++ [(p, (v_inner, w))] ∧
      e₂ = Exp.val v_inner ∧
      BaseStep e σ₁ κ_inner (.val v_inner) σ₂ efs :=
  match step_resolve hstep with
  | .resolveS _ v_n _ _ _ _ κs_n _ hb _ => ⟨κs_n, v_n, rfl, rfl, hb⟩

theorem resolve_reducible {e : Exp} {σ : State} {p : ProphId} {v : Val}
    [hatom : Atomic .StronglyAtomic e] (hred : BaseStep.Reducible (e, σ))
    (hin : σ.usedProphId.contains p) :
    BaseStep.Reducible (Exp.resolve e (.val (.lit (.prophecy p))) (.val v), σ) := by
  obtain ⟨κ, e', σ', efs, hstep⟩ := hred
  obtain ⟨w', rfl⟩ : ∃ w', e' = Exp.val w' := by
    have hval : (toVal e').isSome := hatom.atomic (primStep_of_baseStep hstep)
    cases e' with | val w' => exact ⟨w', rfl⟩ | _ => simp [toVal] at hval
  refine ⟨κ ++ [(p, (w', v))], Exp.val w', σ', efs, ?_⟩
  exact .resolveS p w' e σ v σ' κ efs hstep hin

theorem prim_step_reducible_resolve {e : Exp} {σ : State} {p : ProphId} {w : Val}
    [hatom : Atomic .StronglyAtomic e] (hp_contains : σ.usedProphId.contains p)
    (hred : PrimStep.Reducible (e, σ)) :
    PrimStep.Reducible (Exp.resolve e (.val (.lit (.prophecy p))) (.val w), σ) := by
  obtain ⟨κ, e', σ', efs, hprim⟩ := hred
  obtain ⟨v, rfl⟩ : ∃ v, e' = Exp.val v := by
    match e', (hatom.atomic hprim) with | .val v, _ => exact ⟨v, rfl⟩
  exact primStep_reducible_of_baseStep_reducible
    (resolve_reducible ⟨κ, _, σ', efs, primStep_val_baseStep hprim⟩ hp_contains)

theorem prim_step_more_proph_ids {e : Exp} {σ : State} {κs : List Observation} {e' : Exp}
    {σ' : State} {efs : List Exp} (h : PrimStep.primStep (e, σ) κs (e', σ', efs)) :
    σ.usedProphId ⊆ σ'.usedProphId := by
  obtain ⟨hbase⟩ := h
  exact base_step_more_proph_ids hbase

/-- `resolve e &vp &vt` is atomic whenever its subexpression `e` is strongly
atomic: any step of the whole expression is a `resolveS` base step, which runs
`e` to a value and produces a value. Mirrors `resolve_atomic` in Rocq. -/
instance instAtomicResolve {s} {e : Exp} {vp vt : Val} [hatom : Atomic .StronglyAtomic e] :
    Atomic s (Exp.resolve e (.val vp) (.val vt)) where
  atomic {σ obs e' σ' eₜ} Hstep := by
    cases step_resolve Hstep with
    | resolveS _ v _ _ _ _ _ _ _ _ =>
      cases s
      · exact val_irreducible rfl _
      · rfl

end Iris.HeapLang
