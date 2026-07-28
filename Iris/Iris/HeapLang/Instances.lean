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
      have hne_fill : ProgramLogic.ToVal.toVal (K.fill e) = none := by
        cases K <;> rfl
      cases h with
      | resolveStepS _ _ _ _ _ _ _ _ _ inner => exact IH inner
      | resolveFinalS _ _ _ _ _ _ _ _ hne _ _ => exact IH (hne hne_fill)
      | resolveFinalWrongS _ _ _ _ _ _ _ _ inner _ => exact IH inner
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

local macro "solve_subredex_values" : tactic =>
  `(tactic|
    (apply subredexes_are_values
     intro Ki e_inner heq
     cases Ki <;> cases heq <;> try rfl <;> try done))

local macro "solve_atomic" hstep:ident : tactic =>
  `(tactic| (cases baseStep_of_primStep $hstep (by solve_subredex_values)
             split
             · exact val_irreducible rfl _
             · rfl))

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
  atomic {σ obs e' σ' eₜ} Hstep := by solve_atomic Hstep

instance instAtomicStore {s} {v1 v2 : Val} : Atomic s hl(&v1 ← &v2) where
  atomic {σ obs e' σ' eₜ} Hstep := by solve_atomic Hstep

instance instAtomicFst {s} {v1 : Val} : Atomic s hl(fst(&v1)) where
  atomic {σ obs e' σ' eₜ} Hstep := by solve_atomic Hstep

instance instAtomicSnd {s} {v1 : Val} : Atomic s hl(snd(&v1)) where
  atomic {σ obs e' σ' eₜ} Hstep := by solve_atomic Hstep

instance instAtomicAllocN {s} {v1 v2 : Val} : Atomic s hl(allocn(&v1, &v2)) where
  atomic {σ obs e' σ' eₜ} Hstep := by solve_atomic Hstep

instance instAtomicFree {s} {v : Val} : Atomic s hl(free(&v)) where
  atomic {σ obs e' σ' eₜ} Hstep := by solve_atomic Hstep

instance instAtomicXchg {s} {v1 v2 : Val} : Atomic s hl(xchg(&v1, &v2)) where
  atomic {σ obs e' σ' eₜ} Hstep := by solve_atomic Hstep

instance instAtomicFaa {s} {v1 v2 : Val} : Atomic s hl(faa(&v1, &v2)) where
  atomic {σ obs e' σ' eₜ} Hstep := by solve_atomic Hstep

instance instAtomicFork {s} {e : Exp} : Atomic s hl(fork(&e)) where
  atomic {σ obs e' σ' eₜ} Hstep := by solve_atomic Hstep

instance instAtomicNewProph {s} : Atomic s (State := State) Exp.newProph where
  atomic {σ obs e' σ' eₜ} Hstep := by solve_atomic Hstep

instance instAtomicCmpXChg {s} {v1 v2 v3 : Val} : Atomic s hl(cmpXchg(&v1, &v2, &v3)) where
  atomic {σ obs e' σ' eₜ} Hstep := by solve_atomic Hstep

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
    (h_notresolve : ∀ e vp w, e₁ ≠ .resolve e (.val vp) (.val w))
    (h₁ : BaseStep e₁ σ₁ₐ κsₐ (Exp.val v₂ₐ) σ₂ₐ efsₐ)
    (h₂ : BaseStep e₁ σ₁ᵦ κsᵦ e₂ᵦ σ₂ᵦ efsᵦ) :
    (toVal e₂ᵦ).isSome := by
  cases h₁ <;> cases h₂ <;> simp_all <;> grind

theorem prim_step_to_val_always_to_val
    {e₁ : Exp} {σ₁ₐ : State} {κsₐ : List Observation} {v₂ₐ : Val} {σ₂ₐ : State}
    {efsₐ : List Exp} {σ₁ᵦ : State} {κsᵦ : List Observation}
    {e₂ᵦ : Exp} {σ₂ᵦ : State} {efsᵦ : List Exp}
    (h_notresolve : ∀ e vp w, e₁ ≠ .resolve e (.val vp) (.val w))
    (h₁ : PrimStep.primStep (e₁, σ₁ₐ) κsₐ (Exp.val v₂ₐ, σ₂ₐ, efsₐ))
    (h₂ : PrimStep.primStep (e₁, σ₁ᵦ) κsᵦ (e₂ᵦ, σ₂ᵦ, efsᵦ)) :
    (toVal e₂ᵦ).isSome := by
  refine base_step_to_val_always_to_val h_notresolve
    (primStep_val_baseStep h₁) (baseStep_of_primStep h₂ ?_)
  intro K e' heq hnv
  rcases base_ctx_step_val (K := K) (e := e') (heq ▸primStep_val_baseStep h₁) with h | h
  · rw [hnv] at h; simp at h
  · exact h

theorem base_step_to_val_atomic {e₁ : Exp} {σ₁ₐ : State} {κsₐ : List Observation} {v₂ₐ : Val}
    {σ₂ₐ : State} {efsₐ : List Exp} (a : Atomicity)
    (h : BaseStep e₁ σ₁ₐ κsₐ (Exp.val v₂ₐ) σ₂ₐ efsₐ)
    (h_notresolve : ∀ e vp w, e₁ ≠ .resolve e (.val vp) (.val w) := by
      intros _ _ _; intro heq; cases heq) :
    Atomic (State := State) a e₁ :=
  stronglyAtomic_atomic ⟨prim_step_to_val_always_to_val h_notresolve (primStep_of_baseStep h)⟩

/- TODO: Coq has a `Hint Extern (Atomic _ _) => by eapply base_step_to_val_atomic`.
   No Lean equivalent — `BaseStep` is not a typeclass, so we can't make this
   a real instance. At use sites, manually apply `base_step_to_val_atomic`. -/

theorem base_step_more_proph_ids {e : Exp} {σ : State} {κs : List Observation}
    {e' : Exp} {σ' : State} {efs : List Exp} (h : BaseStep e σ κs e' σ' efs) :
    σ.usedProphId ⊆ σ'.usedProphId := by
  induction h with
  | newProphS _ p _ => intro x hx; rw [Std.ExtTreeSet.mem_insert]; right; exact hx
  | resolveStepS _ _ _ _ _ _ _ _ _ _ IH => exact IH
  | resolveFinalS _ _ e _ _ σ' _ _ hne _ _ IH =>
    cases hval : ProgramLogic.ToVal.toVal e with
    | some v' =>
      rename_i H1 _; obtain ⟨_, hσ, _, _⟩ := H1 v' hval; subst hσ
      intro _ hx; exact hx
    | none => exact IH hval
  | resolveFinalWrongS _ _ _ _ _ _ _ _ _ _ IH => exact IH
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
        (κ_e ++ [(p, (v_e, w))]) (Exp.val v_e, σ_e, efs_e) := by
  have hp_mem : p ∈ σ.usedProphId := Std.ExtTreeSet.mem_iff_contains.symm.mpr hp_contains
  have hp_mem_e : p ∈ σ_e.usedProphId := base_step_more_proph_ids Hbase_e p hp_mem
  refine primStep_of_baseStep
    (BaseStep.resolveFinalS p v_e e σ w σ_e κ_e efs_e (fun _ => Hbase_e) ?_ hp_mem_e)
  intro v' hv
  cases e with
  | val v'' => cases Hbase_e
  | _ => simp [ProgramLogic.ToVal.toVal, toVal] at hv

theorem step_resolve_decompose {e : Exp} {p : ProphId} {w : Val} {σ₁ σ₂ : State} {κ : List Observation}
    {e₂ : Exp} {efs : List Exp} [hatom : Atomic .StronglyAtomic e]
    (hne : ProgramLogic.ToVal.toVal e = none)
    (hp : p ∈ σ₁.usedProphId)
    (hstep : PrimStep.primStep (Exp.resolve e (.val (.lit (.prophecy p))) (.val w), σ₁) κ (e₂, σ₂, efs)) :
    ∃ (κ_inner : List Observation) (v_inner : Val),
      κ = κ_inner ++ [(p, (v_inner, w))] ∧
      e₂ = Exp.val v_inner ∧
      BaseStep e σ₁ κ_inner (.val v_inner) σ₂ efs := by
  have Hbase := step_resolve hstep
  cases Hbase with
  | resolveStepS _ e' _ _ _ _ _ _ hne_e' inner =>
    exfalso
    have hv : (toVal e').isSome := hatom.atomic (primStep_of_baseStep inner)
    rw [hne_e'] at hv
    simp at hv
  | resolveFinalS _ v _ _ _ _ κs efs H0 _ _ =>
    exact ⟨κs, v, rfl, rfl, H0 hne⟩
  | resolveFinalWrongS _ _ _ _ _ _ _ _ inner hne_wrong =>
    exfalso
    have hp_mem_e : p ∈ σ₂.usedProphId := base_step_more_proph_ids inner p hp
    exact hne_wrong p rfl hp_mem_e

theorem resolve_reducible {e : Exp} {σ : State} {p : ProphId} {v : Val}
    [hatom : Atomic .StronglyAtomic e] (hred : BaseStep.Reducible (e, σ))
    (hin : σ.usedProphId.contains p) :
    BaseStep.Reducible (Exp.resolve e (.val (.lit (.prophecy p))) (.val v), σ) := by
  obtain ⟨κ, e', σ', efs, hstep⟩ := hred
  obtain ⟨w', rfl⟩ : ∃ w', e' = Exp.val w' := by
    have hval : (toVal e').isSome := hatom.atomic (primStep_of_baseStep hstep)
    cases e' with | val w' => exact ⟨w', rfl⟩ | _ => simp [toVal] at hval
  have hp_mem : p ∈ σ.usedProphId := Std.ExtTreeSet.mem_iff_contains.symm.mpr hin
  have hp_mem' : p ∈ σ'.usedProphId := base_step_more_proph_ids hstep p hp_mem
  refine ⟨κ ++ [(p, (w', v))], Exp.val w', σ', efs, ?_⟩
  refine .resolveFinalS p w' e σ v σ' κ efs (fun _ => hstep) ?_ hp_mem'
  intro v' hv
  cases e with
  | val v'' => cases hstep
  | _ => simp [ProgramLogic.ToVal.toVal, toVal] at hv

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

theorem stuckTerm_baseStep_irreducible {σ : State} :
    BaseStep.Irreducible (stuckTerm, σ) := by
  intro obs e' σ' eₜ hstep
  cases hstep

theorem stuckTerm_subredexes_are_values : SubredexesAreValues stuckTerm := by
  solve_subredex_values

theorem stuckTerm_irreducible {σ : State} : PrimStep.Irreducible (stuckTerm, σ) :=
  primStep_irreducible_of_baseStep_irreducible
    stuckTerm_baseStep_irreducible
    stuckTerm_subredexes_are_values

theorem irreducible_resolve {e : Exp} {vp vt : Val} {σ : State}
    (Hnv : toVal e = none) (H : PrimStep.Irreducible (e, σ)) :
    PrimStep.Irreducible (Exp.resolve e (.val vp) (.val vt), σ) := by
  intro obs e' σ' eₜ ⟨Hbase⟩
  rename_i e₁' e₂' K
  induction K using List.reverseRec with
  | nil =>
    simp only [fill_nil] at Hbase
    cases Hbase with
    | resolveStepS _ _ _ _ _ _ _ _ _ inner =>
      exact H obs _ σ' eₜ (primStep_of_baseStep inner)
    | resolveFinalS _ _ _ _ _ _ _ _ H0 _ _ =>
      exact H _ _ σ' eₜ (primStep_of_baseStep (H0 Hnv))
    | resolveFinalWrongS _ _ _ _ _ _ _ _ inner _ =>
      exact H _ _ σ' eₜ (primStep_of_baseStep inner)
  | append_singleton K' Ki _ =>
    have hnv_fill : toVal (fill K' e₁') = none :=
      EctxLanguage.fill_not_val K' e₁' (EctxLanguage.val_stuck Hbase)
    cases Ki <;>
      simp only [fillItem, ECtxItem.fill, fill_append, fill_cons, fill_nil,
        Exp.resolve.injEq, reduceCtorEq] at * <;>
      first
      | (obtain ⟨heq_e, _, _⟩ := ‹_ = _ ∧ _›
         exact H obs (fill K' e₂') σ' eₜ ⟨.ofBaseStep' K' heq_e rfl Hbase⟩)
      | (obtain ⟨_, heqM, _⟩ := ‹_ = _ ∧ _›
         rw [← heqM] at hnv_fill
         cases hnv_fill)
      | (obtain ⟨_, _, heqR⟩ := ‹_ = _ ∧ _›
         rw [← heqR] at hnv_fill
         cases hnv_fill)

instance instAtomicResolveWeaklyAtomic {e : Exp} {vp vt : Val}
    [hatom : Atomic .WeaklyAtomic e] :
    Atomic .WeaklyAtomic (Exp.resolve e (.val vp) (.val vt)) where
  atomic {σ obs e' σ' eₜ} Hstep := by
    obtain ⟨Hbase⟩ := Hstep
    rename_i e₁' e₂' K
    induction K using List.reverseRec with
    | nil =>
      simp only [fill_nil] at Hbase
      cases Hbase with
      | resolveStepS _ _ _ _ _ _ _ _ hne_e' inner =>
        refine irreducible_resolve hne_e' ?_
        exact hatom.atomic (primStep_of_baseStep inner)
      | resolveFinalS _ v _ _ _ _ _ _ _ _ _ =>
        exact val_irreducible (by simp [toVal]) _
      | resolveFinalWrongS _ _ _ _ _ _ _ _ _ _ =>
        exact stuckTerm_irreducible
    | append_singleton K' Ki _ =>
      have hnv_fill : toVal (fill K' e₁') = none :=
        EctxLanguage.fill_not_val K' e₁' (EctxLanguage.val_stuck Hbase)
      cases Ki <;>
        simp only [fillItem, ECtxItem.fill, fill_append, fill_cons, fill_nil,
          Exp.resolve.injEq, reduceCtorEq] at * <;>
        first
        | (obtain ⟨heq_e, _, _⟩ := ‹_ = _ ∧ _›
           refine irreducible_resolve (EctxLanguage.fill_not_val [_] _ hnv_fill) ?_
           exact hatom.atomic ⟨.ofBaseStep' K' heq_e rfl Hbase⟩)
        | (obtain ⟨_, heqM, _⟩ := ‹_ = _ ∧ _›
           rw [← heqM] at hnv_fill; cases hnv_fill)
        | (obtain ⟨_, _, heqR⟩ := ‹_ = _ ∧ _›
           rw [← heqR] at hnv_fill; cases hnv_fill)

end Iris.HeapLang
