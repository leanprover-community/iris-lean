module

public import Iris.ProofMode
public import Iris.HeapLang.Tactic
public import Iris.HeapLang.Instances
public import Iris.ProgramLogic.WeakestPre
public import Iris.ProgramLogic.Language
public import Iris.ProgramLogic.EctxLanguage
public import Iris.ProgramLogic.EctxiLanguage
public import Iris.ProgramLogic.Lifting
public import Lean
public import Lean.Elab.Tactic.Simp
public import Qq

namespace Iris.ProofMode

open Lean hiding Expr
open Meta Elab Tactic Qq
open Iris.HeapLang

elab "wp_bind" focus:hl_exp : tactic => do
  -- TODO: Do we ask for a function or for a "pattern"?
  let focus ← elabTermEnsuringTypeQ (←`(hl($focus))) q(HeapLang.Exp)
  trace[bind] s!"Context to bind over: {←ppExpr focus}"
  ProofModeM.runTactic fun mvar {u, prop, bi, hyps, goal, ..} => do
    let .defEq _ ← isLevelDefEqQ u 0
      | throwError "`wp_bind` only works over `IProp` (at universe level 0)"
    let ~q(IProp $GF) := prop
      | throwError "`wp_bind` only works over `IProp`"
    let ~q(UPred.instBIUPred) := bi
      | throwError "`wp_bind` expected the BI implementation of `IProp` to be `UPred.instBIUPred`"

    let ~q(Wp.wp (A := Stuckness) (Expr := Exp) (Val := Val)
      (self := wp.def (Λ := @ProgramLogic.EctxLanguage.instLanguage _ _ _ _ _ (ProgramLogic.EctxItemLanguage.instEctxLanguage (EctxItem := ECtxItem) (Λ := $Λ))) (ι := $ι))
      $s $E $e $Φ) := goal
      | throwError "The goal was not a WP application"

    let (outer_ctx, e') :: _ ← (←extractAllOuterEvCtx e).filterM (isDefEq ·.2 focus)
      | throwError s!"Couldn't unify {←ppExpr focus} with any possible evaluation context"
    trace[bind] s!"Found ctx {←ppExpr outer_ctx} with expression {←ppExpr e'} matching our focus"
    /- We assume that `extractAllOuterEvCtx` gives the following invariant -/
    have : ProgramLogic.fill $outer_ctx $e' =Q $e := ⟨⟩

    let evctxInst : Q(ProgramLogic.Language.Context (ProgramLogic.fill (Expr := Exp) $outer_ctx)) := q(ProgramLogic.EctxLanguage.instContextFill ..)
    trace[wp_bind] s!"Evaluation context instance: {←ppExpr evctxInst}"

    let pf := q(wp_bind (GF := $GF) (ProgramLogic.fill _) (κ := $evctxInst) (s := $s) (E := $E) (e := $focus) (Φ := $Φ))

    -- NOTE: Option 1: We perform the simplification ourselves
    let innerPostcond : Q(Val → IProp $GF) ← Qq.withLocalDeclDQ `v q(Val) fun v => do
      mkLambdaFVars #[v] <| q(Wp.wp (PROP := IProp $GF) $s $E $(←HeapLang.fill outer_ctx q(($v : Exp))) $Φ)
    have : $innerPostcond =Q (fun v : Val => Wp.wp (PROP := IProp $GF) $s $E (ProgramLogic.fill $outer_ctx (v : Exp)) $Φ) := ⟨⟩

    -- NOTE: Option 2: We call `cbv` or `simp` to perform the simplification
    -- let innerPostcond := q(fun v : Val => Wp.wp (PROP := IProp $GF) $s $E (ProgramLogic.fill $outer_ctx (v : Exp)) $Φ)

    let newGoal := q(Wp.wp (PROP := IProp $GF) $s $E $focus $innerPostcond)

    let newProof ← addBIGoal hyps newGoal
    -- do
    --   let savedGoals ← Tactic.getGoals
    --   Tactic.setGoals [newProof.mvarId!]
    --   newProof.mvarId!.withContext do
    --     -- TODO: Pretty this up.
    --     evalTactic <| ← `(tactic| try simp only [
    --         -- wp_value_simp,
    --         -- wp_value_iff,
    --         -- ←fupd_wp_iff.to_eq,
    --         -- fupd_idem.to_eq,
    --         -- Iris.ProgramLogic.EctxItemLanguage.fill_cons,
    --         -- Iris.ProgramLogic.EctxItemLanguage.fill_nil,
    --         -- Iris.ProgramLogic.EctxItemLanguage.fillItem,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_1,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_2,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_3,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_4,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_5,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_6,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_7,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_8,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_9,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_10,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_11,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_12,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_13,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_14,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_15,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_16,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_17,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_18,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_19,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_20,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_21,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_22,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_23,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_24,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_25,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_26,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_27,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_28,
    --         -- Iris.HeapLang.ECtxItem.fill.eq_29
    --         ])
    --   let newGoals ← Tactic.getGoals
    --   Tactic.setGoals (savedGoals ++ newGoals)

    mvar.assign q($(newProof).trans $pf)

public theorem tac_wp_pure [ι : IrisGS_gen hlc Exp GF] {Δ Δ'} {s : Stuckness} {E : CoPset} {K : List ECtxItem} {e₁ e₂ : Exp} {φ : Prop} {n : Nat} {Φ : Val → IProp GF} :
    ProgramLogic.Language.PureExec φ n e₁ e₂ →
    φ →
    IntoLaterN false n Δ Δ' →
    (Δ' ⊢ WP (ProgramLogic.fill K e₂) @ s ; E {{ Φ }}) →
    (Δ ⊢ WP (ProgramLogic.fill K e₁) @ s ; E {{ Φ }})
    := by
  intro Hpstep _ ⟨Δ_Δ'⟩ H
  refine Δ_Δ'.trans ?_
  replace Hpstep := ProgramLogic.EctxLanguage.pureExec_fill (K := K) φ n Hpstep
  refine .trans ?_ <| ProgramLogic.wp_pure_step_later (GF := GF) ‹φ›
  refine .trans (BI.laterN_mono _ H) ?_
  iintro $ !> -; itrivial

-- NOTE: Potential postprocessing lemma for `wp_pure` (could be called in a `simp` only on the resulting goal)
public
theorem wp_value_simp [IrisGS_gen hlc Exp GF]{s : Stuckness} {E : CoPset} {v : Val} {Φ : Val → IProp GF} :
    (WP hl(v(v)) @ s; E {{ Φ }}) = iprop(|={E}=> Φ v) := by
  simp [wp_unfold.to_eq, wp.pre]

-- NOTE: Potential postprocessing lemma for `wp_pure` (could be called in a `simp` only on the resulting goal)
public
theorem fupd_full_fupd [IrisGS_gen hlc Exp GF]{P : IProp GF} :
    iprop(|={⊤}=> |={E}=> P) = iprop(|={⊤}=> P) := by
  ext; constructor
  · iintro >H
    ihave >aux := BIFUpdate.subset (E1 := ⊤) (E2 := E) (by simp [Std.top, Subset, Membership.mem, CoPset.full])
    imod H
    imod aux with -
    iassumption
  · apply fupd_elim;
    refine fupd_intro.trans fupd_intro

meta def _root_.Lean.MVarId.trySolveWith (mvarId : MVarId) (tac : TacticM α) : TacticM α := do
  let savedGoals ← getGoals
  setGoals [mvarId]
  let a ← tac
  setGoals savedGoals
  pure a

elab "wp_pure" focus:hl_exp " by " tac:tactic : tactic => do
  let focus ← elabTermEnsuringTypeQ (← `(hl($focus))) q(HeapLang.Exp)
  let (focus_ctx, _) ← HeapLang.extractAllEctxItems focus
  trace[wp_pure] s!"Focusing with {←ppExpr focus} of depth {focus_ctx.length}"
  ProofModeM.runTactic fun mvar {u, prop, bi, hyps, goal, ..} => do
    let .defEq _ ← isLevelDefEqQ u 0
      | throwError "`wp_bind` only works over `IProp` (at universe level 0)"
    let ~q(IProp $GF) := prop
      | throwError "`wp_bind` only works over `IProp`"
    let ~q(UPred.instBIUPred) := bi
      | throwError "`wp_bind` expected the BI implementation of `IProp` to be `UPred.instBIUPred`"

    let ~q(Wp.wp (A := Stuckness) (Expr := Exp) (Val := Val)
            (self := wp.def
              (Λ := @ProgramLogic.EctxLanguage.instLanguage _ _ (HeapLang.State) (HeapLang.Observation) _
                (ProgramLogic.EctxItemLanguage.instEctxLanguage (EctxItem := ECtxItem) (Λ := instEctxItemLanguageExp)))
              (ι := $ι))
            $s $E $e $Φ) := goal
      | throwError "The goal was not a WP application"

    -- NOTE: We use `withoutModifyingState` to ensure successful metavariable assignments are reverted at each iteration.
    -- We didn't have to do this with `wp_bind` because we never backtrack once we found a subexpression defeq with `focus`.
    for (outer_ctx, curr) in ← (← extractAllOuterEvCtx e).filterM (liftM ∘ withoutModifyingState <| isDefEq ·.2 focus) do
      let φ ← mkFreshExprMVarQ q(Prop)
      let n ← mkFreshExprMVarQ q(Nat)
      let e₂ ← mkFreshExprMVarQ q(Exp)
      let .some instPureExec ← ProofModeM.trySynthInstanceQ q(ProgramLogic.Language.PureExec $φ $n $curr $e₂)
        | continue
      trace[wp_pure] s!"Found `PureExec` rule to apply: {←ppExpr instPureExec}"

      let Δ' ← mkFreshExprMVarQ q(IProp $GF)
      let .some instIntoLaterN ← ProofModeM.trySynthInstanceQ q(IntoLaterN false $n $(hyps.tm) $Δ')
        | continue
      trace[wp_pure] s!"Found `IntoLaterN` instance {←ppExpr instIntoLaterN}"

      -- TODO: See previous comment on the `ProgramLogic.fill` duplication
      -- let newGoal := q(Wp.wp $s $E (ProgramLogic.fill $(quoteList outer_ctx) $e₂) $Φ)
      let inner ← HeapLang.fill outer_ctx e₂
      have : $inner =Q ProgramLogic.fill $outer_ctx $e₂ := ⟨⟩

      let newGoal := q(Wp.wp $s $E $inner $Φ)
      -- do
      --   let savedGoals ← Tactic.getGoals
      --   Tactic.setGoals [newProof.mvarId!]
      --   newProof.mvarId!.withContext do
      --     -- TODO: Pretty this up.
      --     evalTactic <| ← `(tactic| try simp only [
      --         -- wp_value_simp,
      --         -- wp_value_iff,
      --         -- ←fupd_wp_iff.to_eq,
      --         -- fupd_idem.to_eq,
      --         -- Iris.ProgramLogic.EctxItemLanguage.fill_cons,
      --         -- Iris.ProgramLogic.EctxItemLanguage.fill_nil,
      --         -- Iris.ProgramLogic.EctxItemLanguage.fillItem,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_1,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_2,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_3,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_4,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_5,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_6,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_7,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_8,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_9,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_10,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_11,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_12,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_13,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_14,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_15,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_16,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_17,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_18,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_19,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_20,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_21,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_22,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_23,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_24,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_25,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_26,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_27,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_28,
      --         -- Iris.HeapLang.ECtxItem.fill.eq_29,
      --         -- fupd_full_fupd
      --         ])
      --   let newGoals ← Tactic.getGoals
      --   Tactic.setGoals (savedGoals ++ newGoals)

      let .some ⟨Δ'₂, hyps'⟩ := parseHyps? bi <| ←instantiateMVars Δ'
        | throwError s!"Obtained hypothesis {←ppExpr Δ'} from `IntroLaterN`, but these couldn't be parsed as {←ppExpr <| ←inferType bi} hypothesis"
      -- We make use of the invariant that `parseHyps? Δ = .some (Δ', hyps) → Δ = Δ'`.
      have : $Δ'₂ =Q $Δ' := ⟨⟩
      let nextPf ← addBIGoal hyps' newGoal

      let HΦ : Q($φ) ← (liftM ∘ mkFreshExprSyntheticOpaqueMVar) q($φ)
      addMVarGoal HΦ.mvarId!
      HΦ.mvarId!.trySolveWith do
        evalTactic tac

      let pf := q(tac_wp_pure (ι := $ι) $instPureExec $HΦ $instIntoLaterN $nextPf)

      mvar.assign pf
      return ()
    throwError "Found no `PureExec` rule to apply in the expression {←ppExpr e}"

-- TODO: Rething these syntax declarations
macro "wp_pure" : tactic => `(tactic| wp_pure _ by grind only)
macro "wp_pure" " by " tac:tactic : tactic => `(tactic| wp_pure _ by $tac)
macro "wp_pure" focus:hl_exp : tactic => `(tactic| wp_pure $focus by grind only)

initialize registerTraceClass `wp_bind
initialize registerTraceClass `wp_pure
