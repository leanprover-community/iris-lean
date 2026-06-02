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

public
theorem wp_value_simp [IrisGS_gen hlc Exp GF]{s : Stuckness} {E : CoPset} {v : Val} {Φ : Val → IProp GF} :
    (WP hl(v(v)) @ s; E {{ Φ }}) = iprop(|={E}=> Φ v) := by
  simp [wp_unfold.to_eq, wp.pre]

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
    dbg_trace s!"Considering ctx {←ppExpr outer_ctx} with focused expression {←ppExpr e'}"
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
  refine .trans ?_ <| ProgramLogic.wp_pure_step_later (GF := GF) Hpstep ‹φ›
  refine .trans (BI.laterN_mono _ H) ?_
  iintro $ !> -; itrivial

meta def _root_.Lean.MVarId.trySolveWith (mvarId : MVarId) (tac : TacticM α) : TacticM α := do
  let savedGoals ← getGoals
  setGoals [mvarId]
  let a ← tac
  setGoals savedGoals
  pure a

elab "wp_pure" focus:term " by " tac:tactic : tactic => do
  let focus ← elabTermEnsuringTypeQ focus q(HeapLang.Exp)
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

    let (ctx, radical) ← HeapLang.extractAllEctxItems e
    trace[wp_pure] s!"Goal context is {←ctx.mapM (liftM ∘ ppExpr)} with radical {←ppExpr radical}"
    for i in focus_ctx.length...=ctx.length do
      let (inner_ctx, outer_ctx) := ctx.splitAt i
      let curr ← HeapLang.fill inner_ctx radical
      trace[wp_pure] s!"Trying to reduce {←ppExpr curr} using {←ppExpr focus}"
      unless ← liftM ∘ withoutModifyingState <| isDefEq curr focus do continue

      let φ ← mkFreshExprMVarQ q(Prop)
      -- let n ← mkFreshExprMVarQ q(Nat)
      -- TODO: Why is `n` not `outParam` in `PureExec`?
      let n := q(1)
      let e₂ ← mkFreshExprMVarQ q(Exp)

      let .some instPureExec ← ProofModeM.trySynthInstanceQ q(ProgramLogic.Language.PureExec $φ $n $curr $e₂)
        | continue
      trace[wp_pure] s!"Wee"
      trace[wp_pure] s!"Found {←ppExpr instPureExec}"
      let Δ' ← mkFreshExprMVarQ q(IProp $GF)
      let .some instIntoLaterN ← ProofModeM.trySynthInstanceQ q(IntoLaterN false $n $(hyps.tm) $Δ')
        | continue
      trace[wp_pure] s!"Found instance {←ppExpr instIntoLaterN}"

      -- TODO: See previous comment on the `ProgramLogic.fill` duplication
      -- let newGoal := q(Wp.wp $s $E (ProgramLogic.fill $(quoteList outer_ctx) $e₂) $Φ)
      let inner ← HeapLang.fill outer_ctx e₂
      let newGoal := q(Wp.wp $s $E $inner $Φ)
      have : (ProgramLogic.fill $(quoteList outer_ctx) $e₂) =Q $inner := ⟨⟩

      trace[wp_pure] s!"Parsing {Δ'}"
      let .some ⟨Δ'₂, hyps'⟩ := parseHyps? bi <| ←instantiateMVars Δ'
        | throwError s!"Obtained hypothesis {←ppExpr Δ'} from `IntroLaterN`, but these couldn't be parsed as {←ppExpr <| ←inferType bi} hypothesis"
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

example : (λ x ↦ x) 0 = 0 := by
  cbv

-- TODO: Rething these syntax declarations
macro "wp_pure" : tactic => `(tactic| wp_pure _ by grind only)
macro "wp_pure" " by " tac:tactic : tactic => `(tactic| wp_pure _ by $tac)
macro "wp_pure" focus:term : tactic => `(tactic| wp_pure $focus by grind only)

initialize registerTraceClass `wp_bind
initialize registerTraceClass `wp_pure
