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
