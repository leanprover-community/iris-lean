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
open Iris.HeapLang Iris.BI

public structure WpGoal where
  u : Level
  prop : Q(Type u)
  bi : Q(BI $prop)
  ehyps : Q($prop)
  hyps : Hyps bi ehyps
  GF : Q(BundledGFunctors.{0, 0, 0})
  hlc : Q(HasLC)
  ι : Q(IrisGS_gen $hlc Exp $GF)
  s : Q(Stuckness)
  E : Q(CoPset)
  e : Q(Exp)
  Φ : Q(Val → IProp $GF)
  hu : QuotedLevelDefEq u 0
  hprop : $prop =Q IProp $GF
  hbi : $bi =Q UPred.instBIUPred


public meta def ProofModeM.runTacticWp {α} (k : MVarId → WpGoal → ProofModeM α)
  : TacticM α := do  ProofModeM.runTactic fun mvar {u, prop, bi, e:=ehyps, hyps, goal, ..} => do
    let .defEq _ ← isLevelDefEqQ u 0
      | throwError "`wp_bind` only works over `IProp` (at universe level 0)"
    let ~q(IProp $GF) := prop
      | throwError "`wp_bind` only works over `IProp`"
    let ~q(UPred.instBIUPred) := bi
      | throwError "`wp_bind` expected the BI implementation of `IProp` to be `UPred.instBIUPred`"

    let ~q(Wp.wp (A := Stuckness) (Expr := Exp) (self := wp.def (ι := $ι)) $s $E $e $Φ) := goal
      | throwError "The goal was not a WP application"
    k mvar { u, prop, bi, ehyps, hyps, GF, ι, hlc:=_, s, E, e, Φ, hu:=⟨⟩, hprop:=⟨⟩, hbi:=⟨⟩ }

public theorem tac_wp_bind [ι : IrisGS_gen hlc Exp GF] {Δ} {s : Stuckness} {E : CoPset} {K : List ECtxItem} {e e' : Exp} {Φ Φ' : Val → IProp GF} :
    (Δ ⊢ WP e' @ s ; E {{ Φ' }}) →
    e = ProgramLogic.fill K e' →
    Φ' = (λ v : Val => WP (ProgramLogic.fill K (Exp.val v)) @ s; E {{ Φ }}) →
    (Δ ⊢ WP e @ s ; E {{ Φ }})
    := by
  rintro H rfl rfl
  iintro _
  iapply wp_bind
  iapply H $$ [$]

elab "wp_bind" focus:hl_exp : tactic => do
  let focus ← elabTermEnsuringTypeQ (←`(hl($focus))) q(HeapLang.Exp)

  trace[bind] s!"Context to bind over: {←ppExpr focus}"
  -- TODO: why is it necessary to mention all the fields we don't need here?
  ProofModeM.runTacticWp fun mvar {GF, hyps, s, E, e, Φ, u:=_, prop:=_, bi:=_, ehyps:=_, hlc:=_, ι:=_, hu :=_, hprop:=_, hbi:=_} => do

    let some ⟨_, K, e'⟩ ← findECtx e (do
      if ← isDefEq · focus then return some () else return none)
      | throwError s!"Couldn't unify {←ppExpr focus} with any possible evaluation context"
    trace[bind] s!"Found ctx {←ppExpr K} with expression {←ppExpr e'} matching our focus"

    -- findECtx guarantees that this holds
    have _ : $e =Q ProgramLogic.fill $K $e' := ⟨⟩
    have he : Q($e = ProgramLogic.fill $K $e') := q(rfl)

    -- construct the new postcondition
    let Φ' : Q(Val → IProp $GF) ←
      Qq.withLocalDeclDQ `v q(Val) fun v => do
        mkLambdaFVars #[v] <|
          q(Wp.wp $s $E $(← HeapLang.fill K q(.val $v)) $Φ)
    have _ : $Φ' =Q (fun v : Val => Wp.wp (PROP := IProp $GF) $s $E (ProgramLogic.fill $K (v : Exp)) $Φ) := ⟨⟩
    -- TODO: check that this proofterm actually works
    have hΦ : Q($Φ' = (fun v : Val => Wp.wp (PROP := IProp $GF) $s $E (ProgramLogic.fill $K (v : Exp)) $Φ)) := q(rfl)

    let newGoal := q(Wp.wp $s $E $e' $Φ')
    let pf ← addBIGoal hyps newGoal
    mvar.assign q(tac_wp_bind $pf $he $hΦ)

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

elab "wp_pure" colGt focus:hl_exp : tactic => do
  let focus ← elabTermEnsuringTypeQ (← `(hl($focus))) q(HeapLang.Exp)
  let (focus_ctx, _) ← HeapLang.extractAllEctxItems focus
  trace[wp_pure] s!"Focusing with {←ppExpr focus} of depth {focus_ctx.length}"
  ProofModeM.runTacticWp fun mvar {GF, bi, hyps, ι, s, E, e, Φ, u:=_, prop:=_, ehyps:=_, hlc:=_, hu :=_, hprop:=_, hbi:=_} => do

    -- NOTE: We use `withoutModifyingState` to ensure successful metavariable assignments are reverted at each iteration.
    -- We didn't have to do this with `wp_bind` because we never backtrack once we found a subexpression defeq with `focus`.
    let some ⟨(φ, n, e₂, inst), outer_ctx, e⟩ ← findECtx e fun e => do
      unless ← (withoutModifyingMCtx <| isDefEq e focus) do
        return none
      let φ ← mkFreshExprMVarQ q(Prop)
      let n ← mkFreshExprMVarQ q(Nat)
      let e₂ ← mkFreshExprMVarQ q(Exp)
      let some inst ← ProofModeM.trySynthInstanceQ q(ProgramLogic.Language.PureExec $φ $n $e $e₂)
        | return none
      return some (φ, n, e₂, inst)
      | throwError "wp_pure: Cannot find expression to evaluate"

    have inst : Q(ProgramLogic.Language.PureExec $φ $n $e $e₂) := inst
    let Δ' ← mkFreshExprMVarQ q(IProp $GF)
    let .some instIntoLaterN ← ProofModeM.trySynthInstanceQ q(IntoLaterN false $n $(hyps.tm) $Δ')
      | throwError "wp_pure: Cannot synthesize IntoLaterN"
    trace[wp_pure] s!"Found `IntoLaterN` instance {←ppExpr instIntoLaterN}"

      -- TODO: See previous comment on the `ProgramLogic.fill` duplication
      -- let newGoal := q(Wp.wp $s $E (ProgramLogic.fill $(quoteList outer_ctx) $e₂) $Φ)
    let inner ← HeapLang.fill outer_ctx e₂
    have : $inner =Q ProgramLogic.fill $outer_ctx $e₂ := ⟨⟩
    let newGoal := q(Wp.wp $s $E $inner $Φ)

    let .some ⟨Δ'₂, hyps'⟩ := parseHyps? bi <| ←instantiateMVars Δ'
      | throwError s!"Obtained hypothesis {←ppExpr Δ'} from `IntroLaterN`, but these couldn't be parsed as {←ppExpr <| ←inferType bi} hypothesis"
      -- We make use of the invariant that `parseHyps? Δ = .some (Δ', hyps) → Δ = Δ'`.
    have : $Δ'₂ =Q $Δ' := ⟨⟩
    let nextPf ← addBIGoal hyps' newGoal

    let HΦ : Q($φ) ← mkFreshExprSyntheticOpaqueMVar q($φ)
    iSolveSideconditionAt HΦ.mvarId! (failOnUnsolved := false)

    let pf := q(tac_wp_pure (ι := $ι) $inst $HΦ $instIntoLaterN $nextPf)

    mvar.assign pf
    return ()

macro "wp_pure" : tactic => `(tactic| wp_pure _)

initialize registerTraceClass `wp_bind
initialize registerTraceClass `wp_pure
