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

public theorem tac_wp_bind [ι : IrisGS_gen hlc Exp GF] {Δ} {s : Stuckness} {E : CoPset} {K : List ECtxItem} {e' : Exp} {Φ : Val → IProp GF}
  ( H : Δ ⊢ WP e' @ s ; E {{ v, WP (ProgramLogic.fill K (Exp.val v)) @ s; E {{ Φ }} }}) :
    (Δ ⊢ WP (ProgramLogic.fill K e') @ s ; E {{ Φ }}) :=
  H.trans (wp_bind (ProgramLogic.fill K))

elab "wp_bind" colGt ppSpace focus:hl_exp : tactic =>
  ProofModeM.runTacticWp fun mvar {GF, hyps, s, E, e, Φ, ..} => do
    let focus ← elabTermEnsuringTypeQ (←`(hl($focus))) q(HeapLang.Exp)
    trace[bind] s!"Context to bind over: {←ppExpr focus}"

    let some {ctx, e', ..} ← findECtx e (do guard <| ← isDefEq · focus)
      | throwTacticEx `wp_bind mvar s!"Couldn't unify {←ppExpr focus} with any possible evaluation context"
    trace[wp_bind] s!"Found context {←ppExpr ctx} with expression {←ppExpr e'} matching our focus"

    -- construct the new postcondition
    let Φ' : Q(Val → IProp $GF) ←
      Qq.withLocalDeclDQ `v q(Val) fun v => do
        mkLambdaFVars #[v] <|
          q(Wp.wp $s $E $(← HeapLang.fill ctx q(.val $v)) $Φ)
    have _ : $Φ' =Q (fun v : Val => Wp.wp (PROP := IProp $GF) $s $E (ProgramLogic.fill $ctx (v : Exp)) $Φ) := ⟨⟩

    let newGoal := q(Wp.wp $s $E $e' $Φ')
    let pf ← addBIGoal hyps newGoal
    mvar.assign q(tac_wp_bind $pf)

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

elab "wp_pure " colGt ppSpace focus:hl_exp : tactic =>
  ProofModeM.runTacticWp fun mvar {GF, bi, hyps, ι, s, E, e, Φ, ..} => do
    let focus ← elabTermEnsuringTypeQ (← `(hl($focus))) q(HeapLang.Exp)
    trace[wp_pure] m!"Focusing with {focus}"

    let some {result := (φ, n, e₂, inst), ctx := outer_ctx, e' := e₁} ← findECtx e fun e₁ => do
      guard <| ← isDefEq e₁ focus
      let φ ← mkFreshExprMVarQ q(Prop)
      let n ← mkFreshExprMVarQ q(Nat)
      let e₂ ← mkFreshExprMVarQ q(Exp)
      let some inst ← ProofModeM.trySynthInstanceQ q(ProgramLogic.Language.PureExec $φ $n $e₁ $e₂) | failure
      return (φ, n, e₂, inst)
      | throwTacticEx `wp_pure mvar "Cannot find expression to evaluate"
    have inst : Q(ProgramLogic.Language.PureExec $φ $n $e₁ $e₂) := inst

    let Δ' ← mkFreshExprMVarQ q(IProp $GF)
    let .some instIntoLaterN ← ProofModeM.trySynthInstanceQ q(IntoLaterN false $n $(hyps.tm) $Δ')
      | throwTacticEx `wp_pure mvar "Cannot synthesize IntoLaterN"
    trace[wp_pure] s!"Found `IntoLaterN` instance {←ppExpr instIntoLaterN}"

    let ⟨inner, .up _⟩ ← HeapLang.fill' outer_ctx e₂

    let newGoal := q(Wp.wp $s $E $inner $Φ)

    let .some ⟨Δ'₂, hyps'⟩ := parseHyps? bi <| ←instantiateMVars Δ'
      | throwTacticEx `wp_pure mvar m!"Obtained hypothesis {Δ'} from `IntroLaterN`, but these couldn't be parsed as {←inferType bi} hypothesis"
    -- We make use of the invariant that `parseHyps? Δ = .some (Δ', hyps) → Δ = Δ'`.
    have : $Δ'₂ =Q $Δ' := ⟨⟩

    let nextPf ← addBIGoal hyps' newGoal

    let HΦ ← mkSimpleSidecondition q($φ) (failOnUnsolved := false)

    let pf := q(tac_wp_pure (ι := $ι) $inst $HΦ $instIntoLaterN $nextPf)

    mvar.assign pf

macro "wp_pure" : tactic => `(tactic| wp_pure _)

initialize registerTraceClass `wp_bind
initialize registerTraceClass `wp_pure
