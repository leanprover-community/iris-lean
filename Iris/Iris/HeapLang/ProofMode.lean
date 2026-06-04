/-
Copyright (c) 2026 Fernando Leal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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
  {u : Level}
  {prop : Q(Type u)}
  {bi : Q(BI $prop)}
  {ehyps : Q($prop)}
  hyps : Hyps bi ehyps
  {GF : Q(BundledGFunctors.{0, 0, 0})}
  {hlc : Q(HasLC)}
  ι : Q(IrisGS_gen $hlc Exp $GF)
  s : Q(Stuckness)
  E : Q(CoPset)
  e : Q(Exp)
  Φ : Q(Val → IProp $GF)
  -- TODO: make the tactics work for universes other than 0
  hu : QuotedLevelDefEq u 0
  hprop : $prop =Q IProp $GF
  hbi : $bi =Q UPred.instBIUPred

public meta def ProofModeM.runTacticWp {α} (k : MVarId → WpGoal → ProofModeM α)
  : TacticM α := do
  ProofModeM.runTactic fun mvar {u, prop, bi, hyps, goal, ..} => do
    let .defEq _ ← isLevelDefEqQ u 0
      | throwError "The goal must be an `IProp` at universe level 0"
    let ~q(IProp $GF) := prop
      | throwError "The goal must be an `IProp`"
    let ~q(UPred.instBIUPred) := bi
      | throwError "Expected the BI implementation of `IProp` to be `UPred.instBIUPred`"

    let ~q(Wp.wp (A := Stuckness) (Expr := Exp) (self := wp.def (ι := $ι)) $s $E $e $Φ) := goal
      | throwError "The goal was not a WP application"
    k mvar {hyps, ι, s, E, e, Φ, hu:=⟨⟩, hprop:=⟨⟩, hbi:=⟨⟩ }

public theorem tac_wp_value [ι : IrisGS_gen hlc Exp GF] {Δ} {s : Stuckness} {E : CoPset} {v : Val} {Φ : Val → IProp GF}
  (H : Δ ⊢ |={E}=> Φ v) :
  (Δ ⊢ WP (v : Exp) @ s ; E {{ Φ }}) :=
  H.trans (wp_value_fupd ⟨rfl⟩).2

public theorem tac_wp_value_nofupd [ι : IrisGS_gen hlc Exp GF] {Δ} {s : Stuckness} {E : CoPset} {v : Val} {Φ : Val → IProp GF}
  (H : Δ ⊢ Φ v) :
  (Δ ⊢ WP (v : Exp) @ s ; E {{ Φ }}) :=
  H.trans <| fupd_intro.trans (wp_value_fupd ⟨rfl⟩).2

public meta
def iWpValueHead {u}
  {GF : Q(BundledGFunctors.{0, 0, 0})}
  {hlc : Q(HasLC)}
  {prop : Q(Type u)}
  {bi : Q(BI $prop)}
  {ehyps : Q($prop)}
  (hyps : Hyps bi ehyps)
  (ι : Q(IrisGS_gen $hlc Exp $GF))
  (κ : Q(Wp $prop Exp Val Stuckness))
  (s : Q(Stuckness))
  (E : Q(CoPset))
  (e : Q(Exp))
  (Φ : Q(Val → $prop))

  (_hu : QuotedLevelDefEq u 0 := ⟨⟩)
  (_hprop : $prop =Q IProp $GF := ⟨⟩)
  (_hbi : $bi =Q UPred.instBIUPred := ⟨⟩)
  (_hwp : $κ =Q wp.def := ⟨⟩)

  (throwEx : ∀ {α : Type _}, MessageData → ProofModeM α := Lean.throwError) :
    ProofModeM Q($ehyps ⊢ Wp.wp $s $E $e $Φ) := (do
  let ~q(ProgramLogic.ToVal.ofVal $v) := e
    | throwEx m!"{e} is not a value"
  have goal : Q(IProp $GF) := Expr.headBeta q($Φ $v)
  have : $goal =Q $Φ $v := ⟨⟩

  -- Check if we can eliminate ̄|={E}=> in $Φ.
  -- If yes, we don't need to add ̄|={E}=> to the goal
  let c : Q(Prop) ← mkFreshExprMVarQ q(Prop)
  let p' : Q(Bool) ← mkFreshExprMVarQ q(Bool)
  let A' : Q(IProp $GF) ← mkFreshExprMVarQ q(IProp $GF)
  let Q' : Q(IProp $GF) ← mkFreshExprMVarQ q(IProp $GF)
  if let .some _ ← ProofModeM.trySynthInstanceQ q(ElimModal $c false $p' iprop(|={$E}=> $goal) $A' $goal $Q') then
    if let some _ ← try? <| iSolveSidecondition c then
      let pf ← addBIGoal hyps q($goal)
      return q(tac_wp_value_nofupd (s:=$s) (E:=$E) $pf)

  let pf ← addBIGoal hyps q(iprop(|={$E}=> $goal))
  return q(tac_wp_value (s:=$s) $pf))

elab "wp_value_head" : tactic =>
  ProofModeM.runTacticWp fun mvar {bi, hyps, ι, s, E, e, Φ, hbi, ..} => do
    have : $bi =Q UPred.instBIUPred := hbi
    let pf ← iWpValueHead hyps ι q(wp.def) s E e Φ (throwEx := (throwTacticEx `wp_value_head mvar ·))
    mvar.assign pf

public theorem tac_wp_bind [ι : IrisGS_gen hlc Exp GF] {Δ} {s : Stuckness} {E : CoPset} {K : List ECtxItem} {e' : Exp} {Φ : Val → IProp GF}
  (H : Δ ⊢ WP e' @ s ; E {{ v, WP (ProgramLogic.fill K (Exp.val v)) @ s; E {{ Φ }} }}) :
    (Δ ⊢ WP (ProgramLogic.fill K e') @ s ; E {{ Φ }}) :=
  H.trans (wp_bind (ProgramLogic.fill K))

elab "wp_bind" colGt ppSpace focus:hl_exp : tactic =>
  ProofModeM.runTacticWp fun mvar {GF, hyps, s, E, e, Φ, ..} => do
    let focus ← elabTermEnsuringTypeQ (←`(hl($focus))) q(HeapLang.Exp)
    trace[bind] s!"Context to bind over: {←ppExpr focus}"

    let some {K, e', ..} ← findECtx e (do guard <| ← isDefEq · focus)
    -- TODO: add a throwProofModeEx for throwing errors consistently across all tactics
      | throwTacticEx `wp_bind mvar s!"Cannot unify {←ppExpr focus} with any possible evaluation context"
    trace[wp_bind] s!"Found context {←ppExpr K} with expression {←ppExpr e'} matching our focus"

    -- construct the new postcondition
    let Φ' : Q(Val → IProp $GF) ←
      Qq.withLocalDeclDQ `v q(Val) fun v => do
        mkLambdaFVars #[v] <|
          q(Wp.wp $s $E $(← HeapLang.fill K q(.val $v)) $Φ)
    have _ : $Φ' =Q (fun v : Val => Wp.wp (PROP := IProp $GF) $s $E (ProgramLogic.fill $K (v : Exp)) $Φ) := ⟨⟩

    let pf ← addBIGoal hyps q(Wp.wp $s $E $e' $Φ')
    mvar.assign q(tac_wp_bind $pf)

public theorem tac_wp_pure [ι : IrisGS_gen hlc Exp GF] {Δ Δ'} {s : Stuckness} {E : CoPset} {K : List ECtxItem} {e₁ e₂ : Exp} {φ : Prop} {n : Nat} {Φ : Val → IProp GF} :
    ProgramLogic.Language.PureExec φ n e₁ e₂ →
    φ →
    (Δ ⊢ ▷^[n] Δ') →
    (Δ' ⊢ WP (ProgramLogic.fill K e₂) @ s ; E {{ Φ }}) →
    (Δ ⊢ WP (ProgramLogic.fill K e₁) @ s ; E {{ Φ }})
    := by
  intro Hpstep _ Δ_Δ' H
  refine Δ_Δ'.trans ?_
  replace Hpstep := ProgramLogic.EctxLanguage.pureExec_fill (K := K) φ n Hpstep
  refine .trans ?_ <| ProgramLogic.wp_pure_step_later (GF := GF) ‹φ›
  refine .trans (BI.laterN_mono _ H) ?_
  iintro $ !> -; itrivial

elab "wp_pure " colGt ppSpace focus:hl_exp : tactic =>
  ProofModeM.runTacticWp fun mvar {hyps, s, E, e, Φ, ..} => do
    let focus ← elabTermEnsuringTypeQ (← `(hl($focus))) q(HeapLang.Exp)
    trace[wp_pure] m!"Focusing with {focus}"

    let some {result := (φ, n, e₂, inst), K, e' := e₁} ← findECtx e fun e₁ => do
      guard <| ← isDefEq e₁ focus
      let φ ← mkFreshExprMVarQ q(Prop)
      let n ← mkFreshExprMVarQ q(Nat)
      let e₂ ← mkFreshExprMVarQ q(Exp)
      let some inst ← ProofModeM.trySynthInstanceQ q(ProgramLogic.Language.PureExec $φ $n $e₁ $e₂) | failure
      return (φ, n, e₂, inst)
      | throwTacticEx `wp_pure mvar "Cannot find expression to evaluate"
    have inst : Q(ProgramLogic.Language.PureExec $φ $n $e₁ $e₂) := inst

    let ⟨_, hyps', pf⟩ ← iModAction hyps q(modality_laterN $n)

    let ⟨inner, .up _⟩ ← HeapLang.fillQ K e₂

    let nextPf ← addBIGoal hyps' q(Wp.wp $s $E $inner $Φ)

    let HΦ ← iSolveSidecondition q($φ) (failOnUnsolved := false)

    let pf := q(tac_wp_pure $inst $HΦ $pf $nextPf)

    mvar.assign pf

macro "wp_pure" : tactic => `(tactic| wp_pure _)

initialize registerTraceClass `wp_bind
initialize registerTraceClass `wp_pure
