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

public section wp_expr_simp

@[wp_expr_simp]
theorem subst_anon {v e} : Exp.subst (.anon) v e = e := rfl

@[wp_expr_simp]
theorem subst_ofVal {x v v'} : Exp.subst (.named x) v (Exp.ofVal v') = (Exp.ofVal v') := rfl

@[wp_expr_simp]
theorem subst_var_eq {x v} : Exp.subst (.named x) v (.var x) = (Exp.ofVal v) := by simp [Exp.subst, Exp.substStr]

@[wp_expr_simp]
theorem subst_var_neq {x y v} : x ≠ y → Exp.subst (.named x) v (.var y) = (.var y) := by simp [Exp.subst, Exp.substStr]

@[wp_expr_simp]
theorem subst_rec_eq {x f fx e v} :
  .named x = f ∨ .named x = fx →
  Exp.subst (.named x) v (.rec_ f fx e) = (.rec_ f fx e) :=
  by simp [Exp.subst, Exp.substStr]; grind

@[wp_expr_simp]
theorem subst_rec_neq {x f fx e v} :
  .named x ≠ f →
  .named x ≠ fx →
  Exp.subst (.named x) v (.rec_ f fx e) = (.rec_ f fx $ e.subst (.named x) v) :=
  by simp [Exp.subst, Exp.substStr]; grind

@[wp_expr_simp]
theorem subst_app {x v e₁ e₂} :
  Exp.subst (.named x) v (.app e₁ e₂) = (.app (e₁.subst (.named x) v) (e₂.subst (.named x) v)) :=
  by simp [Exp.subst, Exp.substStr]

@[wp_expr_simp]
theorem subst_case {x v e₁ e₂ e₃} :
  Exp.subst (.named x) v (.case e₁ e₂ e₃) = (.case (e₁.subst (.named x) v) (e₂.subst (.named x) v) (e₃.subst (.named x) v)) :=
  by simp [Exp.subst, Exp.substStr]

@[wp_expr_simp]
theorem subst_unop {x v op e} :
  Exp.subst (.named x) v (.unop op e) = (.unop op (e.subst (.named x) v)) :=
  by simp [Exp.subst, Exp.substStr]

@[wp_expr_simp]
theorem subst_binop {x v op e₁ e₂} :
  Exp.subst (.named x) v (.binop op e₁ e₂) = (.binop op (e₁.subst (.named x) v) (e₂.subst (.named x) v)) :=
  by simp [Exp.subst, Exp.substStr]

@[wp_expr_simp]
theorem subst_if {x v e₀ e₁ e₂} :
  Exp.subst (.named x) v (.if e₀ e₁ e₂) = (.if (e₀.subst (.named x) v) (e₁.subst (.named x) v) (e₂.subst (.named x) v)) :=
  by simp [Exp.subst, Exp.substStr]

@[wp_expr_simp]
theorem subst_pair {x v e₁ e₂} :
  Exp.subst (.named x) v (.pair e₁ e₂) = (.pair (e₁.subst (.named x) v) (e₂.subst (.named x) v)) :=
  by simp [Exp.subst, Exp.substStr]

@[wp_expr_simp]
theorem subst_fst {x v e} :
  Exp.subst (.named x) v (.fst e) = (.fst (e.subst (.named x) v)) :=
  by simp [Exp.subst, Exp.substStr]

@[wp_expr_simp]
theorem subst_snd {x v e} :
  Exp.subst (.named x) v (.snd e) = (.snd (e.subst (.named x) v)) :=
  by simp [Exp.subst, Exp.substStr]

@[wp_expr_simp]
theorem subst_injL {x v e} :
  Exp.subst (.named x) v (.injL e) = (.injL (e.subst (.named x) v)) :=
  by simp [Exp.subst, Exp.substStr]

@[wp_expr_simp]
theorem subst_injR {x v e} :
  Exp.subst (.named x) v (.injR e) = (.injR (e.subst (.named x) v)) :=
  by simp [Exp.subst, Exp.substStr]

@[wp_expr_simp]
theorem subst_allocN {x v e₁ e₂} :
  Exp.subst (.named x) v (.allocN e₁ e₂) = (.allocN (e₁.subst (.named x) v) (e₂.subst (.named x) v)) :=
  by simp [Exp.subst, Exp.substStr]

@[wp_expr_simp]
theorem subst_free {x v e} :
  Exp.subst (.named x) v (.free e) = (.free (e.subst (.named x) v)) :=
  by simp [Exp.subst, Exp.substStr]

@[wp_expr_simp]
theorem subst_load {x v e} :
  Exp.subst (.named x) v (.load e) = (.load (e.subst (.named x) v)) :=
  by simp [Exp.subst, Exp.substStr]

@[wp_expr_simp]
theorem subst_store {x v e₁ e₂} :
  Exp.subst (.named x) v (.store e₁ e₂) = (.store (e₁.subst (.named x) v) (e₂.subst (.named x) v)) :=
  by simp [Exp.subst, Exp.substStr]

@[wp_expr_simp]
theorem subst_cmpXchg {x v e₀ e₁ e₂} :
  Exp.subst (.named x) v (.cmpXchg e₀ e₁ e₂) = (.cmpXchg (e₀.subst (.named x) v) (e₁.subst (.named x) v) (e₂.subst (.named x) v)) :=
  by simp [Exp.subst, Exp.substStr]

@[wp_expr_simp]
theorem subst_xchg {x v e₁ e₂} :
  Exp.subst (.named x) v (.xchg e₁ e₂) = (.xchg (e₁.subst (.named x) v) (e₂.subst (.named x) v)) :=
  by simp [Exp.subst, Exp.substStr]

@[wp_expr_simp]
theorem subst_faa {x v e₁ e₂} :
  Exp.subst (.named x) v (.faa e₁ e₂) = (.faa (e₁.subst (.named x) v) (e₂.subst (.named x) v)) :=
  by simp [Exp.subst, Exp.substStr]

@[wp_expr_simp]
theorem subst_fork {x v e} :
  Exp.subst (.named x) v (.fork e) = (.fork (e.subst (.named x) v)) :=
  by simp [Exp.subst, Exp.substStr]

@[wp_expr_simp]
theorem subst_newProph {x v} :
  Exp.subst (.named x) v .newProph = .newProph :=
  by simp [Exp.subst, Exp.substStr]

@[wp_expr_simp]
theorem subst_resolve {x v e₀ e₁ e₂} :
  Exp.subst (.named x) v (.resolve e₀ e₁ e₂) = (.resolve (e₀.subst (.named x) v) (e₁.subst (.named x) v) (e₂.subst (.named x) v)) :=
  by simp [Exp.subst, Exp.substStr]

simproc [wp_expr_simp] String.reduceEq_copy (( _ : String) = _) := String.reduceEq
simproc [wp_expr_simp] reduceCtorEq_copy (_ = _) := reduceCtorEq
attribute [wp_expr_simp] ne_eq not_false_eq_true Binder.named.injEq _root_.or_true _root_.true_or

end wp_expr_simp


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
      | throwError "The goal {goal} must be an `IProp` at universe level 0"
    let ~q(IProp $GF) := prop
      | throwError "The goal {goal} must be an `IProp`"
    let ~q(UPred.instBIUPred) := bi
      | throwError "Expected the BI implementation of `IProp` to be `UPred.instBIUPred`"

    let ~q(Wp.wp (A := Stuckness) (Expr := Exp) (self := wp.def (ι := $ι)) $s $E $e $Φ) := goal
      | throwError "The goal {goal} must be a WP"
    k mvar {hyps, ι, s, E, e, Φ, hu:=⟨⟩, hprop:=⟨⟩, hbi:=⟨⟩ }

public theorem tac_wp_value [ι : IrisGS_gen hlc Exp GF] {Δ} {s : Stuckness} {E : CoPset} {v : Val} {Φ : Val → IProp GF}
  (H : Δ ⊢ |={E}=> Φ v) :
  (Δ ⊢ WP (v : Exp) @ s ; E {{ Φ }}) :=
  H.trans (wp_value_fupd ⟨rfl⟩).2

public theorem tac_wp_value_nofupd [ι : IrisGS_gen hlc Exp GF] {Δ} {s : Stuckness} {E : CoPset} {v : Val} {Φ : Val → IProp GF}
  (H : Δ ⊢ Φ v) :
  (Δ ⊢ WP (v : Exp) @ s ; E {{ Φ }}) :=
  H.trans <| fupd_intro.trans (wp_value_fupd ⟨rfl⟩).2

public meta def iWpValueHead {u}
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
  (_hwp : $κ =Q wp.def := ⟨⟩) :
    ProofModeM (Option Q($ehyps ⊢ Wp.wp $s $E $e $Φ)) := do
  let ~q(ProgramLogic.ToVal.ofVal $v) := e
    | return none
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
      return some q(tac_wp_value_nofupd (s:=$s) (E:=$E) $pf)

  let pf ← addBIGoal hyps q(iprop(|={$E}=> $goal))
  return some q(tac_wp_value (s:=$s) $pf)

elab "wp_value_head" : tactic =>
  ProofModeM.runTacticWp fun mvar {bi, hyps, ι, s, E, e, Φ, hbi, ..} => do
    have : $bi =Q UPred.instBIUPred := hbi
    let some pf ← iWpValueHead hyps ι q(wp.def) s E e Φ
      | throwTacticEx `wp_value_head mvar s!"{e} is not a value"
    mvar.assign pf

public meta def iWpExprSimp (e : Q(Exp)) :
    ProofModeM ((e' : Q(Exp)) × Q($e = $e')) := do
  let some ext ← getSimpExtension? `wp_expr_simp
    | throwError "Cannot find `wp_expr_simp` attribute"
  let some procext ← Simp.getSimprocExtension? `wp_expr_simp
    | throwError "Cannot find `wp_expr_simp` attribute"

  let theorems ← ext.getTheorems
  let procs ← procext.getSimprocs
  let simpctx := ← Simp.mkContext (simpTheorems := #[theorems])
  let ⟨res, _⟩ ← Meta.simp e simpctx (simprocs:=#[procs])
  return ⟨res.expr, ← res.getProof' e⟩

public theorem tac_wp_expr_simp [ι : IrisGS_gen hlc Exp GF] {Δ} {s : Stuckness} {E : CoPset} {e e' : Exp} {Φ : Val → IProp GF}
  (h : Δ ⊢ WP e' @ s ; E {{ Φ }})
  (heq : e = e') :
  (Δ ⊢ WP e @ s ; E {{ Φ }}) := by simp [*]

elab "wp_expr_simp" : tactic =>
  ProofModeM.runTacticWp fun mvar {hyps, s, E, e, Φ, ..} => do
    let ⟨e', pfeq⟩ ← iWpExprSimp e
    let pf ← addBIGoal hyps q(Wp.wp $s $E $e' $Φ)
    mvar.assign q(tac_wp_expr_simp $pf $pfeq)

public meta def iWpFinish {u}
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
  (_hwp : $κ =Q wp.def := ⟨⟩) :
    ProofModeM (Q($ehyps ⊢ Wp.wp $s $E $e $Φ)) := do
  let ⟨e', pfeq⟩ ← iWpExprSimp e
  let nextPf ← (← iWpValueHead hyps ι q(wp.def) s E e' Φ).getDM
      (addBIGoal hyps q(Wp.wp $s $E $e' $Φ))
  return q(tac_wp_expr_simp $nextPf $pfeq)

elab "wp_finish" : tactic =>
  ProofModeM.runTacticWp fun mvar {hyps, ι, s, E, e, Φ, ..} => do
    let pf ← iWpFinish hyps ι q(wp.def) s E e Φ
    mvar.assign pf

public theorem tac_wp_bind [ι : IrisGS_gen hlc Exp GF] {Δ} {s : Stuckness} {E : CoPset} {K : List ECtxItem} {e' : Exp} {Φ : Val → IProp GF}
  (H : Δ ⊢ WP e' @ s ; E {{ v, WP (ProgramLogic.fill K (Exp.ofVal (Expr:=Exp) v)) @ s; E {{ Φ }} }}) :
    (Δ ⊢ WP (ProgramLogic.fill K e') @ s ; E {{ Φ }}) :=
  H.trans (wp_bind (ProgramLogic.fill K))

elab "wp_bind" colGt ppSpace focus:hl_exp : tactic =>
  ProofModeM.runTacticWp fun mvar {GF, hyps, s, E, e, Φ, ..} => do
    let focus ← elabTermEnsuringTypeQ (←`(hl($focus))) q(HeapLang.Exp)
    trace[wp_bind] s!"Context to bind over: {←ppExpr focus}"

    let some {K, e', ..} ← findECtx e (fun e => do
      trace[wp_bind] s!"trying to unify {←ppExpr e} with {←ppExpr focus}"
      guard <| ← isDefEq e focus)
    -- TODO: add a throwProofModeEx for throwing errors consistently across all tactics
      | throwTacticEx `wp_bind mvar s!"Cannot unify {←ppExpr focus} with any possible evaluation context"
    trace[wp_bind] s!"Found context {←ppExpr K} with expression {←ppExpr e'} matching our focus"

    -- construct the new postcondition
    let Φ' : Q(Val → IProp $GF) ←
      Qq.withLocalDeclDQ `v q(Val) fun v => do
        mkLambdaFVars #[v] <|
          q(Wp.wp $s $E $(← HeapLang.fill K q(.ofVal $v)) $Φ)
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
  ProofModeM.runTacticWp fun mvar {hyps, ι, s, E, e, Φ, ..} => do
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

    let nextPf ← iWpFinish hyps' ι q(wp.def) s E inner Φ

    let HΦ ← iSolveSidecondition q($φ) (failOnUnsolved := false)

    let pf := q(tac_wp_pure $inst $HΦ $pf $nextPf)

    mvar.assign pf

macro "wp_pure" : tactic => `(tactic| wp_pure _)
macro "wp_pures" : tactic => `(tactic| repeat wp_pure)

macro "wp_rec" : tactic => `(tactic | (iapply $(mkIdent `wp_rec):ident; rfl; imodintro; wp_finish))

initialize registerTraceClass `wp_bind
initialize registerTraceClass `wp_pure
