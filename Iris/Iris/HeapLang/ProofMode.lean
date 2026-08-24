/-
Copyright (c) 2026 Fernando Leal, Klaus Kraßnitzer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Leal, Klaus Kraßnitzer
-/
module

public import Iris.ProofMode
public import Iris.HeapLang.Tactic
public import Iris.HeapLang.Instances
public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.DerivedLaws
public import Iris.ProgramLogic.WeakestPre
public import Iris.ProgramLogic.Language
public import Iris.ProgramLogic.EctxLanguage
public import Iris.ProgramLogic.EctxiLanguage
public import Iris.ProgramLogic.Lifting
public import Lean.Elab.Tactic.Simp

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

public meta def ProofModeM.runTacticWp {α} (tacName : Name) (k : MVarId → WpGoal → ProofModeM α)
  : TacticM α := do
  ProofModeM.runTactic tacName fun mvar {u, prop, bi, hyps, goal, ..} => do
    let .defEq _ ← isLevelDefEqQ u 0
      | throwIPMError "The goal {goal} must be an `IProp` at universe level 0"
    let ~q(IProp $GF) := prop
      | throwIPMError "The goal {goal} must be an `IProp`"
    let ~q(UPred.instBIUPred) := bi
      | throwIPMError "Expected the BI implementation of `IProp` to be `UPred.instBIUPred`"

    let ~q(Wp.wp (A := Stuckness) (Expr := Exp) (self := wp.def (ι := $ι)) $s $E $e $Φ) := goal
      | throwIPMError "The goal {goal} must be a WP"
    k mvar {hyps, ι, s, E, e, Φ, hu:=⟨⟩, hprop:=⟨⟩, hbi:=⟨⟩ }

@[rocq_alias heap_lang.tac_wp_value]
public theorem tac_wp_value [ι : IrisGS_gen hlc Exp GF] {Δ} {s : Stuckness} {E : CoPset} {v : Val} {Φ : Val → IProp GF}
  (H : Δ ⊢ |={E}=> Φ v) :
  (Δ ⊢ WP (v : Exp) @ s ; E {{ Φ }}) :=
  H.trans (wp_value_fupd ⟨rfl⟩).2

@[rocq_alias heap_lang.tac_wp_value_nofupd]
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
  (s : Q(Stuckness))
  (E : Q(CoPset))
  (e : Q(Exp))
  (Φ : Q(Val → $prop))

  (_hu : QuotedLevelDefEq u 0 := ⟨⟩)
  (_hprop : $prop =Q IProp $GF := ⟨⟩)
  (_hbi : $bi =Q UPred.instBIUPred := ⟨⟩)
  (κ : Q(Wp $prop Exp Val Stuckness) := q(wp.def))
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
  if let .some _ ← ProofModeM.trySynthInstanceQ q(ElimModal $c false .out $p' iprop(|={$E}=> $goal) $A' $goal $Q') then
    if let some _ ← try? <| iSolveSidecondition c then
      let pf ← addBIGoal hyps q($goal)
      return some q(tac_wp_value_nofupd (s:=$s) (E:=$E) $pf)

  let pf ← addBIGoal hyps q(iprop(|={$E}=> $goal))
  return some q(tac_wp_value (s:=$s) $pf)

elab "wp_value_head" : tactic =>
  ProofModeM.runTacticWp `wp_value_head fun mvar {bi, hyps, ι, s, E, e, Φ, hbi, ..} => do
    have : $bi =Q UPred.instBIUPred := hbi
    let some pf ← iWpValueHead hyps ι s E e Φ
      | throwIPMError s!"{e} is not a value"
    mvar.assign pf

public meta def iWpExprSimp (e : Q(Exp)) :
    ProofModeM ((e' : Q(Exp)) × Q($e = $e')) := do
  let some ext ← getSimpExtension? `wp_expr_simp
    | throwIPMError "Cannot find `wp_expr_simp` attribute"
  let some procext ← Simp.getSimprocExtension? `wp_expr_simp
    | throwIPMError "Cannot find `wp_expr_simp` attribute"

  let theorems ← ext.getTheorems
  let procs ← procext.getSimprocs
  let simpctx := ← Simp.mkContext (simpTheorems := #[theorems])
  let ⟨res, _⟩ ← Meta.simp e simpctx (simprocs:=#[procs])
  return ⟨res.expr, ← res.getProof' e⟩

@[rocq_alias heap_lang.tac_wp_expr_eval]
public theorem tac_wp_expr_simp [ι : IrisGS_gen hlc Exp GF] {Δ} {s : Stuckness} {E : CoPset} {e e' : Exp} {Φ : Val → IProp GF}
  (h : Δ ⊢ WP e' @ s ; E {{ Φ }})
  (heq : e = e') :
  (Δ ⊢ WP e @ s ; E {{ Φ }}) := by simp [*]

elab "wp_expr_simp" : tactic =>
  ProofModeM.runTacticWp `wp_expr_simp fun mvar {hyps, s, E, e, Φ, ..} => do
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
  (s : Q(Stuckness))
  (E : Q(CoPset))
  (e : Q(Exp))
  (Φ : Q(Val → $prop))

  (_hu : QuotedLevelDefEq u 0 := ⟨⟩)
  (_hprop : $prop =Q IProp $GF := ⟨⟩)
  (_hbi : $bi =Q UPred.instBIUPred := ⟨⟩)
  (κ : Q(Wp $prop Exp Val Stuckness) := q(wp.def))
  (_hwp : $κ =Q wp.def := ⟨⟩) :
    ProofModeM (Q($ehyps ⊢ Wp.wp $s $E $e $Φ)) := do
  let ⟨e', pfeq⟩ ← iWpExprSimp e
  let nextPf ← (← iWpValueHead hyps ι s E e' Φ).getDM
      (addBIGoal hyps q(Wp.wp $s $E $e' $Φ))
  return q(tac_wp_expr_simp $nextPf $pfeq)

elab "wp_finish" : tactic =>
  ProofModeM.runTacticWp `wp_finish fun mvar {hyps, ι, s, E, e, Φ, ..} => do
    let pf ← iWpFinish hyps ι s E e Φ
    mvar.assign pf

@[rocq_alias heap_lang.tac_wp_bind]
public theorem tac_wp_bind [ι : IrisGS_gen hlc Exp GF] {Δ} {s : Stuckness} {E : CoPset} {K : List ECtxItem} {e' : Exp} {Φ : Val → IProp GF}
  (H : Δ ⊢ WP e' @ s ; E {{ v, WP (ProgramLogic.fill K (Exp.ofVal (Expr:=Exp) v)) @ s; E {{ Φ }} }}) :
    (Δ ⊢ WP (ProgramLogic.fill K e') @ s ; E {{ Φ }}) :=
  H.trans (wp_bind (ProgramLogic.fill K))

public meta def iWpBindCore {u}
  {GF : Q(BundledGFunctors.{0, 0, 0})}
  {hlc : Q(HasLC)}
  {prop : Q(Type u)}
  {bi : Q(BI $prop)}
  (ehyps : Q($prop))
  (ι : Q(IrisGS_gen $hlc Exp $GF))
  (s : Q(Stuckness))
  (E : Q(CoPset))
  (e : Q(Exp))
  (Φ : Q(Val → $prop))
  (K : Q(List ECtxItem))
  (e' : Q(Exp))
  (k : (A : Q($prop)) → ProofModeM Q($ehyps ⊢ $A))

  (_hu : QuotedLevelDefEq u 0 := ⟨⟩)
  (_hprop : $prop =Q IProp $GF := ⟨⟩)
  (_hbi : $bi =Q UPred.instBIUPred := ⟨⟩)
  (κ : Q(Wp $prop Exp Val Stuckness) := q(wp.def))
  (_hwp : $κ =Q wp.def := ⟨⟩) :
    ProofModeM (Q($ehyps ⊢ Wp.wp $s $E (ProgramLogic.fill $K $e') $Φ)) := do
  match K with
  | ~q([]) =>
    -- don't do anything for empty evaluation context
    k q(Wp.wp $s $E $e $Φ)
  | _ =>
    -- construct the new postcondition
    let Φ' : Q(Val → IProp $GF) ←
      Qq.withLocalDeclDQ `v q(Val) fun v => do
        mkLambdaFVars #[v] <|
          q(Wp.wp $s $E $(← HeapLang.fill K q(.ofVal $v)) $Φ)
    have _ : $Φ' =Q (fun v : Val => Wp.wp (PROP := IProp $GF) $s $E (ProgramLogic.fill $K (v : Exp)) $Φ) := ⟨⟩

    let pf ← k q(Wp.wp $s $E $e' $Φ')
    return q(tac_wp_bind $pf)


-- `hl_exp` must bind tighter than `;` in the heaplang notation so `wp_bind _ _; tac` parses
elab "wp_bind" colGt ppSpace focus:hl_exp:10 : tactic =>
  ProofModeM.runTacticWp `wp_bind fun mvar {ehyps, hyps, s, ι, E, e, Φ, ..} => do
    let focus ← elabTermEnsuringTypeQ (←`(hl($focus))) q(HeapLang.Exp)
    trace[wp_bind] s!"Context to bind over: {←ppExpr focus}"

    let some {K, e', ..} ← findECtx e fun _ e => do
      trace[wp_bind] s!"trying to unify {←ppExpr e} with {←ppExpr focus}"
      guard <| ← isDefEq e focus
    | throwIPMError s!"Cannot unify {←ppExpr focus} with any possible evaluation context"
    trace[wp_bind] s!"Found context {←ppExpr K} with expression {←ppExpr e'} matching our focus"

    mvar.assign <| ← iWpBindCore ehyps ι s E e Φ K e' (addBIGoal hyps)

@[rocq_alias heap_lang.tac_wp_pure]
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

public meta def iWpPure {u}
    {GF : Q(BundledGFunctors.{0, 0, 0})}
    {hlc : Q(HasLC)}
    {prop : Q(Type u)}
    {bi : Q(BI $prop)}
    {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps)
    (ι : Q(IrisGS_gen $hlc Exp $GF))
    (s : Q(Stuckness))
    (E : Q(CoPset))
    (e : Q(Exp))
    (Φ : Q(Val → $prop))
    (failOnUnsolved : Bool)
    (findPureExec : (e₁ : Q(Exp)) →
      ProofModeM ((φ : Q(Prop)) × (n : Q(Nat)) × (e₂ : Q(Exp)) ×
        Q(ProgramLogic.Language.PureExec $φ $n $e₁ $e₂)))
    (_hu : QuotedLevelDefEq u 0 := ⟨⟩)
    (_hprop : $prop =Q IProp $GF := ⟨⟩)
    (_hbi : $bi =Q UPred.instBIUPred := ⟨⟩)
    (κ : Q(Wp $prop Exp Val Stuckness) := q(wp.def))
    (_hwp : $κ =Q wp.def := ⟨⟩) :
      ProofModeM ((ehyps' : Q($prop)) × Hyps bi ehyps' × (e' : Q(Exp)) ×
      (Q(($ehyps' ⊢ Wp.wp $s $E $e' $Φ) → $ehyps ⊢ Wp.wp $s $E $e $Φ))) := do
  let some {result := ⟨φ, n, e₂, inst⟩, K, e' := e₁, ..} ←
    findECtx (α:=((_ : Q(Prop)) × (_ : Q(Nat)) × (_ : Q(Exp)) × Lean.Expr)) e fun _ => findPureExec
  | throwIPMError "Cannot find expression to evaluate"
  have inst : Q(ProgramLogic.Language.PureExec $φ $n $e₁ $e₂) := inst

  let ⟨_, hyps', pf⟩ ← iModAction hyps q(modality_laterN $n)
  let ⟨inner, .up _⟩ ← HeapLang.fillQ K e₂
  let HΦ ← iSolveSidecondition φ (failOnUnsolved := failOnUnsolved)
  return ⟨_, hyps', inner, q(fun nextPf => tac_wp_pure $inst $HΦ $pf nextPf)⟩

/-- Find any pure step for `e₁`, as `wp_pure _` does. -/
public meta def findAnyPureExec (e₁ : Q(Exp)) :
    ProofModeM ((φ : Q(Prop)) × (n : Q(Nat)) × (e₂ : Q(Exp)) ×
      Q(ProgramLogic.Language.PureExec $φ $n $e₁ $e₂)) := do
  let φ  ← mkFreshExprMVarQ q(Prop)
  let n  ← mkFreshExprMVarQ q(Nat)
  let e₂ ← mkFreshExprMVarQ q(Exp)
  let some inst ← ProofModeM.trySynthInstanceQ q(ProgramLogic.Language.PureExec $φ $n $e₁ $e₂)
    | failure
  return ⟨φ, n, e₂, inst⟩

elab "wp_pure" failOnUnsolved:("+!failOnUnsolved")? colGt ppSpace focus:hl_exp:10 : tactic =>
  ProofModeM.runTacticWp `wp_pure fun mvar {hyps, ι, s, E, e, Φ, ..} => do
    let focus ← elabTermEnsuringTypeQ (← `(hl($focus))) q(HeapLang.Exp)
    let ⟨_, hyps', e', pf⟩ ← iWpPure hyps ι s E e Φ failOnUnsolved.isSome fun e₁ => do
      guard <| ← isDefEq e₁ focus
      findAnyPureExec e₁
    let pf' ← iWpFinish hyps' ι s E e' Φ
    mvar.assign <| q($pf $pf')

macro "wp_pure" : tactic => `(tactic| wp_pure _)
macro "wp_pure" "+!failOnUnsolved" : tactic => `(tactic| wp_pure +!failOnUnsolved _)

/-- Reduce all pure redexes at the head of the weakest precondition, then simplify the
resulting expression and strip the weakest precondition if it has become a value.

A pure step whose side condition cannot be discharged is not taken. -/
macro "wp_pures" : tactic =>
  -- Rocq: `first [progress repeat (wp_pure _; []) | wp_finish]`
  `(tactic| first
    | (wp_pure +!failOnUnsolved; repeat wp_pure +!failOnUnsolved)
    | wp_finish)

/-- Beta-reduce the innermost application, unfolding a head hidden behind a definition. -/
elab "wp_rec" : tactic =>
  ProofModeM.runTacticWp `wp_rec fun mvar {hyps, ι, s, E, e, Φ, ..} => do
    let ⟨_, hyps', e', pf⟩ ← iWpPure hyps ι s E e Φ (failOnUnsolved := false) fun e₁ => do
      let ~q(Exp.app (Exp.ofVal $f) (Exp.ofVal $a)) := e₁ | failure
      -- reduce `f` to find a recursive function
      let f' : Q(Val) ← whnf f
      let ~q(Val.rec_ $fb $xb $body) := f' | failure
      have : $f' =Q $f := ⟨⟩
      -- substitute the folded head `f`, not the unfolded `Val.rec_`
      let e₂ := q(Exp.subst $xb $a (Exp.subst $fb $f $body))
      return ⟨_, _, e₂, q(instPureExecBeta)⟩
    let pf' ← iWpFinish hyps' ι s E e' Φ
    mvar.assign <| q($pf $pf')


macro "wp_if" : tactic => `(tactic | wp_pure (if _ then _ else _))
macro "wp_if_true" : tactic => `(tactic | wp_pure (if #true then _ else _))
macro "wp_if_false" : tactic => `(tactic | wp_pure (if #false then _ else _))
macro "wp_unop" : tactic => `(tactic | wp_pure (&(Exp.unop _ _)))
macro "wp_binop" : tactic => `(tactic | wp_pure (&(Exp.binop _ _ _)))
macro "wp_op" : tactic => `(tactic | first | wp_unop | wp_binop)
macro "wp_lam" : tactic => `(tactic | wp_rec)
-- use `wp_pure (_ _)` in `wp_let`, `wp_seq` and `wp_match` because no unfolding is needed
macro "wp_let" : tactic => `(tactic | (wp_pure (rec _ &(.named _) := _); wp_pure (_ _)))
macro "wp_seq" : tactic => `(tactic | (wp_pure (rec _ _ := _); wp_pure (_ _)))
macro "wp_proj" : tactic => `(tactic | first | wp_pure (fst(_)) | wp_pure (snd(_)))
macro "wp_case" : tactic => `(tactic | wp_pure (&(Exp.case _ _ _)))
macro "wp_inj" : tactic => `(tactic | first | wp_pure (injl(_)) | wp_pure (injr(_)))
macro "wp_pair" : tactic => `(tactic | wp_pure ((_, _)))
macro "wp_closure" : tactic => `(tactic | wp_pure (rec &_ &_ := _))
macro "wp_match" : tactic => `(tactic | (wp_case; wp_closure; wp_pure (_ _)))

/-! ## The `wp_apply` tactics -/

/-- Indicates whether `wp_apply` or `wp_smart_apply` is used. -/
inductive WpApplyKind where
  | apply
  | smartApply

structure WpApplyState {u} {GF : Q(BundledGFunctors.{0, 0, 0})}
    {hlc : Q(HasLC)} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    {s : Q(Stuckness)} {E : Q(CoPset)} {e : Q(Exp)} {Φ : Q(Val → $prop)}
    (κ : Q(Wp $prop Exp Val Stuckness)) where
  {ehypsC : Q($prop)}
  hypsC : Hyps bi ehypsC
  eC : Q(Exp)
  prefixPf : Q(($ehypsC ⊢ @Wp.wp $prop Exp Val Stuckness $κ $s $E $eC $Φ) →
    $ehyps ⊢ @Wp.wp $prop Exp Val Stuckness $κ $s $E $e $Φ)

meta partial def iWpApplyCore {u} {GF : Q(BundledGFunctors.{0, 0, 0})} {hlc : Q(HasLC)}
    {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (ι : Q(IrisGS_gen $hlc Exp $GF)) (s : Q(Stuckness)) (E : Q(CoPset))
    (e : Q(Exp)) (Φ : Q(Val → $prop)) (pmt : PMTerm) (wpApplyKind : WpApplyKind)
    (_hu : QuotedLevelDefEq u 0 := ⟨⟩) (_hprop : $prop =Q IProp $GF := ⟨⟩)
    (_hbi : $bi =Q UPred.instBIUPred := ⟨⟩)
    (κ : Q(Wp $prop Exp Val Stuckness) := q(wp.def)) (_hwp : $κ =Q wp.def := ⟨⟩) :
    ProofModeM Q($ehyps ⊢ Wp.wp $s $E $e $Φ) := do
  let ⟨_, hypsP, p, A, posePf⟩ ← iHave hyps q(Wp.wp $s $E $e $Φ) pmt true
  let lemIVar ← mkFreshIVarId (isTrue p)
  let ⟨_, hyps0, addPf⟩ := Hyps.add bi .anonymous lemIVar p A hypsP
  let mut st : @WpApplyState u GF hlc prop bi ehyps s E e Φ κ :=
    { hypsC := hyps0, eC := e,
      prefixPf := q(fun pf => $posePf ($(addPf).mp.trans pf)) }
  let failed ← addMessageContext m!"cannot apply {A}"
  repeat
    let ⟨hypsC, eC, prefixPf⟩ := st
    let ⟨ehypsR, hypsR, _, A', p', _, remPf⟩ := Hyps.remove (rp := true) hypsC lemIVar
    let applied ←
      findECtx (α := Q($ehypsR ∗ □?$p' $A' ⊢ Wp.wp $s $E $eC $Φ)) eC fun K e' => do
        trace[wp_apply] m!"trying to apply {A'} to {e'}"
        iWpBindCore _ ι s E eC Φ K e' (iApply hypsR p' A' ·)
    if let some {result := pf, ..} := applied then
      return q($prefixPf <| $(remPf).mp.trans $pf)
    match wpApplyKind with
    | .apply => throwIPMError failed
    | .smartApply =>
      try
        let ⟨_, hypsN, eN, purePf⟩ ←
          iWpPure hypsC ι s E eC Φ (failOnUnsolved := true) findAnyPureExec
        let ⟨eN', pfeq⟩ ← iWpExprSimp eN
        st := ⟨hypsN, eN', q(fun pf => $prefixPf ($purePf (tac_wp_expr_simp pf $pfeq)))⟩
      catch err =>
        trace[wp_apply] "Error: {err.toMessageData}"
        if err.isInterrupt || err.isMaxHeartbeat then throw err
        throwIPMError failed

meta def wpApplyRaw (tacName : Name) (wpApplyKind : WpApplyKind) (pmt : TSyntax `pmTerm) :
    TacticM Unit := do
  let pmt ← liftMacroM <| PMTerm.parse pmt
  ProofModeM.runTacticWp tacName fun mvar {hyps, ι, s, E, e, Φ, ..} => do
    mvar.assign (← iWpApplyCore hyps ι s E e Φ pmt wpApplyKind)

elab "wp_apply_raw" colGt pmt:pmTerm : tactic =>
  wpApplyRaw `wp_apply .apply pmt
elab "wp_smart_apply_raw" colGt pmt:pmTerm : tactic =>
  wpApplyRaw `wp_smart_apply .smartApply pmt
/-- Strip a leading `▷` and simplify WP expressions in the goals an application produced. -/
macro "wp_apply_post" : tactic => `(tactic| ((try inext) <;> (try wp_expr_simp)))

/--
`wp_apply lem` poses the lemma `lem`, whose conclusion must be a `WP e' ...`, and applies
it to the goal `WP e ...` after binding an evaluation context `K` with `e = K[e']`.
Premises of `lem` become new goals; a leading `▷` in a premise is stripped, and WP
premises have their expression simplified. `wp_apply lem $$ pats` additionally
specialises the premises of `lem` with the given specialisation patterns, and
`wp_apply lem with introPats` introduces the intro patterns introPats in the last Iris goal
after applying the lemma.
-/
syntax (name := wpApply) "wp_apply " colGt pmTerm
  (" with" (colGt ppSpace introPat)+)? : tactic

macro_rules
  | `(tactic| wp_apply $pmt:pmTerm $[with $pats*]?) => do
    let t : TSyntax `tactic ←
      if let some pats := pats then
        `(tactic| focusLastIrisGoal (iintro $pats*))
      else
        `(tactic| skip)
    `(tactic| focus (((wp_apply_raw $pmt) <;> wp_apply_post); $t:tactic))

/--
`wp_smart_apply lem` is like `wp_apply lem`, but when the lemma does not apply,
it takes single pure steps (`wp_pure`) and retries, until the lemma applies or
no pure step is possible. `$$` and `with` behave as for `wp_apply`.
-/
syntax (name := wpSmartApply) "wp_smart_apply " colGt pmTerm
  (" with" (colGt ppSpace introPat)+)? : tactic

macro_rules
  | `(tactic| wp_smart_apply $pmt:pmTerm $[with $pats*]?) => do
    let t : TSyntax `tactic ←
      if let some pats := pats then
        `(tactic| focusLastIrisGoal (iintro $pats*))
      else
        `(tactic| skip)
    `(tactic| focus (((wp_smart_apply_raw $pmt) <;> wp_apply_post); $t:tactic))

/-! ## Tactic lemmas for the heap tactics -/

/-- Hand out looked-up hypothesis and a wand that restores the context
    Analogue of `envs_lookup_split` in Iris-Rocq, used by read lemmas -/
theorem lookup_split [BI PROP] {Δ' Δ'' P : PROP} [Affine P] {p : Bool}
    (hsplit : Δ' ⊣⊢ Δ'' ∗ □?p P) : Δ' ⊢ P ∗ (P -∗ Δ') := by
  match p with
  | false => exact hsplit.1.trans (sep_comm.1.trans (sep_mono .rfl (wand_intro hsplit.2)))
  | true =>
    refine hsplit.1.trans ?_
    refine (sep_mono .rfl intuitionistically_sep_dup.1).trans ?_
    refine sep_left_comm.1.trans ?_
    exact sep_mono intuitionistically_elim (wand_intro (sep_elim_left.trans hsplit.2))

/-- Recover the exact-result form used by the shared heap-tactic machinery from a Texan
triple. -/
private theorem wp_exact_of_triple [HeapLangGS hlc GF]
    {s : Stuckness} {E : CoPset} {e : Exp} {r : Val} {P P' : IProp GF}
    (hwp : {{ ▷ P }} e @ s; E {{ RET r; P' }}) :
    ▷ P ⊢ WP e @ s; E {{ v', ⌜v' = r⌝ ∗ P' }} := by
  iintro HP
  iapply hwp $$ HP
  iintro !> HP'
  iframe HP'
  ipureintro
  rfl

/-- Helper lemma for the heap `tac_wp_*` lemmas. -/
theorem tac_wp_heap_op [ι : HeapLangGS hlc GF] {Δ Δ' Δ'' P P' : IProp GF}
    {s : Stuckness} {E : CoPset} {K : List ECtxItem} {e : Exp} {r : Val} {Φ}
    (hval : ProgramLogic.toVal e = none)
    (hwp : ▷ P ⊢ WP e @ s ; E {{ v', ⌜v' = r⌝ ∗ P' }})
    (hlater : Δ ⊢ ▷ Δ')
    (hsplit : Δ' ⊣⊢ Δ'' ∗ P)
    (hcont : Δ'' ∗ P' ⊢ WP (ProgramLogic.fill K (Exp.ofVal (Expr := Exp) r)) @ s ; E {{ Φ }}) :
    Δ ⊢ WP (ProgramLogic.fill K e) @ s ; E {{ Φ }} := by
  refine hlater.trans ?_
  refine .trans ?_ (wp_bind (ProgramLogic.fill K))
  refine (later_mono hsplit.1).trans ?_
  refine later_sep.1.trans ?_
  refine (sep_mono .rfl hwp).trans ?_
  refine (wp_frame_step_l' hval Std.LawfulSet.subset_refl).trans (wp_mono fun v' => ?_)
  iintro ⟨HΔ, %hv, HP⟩
  subst hv
  iapply hcont
  iframe

@[rocq_alias heap_lang.tac_wp_alloc]
public theorem tac_wp_alloc [ι : HeapLangGS hlc GF] {Δ Δ' : IProp GF}
    {s : Stuckness} {E : CoPset} {K : List ECtxItem} {v : Val} {Φ}
    (hlater : Δ ⊢ ▷ Δ')
    (hcont : ∀ l : Loc, Δ' ∗ (l ↦ some v) ⊢
      WP (ProgramLogic.fill K (Exp.ofVal (Expr := Exp) hl_val(#l))) @ s ; E {{ Φ }}) :
    Δ ⊢ WP (ProgramLogic.fill K hl(ref(&v))) @ s ; E {{ Φ }} := by
  refine hlater.trans ?_
  refine .trans ?_ (wp_bind (ProgramLogic.fill K))
  refine .trans ?_ (wand_entails (true_intro.trans
    (wand_entails ((wp_alloc v).trans (forall_elim _)))))
  exact later_mono <| forall_intro fun l => wand_intro (hcont l)

@[rocq_alias heap_lang.tac_wp_free]
public theorem tac_wp_free [ι : HeapLangGS hlc GF] {Δ Δ' Δ'' : IProp GF}
    {s : Stuckness} {E : CoPset} {K : List ECtxItem} {l : Loc} {v : Val} {Φ}
    (hlater : Δ ⊢ ▷ Δ')
    (hsplit : Δ' ⊣⊢ Δ'' ∗ (l ↦ some v))
    (hcont : Δ'' ⊢ WP (ProgramLogic.fill K (Exp.ofVal (Expr := Exp) hl_val(#()))) @ s ; E {{ Φ }}) :
    Δ ⊢ WP (ProgramLogic.fill K hl(free(#l))) @ s ; E {{ Φ }} :=
  tac_wp_heap_op rfl (wp_exact_of_triple wp_free) hlater hsplit (sep_elim_left.trans hcont)

@[rocq_alias heap_lang.tac_wp_load]
public theorem tac_wp_load [ι : HeapLangGS hlc GF] {Δ Δ' Δ'' : IProp GF} {p : Bool}
    {s : Stuckness} {E : CoPset} {K : List ECtxItem} {l : Loc} {q} {v : Val} {Φ}
    (hlater : Δ ⊢ ▷ Δ')
    (hsplit : Δ' ⊣⊢ Δ'' ∗ □?p (l ↦{q} some v))
    (hcont : Δ' ⊢ WP (ProgramLogic.fill K (Exp.ofVal (Expr := Exp) v)) @ s ; E {{ Φ }}) :
    Δ ⊢ WP (ProgramLogic.fill K hl(!v(#l))) @ s ; E {{ Φ }} := by
  refine hlater.trans ?_
  refine .trans ?_ (wp_bind (ProgramLogic.fill K))
  iapply wand_apply (wand_entails ((wp_load (s := s) (E := E) (l := l)
    (q := q) (v := v)).trans (forall_elim _)))
  refine .trans ?_ later_sep.1
  refine later_mono ?_
  exact (lookup_split hsplit).trans (sep_mono .rfl (wand_mono .rfl hcont))

@[rocq_alias heap_lang.tac_wp_store]
public theorem tac_wp_store [ι : HeapLangGS hlc GF] {Δ Δ' Δ'' : IProp GF}
    {s : Stuckness} {E : CoPset} {K : List ECtxItem} {l : Loc} {v v' : Val} {Φ}
    (hlater : Δ ⊢ ▷ Δ')
    (hsplit : Δ' ⊣⊢ Δ'' ∗ (l ↦ some v))
    (hcont : Δ'' ∗ (l ↦ some v') ⊢
      WP (ProgramLogic.fill K (Exp.ofVal (Expr := Exp) hl_val(#()))) @ s ; E {{ Φ }}) :
    Δ ⊢ WP (ProgramLogic.fill K hl(v(#l) ← &v')) @ s ; E {{ Φ }} := by
  refine hlater.trans ?_
  refine .trans ?_ (wp_bind (ProgramLogic.fill K))
  iapply wand_apply (wand_entails ((wp_store (s := s) (E := E) (l := l)
    (v := v') (v' := v)).trans (forall_elim _)))
  refine .trans ?_ later_sep.1
  refine later_mono ?_
  refine hsplit.1.trans ?_
  refine .trans sep_comm.mp ?_
  exact sep_mono .rfl (wand_intro hcont)

@[rocq_alias heap_lang.tac_wp_xchg]
public theorem tac_wp_xchg [ι : HeapLangGS hlc GF] {Δ Δ' Δ'' : IProp GF}
    {s : Stuckness} {E : CoPset} {K : List ECtxItem} {l : Loc} {v v' : Val} {Φ}
    (hlater : Δ ⊢ ▷ Δ')
    (hsplit : Δ' ⊣⊢ Δ'' ∗ (l ↦ some v))
    (hcont : Δ'' ∗ (l ↦ some v') ⊢
      WP (ProgramLogic.fill K (Exp.ofVal (Expr := Exp) v)) @ s ; E {{ Φ }}) :
    Δ ⊢ WP (ProgramLogic.fill K hl(xchg(#l, &v'))) @ s ; E {{ Φ }} :=
  tac_wp_heap_op rfl (wp_exact_of_triple wp_xchg) hlater hsplit hcont

@[rocq_alias heap_lang.tac_wp_cmpxchg_fail]
public theorem tac_wp_cmpXchg_fail [ι : HeapLangGS hlc GF] {Δ Δ' Δ'' : IProp GF} {p : Bool}
    {s : Stuckness} {E : CoPset} {K : List ECtxItem} {l : Loc} {q} {v v1 v2 : Val} {Φ}
    (hlater : Δ ⊢ ▷ Δ')
    (hsplit : Δ' ⊣⊢ Δ'' ∗ □?p (l ↦{q} some v))
    (hne : v ≠ v1) (hsafe : v.compareSafe v1)
    (hcont : Δ' ⊢
      WP (ProgramLogic.fill K (Exp.ofVal (Expr := Exp) hl_val((&v, #false)))) @ s ; E {{ Φ }}) :
    Δ ⊢ WP (ProgramLogic.fill K hl(cmpXchg(v(#l), v(&v1), v(&v2)))) @ s ; E {{ Φ }} := by
  refine hlater.trans ?_
  refine .trans ?_ (wp_bind (ProgramLogic.fill K))
  refine (later_mono ((lookup_split hsplit).trans sep_comm.1)).trans ?_
  refine later_sep.1.trans ?_
  refine (sep_mono .rfl (wp_exact_of_triple (wp_cmpXchg_fail (s := s) (E := E)
    (e1 := hl(v(&v1))) (e2 := hl(v(&v2))) rfl rfl hsafe (decide_eq_false hne)))).trans ?_
  refine (wp_frame_step_l' rfl Std.LawfulSet.subset_refl).trans (wp_mono fun _ => ?_)
  iintro ⟨Hrestore, %hv, HP⟩
  subst hv
  iapply hcont
  iapply Hrestore $$ HP

@[rocq_alias heap_lang.tac_wp_cmpxchg_suc]
public theorem tac_wp_cmpXchg_suc [ι : HeapLangGS hlc GF] {Δ Δ' Δ'' : IProp GF}
    {s : Stuckness} {E : CoPset} {K : List ECtxItem} {l : Loc} {v v1 v2 : Val} {Φ}
    (hlater : Δ ⊢ ▷ Δ')
    (hsplit : Δ' ⊣⊢ Δ'' ∗ (l ↦ some v))
    (heq : v = v1) (hsafe : v.compareSafe v1)
    (hcont : Δ'' ∗ (l ↦ some v2) ⊢
      WP (ProgramLogic.fill K (Exp.ofVal (Expr := Exp) hl_val((&v, #true)))) @ s ; E {{ Φ }}) :
    Δ ⊢ WP (ProgramLogic.fill K hl(cmpXchg(v(#l), v(&v1), v(&v2)))) @ s ; E {{ Φ }} :=
  tac_wp_heap_op rfl
    (wp_exact_of_triple (wp_cmpXchg_true rfl rfl hsafe (decide_eq_true heq)))
    hlater hsplit hcont

@[rocq_alias heap_lang.tac_wp_cmpxchg]
public theorem tac_wp_cmpXchg [ι : HeapLangGS hlc GF] {Δ Δ' Δ'' : IProp GF}
    {s : Stuckness} {E : CoPset} {K : List ECtxItem} {l : Loc} {v v1 v2 : Val} {Φ}
    (hlater : Δ ⊢ ▷ Δ')
    (hsplit : Δ' ⊣⊢ Δ'' ∗ (l ↦ some v))
    (hsafe : v.compareSafe v1)
    (hsuc : v = v1 → Δ'' ∗ (l ↦ some v2) ⊢
      WP (ProgramLogic.fill K (Exp.ofVal (Expr := Exp) hl_val((&v, #true)))) @ s ; E {{ Φ }})
    (hfail : v ≠ v1 → Δ' ⊢
      WP (ProgramLogic.fill K (Exp.ofVal (Expr := Exp) hl_val((&v, #false)))) @ s ; E {{ Φ }}) :
    Δ ⊢ WP (ProgramLogic.fill K hl(cmpXchg(v(#l), v(&v1), v(&v2)))) @ s ; E {{ Φ }} :=
  if heq : v = v1 then tac_wp_cmpXchg_suc hlater hsplit heq hsafe (hsuc heq)
  else tac_wp_cmpXchg_fail (p := false) hlater hsplit heq hsafe (hfail heq)

@[rocq_alias heap_lang.tac_wp_faa]
public theorem tac_wp_faa [ι : HeapLangGS hlc GF] {Δ Δ' Δ'' : IProp GF}
    {s : Stuckness} {E : CoPset} {K : List ECtxItem} {l : Loc} {z1 z2 : Int} {Φ}
    (hlater : Δ ⊢ ▷ Δ')
    (hsplit : Δ' ⊣⊢ Δ'' ∗ (l ↦ some hl_val(#z1)))
    (hcont : Δ'' ∗ (l ↦ some hl_val(#(z1 + z2))) ⊢
      WP (ProgramLogic.fill K (Exp.ofVal (Expr := Exp) hl_val(#z1))) @ s ; E {{ Φ }}) :
    Δ ⊢ WP (ProgramLogic.fill K hl(faa(#l, #z2))) @ s ; E {{ Φ }} :=
  tac_wp_heap_op rfl (wp_exact_of_triple wp_faa) hlater hsplit hcont

@[rocq_alias heap_lang.tac_wp_allocN]
public theorem tac_wp_allocN [ι : HeapLangGS hlc GF] {Δ Δ' : IProp GF}
    {s : Stuckness} {E : CoPset} {K : List ECtxItem} {v : Val} {n : Int} {Φ}
    (hn : 0 < n)
    (hlater : Δ ⊢ ▷ Δ')
    (hcont : ∀ l : Loc, Δ' ∗ (l ↦∗ List.replicate n.toNat v) ⊢
      WP (ProgramLogic.fill K hl(#l)) @ s ; E {{ Φ }}) :
    Δ ⊢ WP (ProgramLogic.fill K hl(allocn(#n, &v))) @ s ; E {{ Φ }} := by
  refine hlater.trans ?_
  refine .trans ?_ (wp_bind (ProgramLogic.fill K))
  refine .trans ?_ (wand_entails (true_intro.trans
    (wand_entails ((wp_allocN v hn).trans (forall_elim _)))))
  exact later_mono <| forall_intro fun l =>
    wand_intro <| (sep_mono_right sep_elim_left).trans (hcont l)

/-! ## Shared machinery for the heap tactics -/

/-- Epilogue shared by the heap tactics: fill the result value `r` back into the evaluation
context `K` and run `iWpFinish` over the continuation context `hyps`. Returns the continuation
proof typed against `fill K (Exp.ofVal r)`, so the caller's `assign` matches the tac lemma's
`hcont`. -/
meta def finishHeapOp {u} {GF : Q(BundledGFunctors.{0, 0, 0})} {hlc : Q(HasLC)}
    {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (hgs : Q(HeapLangGS $hlc $GF))
    (s : Q(Stuckness)) (E : Q(CoPset)) (K : Q(List ECtxItem)) (r : Q(Val)) (Φ : Q(Val → $prop))
    (_hu : QuotedLevelDefEq u 0 := ⟨⟩) (_hprop : $prop =Q IProp $GF := ⟨⟩)
    (κ : Q(Wp $prop Exp Val Stuckness) := q(wp.def)) (_hwp : $κ =Q wp.def := ⟨⟩) :
    ProofModeM Q($ehyps ⊢ Wp.wp (self := $κ) $s $E (ProgramLogic.fill $K (Exp.ofVal $r)) $Φ) := do
  let ⟨inner, .up _⟩ ← HeapLang.fillQ K q(Exp.ofVal $r)
  iWpFinish hyps q(@HeapLang $hlc $GF $hgs) s E inner Φ (κ := κ)

/-- The points-to hypothesis located by `lookupPointsTo` for location `l`
in the (later-stripped) context `eΔ'`, together with the pruned context `eΔ''`/`hyps''` and
the splitting proof `pfSplit`, whose type is already recast to the `pointsTo` shape that the
`tac_wp_*` lemmas expect. -/
structure PointsToLookup {u : Level} {GF : Q(BundledGFunctors.{0, 0, 0})}
    {hlc : Q(HasLC)} (hgs : Q(HeapLangGS $hlc $GF)) {prop : Q(Type u)} (bi : Q(BI $prop))
    (eΔ' : Q($prop)) (l : Q(Loc)) (dq : Q(DFrac)) (p : Q(Bool)) (hu : QuotedLevelDefEq u 0)
    (hprop : $prop =Q IProp $GF) where
  /-- The value stored at `l`. -/
  v : Q(Val)
  /-- The user-facing name of the found hypothesis. -/
  name : Name
  /-- The `IVarId` of the found hypothesis. -/
  vid : IVarId
  /-- The context with the points-to hypothesis removed. -/
  eΔ'' : Q($prop)
  hyps'' : @Hyps u prop bi eΔ''
  /-- The split certificate, recast to the shape the `tac_wp_*` lemmas expect. -/
  pfSplit : Q($eΔ' ⊣⊢ $eΔ'' ∗ □?$p (pointsTo $l $dq (some $v)))

/-- Locate a hypothesis `l ↦{dq} some v` and remove it from the spatial context.
Throws if no matching hypothesis exists. -/
meta def lookupPointsTo {u} {GF : Q(BundledGFunctors.{0, 0, 0})} {hlc : Q(HasLC)}
    {prop : Q(Type u)} {bi : Q(BI $prop)} {eΔ' : Q($prop)}
    (hgs : Q(HeapLangGS $hlc $GF))
    (hyps' : Hyps bi eΔ') (l : Q(Loc)) (dq : Q(DFrac)) (p : Q(Bool))
    (hu : QuotedLevelDefEq u 0 := ⟨⟩)
    (hprop : $prop =Q IProp $GF := ⟨⟩) :
    ProofModeM (@PointsToLookup u GF hlc hgs prop bi eΔ' l dq p hu hprop) := do
  let some ⟨⟨v, name, vid⟩, eΔ'', hyps'', _, _, _, _, pf⟩ ←
      hyps'.removeG false fun name vid p' ty => do
        have ty : Q(IProp $GF) := ty
        -- destructure ty to get the location l', fraction dq' and stored value v
        let ~q(pointsTo $l' $dq' (some $v)) := ty | return none
        unless ← isDefEq l' l do return none
        -- a literal `dq`/`p` rejects other candidates; a metavariable records what was found
        unless ← isDefEq dq' dq do return none
        unless ← isDefEq p' p do return none
        return some ((v : Q(Val)), name, vid)
    | throwIPMError
        m!"cannot find a points-to hypothesis for {l} ↦\{{dq}} _"
  trace[wp_heap.lookup] "found {name} : □?{p} (pointsTo {l} ({dq}) (some {v}))"
  let pfSplit : Q($eΔ' ⊣⊢ $eΔ'' ∗ □?$p (pointsTo $l $dq (some $v))) := pf
  return { v, name, vid, eΔ'', hyps'', pfSplit }

/-- The goal handed to a heap tactic by `ProofModeM.runTacticHeapWp`: `WpGoal` fields,
plus the `HeapLangGS` instance `hgs` extracted from the goal's `IrisGS_gen`, and the
context `hyps'`/`eΔ'` after stripping the WP's step modality, with `pfLater` witnessing
the strip. -/
structure HeapWpGoal extends WpGoal where
  hgs : Q(HeapLangGS $hlc $GF)
  {eΔ' : Q($prop)}
  hyps' : @Hyps u prop bi eΔ'
  pfLater : Q($ehyps ⊢ (modality_laterN 1).M $eΔ')

/-- Shared prologue for the heap tactics: run the tactic on a WP goal, check that it is a
HeapLang WP (from the `HeapLangGS` instance), and strip the WP's step modality
off the hypotheses. -/
meta def runTacticHeapWp {α} (tacName : Name)
    (k : MVarId → HeapWpGoal → ProofModeM α) : TacticM α := do
  -- Rocq parity: every heap tactic first normalizes pure redexes. `wp_pures` only fails
  -- when the goal is not a WP, which is this tactic's failure to report, not `wp_finish`'s
  try evalTactic (← `(tactic| wp_pures))
  catch _ => throwError "{tacName}: the goal is not a WP"
  -- `wp_pures` fails on a goal that is not a WP, so if it leaves one, the pure steps have
  -- reduced the expression to a value
  let goalType ← instantiateMVars (← (← getMainGoal).getType)
  if let some {goal, ..} := parseIrisGoal? goalType then
    unless goal.consumeMData.isAppOf ``Wp.wp do
      throwError "{tacName}: the expression has been reduced to a value, there is no redex left"
  ProofModeM.runTacticWp tacName fun mvar {hyps, GF, hlc, ι, s, E, e, Φ, hu, hprop, hbi, ..} => do
    have ιQ : Q(IrisGS_gen $hlc Exp $GF) := ι
    let ~q(@HeapLang _ _ $hgs) := ιQ
      | throwIPMError "the goal is not a HeapLang WP"
    trace[wp_heap] "{tacName}: e = {e}"
    -- currently specialized to later (no twp exists yet)
    let ⟨_, hyps', pfLater⟩ ← iModAction hyps q(modality_laterN 1)
    k mvar { hyps, ι, s, E, e, Φ, hu, hprop, hbi, hgs, hyps', pfLater }

/-! ## The heap tactics -/

elab "wp_load" : tactic =>
  runTacticHeapWp `wp_load fun mvar {s, E, e, Φ, hgs, eΔ', hyps', pfLater, ..} => do
    let some {result := l, K, ..} ← findECtx e fun _ e' => do
      let ~q(Exp.load (Exp.ofVal (Val.lit (BaseLit.loc $l)))) := e' | failure
      return l
    | throwIPMError "cannot find a `load` redex"
    trace[wp_heap.redex] "load {l}; K = {K}"

    -- find `l ↦{dq} some v` in the spatial context and extract `dq`
    let dq ← mkFreshExprMVarQ q(DFrac)
    let p ← mkFreshExprMVarQ q(Bool)
    let ⟨v, _, _, _, _, pfSplit⟩ ← lookupPointsTo hgs hyps' l dq p

    -- fill the loaded value back into `K` and finish the continuation
    -- (over `hyps'`: the points-to hypothesis is kept)
    let pfCont ← finishHeapOp hyps' hgs s E K v Φ

    mvar.assign q(tac_wp_load (ι := $hgs) (Δ' := $eΔ') $pfLater $pfSplit $pfCont)

elab "wp_store" : tactic => do
  runTacticHeapWp `wp_store fun mvar {bi, s, E, e, Φ, hgs, eΔ', hyps', pfLater, ..} => do
    let some {result := (l, v'), K, ..} ← findECtx e fun _ e' => do
      let ~q(Exp.store (Exp.ofVal (Val.lit (BaseLit.loc $l))) (Exp.ofVal $v')) := e' | failure
      return (l, v')
    | throwIPMError "cannot find a `store` redex"
    trace[wp_heap.redex] "store {l} ← {v'}; K = {K}"

    -- find and remove `l ↦ some v` (stores need full ownership)
    let ⟨_, name, vid, _, hyps'', pfSplit⟩ ←
      lookupPointsTo hgs hyps' l q(DFrac.own 1) q(false)

    let ⟨_, hyps''', pf'''⟩ := hyps''.add bi name vid q(false) q(pointsTo $l (DFrac.own 1) (some $v'))

    let pfCont ← finishHeapOp hyps''' hgs s E K q(hl_val(#())) Φ

    mvar.assign q(tac_wp_store (ι := $hgs) (Δ' := $eΔ') $pfLater $pfSplit <| $(pf''').mp.trans $pfCont)
  -- a store's result is often discarded by a `;`, so try stepping through the
  -- sequencing redex using `wp_seq`
  evalTactic (← `(tactic| try wp_seq))

elab "wp_xchg" : tactic => do
  runTacticHeapWp `wp_xchg fun mvar {bi, s, E, e, Φ, hgs, eΔ', hyps', pfLater, ..} => do
    let some {result := (l, v'), K, ..} ← findECtx e fun _ e' => do
      let ~q(Exp.xchg (Exp.ofVal (Val.lit (BaseLit.loc $l))) (Exp.ofVal $v')) := e' | failure
      return (l, v')
    | throwIPMError "cannot find an `xchg` redex"
    trace[wp_heap.redex] "xchg {l} ← {v'}; K = {K}"

    -- find and remove `l ↦ some v` (xchg writes, so it needs full ownership)
    let ⟨v, name, vid, _, hyps'', pfSplit⟩ ←
      lookupPointsTo hgs hyps' l q(DFrac.own 1) q(false)

    let ⟨_, hyps''', pf'''⟩ := hyps''.add bi name vid q(false) q(pointsTo $l (DFrac.own 1) (some $v'))

    let pfCont ← finishHeapOp hyps''' hgs s E K v Φ

    mvar.assign q(tac_wp_xchg (ι := $hgs) (Δ' := $eΔ') $pfLater $pfSplit <| $(pf''').mp.trans $pfCont)
  -- like in `wp_store`, an `xchg` often discards its result, so try `wp_seq`
  evalTactic (← `(tactic| try wp_seq))

elab "wp_faa" : tactic =>
  runTacticHeapWp `wp_faa fun mvar {bi, s, E, e, Φ, hgs, eΔ', hyps', pfLater, ..} => do
    let some {result := (l, z2), K, ..} ← findECtx e fun _ e' => do
      -- faa is only defined on integers
      let ~q(Exp.faa (Exp.ofVal (Val.lit (BaseLit.loc $l)))
          (Exp.ofVal (Val.lit (BaseLit.int $z2)))) := e' | failure
      return (l, z2)
    | throwIPMError "cannot find a `faa` redex"
    trace[wp_heap.redex] "faa {l} += {z2}; K = {K}"

    -- find and remove `l ↦ some v` (faa writes, so it needs full ownership)
    let ⟨v, name, vid, eΔ'', hyps'', pfSplit⟩ ←
      lookupPointsTo hgs hyps' l q(DFrac.own 1) q(false)

    -- check that the points-to value is an integer (FAA requirement)
    let ~q(Val.lit (BaseLit.int $z1)) := v
      | throwIPMError
          m!"the points-to hypothesis for location {l} does not store an integer"
    have pfSplit : Q($eΔ' ⊣⊢ $eΔ'' ∗
      pointsTo $l (DFrac.own 1) (some (Val.lit (BaseLit.int $z1)))) := pfSplit

    let ⟨_, hyps''', pf'''⟩ := hyps''.add bi name vid q(false)
      q(pointsTo $l (DFrac.own 1) (some (Val.lit (BaseLit.int ($z1 + $z2)))))

    let pfCont ← finishHeapOp hyps''' hgs s E K q(Val.lit (BaseLit.int $z1)) Φ

    mvar.assign q(tac_wp_faa (ι := $hgs) (Δ' := $eΔ') $pfLater $pfSplit <| $(pf''').mp.trans $pfCont)

elab "wp_cmpxchg_suc" : tactic =>
  runTacticHeapWp `wp_cmpxchg_suc fun mvar {bi, s, E, e, Φ, hgs, eΔ', hyps', pfLater, ..} => do
    let some {result := (l, v1, v2), K, ..} ← findECtx e fun _ e' => do
      let ~q(Exp.cmpXchg (Exp.ofVal (Val.lit (BaseLit.loc $l)))
          (Exp.ofVal $v1) (Exp.ofVal $v2)) := e' | failure
      return (l, v1, v2)
    | throwIPMError "cannot find a `cmpXchg` redex"
    trace[wp_heap.redex] "cmpXchg {l}: {v1} → {v2}; K = {K}"

    -- find and remove `l ↦ some v` (a successful cmpXchg writes, so full ownership)
    let ⟨v, name, vid, _, hyps'', pfSplit⟩ ←
      lookupPointsTo hgs hyps' l q(DFrac.own 1) q(false)

    -- check safety, don't throw hard error to match Rocq behavior
    let pfSafe ← iSolveSidecondition q(($v).compareSafe $v1 = true) (failOnUnsolved := false)

    -- check equality, don't throw hard error to match Rocq behavior
    let pfEq ← iSolveSidecondition q($v = $v1) (failOnUnsolved := false)

    let ⟨_, hyps''', pf'''⟩ := hyps''.add bi name vid q(false)
      q(pointsTo $l (DFrac.own 1) (some $v2))

    let pfCont ← finishHeapOp hyps''' hgs s E K
      q(Val.pair $v (Val.lit (BaseLit.bool true))) Φ

    mvar.assign
      q(tac_wp_cmpXchg_suc (ι := $hgs) (Δ' := $eΔ') $pfLater $pfSplit $pfEq $pfSafe <| $(pf''').mp.trans $pfCont)

elab "wp_cmpxchg_fail" : tactic =>
  runTacticHeapWp `wp_cmpxchg_fail fun mvar {s, E, e, Φ, hgs, eΔ', hyps', pfLater, ..} => do
    let some {result := (l, v1, v2), K, ..} ← findECtx e fun _ e' => do
      let ~q(Exp.cmpXchg (Exp.ofVal (Val.lit (BaseLit.loc $l)))
          (Exp.ofVal $v1) (Exp.ofVal $v2)) := e' | failure
      return (l, v1, v2)
    | throwIPMError "cannot find a `cmpXchg` redex"
    trace[wp_heap.redex] "cmpXchg {l}: {v1} → {v2}; K = {K}"

    -- any fraction suffices for a failing compare (the points-to is only read)
    let dq ← mkFreshExprMVarQ q(DFrac)
    let p ← mkFreshExprMVarQ q(Bool)
    let ⟨v, _, _, _, _, pfSplit⟩ ← lookupPointsTo hgs hyps' l dq p

    -- check safety, don't throw hard error to match Rocq behavior
    let pfSafe ← iSolveSidecondition q(($v).compareSafe $v1 = true) (failOnUnsolved := false)

    -- check equality, don't throw hard error to match Rocq behavior
    let pfNeq ← iSolveSidecondition q($v ≠ $v1) (failOnUnsolved := false)

    let pfCont ← finishHeapOp hyps' hgs s E K
      q(Val.pair $v (Val.lit (BaseLit.bool false))) Φ

    mvar.assign
      q(tac_wp_cmpXchg_fail (ι := $hgs) (Δ' := $eΔ') (v2 := $v2)
        $pfLater $pfSplit $pfNeq $pfSafe $pfCont)

-- `colGt` on the names keeps an omitted one from swallowing the next line's tactic
elab "wp_cmpxchg" " with" colGt ppSpace h1:binderIdent colGt ppSpace h2:binderIdent : tactic =>
  runTacticHeapWp `wp_cmpxchg fun mvar {bi, GF, hlc, s, E, e, Φ, hgs, eΔ', hyps', pfLater, ..} => do
    let some {result := (l, v1, v2), K, ..} ← findECtx e fun _ e' => do
      let ~q(Exp.cmpXchg (Exp.ofVal (Val.lit (BaseLit.loc $l)))
          (Exp.ofVal $v1) (Exp.ofVal $v2)) := e' | failure
      return (l, v1, v2)
    | throwIPMError "cannot find a `cmpXchg` redex"
    trace[wp_heap.redex] "cmpXchg {l}: {v1} → {v2}; K = {K}"

    -- find and remove `l ↦ some v` (the success branch writes, so full ownership)
    let ⟨v, name, vid, eΔ'', hyps'', pfSplit⟩ ←
      lookupPointsTo hgs hyps' l q(DFrac.own 1) q(false)

    let ⟨_, hypsSuc, pfEq⟩ := hyps''.add bi name vid q(false)
      q(pointsTo $l (DFrac.own 1) (some $v2))

    -- check safety, don't throw hard error to match Rocq behavior
    let pfSafe ← iSolveSidecondition q(($v).compareSafe $v1 = true) (failOnUnsolved := false)

    let (sucName, _) ← getFreshName h1
    let pfSuc : Q($v = $v1 → ($eΔ'' ∗ pointsTo $l (DFrac.own 1) (some $v2) ⊢
      Wp.wp (self := wp.def (ι := @HeapLang $hlc $GF $hgs)) $s $E
        (ProgramLogic.fill $K (Exp.ofVal (Expr := Exp)
          (Val.pair $v (Val.lit (BaseLit.bool true))))) $Φ)) ←
        Qq.withLocalDeclDQ sucName q($v = $v1) fun _h => do
          let pf ← finishHeapOp hypsSuc hgs s E K
            q(Val.pair $v (Val.lit (BaseLit.bool true))) Φ
          mkLambdaFVars #[_h] q($(pfEq).mp.trans $pf)

    let (failName, _) ← getFreshName h2
    let pfFail : Q($v ≠ $v1 → $eΔ' ⊢
      Wp.wp (self := wp.def (ι := @HeapLang $hlc $GF $hgs)) $s $E
        (ProgramLogic.fill $K (Exp.ofVal (Expr := Exp)
          (Val.pair $v (Val.lit (BaseLit.bool false))))) $Φ) ←
        Qq.withLocalDeclDQ failName q($v ≠ $v1) fun _h => do
          let pf ← finishHeapOp hyps' hgs s E K
            q(Val.pair $v (Val.lit (BaseLit.bool false))) Φ
          mkLambdaFVars #[_h] pf

    mvar.assign
      q(tac_wp_cmpXchg (ι := $hgs) (Δ' := $eΔ') (v2 := $v2)
        $pfLater $pfSplit $pfSafe $pfSuc $pfFail)

elab "wp_free" : tactic =>
  runTacticHeapWp `wp_free fun mvar {s, E, e, Φ, hgs, eΔ', hyps', pfLater, ..} => do
    let some {result := l, K, ..} ← findECtx e fun _ e' => do
      let ~q(Exp.free (Exp.ofVal (Val.lit (BaseLit.loc $l)))) := e' | failure
      return l
    | throwIPMError "cannot find a `free` redex"
    trace[wp_heap.redex] "free {l}; K = {K}"

    -- find and remove `l ↦ some v` (freeing needs full ownership); the continuation
    -- runs over the pruned context `hyps''` since the points-to is consumed
    let ⟨_, _, _, _, hyps'', pfSplit⟩ ←
      lookupPointsTo hgs hyps' l q(DFrac.own 1) q(false)

    let pfCont ← finishHeapOp hyps'' hgs s E K q(hl_val(#())) Φ

    mvar.assign q(tac_wp_free (ι := $hgs) (Δ' := $eΔ') $pfLater $pfSplit $pfCont)


elab "wp_alloc" colGt ppSpace loc:binderIdent " with" colGt ppSpace hyp:binderIdent : tactic =>
  runTacticHeapWp `wp_alloc fun mvar
      {bi, GF, hlc, s, E, e, Φ, hgs, eΔ', hyps', pfLater, ..} => do
    let some {result := (n, v), K, ..} ← findECtx e fun _ e' => do
      let ~q(Exp.allocN (Exp.ofVal (Val.lit (BaseLit.int $n)))
          (Exp.ofVal $v)) := e' | failure
      return (n, v)
    | throwIPMError "cannot find an allocation redex"
    let single ← isDefEq n q((1 : Int))

    trace[wp_heap.redex] "allocn {n} {v}; K = {K}"

    let (locName, _) ← getFreshName loc
    let finish (P : Q(Loc → IProp $GF)) : ProofModeM Q(∀ l : Loc, $eΔ' ∗ $P l ⊢
          Wp.wp (self := wp.def (ι := @HeapLang $hlc $GF $hgs)) $s $E
            (ProgramLogic.fill $K (Exp.ofVal (Expr := Exp) (Val.lit (BaseLit.loc l)))) $Φ) :=
      Qq.withLocalDeclDQ locName q(Loc) fun l => do
        let Pl : Q(IProp $GF) := q($P $l)
        let ⟨_, _, hyps'', pfEq⟩ ← hyps'.addWithInfo bi hyp q(false) Pl
        let pf ← finishHeapOp hyps'' hgs s E K q(Val.lit (BaseLit.loc $l)) Φ
        mkLambdaFVars #[l] q($(pfEq).mp.trans $pf)

    if single then
      let P : Q(Loc → IProp $GF) := q(fun l => pointsTo l (DFrac.own 1) (some $v))
      let pfCont ← finish P
      mvar.assign q(tac_wp_alloc (ι := $hgs) (Δ' := $eΔ') $pfLater $pfCont)
    else
      -- a non-positive allocation is stuck, so the bound is the caller's to discharge
      let pfPos ← iSolveSidecondition q(0 < $n) (failOnUnsolved := false)
      let P : Q(Loc → IProp $GF) :=
        q(fun l => array l (DFrac.own 1) (List.replicate ($n).toNat $v))
      let pfCont ← finish P
      mvar.assign q(tac_wp_allocN (ι := $hgs) (Δ' := $eΔ') $pfPos $pfLater $pfCont)

macro "wp_alloc" colGt ppSpace loc:binderIdent : tactic => `(tactic| wp_alloc $loc with _)

-- Register the trace classes emitted by the tactics above; enables
-- `set_option trace.wp_bind true` (and analogously for the others).
initialize registerTraceClass `wp_bind
initialize registerTraceClass `wp_pure
initialize registerTraceClass `wp_apply
initialize registerTraceClass `wp_heap
initialize registerTraceClass `wp_heap.redex (inherited := true)
initialize registerTraceClass `wp_heap.lookup (inherited := true)
