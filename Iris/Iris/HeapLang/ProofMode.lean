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
  if let .some _ ← ProofModeM.trySynthInstanceQ q(ElimModal $c false $p' iprop(|={$E}=> $goal) $A' $goal $Q') then
    if let some _ ← try? <| iSolveSidecondition c then
      let pf ← addBIGoal hyps q($goal)
      return some q(tac_wp_value_nofupd (s:=$s) (E:=$E) $pf)

  let pf ← addBIGoal hyps q(iprop(|={$E}=> $goal))
  return some q(tac_wp_value (s:=$s) $pf)

elab "wp_value_head" : tactic =>
  ProofModeM.runTacticWp fun mvar {bi, hyps, ι, s, E, e, Φ, hbi, ..} => do
    have : $bi =Q UPred.instBIUPred := hbi
    let some pf ← iWpValueHead hyps ι s E e Φ
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
  ProofModeM.runTacticWp fun mvar {hyps, ι, s, E, e, Φ, ..} => do
    let pf ← iWpFinish hyps ι s E e Φ
    mvar.assign pf

public theorem tac_wp_bind [ι : IrisGS_gen hlc Exp GF] {Δ} {s : Stuckness} {E : CoPset} {K : List ECtxItem} {e' : Exp} {Φ : Val → IProp GF}
  (H : Δ ⊢ WP e' @ s ; E {{ v, WP (ProgramLogic.fill K (Exp.ofVal (Expr:=Exp) v)) @ s; E {{ Φ }} }}) :
    (Δ ⊢ WP (ProgramLogic.fill K e') @ s ; E {{ Φ }}) :=
  H.trans (wp_bind (ProgramLogic.fill K))

-- level of hl_exp should be above the level of ; in the heaplang notation to make `wp_bind _ _; wp_rec` work
elab "wp_bind" colGt ppSpace focus:hl_exp:10 : tactic =>
  ProofModeM.runTacticWp fun mvar {GF, hyps, s, E, e, Φ, ..} => do
    let focus ← elabTermEnsuringTypeQ (←`(hl($focus))) q(HeapLang.Exp)
    trace[wp_bind] s!"Context to bind over: {←ppExpr focus}"

    let some {K, e', ..} ← findECtx e (fun e => do
      trace[wp_bind] s!"trying to unify {←ppExpr e} with {←ppExpr focus}"
      guard <| ← isDefEq e focus)
    -- TODO: add a throwProofModeEx for throwing errors consistently across all tactics
      | throwTacticEx `wp_bind mvar s!"Cannot unify {←ppExpr focus} with any possible evaluation context"
    trace[wp_bind] s!"Found context {←ppExpr K} with expression {←ppExpr e'} matching our focus"

    match K with
    | ~q([]) =>
      -- don't do anything for empty evaluation context
      addMVarGoal mvar
    | _ =>
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

elab "wp_pure " colGt ppSpace focus:hl_exp:10 : tactic =>
  ProofModeM.runTacticWp fun mvar {hyps, ι, s, E, e, Φ, ..} => do
    let focus ← elabTermEnsuringTypeQ (← `(hl($focus))) q(HeapLang.Exp)
    trace[wp_pure] m!"Focusing with {focus}"

    let some {result := (φ, n, e₂, inst), K, e' := e₁, heq := _} ← findECtx e fun e₁ => do
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

    let nextPf ← iWpFinish hyps' ι s E inner Φ

    let HΦ ← iSolveSidecondition q($φ) (failOnUnsolved := false)

    let pf := q(tac_wp_pure $inst $HΦ $pf $nextPf)

    mvar.assign pf

macro "wp_pure" : tactic => `(tactic| wp_pure _)
macro "wp_pures" : tactic => `(tactic| repeat wp_pure)

macro "wp_rec" : tactic => `(tactic | (wp_bind _ _; iapply $(mkIdent `wp_rec):ident; rfl; imodintro; wp_finish))

macro "wp_if" : tactic => `(tactic | wp_pure (if _ then _ else _))
macro "wp_if_true" : tactic => `(tactic | wp_pure (if #true then _ else _))
macro "wp_if_false" : tactic => `(tactic | wp_pure (if #false then _ else _))
macro "wp_unop" : tactic => `(tactic | wp_pure (&(Exp.unop _ _)))
macro "wp_binop" : tactic => `(tactic | wp_pure (&(Exp.binop _ _ _)))
macro "wp_op" : tactic => `(tactic | first | wp_unop | wp_binop)
macro "wp_lam" : tactic => `(tactic | wp_rec)
macro "wp_let" : tactic => `(tactic | (wp_pure (rec _ &(.named _) := _); wp_lam))
macro "wp_seq" : tactic => `(tactic | (wp_pure (rec _ _ := _); wp_lam))
macro "wp_proj" : tactic => `(tactic | first | wp_pure (fst(_)) | wp_pure (snd(_)))
macro "wp_case" : tactic => `(tactic | wp_pure (&(Exp.case _ _ _)))
macro "wp_inj" : tactic => `(tactic | first | wp_pure (injl(_)) | wp_pure (injr(_)))
macro "wp_pair" : tactic => `(tactic | wp_pure ((_, _)))
macro "wp_closure" : tactic => `(tactic | wp_pure (rec &_ &_ := _))
macro "wp_match" : tactic => `(tactic | (wp_case; wp_closure; wp_lam))

/-! ## Tactic lemmas for the heap tactics -/

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

public theorem tac_wp_alloc [ι : HeapLangGS hlc GF] {Δ Δ' : IProp GF}
    {s : Stuckness} {E : CoPset} {K : List ECtxItem} {v : Val} {Φ}
    (hlater : Δ ⊢ ▷ Δ')
    (hcont : ∀ l : Loc, Δ' ∗ (l ↦ some v) ⊢
      WP (ProgramLogic.fill K (Exp.ofVal (Expr := Exp) hl_val(#l))) @ s ; E {{ Φ }}) :
    Δ ⊢ WP (ProgramLogic.fill K hl(ref(&v))) @ s ; E {{ Φ }} := by
  refine hlater.trans ?_
  refine .trans ?_ (wp_bind (ProgramLogic.fill K))
  refine .trans ?_ (wand_entails (wp_alloc v _))
  exact later_mono <| forall_intro fun l => wand_intro (hcont l)

public theorem tac_wp_free [ι : HeapLangGS hlc GF] {Δ Δ' Δ'' : IProp GF}
    {s : Stuckness} {E : CoPset} {K : List ECtxItem} {l : Loc} {v : Val} {Φ}
    (hlater : Δ ⊢ ▷ Δ')
    (hsplit : Δ' ⊣⊢ Δ'' ∗ (l ↦ some v))
    (hcont : Δ'' ⊢ WP (ProgramLogic.fill K (Exp.ofVal (Expr := Exp) hl_val(#()))) @ s ; E {{ Φ }}) :
    Δ ⊢ WP (ProgramLogic.fill K hl(free(#l))) @ s ; E {{ Φ }} :=
  tac_wp_heap_op rfl wp_free hlater hsplit (sep_elim_left.trans hcont)

public theorem tac_wp_load [ι : HeapLangGS hlc GF] {Δ Δ' Δ'' : IProp GF}
    {s : Stuckness} {E : CoPset} {K : List ECtxItem} {l : Loc} {q} {v : Val} {Φ}
    (hlater : Δ ⊢ ▷ Δ')
    (hsplit : Δ' ⊣⊢ Δ'' ∗ (l ↦{q} some v))
    (hcont : Δ' ⊢ WP (ProgramLogic.fill K (Exp.ofVal (Expr := Exp) v)) @ s ; E {{ Φ }}) :
    Δ ⊢ WP (ProgramLogic.fill K hl(!v(#l))) @ s ; E {{ Φ }} := by
  refine hlater.trans ?_
  refine .trans ?_ (wp_bind (ProgramLogic.fill K))
  iapply wand_apply (wand_entails (wp_load _))
  refine .trans ?_ later_sep.1
  refine later_mono ?_
  refine hsplit.1.trans ?_
  refine .trans sep_comm.mp ?_
  exact sep_mono .rfl (wand_intro (hsplit.2.trans hcont))

public theorem tac_wp_store [ι : HeapLangGS hlc GF] {Δ Δ' Δ'' : IProp GF}
    {s : Stuckness} {E : CoPset} {K : List ECtxItem} {l : Loc} {v v' : Val} {Φ}
    (hlater : Δ ⊢ ▷ Δ')
    (hsplit : Δ' ⊣⊢ Δ'' ∗ (l ↦ some v))
    (hcont : Δ'' ∗ (l ↦ some v') ⊢
      WP (ProgramLogic.fill K (Exp.ofVal (Expr := Exp) hl_val(#()))) @ s ; E {{ Φ }}) :
    Δ ⊢ WP (ProgramLogic.fill K hl(v(#l) ← &v')) @ s ; E {{ Φ }} := by
  refine hlater.trans ?_
  refine .trans ?_ (wp_bind (ProgramLogic.fill K))
  iapply wand_apply (wand_entails (wp_store _))
  refine .trans ?_ later_sep.1
  refine later_mono ?_
  refine hsplit.1.trans ?_
  refine .trans sep_comm.mp ?_
  exact sep_mono .rfl (wand_intro hcont)

public theorem tac_wp_xchg [ι : HeapLangGS hlc GF] {Δ Δ' Δ'' : IProp GF}
    {s : Stuckness} {E : CoPset} {K : List ECtxItem} {l : Loc} {v v' : Val} {Φ}
    (hlater : Δ ⊢ ▷ Δ')
    (hsplit : Δ' ⊣⊢ Δ'' ∗ (l ↦ some v))
    (hcont : Δ'' ∗ (l ↦ some v') ⊢
      WP (ProgramLogic.fill K (Exp.ofVal (Expr := Exp) v)) @ s ; E {{ Φ }}) :
    Δ ⊢ WP (ProgramLogic.fill K hl(xchg(#l, &v'))) @ s ; E {{ Φ }} :=
  tac_wp_heap_op rfl wp_xchg hlater hsplit hcont

public theorem tac_wp_cmpXchg_fail [ι : HeapLangGS hlc GF] {Δ Δ' Δ'' : IProp GF}
    {s : Stuckness} {E : CoPset} {K : List ECtxItem} {l : Loc} {q} {v v1 v2 : Val} {Φ}
    (hlater : Δ ⊢ ▷ Δ')
    (hsplit : Δ' ⊣⊢ Δ'' ∗ (l ↦{q} some v))
    (hne : v ≠ v1) (hsafe : v.compareSafe v1)
    (hcont : Δ' ⊢
      WP (ProgramLogic.fill K (Exp.ofVal (Expr := Exp) hl_val((&v, #false)))) @ s ; E {{ Φ }}) :
    Δ ⊢ WP (ProgramLogic.fill K hl(cmpXchg(v(#l), v(&v1), v(&v2)))) @ s ; E {{ Φ }} :=
  tac_wp_heap_op rfl (wp_cmpXchg_fail rfl rfl hsafe (decide_eq_false hne)) hlater hsplit
    (hsplit.2.trans hcont)

public theorem tac_wp_cmpXchg_suc [ι : HeapLangGS hlc GF] {Δ Δ' Δ'' : IProp GF}
    {s : Stuckness} {E : CoPset} {K : List ECtxItem} {l : Loc} {v v1 v2 : Val} {Φ}
    (hlater : Δ ⊢ ▷ Δ')
    (hsplit : Δ' ⊣⊢ Δ'' ∗ (l ↦ some v))
    (heq : v = v1) (hsafe : v.compareSafe v1)
    (hcont : Δ'' ∗ (l ↦ some v2) ⊢
      WP (ProgramLogic.fill K (Exp.ofVal (Expr := Exp) hl_val((&v, #true)))) @ s ; E {{ Φ }}) :
    Δ ⊢ WP (ProgramLogic.fill K hl(cmpXchg(v(#l), v(&v1), v(&v2)))) @ s ; E {{ Φ }} :=
  tac_wp_heap_op rfl (wp_cmpXchg_true rfl rfl hsafe (decide_eq_true heq)) hlater hsplit hcont

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
  else tac_wp_cmpXchg_fail hlater hsplit heq hsafe (hfail heq)

public theorem tac_wp_faa [ι : HeapLangGS hlc GF] {Δ Δ' Δ'' : IProp GF}
    {s : Stuckness} {E : CoPset} {K : List ECtxItem} {l : Loc} {z1 z2 : Int} {Φ}
    (hlater : Δ ⊢ ▷ Δ')
    (hsplit : Δ' ⊣⊢ Δ'' ∗ (l ↦ some hl_val(#z1)))
    (hcont : Δ'' ∗ (l ↦ some hl_val(#(z1 + z2))) ⊢
      WP (ProgramLogic.fill K (Exp.ofVal (Expr := Exp) hl_val(#z1))) @ s ; E {{ Φ }}) :
    Δ ⊢ WP (ProgramLogic.fill K hl(faa(#l, #z2))) @ s ; E {{ Φ }} :=
  tac_wp_heap_op rfl wp_faa hlater hsplit hcont

-- TODO: port `tac_wp_allocN` once `array` and `wp_allocN` are ported

/-! ## Shared machinery for the heap tactics -/

/-- Epilogue shared by the keep/consume heap tactics: fill the result value `r` back into
the evaluation context `K` and run `iWpFinish` over the continuation context `hyps`. Returns
the continuation proof typed against `fill K (Exp.ofVal r)`, so the caller's `assign` matches
the tac lemma's `hcont`. -/
meta def finishHeapOp {u} {GF : Q(BundledGFunctors.{0, 0, 0})} {hlc : Q(HasLC)}
    {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (ι : Q(IrisGS_gen $hlc Exp $GF))
    (s : Q(Stuckness)) (E : Q(CoPset)) (K : Q(List ECtxItem)) (r : Q(Val)) (Φ : Q(Val → $prop))
    (_hu : QuotedLevelDefEq u 0 := ⟨⟩) (_hprop : $prop =Q IProp $GF := ⟨⟩)
    (κ : Q(Wp $prop Exp Val Stuckness) := q(wp.def)) (_hwp : $κ =Q wp.def := ⟨⟩) :
    ProofModeM Q($ehyps ⊢ Wp.wp (self := $κ) $s $E (ProgramLogic.fill $K (Exp.ofVal $r)) $Φ) := do
  let ⟨inner, .up _⟩ ← HeapLang.fillQ K q(Exp.ofVal $r)
  iWpFinish hyps ι s E inner Φ (κ := κ)

/-- The points-to hypothesis located by `lookupPointsTo` for location `l`
in the (later-stripped) context `eΔ'`, together with the pruned context `eΔ''`/`hyps''` and
the splitting proof `pfSplit`, whose type is already recast to the `pointsTo` shape that the
`tac_wp_*` lemmas expect. -/
structure PointsToLookup {u : Level} {GF : Q(BundledGFunctors.{0, 0, 0})}
    {hlc : Q(HasLC)} (hgs : Q(HeapLangGS $hlc $GF)) {prop : Q(Type u)} (bi : Q(BI $prop))
    (eΔ' : Q($prop)) (l : Q(Loc)) (dq : Q(DFrac)) (hu : QuotedLevelDefEq u 0)
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
  pfSplit : Q($eΔ' ⊣⊢ $eΔ'' ∗ pointsTo $l $dq (some $v))

/-- Locate and remove a spatial hypothesis `l ↦{dq} some v`.
Reading operations pass a fresh metavariable, which the lookup assigns to whatever
fraction is found and the lemmas' `↦{q}` implicit then picks up.
Throws if no matching hypothesis exists. -/
meta def lookupPointsTo {u} {GF : Q(BundledGFunctors.{0, 0, 0})} {hlc : Q(HasLC)}
    {prop : Q(Type u)} {bi : Q(BI $prop)} {eΔ' : Q($prop)}
    (tacName : Name) (mvar : MVarId) (hgs : Q(HeapLangGS $hlc $GF))
    (hyps' : Hyps bi eΔ') (l : Q(Loc)) (dq : Q(DFrac))
    (hu : QuotedLevelDefEq u 0 := ⟨⟩)
    (hprop : $prop =Q IProp $GF := ⟨⟩) :
    ProofModeM (@PointsToLookup u GF hlc hgs prop bi eΔ' l dq hu hprop) := do
  let some ⟨⟨v, name, vid⟩, eΔ'', hyps'', _, _, _, _, pf⟩ ←
      hyps'.removeG false fun name vid p ty => do
        -- ignore intuitionistic hyps
        if isTrue p then return none
        have ty : Q(IProp $GF) := ty
        -- destructure ty to get the location l', fraction dq' and stored value v
        let ~q(pointsTo $l' $dq' (some $v)) := ty | return none
        unless ← isDefEq l' l do return none
        -- a literal `dq` rejects other fractions; a metavariable records the one found
        unless ← isDefEq dq' dq do return none
        return some ((v : Q(Val)), name, vid)
    | throwTacticEx tacName mvar (if dq.isMVar
        then m!"cannot find a points-to hypothesis for location {l}"
        else m!"cannot find a full-ownership points-to hypothesis for location {l}")
  trace[wp_heap.lookup] "found {name} : pointsTo {l} ({dq}) (some {v})"
  have pfSplit : Q($eΔ' ⊣⊢ $eΔ'' ∗ pointsTo $l $dq (some $v)) := pf
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
  hι : $ι =Q @HeapLang $hlc $GF $hgs

/-- Shared prologue for the heap tactics: run the tactic on a WP goal, check that it is a
HeapLang WP (from the `HeapLangGS` instance), and strip the WP's step modality
off the hypotheses. -/
meta def runTacticHeapWp {α} (tacName : Name)
    (k : MVarId → HeapWpGoal → ProofModeM α) : TacticM α := do
  -- Rocq parity: every heap tactic first normalizes pure redexes
  evalTactic (← `(tactic| wp_pures))
  ProofModeM.runTacticWp fun mvar {hyps, GF, hlc, ι, s, E, e, Φ, hu, hprop, hbi, ..} => do
    have ιQ : Q(IrisGS_gen $hlc Exp $GF) := ι
    let ~q(@HeapLang _ _ $hgs) := ιQ
      | throwTacticEx tacName mvar "the goal is not a HeapLang WP"
    trace[wp_heap] "{tacName}: e = {e}"
    -- currently specialized to later (no twp exists yet)
    let ⟨_, hyps', pfLater⟩ ← iModAction hyps q(modality_laterN 1)
    k mvar { hyps, ι, s, E, e, Φ, hu, hprop, hbi, hgs, hyps', pfLater, hι := ⟨⟩ }

/-! ## The heap tactics -/

elab "wp_load" : tactic =>
  runTacticHeapWp `wp_load fun mvar {ι, s, E, e, Φ, hgs, eΔ', hyps', pfLater, ..} => do
    let some {result := l, K, ..} ← findECtx e fun e' => do
        let ~q(Exp.load (Exp.ofVal (Val.lit (BaseLit.loc $l)))) := e' | failure
        return l
      | throwTacticEx `wp_load mvar "cannot find a `load` redex"
    trace[wp_heap.redex] "load {l}; K = {K}"

    -- find `l ↦{dq} some v` in the spatial context and extract `dq`
    let dq ← mkFreshExprMVarQ q(DFrac)
    let ⟨v, _, _, _, _, pfSplit⟩ ← lookupPointsTo `wp_load mvar hgs hyps' l dq

    -- fill the loaded value back into `K` and finish the continuation
    -- (over `hyps'`: the points-to hypothesis is kept)
    let pfCont ← finishHeapOp hyps' ι s E K v Φ

    mvar.assign q(tac_wp_load (ι := $hgs) (Δ' := $eΔ') $pfLater $pfSplit $pfCont)

elab "wp_store" : tactic =>
  runTacticHeapWp `wp_store fun mvar {bi, ι, s, E, e, Φ, hgs, eΔ', hyps', pfLater, ..} => do
    let some {result := (l, v'), K, ..} ← findECtx e fun e' => do
        let ~q(Exp.store (Exp.ofVal (Val.lit (BaseLit.loc $l))) (Exp.ofVal $v')) := e' | failure
        return (l, v')
      | throwTacticEx `wp_store mvar "cannot find a `store` redex"
    trace[wp_heap.redex] "store {l} ← {v'}; K = {K}"

    -- find and remove `l ↦ some v` (stores need full ownership)
    let ⟨_, name, vid, _, hyps'', pfSplit⟩ ←
      lookupPointsTo `wp_store mvar hgs hyps' l q(DFrac.own 1)

    let hyps''' := hyps''.add bi name vid q(false) q(pointsTo $l (DFrac.own 1) (some $v'))

    let pfCont ← finishHeapOp hyps''' ι s E K q(hl_val(#())) Φ

    mvar.assign q(tac_wp_store (ι := $hgs) (Δ' := $eΔ') $pfLater $pfSplit $pfCont)

elab "wp_xchg" : tactic =>
  runTacticHeapWp `wp_xchg fun mvar {bi, ι, s, E, e, Φ, hgs, eΔ', hyps', pfLater, ..} => do
    let some {result := (l, v'), K, ..} ← findECtx e fun e' => do
        let ~q(Exp.xchg (Exp.ofVal (Val.lit (BaseLit.loc $l))) (Exp.ofVal $v')) := e' | failure
        return (l, v')
      | throwTacticEx `wp_xchg mvar "cannot find an `xchg` redex"
    trace[wp_heap.redex] "xchg {l} ← {v'}; K = {K}"

    -- find and remove `l ↦ some v` (xchg writes, so it needs full ownership)
    let ⟨v, name, vid, _, hyps'', pfSplit⟩ ← lookupPointsTo `wp_xchg mvar hgs hyps' l q(DFrac.own 1)

    let hyps''' := hyps''.add bi name vid q(false) q(pointsTo $l (DFrac.own 1) (some $v'))

    let pfCont ← finishHeapOp hyps''' ι s E K v Φ

    mvar.assign q(tac_wp_xchg (ι := $hgs) (Δ' := $eΔ') $pfLater $pfSplit $pfCont)

elab "wp_faa" : tactic =>
  runTacticHeapWp `wp_faa fun mvar {bi, ι, s, E, e, Φ, hgs, eΔ', hyps', pfLater, ..} => do
    let some {result := (l, z2), K, ..} ← findECtx e fun e' => do
        -- faa is only defined on integers
        let ~q(Exp.faa (Exp.ofVal (Val.lit (BaseLit.loc $l)))
            (Exp.ofVal (Val.lit (BaseLit.int $z2)))) := e' | failure
        return (l, z2)
      | throwTacticEx `wp_faa mvar "cannot find a `faa` redex"
    trace[wp_heap.redex] "faa {l} += {z2}; K = {K}"

    -- find and remove `l ↦ some v` (faa writes, so it needs full ownership)
    let ⟨v, name, vid, eΔ'', hyps'', pfSplit⟩ ←
      lookupPointsTo `wp_faa mvar hgs hyps' l q(DFrac.own 1)

    -- check that the points-to value is an integer (FAA requirement)
    let ~q(Val.lit (BaseLit.int $z1)) := v
      | throwTacticEx `wp_faa mvar
          m!"the points-to hypothesis for location {l} does not store an integer"
    have pfSplit : Q($eΔ' ⊣⊢ $eΔ'' ∗
      pointsTo $l (DFrac.own 1) (some (Val.lit (BaseLit.int $z1)))) := pfSplit

    let hyps''' := hyps''.add bi name vid q(false)
      q(pointsTo $l (DFrac.own 1) (some (Val.lit (BaseLit.int ($z1 + $z2)))))

    let pfCont ← finishHeapOp hyps''' ι s E K q(Val.lit (BaseLit.int $z1)) Φ

    mvar.assign q(tac_wp_faa (ι := $hgs) (Δ' := $eΔ') $pfLater $pfSplit $pfCont)

elab "wp_cmpxchg_suc" : tactic =>
  runTacticHeapWp `wp_cmpxchg_suc fun mvar {bi, ι, s, E, e, Φ, hgs, eΔ', hyps', pfLater, ..} => do
    let some {result := (l, v1, v2), K, ..} ← findECtx e fun e' => do
        let ~q(Exp.cmpXchg (Exp.ofVal (Val.lit (BaseLit.loc $l)))
            (Exp.ofVal $v1) (Exp.ofVal $v2)) := e' | failure
        return (l, v1, v2)
      | throwTacticEx `wp_cmpxchg_suc mvar "cannot find a `cmpXchg` redex"
    trace[wp_heap.redex] "cmpXchg {l}: {v1} → {v2}; K = {K}"

    -- find and remove `l ↦ some v` (a successful cmpXchg writes, so full ownership)
    let ⟨v, name, vid, _, hyps'', pfSplit⟩ ←
      lookupPointsTo `wp_cmpxchg_suc mvar hgs hyps' l q(DFrac.own 1)

    -- check safety, don't throw hard error to match Rocq behavior
    let pfSafe ← iSolveSidecondition q(($v).compareSafe $v1 = true) (failOnUnsolved := false)

    -- check equality, don't throw hard error to match Rocq behavior
    let pfEq ← iSolveSidecondition q($v = $v1) (failOnUnsolved := false)

    let hyps''' := hyps''.add bi name vid q(false)
      q(pointsTo $l (DFrac.own 1) (some $v2))

    let pfCont ← finishHeapOp hyps''' ι s E K
      q(Val.pair $v (Val.lit (BaseLit.bool true))) Φ

    mvar.assign
      q(tac_wp_cmpXchg_suc (ι := $hgs) (Δ' := $eΔ') $pfLater $pfSplit $pfEq $pfSafe $pfCont)

elab "wp_cmpxchg_fail" : tactic =>
  runTacticHeapWp `wp_cmpxchg_fail fun mvar {ι, s, E, e, Φ, hgs, eΔ', hyps', pfLater, ..} => do
    let some {result := (l, v1, v2), K, ..} ← findECtx e fun e' => do
        let ~q(Exp.cmpXchg (Exp.ofVal (Val.lit (BaseLit.loc $l)))
            (Exp.ofVal $v1) (Exp.ofVal $v2)) := e' | failure
        return (l, v1, v2)
      | throwTacticEx `wp_cmpxchg_fail mvar "cannot find a `cmpXchg` redex"
    trace[wp_heap.redex] "cmpXchg {l}: {v1} → {v2}; K = {K}"

    -- any fraction suffices for a failing compare (the points-to is only read)
    let dq ← mkFreshExprMVarQ q(DFrac)
    let ⟨v, _, _, _, _, pfSplit⟩ ← lookupPointsTo `wp_cmpxchg_fail mvar hgs hyps' l dq

    -- check safety, don't throw hard error to match Rocq behavior
    let pfSafe ← iSolveSidecondition q(($v).compareSafe $v1 = true) (failOnUnsolved := false)

    -- check equality, don't throw hard error to match Rocq behavior
    let pfNeq ← iSolveSidecondition q($v ≠ $v1) (failOnUnsolved := false)

    let pfCont ← finishHeapOp hyps' ι s E K
      q(Val.pair $v (Val.lit (BaseLit.bool false))) Φ

    mvar.assign
      q(tac_wp_cmpXchg_fail (ι := $hgs) (Δ' := $eΔ') (v2 := $v2)
        $pfLater $pfSplit $pfNeq $pfSafe $pfCont)

elab "wp_cmpxchg" " as " h1:binderIdent " | " h2:binderIdent : tactic =>
  runTacticHeapWp `wp_cmpxchg fun mvar {bi, ι, s, E, e, Φ, hgs, eΔ', hyps', pfLater, ..} => do
    let some {result := (l, v1, v2), K, ..} ← findECtx e fun e' => do
        let ~q(Exp.cmpXchg (Exp.ofVal (Val.lit (BaseLit.loc $l)))
            (Exp.ofVal $v1) (Exp.ofVal $v2)) := e' | failure
        return (l, v1, v2)
      | throwTacticEx `wp_cmpxchg mvar "cannot find a `cmpXchg` redex"
    trace[wp_heap.redex] "cmpXchg {l}: {v1} → {v2}; K = {K}"

    -- find and remove `l ↦ some v` (the success branch writes, so full ownership)
    let ⟨v, name, vid, eΔ'', hyps'', pfSplit⟩ ←
      lookupPointsTo `wp_cmpxchg mvar hgs hyps' l q(DFrac.own 1)

    let hypsSuc := hyps''.add bi name vid q(false)
      q(pointsTo $l (DFrac.own 1) (some $v2))

    -- check safety, don't throw hard error to match Rocq behavior
    let pfSafe ← iSolveSidecondition q(($v).compareSafe $v1 = true) (failOnUnsolved := false)

    let (sucName, _) ← getFreshName h1
    let pfSuc : Q($v = $v1 → ($eΔ'' ∗ pointsTo $l (DFrac.own 1) (some $v2) ⊢
      Wp.wp $s $E (ProgramLogic.fill $K (Exp.ofVal (Expr := Exp)
      (Val.pair $v (Val.lit (BaseLit.bool true))))) $Φ)) ←
        Qq.withLocalDeclDQ sucName q($v = $v1) fun _h => do
          let ⟨innerSuc, .up _⟩ ← HeapLang.fillQ K
            q(Exp.ofVal (Val.pair $v (Val.lit (BaseLit.bool true))))
          let pf ← iWpFinish hypsSuc ι s E innerSuc Φ
          mkLambdaFVars #[_h] pf

    let (failName, _) ← getFreshName h2
    let pfFail : Q($v ≠ $v1 → $eΔ' ⊢
      Wp.wp $s $E (ProgramLogic.fill $K (Exp.ofVal (Expr := Exp)
      (Val.pair $v (Val.lit (BaseLit.bool false))))) $Φ) ←
        Qq.withLocalDeclDQ failName q($v ≠ $v1) fun _h => do
          let ⟨innerFail, .up _⟩ ← HeapLang.fillQ K
            q(Exp.ofVal (Val.pair $v (Val.lit (BaseLit.bool false))))
          let pf ← iWpFinish hyps' ι s E innerFail Φ
          mkLambdaFVars #[_h] pf

    mvar.assign
      q(tac_wp_cmpXchg (ι := $hgs) (Δ' := $eΔ') (v2 := $v2)
        $pfLater $pfSplit $pfSafe $pfSuc $pfFail)

elab "wp_free" : tactic =>
  runTacticHeapWp `wp_free fun mvar {ι, s, E, e, Φ, hgs, eΔ', hyps', pfLater, ..} => do
    let some {result := l, K, ..} ← findECtx e fun e' => do
        let ~q(Exp.free (Exp.ofVal (Val.lit (BaseLit.loc $l)))) := e' | failure
        return l
      | throwTacticEx `wp_free mvar "cannot find a `free` redex"
    trace[wp_heap.redex] "free {l}; K = {K}"

    -- find and remove `l ↦ some v` (freeing needs full ownership); the continuation
    -- runs over the pruned context `hyps''` since the points-to is consumed
    let ⟨_, _, _, _, hyps'', pfSplit⟩ ← lookupPointsTo `wp_free mvar hgs hyps' l q(DFrac.own 1)

    let pfCont ← finishHeapOp hyps'' ι s E K q(hl_val(#())) Φ

    mvar.assign q(tac_wp_free (ι := $hgs) (Δ' := $eΔ') $pfLater $pfSplit $pfCont)


elab "wp_alloc" ppSpace loc:binderIdent " as " hyp:binderIdent : tactic =>
  runTacticHeapWp `wp_alloc fun mvar {bi, ι, s, E, e, Φ, hgs, eΔ', hyps', pfLater, ..} => do
    let some {result := v, K, ..} ← findECtx e fun e' => do
        let ~q(Exp.allocN (Exp.ofVal (Val.lit (BaseLit.int 1)))
            (Exp.ofVal $v)) := e' | failure
        return v
      | throwTacticEx `wp_alloc mvar "cannot find a `ref` alloc"
    trace[wp_heap.redex] "ref {v}; K = {K}"

    -- get location name from tactic call
    let (locName, _) ← getFreshName loc

    let pfCont : Q(∀ l : Loc, $eΔ' ∗ pointsTo l (DFrac.own 1) (some $v) ⊢
        Wp.wp $s $E (ProgramLogic.fill $K (Exp.ofVal (Expr := Exp) (Val.lit (BaseLit.loc l)))) $Φ) ←
      Qq.withLocalDeclDQ locName q(Loc) fun l => do
        let ⟨_, hyps''⟩ ← hyps'.addWithInfo bi hyp q(false)
          q(pointsTo $l (DFrac.own 1) (some $v))

        let ⟨inner, .up _⟩ ← HeapLang.fillQ K q(Exp.ofVal (Val.lit (BaseLit.loc $l)))
        let pf ← iWpFinish hyps'' ι s E inner Φ
        mkLambdaFVars #[l] pf

    mvar.assign q(tac_wp_alloc (ι := $hgs) (Δ' := $eΔ') $pfLater $pfCont)

macro "wp_alloc" ppSpace loc:binderIdent : tactic => `(tactic| wp_alloc $loc as _)

-- Register the trace classes emitted by the tactics above; enables
-- `set_option trace.wp_bind true` (and analogously for the others).
initialize registerTraceClass `wp_bind
initialize registerTraceClass `wp_pure
initialize registerTraceClass `wp_heap
initialize registerTraceClass `wp_heap.redex (inherited := true)
initialize registerTraceClass `wp_heap.lookup (inherited := true)
