/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Alvin Tang
-/
module

public meta import Iris.ProofMode.Tactics.Assumption
public meta import Iris.ProofMode.Tactics.Cases
public meta import Iris.ProofMode.Tactics.Intro
public meta import Iris.ProofMode.Patterns.CasesPattern
public meta import Iris.ProofMode.Patterns.IntroPattern
public meta import Iris.ProofMode.Patterns.SelPattern
public meta import Iris.ProofMode.ClassesMake

namespace Iris.ProofMode

public meta section
open Lean Elab Tactic Meta Qq BI Std

private def optionMap {PROP : Type u} {X : Type} (mP : Option (X → PROP)) (x : X) : Option PROP :=
  mP.map (· x)

@[rocq_alias tac_inv_elim]
theorem tac_inv_elim [BI PROP] {e e' goal : PROP} {ϕ : Prop} {X : Type} {p : Bool}
    {Pinv Pin : PROP} {mPclose : Option <| X → PROP} {Pout Q' : X → PROP}
    (inst : ElimInv ϕ X Pinv Pin Pout mPclose goal Q')
    (hϕ : ϕ)
    (hAcc : ∀ x, e' ⊢ Pout x -∗ mPclose.map (· x) -∗? Q' x)
    (pf : e ⊣⊢ e' ∗ □?p Pinv) :
    e ⊢ goal := by
  apply pf.mp.trans
  have h := inst.elim_inv hϕ
  clear inst hϕ pf
  cases mPclose with simp_all
  | none => sorry
  | some mPclose => sorry

private def iInvCore {u} {prop : Q(Type u)} {bi e} (hyps : Hyps bi e) (goal : Q($prop))
    (ivar : IVarId)
    -- (selPats : Option <| List SelPat)
    (introPat : Syntax × IntroPat)
    (hclose : Option <| TSyntax `ident) :
    ProofModeM Q($e ⊢ $goal) := do
  -- Find the hypothesis from the context
  let ⟨e', hyps', _, Pinv, _, _ , pfEq⟩ := hyps.remove false ivar

  let ϕ ← mkFreshExprMVarQ q(Prop)
  let Pin ← mkFreshExprMVarQ q($prop)
  let X ← mkFreshExprMVarQ q(Type)
  let Pout ← mkFreshExprMVarQ q($X → $prop)
  let mPclose ← mkFreshExprMVarQ q(Option ($X → $prop))
  let Q' ← mkFreshExprMVarQ q($X → $prop)
  let some inst ← ProofModeM.trySynthInstanceQ q(ElimInv $ϕ $X $Pinv $Pin $Pout $mPclose $goal $Q')
  | throwError "iinv: invalid invariant {Pinv}"

  -- Solve side conditions automatically if possible, otherwise add them into the proof state
  let hϕ ← iSolveSidecondition q($ϕ) false

  -- Create an introduction pattern for `hclose`
  let hClosePat ← match hclose with
  | none => pure none
  | some hclose => pure <| some (hclose.raw, IntroPat.intro (.one (← `(binderIdent| $hclose:ident))))

  -- Create the wand proposition and apply the introduction pattern to destruct the premise
  let hAcc : Q(∀ x : $X, $e' ⊢ $Pout x -∗ BIBase.wandM (optionMap $mPclose x) ($Q' x)) ←
    withLocalDeclDQ (u := 0) (← mkFreshUserName `x) X fun x => do
      let poutX : Q($prop) := Expr.headBeta q($Pout $x)
      let qX : Q($prop) := Expr.headBeta q($Q' $x)
      let body ← match mPclose with
      | ~q(none) =>
        iIntroCore hyps' q(iprop($poutX -∗ $qX)) [introPat]
      | ~q(some $f) =>
        match hClosePat with
        | some closePat =>
          let closeX : Q($prop) := Expr.headBeta q(optionMap $mPclose $x)
          iIntroCore hyps' q(iprop($poutX -∗ $closeX -∗ $qX)) [introPat, closePat]
        -- Throw an error if `hclose` is not given, but `mPclose` is not `none`
        | none => throwError "iinv: error"
      mkLambdaFVars #[x] body

  return q(tac_inv_elim $inst $hϕ $hAcc $pfEq)

/-- `iinv` opens an invariant in the proof state. -/
syntax (name := iinv) "iinv " colGt ident (" with " (colGt ppSpace selPat)*)?
    " as " colGt introPat (ident)? : tactic

elab_rules : tactic
  | `(tactic| iinv $h:ident as $ipat:introPat $[$hclose:ident]?) => do
    -- Parse the introduction pattern used for destructing the result
    let introPat ← liftMacroM <| IntroPat.parse ipat

    ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
      -- Find the hypothesis in which the invariant is opened
      let ivar ← hyps.findWithInfo h

      let pf ← iInvCore hyps goal ivar introPat hclose
      mvar.assign pf
