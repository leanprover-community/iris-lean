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

@[rocq_alias tac_inv_elim]
theorem tac_inv_elim [BI PROP] {e e' goal : PROP} {ϕ : Prop} {X : Type} {p : Bool}
    {Pinv Pin : PROP} {mPclose : Option <| X → PROP} {Pout Q' : X → PROP}
    (inst : ElimInv ϕ X Pinv Pin Pout mPclose goal Q')
    (hϕ : ϕ)
    (hAcc : ∀ x, e' ⊢ Pout x -∗ Q' x)
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
    (introPat : Syntax × IntroPat) :
    -- (hclose : Option <| TSyntax `ident) :
    ProofModeM Q($e ⊢ $goal) := do
  -- Find the hypothesis from the context
  let ⟨e', hyps', _, Pinv, _, _ , pf⟩ := hyps.remove false ivar

  let ϕ ← mkFreshExprMVarQ q(Prop)
  let Pin ← mkFreshExprMVarQ q($prop)
  let X ← mkFreshExprMVarQ q(Type)
  let Pout ← mkFreshExprMVarQ q($X → $prop)
  let mPclose ← mkFreshExprMVarQ q(Option ($X → $prop))
  let Q' ← mkFreshExprMVarQ q($X → $prop)

  let X    : Q(Type)       ← instantiateMVars X
  let Pout : Q($X → $prop) ← instantiateMVars Pout
  let Q'   : Q($X → $prop) ← instantiateMVars Q'
  let mPclose : Q(Option ($X → $prop)) ← instantiateMVars mPclose

  let some inst ← ProofModeM.trySynthInstanceQ q(ElimInv $ϕ $X $Pinv $Pin $Pout $mPclose $goal $Q')
  | throwError "iinv: ElimInv type class synthesis error with goal {goal}"

  let hϕ ← iSolveSidecondition q($ϕ) false

  let hAcc : Q(∀ x, $e' ⊢ $Pout x -∗ $Q' x) ←
    withLocalDeclDQ (← mkFreshUserName `x) X fun x => do
      let poutX : Q($prop) := Expr.headBeta q($Pout $x)
      let qX : Q($prop) := Expr.headBeta q($Q' $x)
      let body ← iIntroCore hyps' q(iprop($poutX -∗ $qX)) [introPat]
      mkLambdaFVars #[x] body

  return q(tac_inv_elim $inst $hϕ $hAcc $pf)

elab "iinv " h:ident " as " ipat:introPat : tactic => do
  -- Parse the introduction pattern used for destructing the result
  let introPat ← liftMacroM <| IntroPat.parse ipat

  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    -- Find the hypothesis in which the invariant is opened
    let ivar ← hyps.findWithInfo h

    let pf ← iInvCore hyps goal ivar introPat
    mvar.assign pf

-- /-- `iinv` opens an invariant in the proof state. -/
-- syntax (name := iinv) "iinv " colGt ident (" with " (colGt ppSpace selPat)*)?
--     " as " colGt introPat (ident)? : tactic

-- elab_rules : tactic
--   | `(tactic| iinv $h:ident $[with $spats:selPat*]? as $ipat:introPat $[$hclose:ident]?) => do
--   -- Parse the optional selection pattern used for auxiliary assertions needed to open the invariant
--   let selPats ← spats.mapM <| fun pats => do
--     liftMacroM <| SelPat.parse pats
--   -- Parse the introduction pattern used for destructing the result
--   let introPat ← liftMacroM <| IntroPat.parse ipat

--   ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
--     -- Find the hypothesis in which the invariant is opened
--     let ivar ← hyps.findWithInfo h

--     let pf ← iInvCore hyps goal ivar selPats introPat hclose
--     mvar.assign pf
