/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Alvin Tang
-/
module

public meta import Iris.ProofMode.Tactics.Assumption
public meta import Iris.ProofMode.Tactics.Cases
public meta import Iris.ProofMode.Patterns.CasesPattern
public meta import Iris.ProofMode.Patterns.IntroPattern
public meta import Iris.ProofMode.Patterns.SelPattern
public meta import Iris.ProofMode.ClassesMake

namespace Iris.ProofMode

public meta section
open Lean Elab Tactic Meta Qq BI Std

@[rocq_alias tac_inv_elim]
theorem tac_inv_elim [BI PROP] {e goal : PROP} : e ⊢ goal := sorry

private def iInvCore {u} {prop : Q(Type u)} {bi e} (hyps : Hyps bi e) (goal : Q($prop))
    (ivar : IVarId) (selPats : Option <| List SelPat)
    (introPat : Syntax × IntroPat) (hclose : Option <| TSyntax `ident) :
    ProofModeM Q($e ⊢ $goal) := do
  -- Find the hypothesis from the context
  let some ⟨_, _, p, ty⟩ := hyps.getDecl? ivar
  | throwError m!"iinv: unable to find {ivar.name}"

  let ϕ ← mkFreshExprMVarQ q(Prop)
  let Pin ← mkFreshExprMVarQ q($prop)
  let X ← mkFreshExprMVarQ q(Type)
  let Pout ← mkFreshExprMVarQ q($X → $prop)
  let Pclose ← mkFreshExprMVarQ q($X → $prop)
  let Q' ← mkFreshExprMVarQ q($X → $prop)

  let some elimInv ← ProofModeM.trySynthInstanceQ q(ElimInv $ϕ $X $ty $Pin $Pout $Pclose $goal $Q')
  | throwError "iinv: ElimInv type class synthesis error"

  let hϕ ← iSolveSidecondition q($ϕ)

  let ⟨_, hyps', _, _, _, _, pf⟩ := hyps.remove false ivar

  let jvar ← mkFreshIVarId false
  let name ← mkFreshUserName .anonymous

  let hyps'' := hyps'.add bi name jvar q(false) ty

  let pf' ← addBIGoal hyps'' goal
  return q(tac_inv_elim)

/-- `iinv` opens an invariant in the proof state. -/
syntax (name := iinv) "iinv " colGt ident (" with " (colGt ppSpace selPat)*)?
    " as " colGt introPat (ident)? : tactic

elab_rules : tactic
  | `(tactic| iinv $h:ident $[with $spats:selPat*]? as $ipat:introPat $[$hclose:ident]?) => do
  -- Parse the optional selection pattern used for auxiliary assertions needed to open the invariant
  let selPats ← spats.mapM <| fun pats => do
    liftMacroM <| SelPat.parse pats
  -- Parse the introduction pattern used for destructing the result
  let introPat ← liftMacroM <| IntroPat.parse ipat

  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    -- Find the hypothesis in which the invariant is opened
    let ivar ← hyps.findWithInfo h

    let pf ← iInvCore hyps goal ivar selPats introPat hclose
    mvar.assign pf
