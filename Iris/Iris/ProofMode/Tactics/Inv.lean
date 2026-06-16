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

private def iInvCore {u} {prop : Q(Type u)} {bi e} (hyps : Hyps bi e) (goal : Q($prop))
    (h : TSyntax `ident) (selPats : Option <| List SelPat)
    (introPat : Option <| Syntax × IntroPat)
    (hclose : Option <| TSyntax `ident) : ProofModeM Q($e ⊢ $goal) :=
  sorry

/-- `iinv` opens an invariant in the proof state. -/
syntax (name := iinv) "iinv " colGt ident (" with " (colGt ppSpace selPat)*)?
    " as " colGt introPat (ident)? : tactic

elab_rules : tactic
  | `(tactic| iinv $h:ident $[with $spats:selPat*]? as $ipat:introPat $[$hclose:ident]?) => do
  let selPats ← spats.mapM <| fun pats => do
    liftMacroM <| SelPat.parse pats
  let introPat ← liftMacroM <| IntroPat.parse ipat

  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    let pf ← iInvCore hyps goal h selPats introPat hclose
    mvar.assign pf
