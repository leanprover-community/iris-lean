/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Zongyuan Liu, Yunsong Yang, Michael Sammler, Alvin Tang
-/
module

public import Lean.Syntax
public meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris.ProofMode
open Lean

declare_syntax_cat frameIdent
syntax ident : frameIdent
-- We actually don't want to add the following since it would allow a space between $ and ident.
-- Instead we rely on the fact that Lean allows $x as an identifier, denoting an antiquotation
-- syntax "$" ident : frameIdent

declare_syntax_cat specPat

syntax ident : specPat
/-- Use a proof or a tactic sequence to match a pure hypothesis in the premise. -/
syntax "%" term:max : specPat
/--
  `[ H₁ … Hₙ ]` generates a subgoal for the premise with `H₁ … Hₙ` as the
  hypotheses chosen for the context of the subgoal. `[- H₁ … Hₙ ]` is analogous
  with all but `H₁ … Hₙ` as the chosen hypotheses. `[ H₁ … Hₙ ]` and
  `[- H₁ … Hₙ // ]` attempt to solve the subgoal using `itrivial`.
-/
syntax "[" ("-")? (colGt ppSpace frameIdent)* ("//")? ppSpace "]" (" as " colGt ident)? : specPat
/--
  `[> H₁ … Hₙ ]` generates a subgoal for the premise with `H₁ … Hₙ` as the
  hypotheses chosen for the context of the subgoal wrapped in a modality.
  `[> H₁ … Hₙ ]` is analogous with all but `H₁ … Hₙ` as the chosen hypotheses.
  `[ H₁ … Hₙ // ]` and `[> H₁ … Hₙ // ]` also attempt to solve the subgoal
  using `itrivial`.
-/
syntax "[>" ("-")? (colGt ppSpace frameIdent)* ("//")? ppSpace "]" (" as " colGt ident)? : specPat
/--
  `[# H₁ … Hₙ ]` generates a subgoal for the persistent premise
  with all hypotheses in the context available for the subgoal.
  `[# H₁ … Hₙ // ]` attempts to solve the subgoal using `itrivial`.
-/
syntax "[#" (colGt ppSpace frameIdent)* ("//")? ppSpace "]" (" as " colGt ident)? : specPat
/--
  `[$]` solves the subgoal by framing, first with spatial hypotheses, and
  then with intuitionistic hypotheses. Spatial hypotheses that are not framed
  are carried over to the subsequent goal.
-/
syntax "[" "$" "]" : specPat
/-- `[>$]` solves the subgoal by wrapping the premise with the modality and then by framing. -/
syntax "[>" "$" "]" : specPat
/-- `[#$]` solves the subgoal for the persistent premise by framing. -/
syntax "[#" "$" "]" : specPat

@[rocq_alias goal_kind]
inductive SpecGoalKind
  | spatial
  -- TODO: implement
  | modal
  -- TODO: implement
  | persistent
  deriving Repr, Inhabited, BEq

@[rocq_alias spec_goal]
structure SpecGoal where
  kind : SpecGoalKind
  trivial : Bool
  negate : Bool
  frame : List Ident
  hyps : List Ident
deriving Repr, Inhabited

-- see https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/proofmode/spec_patterns.v?ref_type=heads#L15
@[rocq_alias spec_pat]
inductive SpecPat
  | ident (name : Ident)
  | pure (t : Term)
  | goal (goal : SpecGoal) (goalName : Name)
  | autoframe (goal : SpecGoalKind)
  deriving Repr, Inhabited

@[rocq_alias goal_kind_modal]
def SpecGoalKind.isModal : SpecGoalKind → Bool
  | modal => true
  | _ => false

@[rocq_alias spec_pat_modal]
def SpecPat.isModal : SpecPat → Bool
  | .goal g _ => g.kind.isModal
  | .autoframe g => g.isModal
  | _ => false

#rocq_ignore spec_pat.stack_item "Not necessary in Lean"
#rocq_ignore spec_pat.parse_go "Not necessary in Lean"
#rocq_ignore spec_pat.close "Not necessary in Lean"
#rocq_ignore spec_pat.close_ident "Not necessary in Lean"

def FrameIdent.parse : TSyntax `frameIdent → (Ident ⊕ Ident)
  | `(frameIdent| $name:ident) => .inl name
  | e =>
    -- Antiquotations start with $, so if we find one, it is a framing assumption
    if e.raw.isAntiquot then
      .inr ⟨e.raw.getAntiquotTerm⟩
    else .inl default -- should not happen

@[rocq_alias spec_pat.parse]
def SpecPat.parse (pat : Syntax) : MacroM SpecPat := do
  match go ⟨← expandMacros pat⟩ with
  | none => Macro.throwUnsupported
  | some pat => return pat
where
  go : TSyntax `specPat → Option SpecPat
  | `(specPat| $name:ident) => some <| .ident name
  | `(specPat| % $term:term) => some <| .pure term
  | `(specPat| [$[-%$negTk]? $[$names:frameIdent]* $[//%$trivTk]?] $[as $goal:ident]?) =>
    let (hyps, frame) := names.toList.partitionMap FrameIdent.parse;
    some <| .goal {kind := .spatial, negate := negTk.isSome, trivial := trivTk.isSome, frame, hyps } <| (TSyntax.getId <*> goal).getD .anonymous
  | `(specPat| [> $[-%$negTk]? $[$names:frameIdent]* $[//%$trivTk]?] $[as $goal:ident]?) =>
    let (hyps, frame) := names.toList.partitionMap FrameIdent.parse;
    some <| .goal {kind := .modal, negate := negTk.isSome, trivial := trivTk.isSome, frame, hyps } <| (TSyntax.getId <*> goal).getD .anonymous
  | `(specPat| [# $[$names:frameIdent]* $[//%$trivTk]?] $[as $goal:ident]?) =>
    let (hyps, frame) := names.toList.partitionMap FrameIdent.parse;
    some <| .goal {kind := .persistent, negate := false, trivial := trivTk.isSome, frame, hyps } <| (TSyntax.getId <*> goal).getD .anonymous
  | `(specPat| [$]) => some <| .autoframe .spatial
  | `(specPat| [# $]) => some <| .autoframe .persistent
  | `(specPat| [> $]) => some <| .autoframe .modal
  | _ => none
