/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Zongyuan Liu, Yunsong Yang, Michael Sammler
-/
module

public import Lean.Syntax
meta import Iris.Std.RocqPorting

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
syntax "%" term:max : specPat
syntax "[" frameIdent* "]" optional(" as " ident) : specPat
syntax "[" "-" frameIdent* "]" optional(" as " ident) : specPat
syntax "[>" frameIdent* "]" optional(" as " ident) : specPat
syntax "[>" "-" frameIdent* "]" optional(" as " ident) : specPat
syntax "[#" frameIdent* "]" optional(" as " ident) : specPat
syntax "[" "$" "]" : specPat
syntax "[#" "$" "]" : specPat

@[rocq_alias goal_kind]
inductive SpecGoalKind
  | spatial
  -- TODO: implement
  | modal
  -- TODO: implement
  | intuitionistic
  deriving Repr, Inhabited, BEq

@[rocq_alias spec_goal]
structure SpecGoal where
  kind : SpecGoalKind
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

#rocq_ignore spec_pat.stack_item "Not necessary in Lean"
#rocq_ignore spec_pat.parse_go "Not necessary in Lean"
#rocq_ignore spec_pat.close "Not necessary in Lean"
#rocq_ignore spec_pat.close_ident "Not necessary in Lean"

partial def FrameIdent.parse : TSyntax `frameIdent → (Ident ⊕ Ident)
  | `(frameIdent| $name:ident) => .inl name
  | e =>
    -- Antiquotations start with $, so if we find one, it is a framing assumption
    if e.raw.isAntiquot then
      .inr ⟨e.raw.getAntiquotTerm⟩
    else .inl default -- should not happen

@[rocq_alias spec_pat.parse]
partial def SpecPat.parse (pat : Syntax) : MacroM SpecPat := do
  match go ⟨← expandMacros pat⟩ with
  | none => Macro.throwUnsupported
  | some pat => return pat
where
  go : TSyntax `specPat → Option SpecPat
  | `(specPat| $name:ident) => some <| .ident name
  | `(specPat| % $term:term) => some <| .pure term
  | `(specPat| [$[$names:frameIdent]*]) =>
    let (hyps, frame) := names.toList.partitionMap FrameIdent.parse;
    some <| .goal {kind := .spatial, negate := false, frame, hyps } .anonymous
  | `(specPat| [$[$names:frameIdent]*] as $goal:ident) =>
    let (hyps, frame) := names.toList.partitionMap FrameIdent.parse;
    some <| .goal {kind := .spatial, negate := false, frame, hyps } goal.getId
  | `(specPat| [- $[$names:frameIdent]*]) =>
    let (hyps, frame) := names.toList.partitionMap FrameIdent.parse;
    some <| .goal {kind := .spatial, negate := true, frame, hyps } .anonymous
  | `(specPat| [- $[$names:frameIdent]*] as $goal:ident) =>
    let (hyps, frame) := names.toList.partitionMap FrameIdent.parse;
    some <| .goal {kind := .spatial, negate := true, frame, hyps } goal.getId
  | `(specPat| [> $[$names:frameIdent]*]) =>
    let (hyps, frame) := names.toList.partitionMap FrameIdent.parse;
    some <| .goal {kind := .modal, negate := false, frame, hyps } .anonymous
  | `(specPat| [> $[$names:frameIdent]*] as $goal:ident) =>
    let (hyps, frame) := names.toList.partitionMap FrameIdent.parse;
    some <| .goal {kind := .modal, negate := false, frame, hyps } goal.getId
  | `(specPat| [> - $[$names:frameIdent]*]) =>
    let (hyps, frame) := names.toList.partitionMap FrameIdent.parse;
    some <| .goal {kind := .modal, negate := true, frame, hyps } .anonymous
  | `(specPat| [> - $[$names:frameIdent]*] as $goal:ident) =>
    let (hyps, frame) := names.toList.partitionMap FrameIdent.parse;
    some <| .goal {kind := .modal, negate := true, frame, hyps } goal.getId
  | `(specPat| [# $[$names:frameIdent]*]) =>
    let (hyps, frame) := names.toList.partitionMap FrameIdent.parse;
    some <| .goal {kind := .intuitionistic, negate := false, frame, hyps } .anonymous
  | `(specPat| [# $[$names:frameIdent]*] as $goal:ident) =>
    let (hyps, frame) := names.toList.partitionMap FrameIdent.parse;
    some <| .goal {kind := .intuitionistic, negate := false, frame, hyps } goal.getId
  | `(specPat| [$]) => some <| .autoframe .spatial
  | `(specPat| [# $]) => some <| .autoframe .intuitionistic
  | _ => none
