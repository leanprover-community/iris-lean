/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
namespace Iris.ProofMode
open Lean

declare_syntax_cat specPat

syntax ident : specPat
syntax "%" term : specPat
syntax "[" ident,* "]" optional(" as " ident) : specPat

-- see https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/proofmode/spec_patterns.v?ref_type=heads#L15
inductive SpecPat
  | ident (name : Ident)
  | pure (t : Term)
  | goal (names : List Ident) (goalName : Name)
  deriving Repr, Inhabited

partial def SpecPat.parse (pat : Syntax) : MacroM SpecPat := do
  match go ⟨← expandMacros pat⟩ with
  | none => Macro.throwUnsupported
  | some pat => return pat
where
  go : TSyntax `specPat → Option SpecPat
  | `(specPat| $name:ident) => some <| .ident name
  | `(specPat| % $term:term) => some <| .pure term
  | `(specPat| [$[$names:ident],*]) => some <| .goal names.toList .anonymous
  | `(specPat| [$[$names:ident],*] as $goal:ident) => match goal.raw with
    | .ident _ _ val _ => some <| .goal names.toList val
    | _ => none
  | _ => none
