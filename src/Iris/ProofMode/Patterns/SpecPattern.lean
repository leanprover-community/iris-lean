/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
namespace Iris.ProofMode
open Lean

declare_syntax_cat specPat

syntax binderIdent : specPat
syntax "[" binderIdent,* "]" optional(" as " ident) : specPat

inductive SpecPat
  | ident (name : TSyntax ``binderIdent)
  | idents (names : List (TSyntax ``binderIdent)) (goalName : Name)
  deriving Repr, Inhabited

partial def SpecPat.parse (pat : Syntax) : MacroM SpecPat := do
  match go ⟨← expandMacros pat⟩ with
  | none => Macro.throwUnsupported
  | some pat => return pat
where
  go : TSyntax `specPat → Option SpecPat
  | `(specPat| $name:binderIdent) => some <| .ident name
  | `(specPat| [$[$names:binderIdent],*]) => some <| .idents names.toList .anonymous
  | `(specPat| [$[$names:binderIdent],*] as $goal:ident) => match goal.raw with
    | .ident _ _ val _ => some <| .idents names.toList val
    | _ => none
  | _ => none

def headName (spats : List SpecPat) : Name :=
  match spats.head? with
    | some <| .ident _ => .anonymous
    | some <| .idents _ name => name
    | _ => .anonymous
