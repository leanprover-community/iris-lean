/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
namespace Iris.ProofMode
open Lean

declare_syntax_cat specPat

syntax binderIdent optional(str) : specPat
syntax "[" binderIdent,* "]" optional(str) : specPat

inductive SpecPat
  | idents (names : List (TSyntax ``binderIdent)) (goalName : Name)
  deriving Repr, Inhabited

partial def SpecPat.parse (pat : Syntax) : MacroM SpecPat := do
  match go ⟨← expandMacros pat⟩ with
  | none => Macro.throwUnsupported
  | some pat => return pat
where
  go : TSyntax `specPat → Option SpecPat
  | `(specPat| $name:binderIdent) => some <| .idents [name] .anonymous
  | `(specPat| $name:binderIdent $goal:str) => some <| .idents [name] (.mkSimple goal.getString)
  | `(specPat| [$[$names:binderIdent],*]) => some <| .idents names.toList .anonymous
  | `(specPat| [$[$names:binderIdent],*] $goal:str) => some <| .idents names.toList (.mkSimple goal.getString)
  | _ => none

def headName (spats : List SpecPat) : Name :=
  match spats.head? with
    | some <| .idents _ n => n
    | _ => .anonymous
