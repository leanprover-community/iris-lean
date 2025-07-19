/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
namespace Iris.ProofMode
open Lean

declare_syntax_cat specPat

syntax binderIdent : specPat
syntax "[" binderIdent,* "]" : specPat

inductive SpecPat
  | idents (names : List (TSyntax ``binderIdent))
  deriving Repr, Inhabited

partial def SpecPat.parse (pat : Syntax) : MacroM SpecPat := do
  match go ⟨← expandMacros pat⟩ with
  | none => Macro.throwUnsupported
  | some pat => return pat
where
  go : TSyntax `specPat → Option SpecPat
  | `(specPat| $name:binderIdent) => some <| .idents [name]
  | `(specPat| [$[$names:binderIdent],*]) => some <| .idents names.toList
  | _ => none
