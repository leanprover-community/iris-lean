/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Patterns.SpecPattern

namespace Iris.ProofMode
open Lean

declare_syntax_cat pmTerm

syntax binderIdent : pmTerm
syntax binderIdent "with" specPat,+ : pmTerm

inductive PmTerm
  | pats (ident : TSyntax ``binderIdent) (spats : List Syntax)
  deriving Repr, Inhabited

partial def PmTerm.parse (term : Syntax) : MacroM PmTerm := do
  match go ⟨← expandMacros term⟩ with
  | none => Macro.throwUnsupported
  | some term => return term
where
  go : TSyntax `pmTerm → Option PmTerm
  | `(pmTerm| $name:binderIdent) => some <| .pats name []
  | `(pmTerm| $name:binderIdent with $spats,*) =>
    some <| .pats name spats.elemsAndSeps.toList
  | _ => none
