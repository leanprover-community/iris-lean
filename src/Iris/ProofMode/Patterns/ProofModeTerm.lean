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
syntax binderIdent "$!" binderIdent,+ : pmTerm
syntax binderIdent "$!" binderIdent,+ "with" specPat,+ : pmTerm

structure PMTerm where
  ident : TSyntax ``binderIdent
  ts : List (TSyntax ``binderIdent)
  spats : List SpecPat
  deriving Repr, Inhabited

partial def PMTerm.parse (term : Syntax) : MacroM PMTerm := do
  match ← expandMacros term with
  | `(pmTerm| $name:binderIdent) => pmt name ⟨#[]⟩ ⟨#[]⟩
  | `(pmTerm| $name:binderIdent with $spats,*) => pmt name ⟨#[]⟩ spats
  | `(pmTerm| $name:binderIdent $! $ts:binderIdent,*) => pmt name ts ⟨#[]⟩
  | `(pmTerm| $name:binderIdent $! $ts:binderIdent,* with $spats,*) => pmt name ts spats
  | _ => Macro.throwUnsupported
where
  pmt name ts spats : MacroM PMTerm := return ⟨name, ts.getElems.toList,
      (← spats.elemsAndSeps.toList.mapM fun pat => SpecPat.parse pat)⟩
