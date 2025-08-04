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
syntax binderIdent "$!" ident,+ : pmTerm
syntax binderIdent "$!" ident,+ "with" specPat,+ : pmTerm

structure PMTerm where
  ident : Ident
  ts : List Ident
  spats : List SpecPat
  deriving Repr, Inhabited

partial def PMTerm.parse (term : Syntax) : MacroM PMTerm := do
  match ← expandMacros term with
  | `(pmTerm| $name:ident) => return ⟨name, [], []⟩
  | `(pmTerm| $name:ident with $spats,*) => return ⟨name, [], ← parseSpats spats⟩
  | `(pmTerm| $name:ident $! $ts,*) => return ⟨name, ts.getElems.toList, []⟩
  | `(pmTerm| $name:ident $! $ts,* with $spats,*) =>
    return ⟨name, ts.getElems.toList, ← parseSpats spats⟩
  | _ => Macro.throwUnsupported
where
  parseSpats (spats : Syntax.TSepArray `specPat ",") : MacroM (List SpecPat) :=
      return (← spats.getElems.toList.mapM fun pat => SpecPat.parse pat.raw)
