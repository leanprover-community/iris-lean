/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Patterns.SpecPattern

namespace Iris.ProofMode
open Lean

declare_syntax_cat pmTerm

syntax term : pmTerm
syntax term "with" specPat,+ : pmTerm
syntax term "$!" term,+ : pmTerm
syntax term "$!" term,+ "with" specPat,+ : pmTerm

structure PMTerm where
  term : Term
  terms : List Term
  spats : List SpecPat
  deriving Repr, Inhabited

partial def PMTerm.parse (term : Syntax) : MacroM PMTerm := do
  match ← expandMacros term with
  | `(pmTerm| $trm:term) => return ⟨trm, [], []⟩
  | `(pmTerm| $trm:term with $spats,*) => return ⟨trm, [], ← parseSpats spats⟩
  | `(pmTerm| $trm:term $! $ts,*) => return ⟨trm, ts.getElems.toList, []⟩
  | `(pmTerm| $trm:term $! $ts,* with $spats,*) =>
    return ⟨trm, ts.getElems.toList, ← parseSpats spats⟩
  | _ => Macro.throwUnsupported
where
  parseSpats (spats : Syntax.TSepArray `specPat ",") : MacroM (List SpecPat) :=
      return (← spats.getElems.toList.mapM fun pat => SpecPat.parse pat.raw)
