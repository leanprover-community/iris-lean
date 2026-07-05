/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Zongyuan Liu
-/
module

public import Iris.ProofMode.Patterns.SpecPattern
meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris.ProofMode
open Lean

declare_syntax_cat pmTerm
/--
  The proof mode term `H $$ spat₁ … spatₙ` refers to `H`, a hypothesis or a
  Lean term whose conclusion is an entailment, with the specialisation patterns
  `spat₁ … spatₙ` applied to its premises.
-/
syntax term (colGt " $$ " (colGt ppSpace specPat)+)? : pmTerm

@[rocq_alias iTrm]
structure PMTerm where
  term : Term
  spats : List (Syntax × SpecPat)
  deriving Repr, Inhabited

partial def PMTerm.parse (term : Syntax) : MacroM PMTerm := do
  match ← expandMacros term with
  | `(pmTerm| $trm:term) => return ⟨trm, []⟩
  | `(pmTerm| $trm:term $$ $[$spats:specPat]*) => return ⟨trm, ← parseSpats spats⟩
  | _ => Macro.throwUnsupported
where
  parseSpats (spats : TSyntaxArray `specPat) : MacroM (List (Syntax × SpecPat)) :=
      return (← spats.toList.mapM fun pat => SpecPat.parse pat.raw)

def PMTerm.is_nontrivial (pmt : PMTerm) : Bool := !pmt.spats.isEmpty
