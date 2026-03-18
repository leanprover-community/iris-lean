/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
module

public import Iris.ProofMode.Patterns.CasesPattern

@[expose] public section

namespace Iris.ProofMode
open Lean

declare_syntax_cat introPat

syntax icasesPat : introPat
syntax "!>" : introPat

inductive IntroPat
  | intro (case : iCasesPat)
  | modintro
  deriving Repr, Inhabited

partial def IntroPat.parse (term : Syntax) : MacroM (Syntax × IntroPat) := do
  match ← expandMacros term with
  | `(introPat| $case:icasesPat) => return (term, .intro (← iCasesPat.parse case))
  | `(introPat| !>) => return (term, .modintro)
  | _ => Macro.throwUnsupported
