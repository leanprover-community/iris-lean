/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.ProofMode.Patterns.CasesPattern

namespace Iris.ProofMode
open Lean

declare_syntax_cat introPat

syntax icasesPat : introPat

inductive IntroPat
  | intro (case : iCasesPat)
  deriving Repr, Inhabited

partial def IntroPat.parse (term : Syntax) : MacroM (Syntax × IntroPat) := do
  match ← expandMacros term with
  | `(introPat| $case:icasesPat) => return (term, .intro (← iCasesPat.parse case))
  | _ => Macro.throwUnsupported
