/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
module

public import Iris.ProofMode.Patterns.CasesPattern
meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris.ProofMode
open Lean

declare_syntax_cat introPat

syntax icasesPat : introPat
syntax "!>" : introPat
syntax "//" : introPat

@[rocq_alias intro_pat]
inductive IntroPat
  | intro (case : iCasesPat)
  | trivial
  | modintro
  deriving Repr, Inhabited

partial def IntroPat.parse (term : Syntax) : MacroM (Syntax × IntroPat) := do
  match ← expandMacros term with
  | `(introPat| $case:icasesPat) => return (term, .intro (← iCasesPat.parse case))
  | `(introPat| //) => return (term, .trivial)
  | `(introPat| !>) => return (term, .modintro)
  | _ => Macro.throwUnsupported

#rocq_ignore gallina_ident "Not necessary in Lean"
#rocq_ignore intro_pat.big_conj "Not necessary in Lean"
#rocq_ignore intro_pat.close "Not necessary in Lean"
#rocq_ignore intro_pat.close_conj_list "Not necessary in Lean"
#rocq_ignore intro_pat.close_list "Not necessary in Lean"
#rocq_ignore intro_pat.parse "Not necessary in Lean"
#rocq_ignore intro_pat.parse_go "Not necessary in Lean"
#rocq_ignore intro_pat.stack_item "Not necessary in Lean"
