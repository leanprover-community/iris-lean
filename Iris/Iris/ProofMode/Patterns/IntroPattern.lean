/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Alvin Tang
-/
module

public import Iris.ProofMode.Patterns.CasesPattern
public import Iris.ProofMode.Patterns.SelPattern
meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris.ProofMode
open Lean

declare_syntax_cat selPatFrame
syntax ("!" noWs)? selPat : selPatFrame

declare_syntax_cat introPat

syntax icasesPat : introPat
syntax "!>" : introPat
syntax "//" : introPat
syntax "/=" : introPat
syntax "//=" : introPat
syntax "*" : introPat
syntax "**" : introPat
syntax "!%" : introPat
syntax "{" (colGt ppSpace selPatFrame)* ppSpace "}" : introPat

@[rocq_alias intro_pat]
inductive IntroPat
  | intro (case : iCasesPat)
  | trivial
  | modintro
  | simp
  | simptrivial
  | all
  | allwand
  | pureintro
  | clear (selPats : List <| Bool × SelPat)
  deriving Repr, Inhabited

partial def IntroPat.parse (term : Syntax) : MacroM (Syntax × IntroPat) := do
  match ← expandMacros term with
  | `(introPat| $case:icasesPat) => return (term, .intro (← iCasesPat.parse case))
  | `(introPat| //) => return (term, .trivial)
  | `(introPat| !>) => return (term, .modintro)
  | `(introPat| /=) => return (term, .simp)
  | `(introPat| //=) => return (term, .simptrivial)
  | `(introPat| *) => return (term, .all)
  | `(introPat| **) => return (term, .allwand)
  | `(introPat| !%) => return (term, .pureintro)
  | `(introPat| { $spats:selPatFrame* }) => return (term, .clear (← spats.toList.mapM parseSelPats))
  | _ => Macro.throwUnsupported
  where parseSelPats (spat : TSyntax `selPatFrame) : MacroM <| Bool × SelPat := do
    return ⟨!spat.raw[0].getArgs.isEmpty, ← SelPat.parseOne ⟨spat.raw[1]⟩⟩

#rocq_ignore gallina_ident "Not necessary in Lean"
#rocq_ignore intro_pat.big_conj "Not necessary in Lean"
#rocq_ignore intro_pat.close "Not necessary in Lean"
#rocq_ignore intro_pat.close_conj_list "Not necessary in Lean"
#rocq_ignore intro_pat.close_list "Not necessary in Lean"
#rocq_ignore intro_pat.parse "Not necessary in Lean"
#rocq_ignore intro_pat.parse_go "Not necessary in Lean"
#rocq_ignore intro_pat.stack_item "Not necessary in Lean"
