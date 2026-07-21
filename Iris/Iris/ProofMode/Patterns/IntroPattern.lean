/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Alvin Tang
-/
module

public import Iris.ProofMode.Patterns.CasesPattern
public import Iris.ProofMode.Patterns.SelPattern
meta import Iris.Std.RocqPorting
public import Lean.Syntax

@[expose] public section

namespace Iris.ProofMode
open Lean

declare_syntax_cat selPatFrame
syntax selPat : selPatFrame
syntax "$%" : selPatFrame
syntax "$%" noWs ident : selPatFrame
syntax "$#" : selPatFrame
syntax "$∗" : selPatFrame

declare_syntax_cat introPat

syntax icasesPat : introPat
/-- Introduce a modality, analogous to applying `imodintro`. -/
syntax "!>" : introPat
/-- Try to solve the goal using `itrivial`. -/
syntax "//" : introPat
/-- Apply simplification. -/
syntax "/=" : introPat
/-- Apply simplifcation (`/=`) and try solving the goal (`//`). -/
syntax "//=" : introPat
/-- Introduce all universal quantifiers. -/
syntax "*" : introPat
/-- Introduce all universal quantifiers, pure arrows and wands. -/
syntax "**" : introPat
/-- Introduces a pure proof goal, analogous to applying `ipureintro`. -/
syntax "!%" : introPat
/--
  Given selection patterns `spats`, the introduction pattern `{ spats }`
  *clears* the hypotheses chosen by `spats`. Prefix an element in the selection
  patterns with `!` to *frame* the hypotheses instead.
-/
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
    if spat.raw.isAntiquot then
      return ⟨true, .ident ⟨spat.raw.getAntiquotTerm⟩⟩
    else
      match spat with
      | `(selPatFrame| $spat:selPat) => return ⟨false, ← SelPat.parseOne spat⟩
      | `(selPatFrame| $%$name:ident) => return ⟨true, .leanIdent name⟩
      | `(selPatFrame| $%) => return ⟨true, .pure⟩
      | `(selPatFrame| $#) => return ⟨true, .intuitionistic⟩
      | `(selPatFrame| $∗) => return ⟨true, .spatial⟩
      | _ => Macro.throwUnsupported

#rocq_ignore gallina_ident "Not necessary in Lean"
#rocq_ignore intro_pat.big_conj "Not necessary in Lean"
#rocq_ignore intro_pat.close "Not necessary in Lean"
#rocq_ignore intro_pat.close_conj_list "Not necessary in Lean"
#rocq_ignore intro_pat.close_list "Not necessary in Lean"
#rocq_ignore intro_pat.parse "Not necessary in Lean"
#rocq_ignore intro_pat.parse_go "Not necessary in Lean"
#rocq_ignore intro_pat.stack_item "Not necessary in Lean"
