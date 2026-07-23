/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Alvin Tang
-/
module

public import Lean.Data.Name

@[expose] public section

namespace Iris.ProofMode
open Lean

declare_syntax_cat icasesPat
syntax icasesPatAlts := sepBy1(icasesPat, " | ")
syntax binderIdent : icasesPat
/-- Drop the hypothesis. -/
syntax "-" : icasesPat
/-- Frame the hypothesis and cancel it against the goal. -/
syntax "$" : icasesPat
/--
  Destruct a (separating) conjunction or existential; an existential variable is
  bound with `%x` where `x` is the name for it.
-/
syntax "⟨" icasesPatAlts,* "⟩" : icasesPat
/-- Destruct a disjunction, one goal per disjunct. -/
syntax "(" icasesPatAlts ")" : icasesPat
/-- Move the hypothesis to the pure Lean context and give it a name. -/
syntax "%" rcasesPat : icasesPat
/-- Move the hypothesis to the intuitionistic context and destruct the proposition. -/
syntax "#" icasesPat : icasesPat
/-- Move the hypothesis to the spatial context and destruct the proposition. -/
syntax "∗" icasesPat : icasesPat
/-- Eliminate the modality at the top of the hypothesis and destruct the remaining proposition. -/
syntax ">" icasesPat : icasesPat
/-- Introduce a pure equality and use it for rewriting in the backward direction. -/
syntax "←" : icasesPat
/-- Introduce a pure equality and use it for rewriting in the forward direction. -/
syntax "→" : icasesPat

inductive iCasesPatCase
  | one (name : TSyntax ``binderIdent)
  | clear
  | frame
  | conjunction (args : List iCasesPatCase)
  | disjunction (args : List iCasesPatCase)
  | pure (pat : TSyntax `rcasesPat)
  | intuitionistic (pat : iCasesPatCase)
  | spatial (pat : iCasesPatCase)
  | mod (pat : iCasesPatCase)
  | rewrite (forward : Bool)
  deriving Repr, Inhabited

structure iCasesPat where
  ref : Syntax
  case : iCasesPatCase

partial def iCasesPat.parse (pat : TSyntax `icasesPat) : MacroM iCasesPat := do
  let stx ← expandMacros pat
  match go ⟨stx⟩ with
  | none => Macro.throwUnsupported
  | some pat => return { ref := stx, case := pat }
where
  go (stx : TSyntax `icasesPat) : Option iCasesPatCase :=
    match stx.raw with
    | `(icasesPat| $name:binderIdent) => some <| .one name
    | `(icasesPat| -) => some <| .clear
    | `(icasesPat| $) => some <| .frame
    | `(icasesPat| ⟨$[$args],*⟩) => args.mapM goAlts |>.map (.conjunction <| ·.toList)
    | `(icasesPat| %$pat:rcasesPat) => some <| .pure pat
    | `(icasesPat| #$pat) => go pat |>.map <| .intuitionistic
    | `(icasesPat| ∗$pat) => go pat |>.map <| .spatial
    | `(icasesPat| >$pat) => go pat |>.map <| .mod
    | `(icasesPat| ($pat)) => goAlts pat
    | `(icasesPat| ←) => some <| .rewrite false
    | `(icasesPat| →) => some <| .rewrite true
    | _ => none
  goAlts (stx : TSyntax ``icasesPatAlts) : Option iCasesPatCase :=
    match stx with
    | `(icasesPatAlts| $args|*) =>
      match args.getElems with
      | #[arg] => go arg
      | args   => args.mapM go |>.map (.disjunction ·.toList)
    | _ => none

end Iris.ProofMode
