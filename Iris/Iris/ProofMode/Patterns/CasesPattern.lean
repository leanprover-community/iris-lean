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
syntax "%" noWs binderIdent : icasesPat
/-- Move the hypothesis to the intuitionistic context and destruct the proposition. -/
syntax "#" noWs icasesPat : icasesPat
/-- Move the hypothesis to the spatial context and destruct the proposition. -/
syntax "∗" noWs icasesPat : icasesPat
/-- Eliminate the modality at the top of the hypothesis and destruct the remaining proposition. -/
syntax ">" noWs icasesPat : icasesPat
/-- Introduce a pure equality and use it for rewriting in the backward direction. -/
syntax "←" : icasesPat
/-- Introduce a pure equality and use it for rewriting in the forward direction. -/
syntax "→" : icasesPat

inductive iCasesPat
  | one (ref : Syntax) (name : TSyntax ``binderIdent)
  | clear (ref : Syntax)
  | frame (ref : Syntax)
  | conjunction (ref : Syntax) (args : List iCasesPat)
  | disjunction (ref : Syntax) (args : List iCasesPat)
  | pure (ref : Syntax) (pat : TSyntax ``binderIdent)
  | intuitionistic (ref : Syntax) (pat : iCasesPat)
  | spatial (ref : Syntax) (pat : iCasesPat)
  | mod (ref : Syntax) (pat : iCasesPat)
  | rewrite (ref : Syntax) (forward : Bool)
  deriving Repr, Inhabited

def iCasesPat.ref : iCasesPat → Syntax
  | .one r _ | .clear r | .frame r | .conjunction r _ | .disjunction r _
  | .pure r _ | .intuitionistic r _ | .spatial r _ | .mod r _ | .rewrite r _ => r

partial def iCasesPat.parse (pat : TSyntax `icasesPat) : MacroM iCasesPat := do
  match go ⟨← expandMacros pat⟩ with
  | none => Macro.throwUnsupported
  | some pat => return pat
where
  go (stx : TSyntax `icasesPat) : Option iCasesPat :=
    let ref := stx.raw
    match ref with
    | `(icasesPat| $name:binderIdent) => some <| .one ref name
    | `(icasesPat| -) => some <| .clear ref
    | `(icasesPat| $) => some <| .frame ref
    | `(icasesPat| ⟨$[$args],*⟩) => args.mapM goAlts |>.map (.conjunction ref ·.toList)
    | `(icasesPat| %$pat:binderIdent) => some <| .pure ref pat
    | `(icasesPat| #$pat) => go pat |>.map <| .intuitionistic ref
    | `(icasesPat| ∗$pat) => go pat |>.map <| .spatial ref
    | `(icasesPat| >$pat) => go pat |>.map <| .mod ref
    | `(icasesPat| ($pat)) => goAlts pat
    | `(icasesPat| ←) => some <| .rewrite ref false
    | `(icasesPat| →) => some <| .rewrite ref true
    | _ => none
  goAlts (stx : TSyntax ``icasesPatAlts) : Option iCasesPat :=
    let ref := stx.raw
    match stx with
    | `(icasesPatAlts| $args|*) =>
      match args.getElems with
      | #[arg] => go arg
      | args   => args.mapM go |>.map (.disjunction ref ·.toList)
    | _ => none

end Iris.ProofMode
