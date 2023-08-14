/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Lean.Data.Name

namespace Iris.ProofMode
open Lean

declare_syntax_cat icasesPat
syntax icasesPatAlts := sepBy1(icasesPat, " | ")
syntax binderIdent : icasesPat
syntax "-" : icasesPat
syntax "⟨" icasesPatAlts,* "⟩" : icasesPat
syntax "(" icasesPatAlts ")" : icasesPat
syntax "⌜" icasesPat "⌝" : icasesPat
syntax "□" icasesPat : icasesPat
syntax "∗" icasesPat : icasesPat

macro "%" pat:icasesPat : icasesPat => `(icasesPat| ⌜$pat⌝)
macro "#" pat:icasesPat : icasesPat => `(icasesPat| □ $pat)
macro "*" pat:icasesPat : icasesPat => `(icasesPat| ∗ $pat)

inductive iCasesPat
  | one (name : Option Name)
  | clear
  | conjunction (args : List iCasesPat)
  | disjunction (args : List iCasesPat)
  | pure           (pat : iCasesPat)
  | intuitionistic (pat : iCasesPat)
  | spatial        (pat : iCasesPat)
  deriving Repr, Inhabited

partial def iCasesPat.parse (pat : TSyntax `icasesPat) : MacroM iCasesPat := do
  match go ⟨← expandMacros pat⟩ with
  | none => Macro.throwUnsupported
  | some pat => return pat
where
  go : TSyntax `icasesPat → Option iCasesPat
  | `(icasesPat| $name:ident) =>
    let name := name.getId
    if name.isAnonymous then
      none
    else
      some <| .one name
  | `(icasesPat| _) => some <| .one none
  | `(icasesPat| -) => some <| .clear
  | `(icasesPat| ⟨$[$args],*⟩) => args.mapM goAlts |>.map (.conjunction ·.toList)
  | `(icasesPat| ⌜$pat⌝) => go pat |>.map .pure
  | `(icasesPat| □$pat) => go pat |>.map .intuitionistic
  | `(icasesPat| ∗$pat) => go pat |>.map .spatial
  | `(icasesPat| ($pat)) => goAlts pat
  | _ => none
  goAlts : TSyntax ``icasesPatAlts → Option iCasesPat
  | `(icasesPatAlts| $args|*) =>
    match args.getElems with
    | #[arg] => go arg
    | args   => args.mapM go |>.map (.disjunction ·.toList)
  | _ => none

end Iris.ProofMode
