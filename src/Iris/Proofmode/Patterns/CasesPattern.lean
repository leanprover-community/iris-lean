/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Lean.Data.Name

namespace Iris.Proofmode
open Lean

declare_syntax_cat icasesPat
syntax icasesPatAlts := sepBy1(icasesPat, " | ")
syntax ident : icasesPat
syntax "_" : icasesPat
syntax "⟨" icasesPatAlts,* "⟩" : icasesPat
syntax "(" icasesPatAlts ")" : icasesPat
syntax "⌜" icasesPat "⌝" : icasesPat
syntax "□" icasesPat : icasesPat
syntax "-□" icasesPat : icasesPat

macro "%" pat:icasesPat : icasesPat => `(icasesPat| ⌜$pat⌝)
macro "#" pat:icasesPat : icasesPat => `(icasesPat| □ $pat)
macro "-#" pat:icasesPat : icasesPat => `(icasesPat| -□ $pat)

inductive iCasesPat
  | one (name : Name)
  | clear
  | conjunction (args : Array iCasesPat)
  | disjunction (args : Array iCasesPat)
  | pure           (pat : iCasesPat)
  | intuitionistic (pat : iCasesPat)
  | spatial        (pat : iCasesPat)
  deriving Repr, Inhabited

partial def iCasesPat.parse (pat : TSyntax `icasesPat) : MacroM <| Option iCasesPat := do
  let pat ← expandMacros pat
  return go <| TSyntax.mk pat
where
  go : TSyntax `icasesPat → Option iCasesPat
  | `(icasesPat| $name:ident) =>
    let name := name.getId
    if name.isAnonymous then
      none
    else
      some <| .one name
  | `(icasesPat| _) =>
    some <| .clear
  | `(icasesPat| ⟨$[$args],*⟩) =>
    args.sequenceMap goAlts |>.map .conjunction
  | `(icasesPat| ⌜$pat⌝) =>
    go pat |>.map .pure
  | `(icasesPat| □$pat) =>
    go pat |>.map .intuitionistic
  | `(icasesPat| -□$pat) =>
    go pat |>.map .spatial
  | `(icasesPat| ($pat)) =>
    goAlts pat
  | _ => none
  goAlts : TSyntax ``icasesPatAlts → Option iCasesPat
  | `(icasesPatAlts| $[$args]|*) =>
    match args with
    | #[arg] => go arg
    | args   => args.sequenceMap go |>.map .disjunction
  | _ => none

end Iris.Proofmode
