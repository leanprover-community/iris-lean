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

inductive iCasesPat
  | one (name : Name)
  | clear
  | conjunction (args : Array iCasesPat)
  | disjunction (args : Array iCasesPat)
  | pure           (pat : iCasesPat)
  | intuitionistic (pat : iCasesPat)
  | spatial        (pat : iCasesPat)
  deriving Repr, Inhabited

partial def iCasesPat.parse : TSyntax icasesPat → Option iCasesPat
  | `(icasesPat| $name:ident) =>
    let name := name.getId
    if name.isAnonymous then
      none
    else
      some <| .one name
  | `(icasesPat| _) =>
    some <| .clear
  | `(icasesPat| ⟨$[$args],*⟩) =>
    args.sequenceMap parse |>.map .conjunction
  | `(icasesPatAlts| $[$args]|*) =>
    match args with
    | #[arg] => parse arg
    | args   => args.sequenceMap parse |>.map .disjunction
  | `(icasesPat| ⌜$pat⌝) =>
    parse pat |>.map .pure
  | `(icasesPat| □$pat) =>
    parse pat |>.map .intuitionistic
  | `(icasesPat| -□$pat) =>
    parse pat |>.map .spatial
  | `(icasesPat| ($pat)) =>
    parse pat
  | _ => none

end Iris.Proofmode
