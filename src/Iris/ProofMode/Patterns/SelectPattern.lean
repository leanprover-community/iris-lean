/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/

import Lean.Data.Name

namespace Iris.ProofMode
open Lean

declare_syntax_cat iselectPat
syntax iselectPatAlts := sepBy1(iselectPat, " ")
syntax binderIdent : iselectPat
-- syntax "-" : iselectPat
syntax "%" : iselectPat
syntax "#" : iselectPat
syntax "∗" : iselectPat

inductive iSelectPat
  | one (name : TSyntax ``binderIdent)
  | pure           (pat : iSelectPat)
  | intuitionistic (pat : iSelectPat)
  | spatial        (pat : iSelectPat)
  deriving Repr, Inhabited

partial def iSelectPat.parse (pat : TSyntax `iselectPat) : MacroM iSelectPat := do
  match go ⟨← expandMacros pat⟩ with
  | none => Macro.throwUnsupported
  | some pat => return pat
where
  go : TSyntax `iselectPat → Option iSelectPat
  | `(iselectPat| $name:binderIdent) =>  some <| .one name
  | `(iselectPat| %) => go pat |>.map .pure
  | `(iselectPat| #) => go pat |>.map .intuitionistic
  | `(iselectPat| ∗) => go pat |>.map .spatial
  | _ => none
  goAlts : TSyntax ``iselectPatAlts → Option (Array iSelectPat)
  | `(iselectPatAlts| $args*) =>
    match args.getElems with
    -- | #[arg] => go arg
    | args   => args.mapM go
  | _ => none

end Iris.ProofMode
