/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/

import Lean.Data.Name

namespace Iris.ProofMode
open Lean

declare_syntax_cat iselectPat
syntax binderIdent : iselectPat
syntax "%" : iselectPat
syntax "#" : iselectPat
syntax "*" : iselectPat

inductive iSelectPat
  | one (name : Name)
  | pure
  | intuitionistic
  | spatial
  deriving Repr, Inhabited

partial def iSelectPat.parse (pat : TSyntax `iselectPat) : MacroM (iSelectPat) := do
  match go ⟨← expandMacros pat⟩ with
  | none => Macro.throwUnsupported
  | some pat => return pat
where
  go : TSyntax `iselectPat → Option iSelectPat
  | `(iselectPat| $name:ident) =>  some <| .one (name.getId)
  | `(iselectPat| %) => some .pure
  | `(iselectPat| #) => some .intuitionistic
  | `(iselectPat| *) => some .spatial
  | _ => none

end Iris.ProofMode
