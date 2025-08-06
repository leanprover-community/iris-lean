/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/

import Lean.Data.Name

namespace Iris.ProofMode
open Lean

declare_syntax_cat iselectPatAtom
syntax binderIdent : iselectPatAtom
syntax "%" : iselectPatAtom
syntax "#" : iselectPatAtom
syntax "*" : iselectPatAtom

declare_syntax_cat iselectPat
syntax "[" (colGt iselectPatAtom)* "]": iselectPat

inductive iSelectPatAtom
  | one (name : Name)
  | pure
  | intuitionistic
  | spatial
  deriving Repr, Inhabited

def iSelectPat := Array iSelectPatAtom

partial def iSelectPatAtom.parse (pat : TSyntax `iselectPatAtom) : MacroM (iSelectPatAtom) := do
  match go ⟨← expandMacros pat⟩ with
  | none => Macro.throwUnsupported
  | some pat => return pat
where
  go : TSyntax `iselectPatAtom → Option iSelectPatAtom
  | `(iselectPatAtom| $name:ident) =>  some <| .one (name.getId)
  | `(iselectPatAtom| %) => some .pure
  | `(iselectPatAtom| #) => some .intuitionistic
  | `(iselectPatAtom| *) => some .spatial
  | _ => none

partial def iSelectPat.parse (pat : TSyntax `iselectPat) : MacroM (iSelectPat) := do
  match go ⟨← expandMacros pat⟩ with
  | none => Macro.throwUnsupported
  | some pat => return pat
where
  go : TSyntax `iselectPat → Option (iSelectPat)
  | `(iselectPat| [$atoms:iselectPatAtom*]) => atoms.mapM iSelectPatAtom.parse.go
  | _ => none

end Iris.ProofMode
