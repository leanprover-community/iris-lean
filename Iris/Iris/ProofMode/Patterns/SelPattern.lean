/-
Copyright (c) 2026 Yunsong Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunsong Yang
-/
module

public meta import Iris.ProofMode.ProofModeM

@[expose] public section

namespace Iris.ProofMode
open Lean Meta Std

declare_syntax_cat selPat

syntax ident : selPat
syntax "%" : selPat
syntax "%" noWs ident : selPat
syntax "#" : selPat
syntax "∗" : selPat

inductive SelPat
  | pure
  | intuitionistic
  | spatial
  | ident (name : Ident)
  | leanIdent (name : Ident)
  deriving Repr, Inhabited

partial def SelPat.parseOne (pat : TSyntax `selPat) : MacroM SelPat := do
  match go ⟨← expandMacros pat⟩ with
  | none => Macro.throwUnsupported
  | some pat => return pat
where
  go : TSyntax `selPat → Option SelPat
  | `(selPat| %$name:ident) => some <| .leanIdent name
  | `(selPat| %) => some .pure
  | `(selPat| #) => some .intuitionistic
  | `(selPat| ∗) => some .spatial
  | `(selPat| $name:ident) => some <| .ident name
  | _ => none

partial def SelPat.parse (pats : TSyntaxArray `selPat) : MacroM (List SelPat) := do
  return (← pats.mapM SelPat.parseOne).toList

public meta section

abbrev SelTarget := Name ⊕ FVarId

/-- Resolve selection patterns to concrete proofmode hypotheses (`.inl`) and Lean locals (`.inr`). -/
def SelPat.resolveOne (hyps : Hyps bi e) : SelPat → ProofModeM (List SelTarget)
  | .ident name =>
      return [.inl (← hyps.findWithInfo name)]
  | .leanIdent name => do
      let ldecl ← getLocalDeclFromUserName name.getId
      return [.inr ldecl.fvarId]
  | .intuitionistic =>
      return hyps.intuitionisticUniqs.map .inl
  | .spatial =>
      return hyps.spatialUniqs.map .inl
  | .pure => do
      -- `%` selects user-facing Lean pure assumptions, so we keep only `Prop` hypotheses.
      let mut hyps := #[]
      for ldecl in ← getLCtx do
        if ldecl.isAuxDecl || ldecl.isImplementationDetail then
          continue
        if ! (← isProp ldecl.type) then
          continue
        hyps := hyps.push (.inr ldecl.fvarId)
      return hyps.toList

def SelPat.resolve (hyps : Hyps bi e) (pats : List SelPat) :
    ProofModeM (List SelTarget) := do
  return (← pats.flatMapM (SelPat.resolveOne hyps)).eraseDups

end

end Iris.ProofMode
