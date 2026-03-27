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

partial def SelPat.parse (pat : Syntax) : MacroM SelPat := do
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

public meta section

abbrev SelTarget := Name ⊕ FVarId

/-- Resolve selection patterns to concrete proofmode hypotheses (`.inl`) and Lean locals (`.inr`). -/
def resolveSelTargets (hyps : Hyps bi e) (pats : List SelPat) :
    ProofModeM (List SelTarget) := do
  let targetsRev ← pats.foldlM (init := []) fun acc pat => do
    match pat with
    | .ident name =>
        return .inl (← hyps.findWithInfo name) :: acc
    | .leanIdent name => do
        let ldecl ← getLocalDeclFromUserName name.getId
        return .inr ldecl.fvarId :: acc
    | .intuitionistic =>
        return hyps.allIntuitionistic.map .inl ++ acc
    | .spatial =>
        return hyps.allSpatial.map .inl ++ acc
    | .pure => do
        -- `%` selects user-facing Lean pure assumptions, so we keep only `Prop` hypotheses.
        let fvars ← (← getLCtx).foldlM (init := []) fun acc ldecl => do
          if ldecl.isAuxDecl || ldecl.isImplementationDetail then
            return acc
          if ← isProp ldecl.type then
            return ldecl.fvarId :: acc
          return acc
        return fvars.map .inr ++ acc
  return targetsRev.reverse.eraseDups

/-- Split elaborated selection targets into proofmode hypotheses and Lean locals, preserving order. -/
def splitSelTargets (targets : List SelTarget) : List Name × List FVarId :=
  targets.foldr (init := ([], [])) fun target (uniqs, fvars) =>
    match target with
    | .inl uniq => (uniq :: uniqs, fvars)
    | .inr fvar => (uniqs, fvar :: fvars)

end

end Iris.ProofMode
