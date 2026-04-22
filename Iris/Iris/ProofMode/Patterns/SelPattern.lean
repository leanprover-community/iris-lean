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

structure SelTarget where
  target : Name ⊕ FVarId
  /- Was this target specified explicitly or is it from a glob like ∗? -/
  explicit : Bool

/-- Resolve selection patterns to concrete proofmode hypotheses (`.inl`) and Lean locals (`.inr`). -/
def SelPat.resolveOne (hyps : Hyps bi e) : SelPat → ProofModeM (List SelTarget)
  | .ident name =>
      return [⟨.inl (← hyps.findWithInfo name), true⟩]
  | .leanIdent name => do
      let ldecl ← getLocalDeclFromUserName name.getId
      return [⟨.inr ldecl.fvarId, true⟩]
  | .intuitionistic =>
      return hyps.intuitionisticUniqs.map (⟨.inl ·, false⟩)
  | .spatial =>
      return hyps.spatialUniqs.map (⟨.inl ·, false⟩)
  | .pure => do
      -- `%` selects user-facing Lean pure assumptions, so we keep only `Prop` hypotheses.
      let mut hyps := #[]
      for ldecl in ← getLCtx do
        if ldecl.isAuxDecl || ldecl.isImplementationDetail then
          continue
        if ! (← isProp ldecl.type) then
          continue
        hyps := hyps.push (⟨.inr ldecl.fvarId, false⟩)
      return hyps.toList

def SelPat.resolve (hyps : Hyps bi e) (pats : List SelPat) :
    ProofModeM (List SelTarget) := do
  -- we want to remove duplicates and if an pattern is first explicitly specified and then non-explicitly, we want to remove the non-explicit version (but not the other way around)
  return (← pats.flatMapM (SelPat.resolveOne hyps)).eraseDupsBy (λ snd fst => snd.target == fst.target && (fst.explicit == snd.explicit || fst.explicit))

end

end Iris.ProofMode
