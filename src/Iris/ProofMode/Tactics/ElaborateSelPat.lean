/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.BI
import Iris.ProofMode.Expr
import Iris.ProofMode.Classes
import Iris.ProofMode.Tactics.Basic
import Iris.Std
import Lean.Elab
import Iris.ProofMode.Patterns.SelectPattern

namespace Iris.ProofMode
open Lean

open Lean Elab Tactic Meta Qq BI Std

inductive iElaboratedSelectPat
| pure
| ident (intuitionistic: Bool) (uniq : Name)

-- Ad-hoc NameSet
namespace iNameSet
/-- Lean.NameSet is based on red-black trees. Fine for smallish context. -/
private def Impl := Lean.NameSet
def Ty := Impl
def emp : Ty := NameSet.empty
def addUniq (set : Ty) (uniq:Name): MetaM Ty :=
    if set.contains uniq then throwError "duplicate hypothesis" else pure (set.insert uniq)
end iNameSet

variable {prop : Q(Type u)} (bi : Q(BI $prop)) in
def elaborateSelPatsCore {e} (hyps : Hyps bi e) (pat: iSelectPat) : MetaM (List iElaboratedSelectPat) := do
  let (_, epats) ← pat.foldrM (fun pat ⟨st, el⟩ => elaborateSelPat el st pat) (iNameSet.emp , [])
  pure (epats)
  where elaborateSelPat (el: List iElaboratedSelectPat) (set: iNameSet.Ty) (pata: iSelectPatAtom): MetaM (iNameSet.Ty × List iElaboratedSelectPat) :=
  match pata with
  | (iSelectPatAtom.intuitionistic) =>
      (hyps.findAll (fun _ p => isTrue p))
       |>.foldlM (fun ⟨s, l⟩ ⟨uniq,_,_⟩ => do
        let newSet ← iNameSet.addUniq s uniq
        pure (newSet, .ident true uniq:: l)) (set, el)
  | (iSelectPatAtom.spatial) =>
      (hyps.findAll (fun _ p => isTrue p |> not))
       |>.foldlM (fun ⟨s, l⟩ ⟨uniq,_,_⟩ => do
        let newSet ← iNameSet.addUniq s uniq
        pure (newSet, .ident false uniq:: l)) (set, el)
  | (iSelectPatAtom.one name) =>
        match hyps.find? (fun n _ => n == name) with
        | some (uniq, p, _) => do
            let newSet ← iNameSet.addUniq set uniq
            pure (newSet, (.ident (isTrue p) uniq) :: el)
        | none =>
            throwError "hypothesis not found: {name}"
  | iSelectPatAtom.pure =>
      pure (set, .pure :: el)
