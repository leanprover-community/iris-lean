/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/

module

import Lean
public import Iris.ProofMode

open Lean Elab Meta

namespace Iris.Tests

meta section

partial def collectTags {α} (t : Widget.TaggedText α)
    (acc : Array (String × α) := #[]) : Array (String × α) :=
  match t with
  | .text _    => acc
  | .append ts => ts.foldl (init := acc) fun acc t => collectTags t acc
  | .tag a t'  => collectTags t' (acc.push (t'.stripTags, a))

/-- Delaborators record their info as `ofDelabTermInfo`; hand-rolled
`Elab.withInfoContext'` sites record `ofTermInfo`. Accept either. -/
def asTermInfo? : Info → Option TermInfo
  | .ofTermInfo ti      => some ti
  | .ofDelabTermInfo ti => some ti.toTermInfo
  | _                   => none

/-- Report, for each hoverable region of the pretty-printed `e`,
the text and the type its popup would show. -/
def hoverReport (e : Expr) : MetaM MessageData := do
  let ⟨fmt, infos⟩ ← PrettyPrinter.ppExprWithInfos e
  let mut lines : Array MessageData := #[]
  for (txt, tag) in collectTags (Widget.TaggedText.prettyTagged fmt) do
    let some info := infos.get? tag.fst | continue
    let some ti := asTermInfo? info | continue
    let ty ← withLCtx ti.lctx (← getLocalInstances) do
      try ppExpr (← inferType ti.expr)
      catch _ => pure "<not typable>"
    lines := lines.push
      m!"⋆ {txt.trimAscii}{if ti.isBinder then " (binder)" else ""} : {ty}"
  return MessageData.joinSep lines.toList "\n"

elab "print_iris_delab" : tactic => do
  let g ← Tactic.getMainGoal
  g.withContext do logInfo (← hoverReport (← g.getType))

end

section

/--
info:
⋆ ∗HP1 : P
∗HP2 : P
∗HR : R
∗HPQ : P ∗ P -∗ R -∗ Q
⊢ Q : Prop
⋆ HP1 (binder) : P
⋆ P : PROP
⋆ HP2 (binder) : P
⋆ P : PROP
⋆ HR (binder) : R
⋆ R : PROP
⋆ HPQ (binder) : P ∗ P -∗ R -∗ Q
⋆ P ∗ P -∗ R -∗ Q : PROP
⋆ P : PROP
⋆ P : PROP
⋆ R : PROP
⋆ Q : PROP
⋆ Q : PROP
-/
#guard_msgs in
example [BI PROP] (P Q R : PROP) : P ⊢ P -∗ R -∗ (P ∗ P -∗ R -∗ Q) -∗ Q := by
  iintro HP1 HP2 HR HPQ
  print_iris_delab
  ispecialize HPQ $$ [$HP1 HP2] [-]
  . iexact HP2
  . iexact HR
  iexact HPQ

/--
info:
⋆ ∗HP1 : <absorb> P1
∗HP2 : <absorb> P2
∗HP3 : <absorb> <affine> P3
∗HP4 : <absorb> <affine> P4
∗H : <absorb> (P1 ∗ P2 ∗ <affine> (P3 ∗ P4)) -∗ Q
⊢ Q : Prop
⋆ HP1 (binder) : <absorb> P1
⋆ <absorb> P1 : PROP
⋆ P1 : PROP
⋆ HP2 (binder) : <absorb> P2
⋆ <absorb> P2 : PROP
⋆ P2 : PROP
⋆ HP3 (binder) : <absorb> <affine> P3
⋆ <absorb> <affine> P3 : PROP
⋆ P3 : PROP
⋆ HP4 (binder) : <absorb> <affine> P4
⋆ <absorb> <affine> P4 : PROP
⋆ P4 : PROP
⋆ H (binder) : <absorb> (P1 ∗ P2 ∗ <affine> (P3 ∗ P4)) -∗ Q
⋆ <absorb> (P1 ∗ P2 ∗ <affine> (P3 ∗ P4)) -∗ Q : PROP
⋆ (P1 ∗ P2 ∗ <affine> (P3 ∗ P4)) : PROP
⋆ P1 : PROP
⋆ P2 : PROP
⋆ (P3 ∗ P4) : PROP
⋆ P3 : PROP
⋆ P4 : PROP
⋆ Q : PROP
⋆ Q : PROP
-/
#guard_msgs in
example [BI PROP] {P1 P2 Q : PROP} :
    ⊢ <absorb> P1 -∗ <absorb> P2 -∗ <absorb> <affine> P3 -∗ <absorb> <affine> P4 -∗
      (<absorb> (P1 ∗ P2 ∗ <affine> (P3 ∗ P4)) -∗ Q) -∗ Q := by
  iintro HP1 HP2 HP3 HP4 H
  print_iris_delab
  icombine HP1 HP2 HP3 HP4 as HNew
  iapply H
  iexact HNew

end
