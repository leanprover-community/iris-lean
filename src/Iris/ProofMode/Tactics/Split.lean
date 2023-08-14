/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.ProofMode.Tactics.Basic
import Iris.ProofMode.Tactics.Remove

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI

theorem from_and_intro [BI PROP] {P Q A1 A2 : PROP} [inst : FromAnd Q A1 A2]
    (h1 : P ⊢ A1) (h2 : P ⊢ A2) : P ⊢ Q :=
  (and_intro h1 h2).trans inst.1

elab "isplit" : tactic => do
  let (mvar, { prop, bi, e, hyps, goal }) ← istart (← getMainGoal)
  mvar.withContext do

  let A1 ← mkFreshExprMVarQ prop
  let A2 ← mkFreshExprMVarQ prop
  let _ ← synthInstanceQ q(FromAnd $goal $A1 $A2)
  let m1 : Q($e ⊢ $A1) ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { prop, bi, hyps, goal := A1 }
  let m2 : Q($e ⊢ $A2) ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { prop, bi, hyps, goal := A2 }
  mvar.assign q(from_and_intro (Q := $goal) $m1 $m2)
  replaceMainGoal [m1.mvarId!, m2.mvarId!]


theorem split_es [BI PROP] {Q Q1 Q2 : PROP} (h : Q ⊣⊢ Q1 ∗ Q2) : emp ∗ Q ⊣⊢ Q1 ∗ Q2 :=
  emp_sep.trans h
theorem split_ls [BI PROP] {P Q Q1 Q2 : PROP} (h : Q ⊣⊢ Q1 ∗ Q2) : P ∗ Q ⊣⊢ (P ∗ Q1) ∗ Q2 :=
  (sep_congr_r h).trans sep_assoc.symm
theorem split_rs [BI PROP] {P Q Q1 Q2 : PROP} (h : Q ⊣⊢ Q1 ∗ Q2) : P ∗ Q ⊣⊢ Q1 ∗ (P ∗ Q2) :=
  (sep_congr_r h).trans sep_left_comm
theorem split_se [BI PROP] {P P1 P2 : PROP} (h : P ⊣⊢ P1 ∗ P2) : P ∗ emp ⊣⊢ P1 ∗ P2 :=
  sep_emp.trans h
theorem split_sl [BI PROP] {P Q P1 P2 : PROP} (h : P ⊣⊢ P1 ∗ P2) : P ∗ Q ⊣⊢ (P1 ∗ Q) ∗ P2 :=
  (sep_congr_l h).trans sep_right_comm
theorem split_sr [BI PROP] {P Q P1 P2 : PROP} (h : P ⊣⊢ P1 ∗ P2) : P ∗ Q ⊣⊢ P1 ∗ (P2 ∗ Q) :=
  (sep_congr_l h).trans sep_assoc
theorem split_ss [BI PROP] {P Q P1 P2 Q1 Q2 : PROP}
    (h1 : P ⊣⊢ P1 ∗ P2) (h2 : Q ⊣⊢ Q1 ∗ Q2) : P ∗ Q ⊣⊢ (P1 ∗ Q1) ∗ (P2 ∗ Q2) :=
  (sep_congr h1 h2).trans sep_sep_sep_comm

inductive SplitResult {prop : Q(Type)} (bi : Q(BI $prop)) (e : Q($prop)) where
  | emp (_ : $e =Q BI.emp)
  | left
  | right
  | split {elhs erhs : Q($prop)} (lhs : Hyps bi elhs) (rhs : Hyps bi erhs)
          (pf : Q($e ⊣⊢ $elhs ∗ $erhs))

variable {prop : Q(Type)} (bi : Q(BI $prop)) (toRight : Name → Bool) in
def Hyps.splitCore : ∀ {e}, Hyps bi e → SplitResult bi e
  | _, .emp _ => .emp ⟨⟩
  | ehyp, h@(.hyp _ name b ty _) =>
    match matchBool b with
    | .inl _ =>
      have : $ehyp =Q iprop(□ $ty) := ⟨⟩
      .split h h q(intuitionistically_sep_dup)
    | .inr _ => if toRight name then .right else .left
  | _, .sep _ _ _ _ lhs rhs =>
    let resl := lhs.splitCore
    let resr := rhs.splitCore
    match resl, resr with
    | .emp _, .emp _ | .left, .emp _ | .emp _, .left | .left, .left => .left
    | .right, .emp _ | .emp _, .right | .right, .right => .right
    | .left, .right => .split lhs rhs q(.rfl)
    | .right, .left => .split rhs lhs q(sep_comm)
    | .emp _, .split r1 r2 rpf => .split r1 r2 q(split_es $rpf)
    | .left, .split r1 r2 rpf => .split (lhs.mkSep r1) r2 q(split_ls $rpf)
    | .right, .split r1 r2 rpf => .split r1 (lhs.mkSep r2) q(split_rs $rpf)
    | .split l1 l2 lpf, .emp _ => .split l1 l2 q(split_se $lpf)
    | .split l1 l2 lpf, .left => .split (l1.mkSep rhs) l2 q(split_sl $lpf)
    | .split l1 l2 lpf, .right => .split l1 (l2.mkSep rhs) q(split_sr $lpf)
    | .split l1 l2 lpf, .split r1 r2 rpf => .split (l1.mkSep r1) (l2.mkSep r2) q(split_ss $lpf $rpf)

def Hyps.split {prop : Q(Type)} (bi : Q(BI $prop)) (toRight : Name → Bool) {e} (hyps : Hyps bi e) :
    (elhs erhs : Q($prop)) × Hyps bi elhs × Hyps bi erhs × Q($e ⊣⊢ $elhs ∗ $erhs) :=
  match hyps.splitCore bi toRight with
  | .emp _ => ⟨_, _, hyps, hyps, q(sep_emp_rev)⟩
  | .left => ⟨_, _, hyps, .mkEmp bi, q(sep_emp_rev)⟩
  | .right => ⟨_, _, .mkEmp bi, hyps, q(emp_sep_rev)⟩
  | .split lhs rhs pf => ⟨_, _, lhs, rhs, pf⟩

theorem sep_split [BI PROP] {P P1 P2 Q Q1 Q2 : PROP} [inst : FromSep Q Q1 Q2]
    (h : P ⊣⊢ P1 ∗ P2) (h1 : P1 ⊢ Q1) (h2 : P2 ⊢ Q2) : P ⊢ Q :=
  h.1.trans <| (sep_mono h1 h2).trans inst.1

declare_syntax_cat splitSide
syntax "l" : splitSide
syntax "r" : splitSide

elab "isplit" side:splitSide "[" hyps:ident,* "]" : tactic => do
  -- parse syntax
  let splitRight ← match side with
    | `(splitSide| l) => pure false
    | `(splitSide| r) => pure true
    | _  => throwUnsupportedSyntax
  let names ← hyps.getElems.mapM fun name => do
    let name := name.getId
    if name.isAnonymous then
      throwUnsupportedSyntax
    pure name

  -- extract environment
  let (mvar, { prop, bi, hyps, goal }) ← istart (← getMainGoal)
  mvar.withContext do

  let Q1 ← mkFreshExprMVarQ prop
  let Q2 ← mkFreshExprMVarQ prop
  let _ ← synthInstanceQ q(FromSep $goal $Q1 $Q2)

  -- split conjunction
  let ⟨el, er, lhs, rhs, pf⟩ := hyps.split bi (names.contains · == splitRight)

  let m1 : Q($el ⊢ $Q1) ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { prop, bi, hyps := lhs, goal := Q1 }
  let m2 : Q($er ⊢ $Q2) ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { prop, bi, hyps := rhs, goal := Q2 }
  mvar.assign q(sep_split (Q := $goal) $pf $m1 $m2)
  replaceMainGoal [m1.mvarId!, m2.mvarId!]

macro "isplit" &"l" : tactic => `(tactic| isplit r [])
macro "isplit" &"r" : tactic => `(tactic| isplit l [])
