/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.Proofmode.Tactics.Basic
import Iris.Proofmode.Tactics.Remove

namespace Iris.Proofmode
open Lean Elab Tactic Meta Qq BI

theorem from_and_intro [BI PROP] {P Q A1 A2 : PROP} [inst : FromAnd Q A1 A2]
    (h1 : P ⊢ A1) (h2 : P ⊢ A2) : P ⊢ Q :=
  (and_intro h1 h2).trans inst.1

elab "isplit" : tactic => do
  let (mvar, { prop, bi, hyps, goal }) ← istart (← getMainGoal)
  mvar.withContext do

  have ehyps := hyps.strip
  let A1 ← mkFreshExprMVarQ prop
  let A2 ← mkFreshExprMVarQ prop
  let _ ← synthInstanceQ q(FromAnd $goal $A1 $A2)
  let m1 : Q($ehyps ⊢ $A1) ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { prop, bi, hyps, goal := A1 }
  let m2 : Q($ehyps ⊢ $A2) ← mkFreshExprSyntheticOpaqueMVar <|
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

inductive SplitResult (prop : Q(Type)) (bi : Q(BI $prop)) (e : Q($prop)) where
  | emp (_ : $e =Q BI.emp)
  | left
  | right
  | split (lhs rhs : Hyps prop) (elhs erhs : Q($prop)) (pf : Q($e ⊣⊢ $elhs ∗ $erhs))

variable (prop : Q(Type)) (bi : Q(BI $prop)) (toRight : Name → Bool) in
def Hyps.splitCore : (h : Hyps prop) → SplitResult prop bi h.strip
  | .emp _ => .emp ⟨⟩
  | h@(.hyp _ ehyp .intuitionistic _ ty) =>
    have : $ehyp =Q iprop(□ $ty) := ⟨⟩
    .split h h ehyp ehyp q(intuitionistically_sep_dup)
  | .hyp _ _ .spatial name _ => if toRight name then .right else .left
  | .sep _ ehyp lhs rhs =>
    let resl := lhs.splitCore; let elhs := lhs.strip
    let resr := rhs.splitCore; let erhs := rhs.strip
    have : iprop($elhs ∗ $erhs) =Q $ehyp := ⟨⟩
    match resl, resr with
    | .emp _, .emp _ | .left, .emp _ | .emp _, .left | .left, .left => .left
    | .right, .emp _ | .emp _, .right | .right, .right => .right
    | .left, .right => .split lhs rhs elhs erhs q(.rfl)
    | .right, .left => .split rhs lhs erhs elhs q(sep_comm)
    | .emp _, .split r1 r2 er1 er2 rpf => .split r1 r2 er1 er2 q(split_es $rpf)
    | .left, .split r1 r2 er1 er2 rpf =>
      .split (lhs.mkSep bi r1) r2 q(iprop($elhs ∗ $er1)) er2 q(split_ls $rpf)
    | .right, .split r1 r2 er1 er2 rpf =>
      .split r1 (lhs.mkSep bi r2) er1 q(iprop($elhs ∗ $er2)) q(split_rs $rpf)
    | .split l1 l2 el1 el2 lpf, .emp _ => .split l1 l2 el1 el2 q(split_se $lpf)
    | .split l1 l2 el1 el2 lpf, .left =>
      .split (l1.mkSep bi rhs) l2 q(iprop($el1 ∗ $erhs)) el2 q(split_sl $lpf)
    | .split l1 l2 el1 el2 lpf, .right =>
      .split l1 (l2.mkSep bi rhs) el1 q(iprop($el2 ∗ $erhs)) q(split_sr $lpf)
    | .split l1 l2 el1 el2 lpf, .split r1 r2 er1 er2 rpf =>
      .split (l1.mkSep bi r1) (l2.mkSep bi r2) q(iprop($el1 ∗ $er1)) q(iprop($el2 ∗ $er2))
        q(split_ss $lpf $rpf)

def Hyps.split (prop : Q(Type)) (bi : Q(BI $prop)) (toRight : Name → Bool) (hyps : Hyps prop) :
    (_lhs _rhs : Hyps prop) × (elhs erhs : Q($prop)) × Q($(hyps.strip) ⊣⊢ $elhs ∗ $erhs) :=
  let ehyps := hyps.strip
  match hyps.splitCore prop bi toRight with
  | .emp _ => ⟨hyps, hyps, ehyps, ehyps, q(sep_emp_rev)⟩
  | .left => ⟨hyps, .mkEmp bi, ehyps, q(BI.emp), q(sep_emp_rev)⟩
  | .right => ⟨.mkEmp bi, hyps, q(BI.emp), ehyps, q(emp_sep_rev)⟩
  | .split lhs rhs el er pf => ⟨lhs, rhs, el, er, pf⟩

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
  let ⟨lhs, rhs, el, er, pf⟩ := hyps.split prop bi (names.contains · == splitRight)

  let m1 : Q($el ⊢ $Q1) ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { prop, bi, hyps := lhs, goal := Q1 }
  let m2 : Q($er ⊢ $Q2) ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { prop, bi, hyps := rhs, goal := Q2 }
  mvar.assign q(sep_split (Q := $goal) $pf $m1 $m2)
  replaceMainGoal [m1.mvarId!, m2.mvarId!]

macro "isplit" &"l" : tactic => `(tactic| isplit r [])
macro "isplit" &"r" : tactic => `(tactic| isplit l [])
