/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.BI
import Iris.ProofMode.Expr
import Iris.ProofMode.Classes
import Iris.Std
import Lean.Elab

namespace Iris.ProofMode
open Lean Elab.Tactic Meta Qq BI

structure RemoveHyp {prop : Q(Type u)} (bi : Q(BI $prop)) (e : Q($prop)) where
  (e' : Q($prop)) (hyps' : Hyps bi e') (out out' : Q($prop)) (p : Q(Bool))
  (eq : $out =Q iprop(□?$p $out'))
  (pf : Q($e ⊣⊢ $e' ∗ $out))
  deriving Inhabited

inductive RemoveHypCore {prop : Q(Type u)} (bi : Q(BI $prop)) (e : Q($prop)) (α : Type) where
  | none
  | one (a : α) (out' : Q($prop)) (p : Q(Bool)) (eq : $e =Q iprop(□?$p $out'))
  | main (a : α) (_ : RemoveHyp bi e)

theorem remove_l [BI PROP] {P P' Q R : PROP} (h : P ⊣⊢ P' ∗ R) :
    P ∗ Q ⊣⊢ (P' ∗ Q) ∗ R :=
  (sep_congr_l h).trans sep_right_comm

theorem remove_r [BI PROP] {P Q Q' R : PROP} (h : Q ⊣⊢ Q' ∗ R) :
    P ∗ Q ⊣⊢ (P ∗ Q') ∗ R :=
  (sep_congr_r h).trans sep_assoc.symm

theorem intuitionistically_sep_dup [BI PROP] {P : PROP} : □ P ⊣⊢ □ P ∗ □ P :=
  intuitionistically_sep_idem.symm

variable [Monad m] {prop : Q(Type u)} (bi : Q(BI $prop)) (rp : Bool)
  (check : Name → Name → Q(Bool) → Q($prop) → m (Option α)) in
/-- If `rp` is true, the hyp will be removed even if it is in the intuitionistic context. -/
def Hyps.removeCore : ∀ {e}, Hyps bi e → m (RemoveHypCore bi e α)
  | _, .emp _ => pure .none
  | e, h@(.hyp _ name uniq p ty _) => do
    if let some a ← check name uniq p ty then
      match matchBool p, rp with
      | .inl _, false =>
        have : $e =Q iprop(□ $ty) := ⟨⟩
        return .main a ⟨e, h, e, ty, q(true), ⟨⟩, q(intuitionistically_sep_dup)⟩
      | _, _ => return .one a ty p ⟨⟩
    else
      return .none
  | _, .sep _ elhs erhs _ lhs rhs => do
    match ← rhs.removeCore with
    | .one a out' p h =>
      return .main a ⟨elhs, lhs, erhs, out', p, h, q(.rfl)⟩
    | .main a ⟨_, rhs', out, out', p, h, pf⟩ =>
      let hyps' := .mkSep lhs rhs'
      return .main a ⟨_, hyps', out, out', p, h, q(remove_r $pf)⟩
    | .none => match ← lhs.removeCore with
      | .one a out' p h =>
        return .main a ⟨erhs, rhs, elhs, out', p, h, q(sep_comm)⟩
      | .main a ⟨_, lhs', out, out', p, h, pf⟩ =>
        let hyps' := .mkSep lhs' rhs
        return .main a ⟨_, hyps', out, out', p, h, q(remove_l $pf)⟩
      | .none => pure .none

theorem sep_emp_rev [BI PROP] {P : PROP} : P ⊣⊢ P ∗ emp := sep_emp.symm

theorem emp_sep_rev [BI PROP] {P : PROP} : P ⊣⊢ emp ∗ P := emp_sep.symm

def Hyps.removeG [Monad m] {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q(Prop)}
    (rp : Bool) (hyps : Hyps bi e)
    (check : Name → Name → Q(Bool) → Q($prop) → m (Option α)) :
    m (Option (α × RemoveHyp bi e)) := do
  match ← hyps.removeCore bi rp check with
  | .none => return none
  | .one a out' p h => return some ⟨a, _, .mkEmp bi, e, out', p, h, q(emp_sep_rev)⟩
  | .main a res => return some (a, res)

def Hyps.remove {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (rp : Bool) (hyps : Hyps bi e) (uniq : Name) : RemoveHyp bi e :=
  match Id.run (hyps.removeG rp fun _ uniq' _ _ => if uniq == uniq' then some () else none) with
  | some (_, r) => r
  | none => panic! "variable not found"
