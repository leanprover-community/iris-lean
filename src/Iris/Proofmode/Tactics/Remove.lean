/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.BI
import Iris.Proofmode.Expr
import Iris.Proofmode.Classes
import Iris.Std
import Lean.Elab

namespace Iris.Proofmode
open Lean Elab.Tactic Meta Qq BI

structure RemoveHyp (prop : Q(Type)) (bi : Q(BI $prop)) (e : Q($prop)) where
  (hyps' : Hyps prop) (out out' : Q($prop)) (p : Q(Bool))
  (eq : $out =Q iprop(□?$p $out'))
  (pf : Q($e ⊣⊢ $hyps'.strip ∗ $out))

inductive RemoveHypCore (prop : Q(Type)) (bi : Q(BI $prop)) (e : Q($prop)) (α : Type) where
  | none
  | one (a : α) (out' : Q($prop)) (p : Q(Bool)) (eq : $e =Q iprop(□?$p $out'))
  | main (a : α) (_ : RemoveHyp prop bi e)

theorem remove_l [BI PROP] {P P' Q R : PROP} (h : P ⊣⊢ P' ∗ R) :
    P ∗ Q ⊣⊢ (P' ∗ Q) ∗ R :=
  (sep_congr_l h).trans sep_right_comm

theorem remove_r [BI PROP] {P Q Q' R : PROP} (h : Q ⊣⊢ Q' ∗ R) :
    P ∗ Q ⊣⊢ (P ∗ Q') ∗ R :=
  (sep_congr_r h).trans sep_assoc.symm

theorem intuitionistically_sep_dup [BI PROP] {P : PROP} : □ P ⊣⊢ □ P ∗ □ P :=
  intuitionistically_sep_idem.symm

variable [Monad m] {prop : Q(Type)} (bi : Q(BI $prop)) (rp : Bool)
  (check : HypothesisKind → Name → Q($prop) → m (Option α)) in
/-- If `rp` is true, the hyp will be removed even if it is in the intuitionistic context. -/
def Hyps.removeCore : (hyps : Hyps prop) → m (RemoveHypCore prop bi hyps.strip α)
  | .emp _ => pure .none
  | h@(.hyp _ e kind name ty) => do
    if let some a ← check kind name ty then
      match kind, rp with
      | .intuitionistic, false =>
        have : $e =Q $h.strip := ⟨⟩
        have : $e =Q iprop(□ $ty) := ⟨⟩
        return .main a ⟨h, e, ty, q(true), ⟨⟩, q(intuitionistically_sep_dup)⟩
      | .intuitionistic, _ => return .one a ty q(true) ⟨⟩
      | .spatial, _ => return .one a ty q(false) ⟨⟩
    else
      return .none
  | .sep _ s lhs rhs => do
    let elhs := lhs.strip
    let erhs := rhs.strip
    have : $s =Q iprop($elhs ∗ $erhs) := ⟨⟩
    match ← rhs.removeCore with
    | .one a out' p h =>
      return .main a ⟨lhs, erhs, out', p, h, q(.rfl)⟩
    | .main a ⟨rhs', out, out', p, h, pf⟩ =>
      let hyps' := .mkSep bi lhs rhs'
      return .main a ⟨hyps', out, out', p, h, q(remove_r $pf)⟩
    | .none => match ← lhs.removeCore with
      | .one a out' p h =>
        return .main a ⟨rhs, elhs, out', p, h, q(sep_comm)⟩
      | .main a ⟨lhs', out, out', p, h, pf⟩ =>
        let hyps' := .mkSep bi lhs' rhs
        return .main a ⟨hyps', out, out', p, h, q(remove_l $pf)⟩
      | .none => pure .none

theorem sep_emp_rev [BI PROP] {P : PROP} : P ⊣⊢ P ∗ emp := sep_emp.symm

theorem emp_sep_rev [BI PROP] {P : PROP} : P ⊣⊢ emp ∗ P := emp_sep.symm

def Hyps.removeG [Monad m] {prop : Q(Type)} (bi : Q(BI $prop)) (rp : Bool) (hyps : Hyps prop)
    (check : HypothesisKind → Name → Q($prop) → m (Option α)) :
    m (Option (α × RemoveHyp prop bi hyps.strip)) := do
  match ← hyps.removeCore bi rp check with
  | .none => return none
  | .one a out' p h => return some ⟨a, .mkEmp bi, hyps.strip, out', p, h, q(emp_sep_rev)⟩
  | .main a res => return some (a, res)

def Hyps.remove {prop : Q(Type)} (bi : Q(BI $prop)) (rp : Bool) (hyps : Hyps prop) (name : Name) :
    Option (RemoveHyp prop bi hyps.strip) :=
  (·.2) <$> Id.run (hyps.removeG bi rp fun _ name' _ => if name == name' then some () else none)
