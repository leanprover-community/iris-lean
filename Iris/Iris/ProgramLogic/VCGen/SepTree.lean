/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

public import Iris.ProgramLogic.VCGen.Lattice

@[expose] public section

/-!
# Separating conjunctions up to associativity, commutativity and unit

A `SepTree` is the syntax of a separating conjunction over numbered atoms. `SepTree.eval ctx t`
interprets atom `i` as the `i`th entry of `ctx`. Two trees with the same atoms up to permutation
evaluate to the same assertion (`eval_eq_of_isPerm`). The permutation check `List.isPerm` runs on
lists of numerals, so a proof term `Eq.refl true` certifies it.

Example: with `ctx = [A, B, C]`, the tree `sep (atom 2) (sep emp (atom 0))` evaluates to
`C ∗ (emp ∗ A)`, and its atoms `[2, 0]` are a permutation of the atoms `[0, 2]` of
`sep (atom 0) (atom 2)`, so both evaluate to the same assertion `A ∗ C`.

The frame inference procedure of `Iris.VCGen.FrameProc` proves its entailments with
`cancel_le` and `frame_le`.
-/

open Iris Iris.BI Lean.Order

namespace Iris.VCGen

/-- A separating conjunction over numbered atoms. -/
inductive SepTree where
  | emp
  | atom (i : Nat)
  | sep (a b : SepTree)

namespace SepTree

variable {PROP : Type _} [BI PROP]

/-- The `i`th atom of `ctx`. -/
def get (ctx : List PROP) (i : Nat) : PROP := ctx.getD i BIBase.emp

/-- The assertion denoted by a tree. -/
def eval (ctx : List PROP) : SepTree → PROP
  | .emp => BIBase.emp
  | .atom i => get ctx i
  | .sep a b => BIBase.sep (eval ctx a) (eval ctx b)

/-- The atoms of a tree, from left to right. -/
def atoms : SepTree → List Nat
  | .emp => []
  | .atom i => [i]
  | .sep a b => atoms a ++ atoms b

/-- The separating conjunction of a list of atoms. -/
def denote (ctx : List PROP) : List Nat → PROP
  | [] => BIBase.emp
  | i :: is => BIBase.sep (get ctx i) (denote ctx is)

theorem denote_append (ctx : List PROP) (l₁ l₂ : List Nat) :
    denote ctx (l₁ ++ l₂) = BIBase.sep (denote ctx l₁) (denote ctx l₂) := by
  induction l₁ with
  | nil => exact BI.emp_sep.to_eq.symm
  | cons i is ih => simp only [List.cons_append, denote, ih]; exact sep_assoc.to_eq.symm

theorem eval_eq_denote (ctx : List PROP) (t : SepTree) : eval ctx t = denote ctx t.atoms := by
  induction t with
  | emp => rfl
  | atom i => exact sep_emp.to_eq.symm
  | sep a b iha ihb => simp only [eval, atoms, denote_append, iha, ihb]

theorem denote_perm (ctx : List PROP) {l₁ l₂ : List Nat} (h : l₁.Perm l₂) :
    denote ctx l₁ = denote ctx l₂ := by
  induction h with
  | nil => rfl
  | cons i _ ih => simp only [denote, ih]
  | swap i j l =>
    simp only [denote]
    rw [← sep_assoc.to_eq, ← sep_assoc.to_eq, (sep_comm (P := get ctx j) (Q := get ctx i)).to_eq]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem eval_eq_of_isPerm (ctx : List PROP) {t₁ t₂ : SepTree}
    (h : t₁.atoms.isPerm t₂.atoms = true) : eval ctx t₁ = eval ctx t₂ := by
  rw [eval_eq_denote, eval_eq_denote]
  exact denote_perm ctx (List.isPerm_iff.mp h)

theorem eval_append (ctx : List PROP) (t₁ t₂ t : SepTree)
    (h : t.atoms.isPerm (t₁.atoms ++ t₂.atoms) = true) :
    eval ctx t = BIBase.sep (eval ctx t₁) (eval ctx t₂) := by
  rw [eval_eq_denote, denote_perm ctx (List.isPerm_iff.mp h), denote_append,
    ← eval_eq_denote, ← eval_eq_denote]

theorem cancel_le (ctx : List PROP) (tP tA tR tX tK : SepTree)
    (h₁ : tP.atoms.isPerm (tA.atoms ++ tR.atoms) = true)
    (h₂ : tX.atoms.isPerm (tA.atoms ++ tK.atoms) = true)
    (hr : eval ctx tR ⊑ eval ctx tK) : eval ctx tP ⊑ eval ctx tX := by
  rw [eval_append ctx tA tR tP h₁, eval_append ctx tA tK tX h₂]
  exact sep_mono_right hr

theorem frame_le (ctx : List PROP) (tP tR tA : SepTree) {W : PROP}
    (h : tP.atoms.isPerm (tR.atoms ++ tA.atoms) = true)
    (hW : eval ctx tA ⊑ W) : eval ctx tP ⊑ BIBase.sep (eval ctx tR) W := by
  rw [eval_append ctx tR tA tP h]
  exact sep_mono_right hW

theorem emp_frame_le {P W : PROP} (h : P ⊑ W) : P ⊑ BIBase.sep BIBase.emp W :=
  BIBase.Entails.trans h BI.emp_sep.mpr

end SepTree

end Iris.VCGen
