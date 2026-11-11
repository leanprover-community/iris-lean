/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

public import Iris.HeapLang.Syntax

@[expose] public section

/-!
# Parallel substitution for HeapLang

`msubst σ e` substitutes the values of the list `σ : List (String × Val)` for the variables of `e`
in parallel. The first entry for a variable wins: `msubst [("x", v), ("x", w)] (var "x") = val v`.
Under a binder `rec f y e`, `msubst σ` continues with `dropB f y σ`, the entries of `σ` for
variables other than `f` and `y`.

β-reduction substitutes sequentially (`Exp.subst`). The two notions agree:

* `(msubst σ e).substStr x v = msubst (σ ++ [(x, v)]) e`, and
* a closure body `msubst (dropB f y σ) e` applied to `w` reduces to
  `msubst ((f, fv) :: (y, w) :: σ) e`. The new entries shadow `σ`'s entries for `f` and `y`, so the
  filter `dropB` disappears and the substitution list stays a literal cons list.

`vcgen` pushes `msubst σ` into an expression one constructor at a time (`Iris.HeapLang.VCGen`).
-/

namespace Iris.HeapLang.VCGen

open Iris.HeapLang

/-- The entries of `σ` for variables other than the binders `f` and `y`. -/
def dropB (f y : Binder) (σ : List (String × Val)) : List (String × Val) :=
  σ.filter fun p => Binder.named p.1 != f && Binder.named p.1 != y

/-- Parallel substitution of `σ` into `e`; the first entry for a variable wins. -/
def msubst (σ : List (String × Val)) : Exp → Exp
  | .val v => .val v
  | .var z => match σ.lookup z with
    | some v => .val v
    | none => .var z
  | .rec_ f y e => .rec_ f y (msubst (dropB f y σ) e)
  | .app e₁ e₂ => .app (msubst σ e₁) (msubst σ e₂)
  | .unop op e => .unop op (msubst σ e)
  | .binop op e₁ e₂ => .binop op (msubst σ e₁) (msubst σ e₂)
  | .if e₀ e₁ e₂ => .if (msubst σ e₀) (msubst σ e₁) (msubst σ e₂)
  | .pair e₁ e₂ => .pair (msubst σ e₁) (msubst σ e₂)
  | .fst e => .fst (msubst σ e)
  | .snd e => .snd (msubst σ e)
  | .injL e => .injL (msubst σ e)
  | .injR e => .injR (msubst σ e)
  | .case e₀ e₁ e₂ => .case (msubst σ e₀) (msubst σ e₁) (msubst σ e₂)
  | .allocN e₁ e₂ => .allocN (msubst σ e₁) (msubst σ e₂)
  | .free e => .free (msubst σ e)
  | .load e => .load (msubst σ e)
  | .store e₁ e₂ => .store (msubst σ e₁) (msubst σ e₂)
  | .cmpXchg e₀ e₁ e₂ => .cmpXchg (msubst σ e₀) (msubst σ e₁) (msubst σ e₂)
  | .xchg e₁ e₂ => .xchg (msubst σ e₁) (msubst σ e₂)
  | .faa e₁ e₂ => .faa (msubst σ e₁) (msubst σ e₂)
  | .fork e => .fork (msubst σ e)
  | .newProph => .newProph
  | .resolve e₀ e₁ e₂ => .resolve (msubst σ e₀) (msubst σ e₁) (msubst σ e₂)

theorem lookup_dropB (f y : Binder) (σ : List (String × Val)) (z : String) :
    (dropB f y σ).lookup z = if Binder.named z = f ∨ Binder.named z = y then none else σ.lookup z := by
  induction σ with
  | nil => simp [dropB]
  | cons p σ ih =>
    obtain ⟨x, v⟩ := p
    simp only [dropB, List.filter_cons] at ih ⊢
    by_cases hx : Binder.named x = f ∨ Binder.named x = y
    · have : (Binder.named x != f && Binder.named x != y) = false := by
        rcases hx with hx | hx <;> simp [hx]
      rw [this, ite_eq_right (by simp), ih]
      by_cases hz : z = x
      · subst hz; simp [hx]
      · simp [List.lookup, show (z == x) = false by simpa using hz]
    · have : (Binder.named x != f && Binder.named x != y) = true := by
        simp only [not_or] at hx; simp [hx.1, hx.2]
      rw [this, ite_eq_left rfl]
      by_cases hz : z = x
      · subst hz; simp [hx, List.lookup]
      · simp [List.lookup, show (z == x) = false by simpa using hz, ih]

theorem msubst_nil (e : Exp) : msubst [] e = e := by
  induction e using Exp.rec (motive_2 := fun _ => True) <;>
    simp_all [msubst, dropB]

theorem msubst_congr {σ τ : List (String × Val)} (h : ∀ z, σ.lookup z = τ.lookup z) (e : Exp) :
    msubst σ e = msubst τ e := by
  induction e using Exp.rec (motive_2 := fun _ => True) generalizing σ τ
  case rec_ f y e ih =>
    simp only [msubst]
    congr 1
    exact ih fun z => by simp [lookup_dropB, h]
  case var z => simp [msubst, h]
  all_goals first | trivial | (simp only [msubst]; congr 1 <;> solve_by_elim)

theorem dropB_append (f y : Binder) (σ τ : List (String × Val)) :
    dropB f y (σ ++ τ) = dropB f y σ ++ dropB f y τ := by
  simp [dropB]

@[simp] theorem substStr_val (x : String) (v w : Val) : (Exp.val w).substStr x v = .val w := rfl
@[simp] theorem substStr_ofVal (x : String) (v w : Val) :
    (Iris.ProgramLogic.ToVal.ofVal (Expr := Exp) w).substStr x v = .val w := rfl

theorem lookup_cons (z k : String) (v : Val) (σ : List (String × Val)) :
    List.lookup z ((k, v) :: σ) = if z = k then some v else List.lookup z σ := by
  by_cases h : z = k
  · simp [List.lookup, h]
  · have : (z == k) = false := by simpa using h
    simp [List.lookup, h, this]

theorem substStr_msubst (x : String) (v : Val) (σ : List (String × Val)) (e : Exp) :
    (msubst σ e).substStr x v = msubst (σ ++ [(x, v)]) e := by
  induction e using Exp.rec (motive_2 := fun _ => True) generalizing σ <;>
    simp_all [msubst, Exp.substStr]
  case var z =>
    cases h : σ.lookup z with
    | some w => simp [List.lookup_append, h]
    | none =>
      by_cases hz : x = z
      · subst hz; simp [Exp.substStr, List.lookup_append, h]
      · rw [List.lookup_append, h, Option.none_or, lookup_cons, ite_eq_right (Ne.symm hz)]
        simp [Exp.substStr, hz]
  case rec_ f y e ih =>
    rw [dropB_append]
    by_cases hf : Binder.named x = f
    · have : dropB f y [(x, v)] = [] := by simp [dropB, hf]
      rw [this, List.append_nil]; simp [hf]
    by_cases hy : Binder.named x = y
    · have : dropB f y [(x, v)] = [] := by simp [dropB, hy]
      rw [this, List.append_nil]; simp [hy]
    have : dropB f y [(x, v)] = [(x, v)] := by simp [dropB, hf, hy]
    rw [this, ← ih]
    simp [hf, hy]

/-- Cons the entry for the binder `b`: nothing for `anon`. -/
def consB (b : Binder) (v : Val) (σ : List (String × Val)) : List (String × Val) :=
  match b with
  | .anon => σ
  | .named x => (x, v) :: σ

theorem subst_msubst (b : Binder) (v : Val) (σ : List (String × Val)) (e : Exp) :
    (msubst σ e).subst b v = msubst (σ ++ consB b v []) e := by
  cases b with
  | anon => simp [Exp.subst, consB]
  | named x => simp [Exp.subst, consB, substStr_msubst]

theorem beta_eq (f y : Binder) (fv w : Val) (e : Exp) :
    (e.subst f fv).subst y w = msubst (consB f fv (consB y w [])) e := by
  calc (e.subst f fv).subst y w = ((msubst [] e).subst f fv).subst y w := by rw [msubst_nil]
    _ = msubst (([] ++ consB f fv []) ++ consB y w []) e := by
      rw [subst_msubst, ← msubst_nil (Exp.subst _ _ _), subst_msubst, msubst_nil]
    _ = _ := by cases f <;> cases y <;> rfl

theorem beta_msubst_eq (f y : Binder) (fv w : Val) (σ : List (String × Val)) (e : Exp) :
    ((msubst (dropB f y σ) e).subst f fv).subst y w = msubst (consB f fv (consB y w σ)) e := by
  rw [subst_msubst, subst_msubst, List.append_assoc]
  apply msubst_congr
  intro z
  simp only [List.lookup_append, lookup_dropB]
  cases f <;> cases y <;> simp only [consB, lookup_cons, List.lookup] <;>
    grind

/-! `msubst` and `dropB` compute only through their equations. Unification never unfolds them, so
matching a specification against a program `msubst σ e` fails fast. -/
attribute [irreducible] msubst dropB

end Iris.HeapLang.VCGen
