module

public import IrisDoNightly.Legacy.SLFrame
public import IrisDoNightly.Notation
import Std.Tactic.Do
import Std.Internal.Do

set_option mvcgen.warning false

/-!
# Recursion / loop reasoning for HeapLang

HeapLang loops are object-level recursive functions (`rec f x := …`).  Because our `HProp` is a
plain `State → Prop` (no step indexing / `▷`), we do **not** need Löb induction: a terminating loop's
spec is proved by ordinary well-founded induction on a Lean measure, unfolding one iteration per
step.

This file provides the two reusable lemmas that make that mechanical:

* `wp_beta` — one β-step (apply a closure value, land on its substituted body);
* `wp_rec` — well-founded recursion.  Crucially it abstracts the loop as a **variable**, so that when
  the caller symbolically executes the body with `vcgen`, the recursive calls `wp (loop (arg a'))`
  cannot be unfolded and are left verbatim, ready to be closed by the induction hypothesis.

`countdown` at the end is the canonical worked example; every codec loop follows its shape.
-/

open Lean.Order Std.Internal.Do
open Iris.HeapLang

@[expose] public section

namespace Iris.HeapLang.SL

variable {wp} [HeapLangAxioms wp]

/-- Substituting into a value leaf is the identity.  Needed in loop proofs because the default simp
set normalises `.val` to `.ofVal`, so `substStr`'s `.val` arm cannot fire on a `.ofVal` leaf. -/
@[simp] theorem substStr_ofVal (x : String) (v w : Val) :
    Exp.substStr x v (Exp.ofVal w) = Exp.ofVal w := rfl

/-- One β-step: applying a closure value reduces to its substituted body.  A pure lower-bound peel of
`spec_app` + `spec_val` + the closure match; reusable for every loop unfold. -/
theorem wp_beta (f x : Binder) (body : Exp) (v : Val) (Φ : Val → HProp) :
    wp⟦(body.subst f (.rec_ f x body)).subst x v⟧ Φ
      ⊑ wp⟦Exp.app (Exp.ofVal (.rec_ f x body)) (Exp.ofVal v)⟧ Φ := by
  refine PartialOrder.rel_trans ?_ spec_app
  refine PartialOrder.rel_trans ?_ spec_val
  refine PartialOrder.rel_trans ?_ spec_val
  exact le_hexists _ f (le_hexists _ x (le_hexists _ body (le_hand_pure rfl PartialOrder.rel_refl)))

/-- Well-founded recursion for terminating loops.  To prove a spec for `loop = rec f x body` applied
to `arg a`, prove the body spec for each `a`, assuming the spec already holds for every `a'` of
smaller measure `μ`.  Abstracting `loop` as a variable keeps recursive calls opaque to `vcgen`. -/
theorem wp_rec {A : Type} (μ : A → Nat)
    (f x : Binder) (body : Exp) (loop : Val) (hloop : loop = .rec_ f x body)
    (arg : A → Val) (Φ : A → Val → HProp) (pre : A → HProp)
    (hbody : ∀ a,
      (∀ a', μ a' < μ a → pre a' ⊑ wp⟦Exp.app (Exp.ofVal loop) (Exp.ofVal (arg a'))⟧ (Φ a')) →
      pre a ⊑ wp⟦(body.subst f loop).subst x (arg a)⟧ (Φ a)) :
    ∀ a, pre a ⊑ wp⟦Exp.app (Exp.ofVal loop) (Exp.ofVal (arg a))⟧ (Φ a) := by
  subst hloop
  suffices H : ∀ n a, μ a = n →
      pre a ⊑ wp⟦Exp.app (Exp.ofVal (.rec_ f x body)) (Exp.ofVal (arg a))⟧ (Φ a) by
    exact fun a => H (μ a) a rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ihn =>
    intro a ha
    refine PartialOrder.rel_trans (hbody a ?_) (wp_beta f x body (arg a) (Φ a))
    exact fun a' ha' => ihn (μ a') (ha ▸ ha') a' rfl

/-! ## Worked example: `countdown`

The canonical loop-proof template.  `countdown #k` recurses until `k ≤ 0`; the decrement is a `let`
so the recursive argument is an already-evaluated **value**, matching the induction hypothesis. -/

/-- `countdown #k` steps down to `#()`. -/
def countdown : Val := hl_val(rec go k := if k ≤ #0 then #() else (let k' := k - #1; go k'))

theorem countdown_spec (k : Int) :
    (emp : HProp) ⊑ wp⟦Exp.app (Exp.ofVal countdown) (Exp.ofVal (.lit (.int k)))⟧ (fun _ => emp) := by
  refine wp_rec (A := Int) Int.toNat _ _ _ countdown rfl
    (fun k => .lit (.int k)) (fun _ _ => emp) (fun _ => emp) ?_ k
  intro k ih
  -- one iteration: compute the substituted body, then symbolically execute it
  simp [Exp.subst, Exp.substStr]
  vcgen
  -- resolve the `if` condition `k ≤ 0`
  refine le_hexists _ (Val.lit (.bool (decide (k ≤ 0)))) (le_hand_pure (by simp [BinOp.eval]) ?_)
  refine le_hexists _ (decide (k ≤ 0)) (le_hand_pure rfl ?_)
  split
  · -- base case `k ≤ 0`: returns `()`
    vcgen
  · -- recursive case `k > 0`: evaluate the decrement, β the `let`-lambda, apply the IH
    rename_i h
    have hlt : (k - 1).toNat < k.toNat := by simp at h; omega
    vcgen
    refine le_hexists _ (Val.lit (.int (k - 1))) (le_hand_pure (by simp [BinOp.eval]) ?_)
    refine PartialOrder.rel_trans ?_ spec_rec
    refine le_hexists _ _ (le_hexists _ _ (le_hexists _ _ (le_hand_pure rfl ?_)))
    simp [Exp.subst, Exp.substStr]
    exact ih (k - 1) hlt

end Iris.HeapLang.SL
