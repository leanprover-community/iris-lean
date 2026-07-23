module

public import IrisDoNightly.Semantics
import Std.Tactic.Do
import Std.Internal.Do

/-! # Axiomatic Semantics for HeapLang -/

set_option mvcgen.warning false

open Lean.Order

namespace Iris.HeapLang.Ax

/-- A predicate `wp` imbues a fragment of HeapLang with the correct axiomatic semantics.
In particular, `wp` admits proof rules that obey the evaluation order and effects of HeapLang. -/
class HeapLangAxioms (wp : Exp → (Val → Prop) → Prop) where
  wp_mono : (∀ v, Φ v → Ψ v) → wp e Φ → wp e Ψ
  wp_val : Φ v → wp (Exp.ofVal v) Φ
  wp_closure : Φ (.rec_ f x e) → wp (Exp.rec_ f x e) Φ
  wp_app :
    wp e₂ (fun v₂ => wp e₁ (fun vf => ∃ f x body, vf = Val.rec_ f x body ∧
      wp ((body.subst f (.rec_ f x body)).subst x v₂) Φ)) →
    wp (Exp.app e₁ e₂) Φ
  wp_unop :
    wp e (fun v => ∃ v', op.eval v = some v' ∧ Φ v') →
    wp (Exp.unop op e) Φ
  wp_binop :
    wp e₂ (fun v₂ => wp e₁ (fun v₁ => ∃ v', op.eval v₁ v₂ = some v' ∧ Φ v')) →
    wp (Exp.binop op e₁ e₂) Φ
  wp_cond :
    wp e₀ (fun vc => ∃ b, vc = Val.lit (.bool b) ∧ wp (if b then e₁ else e₂) Φ) →
    wp (Exp.if e₀ e₁ e₂) Φ
  wp_pair :
    wp e₂ (fun v₂ => wp e₁ (fun v₁ => Φ (Val.pair v₁ v₂))) →
    wp (Exp.pair e₁ e₂) Φ
  wp_fst : wp e (fun v => ∃ v₁ v₂, v = Val.pair v₁ v₂ ∧ Φ v₁) → wp (Exp.fst e) Φ
  wp_snd : wp e (fun v => ∃ v₁ v₂, v = Val.pair v₁ v₂ ∧ Φ v₂) → wp (Exp.snd e) Φ
  wp_injL : wp e (fun v => Φ (Val.injL v)) → wp (Exp.injL e) Φ
  wp_injR : wp e (fun v => Φ (Val.injR v)) → wp (Exp.injR e) Φ
  wp_case :
    wp e₀ (fun vc =>
      (∃ v, vc = Val.injL v ∧ wp (Exp.app e₁ (Exp.ofVal v)) Φ) ∨
      (∃ v, vc = Val.injR v ∧ wp (Exp.app e₂ (Exp.ofVal v)) Φ)) →
    wp (Exp.case e₀ e₁ e₂) Φ

open HeapLangAxioms Std.Internal.Do

/-- Local notation for a Std.Do weakest precondition. -/
scoped syntax:max "wp⟦" term:min "⟧" ppSpace term:max : term
scoped macro_rules
  | `(wp⟦ $e ⟧ $Φ) => `(Std.Internal.Do.wp $e $Φ Std.Internal.Do.EPost.Nil.mk)

set_option synthInstance.checkSynthOrder false in
instance instWP_HeapLangAxioms {wp} [HeapLangAxioms wp] :
    Std.Internal.Do.WP Exp Val Prop EPost.Nil where
  wpTrans e := ⟨fun Φ _ => wp e Φ⟩
  wp_trans_monotone _ _ _ _ _ _ := wp_mono

section laws

variable {wp} [HeapLangAxioms wp]

@[spec] theorem spec_val {v : Val} {Φ : Val → Prop} :
    Φ v ⊑ wp⟦(Exp.ofVal v : Exp)⟧ Φ := by
  intro h; exact wp_val h

@[spec] theorem spec_rec {f x : Binder} {e : Exp} {Φ : Val → Prop} :
    Φ (.rec_ f x e) ⊑ wp⟦Exp.rec_ f x e⟧ Φ := by
  intro h; exact wp_closure h

@[spec] theorem spec_app {e₁ e₂ : Exp} {Φ : Val → Prop} :
    wp⟦e₂⟧ (fun v₂ => wp⟦e₁⟧ (fun vf => ∃ f x body, vf = Val.rec_ f x body ∧
        wp⟦(body.subst f (.rec_ f x body)).subst x v₂⟧ Φ))
      ⊑ wp⟦Exp.app e₁ e₂⟧ Φ := by
  intro h; exact wp_app h

@[spec] theorem spec_unop {op : UnOp} {e : Exp} {Φ : Val → Prop} :
    wp⟦e⟧ (fun v => ∃ v', op.eval v = some v' ∧ Φ v')
      ⊑ wp⟦Exp.unop op e⟧ Φ := by
  intro h; exact wp_unop h

@[spec] theorem spec_binop {op : BinOp} {e₁ e₂ : Exp} {Φ : Val → Prop} :
    wp⟦e₂⟧ (fun v₂ => wp⟦e₁⟧ (fun v₁ => ∃ v', op.eval v₁ v₂ = some v' ∧ Φ v'))
      ⊑ wp⟦Exp.binop op e₁ e₂⟧ Φ := by
  intro h; exact wp_binop h

@[spec] theorem spec_if {e₀ e₁ e₂ : Exp} {Φ : Val → Prop} :
    wp⟦e₀⟧ (fun vc => ∃ b, vc = Val.lit (.bool b) ∧ wp⟦if b then e₁ else e₂⟧ Φ)
      ⊑ wp⟦Exp.if e₀ e₁ e₂⟧ Φ := by
  intro h; exact wp_cond h

@[spec] theorem spec_pair {e₁ e₂ : Exp} {Φ : Val → Prop} :
    wp⟦e₂⟧ (fun v₂ => wp⟦e₁⟧ (fun v₁ => Φ (Val.pair v₁ v₂)))
      ⊑ wp⟦Exp.pair e₁ e₂⟧ Φ := by
  intro h; exact wp_pair h

@[spec] theorem spec_fst {e : Exp} {Φ : Val → Prop} :
    wp⟦e⟧ (fun v => ∃ v₁ v₂, v = Val.pair v₁ v₂ ∧ Φ v₁)
      ⊑ wp⟦Exp.fst e⟧ Φ := by
  intro h; exact wp_fst h

@[spec] theorem spec_snd {e : Exp} {Φ : Val → Prop} :
    wp⟦e⟧ (fun v => ∃ v₁ v₂, v = Val.pair v₁ v₂ ∧ Φ v₂)
      ⊑ wp⟦Exp.snd e⟧ Φ := by
  intro h; exact wp_snd h

@[spec] theorem spec_injL {e : Exp} {Φ : Val → Prop} :
    wp⟦e⟧ (fun v => Φ (Val.injL v)) ⊑ wp⟦Exp.injL e⟧ Φ := by
  intro h; exact wp_injL h

@[spec] theorem spec_injR {e : Exp} {Φ : Val → Prop} :
    wp⟦e⟧ (fun v => Φ (Val.injR v)) ⊑ wp⟦Exp.injR e⟧ Φ := by
  intro h; exact wp_injR h

@[spec] theorem spec_case {e₀ e₁ e₂ : Exp} {Φ : Val → Prop} :
    wp⟦e₀⟧ (fun vc =>
        (∃ v, vc = Val.injL v ∧ wp⟦Exp.app e₁ (Exp.ofVal v)⟧ Φ) ∨
        (∃ v, vc = Val.injR v ∧ wp⟦Exp.app e₂ (Exp.ofVal v)⟧ Φ))
      ⊑ wp⟦Exp.case e₀ e₁ e₂⟧ Φ := by
  intro h; exact wp_case h

end laws


section demos

variable {wp} [HeapLangAxioms wp]

private def lit (n : Int) : Exp := .ofVal (.lit (.int n))
private def bool (b : Bool) : Exp := .ofVal (.lit (.bool b))
private def lam (x : String) (e : Exp) : Exp := .rec_ .anon (.named x) e
private def add (a b : Exp) : Exp := .binop .plus a b

/-- Substituting into a value-expression is the identity. Needed because the
default simp set normalises `.val` to `.ofVal` (`val_to_ofVal`), so `substStr`'s
`.val` case cannot fire on a `.ofVal` leaf; this `rfl` lemma bridges the gap while
keeping the `vcgen`-friendly `.ofVal` form. -/
@[local simp] private theorem substStr_ofVal (x : String) (v w : Val) :
    Exp.substStr x v (Exp.ofVal w) = Exp.ofVal w := rfl

/-! ### Values and pure arithmetic -/

example : True ⊑ wp⟦lit 0⟧ (fun _v => True) := by
  unfold lit; vcgen

example : True ⊑ wp⟦lit 0⟧ (fun v => v = Val.lit (.int 0)) := by
  unfold lit; vcgen with finish

attribute [simp] BinOp.eval

/-- `(1 + 2) + (3 + 4) = 10`, nested redexes. -/
example : True ⊑ wp⟦add (add (lit 1) (lit 2)) (add (lit 3) (lit 4))⟧ (fun v => v = Val.lit (.int 10)) := by
  simp only [add, lit]
  vcgen
  simp [BinOp.eval]
  vcgen
  simp

/-! ### Computed conditions -/

/-- The guard is a comparison, not a literal: `if 1 < 2 then 1 else 2 = 1`. -/
example : True ⊑ wp⟦Exp.if (.binop .lt (lit 1) (lit 2)) (lit 1) (lit 2)⟧ (fun v => v = Val.lit (.int 1)) := by
  unfold lit
  vcgen
  simp [BinOp.eval]
  vcgen

/-! ### Binders (β-reduction)

The workflow: `vcgen until Exp.subst _ _ _` symbolically executes up to the
substitution redex, `simp [Exp.subst, Exp.substStr]` computes it, then `vcgen`
resumes on the concrete substituted program. -/

/-- Identity applied to a literal: `(λx. x) 0`. -/
example : True ⊑ wp⟦Exp.app (lam "x" (.var "x")) (lit 0)⟧ (fun _v => True) := by
  simp only [lam, lit]
  vcgen until Exp.subst _ _ _
  refine ⟨_, _, _, rfl, ?_⟩
  simp [Exp.subst, Exp.substStr]
  vcgen

/-- The bound variable is used in an arithmetic context: `(λx. x + 1) 5 = 6`. -/
example : True ⊑ wp⟦Exp.app (lam "x" (add (.var "x") (lit 1))) (lit 5)⟧ (fun v => v = Val.lit (.int 6)) := by
  unfold lam add lit
  vcgen until Exp.subst _ _ _
  refine ⟨_, _, _, rfl, ?_⟩
  simp [Exp.subst, Exp.substStr]
  vcgen <;> (try simp [BinOp.eval]) <;> (try vcgen) <;> (try simp [BinOp.eval])

/-! ### Products and sums -/

/-- `fst (1 + 2, 3 + 4) = 3`. -/
example : True ⊑ wp⟦Exp.fst (Exp.pair (add (lit 1) (lit 2)) (add (lit 3) (lit 4)))⟧ (fun v => v = Val.lit (.int 3)) := by
  unfold add lit
  vcgen <;> (try simp [BinOp.eval]) <;> (try vcgen) <;> (try simp [BinOp.eval])

end demos
end Iris.HeapLang.Ax
