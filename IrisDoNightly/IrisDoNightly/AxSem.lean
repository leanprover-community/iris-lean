module

public import IrisDoNightly.Semantics
public import IrisDoNightly.Notation
import Std.Tactic.Do
import Std.Internal.Do

/-! # Axiomatic Semantics for HeapLang -/

set_option mvcgen.warning false

open Lean.Order

namespace Iris.HeapLang.Ax

@[expose] public section

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
  /-- The bind / evaluation-context rule: to run `K[e]`, first run `e`, then plug its value into
  the hole.  This is the one structural rule not tied to a single constructor; it is what lets one
  spec feed its result into another (e.g. composing a codec's compressor with its decompressor). -/
  wp_bind (K : ECtxItem) : wp e (fun v => wp (K.fill (Exp.ofVal v)) Φ) → wp (K.fill e) Φ

end

open HeapLangAxioms Std.Internal.Do

/-! Local notation for a Std.Do weakest precondition. -/
public meta section
scoped syntax:max "wp⟦" term:min "⟧" ppSpace term:max : term
scoped macro_rules
  | `(wp⟦ $e ⟧ $Φ) => `(Std.Internal.Do.wp $e $Φ Std.Internal.Do.EPost.Nil.mk)
end

@[expose] public section
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

theorem spec_bind (K : ECtxItem) {e : Exp} {Φ : Val → Prop} :
    wp⟦e⟧ (fun v => wp⟦K.fill (Exp.ofVal v)⟧ Φ) ⊑ wp⟦K.fill e⟧ Φ := by
  intro h; exact wp_bind K h

end laws

end

end Iris.HeapLang.Ax
