module

public import IrisDoNightly.Codec.Basic
import Std.Tactic.Do
import Std.Internal.Do

/-!
# Codec proof automation: a `vcgen`-steppable spec set for the pure HeapLang fragment

This module packages the reusable `@[spec]` rules that let `vcgen` symbolically execute the pure
HeapLang fragment used by the heap-free codecs *without* the loop-breaking existentials of the raw
structural rules in `AxSem`.

The design (see `MWE/SubstNormalization.lean` for the one remaining framework gap):

* Every rule is either a **value form** (fires when the relevant subterms are already `Exp.ofVal`,
  producing a clean `wp` premise — no `∃`) or a **bind form** (focuses the next evaluation position).
* Priorities implement call-by-value: `spec_beta` (2000) beats `spec_appL` (1500, argument already a
  value → focus the function) beats `spec_appR` (1200, general → focus the argument). `spec_appL`'s
  `ofVal`-keyed argument means it is only ever a candidate once the argument is a value, so the two
  bind rules cannot loop.
* `@[spec]` is import-scoped, so importing this module opts a file into the automated style; files
  that keep the old `AxSem` `spec_app` existential style are unaffected.

`vcgen` still cannot normalise the capture-avoiding substitution that `spec_beta` produces (its
program rewriting is head-only), so the stepping tactics below interleave a `simp` that computes it.
Recursion is discharged by passing the induction hypothesis to `vcgen [ih]` (it unifies the recursive
closure with the folded helper up to defeq), or by a manual `exact ih …`.
-/

set_option mvcgen.warning false

open Lean.Order Std.Internal.Do
open Iris.HeapLang

namespace Iris.HeapLang.Ax

open HeapLangAxioms

variable {wp} [HeapLangAxioms wp]

namespace Auto

@[expose] public section

/-- Focus the function of an application whose argument is already a value. -/
@[scoped spec 1500] theorem spec_appL {e₁ : Exp} {v₂ : Val} {Φ : Val → Prop} :
    wp⟦e₁⟧ (fun vf => wp⟦Exp.app (Exp.ofVal vf) (Exp.ofVal v₂)⟧ Φ)
      ⊑ wp⟦Exp.app e₁ (Exp.ofVal v₂)⟧ Φ := fun h => wp_bind (ECtxItem.appL v₂) h

/-- Focus the argument of an application (evaluated first in HeapLang); general, lower priority. -/
@[scoped spec 1200] theorem spec_appR {e₁ e₂ : Exp} {Φ : Val → Prop} :
    wp⟦e₂⟧ (fun v => wp⟦Exp.app e₁ (Exp.ofVal v)⟧ Φ) ⊑ wp⟦Exp.app e₁ e₂⟧ Φ :=
  fun h => wp_bind (ECtxItem.appR e₁) h

/-- Beta: a literal closure applied to a value. No existential. -/
@[scoped spec 2000] theorem spec_beta {f x : Binder} {body : Exp} {v : Val} {Φ : Val → Prop} :
    wp⟦(body.subst f (.rec_ f x body)).subst x v⟧ Φ
      ⊑ wp⟦Exp.app (Exp.ofVal (Val.rec_ f x body)) (Exp.ofVal v)⟧ Φ :=
  fun h => wp_app (wp_val (wp_val ⟨f, x, body, rfl, h⟩))

@[scoped spec 2000] theorem spec_fst_pair {v₁ v₂ : Val} {Φ : Val → Prop} :
    Φ v₁ ⊑ wp⟦Exp.fst (Exp.ofVal (Val.pair v₁ v₂))⟧ Φ := fun h => wp_fst (wp_val ⟨v₁, v₂, rfl, h⟩)

@[scoped spec 2000] theorem spec_snd_pair {v₁ v₂ : Val} {Φ : Val → Prop} :
    Φ v₂ ⊑ wp⟦Exp.snd (Exp.ofVal (Val.pair v₁ v₂))⟧ Φ := fun h => wp_snd (wp_val ⟨v₁, v₂, rfl, h⟩)

@[scoped spec 2000] theorem spec_case_injL {v : Val} {e₁ e₂ : Exp} {Φ : Val → Prop} :
    wp⟦Exp.app e₁ (Exp.ofVal v)⟧ Φ ⊑ wp⟦Exp.case (Exp.ofVal (Val.injL v)) e₁ e₂⟧ Φ :=
  fun h => wp_case (wp_val (Or.inl ⟨v, rfl, h⟩))

@[scoped spec 2000] theorem spec_case_injR {v : Val} {e₁ e₂ : Exp} {Φ : Val → Prop} :
    wp⟦Exp.app e₂ (Exp.ofVal v)⟧ Φ ⊑ wp⟦Exp.case (Exp.ofVal (Val.injR v)) e₁ e₂⟧ Φ :=
  fun h => wp_case (wp_val (Or.inr ⟨v, rfl, h⟩))

/-- Binop on two literal values; the (decidable) evaluation is a side goal for the discharger. -/
@[scoped spec 2000] theorem spec_binop_ok {op : BinOp} {v₁ v₂ v' : Val} {Φ : Val → Prop}
    (h : op.eval v₁ v₂ = some v') :
    Φ v' ⊑ wp⟦Exp.binop op (Exp.ofVal v₁) (Exp.ofVal v₂)⟧ Φ :=
  fun hΦ => wp_binop (wp_val (wp_val ⟨v', h, hΦ⟩))

/-! Per-op integer-binop *value* forms: fire on two literal `Int` operands and return the concrete
result, so no `op.eval = some ?v'` metavariable side goal is left (which `spec_binop_ok` does, and
which stalls on nested arithmetic like `((c - prev) + 256) % 256`). Higher priority so they win. -/

@[scoped spec 2100] theorem spec_binop_add {n m : Int} {Φ : Val → Prop} :
    Φ (Val.lit (.int (n + m)))
      ⊑ wp⟦Exp.binop BinOp.plus (Exp.ofVal (Val.lit (.int n))) (Exp.ofVal (Val.lit (.int m)))⟧ Φ :=
  fun h => wp_binop (wp_val (wp_val ⟨_, by simp [BinOp.eval], h⟩))

@[scoped spec 2100] theorem spec_binop_sub {n m : Int} {Φ : Val → Prop} :
    Φ (Val.lit (.int (n - m)))
      ⊑ wp⟦Exp.binop BinOp.minus (Exp.ofVal (Val.lit (.int n))) (Exp.ofVal (Val.lit (.int m)))⟧ Φ :=
  fun h => wp_binop (wp_val (wp_val ⟨_, by simp [BinOp.eval], h⟩))

@[scoped spec 2100] theorem spec_binop_mod {n m : Int} {Φ : Val → Prop} :
    Φ (Val.lit (.int (n.tmod m)))
      ⊑ wp⟦Exp.binop BinOp.tmod (Exp.ofVal (Val.lit (.int n))) (Exp.ofVal (Val.lit (.int m)))⟧ Φ :=
  fun h => wp_binop (wp_val (wp_val ⟨_, by simp [BinOp.eval], h⟩))

/-- Integer equality test (every codec guard is one): returns the concrete boolean `n == m`. -/
@[scoped spec 2100] theorem spec_binop_eq {n m : Int} {Φ : Val → Prop} :
    Φ (Val.lit (.bool (n == m)))
      ⊑ wp⟦Exp.binop BinOp.eq (Exp.ofVal (Val.lit (.int n))) (Exp.ofVal (Val.lit (.int m)))⟧ Φ := by
  intro h
  refine wp_binop (wp_val (wp_val ⟨Val.lit (.bool (n == m)), ?_, h⟩))
  simp [BinOp.eval, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]; grind

/-- Focus the left operand of a binop whose right operand is already a value. -/
@[scoped spec 1500] theorem spec_binopL {op : BinOp} {e₁ : Exp} {v₂ : Val} {Φ : Val → Prop} :
    wp⟦e₁⟧ (fun v => wp⟦Exp.binop op (Exp.ofVal v) (Exp.ofVal v₂)⟧ Φ)
      ⊑ wp⟦Exp.binop op e₁ (Exp.ofVal v₂)⟧ Φ := fun h => wp_bind (ECtxItem.binOpL op v₂) h

/-- Focus the right operand of a binop (evaluated first in HeapLang); general, lower priority. -/
@[scoped spec 1200] theorem spec_binopR {op : BinOp} {e₁ e₂ : Exp} {Φ : Val → Prop} :
    wp⟦e₂⟧ (fun v => wp⟦Exp.binop op e₁ (Exp.ofVal v)⟧ Φ) ⊑ wp⟦Exp.binop op e₁ e₂⟧ Φ :=
  fun h => wp_bind (ECtxItem.binOpR op e₁) h

/-- Focus an `if` scrutinee. -/
@[scoped spec 1500] theorem spec_if_bind {e₀ e₁ e₂ : Exp} {Φ : Val → Prop} :
    wp⟦e₀⟧ (fun vc => wp⟦Exp.if (Exp.ofVal vc) e₁ e₂⟧ Φ) ⊑ wp⟦Exp.if e₀ e₁ e₂⟧ Φ :=
  fun h => wp_bind (ECtxItem.if e₁ e₂) h

/-- `if` on a literal boolean. -/
@[scoped spec 2000] theorem spec_if_lit {b : Bool} {e₁ e₂ : Exp} {Φ : Val → Prop} :
    wp⟦if b then e₁ else e₂⟧ Φ ⊑ wp⟦Exp.if (Exp.ofVal (Val.lit (.bool b))) e₁ e₂⟧ Φ :=
  fun h => wp_cond (wp_val ⟨b, rfl, h⟩)

end

end Auto

/-- Turn a closed spec `True ⊑ wp⟦e⟧ (· = r)` into its continuation-passing form
`Φ r ⊑ wp⟦e⟧ Φ` (for an arbitrary postcondition `Φ`). Apply to the *fully-applied* closed spec,
including whatever discharges its `True` precondition, e.g. `by derive_cps (foo_spec l trivial)`.

The CPS form is what makes composition/round-trips reduce to plain `vcgen`: with `Φ` a variable there
is nothing to frame, so `@[spec]`-registering the CPS wrapper lets `vcgen` compose call sites
directly. See `DeltaRoundtrip.lean` / `RleRoundtrip.lean`. -/
scoped macro "derive_cps" spec:term : tactic =>
  `(tactic| (intro h; refine wp_mono ?_ ($spec); intro v hv; subst hv; exact h))

end Iris.HeapLang.Ax
