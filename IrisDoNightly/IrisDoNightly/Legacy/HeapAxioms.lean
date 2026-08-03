module

public import IrisDoNightly.Legacy.SepLogic
public import Std.Internal
public import Std.Tactic.Do

set_option mvcgen.warning false

open Lean.Order
open Iris.HeapLang

@[expose] public section

namespace Iris.HeapLang.SL

def hpure (φ : Prop) : HProp := fun _ => φ
def hand (P Q : HProp) : HProp := fun σ => P σ ∧ Q σ
def hexists {α : Sort _} (P : α → HProp) : HProp := fun σ => ∃ a, P a σ
def hor (P Q : HProp) : HProp := fun σ => P σ ∨ Q σ

/-! ## The axiomatic interface -/

/-- A predicate `wp` imbues a fragment of HeapLang with the correct separation-logic axiomatic
semantics. The pure structural fields are `AxSem.HeapLangAxioms` with `→` replaced by `⊑`; the heap
fields are the small-footprint rules over `↦`. -/
class HeapLangAxioms (wp : Exp → (Val → HProp) → HProp) where
  wp_mono : Φ ⊑ Ψ → wp e Φ ⊑ wp e Ψ
  /-- The frame rule: a resource `F` disjoint from the footprint of `e` commutes into the
  postcondition. This is the separation-logic content that makes `vcgen`'s frame procedure sound;
  it is not derivable from the structural rules alone. -/
  wp_frame (F : HProp) : sepConj F (wp e Φ) ⊑ wp e (fun v => sepConj F (Φ v))
  /-- The bind / evaluation-context rule: to run `K[e]`, first run `e`, then plug its value into the
  hole.  This is what lets the primitive rules (which fire on literal-value operands) reach
  *computed* operands such as a `l +ₗ i` address. -/
  wp_bind (K : ECtxItem) : wp e (fun v => wp (K.fill (Exp.ofVal v)) Φ) ⊑ wp (K.fill e) Φ
  wp_val : Φ v ⊑ wp (Exp.ofVal v) Φ
  wp_closure : Φ (.rec_ f x e) ⊑ wp (Exp.rec_ f x e) Φ
  wp_app :
    wp e₂ (fun v₂ => wp e₁ (fun vf => hexists fun (f : Binder) => hexists fun (x : Binder) =>
      hexists fun (body : Exp) => hand (hpure (vf = Val.rec_ f x body))
        (wp ((body.subst f (.rec_ f x body)).subst x v₂) Φ)))
      ⊑ wp (Exp.app e₁ e₂) Φ
  wp_unop :
    wp e (fun v => hexists fun v' => hand (hpure (op.eval v = some v')) (Φ v'))
      ⊑ wp (Exp.unop op e) Φ
  wp_binop :
    wp e₂ (fun v₂ => wp e₁ (fun v₁ => hexists fun v' => hand (hpure (op.eval v₁ v₂ = some v')) (Φ v')))
      ⊑ wp (Exp.binop op e₁ e₂) Φ
  wp_cond :
    wp e₀ (fun vc => hexists fun b => hand (hpure (vc = Val.lit (.bool b))) (wp (if b then e₁ else e₂) Φ))
      ⊑ wp (Exp.if e₀ e₁ e₂) Φ
  wp_pair :
    wp e₂ (fun v₂ => wp e₁ (fun v₁ => Φ (Val.pair v₁ v₂)))
      ⊑ wp (Exp.pair e₁ e₂) Φ
  wp_fst :
    wp e (fun v => hexists fun v₁ => hexists fun v₂ => hand (hpure (v = Val.pair v₁ v₂)) (Φ v₁))
      ⊑ wp (Exp.fst e) Φ
  wp_snd :
    wp e (fun v => hexists fun v₁ => hexists fun v₂ => hand (hpure (v = Val.pair v₁ v₂)) (Φ v₂))
      ⊑ wp (Exp.snd e) Φ
  wp_injL : wp e (fun v => Φ (Val.injL v)) ⊑ wp (Exp.injL e) Φ
  wp_injR : wp e (fun v => Φ (Val.injR v)) ⊑ wp (Exp.injR e) Φ
  wp_case :
    wp e₀ (fun vc =>
      hor (hexists fun v => hand (hpure (vc = Val.injL v)) (wp (Exp.app e₁ (Exp.ofVal v)) Φ))
          (hexists fun v => hand (hpure (vc = Val.injR v)) (wp (Exp.app e₂ (Exp.ofVal v)) Φ)))
      ⊑ wp (Exp.case e₀ e₁ e₂) Φ
  wp_load (l : Loc) (w : Val) :
    pointsTo l w ⊑ wp (Exp.load (Exp.ofVal (Val.lit (.loc l))))
      (fun v => hand (hpure (v = w)) (pointsTo l w))
  wp_store (l : Loc) (v w : Val) :
    pointsTo l v ⊑ wp (Exp.store (Exp.ofVal (Val.lit (.loc l))) (Exp.ofVal w))
      (fun _ => pointsTo l w)
  wp_alloc (w : Val) :
    emp ⊑ wp (Exp.allocN (Exp.ofVal (Val.lit (.int 1))) (Exp.ofVal w))
      (fun v => hexists fun l => hand (hpure (v = Val.lit (.loc l))) (pointsTo l w))
  wp_allocN (n : Nat) (w : Val) : 0 < n →
    emp ⊑ wp (Exp.allocN (Exp.ofVal (Val.lit (.int n))) (Exp.ofVal w))
      (fun v => hexists fun l => hand (hpure (v = Val.lit (.loc l)))
        (arrayPointsTo l (List.replicate n w)))
  wp_free (l : Loc) (w : Val) :
    pointsTo l w ⊑ wp (Exp.free (Exp.ofVal (Val.lit (.loc l)))) (fun _ => emp)

open Std.Internal.Do HeapLangAxioms

/-! ## The `Std.Do` `WP` instance -/

set_option synthInstance.checkSynthOrder false in
instance instWP_SL {wp} [HeapLangAxioms wp] : WP Exp Val HProp EPost.Nil where
  wpTrans e := ⟨fun Φ _ => wp e Φ⟩
  wp_trans_monotone _ _ _ _ _ _ hp := wp_mono hp

/-- Local notation for a `Std.Do` weakest precondition. -/
scoped syntax:max "wp⟦" term:min "⟧" ppSpace term:max : term
scoped macro_rules
  | `(wp⟦ $e ⟧ $Φ) => `(Std.Internal.Do.wp $e $Φ Std.Internal.Do.EPost.Nil.mk)

@[grind .] theorem sl_frames {wp} [HeapLangAxioms wp] (e : Exp) (F : HProp) :
    WP.Frames sepConj e F where
  op_wp_le_wp_op _ _ := wp_frame F

/-! ## The `@[spec]` laws -/

section laws
variable {wp} [HeapLangAxioms wp]

@[spec] theorem spec_val {v : Val} {Φ : Val → HProp} :
    Φ v ⊑ wp⟦(Exp.ofVal v : Exp)⟧ Φ := wp_val

@[spec] theorem spec_rec {f x : Binder} {e : Exp} {Φ : Val → HProp} :
    Φ (.rec_ f x e) ⊑ wp⟦Exp.rec_ f x e⟧ Φ := wp_closure

@[spec] theorem spec_app {e₁ e₂ : Exp} {Φ : Val → HProp} :
    wp⟦e₂⟧ (fun v₂ => wp⟦e₁⟧ (fun vf => hexists fun (f : Binder) => hexists fun (x : Binder) =>
        hexists fun (body : Exp) => hand (hpure (vf = Val.rec_ f x body))
          (wp⟦(body.subst f (.rec_ f x body)).subst x v₂⟧ Φ)))
      ⊑ wp⟦Exp.app e₁ e₂⟧ Φ := wp_app

/-- Application of a *literal* lambda/closure (as produced by `let`/`λ` sugar): reduces directly to
the substituted body, skipping the closure-match existential of `spec_app`.  This is the ergonomic
rule `vcgen` uses to step through `let`-bindings. -/
@[spec] theorem spec_app_lam {f x : Binder} {body e₂ : Exp} {Φ : Val → HProp} :
    wp⟦e₂⟧ (fun v₂ => wp⟦(body.subst f (.rec_ f x body)).subst x v₂⟧ Φ)
      ⊑ wp⟦Exp.app (Exp.rec_ f x body) e₂⟧ Φ := by
  refine PartialOrder.rel_trans ?_ wp_app
  refine wp_mono ?_
  intro v₂
  refine PartialOrder.rel_trans ?_ wp_closure
  intro σ hσ
  exact ⟨f, x, body, rfl, hσ⟩

@[spec] theorem spec_unop {op : UnOp} {e : Exp} {Φ : Val → HProp} :
    wp⟦e⟧ (fun v => hexists fun v' => hand (hpure (op.eval v = some v')) (Φ v'))
      ⊑ wp⟦Exp.unop op e⟧ Φ := wp_unop

@[spec] theorem spec_binop {op : BinOp} {e₁ e₂ : Exp} {Φ : Val → HProp} :
    wp⟦e₂⟧ (fun v₂ => wp⟦e₁⟧ (fun v₁ => hexists fun v' => hand (hpure (op.eval v₁ v₂ = some v')) (Φ v')))
      ⊑ wp⟦Exp.binop op e₁ e₂⟧ Φ := wp_binop

@[spec] theorem spec_if {e₀ e₁ e₂ : Exp} {Φ : Val → HProp} :
    wp⟦e₀⟧ (fun vc => hexists fun b => hand (hpure (vc = Val.lit (.bool b))) (wp⟦if b then e₁ else e₂⟧ Φ))
      ⊑ wp⟦Exp.if e₀ e₁ e₂⟧ Φ := wp_cond

@[spec] theorem spec_pair {e₁ e₂ : Exp} {Φ : Val → HProp} :
    wp⟦e₂⟧ (fun v₂ => wp⟦e₁⟧ (fun v₁ => Φ (Val.pair v₁ v₂)))
      ⊑ wp⟦Exp.pair e₁ e₂⟧ Φ := wp_pair

@[spec] theorem spec_fst {e : Exp} {Φ : Val → HProp} :
    wp⟦e⟧ (fun v => hexists fun v₁ => hexists fun v₂ => hand (hpure (v = Val.pair v₁ v₂)) (Φ v₁))
      ⊑ wp⟦Exp.fst e⟧ Φ := wp_fst

@[spec] theorem spec_snd {e : Exp} {Φ : Val → HProp} :
    wp⟦e⟧ (fun v => hexists fun v₁ => hexists fun v₂ => hand (hpure (v = Val.pair v₁ v₂)) (Φ v₂))
      ⊑ wp⟦Exp.snd e⟧ Φ := wp_snd

@[spec] theorem spec_injL {e : Exp} {Φ : Val → HProp} :
    wp⟦e⟧ (fun v => Φ (Val.injL v)) ⊑ wp⟦Exp.injL e⟧ Φ := wp_injL

@[spec] theorem spec_injR {e : Exp} {Φ : Val → HProp} :
    wp⟦e⟧ (fun v => Φ (Val.injR v)) ⊑ wp⟦Exp.injR e⟧ Φ := wp_injR

@[spec] theorem spec_case {e₀ e₁ e₂ : Exp} {Φ : Val → HProp} :
    wp⟦e₀⟧ (fun vc =>
        hor (hexists fun v => hand (hpure (vc = Val.injL v)) (wp⟦Exp.app e₁ (Exp.ofVal v)⟧ Φ))
            (hexists fun v => hand (hpure (vc = Val.injR v)) (wp⟦Exp.app e₂ (Exp.ofVal v)⟧ Φ)))
      ⊑ wp⟦Exp.case e₀ e₁ e₂⟧ Φ := wp_case

@[spec] theorem spec_load (l : Loc) (w : Val) :
    pointsTo l w ⊑ wp⟦Exp.load (Exp.ofVal (Val.lit (.loc l)))⟧
      (fun v => hand (hpure (v = w)) (pointsTo l w)) := wp_load l w

@[spec] theorem spec_store (l : Loc) (v w : Val) :
    pointsTo l v ⊑ wp⟦Exp.store (Exp.ofVal (Val.lit (.loc l))) (Exp.ofVal w)⟧
      (fun _ => pointsTo l w) := wp_store l v w

@[spec] theorem spec_alloc (w : Val) :
    emp ⊑ wp⟦Exp.allocN (Exp.ofVal (Val.lit (.int 1))) (Exp.ofVal w)⟧
      (fun v => hexists fun l => hand (hpure (v = Val.lit (.loc l))) (pointsTo l w)) := wp_alloc w

@[spec] theorem spec_allocN (n : Nat) (w : Val) (h : 0 < n) :
    emp ⊑ wp⟦Exp.allocN (Exp.ofVal (Val.lit (.int n))) (Exp.ofVal w)⟧
      (fun v => hexists fun l => hand (hpure (v = Val.lit (.loc l)))
        (arrayPointsTo l (List.replicate n w))) := wp_allocN n w h

@[spec] theorem spec_free (l : Loc) (w : Val) :
    pointsTo l w ⊑ wp⟦Exp.free (Exp.ofVal (Val.lit (.loc l)))⟧ (fun _ => emp) := wp_free l w

/-- Load at a *computed* address `l +ₗ i`.  Derived from `wp_bind` (evaluate the address) +
`spec_binop` (compute the offset) + `wp_load`. -/
@[spec] theorem spec_load_offset (l : Loc) (i : Int) (w : Val) :
    pointsTo (l + i) w ⊑
      wp⟦Exp.load (Exp.binop BinOp.offset (Exp.ofVal (Val.lit (.loc l))) (Exp.ofVal (Val.lit (.int i))))⟧
        (fun v => hand (hpure (v = w)) (pointsTo (l + i) w)) := by
  refine PartialOrder.rel_trans ?_ (wp_bind ECtxItem.load)
  refine PartialOrder.rel_trans ?_ spec_binop
  refine PartialOrder.rel_trans ?_ spec_val
  refine PartialOrder.rel_trans ?_ spec_val
  intro σ hσ
  exact ⟨Val.lit (.loc (l + i)), rfl, wp_load (l + i) w σ hσ⟩

/-- Store at a *computed* address `l +ₗ i`. -/
@[spec] theorem spec_store_offset (l : Loc) (i : Int) (v w : Val) :
    pointsTo (l + i) v ⊑
      wp⟦Exp.store (Exp.binop BinOp.offset (Exp.ofVal (Val.lit (.loc l))) (Exp.ofVal (Val.lit (.int i)))) (Exp.ofVal w)⟧
        (fun _ => pointsTo (l + i) w) := by
  refine PartialOrder.rel_trans ?_ (wp_bind (ECtxItem.storeL w))
  refine PartialOrder.rel_trans ?_ spec_binop
  refine PartialOrder.rel_trans ?_ spec_val
  refine PartialOrder.rel_trans ?_ spec_val
  intro σ hσ
  exact ⟨Val.lit (.loc (l + i)), rfl, wp_store (l + i) v w σ hσ⟩

end laws
end Iris.HeapLang.SL
