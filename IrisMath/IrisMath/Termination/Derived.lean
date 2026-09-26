/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import IrisMath.TimeCredits

/-! # The rules of the termination logic

This file ports `theories/examples/termination/derived.v` of Transfinite Iris: the rules of the
termination logic of the paper, derived from the sequential refinement weakest precondition
`seq` for the ordinal source (time credits `tc α`).

The Hoare triples `{{ P }} e {{ v, Q v }}` (Rocq notation) are written
`termTriple P e Q := □ (P -∗ seq ⊤ e Q)`, and the step triples `⟨⟨ P ⟩⟩ e ⟨⟨ v, Q v ⟩⟩` are
`stepTriple P e Q := □ (P -∗ seqRswp ⊤ e Q)`.
-/

@[expose] public noncomputable section

universe w v u

namespace Iris.Transfinite.Termination

open Iris Iris.Std Iris.BI Iris.HeapLang Iris.HeapLang.Transfinite ProgramLogic Language
open Language.Notation Ordinal

variable {SI : Type v} [instSI : Iris.SIdx SI]
local stepindex SI

variable {GF : BundledGFunctors.{u}} [Hheap : HeapLangTGS GF] [Htc : TcGS.{w} GF] [Hseq : SeqG GF]

/-- The sequential strong refinement weakest precondition (Rocq: `seq_rswp`). -/
def seqRswp (E : CoPset) (e : Exp) (φ : Val → IProp GF) : IProp GF :=
  iprop(NonAtomicInvariant.own Hseq.name E -∗
    rswp (src := tcSource) (ι := heapRefIrisGS) 0 .NotStuck ⊤ e
      fun v => iprop(NonAtomicInvariant.own Hseq.name E ∗ φ v))

/-- The sequential weakest precondition for time credits. -/
abbrev tseq (E : CoPset) (e : Exp) (φ : Val → IProp GF) : IProp GF :=
  seq (src := tcSource.{w}) (ι := heapRefIrisGS) E e φ

/-- Rocq: `{{ P }} e {{ v, Q }}`. -/
def termTriple (P : IProp GF) (e : Exp) (Q : Val → IProp GF) : IProp GF :=
  iprop(□ (P -∗ tseq.{w} ⊤ e Q))

/-- Rocq: `⟨⟨ P ⟩⟩ e ⟨⟨ v, Q ⟩⟩`. -/
def stepTriple (P : IProp GF) (e : Exp) (Q : Val → IProp GF) : IProp GF :=
  iprop(□ (P -∗ seqRswp.{w} ⊤ e Q))

instance termTriple_persistent (P : IProp GF) (e : Exp) (Q : Val → IProp GF) :
    Persistent (termTriple.{w} P e Q) := by
  unfold termTriple; infer_instance

instance stepTriple_persistent (P : IProp GF) (e : Exp) (Q : Val → IProp GF) :
    Persistent (stepTriple.{w} P e Q) := by
  unfold stepTriple; infer_instance

/-- Rocq: `value_term`. -/
theorem value_term (v : Val) :
    ⊢ termTriple.{w} (GF := GF) iprop(True) (v : Exp) fun w => iprop(⌜v = w⌝) := by
  unfold termTriple tseq seq
  iintro !> - Hna
  iapply rwp_value'
  iframe
  ipureintro; rfl

/-- Rocq: `bind_term`. -/
theorem bind_term (e : Exp) (K : List ECtxItem) (P : IProp GF) (Q R : Val → IProp GF) :
    termTriple.{w} P e Q ∗ (∀ v : Val, termTriple.{w} (Q v) (fill K (v : Exp)) R) ⊢
      termTriple.{w} P (fill K e) R := by
  unfold termTriple tseq seq
  iintro ⟨#H1, #H2⟩ !> HP Hna
  iapply rwp_bind (fill K)
  ihave H := H1 $$ HP Hna
  iapply rwp_strong_mono (Std.IsPreorder.le_refl _) LawfulSet.subset_refl $$ H
  iintro %v ⟨Hna, HQ⟩
  imodintro
  iapply H2 $$ HQ Hna

/-- Rocq: `pure_term`. -/
theorem pure_term (e e' : Exp) (P : IProp GF) (Q : Val → IProp GF) (hstep : e -ᵖ-> e') :
    termTriple.{w} P e' Q ⊢ stepTriple.{w} P e Q := by
  unfold termTriple stepTriple tseq seq seqRswp
  iintro #H !> HP Hna
  haveI : PureExec True 1 e e' := ⟨fun _ => .once hstep⟩
  iapply rswp_pure_step_later trivial
  iapply H $$ HP Hna

/-- Rocq: `store_term`. -/
theorem store_term (l : Loc) (v₁ v₂ : Val) :
    ⊢ stepTriple.{w} (GF := GF) iprop(l ↦ some v₁) hl(v(#l) ← &v₂)
      fun w => iprop(⌜w = hl_val(#())⌝ ∗ l ↦ some v₂) := by
  unfold stepTriple seqRswp
  iintro !> Hl Hna
  iapply rswp_store $$ Hl
  iintro Hl
  dsimp only
  iframe
  ipureintro; rfl

/-- Rocq: `load_term`. -/
theorem load_term (l : Loc) (v : Val) :
    ⊢ stepTriple.{w} (GF := GF) iprop(l ↦ some v) hl(!v(#l))
      fun w => iprop(⌜w = v⌝ ∗ l ↦ some v) := by
  unfold stepTriple seqRswp
  iintro !> Hl Hna
  iapply rswp_load $$ Hl
  iintro Hl
  dsimp only
  iframe
  ipureintro; rfl

/-- Rocq: `ref_term`. -/
theorem ref_term (v : Val) :
    ⊢ stepTriple.{w} (GF := GF) iprop(True) hl(ref(&v))
      fun w => iprop(∃ l : Loc, ⌜w = hl_val(#l)⌝ ∗ l ↦ some v) := by
  unfold stepTriple seqRswp
  iintro !> - Hna
  iapply rswp_alloc
  iintro %l Hl
  iframe
  iexists l
  iframe
  ipureintro; rfl

/-- Rocq: `flip_term`. -/
theorem flip_term (e : Exp) (P : IProp GF) (Q : Val → IProp GF) (he : toVal e = none) :
    stepTriple.{w} P e Q ⊢ termTriple.{w} P e Q := by
  unfold stepTriple termTriple tseq seq seqRswp
  iintro #H !> HP Hna
  iapply rwp_no_step he
  iapply H $$ HP Hna

/-- Rocq: `spend_cred_term`. -/
theorem spend_cred_term (P : IProp GF) (e : Exp) (Q : Val → IProp GF) {α β : Ordinal.{w}}
    (he : toVal e = none) (hlt : β < α) :
    stepTriple.{w} iprop(tc β ∗ P) e Q ⊢ termTriple.{w} iprop(tc α ∗ ▷ P) e Q := by
  unfold stepTriple termTriple tseq seq seqRswp
  iintro #H !> ⟨Hc, HP⟩ Hna
  iapply rwp_take_step (P := tc (GF := GF) β) he $$ [Hna HP] [Hc]
  · iintro Hβ
    iapply rswp_do_step
    inext
    iapply H $$ [Hβ HP] Hna
    iframe
  · iapply tc_update ⊤ hlt $$ Hc

/-- Rocq: `split_cred_term`. -/
theorem split_cred_term (α β : Ordinal.{w}) : tc (GF := GF) (α ♯ β) ⊣⊢ tc α ∗ tc β :=
  tc_split α β

end Iris.Transfinite.Termination
