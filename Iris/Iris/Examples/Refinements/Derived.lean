/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.Examples.Refinements.Examples

/-! # The rules of the refinement logic

This file ports `theories/examples/refinements/derived.v` of Transfinite Iris: the rules of the
refinement logic of the paper, derived from the sequential refinement weakest precondition. The
Hoare triples `{{ P }} e {{ v, Q v }}` (Rocq notation) are `hoare P e Q`, and the step triples
`⟨⟨ P ⟩⟩ e ⟨⟨ v, Q v ⟩⟩` are `stepHoare P e Q`.
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite.Refinement.Derived

open Iris Iris.Std Iris.BI Iris.HeapLang Iris.HeapLang.Transfinite ProgramLogic Language
open Language.Notation Iris.Transfinite.Refinement.Examples

set_option linter.unusedSectionVars false

variable {GF : BundledGFunctors} [G : RHeapG GF] [N : NatSourceG GF] [S : SeqG GF]

/-- Rocq: `seq_rswp`. -/
def seqRswp (E : CoPset) (e : Exp) (φ : Val → IProp GF) : IProp GF :=
  iprop(NonAtomicInvariant.own S.name E -∗
    rswp (src := refSrc (GF := GF)) (ι := heapRefIrisGS) 0 .NotStuck ⊤ e
      fun v => iprop(NonAtomicInvariant.own S.name E ∗ φ v))

/-- Rocq: `{{ P }} e {{ v, Q v }}`. -/
def hoare (P : IProp GF) (e : Exp) (Q : Val → IProp GF) : IProp GF :=
  iprop(□ (P -∗ rseq ⊤ e Q))

/-- Rocq: `⟨⟨ P ⟩⟩ e ⟨⟨ v, Q v ⟩⟩`. -/
def stepHoare (P : IProp GF) (e : Exp) (Q : Val → IProp GF) : IProp GF :=
  iprop(□ (P -∗ seqRswp ⊤ e Q))

instance hoare_persistent (P : IProp GF) (e : Exp) (Q : Val → IProp GF) :
    Persistent (hoare P e Q) := by
  unfold hoare; infer_instance

instance stepHoare_persistent (P : IProp GF) (e : Exp) (Q : Val → IProp GF) :
    Persistent (stepHoare P e Q) := by
  unfold stepHoare; infer_instance

/-- Rocq: `|==>src P`. -/
abbrev srcModality (P : IProp GF) : IProp GF := weakSrcUpd ⊤ P

/-- Rocq: `Conseq`. -/
theorem conseq (e : Exp) (P P' : IProp GF) (Q Q' : Val → IProp GF) (h₁ : P ⊢ P')
    (h₂ : ∀ v, Q' v ⊢ Q v) : hoare P' e Q' ⊢ hoare P e Q := by
  unfold hoare rseq seq
  iintro #H !> HP Hna
  ihave HP := h₁ $$ HP
  ihave H := H $$ HP Hna
  iapply rwpR_wand $$ H
  iintro %v ⟨Hna, HQ⟩
  iframe
  iapply h₂ v $$ HQ

/-- Rocq: `HoareExists`. -/
theorem hoare_exists {X : Type _} (e : Exp) (P : X → IProp GF) (Q : Val → IProp GF) :
    (∀ x, hoare (P x) e Q) ⊢ hoare iprop(∃ x, P x) e Q := by
  unfold hoare
  iintro #H !> ⟨%x, HP⟩
  iapply H $$ %x HP

/-- Rocq: `HoarePure`. -/
theorem hoare_pure (e : Exp) (φ : Prop) (P : IProp GF) (Q : Val → IProp GF) (h : P ⊢ ⌜φ⌝) :
    (⌜φ⌝ -∗ hoare P e Q) ⊢ hoare P e Q := by
  unfold hoare
  iintro #H !> HP
  ihave HP := (and_intro h .rfl) $$ HP
  icases HP with ⟨%hφ, HP⟩
  iapply H $$ %hφ HP

/-- Rocq: `Value`. -/
theorem value_rule (v : Val) : ⊢ hoare (GF := GF) iprop(True) (v : Exp) fun w => iprop(⌜v = w⌝) := by
  unfold hoare rseq seq
  iintro !> - Hna
  iapply rwp_value' (src := refSrc (GF := GF))
  iframe
  ipureintro; rfl

/-- Rocq: `Frame`. -/
theorem frame_rule (e : Exp) (P R : IProp GF) (Q : Val → IProp GF) :
    hoare P e Q ⊢ hoare iprop(P ∗ R) e fun v => iprop(Q v ∗ R) := by
  unfold hoare rseq seq
  iintro #H !> ⟨HP, HR⟩ Hna
  ihave H := H $$ HP Hna
  iapply rwpR_wand $$ H
  iintro %v ⟨Hna, HQ⟩
  dsimp only
  iframe

/-- Rocq: `Bind`. -/
theorem bind_rule (e : Exp) (K : List ECtxItem) (P : IProp GF) (Q R : Val → IProp GF) :
    hoare P e Q ∗ (∀ v : Val, hoare (Q v) (fill K (v : Exp)) R) ⊢ hoare P (fill K e) R := by
  unfold hoare rseq seq
  iintro ⟨#H₁, #H₂⟩ !> HP Hna
  iapply rwp_bind (src := refSrc (GF := GF)) (fill K)
  ihave H := H₁ $$ HP Hna
  iapply rwp_strong_mono (src := refSrc (GF := GF)) (Std.IsPreorder.le_refl _)
    LawfulSet.subset_refl $$ H
  iintro %v ⟨Hna, HQ⟩
  imodintro
  iapply H₂ $$ %v HQ Hna

/-- Rocq: `Löb`. -/
theorem loeb_rule (P : IProp GF) : (▷ P → P) ⊢ P := BI.loeb

theorem fill_ne {K : List ECtxItem} {e₁ e₂ : Exp} (h : e₁ ≠ e₂) : fill K e₁ ≠ fill K e₂ :=
  fun heq => h (EvContext.fill_inj heq)

/-- Rocq: `TPPureT`. -/
theorem tp_pure_t (e e' : Exp) (P : IProp GF) (Q : Val → IProp GF) (hstep : e -ᵖ-> e') :
    hoare P e' Q ⊢ stepHoare P e Q := by
  unfold hoare stepHoare rseq seq seqRswp
  iintro #H !> HP Hna
  haveI : PureExec True 1 e e' := ⟨fun _ => .once hstep⟩
  iapply rswp_pure_step_later (src := refSrc (GF := GF)) (k := 0) trivial
  iapply H $$ HP Hna

/-- Rocq: `TPPureS`. -/
theorem tp_pure_s (e e' et : Exp) (K : List ECtxItem) (P : IProp GF) (Q : Val → IProp GF)
    (he : ToVal.toVal et = none) (hstep : e -ᵖ-> e') :
    stepHoare iprop(src (fill K e') ∗ P) et Q ⊢ hoare iprop(src (fill K e) ∗ ▷ P) et Q := by
  unfold hoare stepHoare rseq seq seqRswp
  iintro #H !> ⟨Hsrc, HP⟩ Hna
  iapply rwp_take_step (src := refSrc (GF := GF)) (P := src (fill K e')) he $$ [HP Hna] [Hsrc]
  · iintro Hsrc
    iapply rswp_do_step (src := refSrc (GF := GF))
    inext
    iapply H $$ [Hsrc HP] Hna
    iframe
  · iapply step_pure ⊤ 0 _ _ (purePrimStep_fill (fill K) hstep) $$ Hsrc

/-- Rocq: `TPStoreT`. -/
theorem tp_store_t (l : Loc) (v₁ v₂ : Val) :
    ⊢ stepHoare (GF := GF) iprop(l ↦ some v₁) hl(v(#l) ← &v₂)
      fun w => iprop(⌜w = hl_val(#())⌝ ∗ l ↦ some v₂) := by
  unfold stepHoare seqRswp
  iintro !> Hl Hna
  iapply rswp_store (src := refSrc (GF := GF)) $$ Hl
  iintro Hl
  dsimp only
  iframe
  ipureintro; rfl

/-- Rocq: `TPStoreS`. -/
theorem tp_store_s (et : Exp) (l : Loc) (v₁ v₂ : Val) (K : List ECtxItem) (P : IProp GF)
    (Q : Val → IProp GF) (he : ToVal.toVal et = none) :
    stepHoare iprop(P ∗ src (fill K hl(#())) ∗ heapSPointsTo l (.own 1) v₂) et Q ⊢
      hoare iprop(src (fill K hl(v(#l) ← &v₂)) ∗ heapSPointsTo l (.own 1) v₁ ∗ ▷ P) et Q := by
  unfold hoare stepHoare rseq seq seqRswp
  iintro #H !> ⟨Hsrc, Hl, HP⟩ Hna
  iapply rwp_take_step (src := refSrc (GF := GF))
    (P := iprop(src (fill K hl(#())) ∗ heapSPointsTo l (.own 1) v₂)) he $$ [HP Hna] [Hsrc Hl]
  · iintro ⟨Hsrc, Hl⟩
    iapply rswp_do_step (src := refSrc (GF := GF))
    inext
    iapply H $$ [Hsrc HP Hl] Hna
    iframe
  · iapply step_store ⊤ 0 K l v₂ v₁
    iframe

/-- Rocq: `TPStutterT`. -/
theorem tp_stutter_t (e : Exp) (P : IProp GF) (Q : Val → IProp GF) (he : ToVal.toVal e = none) :
    stepHoare P e Q ⊢ hoare P e Q := by
  unfold hoare stepHoare rseq seq seqRswp
  iintro #H !> HP Hna
  iapply rwp_no_step (src := refSrc (GF := GF)) he
  iapply H $$ HP Hna

/-- Rocq: `TPStutterSStore`. -/
theorem tp_stutter_s_store (et : Exp) (v₁ v₂ : Val) (K : List ECtxItem) (l : Loc) (P : IProp GF)
    (Q : Val → IProp GF) (he : ToVal.toVal et = none) :
    hoare iprop(P ∗ src (fill K hl(#())) ∗ heapSPointsTo l (.own 1) v₂) et Q ⊢
      hoare iprop(heapSPointsTo l (.own 1) v₁ ∗ src (fill K hl(v(#l) ← &v₂)) ∗ P) et Q := by
  unfold hoare rseq seq
  iintro #H !> ⟨Hl, Hsrc, HP⟩ Hna
  iapply rwp_weaken (src := refSrc (GF := GF))
    (P := iprop(src (fill K hl(#())) ∗ heapSPointsTo l (.own 1) v₂)) he $$ [HP Hna] [Hsrc Hl]
  · iintro ⟨Hsrc, Hl⟩
    iapply H $$ [Hsrc HP Hl] Hna
    iframe
  · iapply step_store ⊤ 0 K l v₂ v₁
    iframe

/-- Rocq: `TPStutterSPure`. -/
theorem tp_stutter_s_pure (et es es' : Exp) (P : IProp GF) (Q : Val → IProp GF)
    (he : ToVal.toVal et = none) (hstep : es -ᵖ-> es') :
    hoare iprop(P ∗ src es') et Q ⊢ hoare iprop(P ∗ src es) et Q := by
  unfold hoare rseq seq
  iintro #H !> ⟨HP, Hsrc⟩ Hna
  iapply rwp_weaken (src := refSrc (GF := GF)) (P := src es') he $$ [HP Hna] [Hsrc]
  · iintro Hsrc
    iapply H $$ [Hsrc HP] Hna
    iframe
  · iapply step_pure ⊤ 0 _ _ hstep $$ Hsrc

/-- Rocq: `HoareLöb`. -/
theorem hoare_loeb {X : Type _} (P : X → IProp GF) (Q : X → Val → IProp GF) (e : X → Exp) :
    (∀ x, hoare iprop(P x ∗ ▷ (∀ x, hoare (P x) (e x) (Q x))) (e x) (Q x)) ⊢
      ∀ x, hoare (P x) (e x) (Q x) := by
  iintro #H
  iloeb as IH
  iintro %x
  unfold hoare
  iintro !> HP
  ihave H' := H $$ %x
  iapply H' $$ [HP]
  iframe HP
  iexact IH

/-- Rocq: `HoareLöbNoArgs`. -/
theorem hoare_loeb_no_args (P : IProp GF) (Q : Val → IProp GF) (e : Exp) :
    hoare iprop(P ∗ ▷ hoare P e Q) e Q ⊢ hoare P e Q := by
  iintro #H
  iloeb as IH
  unfold hoare
  iintro !> HP
  iapply H $$ [HP]
  iframe HP
  iexact IH

/-- Rocq: `value_tgt_tpr`. -/
theorem value_tgt_tpr (v : Val) :
    ⊢ hoare (GF := GF) iprop(True) (v : Exp) fun w => iprop(⌜v = w⌝) := value_rule v

/-- Rocq: `bind_tgt_tpr`. -/
theorem bind_tgt_tpr (e : Exp) (K : List ECtxItem) (P : IProp GF) (Q R : Val → IProp GF) :
    hoare P e Q ∗ (∀ v : Val, hoare (Q v) (fill K (v : Exp)) R) ⊢ hoare P (fill K e) R :=
  bind_rule e K P Q R

/-- Rocq: `pure_tgt_tpr`. -/
theorem pure_tgt_tpr (e e' : Exp) (P : IProp GF) (Q : Val → IProp GF) (hstep : e -ᵖ-> e') :
    hoare P e' Q ⊢ stepHoare P e Q := tp_pure_t e e' P Q hstep

/-- Rocq: `pure_src_tpr`. -/
theorem pure_src_tpr (e e' et : Exp) (K : List ECtxItem) (P : IProp GF) (Q : Val → IProp GF)
    (he : ToVal.toVal et = none) (hstep : e -ᵖ-> e') :
    stepHoare iprop(src (fill K e') ∗ P) et Q ⊢ hoare iprop(src (fill K e) ∗ ▷ P) et Q :=
  tp_pure_s e e' et K P Q he hstep

/-- Rocq: `store_tgt_tpr`. -/
theorem store_tgt_tpr (l : Loc) (v₁ v₂ : Val) :
    ⊢ stepHoare (GF := GF) iprop(l ↦ some v₁) hl(v(#l) ← &v₂)
      fun w => iprop(⌜w = hl_val(#())⌝ ∗ l ↦ some v₂) := tp_store_t l v₁ v₂

/-- Rocq: `store_src_tpr`. -/
theorem store_src_tpr (et : Exp) (l : Loc) (v₁ v₂ : Val) (K : List ECtxItem) (P : IProp GF)
    (Q : Val → IProp GF) (he : ToVal.toVal et = none) :
    stepHoare iprop(src (fill K hl(#())) ∗ heapSPointsTo l (.own 1) v₂ ∗ P) et Q ⊢
      hoare iprop(src (fill K hl(v(#l) ← &v₂)) ∗ heapSPointsTo l (.own 1) v₁ ∗ ▷ P) et Q := by
  unfold hoare stepHoare rseq seq seqRswp
  iintro #H !> ⟨Hsrc, Hl, HP⟩ Hna
  iapply rwp_take_step (src := refSrc (GF := GF))
    (P := iprop(src (fill K hl(#())) ∗ heapSPointsTo l (.own 1) v₂)) he $$ [HP Hna] [Hsrc Hl]
  · iintro ⟨Hsrc, Hl⟩
    iapply rswp_do_step (src := refSrc (GF := GF))
    inext
    iapply H $$ [Hsrc HP Hl] Hna
    iframe
  · iapply step_store ⊤ 0 K l v₂ v₁
    iframe

/-- Rocq: `load_tgt_tpr`. -/
theorem load_tgt_tpr (l : Loc) (v : Val) :
    ⊢ stepHoare (GF := GF) iprop(l ↦ some v) hl(!v(#l))
      fun w => iprop(⌜w = v⌝ ∗ l ↦ some v) := by
  unfold stepHoare seqRswp
  iintro !> Hl Hna
  iapply rswp_load (src := refSrc (GF := GF)) $$ Hl
  iintro Hl
  dsimp only
  iframe
  ipureintro; rfl

/-- Rocq: `load_src_tpr`. -/
theorem load_src_tpr (et : Exp) (l : Loc) (v : Val) (K : List ECtxItem) (P : IProp GF)
    (Q : Val → IProp GF) (he : ToVal.toVal et = none) :
    stepHoare iprop(src (fill K (v : Exp)) ∗ heapSPointsTo l (.own 1) v ∗ P) et Q ⊢
      hoare iprop(src (fill K hl(!v(#l))) ∗ heapSPointsTo l (.own 1) v ∗ ▷ P) et Q := by
  unfold hoare stepHoare rseq seq seqRswp
  iintro #H !> ⟨Hsrc, Hl, HP⟩ Hna
  iapply rwp_take_step (src := refSrc (GF := GF))
    (P := iprop(src (fill K (v : Exp)) ∗ heapSPointsTo l (.own 1) v)) he $$ [HP Hna] [Hsrc Hl]
  · iintro ⟨Hsrc, Hl⟩
    iapply rswp_do_step (src := refSrc (GF := GF))
    inext
    iapply H $$ [Hsrc HP Hl] Hna
    iframe
  · iapply step_load ⊤ 0 K l (.own 1) v
    iframe

/-- Rocq: `ref_tgt_tpr`. -/
theorem ref_tgt_tpr (v : Val) :
    ⊢ stepHoare (GF := GF) iprop(True) hl(ref(&v))
      fun w => iprop(∃ l : Loc, ⌜w = hl_val(#l)⌝ ∗ l ↦ some v) := by
  unfold stepHoare seqRswp
  iintro !> - Hna
  iapply rswp_alloc (src := refSrc (GF := GF))
  iintro %l Hl
  dsimp only
  iframe Hna
  iexists l
  iframe Hl
  ipureintro; rfl

/-- Rocq: `ref_src_tpr`. -/
theorem ref_src_tpr (et : Exp) (v : Val) (K : List ECtxItem) (P : IProp GF) (Q : Val → IProp GF)
    (he : ToVal.toVal et = none) :
    stepHoare iprop((∃ l : Loc, src (fill K hl(#l)) ∗ heapSPointsTo l (.own 1) v) ∗ P) et Q ⊢
      hoare iprop(src (fill K hl(ref(&v))) ∗ ▷ P) et Q := by
  unfold hoare stepHoare rseq seq seqRswp
  iintro #H !> ⟨Hsrc, HP⟩ Hna
  iapply rwp_take_step (src := refSrc (GF := GF))
    (P := iprop(∃ l : Loc, src (fill K hl(#l)) ∗ heapSPointsTo l (.own 1) v)) he $$ [HP Hna] [Hsrc]
  · iintro Hsrc
    iapply rswp_do_step (src := refSrc (GF := GF))
    inext
    iapply H $$ [Hsrc HP] Hna
    iframe
  · iapply step_alloc ⊤ 0 K v $$ Hsrc

/-- Rocq: `stutter_src_tpr`. -/
theorem stutter_src_tpr (e : Exp) (P : IProp GF) (Q : Val → IProp GF)
    (he : ToVal.toVal e = none) : stepHoare P e Q ⊢ hoare P e Q := tp_stutter_t e P Q he

/-- Rocq: `stutter_tgt_tpr`. -/
theorem stutter_tgt_tpr (et : Exp) (P : IProp GF) (Q : Val → IProp GF)
    (he : ToVal.toVal et = none) : hoare P et Q ⊢ hoare (srcModality P) et Q := by
  unfold hoare rseq seq
  iintro #H !> HP Hna
  iapply rwp_weaken' (src := refSrc (GF := GF)) (P := P) he $$ [Hna] HP
  iintro HP
  iapply H $$ HP Hna

/-- Rocq: `src_upd_intro`. -/
theorem src_upd_intro (P : IProp GF) : P ⊢ srcModality P := weakSrcUpd_return

/-- Rocq: `src_upd_bind`. -/
theorem src_upd_bind (P Q : IProp GF) :
    srcModality P ∗ (P -∗ srcModality Q) ⊢ srcModality Q := weakSrcUpd_bind

/-- Rocq: `src_upd_frame`. -/
theorem src_upd_frame (P Q : IProp GF) : srcModality P ∗ Q ⊢ srcModality iprop(P ∗ Q) := by
  iintro ⟨HP, HQ⟩
  iapply src_upd_bind
  iframe HP
  iintro HP
  iapply src_upd_intro
  iframe

/-- Rocq: `src_upd_pure`. -/
theorem src_upd_pure (e e' : Exp) (K : List ECtxItem) (hstep : e -ᵖ-> e') :
    src (GF := GF) (fill K e) ⊢ srcModality (src (fill K e')) := by
  iintro Hsrc
  iapply srcUpdate_weakSrcUpdate (src := refSrc (GF := GF))
  iapply step_pure ⊤ 0 _ _ (purePrimStep_fill (fill K) hstep) $$ Hsrc

/-- Rocq: `src_upd_store`. -/
theorem src_upd_store (l : Loc) (v w : Val) (K : List ECtxItem) :
    src (GF := GF) (fill K hl(v(#l) ← &w)) ∗ heapSPointsTo l (.own 1) v ⊢
      srcModality iprop(src (fill K hl(#())) ∗ heapSPointsTo l (.own 1) w) := by
  iintro H
  iapply srcUpdate_weakSrcUpdate (src := refSrc (GF := GF))
  iapply step_store ⊤ 0 K l w v $$ H

/-- Rocq: `src_upd_load`. -/
theorem src_upd_load (l : Loc) (v : Val) (K : List ECtxItem) :
    src (GF := GF) (fill K hl(!v(#l))) ∗ heapSPointsTo l (.own 1) v ⊢
      srcModality iprop(src (fill K (v : Exp)) ∗ heapSPointsTo l (.own 1) v) := by
  iintro H
  iapply srcUpdate_weakSrcUpdate (src := refSrc (GF := GF))
  iapply step_load ⊤ 0 K l (.own 1) v $$ H

/-- Rocq: `src_upd_alloc`. -/
theorem src_upd_alloc (v : Val) (K : List ECtxItem) :
    src (GF := GF) (fill K hl(ref(&v))) ⊢
      srcModality iprop(∃ l : Loc, src (fill K hl(#l)) ∗ heapSPointsTo l (.own 1) v) := by
  iintro H
  iapply srcUpdate_weakSrcUpdate (src := refSrc (GF := GF))
  iapply step_alloc ⊤ 0 K v $$ H

/-- Rocq: `src_stutter_cred`. -/
theorem src_stutter_cred (P : IProp GF) (et : Exp) (Q : Val → IProp GF)
    (he : ToVal.toVal et = none) :
    stepHoare P et Q ⊢ hoare iprop(stutter 1 ∗ ▷ P) et Q := by
  unfold hoare stepHoare rseq seq seqRswp
  iintro #H !> ⟨Hc, HP⟩ Hna
  iapply rwp_take_step (src := refSrc (GF := GF)) (P := stutter (GF := GF) 0) he $$ [HP Hna] [Hc]
  · iintro -
    iapply rswp_do_step (src := refSrc (GF := GF))
    inext
    iapply H $$ HP Hna
  · iapply step_stutter ⊤ 0 $$ Hc

/-- Rocq: `src_stutter_cred_split`. -/
theorem src_stutter_cred_split (n m : Nat) :
    stutter (GF := GF) (n + m) ⊣⊢ stutter n ∗ stutter m := nat_srcF_split n m

/-- Rocq: `pure_src_stutter_tpr`. -/
theorem pure_src_stutter_tpr (e e' et : Exp) (n : Nat) (K : List ECtxItem) (P : IProp GF)
    (Q : Val → IProp GF) (he : ToVal.toVal et = none) (hstep : e -ᵖ-> e') :
    stepHoare iprop(src (fill K e') ∗ stutter n ∗ P) et Q ⊢
      hoare iprop(src (fill K e) ∗ ▷ P) et Q := by
  unfold hoare stepHoare rseq seq seqRswp
  iintro #H !> ⟨Hsrc, HP⟩ Hna
  iapply rwp_take_step (src := refSrc (GF := GF))
    (P := iprop(src (fill K e') ∗ stutter n)) he $$ [HP Hna] [Hsrc]
  · iintro ⟨Hsrc, Hc⟩
    iapply rswp_do_step (src := refSrc (GF := GF))
    inext
    iapply H $$ [Hsrc Hc HP] Hna
    iframe
  · iapply step_pure_cred n ⊤ 0 _ _ (purePrimStep_fill (fill K) hstep) $$ Hsrc

/-- Rocq: `store_src_stutter_tpr`. -/
theorem store_src_stutter_tpr (et : Exp) (l : Loc) (v₁ v₂ : Val) (n : Nat) (K : List ECtxItem)
    (P : IProp GF) (Q : Val → IProp GF) (he : ToVal.toVal et = none) :
    stepHoare iprop(src (fill K hl(#())) ∗ heapSPointsTo l (.own 1) v₂ ∗ stutter n ∗ P) et Q ⊢
      hoare iprop(src (fill K hl(v(#l) ← &v₂)) ∗ heapSPointsTo l (.own 1) v₁ ∗ ▷ P) et Q := by
  unfold hoare stepHoare rseq seq seqRswp
  iintro #H !> ⟨Hsrc, Hl, HP⟩ Hna
  iapply rwp_take_step (src := refSrc (GF := GF))
    (P := iprop((∃ _ : Unit, src (fill K hl(#())) ∗ heapSPointsTo l (.own 1) v₂) ∗ stutter n)) he
    $$ [HP Hna] [Hsrc Hl]
  · iintro ⟨⟨%_, Hsrc, Hl⟩, Hc⟩
    iapply rswp_do_step (src := refSrc (GF := GF))
    inext
    iapply H $$ [Hsrc Hl Hc HP] Hna
    iframe
  · ihave H' := step_inv_alloc n ⊤ 0 (fill K hl(v(#l) ← &v₂)) (fun _ : Unit => fill K hl(#()))
      (fun _ => heapSPointsTo l (.own 1) v₂) (fun _ => fill_ne (by simp)) $$ [Hl]
    · iintro Hsrc
      iapply srcUpdate_mono (src := refSrc (GF := GF))
      isplitl [Hsrc Hl]
      · iapply step_store ⊤ 0 K l v₂ v₁
        iframe
      · iintro ⟨Hsrc, Hl⟩
        iexists ()
        iframe
    iapply H' $$ Hsrc

/-- Rocq: `load_src_stutter_tpr`. -/
theorem load_src_stutter_tpr (et : Exp) (l : Loc) (v : Val) (n : Nat) (K : List ECtxItem)
    (P : IProp GF) (Q : Val → IProp GF) (he : ToVal.toVal et = none) :
    stepHoare iprop(src (fill K (v : Exp)) ∗ heapSPointsTo l (.own 1) v ∗ stutter n ∗ P) et Q ⊢
      hoare iprop(src (fill K hl(!v(#l))) ∗ heapSPointsTo l (.own 1) v ∗ ▷ P) et Q := by
  unfold hoare stepHoare rseq seq seqRswp
  iintro #H !> ⟨Hsrc, Hl, HP⟩ Hna
  iapply rwp_take_step (src := refSrc (GF := GF))
    (P := iprop((∃ _ : Unit, src (fill K (v : Exp)) ∗ heapSPointsTo l (.own 1) v) ∗ stutter n)) he
    $$ [HP Hna] [Hsrc Hl]
  · iintro ⟨⟨%_, Hsrc, Hl⟩, Hc⟩
    iapply rswp_do_step (src := refSrc (GF := GF))
    inext
    iapply H $$ [Hsrc Hl Hc HP] Hna
    iframe
  · ihave H' := step_inv_alloc n ⊤ 0 (fill K hl(!v(#l))) (fun _ : Unit => fill K (v : Exp))
      (fun _ => heapSPointsTo l (.own 1) v) (fun _ => fill_ne (by simp)) $$ [Hl]
    · iintro Hsrc
      iapply srcUpdate_mono (src := refSrc (GF := GF))
      isplitl [Hsrc Hl]
      · iapply step_load ⊤ 0 K l (.own 1) v
        iframe
      · iintro ⟨Hsrc, Hl⟩
        iexists ()
        iframe
    iapply H' $$ Hsrc

/-- Rocq: `ref_src_stutter_tpr`. -/
theorem ref_src_stutter_tpr (et : Exp) (v : Val) (n : Nat) (K : List ECtxItem) (P : IProp GF)
    (Q : Val → IProp GF) (he : ToVal.toVal et = none) :
    stepHoare iprop((∃ l : Loc, src (fill K hl(#l)) ∗ heapSPointsTo l (.own 1) v) ∗ stutter n ∗ P)
      et Q ⊢ hoare iprop(src (fill K hl(ref(&v))) ∗ ▷ P) et Q := by
  unfold hoare stepHoare rseq seq seqRswp
  iintro #H !> ⟨Hsrc, HP⟩ Hna
  iapply rwp_take_step (src := refSrc (GF := GF))
    (P := iprop((∃ l : Loc, src (fill K hl(#l)) ∗ heapSPointsTo l (.own 1) v) ∗ stutter n)) he
    $$ [HP Hna] [Hsrc]
  · iintro ⟨Hsrc, Hc⟩
    iapply rswp_do_step (src := refSrc (GF := GF))
    inext
    iapply H $$ [Hsrc Hc HP] Hna
    iframe
  · ihave H' := step_inv_alloc n ⊤ 0 (fill K hl(ref(&v))) (fun l : Loc => fill K hl(#l))
      (fun l => heapSPointsTo l (.own 1) v) (fun _ => fill_ne (by simp)) $$ []
    · iintro Hsrc
      iapply step_alloc ⊤ 0 K v $$ Hsrc
    iapply H' $$ Hsrc

end Iris.Transfinite.Refinement.Derived
