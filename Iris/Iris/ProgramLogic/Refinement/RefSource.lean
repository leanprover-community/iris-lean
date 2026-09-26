/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.Instances.Lib.FUpdTransfinite
public import Iris.Std.FromMathlib

/-! # Sources of termination-preserving refinements (Transfinite Iris)

This file ports the generic part of `theories/program_logic/refinement/ref_source.v` of
Transfinite Iris. A *source* is a relation `↪` on a type `A` together with an interpretation of
its elements as propositions. The refinement weakest precondition simulates each target step by
zero or more source steps, and at least one source step if the target step is not "free".

- `srcUpdate E P`: take at least one source step (`↪⁺`), then `P` holds;
- `weakSrcUpdate E P`: take any number of source steps (`↪⋆`), then `P` holds;
- the lexicographic product of two sources (stuttering).
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite

open Iris Iris.Std Iris.BI OFE Relation FromMathlib FromMathlib.Relation

/-- A source: a relation `rel` (Rocq: `↪`) and an interpretation `interp` of its states
(Rocq: `source`). -/
class Source (GF : BundledGFunctors) (A : Type _) where
  rel : A → A → Prop
  interp : A → IProp GF

/-- Strong normalization is preserved by taking the transitive closure (Rocq: `sn_tc`). -/
theorem sn_transGen {X : Type _} (R : X → X → Prop) (x : X) :
    StronglyNormalizing R x ↔ StronglyNormalizing (TransGen R) x := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : Acc (TransGen (flip R)) x := h.transGen
    refine Subrelation.accessible (fun {a b} (hab : flip (TransGen R) a b) => ?_) this
    exact transGen_swap.mp hab
  · refine Subrelation.accessible (fun {a b} (hab : flip R a b) => ?_) h
    exact .single hab
where
  transGen_swap {a b : X} : TransGen R b a ↔ TransGen (flip R) a b := by
    constructor
    · intro h
      induction h with
      | single h => exact .single h
      | tail _ h ih => exact TransGen.trans (.single h) ih
    · intro h
      induction h with
      | single h => exact .single h
      | tail _ h ih => exact TransGen.trans (.single h) ih

section SrcUpdate

variable {GF : BundledGFunctors} [W : WsatGS GF] {A : Type _} [src : Source GF A]

/-- Take at least one source step (Rocq: `src_update`). -/
def srcUpdate (E : CoPset) (P : IProp GF) : IProp GF :=
  iprop(∀ a : A, src.interp a -∗ |={E}=> ∃ b : A, ⌜TransGen src.rel a b⌝ ∗ src.interp b ∗ P)

/-- Take any number of source steps (Rocq: `weak_src_update`). -/
def weakSrcUpdate (E : CoPset) (P : IProp GF) : IProp GF :=
  iprop(∀ a : A, src.interp a -∗ |={E}=> ∃ b : A, ⌜ReflTransGen src.rel a b⌝ ∗ src.interp b ∗ P)

variable {E : CoPset} {P Q : IProp GF}

theorem transGen_to_reflTransGen {r : A → A → Prop} {a b : A} (h : TransGen r a b) :
    ReflTransGen r a b := by
  induction h with
  | single h => exact .single h
  | tail _ h ih => exact ih.tail h

theorem transGen_of_reflTransGen_transGen {r : A → A → Prop} {a b c : A}
    (h₁ : ReflTransGen r a b) (h₂ : TransGen r b c) : TransGen r a c := by
  induction h₁ with
  | refl => exact h₂
  | tail _ h ih => exact ih (TransGen.trans (.single h) h₂)

theorem transGen_of_transGen_reflTransGen {r : A → A → Prop} {a b c : A}
    (h₁ : TransGen r a b) (h₂ : ReflTransGen r b c) : TransGen r a c := by
  induction h₂ with
  | refl => exact h₁
  | tail _ h ih => exact ih.tail h

/-- Rocq: `src_update_bind`. -/
theorem srcUpdate_bind :
    srcUpdate (A := A) E P ∗ (P -∗ srcUpdate (A := A) E Q) ⊢ srcUpdate (A := A) E Q := by
  unfold srcUpdate
  iintro ⟨HP, HPQ⟩ %a Ha
  imod HP $$ %a Ha with ⟨%b, %Hab, Hb, HP⟩
  ihave HQ := HPQ $$ HP
  imod HQ $$ %b Hb with ⟨%c, %Hbc, Hc, HQ⟩
  imodintro
  iexists c
  iframe
  ipureintro
  exact TransGen.trans Hab Hbc

/-- Rocq: `src_update_mono_fupd`. -/
theorem srcUpdate_mono_fupd :
    srcUpdate (A := A) E P ∗ (P ={E}=∗ Q) ⊢ srcUpdate (A := A) E Q := by
  unfold srcUpdate
  iintro ⟨HP, HPQ⟩ %a Ha
  imod HP $$ %a Ha with ⟨%b, %Hab, Hb, HP⟩
  imod HPQ $$ HP with HQ
  imodintro
  iexists b
  iframe
  ipureintro
  exact Hab

/-- Rocq: `src_update_mono`. -/
theorem srcUpdate_mono : srcUpdate (A := A) E P ∗ (P -∗ Q) ⊢ srcUpdate (A := A) E Q := by
  iintro ⟨HP, HPQ⟩
  iapply srcUpdate_mono_fupd
  iframe HP
  iintro HP
  imodintro
  iapply HPQ $$ HP

/-- Rocq: `fupd_src_update`. -/
theorem fupd_srcUpdate : (|={E}=> srcUpdate (A := A) E P) ⊢ srcUpdate (A := A) E P := by
  unfold srcUpdate
  iintro H %a Ha
  imod H
  iapply H $$ %a Ha

/-- Rocq: `src_update_weak_src_update`. -/
theorem srcUpdate_weakSrcUpdate : srcUpdate (A := A) E P ⊢ weakSrcUpdate (A := A) E P := by
  unfold srcUpdate weakSrcUpdate
  iintro HP %a Ha
  imod HP $$ %a Ha with ⟨%b, %Hab, Hb, HP⟩
  imodintro
  iexists b
  iframe
  ipureintro
  exact transGen_to_reflTransGen Hab

/-- Rocq: `weak_src_update_return`. -/
theorem weakSrcUpdate_return : P ⊢ weakSrcUpdate (A := A) E P := by
  unfold weakSrcUpdate
  iintro HP %a Ha
  imodintro
  iexists a
  iframe
  ipureintro
  exact .refl

/-- Rocq: `weak_src_update_bind_l`. -/
theorem weakSrcUpdate_bind_l :
    weakSrcUpdate (A := A) E P ∗ (P -∗ srcUpdate (A := A) E Q) ⊢ srcUpdate (A := A) E Q := by
  unfold srcUpdate weakSrcUpdate
  iintro ⟨HP, HPQ⟩ %a Ha
  imod HP $$ %a Ha with ⟨%b, %Hab, Hb, HP⟩
  ihave HQ := HPQ $$ HP
  imod HQ $$ %b Hb with ⟨%c, %Hbc, Hc, HQ⟩
  imodintro
  iexists c
  iframe
  ipureintro
  exact transGen_of_reflTransGen_transGen Hab Hbc

/-- Rocq: `weak_src_update_bind_r`. -/
theorem weakSrcUpdate_bind_r :
    srcUpdate (A := A) E P ∗ (P -∗ weakSrcUpdate (A := A) E Q) ⊢ srcUpdate (A := A) E Q := by
  unfold srcUpdate weakSrcUpdate
  iintro ⟨HP, HPQ⟩ %a Ha
  imod HP $$ %a Ha with ⟨%b, %Hab, Hb, HP⟩
  ihave HQ := HPQ $$ HP
  imod HQ $$ %b Hb with ⟨%c, %Hbc, Hc, HQ⟩
  imodintro
  iexists c
  iframe
  ipureintro
  exact transGen_of_transGen_reflTransGen Hab Hbc

/-- Rocq: `weak_src_update_bind`. -/
theorem weakSrcUpdate_bind :
    weakSrcUpdate (A := A) E P ∗ (P -∗ weakSrcUpdate (A := A) E Q) ⊢
      weakSrcUpdate (A := A) E Q := by
  unfold weakSrcUpdate
  iintro ⟨HP, HPQ⟩ %a Ha
  imod HP $$ %a Ha with ⟨%b, %Hab, Hb, HP⟩
  ihave HQ := HPQ $$ HP
  imod HQ $$ %b Hb with ⟨%c, %Hbc, Hc, HQ⟩
  imodintro
  iexists c
  iframe
  ipureintro
  exact ReflTransGen.trans Hab Hbc

/-- Rocq: `weak_src_update_mono_fupd`. -/
theorem weakSrcUpdate_mono_fupd :
    weakSrcUpdate (A := A) E P ∗ (P ={E}=∗ Q) ⊢ weakSrcUpdate (A := A) E Q := by
  unfold weakSrcUpdate
  iintro ⟨HP, HPQ⟩ %a Ha
  imod HP $$ %a Ha with ⟨%b, %Hab, Hb, HP⟩
  imod HPQ $$ HP with HQ
  imodintro
  iexists b
  iframe
  ipureintro
  exact Hab

/-- Rocq: `weak_src_update_mono`. -/
theorem weakSrcUpdate_mono :
    weakSrcUpdate (A := A) E P ∗ (P -∗ Q) ⊢ weakSrcUpdate (A := A) E Q := by
  iintro ⟨HP, HPQ⟩
  iapply weakSrcUpdate_mono_fupd
  iframe HP
  iintro HP
  imodintro
  iapply HPQ $$ HP

/-- Rocq: `fupd_weak_src_update`. -/
theorem fupd_weakSrcUpdate :
    (|={E}=> weakSrcUpdate (A := A) E P) ⊢ weakSrcUpdate (A := A) E P := by
  unfold weakSrcUpdate
  iintro H %a Ha
  imod H
  iapply H $$ %a Ha

end SrcUpdate

/-! ## Lexicographic products of sources -/

/-- The lexicographic order on pairs (Rocq: `lex`). -/
inductive Lex {X Y : Type _} (R : X → X → Prop) (S : Y → Y → Prop) : X × Y → X × Y → Prop
  | left {x x' : X} (y y' : Y) : R x x' → Lex R S (x, y) (x', y')
  | right (x : X) {y y' : Y} : S y y' → Lex R S (x, y) (x, y')

/-- Rocq: `sn_lex`. -/
theorem sn_lex {X Y : Type _} (R : X → X → Prop) (S : Y → Y → Prop) (x : X) (y : Y)
    (hx : StronglyNormalizing R x) (hy : ∀ y, StronglyNormalizing S y) :
    StronglyNormalizing (Lex R S) (x, y) := by
  induction hx generalizing y with
  | intro x _ ihx =>
    induction (hy y) with
    | intro y _ ihy =>
      constructor
      rintro ⟨x', y'⟩ h
      cases h with
      | left _ _ h => exact ihx x' h y'
      | right _ h => exact ihy y' h

/-- Rocq: `tc_lex_left`. -/
theorem transGen_lex_left {X Y : Type _} {R : X → X → Prop} {S : Y → Y → Prop} {x x' : X}
    (y y' : Y) (h : TransGen R x x') : TransGen (Lex R S) (x, y) (x', y') := by
  induction h generalizing y' with
  | single h => exact .single (.left _ _ h)
  | tail _ h ih => exact TransGen.tail (ih y) (.left _ _ h)

/-- Rocq: `tc_lex_right`. -/
theorem transGen_lex_right {X Y : Type _} {R : X → X → Prop} {S : Y → Y → Prop} (x : X)
    {y y' : Y} (h : TransGen S y y') : TransGen (Lex R S) (x, y) (x, y') := by
  induction h with
  | single h => exact .single (.right _ h)
  | tail _ h ih => exact TransGen.tail ih (.right _ h)

section Lexicographic

variable {GF : BundledGFunctors} [W : WsatGS GF] {A B : Type _}

/-- The lexicographic product of two sources (Rocq: `lex_source`). -/
def lexSource (src₁ : Source GF A) (src₂ : Source GF B) : Source GF (A × B) where
  rel := Lex src₁.rel src₂.rel
  interp p := iprop(src₁.interp p.1 ∗ src₂.interp p.2)

variable (src₁ : Source GF A) (src₂ : Source GF B) {E : CoPset} {P Q : IProp GF}

/-- Rocq: `source_update_embed_l_strong`. -/
theorem srcUpdate_embed_l_strong :
    srcUpdate (src := src₁) E P ∗
      (∀ b : B, src₂.interp b ={E}=∗ ∃ b' : B, src₂.interp b' ∗ Q) ⊢
    srcUpdate (src := lexSource src₁ src₂) E iprop(P ∗ Q) := by
  delta srcUpdate lexSource; dsimp only
  iintro ⟨H, Hupd⟩ %⟨a, b⟩ ⟨Ha, Hb⟩
  imod H $$ %a Ha with ⟨%a', %Hstep, Ha, HP⟩
  imod Hupd $$ %b Hb with ⟨%b', Hb, HQ⟩
  imodintro
  iexists (a', b')
  isplitr
  · ipureintro
    exact transGen_lex_left b b' Hstep
  iframe

/-- Rocq: `source_update_embed_l`. -/
theorem srcUpdate_embed_l :
    srcUpdate (src := src₁) E P ⊢ srcUpdate (src := lexSource src₁ src₂) E P := by
  iintro H
  iapply srcUpdate_mono (src := lexSource src₁ src₂)
  isplitl [H]
  · iapply srcUpdate_embed_l_strong src₁ src₂ (Q := iprop(True))
    iframe H
    iintro %b Hb
    imodintro
    iexists b
    iframe
  · iintro ⟨HP, -⟩
    iexact HP

/-- Rocq: `source_update_embed_r`. -/
theorem srcUpdate_embed_r :
    srcUpdate (src := src₂) E P ⊢ srcUpdate (src := lexSource src₁ src₂) E P := by
  delta srcUpdate lexSource; dsimp only
  iintro H %⟨a, b⟩ ⟨Ha, Hb⟩
  imod H $$ %b Hb with ⟨%b', %Hstep, Hb, HP⟩
  imodintro
  iexists (a, b')
  isplitr
  · ipureintro
    exact transGen_lex_right a Hstep
  iframe

end Lexicographic

end Iris.Transfinite
