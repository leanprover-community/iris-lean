/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public import Iris.BI
public import Iris.ProofMode

@[expose] public section

namespace Iris.Tests
open BI ProofMode

variable {PROP1 PROP2 : Type u} [BI PROP1] [BI PROP2] [BiEmbed PROP1 PROP2]

/-
  Tests `imodintro`, where `fromModal_embed` is preferred over
  `fromModal_id_embed` on `⎡|==> P⎤`.
-/
example [BIUpdate PROP1] (P : PROP1) : ⎡P⎤ ⊢@{PROP2} ⎡|==> P⎤ := by
  iintro HP
  imodintro
  imodintro
  iexact HP

/-- Tests `imodintro` prefers `fromModal_embed` over `fromModal_affinely_embed`. -/
example (P : PROP1) [Affine P] : ⎡P⎤ ⊢@{PROP2} ⎡<affine> P⎤ := by
  iintro HP
  imodintro
  imodintro
  iexact HP

/-- Tests `imodintro` prefers `fromModal_embed` over `fromModal_persistently_embed`. -/
example
    (P : PROP1) : □ ⎡P⎤ ⊢@{PROP2} ⎡<pers> P⎤ := by
  iintro #HP
  imodintro
  imodintro
  iexact HP

/-- Tests `imodintro` prefers `fromModal_embed` over `fromModal_plainly_embed`. -/
example {P1 P2 : Type u} [Sbi P1] [Sbi P2] [BiEmbed P1 P2] [BiEmbedSbi P1 P2]
    (P : P1) [Plain P] : □ ⎡P⎤ ⊢@{P2} ⎡■ P⎤ := by
  iintro #HP
  imodintro
  imodintro
  iexact HP

/--
  Tests that the spatial context is transformed by `IntoEmbed`, i.e. that the
  embedding really was introduced and not the inner modality.
-/
example [BIUpdate PROP1]
    [BiEmbed PROP1 PROP2] (P Q : PROP1) : ⎡P⎤ ∗ ⎡P -∗ Q⎤ ⊢@{PROP2} ⎡|==> Q⎤ := by
  iintro ⟨HP, HPQ⟩
  imodintro
  imodintro
  ispecialize HPQ $$ HP
  iexact HPQ

/-
  Tests `FromModal` instances with the selector not fixed.
  The default instance `modality_embed` is used.
-/
/-- info: solution: FromModal True modality_embed
⎡<affine> P⎤ ⎡<affine> P⎤ iprop(<affine> P), new goals: [] -/
#guard_msgs in
variable (P : PROP1) in
#ipm_synth FromModal (α := PROP2) _ _ _ iprop(⎡<affine> P⎤ : PROP2) _

/-
  Tests `FromModal` instances with the selector fixed: the low priority
  instances are reachable only once the selector rules out `modality_embed`.
-/
/-- info: solution:
FromModal True modality_intuitionistically iprop(□ P) ⎡□ P⎤ ⎡P⎤, new goals: [] -/
#guard_msgs in
variable (P : PROP1) in
#ipm_synth FromModal _ _ iprop(□ P) iprop(⎡□ P⎤ : PROP2) _

/-
  Tests `imodintro` with the selection for `FromModal` fixed.
  The instance `fromModal_affinely_embed` is used.
  In this case, `<affine>` is stripped from the goal, as opposed to the default
  `imodintro`, which would strip the embedding.
-/
example (Q : PROP1) [Affine (embed Q : PROP2)] : ⎡Q⎤ ⊢@{PROP2} ⎡<affine> Q⎤ := by
  iintro HQ
  imodintro (<affine> _)
  iexact HQ

/--
  Tests `ispecialize` through an embedded wand with an ordinary embedded
  argument: `intoWand_embed`, at default priority, is used.
-/
example (P Q : PROP1) : ⎡P⎤ ∗ ⎡P -∗ Q⎤ ⊢@{PROP2} ⎡Q⎤ := by
  iintro ⟨HP, Hwand⟩
  ispecialize Hwand $$ HP
  iexact Hwand

/--
  Tests `ispecialize` where `intoWand_embed` is used so that the subgoal is
  `⎡P⎤`, not `<affine> ⎡P⎤`.
-/
example (P Q : PROP1) : ⎡P⎤ ∗ ⎡P -∗ Q⎤ ⊢@{PROP2} ⎡Q⎤ := by
  iintro ⟨HP, Hwand⟩
  ispecialize Hwand $$ [HP //]
  iexact Hwand

/--
  Tests `ispecialize` with an `<affine>`-wrapped embedded argument and a spatial
  wand: `intoWand_affine_embed_false`.  The `<affine>` is absorbed into the
  embedding, so the result is `⎡Q⎤` rather than `<affine> ⎡Q⎤`.
-/
example (P Q : PROP1) : ⎡<affine> P -∗ Q⎤ ∗ <affine> ⎡P⎤ ⊢@{PROP2} ⎡Q⎤ := by
  iintro ⟨Hwand, HP⟩
  ispecialize Hwand $$ HP
  iexact Hwand

/--
  Tests `ispecialize` with an `<affine>`-wrapped embedded argument and an
  intuitionistic wand: `intoWand_affine_embed_true`.  Here the result keeps the
  `<affine>`.
-/
example (P Q : PROP1) : □ ⎡P -∗ Q⎤ ∗ <affine> ⎡P⎤ ⊢@{PROP2} <affine> ⎡Q⎤ := by
  iintro ⟨#Hwand, HP⟩
  ispecialize Hwand $$ HP
  iexact Hwand

/--
  Tests `iapply` of an embedded intuitionistic wand against an `<affine>` goal,
  i.e. `intoWand_affine_embed_true` in `WandMode.matching .result` (compare the
  `intoWand_affine_args` test above).
-/
example (P Q : PROP1) : □ ⎡P -∗ Q⎤ ⊢@{PROP2} (<affine> ⎡P⎤) -∗ <affine> ⎡Q⎤ := by
  iintro #Hwand HP
  iapply Hwand
  iexact HP

/--
  `intoWand_affine_embed_*` is reached only once `R` has bottomed out at an
  embedding: with an `<affine>` on `⎡R⎤` itself, `intoWand_affinely` wins instead.
-/
example (P Q : PROP1) : (<affine> ⎡P -∗ Q⎤) ⊢@{PROP2} (<affine> ⎡P⎤) -∗ <affine> ⎡Q⎤ := by
  iintro Hwand HP
  iapply Hwand
  iexact HP
