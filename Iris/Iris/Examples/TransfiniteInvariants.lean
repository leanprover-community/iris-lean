/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.ProgramLogic.WeakestPreTransfinite
public import Iris.Instances.Lib.InvariantsTransfinite

/-! # Opening invariants with transfinite step-indices

This file ports the language-independent parts of `theories/examples/transfinite.v` of
Transfinite Iris. With transfinite step-indices, `▷` does not commute with existential
quantification, so the contents `▷ ∃ x, Ψ x` of an opened invariant cannot be destructed directly.
The strong weakest precondition `swp k` solves this: each `swp_step` lets the proof strip one more
later, before the (atomic) program step is taken.

The examples of the Rocq file that use `heap_lang` (loading from a location protected by an
invariant) are instances of `invariants_swp` and `invariants_swp_exists` below.
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite.Examples

open Iris ProgramLogic Iris.Std Iris.BI OFE LawfulSet

variable {Expr State Obs Val : Type _} [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS Expr GF]
variable {s : Stuckness} {e : Expr} {φ : Val → IProp GF} {N : Namespace}

theorem subset_top {E : CoPset} : E ⊆ ⊤ := fun _ _ => CoPset.mem_full

/-- Opening an invariant around an atomic expression, stripping the later of its contents
(Rocq: `invariants_swp`). -/
theorem invariants_swp (k : Nat) (P : IProp GF) [Language.Atomic (Val := Val) .StronglyAtomic e]
    (H : P ⊢ swp k s (⊤ \ ↑N) e fun v => iprop(φ v ∗ P)) :
    inv N P ⊢ swp (k + 1) s ⊤ e φ := by
  iintro #I
  iapply swp_atomic (E₂ := ⊤ \ ↑N)
  imod inv_acc subset_top $$ I with ⟨HP, Hclose⟩
  imodintro
  iapply swp_step
  inext
  ihave Hswp := H $$ HP
  iapply swp_strong_mono (Std.IsPreorder.le_refl s) subset_refl (Nat.le_refl k) $$ Hswp [Hclose]
  iintro %v ⟨Hφ, HP⟩
  imodintro
  imod Hclose $$ [HP] with -
  · inext
    iexact HP
  imodintro
  iexact Hφ

/-- Opening an invariant whose contents are an existential: the later is stripped by `swp_step`
before the existential is destructed (Rocq: `invariants_transfinite`). -/
theorem invariants_swp_exists {X : Type _} (k : Nat) (Ψ : X → IProp GF)
    [Language.Atomic (Val := Val) .StronglyAtomic e]
    (H : ∀ x, Ψ x ⊢ swp k s (⊤ \ ↑N) e fun v => iprop(φ v ∗ ∃ x, Ψ x)) :
    inv N iprop(∃ x, Ψ x) ⊢ swp (k + 1) s ⊤ e φ :=
  invariants_swp k _ (exists_elim H)

/-- Nested invariants can be opened in a single program step, stripping one later for each
invariant (Rocq: `invariants_transfinite_nested`, without `heap_lang`). -/
theorem invariants_swp_nested (k : Nat) {N₁ N₂ : Namespace}
    (hN : (↑N₂ : CoPset) ⊆ ⊤ \ ↑N₁)
    (Q : IProp GF) [Language.Atomic (Val := Val) .StronglyAtomic e]
    (H : Q ⊢ swp k s ((⊤ \ ↑N₁) \ ↑N₂) e fun v => iprop(φ v ∗ Q)) :
    inv N₁ (inv N₂ Q) ⊢ swp (k + 1 + 1) s ⊤ e φ := by
  iintro #I
  iapply swp_atomic (E₂ := ⊤ \ ↑N₁)
  imod inv_acc subset_top $$ I with ⟨HI, Hclose₁⟩
  imodintro
  iapply swp_step
  inext
  icases HI with #HI
  iapply swp_atomic (E₂ := (⊤ \ ↑N₁) \ ↑N₂)
  imod inv_acc hN $$ HI with ⟨HQ, Hclose₂⟩
  imodintro
  iapply swp_step
  inext
  ihave Hswp := H $$ HQ
  iapply swp_strong_mono (Std.IsPreorder.le_refl s) subset_refl (Nat.le_refl k) $$ Hswp
    [Hclose₁ Hclose₂]
  iintro %v ⟨Hφ, HQ⟩
  imodintro
  imod Hclose₂ $$ [HQ] with -
  · inext
    iexact HQ
  imodintro
  imod Hclose₁ $$ [] with -
  · inext
    iexact HI
  imodintro
  iexact Hφ

end Iris.Transfinite.Examples
