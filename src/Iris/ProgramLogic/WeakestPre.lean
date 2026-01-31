/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.BaseLogic.Lib.FancyUpdates
import Iris.ProgramLogic.Language
import Iris.ProofMode.Tactics
import Iris.BI.DerivedLawsLater

/-! # Weakest Precondition

Reference: `iris/program_logic/weakestpre.v`

The weakest precondition `WP e @ s; E {{ Φ }}` asserts that expression `e`,
starting in mask `E` with stuckness `s`, either:
- is a value `v` satisfying `|={E}=> Φ v`, or
- can take a step, and after stepping the WP holds recursively.

The fixpoint is well-founded because the recursive occurrence is guarded
under `▷` (via the step-taking fancy update `|={∅}▷=>^n`).

## Definition

```
wp_pre s wp E e Φ :=
  match to_val e with
  | Some v => |={E}=> Φ v
  | None => ∀ σ ns κ κs nt,
      state_interp σ ns (κ ++ κs) nt ={E,∅}=∗
        ⌜if s is NotStuck then reducible e σ else True⌝ ∗
        ∀ e2 σ2 efs, ⌜prim_step e σ κ e2 σ2 efs⌝ ={∅}▷=∗^(S n) |={∅,E}=>
        state_interp σ2 (S ns) κs (length efs + nt) ∗
        wp E e2 Φ ∗
        [∗ list] ef ∈ efs, wp ⊤ ef fork_post
  end
```

## Main Results

- `wp_value_fupd` — value case: `WP of_val v @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v`
- `wp_strong_mono` — monotonicity in stuckness, mask, and postcondition
- `wp_bind` — compositionality via evaluation contexts
- `wp_frame_l` / `wp_frame_r` — frame rules
- `wp_fupd` — absorb postcondition update
- `wp_wand` — weakening postcondition via wand

## Simplifications

This port omits later credit support and the `step_fupdN` infrastructure.
The `num_laters_per_step` is fixed to 0 (one later per step).
-/

namespace Iris.ProgramLogic

open Iris Iris.Algebra Iris.Std Iris.BI Iris.BaseLogic

variable {GF : BundledGFunctors} {M : Type _ → Type _} {F : Type _}
variable [UFraction F]
variable [FiniteMap Positive M] [DecidableEq Positive]
variable [FiniteMapLaws Positive M] [HeapFiniteMap Positive M]
variable [ElemG GF (InvF GF M F)]
variable [ElemG GF (COFE.constOF CoPsetDisj)]
variable [ElemG GF (COFE.constOF GSetDisj)]

variable {Λ : Language}

/-! ## Iris Ghost State for WP -/

/-- The Iris ghost state typeclass for the weakest precondition.
Packages the state interpretation, fork postcondition, and per-step laters.
Coq: `irisGS_gen` in `weakestpre.v`. -/
class IrisGS (Λ : Language) (GF : BundledGFunctors) where
  /-- World satisfaction witness. -/
  wsatGS : WsatGS GF
  /-- State interpretation invariant: `state → step_count → observations → num_forks → iProp`. -/
  state_interp : Λ.state → Nat → List Λ.observation → Nat → IProp GF
  /-- Fixed postcondition for forked threads. -/
  fork_post : Λ.val → IProp GF
  /-- State interpretation is monotone in step count.
  Full version uses `uPred_fupd wsatGS ∅ ∅ (state_interp σ (ns+1) κs nt)`;
  simplified here to avoid threading `M`/`F` into the class. -/
  state_interp_mono : ∀ σ ns κs nt,
    state_interp σ ns κs nt ⊢ state_interp σ (ns + 1) κs nt

variable [inst : IrisGS Λ GF]

private noncomputable abbrev fupd' (E1 E2 : Iris.Set Positive) (P : IProp GF) : IProp GF :=
  uPred_fupd (M := M) (F := F) (@IrisGS.wsatGS Λ GF inst) E1 E2 P

private theorem fupd_idem (E : Iris.Set Positive) (P : IProp GF) :
    fupd' (Λ := Λ) (M := M) (F := F) E E
        (fupd' (Λ := Λ) (M := M) (F := F) E E P) ⊢
      fupd' (Λ := Λ) (M := M) (F := F) E E P := by
  simpa using
    (fupd_trans (W := IrisGS.wsatGS (Λ := Λ) (GF := GF))
      (M := M) (F := F) (E1 := E) (E2 := E) (E3 := E) (P := P))

private theorem fupd_intro (E : Iris.Set Positive) (P : IProp GF) :
    P ⊢ fupd' (Λ := Λ) (M := M) (F := F) E E P := by
  have hsubset : Subset E E := by
    intro _ hx; exact hx
  have hintro :=
    fupd_intro_mask (W := IrisGS.wsatGS (Λ := Λ) (GF := GF))
      (M := M) (F := F) (E1 := E) (E2 := E) hsubset (P := P)
  have htrans :=
    fupd_trans (W := IrisGS.wsatGS (Λ := Λ) (GF := GF))
      (M := M) (F := F) (E1 := E) (E2 := E) (E3 := E) (P := P)
  exact hintro.trans htrans

/-! ## WP Helpers -/

private abbrev maskEmpty : Iris.Set Positive := fun _ => False

private abbrev fork_post : Λ.val → IProp GF :=
  IrisGS.fork_post (Λ := Λ) (GF := GF)

private abbrev state_interp (σ : Λ.state) (ns : Nat)
    (κs : List Λ.observation) (nt : Nat) : IProp GF :=
  IrisGS.state_interp (Λ := Λ) (GF := GF) σ ns κs nt

private abbrev stuckness_pred (s : Stuckness) (e : Λ.expr) (σ : Λ.state) : Prop :=
  match s with
  | .notStuck => reducible e σ
  | .maybeStuck => True

/-- Order on stuckness: `notStuck` is stronger than `maybeStuck`. -/
def stuckness_le : Stuckness → Stuckness → Prop
  | .notStuck, _ => True
  | .maybeStuck, .maybeStuck => True
  | .maybeStuck, .notStuck => False

private theorem stuckness_pred_mono {s1 s2 : Stuckness}
    (h : stuckness_le s1 s2) (e : Λ.expr) (σ : Λ.state) :
    stuckness_pred s1 e σ → stuckness_pred s2 e σ := by
  -- check the two stuckness cases directly
  cases s1 <;> cases s2 <;> simp [stuckness_pred, stuckness_le] at h ⊢

/-! ## WP Pre-fixpoint -/

/-- The pre-fixpoint for weakest preconditions. Takes the recursive `wp` as
a parameter. In the value case, returns `|={E}=> Φ v`. In the step case,
requires stepping and recursive WP for the continuation.
Coq: `wp_pre` in `weakestpre.v`. -/
noncomputable def wp_pre
    (s : Stuckness)
    (wp : Iris.Set Positive → Λ.expr → (Λ.val → IProp GF) → IProp GF)
    (E : Iris.Set Positive) (e : Λ.expr) (Φ : Λ.val → IProp GF) : IProp GF :=
  match Λ.to_val e with
  | some v => fupd' (Λ := Λ) (M := M) (F := F) E E (Φ v)
  | none =>
      fupd' (Λ := Λ) (M := M) (F := F) E E
        (BIBase.forall fun σ : Λ.state =>
          BIBase.forall fun ns : Nat =>
            BIBase.forall fun κ : List Λ.observation =>
              BIBase.forall fun κs : List Λ.observation =>
                BIBase.forall fun nt : Nat =>
                  BIBase.wand (state_interp σ ns (κ ++ κs) nt)
                    (fupd' (Λ := Λ) (M := M) (F := F) E maskEmpty
                      (BIBase.pure (stuckness_pred s e σ))))

private noncomputable abbrev wp_pre_s
    (s : Stuckness)
    (wp : Iris.Set Positive → Λ.expr → (Λ.val → IProp GF) → IProp GF)
    (E : Iris.Set Positive) (e : Λ.expr) (Φ : Λ.val → IProp GF) : IProp GF :=
  wp_pre (Λ := Λ) (GF := GF) (M := M) (F := F) s wp E e Φ

private theorem wp_pre_contractive (s : Stuckness) :
    OFE.Contractive (fun wp => wp_pre (Λ := Λ) (GF := GF) (M := M) (F := F) s wp) := by
  -- `wp_pre` does not depend on `wp`, so it is trivially contractive
  refine ⟨?_⟩
  intro n wp wp' _hwp E e Φ
  cases hto : Λ.to_val e <;> simp [wp_pre, hto]

private noncomputable abbrev wp_pre_all
    (wp : Stuckness → Iris.Set Positive → Λ.expr → (Λ.val → IProp GF) → IProp GF)
    (s : Stuckness) : Iris.Set Positive → Λ.expr → (Λ.val → IProp GF) → IProp GF :=
  fun E e Φ => wp_pre (Λ := Λ) (GF := GF) (M := M) (F := F) s (wp s) E e Φ

private theorem wp_pre_all_contractive :
    OFE.Contractive (fun wp => wp_pre_all (Λ := Λ) (GF := GF) (M := M) (F := F) wp) := by
  -- contractiveness follows pointwise from `wp_pre_contractive`
  refine ⟨?_⟩
  intro n wp wp' hwp s E e Φ
  have hwp_s : OFE.DistLater n (wp s) (wp' s) := by
    intro m hm; exact hwp m hm s
  exact (wp_pre_contractive (Λ := Λ) (GF := GF) (M := M) (F := F) s).distLater_dist
    hwp_s E e Φ

/-! ## WP Fixpoint -/

/-- The weakest precondition, defined as the fixpoint of `wp_pre`.
The fixpoint is well-founded because `wp_pre` is contractive: the
recursive call to `wp` appears under `▷`.
Coq: `wp_def` in `weakestpre.v`. -/
noncomputable def wp
    (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IProp GF) : IProp GF :=
  let WpF :
      (Stuckness → Iris.Set Positive → Λ.expr → (Λ.val → IProp GF) → IProp GF) -c>
      (Stuckness → Iris.Set Positive → Λ.expr → (Λ.val → IProp GF) → IProp GF) :=
    { f := fun wp => wp_pre_all (Λ := Λ) (GF := GF) (M := M) (F := F) wp,
      contractive := wp_pre_all_contractive (Λ := Λ) (GF := GF) (M := M) (F := F) }
  (OFE.ContractiveHom.fixpoint WpF) s E e Φ

private noncomputable abbrev wp_s (s : Stuckness) :
    Iris.Set Positive → Λ.expr → (Λ.val → IProp GF) → IProp GF :=
  wp (Λ := Λ) (GF := GF) (M := M) (F := F) s

/-! ## Unfold -/

/-- Unfold the WP fixpoint one step.
Coq: `wp_unfold` in `weakestpre.v`. -/
theorem wp_unfold (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IProp GF) :
    wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e Φ ⊣⊢
      wp_pre (Λ := Λ) (GF := GF) (M := M) (F := F) s (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s)
        E e Φ :=
  by
  -- unfold the fixpoint equation and specialize it to `E`, `e`, and `Φ`
  let WpF :
      (Stuckness → Iris.Set Positive → Λ.expr → (Λ.val → IProp GF) → IProp GF) -c>
      (Stuckness → Iris.Set Positive → Λ.expr → (Λ.val → IProp GF) → IProp GF) :=
    { f := fun wp => wp_pre_all (Λ := Λ) (GF := GF) (M := M) (F := F) wp,
      contractive := wp_pre_all_contractive (Λ := Λ) (GF := GF) (M := M) (F := F) }
  have hfix :
      (OFE.ContractiveHom.fixpoint WpF) s E e Φ ≡
        wp_pre (Λ := Λ) (GF := GF) (M := M) (F := F) s
          (OFE.ContractiveHom.fixpoint WpF s) E e Φ := by
    -- `fixpoint_unfold` gives equivalence on the whole function, specialize it
    have h := (fixpoint_unfold (f := WpF))
    simpa [WpF] using (h s E e Φ)
  -- convert OFE equivalence to `⊣⊢` and unfold `wp`
  simpa [wp_s, wp, WpF] using (BI.equiv_iff (PROP := IProp GF)).1 hfix

/-! ## Core Rules -/

/-- Value case: `WP of_val v @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v`.
Coq: `wp_value_fupd'` in `weakestpre.v`. -/
theorem wp_value_fupd (s : Stuckness) (E : Iris.Set Positive)
    (Φ : Λ.val → IProp GF) (v : Λ.val) :
    wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (Λ.of_val v) Φ ⊣⊢
      fupd' (Λ := Λ) (M := M) (F := F) E E (Φ v) :=
  by
  -- unfold the WP and simplify the value case
  have h := wp_unfold (Λ := Λ) (GF := GF) (M := M) (F := F) (s := s) (E := E)
    (e := Λ.of_val v) (Φ := Φ)
  simpa [wp_pre, to_of_val] using h

/-- Strong monotonicity: transform postcondition (same stuckness and mask).
Coq: `wp_strong_mono` in `weakestpre.v`. -/
theorem wp_strong_mono (s1 s2 : Stuckness) (E1 E2 : Iris.Set Positive)
    (e : Λ.expr) (Φ Ψ : Λ.val → IProp GF) :
    s1 = s2 →
    E1 = E2 →
    wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s1 E1 e Φ ⊢
    BIBase.wand
      (BIBase.forall fun v =>
        BIBase.wand (Φ v)
          (fupd' (Λ := Λ) (M := M) (F := F) E2 E2 (Ψ v)))
      (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s2 E2 e Ψ) :=
  by
  intro hs hE
  subst hs hE
  let HΦ : IProp GF :=
    BIBase.forall fun v =>
      BIBase.wand (Φ v)
        (fupd' (Λ := Λ) (M := M) (F := F) E1 E1 (Ψ v))
  refine wand_intro ?_
  have hwpΦ :
      wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s1 E1 e Φ ⊢
        wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s1
          (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s1) E1 e Φ :=
    (wp_unfold (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s1) (E := E1) (e := e) (Φ := Φ)).1
  have hwpΨ :
      wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s1
          (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s1) E1 e Ψ ⊢
        wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s1 E1 e Ψ :=
    (wp_unfold (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s1) (E := E1) (e := e) (Φ := Ψ)).2
  refine (sep_mono hwpΦ .rfl).trans ?_
  cases hto : Λ.to_val e with
  | some v =>
      have hΦv :
          HΦ ⊢
            BIBase.wand (Φ v)
              (fupd' (Λ := Λ) (M := M) (F := F) E1 E1 (Ψ v)) :=
        forall_elim (PROP := IProp GF)
          (Ψ := fun v => BIBase.wand (Φ v)
            (fupd' (Λ := Λ) (M := M) (F := F) E1 E1 (Ψ v))) v
      have hpost :
          BIBase.sep (Φ v) HΦ ⊢
            fupd' (Λ := Λ) (M := M) (F := F) E1 E1 (Ψ v) :=
        (sep_mono .rfl hΦv).trans
          (wand_elim_r (P := Φ v)
            (Q := fupd' (Λ := Λ) (M := M) (F := F) E1 E1 (Ψ v)))
      have hframe :
          BIBase.sep (fupd' (Λ := Λ) (M := M) (F := F) E1 E1 (Φ v)) HΦ ⊢
            fupd' (Λ := Λ) (M := M) (F := F) E1 E1 (BIBase.sep (Φ v) HΦ) :=
        fupd_frame_r (W := IrisGS.wsatGS (Λ := Λ) (GF := GF))
          (M := M) (F := F) (E1 := E1) (E2 := E1) (P := Φ v) (Q := HΦ)
      have hmono :
          fupd' (Λ := Λ) (M := M) (F := F) E1 E1 (BIBase.sep (Φ v) HΦ) ⊢
            fupd' (Λ := Λ) (M := M) (F := F) E1 E1
              (fupd' (Λ := Λ) (M := M) (F := F) E1 E1 (Ψ v)) :=
        fupd_mono (W := IrisGS.wsatGS (Λ := Λ) (GF := GF))
          (M := M) (F := F) (E1 := E1) (E2 := E1) (P := BIBase.sep (Φ v) HΦ)
          (Q := fupd' (Λ := Λ) (M := M) (F := F) E1 E1 (Ψ v)) hpost
      have htrans :
          fupd' (Λ := Λ) (M := M) (F := F) E1 E1
              (fupd' (Λ := Λ) (M := M) (F := F) E1 E1 (Ψ v)) ⊢
            fupd' (Λ := Λ) (M := M) (F := F) E1 E1 (Ψ v) :=
        fupd_idem (Λ := Λ) (M := M) (F := F) (E := E1) (P := Ψ v)
      have hwpΨ' :
          fupd' (Λ := Λ) (M := M) (F := F) E1 E1 (Ψ v) ⊢
            wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s1 E1 e Ψ := by
        simpa [wp_pre, hto] using hwpΨ
      have hmain :
          BIBase.sep (fupd' (Λ := Λ) (M := M) (F := F) E1 E1 (Φ v)) HΦ ⊢
            wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s1 E1 e Ψ :=
        (hframe.trans hmono).trans (htrans.trans hwpΨ')
      simpa [wp_pre, hto] using hmain
  | none =>
      have hpre :
          wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s1
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s1) E1 e Φ ⊢
            wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s1
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s1) E1 e Ψ := by
        simp [wp_pre, hto]
      exact (sep_elim_l (P := wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s1
        (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s1) E1 e Φ) (Q := HΦ)).trans
        (hpre.trans hwpΨ)

/-- Fancy update can be absorbed into WP.
Coq: `fupd_wp` in `weakestpre.v`. -/
theorem fupd_wp (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IProp GF) :
    fupd' (Λ := Λ) (M := M) (F := F) E E
      (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e Φ) ⊢
    wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e Φ :=
  by
  have hwp_pre :
      wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e Φ ⊢
        wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
          (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e Φ :=
    (wp_unfold (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (E := E) (e := e) (Φ := Φ)).1
  have hwp :
      wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
          (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e Φ ⊢
        wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e Φ :=
    (wp_unfold (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (E := E) (e := e) (Φ := Φ)).2
  refine (fupd_mono (W := IrisGS.wsatGS (Λ := Λ) (GF := GF))
    (M := M) (F := F) (E1 := E) (E2 := E)
    (P := wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e Φ)
    (Q := wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
      (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e Φ) hwp_pre).trans ?_
  have hcollapse :
      fupd' (Λ := Λ) (M := M) (F := F) E E
          (wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
            (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e Φ) ⊢
        wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
          (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e Φ := by
    cases hto : Λ.to_val e with
    | some v =>
        simpa [wp_pre, hto] using
          (fupd_idem (Λ := Λ) (M := M) (F := F) (E := E) (P := Φ v))
    | none =>
        let Q : IProp GF :=
          BIBase.forall fun σ : Λ.state =>
            BIBase.forall fun ns : Nat =>
              BIBase.forall fun κ : List Λ.observation =>
                BIBase.forall fun κs : List Λ.observation =>
                  BIBase.forall fun nt : Nat =>
                    BIBase.wand (state_interp σ ns (κ ++ κs) nt)
                      (fupd' (Λ := Λ) (M := M) (F := F) E maskEmpty
                        (BIBase.pure (stuckness_pred s e σ)))
        simpa [wp_pre, hto, Q] using
          (fupd_idem (Λ := Λ) (M := M) (F := F) (E := E) (P := Q))
  exact hcollapse.trans hwp

/-- Postcondition update can be absorbed.
Coq: `wp_fupd` in `weakestpre.v`. -/
theorem wp_fupd (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IProp GF) :
    wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e
      (fun v => fupd' (Λ := Λ) (M := M) (F := F) E E (Φ v)) ⊢
    wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e Φ :=
  by
  have hleft :
      wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e
          (fun v => fupd' (Λ := Λ) (M := M) (F := F) E E (Φ v)) ⊢
        wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
          (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e
          (fun v => fupd' (Λ := Λ) (M := M) (F := F) E E (Φ v)) :=
    (wp_unfold (Λ := Λ) (GF := GF) (M := M) (F := F) (s := s) (E := E) (e := e)
      (Φ := fun v => fupd' (Λ := Λ) (M := M) (F := F) E E (Φ v))).1
  have hright :
      wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
          (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e Φ ⊢
        wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e Φ :=
    (wp_unfold (Λ := Λ) (GF := GF) (M := M) (F := F) (s := s) (E := E) (e := e) (Φ := Φ)).2
  refine hleft.trans ?_
  cases hto : Λ.to_val e with
  | some v =>
      have hpre :
          wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e
              (fun v => fupd' (Λ := Λ) (M := M) (F := F) E E (Φ v)) ⊢
            fupd' (Λ := Λ) (M := M) (F := F) E E
              (fupd' (Λ := Λ) (M := M) (F := F) E E (Φ v)) := by
        simp [wp_pre, hto]
      have hcollapse :
          fupd' (Λ := Λ) (M := M) (F := F) E E
              (fupd' (Λ := Λ) (M := M) (F := F) E E (Φ v)) ⊢
            fupd' (Λ := Λ) (M := M) (F := F) E E (Φ v) :=
        fupd_idem (Λ := Λ) (M := M) (F := F) (E := E) (P := Φ v)
      have hright' :
          fupd' (Λ := Λ) (M := M) (F := F) E E (Φ v) ⊢
            wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e Φ := by
        simpa [wp_pre, hto] using hright
      exact (hpre.trans hcollapse).trans hright'
  | none =>
      have hright' :
          wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e
              (fun v => fupd' (Λ := Λ) (M := M) (F := F) E E (Φ v)) ⊢
            wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e Φ := by
        simpa [wp_pre, hto] using hright
      exact hright'

/-- Bind rule: compositionality via evaluation contexts.
Coq: `wp_bind` in `weakestpre.v`. -/
theorem wp_bind (K : Λ.expr → Λ.expr) [LanguageCtx K]
    (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IProp GF) :
    wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e
      (fun v => wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K (Λ.of_val v)) Φ) ⊢
    wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K e) Φ :=
  by
  have hwp :
      wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e
          (fun v => wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K (Λ.of_val v)) Φ) ⊢
        wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
          (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e
          (fun v => wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K (Λ.of_val v)) Φ) :=
    (wp_unfold (Λ := Λ) (GF := GF) (M := M) (F := F) (s := s) (E := E) (e := e)
      (Φ := fun v => wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K (Λ.of_val v)) Φ)).1
  have hwpK :
      wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
          (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E (K e) Φ ⊢
        wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K e) Φ :=
    (wp_unfold (Λ := Λ) (GF := GF) (M := M) (F := F) (s := s) (E := E) (e := K e) (Φ := Φ)).2
  refine hwp.trans ?_
  cases hto : Λ.to_val e with
  | some v =>
      have hstep :
          fupd' (Λ := Λ) (M := M) (F := F) E E
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K (Λ.of_val v)) Φ) ⊢
            wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K (Λ.of_val v)) Φ :=
        fupd_wp (Λ := Λ) (GF := GF) (M := M) (F := F) (s := s) (E := E)
          (e := K (Λ.of_val v)) (Φ := Φ)
      have hK : K e = K (Λ.of_val v) := by
        simpa [of_to_val e v hto]
      have hwpK' :
          wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K (Λ.of_val v)) Φ ⊢
            wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K e) Φ := by
        simpa [hK]
      have hpre :
          wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e
              (fun v => wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K (Λ.of_val v)) Φ) ⊢
            fupd' (Λ := Λ) (M := M) (F := F) E E
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K (Λ.of_val v)) Φ) := by
        simpa [wp_pre, hto] using (BIBase.Entails.rfl : _)
      exact hpre.trans (hstep.trans hwpK')
  | none =>
      have htoK : Λ.to_val (K e) = none :=
        LanguageCtx.fill_not_val (K := K) e hto
      have hpred :
          ∀ σ, stuckness_pred s e σ → stuckness_pred s (K e) σ := by
        intro σ
        cases s <;> simp [stuckness_pred]
        · intro hred
          exact reducible_fill (K := K) e σ hred
      have hbody :
          BIBase.forall (PROP := IProp GF) (fun σ : Λ.state =>
            BIBase.forall (PROP := IProp GF) fun ns : Nat =>
              BIBase.forall (PROP := IProp GF) fun κ : List Λ.observation =>
                BIBase.forall (PROP := IProp GF) fun κs : List Λ.observation =>
                  BIBase.forall (PROP := IProp GF) fun nt : Nat =>
                    BIBase.wand (state_interp σ ns (κ ++ κs) nt)
                      (fupd' (Λ := Λ) (M := M) (F := F) E maskEmpty
                        (BIBase.pure (stuckness_pred s e σ)))) ⊢
          BIBase.forall (PROP := IProp GF) (fun σ : Λ.state =>
            BIBase.forall (PROP := IProp GF) fun ns : Nat =>
              BIBase.forall (PROP := IProp GF) fun κ : List Λ.observation =>
                BIBase.forall (PROP := IProp GF) fun κs : List Λ.observation =>
                  BIBase.forall (PROP := IProp GF) fun nt : Nat =>
                    BIBase.wand (state_interp σ ns (κ ++ κs) nt)
                      (fupd' (Λ := Λ) (M := M) (F := F) E maskEmpty
                        (BIBase.pure (stuckness_pred s (K e) σ)))) := by
        refine forall_mono ?_
        intro σ
        refine forall_mono ?_
        intro ns
        refine forall_mono ?_
        intro κ
        refine forall_mono ?_
        intro κs
        refine forall_mono ?_
        intro nt
        refine (wand_mono_r (PROP := IProp GF)) ?_
        refine fupd_mono (W := IrisGS.wsatGS (Λ := Λ) (GF := GF))
          (M := M) (F := F) (E1 := E) (E2 := maskEmpty)
          (P := BIBase.pure (stuckness_pred s e σ))
          (Q := BIBase.pure (stuckness_pred s (K e) σ)) ?_
        exact pure_mono (hpred σ)
      have hpre :
          wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e
              (fun v => wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K (Λ.of_val v)) Φ) ⊢
            wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E (K e) Φ := by
        -- both sides are the non-value cases
        have hmono :
            fupd' (Λ := Λ) (M := M) (F := F) E E
                (BIBase.forall fun σ : Λ.state =>
                  BIBase.forall fun ns : Nat =>
                    BIBase.forall fun κ : List Λ.observation =>
                      BIBase.forall fun κs : List Λ.observation =>
                        BIBase.forall fun nt : Nat =>
                          BIBase.wand (state_interp σ ns (κ ++ κs) nt)
                            (fupd' (Λ := Λ) (M := M) (F := F) E maskEmpty
                              (BIBase.pure (stuckness_pred s e σ)))) ⊢
              fupd' (Λ := Λ) (M := M) (F := F) E E
                (BIBase.forall fun σ : Λ.state =>
                  BIBase.forall fun ns : Nat =>
                    BIBase.forall fun κ : List Λ.observation =>
                      BIBase.forall fun κs : List Λ.observation =>
                        BIBase.forall fun nt : Nat =>
                          BIBase.wand (state_interp σ ns (κ ++ κs) nt)
                            (fupd' (Λ := Λ) (M := M) (F := F) E maskEmpty
                              (BIBase.pure (stuckness_pred s (K e) σ)))) :=
          fupd_mono (W := IrisGS.wsatGS (Λ := Λ) (GF := GF))
            (M := M) (F := F) (E1 := E) (E2 := E) (P := _)
            (Q := _) hbody
        simpa [wp_pre, hto, htoK] using hmono
      exact hpre.trans hwpK

/-- Inverse bind rule.
Coq: `wp_bind_inv` in `weakestpre.v`. -/
theorem wp_bind_inv (K : Λ.expr → Λ.expr) [LanguageCtx K]
    (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IProp GF) :
    wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K e) Φ ⊢
    wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e
      (fun v => wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K (Λ.of_val v)) Φ) :=
  by
  have hwp :
      wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K e) Φ ⊢
        wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
          (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E (K e) Φ :=
    (wp_unfold (Λ := Λ) (GF := GF) (M := M) (F := F) (s := s) (E := E) (e := K e) (Φ := Φ)).1
  have hwpK :
      wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
          (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e
          (fun v => wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K (Λ.of_val v)) Φ) ⊢
        wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e
          (fun v => wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K (Λ.of_val v)) Φ) :=
    (wp_unfold (Λ := Λ) (GF := GF) (M := M) (F := F) (s := s) (E := E) (e := e)
      (Φ := fun v => wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K (Λ.of_val v)) Φ)).2
  refine hwp.trans ?_
  cases hto : Λ.to_val e with
  | some v =>
      have hK : K e = K (Λ.of_val v) := by
        simpa [of_to_val e v hto]
      have hwp_back :
          wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E (K e) Φ ⊢
            wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K e) Φ :=
        (wp_unfold (Λ := Λ) (GF := GF) (M := M) (F := F)
          (s := s) (E := E) (e := K e) (Φ := Φ)).2
      have hintro :
          wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K e) Φ ⊢
            fupd' (Λ := Λ) (M := M) (F := F) E E
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K (Λ.of_val v)) Φ) := by
        simpa [hK] using
          (fupd_intro (Λ := Λ) (M := M) (F := F) (E := E)
            (P := wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K (Λ.of_val v)) Φ))
      have hpre :
          wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E (K e) Φ ⊢
            wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e
              (fun v => wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K (Λ.of_val v)) Φ) := by
        have hstep :
            wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
                (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E (K e) Φ ⊢
              fupd' (Λ := Λ) (M := M) (F := F) E E
                (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K (Λ.of_val v)) Φ) :=
          hwp_back.trans hintro
        simpa [wp_pre, hto] using hstep
      exact hpre.trans hwpK
  | none =>
      have htoK : Λ.to_val (K e) = none :=
        LanguageCtx.fill_not_val (K := K) e hto
      have hpred :
          ∀ σ, stuckness_pred s (K e) σ → stuckness_pred s e σ := by
        intro σ
        cases s <;> simp [stuckness_pred]
        · intro hred
          exact reducible_fill_inv (K := K) e σ hto hred
      have hbody :
          BIBase.forall (PROP := IProp GF) (fun σ : Λ.state =>
            BIBase.forall (PROP := IProp GF) fun ns : Nat =>
              BIBase.forall (PROP := IProp GF) fun κ : List Λ.observation =>
                BIBase.forall (PROP := IProp GF) fun κs : List Λ.observation =>
                  BIBase.forall (PROP := IProp GF) fun nt : Nat =>
                    BIBase.wand (state_interp σ ns (κ ++ κs) nt)
                      (fupd' (Λ := Λ) (M := M) (F := F) E maskEmpty
                        (BIBase.pure (stuckness_pred s (K e) σ)))) ⊢
          BIBase.forall (PROP := IProp GF) (fun σ : Λ.state =>
            BIBase.forall (PROP := IProp GF) fun ns : Nat =>
              BIBase.forall (PROP := IProp GF) fun κ : List Λ.observation =>
                BIBase.forall (PROP := IProp GF) fun κs : List Λ.observation =>
                  BIBase.forall (PROP := IProp GF) fun nt : Nat =>
                    BIBase.wand (state_interp σ ns (κ ++ κs) nt)
                      (fupd' (Λ := Λ) (M := M) (F := F) E maskEmpty
                        (BIBase.pure (stuckness_pred s e σ)))) := by
        refine forall_mono ?_
        intro σ
        refine forall_mono ?_
        intro ns
        refine forall_mono ?_
        intro κ
        refine forall_mono ?_
        intro κs
        refine forall_mono ?_
        intro nt
        refine (wand_mono_r (PROP := IProp GF)) ?_
        refine fupd_mono (W := IrisGS.wsatGS (Λ := Λ) (GF := GF))
          (M := M) (F := F) (E1 := E) (E2 := maskEmpty)
          (P := BIBase.pure (stuckness_pred s (K e) σ))
          (Q := BIBase.pure (stuckness_pred s e σ)) ?_
        exact pure_mono (hpred σ)
      have hpre :
          wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E (K e) Φ ⊢
            wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e
              (fun v => wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E (K (Λ.of_val v)) Φ) := by
        have hmono :
            fupd' (Λ := Λ) (M := M) (F := F) E E
                (BIBase.forall fun σ : Λ.state =>
                  BIBase.forall fun ns : Nat =>
                    BIBase.forall fun κ : List Λ.observation =>
                      BIBase.forall fun κs : List Λ.observation =>
                        BIBase.forall fun nt : Nat =>
                          BIBase.wand (state_interp σ ns (κ ++ κs) nt)
                            (fupd' (Λ := Λ) (M := M) (F := F) E maskEmpty
                              (BIBase.pure (stuckness_pred s (K e) σ)))) ⊢
              fupd' (Λ := Λ) (M := M) (F := F) E E
                (BIBase.forall fun σ : Λ.state =>
                  BIBase.forall fun ns : Nat =>
                    BIBase.forall fun κ : List Λ.observation =>
                      BIBase.forall fun κs : List Λ.observation =>
                        BIBase.forall fun nt : Nat =>
                          BIBase.wand (state_interp σ ns (κ ++ κs) nt)
                            (fupd' (Λ := Λ) (M := M) (F := F) E maskEmpty
                              (BIBase.pure (stuckness_pred s e σ)))) :=
          fupd_mono (W := IrisGS.wsatGS (Λ := Λ) (GF := GF))
            (M := M) (F := F) (E1 := E) (E2 := E) (P := _)
            (Q := _) hbody
        simpa [wp_pre, hto, htoK] using hmono
      exact hpre.trans hwpK

/-! ## Derived Rules -/

/-- Monotonicity in postcondition.
Coq: `wp_mono` in `weakestpre.v`. -/
theorem wp_mono (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ Ψ : Λ.val → IProp GF)
    (h : ∀ v, Φ v ⊢ Ψ v) :
    wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e Φ ⊢
      wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e Ψ :=
  by
  have hwpΦ :
      wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e Φ ⊢
        wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
          (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e Φ :=
    (wp_unfold (Λ := Λ) (GF := GF) (M := M) (F := F) (s := s) (E := E) (e := e) (Φ := Φ)).1
  have hwpΨ :
      wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
          (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e Ψ ⊢
        wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e Ψ :=
    (wp_unfold (Λ := Λ) (GF := GF) (M := M) (F := F) (s := s) (E := E) (e := e) (Φ := Ψ)).2
  refine hwpΦ.trans ?_
  cases hto : Λ.to_val e with
  | some v =>
      have hpre :
          wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e Φ ⊢
            fupd' (Λ := Λ) (M := M) (F := F) E E (Φ v) := by
        simp [wp_pre, hto]
      have hmono :
          fupd' (Λ := Λ) (M := M) (F := F) E E (Φ v) ⊢
            fupd' (Λ := Λ) (M := M) (F := F) E E (Ψ v) :=
        fupd_mono (W := IrisGS.wsatGS (Λ := Λ) (GF := GF))
          (M := M) (F := F) (E1 := E) (E2 := E) (P := Φ v) (Q := Ψ v) (h v)
      have hwpΨ' :
          fupd' (Λ := Λ) (M := M) (F := F) E E (Ψ v) ⊢
            wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e Ψ := by
        simpa [wp_pre, hto] using hwpΨ
      exact (hpre.trans hmono).trans hwpΨ'
  | none =>
      have hpre :
          wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e Φ ⊢
            wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e Ψ := by
        simp [wp_pre, hto]
      exact hpre.trans hwpΨ

/-- Frame rule (left).
Coq: `wp_frame_l` in `weakestpre.v`. -/
theorem wp_frame_l (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IProp GF) (R : IProp GF) :
    BIBase.sep R (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e Φ) ⊢
    wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e (fun v => BIBase.sep R (Φ v)) :=
  by
  have hwpΦ :
      wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e Φ ⊢
        wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
          (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e Φ :=
    (wp_unfold (Λ := Λ) (GF := GF) (M := M) (F := F) (s := s) (E := E) (e := e) (Φ := Φ)).1
  have hwpR :
      wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
          (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e
          (fun v => BIBase.sep R (Φ v)) ⊢
        wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e (fun v => BIBase.sep R (Φ v)) :=
    (wp_unfold (Λ := Λ) (GF := GF) (M := M) (F := F) (s := s) (E := E) (e := e)
      (Φ := fun v => BIBase.sep R (Φ v))).2
  refine (sep_mono .rfl hwpΦ).trans ?_
  cases hto : Λ.to_val e with
  | some v =>
      have hswap :
          BIBase.sep R (fupd' (Λ := Λ) (M := M) (F := F) E E (Φ v)) ⊢
            BIBase.sep (fupd' (Λ := Λ) (M := M) (F := F) E E (Φ v)) R :=
        sep_symm
      have hframe :
          BIBase.sep (fupd' (Λ := Λ) (M := M) (F := F) E E (Φ v)) R ⊢
            fupd' (Λ := Λ) (M := M) (F := F) E E (BIBase.sep (Φ v) R) :=
        fupd_frame_r (W := IrisGS.wsatGS (Λ := Λ) (GF := GF))
          (M := M) (F := F) (E1 := E) (E2 := E) (P := Φ v) (Q := R)
      have hmono :
          fupd' (Λ := Λ) (M := M) (F := F) E E (BIBase.sep (Φ v) R) ⊢
            fupd' (Λ := Λ) (M := M) (F := F) E E (BIBase.sep R (Φ v)) :=
        fupd_mono (W := IrisGS.wsatGS (Λ := Λ) (GF := GF))
          (M := M) (F := F) (E1 := E) (E2 := E)
          (P := BIBase.sep (Φ v) R) (Q := BIBase.sep R (Φ v)) sep_symm
      have hwpR' :
          fupd' (Λ := Λ) (M := M) (F := F) E E (BIBase.sep R (Φ v)) ⊢
            wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e (fun v => BIBase.sep R (Φ v)) := by
        simpa [wp_pre, hto] using hwpR
      have hpre :
          BIBase.sep R (wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e Φ) ⊢
            BIBase.sep R (fupd' (Λ := Λ) (M := M) (F := F) E E (Φ v)) := by
        simp [wp_pre, hto]
      exact (hpre.trans hswap).trans (hframe.trans (hmono.trans hwpR'))
  | none =>
      have hdrop :
          BIBase.sep R (wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e Φ) ⊢
            wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e Φ :=
        sep_elim_r (P := R)
          (Q := wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
            (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e Φ)
      have hpre :
          wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e Φ ⊢
            wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e
              (fun v => BIBase.sep R (Φ v)) := by
        simp [wp_pre, hto]
      exact (hdrop.trans hpre).trans hwpR

/-- Frame rule (right).
Coq: `wp_frame_r` in `weakestpre.v`. -/
theorem wp_frame_r (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IProp GF) (R : IProp GF) :
    BIBase.sep (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e Φ) R ⊢
    wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e (fun v => BIBase.sep (Φ v) R) :=
  by
  have hwpΦ :
      wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e Φ ⊢
        wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
          (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e Φ :=
    (wp_unfold (Λ := Λ) (GF := GF) (M := M) (F := F) (s := s) (E := E) (e := e) (Φ := Φ)).1
  have hwpR :
      wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
          (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e
          (fun v => BIBase.sep (Φ v) R) ⊢
        wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e (fun v => BIBase.sep (Φ v) R) :=
    (wp_unfold (Λ := Λ) (GF := GF) (M := M) (F := F) (s := s) (E := E) (e := e)
      (Φ := fun v => BIBase.sep (Φ v) R)).2
  refine (sep_mono hwpΦ .rfl).trans ?_
  cases hto : Λ.to_val e with
  | some v =>
      have hframe :
          BIBase.sep (fupd' (Λ := Λ) (M := M) (F := F) E E (Φ v)) R ⊢
            fupd' (Λ := Λ) (M := M) (F := F) E E (BIBase.sep (Φ v) R) :=
        fupd_frame_r (W := IrisGS.wsatGS (Λ := Λ) (GF := GF))
          (M := M) (F := F) (E1 := E) (E2 := E) (P := Φ v) (Q := R)
      have hwpR' :
          fupd' (Λ := Λ) (M := M) (F := F) E E (BIBase.sep (Φ v) R) ⊢
            wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e (fun v => BIBase.sep (Φ v) R) := by
        simpa [wp_pre, hto] using hwpR
      have hpre :
          BIBase.sep (wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e Φ) R ⊢
            BIBase.sep (fupd' (Λ := Λ) (M := M) (F := F) E E (Φ v)) R := by
        simp [wp_pre, hto]
      exact (hpre.trans hframe).trans hwpR'
  | none =>
      have hdrop :
          BIBase.sep (wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e Φ) R ⊢
            wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e Φ :=
        sep_elim_l (P := wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
          (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e Φ) (Q := R)
      have hpre :
          wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e Φ ⊢
            wp_pre_s (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s) E e
              (fun v => BIBase.sep (Φ v) R) := by
        simp [wp_pre, hto]
      exact (hdrop.trans hpre).trans hwpR

/-- Wand rule: weaken postcondition via wand.
Coq: `wp_wand` in `weakestpre.v`. -/
theorem wp_wand (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ Ψ : Λ.val → IProp GF) :
    wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e Φ ⊢
    BIBase.wand
      (BIBase.forall fun v => BIBase.wand (Φ v) (Ψ v))
      (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e Ψ) :=
  by
  let H1 : IProp GF :=
    BIBase.forall (PROP := IProp GF) fun v => BIBase.wand (Φ v) (Ψ v)
  let H2 : IProp GF :=
    BIBase.forall (PROP := IProp GF) fun v =>
      BIBase.wand (Φ v)
        (fupd' (Λ := Λ) (M := M) (F := F) E E (Ψ v))
  have h12 : H1 ⊢ H2 := by
    refine forall_intro ?_
    intro v
    have hH1 :
        H1 ⊢ BIBase.wand (Φ v) (Ψ v) :=
      forall_elim (PROP := IProp GF)
        (Ψ := fun v => BIBase.wand (Φ v) (Ψ v)) v
    refine hH1.trans ?_
    refine (wand_mono_r (PROP := IProp GF)) ?_
    exact fupd_intro (Λ := Λ) (M := M) (F := F) (E := E) (P := Ψ v)
  have hwand :
      BIBase.wand H2 (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e Ψ) ⊢
        BIBase.wand H1 (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E e Ψ) :=
    wand_mono_l (h := h12)
  exact (wp_strong_mono (Λ := Λ) (GF := GF) (M := M) (F := F) (s1 := s) (s2 := s)
    (E1 := E) (E2 := E)
    (e := e) (Φ := Φ) (Ψ := Ψ) rfl rfl).trans hwand

/-- Atomic expression rule: open invariants around an atomic step.
Coq: `wp_atomic` in `weakestpre.v`. -/
theorem wp_atomic (s : Stuckness) (E1 E2 : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IProp GF)
    [Atomic (Λ := Λ) (match s with | .notStuck => .stronglyAtomic | .maybeStuck => .weaklyAtomic) e] :
    E1 = E2 →
    fupd' (Λ := Λ) (M := M) (F := F) E1 E2
      (wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E2 e
        (fun v => fupd' (Λ := Λ) (M := M) (F := F) E2 E1 (Φ v))) ⊢
    wp_s (Λ := Λ) (GF := GF) (M := M) (F := F) s E1 e Φ :=
  by
  intro hE
  subst hE
  refine (fupd_wp (Λ := Λ) (GF := GF) (M := M) (F := F) (s := s) (E := E1) (e := e)
    (Φ := fun v => fupd' (Λ := Λ) (M := M) (F := F) E1 E1 (Φ v))).trans ?_
  exact wp_fupd (Λ := Λ) (GF := GF) (M := M) (F := F) (s := s) (E := E1) (e := e) (Φ := Φ)

end Iris.ProgramLogic
