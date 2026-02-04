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
wp_pre W s wp W E e Φ :=
  match to_val e with
  | Some v => |={E}=> Φ v
  | None => ∀ σ ns κ κs nt,
      state_interp σ ns (κ ++ κs) nt ={E,∅}=∗
        ⌜if s is NotStuck then reducible e σ else True⌝ ∗
        ∀ e2 σ2 efs, ⌜prim_step e σ κ e2 σ2 efs⌝ ={∅}▷=∗^(S n) |={∅,E}=>
        state_interp σ2 (S ns) κs (length efs + nt) ∗
        wp W E e2 Φ ∗
        [∗ list] ef ∈ efs, wp W ⊤ ef fork_post
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
variable [FiniteMap Positive M] [HeapFiniteMap Positive M]
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
variable {W : WsatGS GF}

private noncomputable abbrev fupd' (W : WsatGS GF)
    (E1 E2 : Iris.Set Positive) (P : IPropWsat GF M F) : IPropWsat GF M F :=
  uPred_fupd (M := M) (F := F) W E1 E2 P

private abbrev maskEmpty : Iris.Set Positive := fun _ => False

private theorem fupd_idem (E : Iris.Set Positive) (P : IPropWsat GF M F) :
    fupd' W E E
        (fupd' W E E P) ⊢
      fupd' W E E P := by
  simpa using
    (Iris.BaseLogic.fupd_trans (W := W) (M := M) (F := F)
      (E1 := E) (E2 := E) (E3 := E) (P := P))

private theorem fupd_intro (E : Iris.Set Positive) (P : IPropWsat GF M F) :
    P ⊢ fupd' W E E P := by
  have hsubset : Subset E E := by
    intro _ hx; exact hx
  have hintro :=
    Iris.BaseLogic.fupd_intro_mask (W := W) (M := M) (F := F)
      (E1 := E) (E2 := E) hsubset (P := P)
  have htrans :=
    Iris.BaseLogic.fupd_trans (W := W) (M := M) (F := F)
      (E1 := E) (E2 := E) (E3 := E) (P := P)
  exact hintro.trans htrans

private abbrev maskDiff (E1 E2 : Iris.Set Positive) : Iris.Set Positive :=
  -- points in `E2` but not in `E1`
  fun i => E2 i ∧ ¬E1 i

private theorem fupd_mask_mono (E1 E2 : Iris.Set Positive) (h : Subset E1 E2)
    (P : IPropWsat GF M F) :
    fupd' W E1 E1 P ⊢
      fupd' W E2 E2 P := by
  -- frame the mask difference, then rejoin
  let Ef : Iris.Set Positive := maskDiff E1 E2
  have hdisj : CoPset.Disjoint (mask E1) (mask Ef) := by
    intro i hboth
    exact hboth.2.2 hboth.1
  have hunion : Iris.union E1 Ef = E2 := by
    funext i
    apply propext
    constructor
    · intro h'
      cases h' with
      | inl hE1 => exact h i hE1
      | inr hEf => exact hEf.1
    · intro hE2
      by_cases hE1 : E1 i
      · exact Or.inl hE1
      · exact Or.inr ⟨hE2, hE1⟩
  have hframe :=
    Iris.BaseLogic.fupd_mask_frame_r (W := W) (M := M) (F := F)
      (E1 := E1) (E2 := E1) (Ef := Ef) (P := P) hdisj
  have hframe' :
      fupd' W E1 E1 P ⊢
      fupd' W (Iris.union E1 Ef) (Iris.union E1 Ef) P := by
    simpa [Iris.union] using hframe
  simpa [hunion] using hframe'

private theorem fupd_close_mask (E1 E2 : Iris.Set Positive) (P : IPropWsat GF M F) :
    fupd' W maskEmpty E1
        (BIBase.sep P (fupd' W E1 E2 (BIBase.emp : IProp GF))) ⊢
      fupd' W maskEmpty E2 P := by
  -- close the mask using the framed update and `Iris.BaseLogic.fupd_trans`
  have hframe :
      BIBase.sep (fupd' W E1 E2 (BIBase.emp : IProp GF)) P ⊢
        fupd' W E1 E2 P := by
    have hmono :
        fupd' W E1 E2 (BIBase.sep (BIBase.emp : IProp GF) P) ⊢
          fupd' W E1 E2 P :=
      Iris.BaseLogic.fupd_mono (W := W) (M := M) (F := F)
        (E1 := E1) (E2 := E2)
        (P := BIBase.sep (BIBase.emp : IProp GF) P) (Q := P) (emp_sep (P := P)).1
    exact (Iris.BaseLogic.fupd_frame_r (W := W)
      (M := M) (F := F) (E1 := E1) (E2 := E2)
      (P := BIBase.emp) (Q := P)).trans hmono
  have hframe' :
      BIBase.sep P (fupd' W E1 E2 (BIBase.emp : IProp GF)) ⊢
        fupd' W E1 E2 P := by
    exact sep_symm.trans hframe
  have hmono :
      fupd' W maskEmpty E1
          (BIBase.sep P (fupd' W E1 E2 (BIBase.emp : IProp GF))) ⊢
        fupd' W maskEmpty E1
          (fupd' W E1 E2 P) :=
    Iris.BaseLogic.fupd_mono (W := W) (M := M) (F := F)
      (E1 := maskEmpty) (E2 := E1)
      (P := BIBase.sep P (fupd' W E1 E2 (BIBase.emp : IProp GF)))
      (Q := fupd' W E1 E2 P) hframe'
  exact hmono.trans <|
    Iris.BaseLogic.fupd_trans (W := W) (M := M) (F := F)
      (E1 := maskEmpty) (E2 := E1) (E3 := E2) (P := P)

private theorem fupd_mask_subseteq_apply (E1 E2 : Iris.Set Positive)
    (h : Subset E1 E2) (P : IPropWsat GF M F) :
    fupd' W E1 maskEmpty P ⊢
      fupd' W E2 maskEmpty
        (BIBase.sep P (fupd' W E1 E2 (BIBase.emp : IProp GF))) := by
  -- open the larger mask, frame the computation, then re-close
  have hclose : (True : IProp GF) ⊢
      fupd' W E2 E1
        (fupd' W E1 E2 (BIBase.emp : IProp GF)) :=
    Iris.BaseLogic.fupd_mask_subseteq (W := W) (M := M) (F := F)
      (E1 := E2) (E2 := E1) h
  refine (true_sep_2 (PROP := IProp GF) (P := fupd' W E1 maskEmpty P)).trans ?_
  refine (sep_mono hclose .rfl).trans ?_
  refine (Iris.BaseLogic.fupd_frame_r (W := W) (M := M) (F := F)
    (E1 := E2) (E2 := E1)
    (P := fupd' W E1 E2 (BIBase.emp : IProp GF))
    (Q := fupd' W E1 maskEmpty P)).trans ?_
  refine (Iris.BaseLogic.fupd_mono (W := W) (M := M) (F := F)
    (E1 := E2) (E2 := E1) (P := _)
    (Q := fupd' W E1 maskEmpty
      (BIBase.sep P (fupd' W E1 E2 (BIBase.emp : IProp GF)))) ?_).trans ?_
  · -- move the closing update inside the inner `fupd`
    refine (sep_symm.trans ?_)
    exact Iris.BaseLogic.fupd_frame_r (W := W) (M := M) (F := F)
      (E1 := E1) (E2 := maskEmpty)
      (P := P) (Q := fupd' W E1 E2 (BIBase.emp : IProp GF))
  -- compose the nested updates to close the mask
  exact Iris.BaseLogic.fupd_trans (W := W) (M := M) (F := F)
    (E1 := E2) (E2 := E1) (E3 := maskEmpty)
    (P := BIBase.sep P (fupd' W E1 E2 (BIBase.emp : IProp GF)))

private theorem fupd_forall {A : Type _} (E1 E2 : Iris.Set Positive)
    (Φ : A → IPropWsat GF M F) :
    fupd' W E1 E2 (BIBase.forall Φ) ⊢
      BIBase.forall fun a => fupd' W E1 E2 (Φ a) := by
  -- commute `fupd` with `∀` using monotonicity
  refine forall_intro ?_; intro a
  have hmono :
      BIBase.forall Φ ⊢ Φ a :=
    forall_elim (PROP := IProp GF) (Ψ := Φ) a
  exact (Iris.BaseLogic.fupd_mono (W := W) (M := M) (F := F)
    (E1 := E1) (E2 := E2) (P := BIBase.forall Φ) (Q := Φ a) hmono)

private theorem fupd_wand (E1 E2 : Iris.Set Positive)
    (P Q : IPropWsat GF M F) :
    fupd' W E1 E2 (BIBase.wand P Q) ⊢
      BIBase.wand P (fupd' W E1 E2 Q) := by
  -- frame a premise through the update, then eliminate the wand
  refine wand_intro ?_
  have hframe :
      BIBase.sep (fupd' W E1 E2 (BIBase.wand P Q)) P ⊢
        fupd' W E1 E2 (BIBase.sep (BIBase.wand P Q) P) :=
    Iris.BaseLogic.fupd_frame_r (W := W) (M := M) (F := F)
      (E1 := E1) (E2 := E2) (P := BIBase.wand P Q) (Q := P)
  have hmono :
      BIBase.sep (BIBase.wand P Q) P ⊢ Q :=
    wand_elim_l (P := P) (Q := Q)
  exact (hframe.trans
    (Iris.BaseLogic.fupd_mono (W := W) (M := M) (F := F)
      (E1 := E1) (E2 := E2)
      (P := BIBase.sep (BIBase.wand P Q) P) (Q := Q) hmono))

/-! ## WP Helpers -/

private abbrev fork_post : Λ.val → IPropWsat GF M F :=
  (inst.fork_post : Λ.val → IPropWsat GF M F)

private abbrev state_interp (σ : Λ.state) (ns : Nat)
    (κs : List Λ.observation) (nt : Nat) : IPropWsat GF M F :=
  (inst.state_interp σ ns κs nt : IPropWsat GF M F)

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

/-- Non-value case of the WP pre-fixpoint.
Coq: non-value branch of `wp_pre W` in `weakestpre.v`. -/
noncomputable def wp_pre_step (W : WsatGS GF)
    (s : Stuckness)
    (wp : Iris.Set Positive → Λ.expr → (Λ.val → IPropWsat GF M F) → IPropWsat GF M F)
    (E : Iris.Set Positive) (e : Λ.expr) (Φ : Λ.val → IPropWsat GF M F) : IPropWsat GF M F :=
  -- quantify over the machine state and require a step + recursive WP
  BIBase.forall fun σ : Λ.state =>
    BIBase.forall fun ns : Nat =>
      BIBase.forall fun κ : List Λ.observation =>
        BIBase.forall fun κs : List Λ.observation =>
          BIBase.forall fun nt : Nat =>
            BIBase.wand (state_interp σ ns (κ ++ κs) nt) <|
              fupd' W E maskEmpty <|
                BIBase.sep (BIBase.pure (stuckness_pred s e σ)) <|
                  BIBase.forall fun e2 : Λ.expr =>
                    BIBase.forall fun σ2 : Λ.state =>
                      BIBase.forall fun efs : List Λ.expr =>
                        BIBase.wand (BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs)) <|
                          fupd' W maskEmpty E <|
                            BIBase.later <|
                              BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt)) <|
                                BIBase.sep (wp E e2 Φ)
                                  (big_sepL (fun _ ef => wp Iris.Set.univ ef fork_post) efs)

/-- The pre-fixpoint for weakest preconditions. Takes the recursive `wp W` as
a parameter. In the value case, returns `|={E}=> Φ v`. In the step case,
requires stepping and recursive WP for the continuation.
Coq: `wp_pre W` in `weakestpre.v`. -/
noncomputable def wp_pre (W : WsatGS GF)
    (s : Stuckness)
    (wp : Iris.Set Positive → Λ.expr → (Λ.val → IPropWsat GF M F) → IPropWsat GF M F)
    (E : Iris.Set Positive) (e : Λ.expr) (Φ : Λ.val → IPropWsat GF M F) : IPropWsat GF M F :=
  match Λ.to_val e with
  | some v => fupd' W E E (Φ v)
  | none => wp_pre_step W s wp E e Φ

private noncomputable abbrev wp_pre_s (W : WsatGS GF)
    (s : Stuckness)
    (wp : Iris.Set Positive → Λ.expr → (Λ.val → IPropWsat GF M F) → IPropWsat GF M F)
    (E : Iris.Set Positive) (e : Λ.expr) (Φ : Λ.val → IPropWsat GF M F) : IPropWsat GF M F :=
  wp_pre W s wp E e Φ

private theorem wp_pre_contractive (W : WsatGS GF) (s : Stuckness) :
    OFE.Contractive (fun (wp :
      Iris.Set Positive → Λ.expr → (Λ.val → IPropWsat GF M F) → IPropWsat GF M F) =>
      wp_pre W s wp) := by
  -- the recursive calls are guarded by `▷`, so contractiveness holds
  refine ⟨?_⟩
  intro n wp wp' _hwp E e Φ
  cases hto : Λ.to_val e with
  | some v =>
      -- value case does not depend on the recursive argument
      simp [wp_pre, hto]
  | none =>
      -- non-value case: unfold and push non-expansiveness under binders/`▷`
      simp [wp_pre, hto, wp_pre_step]
      refine (forall_ne (PROP := IProp GF)) ?_
      intro σ
      refine (forall_ne (PROP := IProp GF)) ?_
      intro ns
      refine (forall_ne (PROP := IProp GF)) ?_
      intro κ
      refine (forall_ne (PROP := IProp GF)) ?_
      intro κs
      refine (forall_ne (PROP := IProp GF)) ?_
      intro nt
      refine (wand_ne.ne .rfl ?_)
      refine (uPred_fupd_ne (W := W) (M := M) (F := F)
        (E1 := E) (E2 := maskEmpty)).ne ?_
      refine (sep_ne.ne .rfl ?_)
      refine (forall_ne (PROP := IProp GF)) ?_
      intro e2
      refine (forall_ne (PROP := IProp GF)) ?_
      intro σ2
      refine (forall_ne (PROP := IProp GF)) ?_
      intro efs
      refine (wand_ne.ne .rfl ?_)
      -- the recursive calls are under `▷`, making the function contractive
      have hcont : OFE.DistLater n
          (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
            (BIBase.sep (wp E e2 Φ)
              (big_sepL (fun _ ef => wp Iris.Set.univ ef fork_post) efs)))
          (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
            (BIBase.sep (wp' E e2 Φ)
              (big_sepL (fun _ ef => wp' Iris.Set.univ ef fork_post) efs))) := by
        intro m hm
        have hwp_main : wp E e2 Φ ≡{m}≡ wp' E e2 Φ := (_hwp m hm) E e2 Φ
        have hwp_fork :
            ∀ (i : Nat) ef, efs[i]? = some ef →
              wp Iris.Set.univ ef fork_post ≡{m}≡ wp' Iris.Set.univ ef fork_post := by
          -- the forked WPs are pointwise related by the IH
          intro _ ef _
          exact (_hwp m hm) Iris.Set.univ ef fork_post
        have hbig :
            big_sepL (fun _ ef => wp Iris.Set.univ ef fork_post) efs ≡{m}≡
              big_sepL (fun _ ef => wp' Iris.Set.univ ef fork_post) efs :=
          big_sepL_ne (PROP := IProp GF)
            (Φ := fun _ ef => wp Iris.Set.univ ef fork_post)
            (Ψ := fun _ ef => wp' Iris.Set.univ ef fork_post) (l := efs) hwp_fork
        have hsep :
            BIBase.sep (wp E e2 Φ)
                (big_sepL (fun _ ef => wp Iris.Set.univ ef fork_post) efs) ≡{m}≡
              BIBase.sep (wp' E e2 Φ)
                (big_sepL (fun _ ef => wp' Iris.Set.univ ef fork_post) efs) :=
          sep_ne.ne hwp_main hbig
        exact sep_ne.ne .rfl hsep
      have hlater :
          BIBase.later
              (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                (BIBase.sep (wp E e2 Φ)
                  (big_sepL (fun _ ef => wp Iris.Set.univ ef fork_post) efs))) ≡{n}≡
            BIBase.later
              (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                (BIBase.sep (wp' E e2 Φ)
                  (big_sepL (fun _ ef => wp' Iris.Set.univ ef fork_post) efs))) :=
        (OFE.Contractive.distLater_dist
          (f := BIBase.later (PROP := IProp GF)) hcont)
      exact (uPred_fupd_ne (W := W) (M := M) (F := F)
        (E1 := maskEmpty) (E2 := E)).ne hlater

private noncomputable abbrev wp_pre_all (W : WsatGS GF)
    (wp : Stuckness → Iris.Set Positive → Λ.expr → (Λ.val → IPropWsat GF M F) → IPropWsat GF M F)
    (s : Stuckness) : Iris.Set Positive → Λ.expr → (Λ.val → IPropWsat GF M F) → IPropWsat GF M F :=
  fun E e Φ => wp_pre W s (wp s) E e Φ

private theorem wp_pre_all_contractive (W : WsatGS GF) :
    OFE.Contractive (fun (wp :
      Stuckness → Iris.Set Positive → Λ.expr → (Λ.val → IPropWsat GF M F) → IPropWsat GF M F) =>
      wp_pre_all W wp) := by
  -- contractiveness follows pointwise from `wp_pre_contractive`
  refine ⟨?_⟩
  intro n wp wp' hwp s E e Φ
  have hwp_s : OFE.DistLater n (wp s) (wp' s) := by
    intro m hm; exact hwp m hm s
  exact (wp_pre_contractive W s).distLater_dist
    hwp_s E e Φ

/-! ## WP Fixpoint -/

/-- The weakest precondition, defined as the fixpoint of `wp_pre W`.
The fixpoint is well-founded because `wp_pre W` is contractive: the
recursive call to `wp W` appears under `▷`.
Coq: `wp_def` in `weakestpre.v`. -/
noncomputable def wp (W : WsatGS GF)
    (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IPropWsat GF M F) : IPropWsat GF M F :=
  let WpF :
      (Stuckness → Iris.Set Positive → Λ.expr → (Λ.val → IPropWsat GF M F) → IPropWsat GF M F) -c>
      (Stuckness → Iris.Set Positive → Λ.expr → (Λ.val → IPropWsat GF M F) → IPropWsat GF M F) :=
    { f := fun wp => wp_pre_all W wp,
      contractive := wp_pre_all_contractive W }
  (OFE.ContractiveHom.fixpoint WpF) s E e Φ

private noncomputable abbrev wp_s (W : WsatGS GF) (s : Stuckness) :
    Iris.Set Positive → Λ.expr → (Λ.val → IPropWsat GF M F) → IPropWsat GF M F :=
  wp W s

/-! ## Unfold -/

/-- Unfold the WP fixpoint one step.
Coq: `wp_unfold` in `weakestpre.v`. -/
theorem wp_unfold (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IPropWsat GF M F) :
    wp_s W s E e Φ ⊣⊢
      wp_pre W s (wp_s W s)
        E e Φ :=
  by
  -- unfold the fixpoint equation and specialize it to `E`, `e`, and `Φ`
  let WpF :
      (Stuckness → Iris.Set Positive → Λ.expr → (Λ.val → IPropWsat GF M F) → IPropWsat GF M F) -c>
      (Stuckness → Iris.Set Positive → Λ.expr → (Λ.val → IPropWsat GF M F) → IPropWsat GF M F) :=
    { f := fun wp => wp_pre_all W wp,
      contractive := wp_pre_all_contractive W }
  have hfix :
      (OFE.ContractiveHom.fixpoint WpF) s E e Φ ≡
        wp_pre W s
          (OFE.ContractiveHom.fixpoint WpF s) E e Φ := by
    -- `fixpoint_unfold` gives equivalence on the whole function, specialize it
    have h := (fixpoint_unfold (f := WpF))
    simpa [WpF] using (h s E e Φ)
  -- convert OFE equivalence to `⊣⊢` and unfold `wp W`
  simpa [wp_s, wp, WpF] using (BI.equiv_iff (PROP := IProp GF)).1 hfix

/-! ## Core Rules -/

/-- Value case: `WP of_val v @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v`.
Coq: `wp_value_fupd' W` in `weakestpre.v`. -/
theorem wp_value_fupd (s : Stuckness) (E : Iris.Set Positive)
    (Φ : Λ.val → IPropWsat GF M F) (v : Λ.val) :
    wp_s W s E (Λ.of_val v) Φ ⊣⊢
      fupd' W E E (Φ v) :=
  by
  -- unfold the WP and simplify the value case
  have h := wp_unfold (W := W) (s := s) (E := E)
    (e := Λ.of_val v) (Φ := Φ)
  simpa [wp_pre, to_of_val] using h

private abbrev wp_post (W : WsatGS GF) (E : Iris.Set Positive)
    (Φ Ψ : Λ.val → IPropWsat GF M F) : IPropWsat GF M F :=
  BIBase.forall fun v =>
    BIBase.wand (Φ v)
      (fupd' W E E (Ψ v))

private theorem wp_post_fork :
    (BIBase.pure True : IPropWsat GF M F) ⊢
      wp_post (Λ := Λ) W Iris.Set.univ
        (fork_post (Λ := Λ)) (fork_post (Λ := Λ)) := by
  -- build the postcondition transformer for forked threads
  refine forall_intro ?_; intro v
  refine wand_intro ?_
  -- drop the `True` frame before introducing the update
  refine (sep_elim_r (PROP := IProp GF) (P := (BIBase.pure True : IProp GF)) (Q := fork_post v)).trans ?_
  exact fupd_intro (E := Iris.Set.univ) (P := fork_post v)

omit [ElemG GF (COFE.constOF CoPsetDisj)] [ElemG GF (COFE.constOF GSetDisj)] in
private theorem later_big_sepL {A : Type _}
    (Φ : Nat → A → IProp GF) (l : List A) :
    BIBase.later (big_sepL Φ l) ⊣⊢
      big_sepL (fun i x => BIBase.later (Φ i x)) l := by
  -- distribute `▷` over the list spine using `later_sep`
  induction l generalizing Φ with
  | nil =>
      -- base case: `▷ emp ⊣⊢ emp`
      simpa [big_sepL_nil] using (later_emp (PROP := IProp GF))
  | cons x xs ih =>
      -- use IH on the shifted predicate for the tail
      have ih' := ih (Φ := fun n x => Φ (n + 1) x)
      -- inductive step: split/merge over head and tail
      refine ⟨?_, ?_⟩
      · simp [big_sepL_cons]
        refine (later_sep (PROP := IProp GF) (P := Φ 0 x)
          (Q := big_sepL (fun n => Φ (n + 1)) xs)).1.trans ?_
        exact sep_mono .rfl ih'.1
      · simp [big_sepL_cons]
        refine (sep_mono .rfl ih'.2).trans ?_
        exact (later_sep (PROP := IProp GF) (P := Φ 0 x)
          (Q := big_sepL (fun n => Φ (n + 1)) xs)).2

omit inst in
private theorem wp_strong_mono_value
    (E1 E2 : Iris.Set Positive) (Φ Ψ : Λ.val → IPropWsat GF M F)
    (v : Λ.val) (hE : Subset E1 E2) :
    BIBase.sep (fupd' W E1 E1 (Φ v))
        (wp_post W E2 Φ Ψ) ⊢
      fupd' W E2 E2 (Ψ v) := by
  -- push the postcondition transformer through the masked update
  have hΦv :
      wp_post W E2 Φ Ψ ⊢
        BIBase.wand (Φ v)
          (fupd' W E2 E2 (Ψ v)) :=
    forall_elim (PROP := IProp GF)
      (Ψ := fun v => BIBase.wand (Φ v)
        (fupd' W E2 E2 (Ψ v))) v
  have hpost :
      BIBase.sep (Φ v)
          (wp_post W E2 Φ Ψ) ⊢
        fupd' W E2 E2 (Ψ v) :=
    (sep_mono .rfl hΦv).trans
      (wand_elim_r (P := Φ v)
        (Q := fupd' W E2 E2 (Ψ v)))
  have hmask :
      fupd' W E1 E1 (Φ v) ⊢
        fupd' W E2 E2 (Φ v) :=
    fupd_mask_mono (E1 := E1) (E2 := E2) hE (P := Φ v)
  have hframe :
      BIBase.sep (fupd' W E2 E2 (Φ v))
          (wp_post W E2 Φ Ψ) ⊢
        fupd' W E2 E2
          (BIBase.sep (Φ v)
            (wp_post W E2 Φ Ψ)) :=
    Iris.BaseLogic.fupd_frame_r (W := W)
      (M := M) (F := F) (E1 := E2) (E2 := E2) (P := Φ v)
      (Q := wp_post W E2 Φ Ψ)
  have hmono :
      fupd' W E2 E2
          (BIBase.sep (Φ v)
            (wp_post W E2 Φ Ψ)) ⊢
        fupd' W E2 E2
          (fupd' W E2 E2 (Ψ v)) :=
    Iris.BaseLogic.fupd_mono (W := W)
      (M := M) (F := F) (E1 := E2) (E2 := E2)
      (P := BIBase.sep (Φ v)
        (wp_post W E2 Φ Ψ))
      (Q := fupd' W E2 E2 (Ψ v)) hpost
  have hcollapse :
      fupd' W E2 E2
          (fupd' W E2 E2 (Ψ v)) ⊢
        fupd' W E2 E2 (Ψ v) :=
    fupd_idem (E := E2) (P := Ψ v)
  exact (sep_mono hmask .rfl).trans (hframe.trans (hmono.trans hcollapse))

private def wp_strong_mono_body : IPropWsat GF M F :=
  -- strong monotonicity packaged as an Iris proposition
  BIBase.forall (fun s1 : Stuckness =>
    BIBase.forall (fun s2 : Stuckness =>
      BIBase.forall (fun E1 : Iris.Set Positive =>
        BIBase.forall (fun E2 : Iris.Set Positive =>
          BIBase.forall (fun e : Λ.expr =>
            BIBase.forall (fun Φ : Λ.val → IPropWsat GF M F =>
              BIBase.forall (fun Ψ : Λ.val → IPropWsat GF M F =>
                BIBase.wand (BIBase.pure (stuckness_le s1 s2))
                  (BIBase.wand (BIBase.pure (Subset E1 E2))
                    (BIBase.wand (wp_s W s1 E1 e Φ)
                      (BIBase.wand (wp_post W E2 Φ Ψ)
                        (wp_s W s2 E2 e Ψ)))))))))))

private theorem wp_strong_mono_body_elim
    (s1 s2 : Stuckness) (E1 E2 : Iris.Set Positive)
    (e : Λ.expr) (Φ Ψ : Λ.val → IPropWsat GF M F) :
    wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W) ⊢
      BIBase.wand (BIBase.pure (stuckness_le s1 s2))
        (BIBase.wand (BIBase.pure (Subset E1 E2))
          (BIBase.wand (wp_s W s1 E1 e Φ)
            (BIBase.wand (wp_post W E2 Φ Ψ)
              (wp_s W s2 E2 e Ψ)))) := by
  -- eliminate the binders of `wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W)`
  refine (forall_elim (PROP := IProp GF) (Ψ := fun s1 => _) s1).trans ?_
  refine (forall_elim (PROP := IProp GF) (Ψ := fun s2 => _) s2).trans ?_
  refine (forall_elim (PROP := IProp GF) (Ψ := fun E1 => _) E1).trans ?_
  refine (forall_elim (PROP := IProp GF) (Ψ := fun E2 => _) E2).trans ?_
  refine (forall_elim (PROP := IProp GF) (Ψ := fun e => _) e).trans ?_
  refine (forall_elim (PROP := IProp GF) (Ψ := fun Φ => _) Φ).trans ?_
  exact (forall_elim (PROP := IProp GF) (Ψ := fun Ψ => _) Ψ)

private theorem wp_strong_mono_body_later_elim
    (s1 s2 : Stuckness) (E1 E2 : Iris.Set Positive)
    (e : Λ.expr) (Φ Ψ : Λ.val → IPropWsat GF M F) :
    BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W)) ⊢
      BIBase.later
        (BIBase.wand (BIBase.pure (stuckness_le s1 s2))
          (BIBase.wand (BIBase.pure (Subset E1 E2))
            (BIBase.wand (wp_s W s1 E1 e Φ)
              (BIBase.wand (wp_post W E2 Φ Ψ)
                (wp_s W s2 E2 e Ψ))))) := by
  -- lift the non-later elimination through `▷`
  exact later_mono (wp_strong_mono_body_elim (s1 := s1) (s2 := s2) (E1 := E1) (E2 := E2) (e := e) (Φ := Φ) (Ψ := Ψ))

omit [ElemG GF (COFE.constOF CoPsetDisj)] [ElemG GF (COFE.constOF GSetDisj)] in
private theorem later_wand_elim (P Q : IProp GF) :
    BIBase.sep (BIBase.later (BIBase.wand P Q)) (BIBase.later P) ⊢
      BIBase.later Q := by
  -- push `▷` through the wand, then eliminate it
  have hwand := later_wand (PROP := IProp GF) (P := P) (Q := Q)
  exact (sep_mono hwand .rfl).trans (wand_elim_l (PROP := IProp GF))

omit [ElemG GF (COFE.constOF CoPsetDisj)] [ElemG GF (COFE.constOF GSetDisj)] in
private theorem sep_later_intro (P Q : IProp GF) (h : (True : IProp GF) ⊢ P) :
    Q ⊢ BIBase.sep (BIBase.later P) Q := by
  -- add `True`, then replace it with a `▷` fact
  refine (true_sep_2 (PROP := IProp GF) (P := Q)).trans ?_
  refine (sep_mono ?_ .rfl)
  exact h.trans later_intro

omit [ElemG GF (COFE.constOF CoPsetDisj)] [ElemG GF (COFE.constOF GSetDisj)] in
private theorem sep_later_pure_intro (φ : Prop) (h : φ) (P : IProp GF) :
    P ⊢ BIBase.sep (BIBase.later (BIBase.pure φ)) P := by
  -- specialize `sep_later_intro` to a pure fact
  exact sep_later_intro (P := BIBase.pure φ) (Q := P) (h := pure_intro h)

omit [ElemG GF (COFE.constOF CoPsetDisj)] [ElemG GF (COFE.constOF GSetDisj)] in
private theorem wp_strong_mono_later_pure
    (φ : Prop) (hφ : φ) (Q R : IProp GF) :
    BIBase.sep (BIBase.later (BIBase.wand (BIBase.pure φ) Q)) R ⊢
      BIBase.sep (BIBase.later Q) R := by
  -- insert `▷⌜φ⌝` and eliminate the wand under `▷`
  have hframe := sep_later_pure_intro (φ := φ) hφ (P := R)
  refine (sep_mono .rfl hframe).trans ?_
  refine (sep_assoc (P := BIBase.later (BIBase.wand (BIBase.pure φ) Q))
    (Q := BIBase.later (BIBase.pure φ)) (R := R)).2.trans ?_
  exact sep_mono (later_wand_elim (P := BIBase.pure φ) (Q := Q)) .rfl

omit [ElemG GF (COFE.constOF CoPsetDisj)] [ElemG GF (COFE.constOF GSetDisj)] in
private theorem wp_strong_mono_later_pures
    (φ ψ : Prop) (hφ : φ) (hψ : ψ) (Q R : IProp GF) :
    BIBase.sep (BIBase.later (BIBase.wand (BIBase.pure φ) (BIBase.wand (BIBase.pure ψ) Q))) R ⊢
      BIBase.sep (BIBase.later Q) R := by
  -- eliminate the two pure premises one after another
  have h1 := wp_strong_mono_later_pure (φ := φ) hφ
    (Q := BIBase.wand (BIBase.pure ψ) Q) (R := R)
  have h2 := wp_strong_mono_later_pure (φ := ψ) hψ (Q := Q) (R := R)
  exact h1.trans h2

omit [ElemG GF (COFE.constOF CoPsetDisj)] [ElemG GF (COFE.constOF GSetDisj)] in
private theorem wp_strong_mono_later_twice (P Q R : IProp GF) :
    BIBase.sep (BIBase.later (BIBase.wand P (BIBase.wand Q R)))
        (BIBase.sep (BIBase.later P) (BIBase.later Q)) ⊢
      BIBase.later R := by
  -- reassociate and eliminate both wands under `▷`
  have hassoc :=
    (sep_assoc (P := BIBase.later (BIBase.wand P (BIBase.wand Q R)))
      (Q := BIBase.later P) (R := BIBase.later Q)).2
  refine hassoc.trans ?_
  refine (sep_mono (later_wand_elim (P := P) (Q := BIBase.wand Q R)) .rfl).trans ?_
  exact later_wand_elim (P := Q) (Q := R)

private theorem wp_strong_mono_later
    (s1 s2 : Stuckness) (E1 E2 : Iris.Set Positive)
    (e : Λ.expr) (Φ Ψ : Λ.val → IPropWsat GF M F)
    (hS : stuckness_le s1 s2) (hE : Subset E1 E2) :
    BIBase.sep
        (BIBase.intuitionistically
          (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W))))
        (BIBase.sep (BIBase.later (wp_s W s1 E1 e Φ))
          (BIBase.later (wp_post W E2 Φ Ψ))) ⊢
      BIBase.later (wp_s W s2 E2 e Ψ) := by
  -- unwrap the intuitionistic hypothesis and discharge the pure premises under `▷`
  have hIH :
      BIBase.sep
          (BIBase.intuitionistically
            (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W))))
          (BIBase.sep (BIBase.later (wp_s W s1 E1 e Φ))
            (BIBase.later (wp_post W E2 Φ Ψ))) ⊢
        BIBase.sep
          (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W)))
          (BIBase.sep (BIBase.later (wp_s W s1 E1 e Φ))
            (BIBase.later (wp_post W E2 Φ Ψ))) :=
    sep_mono (intuitionistically_elim (PROP := IProp GF)) .rfl
  let rest :=
    BIBase.wand (wp_s W s1 E1 e Φ)
      (BIBase.wand (wp_post W E2 Φ Ψ)
        (wp_s W s2 E2 e Ψ))
  have hwand :
      BIBase.sep
          (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W)))
          (BIBase.sep (BIBase.later (wp_s W s1 E1 e Φ))
            (BIBase.later (wp_post W E2 Φ Ψ))) ⊢
        BIBase.sep
          (BIBase.later
            (BIBase.wand (BIBase.pure (stuckness_le s1 s2))
              (BIBase.wand (BIBase.pure (Subset E1 E2)) rest)))
          (BIBase.sep (BIBase.later (wp_s W s1 E1 e Φ))
            (BIBase.later (wp_post W E2 Φ Ψ))) :=
    sep_mono (wp_strong_mono_body_later_elim (s1 := s1) (s2 := s2) (E1 := E1) (E2 := E2) (e := e) (Φ := Φ) (Ψ := Ψ)) .rfl
  have hpure :
      BIBase.sep
          (BIBase.later
            (BIBase.wand (BIBase.pure (stuckness_le s1 s2))
              (BIBase.wand (BIBase.pure (Subset E1 E2)) rest)))
          (BIBase.sep (BIBase.later (wp_s W s1 E1 e Φ))
            (BIBase.later (wp_post W E2 Φ Ψ))) ⊢
        BIBase.sep (BIBase.later rest)
          (BIBase.sep (BIBase.later (wp_s W s1 E1 e Φ))
            (BIBase.later (wp_post W E2 Φ Ψ))) :=
    wp_strong_mono_later_pures (φ := stuckness_le s1 s2) (ψ := Subset E1 E2) hS hE
      (Q := rest)
      (R := BIBase.sep (BIBase.later (wp_s W s1 E1 e Φ))
        (BIBase.later (wp_post W E2 Φ Ψ)))
  have hmain :
      BIBase.sep (BIBase.later rest)
          (BIBase.sep (BIBase.later (wp_s W s1 E1 e Φ))
            (BIBase.later (wp_post W E2 Φ Ψ))) ⊢
        BIBase.later (wp_s W s2 E2 e Ψ) :=
    wp_strong_mono_later_twice
      (P := wp_s W s1 E1 e Φ)
      (Q := wp_post W E2 Φ Ψ)
      (R := wp_s W s2 E2 e Ψ)
  exact hIH.trans (hwand.trans (hpure.trans hmain))

private theorem wp_strong_mono_fork_later
    (s1 s2 : Stuckness) (ef : Λ.expr)
    (hS : stuckness_le s1 s2) :
    (BIBase.sep
        (BIBase.intuitionistically
          (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W))))
        (BIBase.later (wp_s W s1 Iris.Set.univ ef fork_post)) :
        IPropWsat GF M F) ⊢
      (BIBase.later (wp_s W s2 Iris.Set.univ ef fork_post) :
        IPropWsat GF M F) := by
  -- insert the fork postcondition and reuse `wp_strong_mono_later`
  have hpost :
      (True : IProp GF) ⊢
        wp_post (Λ := Λ) W Iris.Set.univ
          (fork_post (Λ := Λ)) (fork_post (Λ := Λ)) :=
    wp_post_fork (M := M) (F := F) (Λ := Λ) (W := W)
  have hadd :
      BIBase.sep
          (BIBase.intuitionistically
            (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W))))
          (BIBase.later (wp_s W s1 Iris.Set.univ ef fork_post)) ⊢
        BIBase.sep
          (BIBase.intuitionistically
            (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W))))
          (BIBase.sep
            (BIBase.later (wp_s W s1 Iris.Set.univ ef fork_post))
            (BIBase.later (wp_post (Λ := Λ) W Iris.Set.univ (fork_post (Λ := Λ)) (fork_post (Λ := Λ))))) := by
    refine (sep_later_intro (P := wp_post (Λ := Λ) W Iris.Set.univ (fork_post (Λ := Λ)) (fork_post (Λ := Λ)))
      (Q := BIBase.sep
        (BIBase.intuitionistically
          (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W))))
        (BIBase.later (wp_s W s1 Iris.Set.univ ef fork_post)))
      hpost).trans ?_
    refine (sep_comm
      (P := BIBase.later (wp_post (Λ := Λ) W Iris.Set.univ (fork_post (Λ := Λ)) (fork_post (Λ := Λ))))
      (Q := BIBase.sep
        (BIBase.intuitionistically
          (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W))))
        (BIBase.later (wp_s W s1 Iris.Set.univ ef fork_post)))).1.trans ?_
    exact (sep_assoc
      (P := BIBase.intuitionistically
        (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W))))
      (Q := BIBase.later (wp_s W s1 Iris.Set.univ ef fork_post))
      (R := BIBase.later (wp_post (Λ := Λ) W Iris.Set.univ (fork_post (Λ := Λ)) (fork_post (Λ := Λ))))).1
  have hmain := wp_strong_mono_later (GF := GF) (Λ := Λ) (W := W)
    (s1 := s1) (s2 := s2) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
    (e := ef) (Φ := fork_post (M := M) (F := F)) (Ψ := fork_post (M := M) (F := F))
      hS (by intro _ hx; exact hx)
  exact hadd.trans hmain

private theorem wp_strong_mono_forks_later_aux
    (s1 s2 : Stuckness) (efs : List Λ.expr) (hS : stuckness_le s1 s2) :
    (BIBase.sep
        (BIBase.intuitionistically
          (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W))))
        (big_sepL (fun _ ef =>
          BIBase.later (wp_s W s1 Iris.Set.univ ef fork_post)) efs) :
        IPropWsat GF M F) ⊢
      (big_sepL (fun _ ef =>
        BIBase.later (wp_s W s2 Iris.Set.univ ef fork_post)) efs :
        IPropWsat GF M F) := by
  -- push the intuitionistic IH down the list, duplicating it for head/tail
  induction efs with
  | nil =>
      simpa [big_sepL_nil] using
        (sep_elim_r (P := BIBase.intuitionistically
          (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W))))
          (Q := (BIBase.emp : IProp GF)))
  | cons ef efs ih =>
      simp [big_sepL_cons]
      have hdup :
          BIBase.intuitionistically
              (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W))) ⊢
            BIBase.sep
              (BIBase.intuitionistically
                (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W))))
              (BIBase.intuitionistically
                (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W)))) :=
        (intuitionistically_sep_idem
          (P := BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W)))).2
      have hcomm :
          BIBase.sep
              (BIBase.sep
                (BIBase.intuitionistically
                  (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W))))
                (BIBase.intuitionistically
                  (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W)))))
              (BIBase.sep
                (BIBase.later
                  (wp_s W s1 Iris.Set.univ ef fork_post))
                (big_sepL (fun _ ef =>
                  BIBase.later (wp_s W s1 Iris.Set.univ ef fork_post)) efs)) ⊢
            BIBase.sep
              (BIBase.sep
                (BIBase.intuitionistically
                  (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W))))
                (BIBase.later
                  (wp_s W s1 Iris.Set.univ ef fork_post)))
              (BIBase.sep
                (BIBase.intuitionistically
                  (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W))))
                (big_sepL (fun _ ef =>
                  BIBase.later (wp_s W s1 Iris.Set.univ ef fork_post)) efs)) :=
        (sep_sep_sep_comm (PROP := IProp GF)
          (P := BIBase.intuitionistically
            (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W))))
          (Q := BIBase.intuitionistically
            (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W))))
          (R := BIBase.later
            (wp_s W s1 Iris.Set.univ ef fork_post))
          (S := big_sepL (fun _ ef =>
            BIBase.later (wp_s W s1 Iris.Set.univ ef fork_post)) efs)).1
      refine (sep_mono hdup .rfl).trans (hcomm.trans ?_)
      refine sep_mono ?_ ih
      exact wp_strong_mono_fork_later (s1 := s1) (s2 := s2) (ef := ef) hS

private theorem wp_strong_mono_forks_later
    (s1 s2 : Stuckness) (efs : List Λ.expr) (hS : stuckness_le s1 s2) :
    (BIBase.sep
        (BIBase.intuitionistically
          (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W))))
        (BIBase.later (big_sepL (fun _ ef =>
          wp_s W s1 Iris.Set.univ ef fork_post) efs)) :
        IPropWsat GF M F) ⊢
      (BIBase.later (big_sepL (fun _ ef =>
        wp_s W s2 Iris.Set.univ ef fork_post) efs) :
        IPropWsat GF M F) := by
  -- distribute `▷` over the forked WPs, use the list lemma, then rewrap
  refine (sep_mono .rfl (later_big_sepL
    (Φ := fun _ ef =>
      wp_s W s1 Iris.Set.univ ef fork_post)
    (l := efs)).1).trans ?_
  refine (wp_strong_mono_forks_later_aux (s1 := s1) (s2 := s2) (efs := efs) hS).trans ?_
  exact (later_big_sepL
    (Φ := fun _ ef =>
      wp_s W s2 Iris.Set.univ ef fork_post)
    (l := efs)).2

private abbrev wp_pre_view (W : WsatGS GF)
    (s : Stuckness) (E : Iris.Set Positive) (e : Λ.expr) (Φ : Λ.val → IPropWsat GF M F)
    (σ : Λ.state) (ns : Nat) (κ κs : List Λ.observation) (nt : Nat) :
    IPropWsat GF M F :=
  BIBase.wand (state_interp σ ns (κ ++ κs) nt)
    (fupd' W E maskEmpty
      (BIBase.sep (BIBase.pure (stuckness_pred s e σ))
        (BIBase.forall fun e2 : Λ.expr =>
          BIBase.forall fun σ2 : Λ.state =>
            BIBase.forall fun efs : List Λ.expr =>
              BIBase.wand (BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs))
                (fupd' W maskEmpty E
                  (BIBase.later
                    (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                      (BIBase.sep (wp_s W s E e2 Φ)
                        (big_sepL (fun _ ef =>
                          wp_s W s Iris.Set.univ ef fork_post)
                          efs))))))))

private theorem wp_pre_elim
    (s : Stuckness) (E : Iris.Set Positive) (e : Λ.expr) (Φ : Λ.val → IPropWsat GF M F)
    (σ : Λ.state) (ns : Nat) (κ κs : List Λ.observation) (nt : Nat)
    (hto : Λ.to_val e = none) :
    wp_pre_s W s
        (wp_s W s) E e Φ ⊢
      wp_pre_view W s E e Φ σ ns κ κs nt := by
  -- specialize the binders in `wp_pre W` to expose the state interpretation
  have hσ :=
    forall_elim (PROP := IProp GF)
      (Ψ := fun σ =>
        BIBase.forall fun ns =>
          BIBase.forall fun κ =>
            BIBase.forall fun κs =>
              BIBase.forall fun nt =>
                wp_pre_view W s E e Φ σ ns κ κs nt) σ
  have hns :=
    forall_elim (PROP := IProp GF)
      (Ψ := fun ns =>
        BIBase.forall fun κ =>
          BIBase.forall fun κs =>
            BIBase.forall fun nt =>
              wp_pre_view W s E e Φ σ ns κ κs nt) ns
  have hκ :=
    forall_elim (PROP := IProp GF)
      (Ψ := fun κ =>
        BIBase.forall fun κs =>
          BIBase.forall fun nt =>
            wp_pre_view W s E e Φ σ ns κ κs nt) κ
  have hκs :=
    forall_elim (PROP := IProp GF)
      (Ψ := fun κs =>
        BIBase.forall fun nt =>
          wp_pre_view W s E e Φ σ ns κ κs nt) κs
  have hnt :=
    forall_elim (PROP := IProp GF)
      (Ψ := fun nt =>
        wp_pre_view W s E e Φ σ ns κ κs nt) nt
  simpa [wp_pre, hto, wp_pre_step, wp_pre_view] using
    hσ.trans (hns.trans (hκ.trans (hκs.trans hnt)))

private theorem wp_strong_mono_step
    (s1 s2 : Stuckness) (E1 E2 : Iris.Set Positive)
    (e : Λ.expr) (Φ Ψ : Λ.val → IPropWsat GF M F)
    (hS : stuckness_le s1 s2) (hE : Subset E1 E2)
    (hto : Λ.to_val e = none) :
    BIBase.sep
        (BIBase.intuitionistically
          (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W))))
        (BIBase.sep
          (wp_pre_s W s1
            (wp_s W s1) E1 e Φ)
          (wp_post W E2 Φ Ψ)) ⊢
      wp_pre_s W s2
        (wp_s W s2) E2 e Ψ := by
  -- unfold the non-value branch and transform the continuation
  simp [wp_pre, hto, wp_pre_step]
  refine forall_intro (PROP := IProp GF) ?_; intro σ
  refine forall_intro (PROP := IProp GF) ?_; intro ns
  refine forall_intro (PROP := IProp GF) ?_; intro κ
  refine forall_intro (PROP := IProp GF) ?_; intro κs
  refine forall_intro (PROP := IProp GF) ?_; intro nt
  refine wand_intro ?_
  let IH : IPropWsat GF M F :=
    BIBase.intuitionistically
      (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W)))
  let Q1 : IPropWsat GF M F :=
    BIBase.forall fun e2 : Λ.expr =>
      BIBase.forall fun σ2 : Λ.state =>
        BIBase.forall fun efs : List Λ.expr =>
          BIBase.wand (BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs))
            (fupd' W maskEmpty E1
              (BIBase.later
                (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                  (BIBase.sep (wp_s W s1 E1 e2 Φ)
                    (big_sepL (fun _ ef =>
                      wp_s W s1 Iris.Set.univ ef fork_post)
                      efs)))))
  let Q2 : IPropWsat GF M F :=
    BIBase.forall fun e2 : Λ.expr =>
      BIBase.forall fun σ2 : Λ.state =>
        BIBase.forall fun efs : List Λ.expr =>
          BIBase.wand (BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs))
            (fupd' W maskEmpty E2
              (BIBase.later
                (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                  (BIBase.sep (wp_s W s2 E2 e2 Ψ)
                    (big_sepL (fun _ ef =>
                      wp_s W s2 Iris.Set.univ ef fork_post)
                      efs)))))
  let P0 : IPropWsat GF M F :=
    BIBase.sep (BIBase.pure (stuckness_pred s1 e σ)) Q1
  let P1 : IPropWsat GF M F :=
    BIBase.sep P0
      (BIBase.sep
        (wp_post W E2 Φ Ψ) IH)
  -- open the left WP using the state interpretation
  have hpre :
      BIBase.sep
          (wp_pre_s W s1
            (wp_s W s1) E1 e Φ)
          (state_interp σ ns (κ ++ κs) nt) ⊢
        fupd' W E1 maskEmpty P0 := by
    have hview :=
      wp_pre_elim (W := W) (s := s1) (E := E1) (e := e) (Φ := Φ)
        (σ := σ) (ns := ns) (κ := κ) (κs := κs) (nt := nt) hto
    exact (sep_mono hview .rfl).trans (wand_elim_l (PROP := IProp GF))
  -- widen the mask and add the closing update
  have hmask :=
    fupd_mask_subseteq_apply (W := W) (E1 := E1) (E2 := E2) hE
      (P := P1)
  -- transform the post-step continuation and close the mask
  have hpost_pure :
      BIBase.sep P1
          (fupd' W E1 E2 (BIBase.emp : IProp GF)) ⊢
        BIBase.sep (BIBase.pure (stuckness_pred s2 e σ)) Q2 := by
    -- rearrange to expose the pure premise and continuation
    have hassoc :
        BIBase.sep P1
            (fupd' W E1 E2 (BIBase.emp : IProp GF)) ⊢
          BIBase.sep (BIBase.pure (stuckness_pred s1 e σ))
            (BIBase.sep Q1
              (BIBase.sep
                (BIBase.sep
                  (wp_post W E2 Φ Ψ) IH)
                (fupd' W E1 E2 (BIBase.emp : IProp GF)))) := by
      -- expand `P1` and reassociate to expose the pure premise
      dsimp [P1, P0]
      refine (sep_assoc (PROP := IProp GF)
        (P := BIBase.sep (BIBase.pure (stuckness_pred s1 e σ)) Q1)
        (Q := BIBase.sep
          (wp_post W E2 Φ Ψ) IH)
        (R := fupd' W E1 E2
          (BIBase.emp : IProp GF))).1.trans ?_
      exact (sep_assoc (PROP := IProp GF)
        (P := BIBase.pure (stuckness_pred s1 e σ))
        (Q := Q1)
        (R := BIBase.sep
          (BIBase.sep
            (wp_post W E2 Φ Ψ) IH)
          (fupd' W E1 E2
            (BIBase.emp : IProp GF)))).1
    refine hassoc.trans ?_
    refine (sep_mono (PROP := IProp GF)
      (P := BIBase.pure (stuckness_pred s1 e σ))
      (Q := BIBase.pure (stuckness_pred s2 e σ))
      (P' := BIBase.sep Q1
        (BIBase.sep
          (BIBase.sep
            (wp_post W E2 Φ Ψ) IH)
          (fupd' W E1 E2 (BIBase.emp : IProp GF))))
      (Q' := Q2)
      (pure_mono (PROP := IProp GF)
        (stuckness_pred_mono (s1 := s1) (s2 := s2) hS e σ)) ?_)
    -- now show `Q1 ∗ wp_post W ∗ IH ⊢ Q2`
    refine forall_intro (PROP := IProp GF) ?_; intro e2
    refine forall_intro (PROP := IProp GF) ?_; intro σ2
    refine forall_intro (PROP := IProp GF) ?_; intro efs
    refine wand_intro ?_
    -- apply the step continuation and frame IH/wp_post
    have hstep :
        BIBase.sep Q1 (BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs)) ⊢
          fupd' W maskEmpty E1
            (BIBase.later
              (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                (BIBase.sep (wp_s W s1 E1 e2 Φ)
                  (big_sepL (fun _ ef =>
                    wp_s W s1 Iris.Set.univ ef fork_post)
                    efs)))) := by
      have h1 :=
        forall_elim (PROP := IProp GF)
          (Ψ := fun e2 : Λ.expr =>
            BIBase.forall fun σ2 : Λ.state =>
              BIBase.forall fun efs : List Λ.expr =>
                BIBase.wand (BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs))
                  (fupd' W maskEmpty E1
                    (BIBase.later
                      (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                        (BIBase.sep (wp_s W s1 E1 e2 Φ)
                          (big_sepL (fun _ ef =>
                            wp_s W s1 Iris.Set.univ ef fork_post)
                            efs)))))) e2
      have h2 :=
        forall_elim (PROP := IProp GF)
          (Ψ := fun σ2 : Λ.state =>
            BIBase.forall fun efs : List Λ.expr =>
              BIBase.wand (BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs))
                (fupd' W maskEmpty E1
                  (BIBase.later
                    (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                      (BIBase.sep (wp_s W s1 E1 e2 Φ)
                        (big_sepL (fun _ ef =>
                          wp_s W s1 Iris.Set.univ ef fork_post)
                          efs)))))) σ2
      have h3 :=
        forall_elim (PROP := IProp GF)
          (Ψ := fun efs : List Λ.expr =>
            BIBase.wand (BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs))
              (fupd' W maskEmpty E1
                (BIBase.later
                  (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                    (BIBase.sep (wp_s W s1 E1 e2 Φ)
                      (big_sepL (fun _ ef =>
                        wp_s W s1 Iris.Set.univ ef fork_post)
                        efs)))))) efs
      have h123 := h1.trans (h2.trans h3)
      exact (sep_mono h123 .rfl).trans (wand_elim_l (PROP := IProp GF))
    have hswap :
        BIBase.sep
            (BIBase.sep Q1
              (BIBase.sep
                (wp_post W E2 Φ Ψ) IH))
            (BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs)) ⊢
          BIBase.sep
            (BIBase.sep Q1 (BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs)))
            (BIBase.sep
              (wp_post W E2 Φ Ψ) IH) := by
      exact (sep_right_comm (PROP := IProp GF)
        (P := Q1)
        (Q := BIBase.sep
          (wp_post W E2 Φ Ψ) IH)
        (R := BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs))).1
    have hframe0 :
        BIBase.sep
            (fupd' W maskEmpty E1
              (BIBase.later
                (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                  (BIBase.sep (wp_s W s1 E1 e2 Φ)
                    (big_sepL (fun _ ef =>
                      wp_s W s1 Iris.Set.univ ef fork_post)
                      efs)))))
            (BIBase.sep
              (wp_post W E2 Φ Ψ) IH) ⊢
          fupd' W maskEmpty E1
            (BIBase.sep
              (BIBase.later
                (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                  (BIBase.sep (wp_s W s1 E1 e2 Φ)
                    (big_sepL (fun _ ef =>
                      wp_s W s1 Iris.Set.univ ef fork_post)
                      efs))))
              (BIBase.sep
                (wp_post W E2 Φ Ψ) IH)) :=
      Iris.BaseLogic.fupd_frame_r 
        (E1 := maskEmpty) (E2 := E1)
        (P := BIBase.later
          (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
            (BIBase.sep (wp_s W s1 E1 e2 Φ)
              (big_sepL (fun _ ef =>
                wp_s W s1 Iris.Set.univ ef fork_post)
                efs))))
        (Q := BIBase.sep
          (wp_post W E2 Φ Ψ) IH)
    -- frame the closing update through the step
    have hframe :
        BIBase.sep
            (fupd' W maskEmpty E1
              (BIBase.sep
                (BIBase.later
                  (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                    (BIBase.sep (wp_s W s1 E1 e2 Φ)
                      (big_sepL (fun _ ef =>
                        wp_s W s1 Iris.Set.univ ef fork_post)
                        efs))))
                (BIBase.sep
                  (wp_post W E2 Φ Ψ) IH)))
            (fupd' W E1 E2 (BIBase.emp : IProp GF)) ⊢
          fupd' W maskEmpty E1
            (BIBase.sep
              (BIBase.sep
                (BIBase.later
                  (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                    (BIBase.sep (wp_s W s1 E1 e2 Φ)
                      (big_sepL (fun _ ef =>
                        wp_s W s1 Iris.Set.univ ef fork_post)
                        efs))))
                (BIBase.sep
                  (wp_post W E2 Φ Ψ) IH))
              (fupd' W E1 E2 (BIBase.emp : IProp GF))) :=
      Iris.BaseLogic.fupd_frame_r 
        (E1 := maskEmpty) (E2 := E1)
        (P := BIBase.sep
          (BIBase.later
            (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
              (BIBase.sep (wp_s W s1 E1 e2 Φ)
                (big_sepL (fun _ ef =>
                  wp_s W s1 Iris.Set.univ ef fork_post)
                  efs))))
          (BIBase.sep
            (wp_post W E2 Φ Ψ) IH))
        (Q := fupd' W E1 E2 (BIBase.emp : IProp GF))
    have hmono :
        BIBase.sep
            (BIBase.later
              (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                (BIBase.sep (wp_s W s1 E1 e2 Φ)
                  (big_sepL (fun _ ef =>
                    wp_s W s1 Iris.Set.univ ef fork_post)
                    efs))))
            (BIBase.sep
              (wp_post W E2 Φ Ψ) IH) ⊢
          BIBase.later
            (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
              (BIBase.sep (wp_s W s2 E2 e2 Ψ)
                (big_sepL (fun _ ef =>
                  wp_s W s2 Iris.Set.univ ef fork_post)
                  efs))) := by
      -- use the intuitionistic Löb hypothesis for the main and forked WPs
      have hmain :
          BIBase.sep
              (BIBase.intuitionistically
                (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W))))
              (BIBase.sep
                (BIBase.later (wp_s W s1 E1 e2 Φ))
                (BIBase.later (wp_post W E2 Φ Ψ))) ⊢
            BIBase.later (wp_s W s2 E2 e2 Ψ) :=
        wp_strong_mono_later (s1 := s1) (s2 := s2) (E1 := E1) (E2 := E2)
          (e := e2) (Φ := Φ) (Ψ := Ψ) hS hE
      have hfork :
          BIBase.sep
              (BIBase.intuitionistically
                (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W))))
              (BIBase.later (big_sepL (fun _ ef =>
                wp_s W s1 Iris.Set.univ ef fork_post) efs)) ⊢
            BIBase.later (big_sepL (fun _ ef =>
              wp_s W s2 Iris.Set.univ ef fork_post) efs) :=
        wp_strong_mono_forks_later (s1 := s1) (s2 := s2) (efs := efs) hS
      have hcont :
          BIBase.sep
              (BIBase.sep
                (wp_post W E2 Φ Ψ) IH)
              (BIBase.later
                (BIBase.sep (wp_s W s1 E1 e2 Φ)
                  (big_sepL (fun _ ef =>
                    wp_s W s1 Iris.Set.univ ef fork_post)
                    efs))) ⊢
            BIBase.later
              (BIBase.sep (wp_s W s2 E2 e2 Ψ)
                (big_sepL (fun _ ef =>
                  wp_s W s2 Iris.Set.univ ef fork_post)
                  efs)) := by
        -- turn `wp_post` into `▷ wp_post` and split the later continuation
        have hpostlater :
            BIBase.sep
                (wp_post W E2 Φ Ψ) IH ⊢
              BIBase.sep
                (BIBase.later
                  (wp_post W E2 Φ Ψ)) IH :=
          sep_mono (later_intro (PROP := IProp GF)
            (P := wp_post W E2 Φ Ψ)) .rfl
        refine (sep_mono hpostlater (later_sep (PROP := IProp GF)
          (P := wp_s W s1 E1 e2 Φ)
          (Q := big_sepL (fun _ ef =>
            wp_s W s1 Iris.Set.univ ef fork_post) efs)).1).trans ?_
        -- now: (▷ wp_post W ∗ IH) ∗ (▷ wp_s1 ∗ ▷ big_sepL)
        have hdup :
            IH ⊢ BIBase.sep IH IH :=
          (intuitionistically_sep_idem
            (P := BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W)))).2
        refine (sep_assoc (PROP := IProp GF)
          (P := BIBase.later
            (wp_post W E2 Φ Ψ))
          (Q := IH)
          (R := BIBase.sep
            (BIBase.later (wp_s W s1 E1 e2 Φ))
            (BIBase.later (big_sepL (fun _ ef =>
              wp_s W s1 Iris.Set.univ ef fork_post)
              efs)))).1.trans ?_
        refine (sep_mono .rfl (sep_mono hdup .rfl)).trans ?_
        refine (sep_mono .rfl (sep_sep_sep_comm (PROP := IProp GF)
          (P := IH)
          (Q := IH)
          (R := BIBase.later (wp_s W s1 E1 e2 Φ))
          (S := BIBase.later (big_sepL (fun _ ef =>
            wp_s W s1 Iris.Set.univ ef fork_post)
            efs))).1).trans ?_
        -- regroup for `hmain` and `hfork`
        refine (sep_assoc (PROP := IProp GF)
          (P := BIBase.later
            (wp_post W E2 Φ Ψ))
          (Q := BIBase.sep IH
            (BIBase.later (wp_s W s1 E1 e2 Φ)))
          (R := BIBase.sep IH
            (BIBase.later (big_sepL (fun _ ef =>
              wp_s W s1 Iris.Set.univ ef fork_post)
              efs)))).2.trans ?_
        have hleft :
            BIBase.sep
                (BIBase.later
                  (wp_post W E2 Φ Ψ))
                (BIBase.sep IH
                  (BIBase.later (wp_s W s1 E1 e2 Φ))) ⊢
              BIBase.sep IH
                (BIBase.sep
                  (BIBase.later (wp_s W s1 E1 e2 Φ))
                  (BIBase.later
                    (wp_post W E2 Φ Ψ))) := by
          refine (sep_left_comm (PROP := IProp GF)
            (P := BIBase.later
              (wp_post W E2 Φ Ψ))
            (Q := IH)
            (R := BIBase.later (wp_s W s1 E1 e2 Φ))).1.trans ?_
          refine (sep_assoc (PROP := IProp GF)
            (P := IH)
            (Q := BIBase.later
              (wp_post W E2 Φ Ψ))
            (R := BIBase.later (wp_s W s1 E1 e2 Φ))).2.trans ?_
          refine (sep_right_comm (PROP := IProp GF)
            (P := IH)
            (Q := BIBase.later
              (wp_post W E2 Φ Ψ))
            (R := BIBase.later (wp_s W s1 E1 e2 Φ))).1.trans ?_
          exact (sep_assoc (PROP := IProp GF)
            (P := IH)
            (Q := BIBase.later (wp_s W s1 E1 e2 Φ))
            (R := BIBase.later
              (wp_post W E2 Φ Ψ))).1
        refine (sep_mono hleft .rfl).trans ?_
        refine (sep_mono hmain hfork).trans ?_
        exact (later_sep (PROP := IProp GF)
          (P := wp_s W s2 E2 e2 Ψ)
          (Q := big_sepL (fun _ ef =>
            wp_s W s2 Iris.Set.univ ef fork_post)
            efs)).2
      -- split state and continuation, apply `hcont`, then reassemble
      refine (sep_mono (later_sep (PROP := IProp GF)
        (P := state_interp σ2 (ns + 1) κs (efs.length + nt))
        (Q := BIBase.sep (wp_s W s1 E1 e2 Φ)
          (big_sepL (fun _ ef =>
            wp_s W s1 Iris.Set.univ ef fork_post) efs))).1 .rfl).trans ?_
      refine (sep_right_comm (PROP := IProp GF)
        (P := BIBase.later (state_interp σ2 (ns + 1) κs (efs.length + nt)))
        (Q := BIBase.later
          (BIBase.sep (wp_s W s1 E1 e2 Φ)
            (big_sepL (fun _ ef =>
              wp_s W s1 Iris.Set.univ ef fork_post) efs)))
        (R := BIBase.sep
          (wp_post W E2 Φ Ψ) IH)).1.trans ?_
      refine (sep_assoc (PROP := IProp GF)
        (P := BIBase.later (state_interp σ2 (ns + 1) κs (efs.length + nt)))
        (Q := BIBase.sep
          (wp_post W E2 Φ Ψ) IH)
        (R := BIBase.later
          (BIBase.sep (wp_s W s1 E1 e2 Φ)
            (big_sepL (fun _ ef =>
              wp_s W s1 Iris.Set.univ ef fork_post) efs)))).1.trans ?_
      refine (sep_mono .rfl hcont).trans ?_
      exact (later_sep (PROP := IProp GF)
        (P := state_interp σ2 (ns + 1) κs (efs.length + nt))
        (Q := BIBase.sep (wp_s W s2 E2 e2 Ψ)
          (big_sepL (fun _ ef =>
            wp_s W s2 Iris.Set.univ ef fork_post) efs))).2
    -- apply the step continuation, frame `wp_post`/IH and the closing update
    have hprep :
        BIBase.sep
            (BIBase.sep Q1
              (BIBase.sep
                (BIBase.sep
                  (wp_post W E2 Φ Ψ) IH)
                (fupd' W E1 E2 (BIBase.emp : IProp GF))))
            (BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs)) ⊢
          BIBase.sep
            (BIBase.sep
              (BIBase.sep Q1 (BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs)))
              (BIBase.sep
                (wp_post W E2 Φ Ψ) IH))
            (fupd' W E1 E2 (BIBase.emp : IProp GF)) := by
      have hassoc :
          BIBase.sep
              (BIBase.sep Q1
                (BIBase.sep
                  (BIBase.sep
                    (wp_post W E2 Φ Ψ) IH)
                  (fupd' W E1 E2 (BIBase.emp : IProp GF))))
              (BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs)) ⊢
            BIBase.sep
              (BIBase.sep
                (BIBase.sep Q1
                  (BIBase.sep
                    (wp_post W E2 Φ Ψ) IH))
                (fupd' W E1 E2 (BIBase.emp : IProp GF)))
              (BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs)) :=
        sep_mono (sep_assoc (PROP := IProp GF)
          (P := Q1)
          (Q := BIBase.sep
            (wp_post W E2 Φ Ψ) IH)
          (R := fupd' W E1 E2 (BIBase.emp : IProp GF))).2 .rfl
      have hswap_f :
          BIBase.sep
              (BIBase.sep
                (BIBase.sep Q1
                  (BIBase.sep
                    (wp_post W E2 Φ Ψ) IH))
                (fupd' W E1 E2 (BIBase.emp : IProp GF)))
              (BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs)) ⊢
            BIBase.sep
              (BIBase.sep
                (BIBase.sep Q1
                  (BIBase.sep
                    (wp_post W E2 Φ Ψ) IH))
                (BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs)))
              (fupd' W E1 E2 (BIBase.emp : IProp GF)) :=
        (sep_right_comm (PROP := IProp GF)
          (P := BIBase.sep Q1
            (BIBase.sep
              (wp_post W E2 Φ Ψ) IH))
          (Q := fupd' W E1 E2 (BIBase.emp : IProp GF))
          (R := BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs))).1
      have hswap2 :
          BIBase.sep
              (BIBase.sep
                (BIBase.sep Q1
                  (BIBase.sep
                    (wp_post W E2 Φ Ψ) IH))
                (BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs)))
              (fupd' W E1 E2 (BIBase.emp : IProp GF)) ⊢
            BIBase.sep
              (BIBase.sep
                (BIBase.sep Q1 (BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs)))
                (BIBase.sep
                  (wp_post W E2 Φ Ψ) IH))
              (fupd' W E1 E2 (BIBase.emp : IProp GF)) :=
        sep_mono hswap .rfl
      exact hassoc.trans (hswap_f.trans hswap2)
    refine hprep.trans ?_
    refine (sep_mono (sep_mono hstep .rfl) .rfl).trans ?_
    refine (sep_mono hframe0 .rfl).trans ?_
    -- close the mask after updating the continuation
    have hmid :
        fupd' W maskEmpty E1
            (BIBase.sep
              (BIBase.sep
                (BIBase.later
                  (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                    (BIBase.sep (wp_s W s1 E1 e2 Φ)
                      (big_sepL (fun _ ef =>
                        wp_s W s1 Iris.Set.univ ef fork_post)
                        efs))))
                (BIBase.sep
                  (wp_post W E2 Φ Ψ) IH))
              (fupd' W E1 E2 (BIBase.emp : IProp GF))) ⊢
          fupd' W maskEmpty E1
            (BIBase.sep
              (BIBase.later
                (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                  (BIBase.sep (wp_s W s2 E2 e2 Ψ)
                    (big_sepL (fun _ ef =>
                      wp_s W s2 Iris.Set.univ ef fork_post)
                      efs))))
              (fupd' W E1 E2 (BIBase.emp : IProp GF))) :=
      Iris.BaseLogic.fupd_mono 
        (E1 := maskEmpty) (E2 := E1)
        (P := BIBase.sep
          (BIBase.sep
            (BIBase.later
              (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                (BIBase.sep (wp_s W s1 E1 e2 Φ)
                  (big_sepL (fun _ ef =>
                    wp_s W s1 Iris.Set.univ ef fork_post)
                    efs))))
            (BIBase.sep
              (wp_post W E2 Φ Ψ) IH))
          (fupd' W E1 E2 (BIBase.emp : IProp GF)))
        (Q := BIBase.sep
          (BIBase.later
            (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
              (BIBase.sep (wp_s W s2 E2 e2 Ψ)
                (big_sepL (fun _ ef =>
                  wp_s W s2 Iris.Set.univ ef fork_post)
                  efs))))
          (fupd' W E1 E2 (BIBase.emp : IProp GF)))
        (sep_mono hmono .rfl)
    have hclose :
        fupd' W maskEmpty E1
            (BIBase.sep
              (BIBase.later
                (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                  (BIBase.sep (wp_s W s2 E2 e2 Ψ)
                    (big_sepL (fun _ ef =>
                      wp_s W s2 Iris.Set.univ ef fork_post)
                      efs))))
              (fupd' W E1 E2 (BIBase.emp : IProp GF))) ⊢
          fupd' W maskEmpty E2
            (BIBase.later
              (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                (BIBase.sep (wp_s W s2 E2 e2 Ψ)
                  (big_sepL (fun _ ef =>
                    wp_s W s2 Iris.Set.univ ef fork_post)
                    efs)))) :=
      fupd_close_mask (E1 := E1) (E2 := E2)
        (P := BIBase.later
          (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
            (BIBase.sep (wp_s W s2 E2 e2 Ψ)
              (big_sepL (fun _ ef =>
                wp_s W s2 Iris.Set.univ ef fork_post)
                efs))))
    exact hframe.trans (hmid.trans hclose)
  have hpost :
      fupd' W E2 maskEmpty
          (BIBase.sep P1
            (fupd' W E1 E2 (BIBase.emp : IProp GF))) ⊢
        fupd' W E2 maskEmpty
          (BIBase.sep (BIBase.pure (stuckness_pred s2 e σ)) Q2) :=
    Iris.BaseLogic.fupd_mono 
      (E1 := E2) (E2 := maskEmpty)
      (P := BIBase.sep P1
        (fupd' W E1 E2 (BIBase.emp : IProp GF)))
      (Q := BIBase.sep (BIBase.pure (stuckness_pred s2 e σ)) Q2) hpost_pure
  have hperm :
      BIBase.sep
          (BIBase.sep IH
            (BIBase.sep (wp_pre_s W s1
              (wp_s W s1) E1 e Φ)
              (wp_post W E2 Φ Ψ)))
          (state_interp σ ns (κ ++ κs) nt) ⊢
        BIBase.sep
          (BIBase.sep
            (wp_pre_s W s1
              (wp_s W s1) E1 e Φ)
            (state_interp σ ns (κ ++ κs) nt))
          (BIBase.sep
            (wp_post W E2 Φ Ψ) IH) := by
    have h1 :
        BIBase.sep
            (BIBase.sep IH
              (BIBase.sep (wp_pre_s W s1
                (wp_s W s1) E1 e Φ)
                (wp_post W E2 Φ Ψ)))
            (state_interp σ ns (κ ++ κs) nt) ⊢
          BIBase.sep
            (BIBase.sep
              (BIBase.sep IH
                (wp_pre_s W s1
                  (wp_s W s1) E1 e Φ))
              (wp_post W E2 Φ Ψ))
            (state_interp σ ns (κ ++ κs) nt) :=
      sep_mono (sep_assoc (PROP := IProp GF)
        (P := IH)
        (Q := wp_pre_s W s1
          (wp_s W s1) E1 e Φ)
        (R := wp_post W E2 Φ Ψ)).2 .rfl
    have h2 :
        BIBase.sep
            (BIBase.sep
              (BIBase.sep IH
                (wp_pre_s W s1
                  (wp_s W s1) E1 e Φ))
              (wp_post W E2 Φ Ψ))
            (state_interp σ ns (κ ++ κs) nt) ⊢
          BIBase.sep
            (BIBase.sep IH
              (wp_post W E2 Φ Ψ))
            (BIBase.sep
              (wp_pre_s W s1
                (wp_s W s1) E1 e Φ)
              (state_interp σ ns (κ ++ κs) nt)) := by
      have h2a :
          BIBase.sep
              (BIBase.sep
                (BIBase.sep IH
                  (wp_pre_s W s1
                    (wp_s W s1) E1 e Φ))
                (wp_post W E2 Φ Ψ))
              (state_interp σ ns (κ ++ κs) nt) ⊢
            BIBase.sep
              (BIBase.sep IH
                (wp_pre_s W s1
                  (wp_s W s1) E1 e Φ))
              (BIBase.sep
                (wp_post W E2 Φ Ψ)
                (state_interp σ ns (κ ++ κs) nt)) :=
        (sep_assoc (PROP := IProp GF)
          (P := BIBase.sep IH
            (wp_pre_s W s1
              (wp_s W s1) E1 e Φ))
          (Q := wp_post W E2 Φ Ψ)
          (R := state_interp σ ns (κ ++ κs) nt)).1
      have h2b :
          BIBase.sep
              (BIBase.sep IH
                (wp_pre_s W s1
                  (wp_s W s1) E1 e Φ))
              (BIBase.sep
                (wp_post W E2 Φ Ψ)
                (state_interp σ ns (κ ++ κs) nt)) ⊢
            BIBase.sep
              (BIBase.sep IH
                (wp_post W E2 Φ Ψ))
              (BIBase.sep
                (wp_pre_s W s1
                  (wp_s W s1) E1 e Φ)
                (state_interp σ ns (κ ++ κs) nt)) :=
        (sep_sep_sep_comm (PROP := IProp GF)
          (P := IH)
          (Q := wp_pre_s W s1
            (wp_s W s1) E1 e Φ)
          (R := wp_post W E2 Φ Ψ)
          (S := state_interp σ ns (κ ++ κs) nt)).1
      exact h2a.trans h2b
    have h3 :
        BIBase.sep
            (BIBase.sep IH
              (wp_post W E2 Φ Ψ))
            (BIBase.sep
              (wp_pre_s W s1
                (wp_s W s1) E1 e Φ)
              (state_interp σ ns (κ ++ κs) nt)) ⊢
          BIBase.sep
            (BIBase.sep
              (wp_pre_s W s1
                (wp_s W s1) E1 e Φ)
              (state_interp σ ns (κ ++ κs) nt))
            (BIBase.sep
              (wp_post W E2 Φ Ψ) IH) := by
      refine (sep_comm (PROP := IProp GF)
        (P := BIBase.sep IH
          (wp_post W E2 Φ Ψ))
        (Q := BIBase.sep
          (wp_pre_s W s1
            (wp_s W s1) E1 e Φ)
          (state_interp σ ns (κ ++ κs) nt))).1.trans ?_
      refine sep_mono .rfl ?_
      exact (sep_comm (PROP := IProp GF)
        (P := IH)
        (Q := wp_post W E2 Φ Ψ)).1
    exact h1.trans (h2.trans h3)
  have hframe_pre :
      BIBase.sep
          (fupd' W E1 maskEmpty P0)
          (BIBase.sep
            (wp_post W E2 Φ Ψ) IH) ⊢
        fupd' W E1 maskEmpty P1 := by
    simpa [P1] using
      (Iris.BaseLogic.fupd_frame_r 
        (E1 := E1) (E2 := maskEmpty)
        (P := P0)
        (Q := BIBase.sep
          (wp_post W E2 Φ Ψ) IH))
  have hpre' :
      BIBase.sep
          (BIBase.sep
            (wp_pre_s W s1
              (wp_s W s1) E1 e Φ)
            (state_interp σ ns (κ ++ κs) nt))
          (BIBase.sep
            (wp_post W E2 Φ Ψ) IH) ⊢
        fupd' W E1 maskEmpty P1 :=
    (sep_mono hpre .rfl).trans hframe_pre
  -- rewrite the `wp_pre W` unfoldings in the framed chain
  have hperm' := by
    -- use the non-value unfolding to align with the goal
    simpa [wp_pre, hto, wp_pre_step] using hperm
  have hpre'' := by
    -- again, unfold the non-value case to match the goal shape
    simpa [wp_pre, hto, wp_pre_step] using hpre'
  exact hperm'.trans (hpre''.trans (hmask.trans hpost))

/-! ## Strong Monotonicity (Löb) -/

omit [ElemG GF (COFE.constOF CoPsetDisj)] [ElemG GF (COFE.constOF GSetDisj)] in
private theorem pure_sep_elim_left (φ : Prop) (P : IProp GF) :
    BIBase.sep (BIBase.pure φ) P ⊢ BIBase.pure φ := by
  -- pure is absorbing, so it can be extracted from a separating conjunction
  exact sep_elim_l (P := BIBase.pure φ) (Q := P)

omit [ElemG GF (COFE.constOF CoPsetDisj)] [ElemG GF (COFE.constOF GSetDisj)] in
private theorem pure_sep_elim_second (φ ψ : Prop) (P : IProp GF) :
    BIBase.sep (BIBase.pure φ) (BIBase.sep (BIBase.pure ψ) P) ⊢ BIBase.pure ψ := by
  -- commute to put the second pure on the left, then eliminate it
  have hswap :
      BIBase.sep (BIBase.pure φ) (BIBase.sep (BIBase.pure ψ) P) ⊢
        BIBase.sep (BIBase.pure ψ) (BIBase.sep (BIBase.pure φ) P) := by
    refine (sep_comm (PROP := IProp GF)
      (P := BIBase.pure φ) (Q := BIBase.sep (BIBase.pure ψ) P)).1.trans ?_
    refine (sep_assoc (PROP := IProp GF)
      (P := BIBase.pure ψ) (Q := P) (R := BIBase.pure φ)).1.trans ?_
    refine sep_mono .rfl ?_
    exact (sep_comm (PROP := IProp GF) (P := P) (Q := BIBase.pure φ)).1
  exact hswap.trans (pure_sep_elim_left (φ := ψ) (P := BIBase.sep (BIBase.pure φ) P))

private theorem wp_strong_mono_body_step :
    (BIBase.intuitionistically
        (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W))) :
        IPropWsat GF M F) ⊢
      (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W) : IPropWsat GF M F) := by
  -- prove the body pointwise and use the non-value step lemma
  refine forall_intro (PROP := IProp GF) ?_; intro s1
  refine forall_intro (PROP := IProp GF) ?_; intro s2
  refine forall_intro (PROP := IProp GF) ?_; intro E1
  refine forall_intro (PROP := IProp GF) ?_; intro E2
  refine forall_intro (PROP := IProp GF) ?_; intro e
  refine forall_intro (PROP := IProp GF) ?_; intro Φ
  refine forall_intro (PROP := IProp GF) ?_; intro Ψ
  refine wand_intro ?_
  refine wand_intro ?_
  refine wand_intro ?_
  refine wand_intro ?_
  have hwpΦ :
      wp_s W s1 E1 e Φ ⊢
        wp_pre_s W s1
          (wp_s W s1) E1 e Φ :=
    (wp_unfold (s := s1) (E := E1) (e := e) (Φ := Φ)).1
  have hwpΨ :
      wp_pre_s W s2
          (wp_s W s2) E2 e Ψ ⊢
        wp_s W s2 E2 e Ψ :=
    (wp_unfold (s := s2) (E := E2) (e := e) (Φ := Ψ)).2
  -- frame `wp_pre W` conversion under the pure assumptions
  have hpre :
      BIBase.sep (BIBase.pure (stuckness_le s1 s2))
          (BIBase.sep (BIBase.pure (Subset E1 E2))
            (BIBase.sep (wp_s W s1 E1 e Φ)
              (wp_post W E2 Φ Ψ))) ⊢
        BIBase.sep (BIBase.pure (stuckness_le s1 s2))
          (BIBase.sep (BIBase.pure (Subset E1 E2))
            (BIBase.sep (wp_pre_s W s1
                (wp_s W s1) E1 e Φ)
              (wp_post W E2 Φ Ψ))) :=
    (sep_mono .rfl <| sep_mono .rfl <| sep_mono hwpΦ .rfl)
  let IH : IPropWsat GF M F :=
    BIBase.intuitionistically
      (BIBase.later (wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W)))
  -- reassociate the left context, then apply the `wp_pre W` unfolding
  have hassoc0 :
      BIBase.sep
          (BIBase.sep
            (BIBase.sep
              (BIBase.sep IH (BIBase.pure (stuckness_le s1 s2)))
              (BIBase.pure (Subset E1 E2)))
            (wp_s W s1 E1 e Φ))
          (wp_post W E2 Φ Ψ) ⊢
        BIBase.sep IH
          (BIBase.sep (BIBase.pure (stuckness_le s1 s2))
            (BIBase.sep (BIBase.pure (Subset E1 E2))
              (BIBase.sep (wp_s W s1 E1 e Φ)
                (wp_post W E2 Φ Ψ)))) := by
    -- reassociate to group `wp_s W`/`wp_post`, then expose `IH`
    refine (sep_assoc (PROP := IProp GF)
      (P := BIBase.sep
        (BIBase.sep IH (BIBase.pure (stuckness_le s1 s2)))
        (BIBase.pure (Subset E1 E2)))
      (Q := wp_s W s1 E1 e Φ)
      (R := wp_post W E2 Φ Ψ)).1.trans ?_
    refine (sep_assoc (PROP := IProp GF)
      (P := BIBase.sep IH (BIBase.pure (stuckness_le s1 s2)))
      (Q := BIBase.pure (Subset E1 E2))
      (R := BIBase.sep (wp_s W s1 E1 e Φ)
        (wp_post W E2 Φ Ψ))).1.trans ?_
    exact (sep_assoc (PROP := IProp GF)
      (P := IH)
      (Q := BIBase.pure (stuckness_le s1 s2))
      (R := BIBase.sep (BIBase.pure (Subset E1 E2))
        (BIBase.sep (wp_s W s1 E1 e Φ)
          (wp_post W E2 Φ Ψ)))).1
  refine hassoc0.trans ?_
  refine (sep_mono .rfl hpre).trans ?_
  -- consume the pure assumptions and apply the step lemma
  refine (pure_elim (φ := stuckness_le s1 s2)
    (h1 := (sep_elim_r (PROP := IProp GF)
      (P := IH)
      (Q := BIBase.sep (BIBase.pure (stuckness_le s1 s2))
        (BIBase.sep (BIBase.pure (Subset E1 E2))
          (BIBase.sep (wp_pre_s W s1
              (wp_s W s1) E1 e Φ)
            (wp_post W E2 Φ Ψ))))).trans
      (pure_sep_elim_left (φ := stuckness_le s1 s2)
        (P := BIBase.sep (BIBase.pure (Subset E1 E2))
          (BIBase.sep (wp_pre_s W s1
              (wp_s W s1) E1 e Φ)
            (wp_post W E2 Φ Ψ)))))
    (h2 := ?_)).trans hwpΨ
  intro hS
  refine (pure_elim (φ := Subset E1 E2)
    (h1 := (sep_elim_r (PROP := IProp GF)
      (P := IH)
      (Q := BIBase.sep (BIBase.pure (stuckness_le s1 s2))
        (BIBase.sep (BIBase.pure (Subset E1 E2))
          (BIBase.sep (wp_pre_s W s1
              (wp_s W s1) E1 e Φ)
            (wp_post W E2 Φ Ψ))))).trans
      (pure_sep_elim_second (φ := stuckness_le s1 s2) (ψ := Subset E1 E2)
        (P := BIBase.sep (wp_pre_s W s1
            (wp_s W s1) E1 e Φ)
          (wp_post W E2 Φ Ψ))))
    (h2 := ?_))
  intro hE
  have hstep :
      BIBase.sep IH
        (BIBase.sep (wp_pre_s W s1
            (wp_s W s1) E1 e Φ)
          (wp_post W E2 Φ Ψ)) ⊢
      wp_pre_s W s2
        (wp_s W s2) E2 e Ψ := by
    cases hto : Λ.to_val e with
    | some v =>
        have hpre' :
            wp_pre_s W s1
                (wp_s W s1) E1 e Φ ⊢
              fupd' W E1 E1 (Φ v) := by
          simp [wp_pre, hto]
        have hval :=
          (sep_mono hpre' .rfl).trans
            (wp_strong_mono_value (E1 := E1) (E2 := E2) (Φ := Φ) (Ψ := Ψ) (v := v) hE)
        have hpost' :
            fupd' W E2 E2 (Ψ v) ⊢
              wp_pre_s W s2
                (wp_s W s2) E2 e Ψ := by
          simp [wp_pre, hto]
        have hmain := hval.trans hpost'
        exact (sep_elim_r (PROP := IProp GF)
          (P := IH)
          (Q := BIBase.sep (wp_pre_s W s1
              (wp_s W s1) E1 e Φ)
            (wp_post W E2 Φ Ψ))).trans hmain
    | none =>
        exact wp_strong_mono_step (s1 := s1) (s2 := s2) (E1 := E1) (E2 := E2)
          (e := e) (Φ := Φ) (Ψ := Ψ) hS hE hto
  -- thread the framed conversion and apply the step result
  have hdrop_pures :
      BIBase.sep (BIBase.pure (stuckness_le s1 s2))
          (BIBase.sep (BIBase.pure (Subset E1 E2))
            (BIBase.sep (wp_pre_s W s1
                (wp_s W s1) E1 e Φ)
              (wp_post W E2 Φ Ψ))) ⊢
        BIBase.sep (wp_pre_s W s1
            (wp_s W s1) E1 e Φ)
          (wp_post W E2 Φ Ψ) := by
    refine (sep_elim_r (PROP := IProp GF)
      (P := BIBase.pure (stuckness_le s1 s2))
      (Q := BIBase.sep (BIBase.pure (Subset E1 E2))
        (BIBase.sep (wp_pre_s W s1
            (wp_s W s1) E1 e Φ)
          (wp_post W E2 Φ Ψ)))).trans ?_
    exact sep_elim_r (PROP := IProp GF)
      (P := BIBase.pure (Subset E1 E2))
      (Q := BIBase.sep (wp_pre_s W s1
          (wp_s W s1) E1 e Φ)
        (wp_post W E2 Φ Ψ))
  have hdrop :
      BIBase.sep IH
          (BIBase.sep (BIBase.pure (stuckness_le s1 s2))
            (BIBase.sep (BIBase.pure (Subset E1 E2))
              (BIBase.sep (wp_pre_s W s1
                  (wp_s W s1) E1 e Φ)
                (wp_post W E2 Φ Ψ)))) ⊢
        BIBase.sep IH
          (BIBase.sep (wp_pre_s W s1
              (wp_s W s1) E1 e Φ)
            (wp_post W E2 Φ Ψ)) :=
    sep_mono .rfl hdrop_pures
  exact hdrop.trans hstep

private theorem wp_strong_mono_body_loeb :
    (True : IPropWsat GF M F) ⊢
      wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W) := by
  -- apply Loeb to the monotonicity body
  let P : IPropWsat GF M F := wp_strong_mono_body (M := M) (F := F) (Λ := Λ) (W := W)
  have hstep : BIBase.intuitionistically (BIBase.later P) ⊢ P :=
    wp_strong_mono_body_step
  have hstep_box :
      BIBase.intuitionistically (BIBase.later P) ⊢
        BIBase.intuitionistically P :=
    intuitionistically_intro' (P := BIBase.later P) (Q := P) hstep
  have hlater :
      BIBase.later (BIBase.intuitionistically P) ⊢
        BIBase.intuitionistically (BIBase.later P) :=
    (later_intuitionistically (PROP := IProp GF) (P := P)).2
  have hloop :
      BIBase.later (BIBase.intuitionistically P) ⊢
        BIBase.intuitionistically P :=
    hlater.trans hstep_box
  have hloeb :
      (True : IProp GF) ⊢ BIBase.intuitionistically P :=
    BILoeb.loeb_weak (PROP := IProp GF) (P := BIBase.intuitionistically P) hloop
  exact hloeb.trans (intuitionistically_elim (PROP := IProp GF) (P := P))

/-- Strong monotonicity: transform postcondition (same stuckness and mask).
Coq: `wp_strong_mono` in `weakestpre.v`. -/
theorem wp_strong_mono (s1 s2 : Stuckness) (E1 E2 : Iris.Set Positive)
    (e : Λ.expr) (Φ Ψ : Λ.val → IPropWsat GF M F) :
    stuckness_le s1 s2 →
    Subset E1 E2 →
    wp_s W s1 E1 e Φ ⊢
      BIBase.wand
        (wp_post W E2 Φ Ψ)
        (wp_s W s2 E2 e Ψ) := by
  intro hS hE
  let Hw : IProp GF :=
    BIBase.wand (BIBase.pure (stuckness_le s1 s2))
      (BIBase.wand (BIBase.pure (Subset E1 E2))
        (BIBase.wand (wp_s W s1 E1 e Φ)
          (BIBase.wand (wp_post W E2 Φ Ψ)
            (wp_s W s2 E2 e Ψ))))
  let P0 : IProp GF :=
    BIBase.sep (BIBase.pure (stuckness_le s1 s2))
      (BIBase.sep (BIBase.pure (Subset E1 E2))
        (BIBase.sep (wp_s W s1 E1 e Φ)
          (wp_post W E2 Φ Ψ)))
  have hW :
      (True : IProp GF) ⊢ Hw :=
    (wp_strong_mono_body_loeb ).trans
      (wp_strong_mono_body_elim (s1 := s1) (s2 := s2) (E1 := E1) (E2 := E2)
        (e := e) (Φ := Φ) (Ψ := Ψ))
  have hS' : (True : IProp GF) ⊢ BIBase.pure (stuckness_le s1 s2) := pure_intro hS
  have hE' : (True : IProp GF) ⊢ BIBase.pure (Subset E1 E2) := pure_intro hE
  have hframeS :
      BIBase.sep (wp_s W s1 E1 e Φ)
          (wp_post W E2 Φ Ψ) ⊢
        BIBase.sep (BIBase.pure (stuckness_le s1 s2))
          (BIBase.sep (wp_s W s1 E1 e Φ)
            (wp_post W E2 Φ Ψ)) := by
    refine (true_sep_2 (PROP := IProp GF)
      (P := BIBase.sep (wp_s W s1 E1 e Φ)
        (wp_post W E2 Φ Ψ))).trans ?_
    exact sep_mono hS' .rfl
  have hframe :
      BIBase.sep (wp_s W s1 E1 e Φ)
          (wp_post W E2 Φ Ψ) ⊢ P0 := by
    refine hframeS.trans ?_
    refine (true_sep_2 (PROP := IProp GF)
      (P := BIBase.sep (BIBase.pure (stuckness_le s1 s2))
        (BIBase.sep (wp_s W s1 E1 e Φ)
          (wp_post W E2 Φ Ψ)))).trans ?_
    refine (sep_mono hE' .rfl).trans ?_
    exact (sep_left_comm (PROP := IProp GF)
      (P := BIBase.pure (Subset E1 E2))
      (Q := BIBase.pure (stuckness_le s1 s2))
      (R := BIBase.sep (wp_s W s1 E1 e Φ)
        (wp_post W E2 Φ Ψ))).1
  have happly :
      BIBase.sep Hw P0 ⊢
        wp_s W s2 E2 e Ψ := by
    refine (sep_assoc (PROP := IProp GF)
      (P := Hw) (Q := BIBase.pure (stuckness_le s1 s2))
      (R := BIBase.sep (BIBase.pure (Subset E1 E2))
        (BIBase.sep (wp_s W s1 E1 e Φ)
          (wp_post W E2 Φ Ψ)))).2.trans ?_
    refine (sep_mono (wand_elim_l (PROP := IProp GF)) .rfl).trans ?_
    refine (sep_assoc (PROP := IProp GF)
      (P := BIBase.wand (BIBase.pure (Subset E1 E2))
        (BIBase.wand (wp_s W s1 E1 e Φ)
          (BIBase.wand (wp_post W E2 Φ Ψ)
            (wp_s W s2 E2 e Ψ))))
      (Q := BIBase.pure (Subset E1 E2))
      (R := BIBase.sep (wp_s W s1 E1 e Φ)
        (wp_post W E2 Φ Ψ))).2.trans ?_
    refine (sep_mono (wand_elim_l (PROP := IProp GF)) .rfl).trans ?_
    refine (sep_assoc (PROP := IProp GF)
      (P := BIBase.wand (wp_s W s1 E1 e Φ)
        (BIBase.wand (wp_post W E2 Φ Ψ)
          (wp_s W s2 E2 e Ψ)))
      (Q := wp_s W s1 E1 e Φ)
      (R := wp_post W E2 Φ Ψ)).2.trans ?_
    refine (sep_mono (wand_elim_l (PROP := IProp GF)) .rfl).trans ?_
    exact wand_elim_l (PROP := IProp GF)
  refine wand_intro ?_
  refine hframe.trans ?_
  refine (true_sep_2 (PROP := IProp GF) (P := P0)).trans ?_
  exact (sep_mono hW .rfl).trans happly

/-- Fancy update can be absorbed into WP.
Coq: `fupd_wp` in `weakestpre.v`. -/
theorem fupd_wp (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IPropWsat GF M F) :
    fupd' W E E
      (wp_s W s E e Φ) ⊢
    wp_s W s E e Φ :=
  by
  have hwp_pre :
      wp_s W s E e Φ ⊢
        wp_pre_s W s
          (wp_s W s) E e Φ :=
    (wp_unfold (s := s) (E := E) (e := e) (Φ := Φ)).1
  have hwp :
      wp_pre_s W s
          (wp_s W s) E e Φ ⊢
        wp_s W s E e Φ :=
    (wp_unfold (s := s) (E := E) (e := e) (Φ := Φ)).2
  refine (Iris.BaseLogic.fupd_mono 
    (E1 := E) (E2 := E)
    (P := wp_s W s E e Φ)
    (Q := wp_pre_s W s
      (wp_s W s) E e Φ) hwp_pre).trans ?_
  have hcollapse :
      fupd' W E E
          (wp_pre_s W s
            (wp_s W s) E e Φ) ⊢
        wp_pre_s W s
          (wp_s W s) E e Φ := by
    cases hto : Λ.to_val e with
    | some v =>
        simpa [wp_pre, hto] using
          (fupd_idem (E := E) (P := Φ v))
    | none =>
        -- push the outer update through binders and collapse the nested update
        simp [wp_pre, hto, wp_pre_step]
        let Qcont (σ : Λ.state) (ns : Nat) (κ : List Λ.observation)
            (κs : List Λ.observation) (nt : Nat) : IPropWsat GF M F :=
          BIBase.forall fun e2 : Λ.expr =>
            BIBase.forall fun σ2 : Λ.state =>
              BIBase.forall fun efs : List Λ.expr =>
                BIBase.wand (BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs)) <|
                  fupd' W maskEmpty E <|
                    BIBase.later <|
                      BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt)) <|
                        BIBase.sep (wp_s W s E e2 Φ)
                          (big_sepL (fun _ ef =>
                            wp_s W s Iris.Set.univ ef fork_post)
                            efs)
        let Pσ (σ : Λ.state) : IPropWsat GF M F :=
          BIBase.forall fun ns : Nat =>
            BIBase.forall fun κ : List Λ.observation =>
              BIBase.forall fun κs : List Λ.observation =>
                BIBase.forall fun nt : Nat =>
                  BIBase.wand (state_interp (M := M) (F := F) σ ns (κ ++ κs) nt) <|
                    fupd' W E maskEmpty <|
                      BIBase.sep (BIBase.pure (stuckness_pred s e σ))
                        (Qcont σ ns κ κs nt)
        have hσ :
            fupd' W E E (BIBase.forall Pσ) ⊢
              BIBase.forall fun a => fupd' W E E (Pσ a) := by
          simpa using
            (fupd_forall (A := Λ.state) (E1 := E) (E2 := E) (Φ := Pσ))
        refine hσ.trans ?_
        refine forall_intro (PROP := IProp GF) ?_; intro σ
        have hσ' :=
          forall_elim (PROP := IProp GF)
            (Ψ := fun σ => fupd' W E E (Pσ σ)) σ
        refine hσ'.trans ?_
        let Pns (ns : Nat) : IPropWsat GF M F :=
          BIBase.forall fun κ : List Λ.observation =>
            BIBase.forall fun κs : List Λ.observation =>
              BIBase.forall fun nt : Nat =>
                BIBase.wand (state_interp (M := M) (F := F) σ ns (κ ++ κs) nt) <|
                  fupd' W E maskEmpty <|
                    BIBase.sep (BIBase.pure (stuckness_pred s e σ))
                      (Qcont σ ns κ κs nt)
        have hns :
            fupd' W E E (BIBase.forall Pns) ⊢
              BIBase.forall fun a => fupd' W E E (Pns a) := by
          simpa using
            (fupd_forall (A := Nat) (E1 := E) (E2 := E) (Φ := Pns))
        refine hns.trans ?_
        refine forall_intro (PROP := IProp GF) ?_; intro ns
        have hns' :=
          forall_elim (PROP := IProp GF)
            (Ψ := fun ns => fupd' W E E (Pns ns)) ns
        refine hns'.trans ?_
        let Pκ (κ : List Λ.observation) : IPropWsat GF M F :=
          BIBase.forall fun κs : List Λ.observation =>
            BIBase.forall fun nt : Nat =>
              BIBase.wand (state_interp (M := M) (F := F) σ ns (κ ++ κs) nt) <|
                fupd' W E maskEmpty <|
                  BIBase.sep (BIBase.pure (stuckness_pred s e σ))
                    (Qcont σ ns κ κs nt)
        have hκ :
            fupd' W E E (BIBase.forall Pκ) ⊢
              BIBase.forall fun a => fupd' W E E (Pκ a) := by
          simpa using
            (fupd_forall (A := List Λ.observation) (E1 := E) (E2 := E) (Φ := Pκ))
        refine hκ.trans ?_
        refine forall_intro (PROP := IProp GF) ?_; intro κ
        have hκ' :=
          forall_elim (PROP := IProp GF)
            (Ψ := fun κ => fupd' W E E (Pκ κ)) κ
        refine hκ'.trans ?_
        let Pκs (κs : List Λ.observation) : IPropWsat GF M F :=
          BIBase.forall fun nt : Nat =>
            BIBase.wand (state_interp (M := M) (F := F) σ ns (κ ++ κs) nt) <|
              fupd' W E maskEmpty <|
                BIBase.sep (BIBase.pure (stuckness_pred s e σ))
                  (Qcont σ ns κ κs nt)
        have hκs :
            fupd' W E E (BIBase.forall Pκs) ⊢
              BIBase.forall fun a => fupd' W E E (Pκs a) := by
          simpa using
            (fupd_forall (A := List Λ.observation) (E1 := E) (E2 := E) (Φ := Pκs))
        refine hκs.trans ?_
        refine forall_intro (PROP := IProp GF) ?_; intro κs
        have hκs' :=
          forall_elim (PROP := IProp GF)
            (Ψ := fun κs => fupd' W E E (Pκs κs)) κs
        refine hκs'.trans ?_
        let Pnt (nt : Nat) : IPropWsat GF M F :=
          BIBase.wand (state_interp (M := M) (F := F) σ ns (κ ++ κs) nt) <|
            fupd' W E maskEmpty <|
              BIBase.sep (BIBase.pure (stuckness_pred s e σ))
                (Qcont σ ns κ κs nt)
        have hnt :
            fupd' W E E (BIBase.forall Pnt) ⊢
              BIBase.forall fun a => fupd' W E E (Pnt a) := by
          simpa using
            (fupd_forall (A := Nat) (E1 := E) (E2 := E) (Φ := Pnt))
        refine hnt.trans ?_
        refine forall_intro (PROP := IProp GF) ?_; intro nt
        have hnt' :=
          forall_elim (PROP := IProp GF)
            (Ψ := fun nt => fupd' W E E (Pnt nt)) nt
        refine hnt'.trans ?_
        -- collapse the outer `fupd` under the wand
        let Pstep : IProp GF :=
          BIBase.sep (BIBase.pure (stuckness_pred s e σ))
            (Qcont σ ns κ κs nt)
        refine (fupd_wand (E1 := E) (E2 := E)
          (P := state_interp σ ns (κ ++ κs) nt)
          (Q := fupd' W E maskEmpty Pstep)).trans ?_
        refine (wand_mono_r (PROP := IProp GF) ?_)
        exact Iris.BaseLogic.fupd_trans 
          (E1 := E) (E2 := E) (E3 := maskEmpty) (P := Pstep)
  exact hcollapse.trans hwp

/-- Postcondition update can be absorbed.
Coq: `wp_fupd` in `weakestpre.v`. -/
theorem wp_fupd (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IPropWsat GF M F) :
    wp_s W s E e
      (fun v => fupd' W E E (Φ v)) ⊢
    wp_s W s E e Φ :=
  by
  -- apply strong monotonicity with the identity postcondition transformer
  have hS : stuckness_le s s := by
    cases s <;> simp [stuckness_le]
  have hE : Subset E E := by
    intro i hi; exact hi
  have hmono :=
    wp_strong_mono (W := W) (s1 := s) (s2 := s) (E1 := E) (E2 := E) (e := e)
      (Φ := fun v => fupd' W E E (Φ v))
      (Ψ := Φ) hS hE
  have hpost :
      (True : IProp GF) ⊢
        wp_post W E
          (fun v => fupd' W E E (Φ v)) Φ := by
    -- the postcondition transformer is just `P -∗ P`
    refine forall_intro ?_; intro v
    exact wand_rfl
  have hframe :
      wp_s W s E e
          (fun v => fupd' W E E (Φ v)) ⊢
        BIBase.sep
          (wp_post W E
            (fun v => fupd' W E E (Φ v)) Φ)
          (wp_s W s E e
            (fun v => fupd' W E E (Φ v))) := by
    -- insert the transformer via `True`
    refine (true_sep_2 (PROP := IProp GF)
      (P := wp_s W s E e
        (fun v => fupd' W E E (Φ v)))).trans ?_
    exact sep_mono hpost .rfl
  refine hframe.trans ?_
  refine (sep_mono (PROP := IProp GF)
    (P := wp_post W E
      (fun v => fupd' W E E (Φ v)) Φ)
    (Q := wp_post W E
      (fun v => fupd' W E E (Φ v)) Φ)
    (P' := wp_s W s E e
      (fun v => fupd' W E E (Φ v)))
    (Q' := BIBase.wand
      (wp_post W E
        (fun v => fupd' W E E (Φ v)) Φ)
      (wp_s W s E e Φ)) .rfl hmono).trans ?_
  exact wand_elim_r (PROP := IProp GF)

/-- Bind rule: compositionality via evaluation contexts.
Coq: `wp_bind` in `weakestpre.v`. -/
theorem wp_bind (K : Λ.expr → Λ.expr) [LanguageCtx K]
    (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IPropWsat GF M F) :
    wp_s W s E e
      (fun v => wp_s W s E (K (Λ.of_val v)) Φ) ⊢
    wp_s W s E (K e) Φ :=
  by
  let post : Λ.val → IPropWsat GF M F :=
    fun v => wp_s W s E (K (Λ.of_val v)) Φ
  let P : IPropWsat GF M F :=
    BIBase.forall fun E =>
      BIBase.forall fun e =>
        BIBase.forall fun Φ =>
          BIBase.wand
            (wp_s W s E e
              (fun v => wp_s W s E (K (Λ.of_val v)) Φ))
            (wp_s W s E (K e) Φ)
  have hPelim (E : Iris.Set Positive) (e : Λ.expr) (Φ : Λ.val → IPropWsat GF M F) :
      P ⊢ BIBase.wand
        (wp_s W s E e
          (fun v => wp_s W s E (K (Λ.of_val v)) Φ))
        (wp_s W s E (K e) Φ) := by
    refine (forall_elim (PROP := IProp GF) (Ψ := fun E => _) E).trans ?_
    refine (forall_elim (PROP := IProp GF) (Ψ := fun e => _) e).trans ?_
    exact (forall_elim (PROP := IProp GF) (Ψ := fun Φ => _) Φ)
  have hstep : BIBase.intuitionistically (BIBase.later P) ⊢ P := by
    refine forall_intro (PROP := IProp GF) ?_; intro E
    refine forall_intro (PROP := IProp GF) ?_; intro e
    refine forall_intro (PROP := IProp GF) ?_; intro Φ
    cases hto : Λ.to_val e with
    | some v =>
        have hval :
            wp_s W s E e
                (fun v => wp_s W s E (K (Λ.of_val v)) Φ) ⊢
              wp_s W s E (K e) Φ := by
          have hstep :
              fupd' W E E
                  (wp_s W s E (K (Λ.of_val v)) Φ) ⊢
                wp_s W s E (K (Λ.of_val v)) Φ :=
            fupd_wp (s := s) (E := E)
              (e := K (Λ.of_val v)) (Φ := Φ)
          have hK : K e = K (Λ.of_val v) := by
            simp [of_to_val e v hto]
          have hwpK' :
              wp_s W s E (K (Λ.of_val v)) Φ ⊢
                wp_s W s E (K e) Φ := by
            simp [hK]
          have hpre :
              wp_pre_s W s
                  (wp_s W s) E e
                  (fun v =>
                    wp_s W s E (K (Λ.of_val v)) Φ) ⊢
                fupd' W E E
                  (wp_s W s E (K (Λ.of_val v)) Φ) := by
            simp [wp_pre, hto]
          have hwp :
              wp_s W s E e
                  (fun v => wp_s W s E (K (Λ.of_val v)) Φ) ⊢
                wp_pre_s W s
                  (wp_s W s) E e
                  (fun v =>
                    wp_s W s E (K (Λ.of_val v)) Φ) :=
            (wp_unfold (s := s) (E := E) (e := e)
              (Φ := fun v =>
                wp_s W s E (K (Λ.of_val v)) Φ)).1
          exact hwp.trans (hpre.trans (hstep.trans hwpK'))
        have htrue :
            (True : IProp GF) ⊢ BIBase.wand
              (wp_s W s E e
                (fun v => wp_s W s E (K (Λ.of_val v)) Φ))
              (wp_s W s E (K e) Φ) := by
          refine wand_intro (PROP := IProp GF) ?_
          -- drop `True`, then use the value case
          exact (sep_elim_r (PROP := IProp GF) (P := (BIBase.pure True))
            (Q := wp_s W s E e
              (fun v => wp_s W s E (K (Λ.of_val v)) Φ))).trans
            hval
        exact (true_intro (P := BIBase.intuitionistically (BIBase.later P))).trans htrue
    | none =>
        let IH : IPropWsat GF M F :=
          BIBase.intuitionistically (BIBase.later P)
        refine wand_intro (PROP := IProp GF) ?_
        have hwp :
            wp_s W s E e
                (fun v => wp_s W s E (K (Λ.of_val v)) Φ) ⊢
              wp_pre_s W s
                (wp_s W s) E e
                (fun v =>
                  wp_s W s E (K (Λ.of_val v)) Φ) :=
          (wp_unfold (s := s) (E := E) (e := e)
            (Φ := fun v =>
              wp_s W s E (K (Λ.of_val v)) Φ)).1
        have hwpK :
            wp_pre_s W s
                (wp_s W s) E (K e) Φ ⊢
              wp_s W s E (K e) Φ :=
          (wp_unfold (s := s) (E := E) (e := K e) (Φ := Φ)).2
        refine (sep_mono (PROP := IProp GF) .rfl hwp).trans ?_
        have htoK : Λ.to_val (K e) = none :=
          LanguageCtx.fill_not_val (K := K) e hto
        have hpre :
            BIBase.sep IH
                (wp_pre_s W s
                  (wp_s W s) E e
                  (fun v =>
                    wp_s W s E (K (Λ.of_val v)) Φ)) ⊢
              wp_pre_s W s
                (wp_s W s) E (K e) Φ := by
          -- unfold only the right-hand `wp_pre W`
          simp [wp_pre, htoK, wp_pre_step]
          -- specialize the right-hand binders
          refine forall_intro (PROP := IProp GF) ?_; intro σ
          refine forall_intro (PROP := IProp GF) ?_; intro ns
          refine forall_intro (PROP := IProp GF) ?_; intro κ
          refine forall_intro (PROP := IProp GF) ?_; intro κs
          refine forall_intro (PROP := IProp GF) ?_; intro nt
          -- open the left wp_pre W
          have hview :=
            wp_pre_elim (W := W) (s := s) (E := E) (e := e)
              (Φ := fun v =>
                wp_s W s E (K (Λ.of_val v)) Φ)
              (σ := σ) (ns := ns) (κ := κ) (κs := κs) (nt := nt) hto
          have hleft :
              BIBase.sep IH
                  (wp_pre_s W s
                    (wp_s W s) E e
                    (fun v =>
                      wp_s W s E (K (Λ.of_val v)) Φ)) ⊢
                BIBase.sep IH
                  (wp_pre_view W s E e
                    (fun v =>
                      wp_s W s E (K (Λ.of_val v)) Φ)
                    σ ns κ κs nt) :=
            sep_mono (PROP := IProp GF) .rfl hview
          refine hleft.trans ?_
          -- now show the view for `K e`
          let Q1 : IPropWsat GF M F :=
            BIBase.forall fun e2 : Λ.expr =>
              BIBase.forall fun σ2 : Λ.state =>
                BIBase.forall fun efs : List Λ.expr =>
                  BIBase.wand (BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs))
                    (fupd' W maskEmpty E
                      (BIBase.later
                        (BIBase.sep (state_interp (M := M) (F := F) σ2 (ns + 1) κs (efs.length + nt))
                          (BIBase.sep
                            (wp_s W s E e2
                              (fun v =>
                                wp_s W s E
                                  (K (Λ.of_val v)) Φ))
                            (big_sepL (fun _ ef =>
                              wp_s W s
                                Iris.Set.univ ef fork_post) efs)))))
          let Q2 : IPropWsat GF M F :=
            BIBase.forall fun e2 : Λ.expr =>
              BIBase.forall fun σ2 : Λ.state =>
                BIBase.forall fun efs : List Λ.expr =>
                  BIBase.wand (BIBase.pure (Λ.prim_step (K e) σ κ e2 σ2 efs))
                    (fupd' W maskEmpty E
                      (BIBase.later
                        (BIBase.sep (state_interp (M := M) (F := F) σ2 (ns + 1) κs (efs.length + nt))
                          (BIBase.sep
                            (wp_s W s E e2 Φ)
                            (big_sepL (fun _ ef =>
                              wp_s W s
                                Iris.Set.univ ef fork_post) efs)))))
          let P0 : IPropWsat GF M F :=
            BIBase.sep (BIBase.pure (stuckness_pred s e σ)) Q1
          let P1 : IPropWsat GF M F :=
            BIBase.sep (BIBase.pure (stuckness_pred s (K e) σ)) Q2
          -- unfold the view and prove the step relation
          dsimp [wp_pre_view, Q1, Q2, P0, P1]
          refine wand_intro (PROP := IProp GF) ?_
          -- reorder to apply the left wand
          have hassoc :
              BIBase.sep (state_interp (M := M) (F := F) σ ns (κ ++ κs) nt)
                  (BIBase.sep IH
                    (BIBase.wand (state_interp (M := M) (F := F) σ ns (κ ++ κs) nt)
                      (fupd' W E maskEmpty P0))) ⊢
                BIBase.sep IH
                  (BIBase.sep (state_interp (M := M) (F := F) σ ns (κ ++ κs) nt)
                    (BIBase.wand (state_interp (M := M) (F := F) σ ns (κ ++ κs) nt)
                      (fupd' W E maskEmpty P0))) := by
            simpa [sep_assoc] using
              (sep_left_comm (PROP := IProp GF)
                (P := state_interp (M := M) (F := F) σ ns (κ ++ κs) nt) (Q := IH)
                (R := BIBase.wand (state_interp (M := M) (F := F) σ ns (κ ++ κs) nt)
                  (fupd' W E maskEmpty P0))).1
          have hpre :
              BIBase.sep (state_interp σ ns (κ ++ κs) nt)
                  (BIBase.wand (state_interp σ ns (κ ++ κs) nt)
                    (fupd' W E maskEmpty P0)) ⊢
                fupd' W E maskEmpty P0 := by
            simpa using
              (wand_elim_r (PROP := IProp GF)
                (P := state_interp σ ns (κ ++ κs) nt)
                (Q := fupd' W E maskEmpty P0))
          have hpre' :
              BIBase.sep (state_interp σ ns (κ ++ κs) nt)
                  (BIBase.sep IH
                    (BIBase.wand (state_interp σ ns (κ ++ κs) nt)
                      (fupd' W E maskEmpty P0))) ⊢
                BIBase.sep IH (fupd' W E maskEmpty P0) := by
            exact hassoc.trans (sep_mono (PROP := IProp GF) .rfl hpre)
          have hswap :
              BIBase.sep IH (fupd' W E maskEmpty P0) ⊢
                BIBase.sep (fupd' W E maskEmpty P0) IH :=
            (sep_comm (PROP := IProp GF)
              (P := IH)
              (Q := fupd' W E maskEmpty P0)).1
          have hpre'' :
              BIBase.sep (state_interp σ ns (κ ++ κs) nt)
                  (BIBase.sep IH
                    (BIBase.wand (state_interp σ ns (κ ++ κs) nt)
                      (fupd' W E maskEmpty P0))) ⊢
                BIBase.sep (fupd' W E maskEmpty P0) IH :=
            hpre'.trans hswap
          have hframe :
              BIBase.sep (fupd' W E maskEmpty P0) IH ⊢
                fupd' W E maskEmpty (BIBase.sep P0 IH) :=
            Iris.BaseLogic.fupd_frame_r 
              (E1 := E) (E2 := maskEmpty)
              (P := P0) (Q := IH)
          have hpred :
              ∀ σ, stuckness_pred s e σ → stuckness_pred s (K e) σ := by
            intro σ
            cases s <;> simp [stuckness_pred]
            · intro hred
              exact reducible_fill (K := K) e σ hred
          have hQ :
              BIBase.sep Q1 IH ⊢ Q2 := by
            refine forall_intro (PROP := IProp GF) ?_; intro e2
            refine forall_intro (PROP := IProp GF) ?_; intro σ2
            refine forall_intro (PROP := IProp GF) ?_; intro efs
            refine wand_intro (PROP := IProp GF) ?_
            -- turn the step of `K e` into a step of `e`
            have hstep_ex :
                BIBase.pure (Λ.prim_step (K e) σ κ e2 σ2 efs) ⊢
                  BIBase.pure (∃ e2', e2 = K e2' ∧ Λ.prim_step e σ κ e2' σ2 efs) :=
              pure_mono (PROP := IProp GF) <| by
                intro hstep
                exact LanguageCtx.fill_step_inv (K := K) (e1' := e) (σ1 := σ) (κ := κ)
                  (e2 := e2) (σ2 := σ2) (efs := efs) hto hstep
            have h1 :
                BIBase.sep (BIBase.sep Q1 IH)
                    (BIBase.pure (Λ.prim_step (K e) σ κ e2 σ2 efs)) ⊢
                  BIBase.pure (∃ e2', e2 = K e2' ∧
                    Λ.prim_step e σ κ e2' σ2 efs) := by
              refine (sep_mono (PROP := IProp GF) .rfl hstep_ex).trans ?_
              refine (sep_comm (PROP := IProp GF)
                (P := BIBase.sep Q1 IH)
                (Q := BIBase.pure (∃ e2', e2 = K e2' ∧
                  Λ.prim_step e σ κ e2' σ2 efs))).1.trans ?_
              exact pure_sep_elim_left (φ := ∃ e2', e2 = K e2' ∧
                Λ.prim_step e σ κ e2' σ2 efs) (P := BIBase.sep Q1 IH)
            refine pure_elim (φ := ∃ e2', e2 = K e2' ∧ Λ.prim_step e σ κ e2' σ2 efs)
              (h1 := h1) ?_
            intro hstep
            rcases hstep with ⟨e2', heq, hstep⟩
            have hdrop :
                BIBase.sep (BIBase.sep Q1 IH)
                    (BIBase.pure (∃ e2', e2 = K e2' ∧
                      Λ.prim_step e σ κ e2' σ2 efs)) ⊢
                  BIBase.sep Q1 IH := by
              refine (sep_comm (PROP := IProp GF)
                (P := BIBase.sep Q1 IH)
                (Q := BIBase.pure (∃ e2', e2 = K e2' ∧
                  Λ.prim_step e σ κ e2' σ2 efs))).1.trans ?_
              exact sep_elim_r (PROP := IProp GF)
                (P := BIBase.pure (∃ e2', e2 = K e2' ∧
                  Λ.prim_step e σ κ e2' σ2 efs))
                (Q := BIBase.sep Q1 IH)
            have hstep_pure :
                (True : IProp GF) ⊢ BIBase.pure (Λ.prim_step e σ κ e2' σ2 efs) :=
              pure_intro hstep
            have hinsert :
                BIBase.sep Q1 IH ⊢
                  BIBase.sep (BIBase.pure (Λ.prim_step e σ κ e2' σ2 efs))
                    (BIBase.sep Q1 IH) := by
              refine (true_sep_2 (PROP := IProp GF) (P := BIBase.sep Q1 IH)).trans ?_
              exact sep_mono (PROP := IProp GF) hstep_pure .rfl
            have hswap :
                BIBase.sep (BIBase.pure (Λ.prim_step e σ κ e2' σ2 efs))
                    (BIBase.sep Q1 IH) ⊢
                  BIBase.sep (BIBase.sep Q1
                      (BIBase.pure (Λ.prim_step e σ κ e2' σ2 efs))) IH := by
              refine (sep_left_comm (PROP := IProp GF)
                (P := BIBase.pure (Λ.prim_step e σ κ e2' σ2 efs))
                (Q := Q1) (R := IH)).1.trans ?_
              exact (sep_assoc (PROP := IProp GF)
                (P := Q1) (Q := BIBase.pure (Λ.prim_step e σ κ e2' σ2 efs))
                (R := IH)).2
            have hcont :
                BIBase.sep Q1 (BIBase.pure (Λ.prim_step e σ κ e2' σ2 efs)) ⊢
                  fupd' W maskEmpty E
                    (BIBase.later
                      (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                        (BIBase.sep
                          (wp_s W s E e2'
                            (fun v =>
                              wp_s W s E
                                (K (Λ.of_val v)) Φ))
                          (big_sepL (fun _ ef =>
                            wp_s W s
                              Iris.Set.univ ef fork_post) efs)))) := by
              have h1 :=
                forall_elim (PROP := IProp GF)
                  (Ψ := fun e2 : Λ.expr =>
                    BIBase.forall fun σ2 : Λ.state =>
                      BIBase.forall fun efs : List Λ.expr =>
                        BIBase.wand (BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs))
                          (fupd' W maskEmpty E
                            (BIBase.later
                              (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                                (BIBase.sep
                                  (wp_s W s E e2
                                    (fun v =>
                                      wp_s W s E
                                        (K (Λ.of_val v)) Φ))
                                  (big_sepL (fun _ ef =>
                                    wp_s W s
                                      Iris.Set.univ ef fork_post) efs)))))) e2'
              have h2 :=
                forall_elim (PROP := IProp GF)
                  (Ψ := fun σ2 : Λ.state =>
                    BIBase.forall fun efs : List Λ.expr =>
                      BIBase.wand (BIBase.pure (Λ.prim_step e σ κ e2' σ2 efs))
                        (fupd' W maskEmpty E
                          (BIBase.later
                            (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                              (BIBase.sep
                                (wp_s W s E e2'
                                  (fun v =>
                                    wp_s W s E
                                      (K (Λ.of_val v)) Φ))
                                (big_sepL (fun _ ef =>
                                  wp_s W s
                                    Iris.Set.univ ef fork_post) efs)))))) σ2
              have h3 :=
                forall_elim (PROP := IProp GF)
                  (Ψ := fun efs : List Λ.expr =>
                    BIBase.wand (BIBase.pure (Λ.prim_step e σ κ e2' σ2 efs))
                      (fupd' W maskEmpty E
                        (BIBase.later
                          (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                            (BIBase.sep
                              (wp_s W s E e2'
                                (fun v =>
                                  wp_s W s E
                                    (K (Λ.of_val v)) Φ))
                              (big_sepL (fun _ ef =>
                                wp_s W s
                                  Iris.Set.univ ef fork_post) efs)))))) efs
              have h123 := h1.trans (h2.trans h3)
              exact (sep_mono (PROP := IProp GF) h123 .rfl).trans
                (wand_elim_l (PROP := IProp GF))
            -- use the continuation and thread IH through the later
            have happly :
                BIBase.sep (BIBase.sep Q1 (BIBase.pure (Λ.prim_step e σ κ e2' σ2 efs))) IH ⊢
                  BIBase.sep
                    (fupd' W maskEmpty E
                      (BIBase.later
                        (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                          (BIBase.sep
                            (wp_s W s E e2'
                              (fun v =>
                                wp_s W s E
                                  (K (Λ.of_val v)) Φ))
                            (big_sepL (fun _ ef =>
                              wp_s W s
                                Iris.Set.univ ef fork_post) efs)))))
                    IH :=
              sep_mono (PROP := IProp GF) hcont .rfl
            have hframe :
                BIBase.sep
                    (fupd' W maskEmpty E
                      (BIBase.later
                        (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                          (BIBase.sep
                            (wp_s W s E e2'
                              (fun v =>
                                wp_s W s E
                                  (K (Λ.of_val v)) Φ))
                            (big_sepL (fun _ ef =>
                              wp_s W s
                                Iris.Set.univ ef fork_post) efs)))))
                    IH ⊢
                  fupd' W maskEmpty E
                    (BIBase.sep
                      (BIBase.later
                        (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                          (BIBase.sep
                            (wp_s W s E e2'
                              (fun v =>
                                wp_s W s E
                                  (K (Λ.of_val v)) Φ))
                            (big_sepL (fun _ ef =>
                              wp_s W s
                                Iris.Set.univ ef fork_post) efs))))
                      IH) :=
              Iris.BaseLogic.fupd_frame_r 
                (E1 := maskEmpty) (E2 := E)
                (P := BIBase.later
                  (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                    (BIBase.sep
                      (wp_s W s E e2'
                        (fun v =>
                          wp_s W s E
                            (K (Λ.of_val v)) Φ))
                      (big_sepL (fun _ ef =>
                        wp_s W s
                          Iris.Set.univ ef fork_post) efs))))
                (Q := IH)
            have hIHlater :
                BIBase.sep IH
                    (BIBase.later
                      (wp_s W s E e2'
                        (fun v =>
                          wp_s W s E
                            (K (Λ.of_val v)) Φ))) ⊢
                  BIBase.later
                    (wp_s W s E (K e2') Φ) := by
              have hPelim' :
                  BIBase.later P ⊢ BIBase.later
                    (BIBase.wand
                      (wp_s W s E e2'
                        (fun v =>
                          wp_s W s E
                            (K (Λ.of_val v)) Φ))
                      (wp_s W s E (K e2') Φ)) :=
                later_mono (hPelim (E := E) (e := e2') (Φ := Φ))
              have hwand :
                  IH ⊢ BIBase.later
                    (BIBase.wand
                      (wp_s W s E e2'
                        (fun v =>
                          wp_s W s E
                            (K (Λ.of_val v)) Φ))
                      (wp_s W s E (K e2') Φ)) :=
                (intuitionistically_elim (PROP := IProp GF) (P := BIBase.later P)).trans hPelim'
              exact (sep_mono (PROP := IProp GF) hwand .rfl).trans
                (later_wand_elim (P := wp_s W s E e2'
                  (fun v =>
                    wp_s W s E
                      (K (Λ.of_val v)) Φ))
                  (Q := wp_s W s E (K e2') Φ))
            have hinner :
                BIBase.sep
                    (BIBase.later
                      (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                        (BIBase.sep
                          (wp_s W s E e2'
                            (fun v =>
                              wp_s W s E
                                (K (Λ.of_val v)) Φ))
                          (big_sepL (fun _ ef =>
                            wp_s W s
                              Iris.Set.univ ef fork_post) efs))))
                    IH ⊢
                  BIBase.later
                    (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                      (BIBase.sep
                        (wp_s W s E (K e2') Φ)
                        (big_sepL (fun _ ef =>
                          wp_s W s
                            Iris.Set.univ ef fork_post) efs))) := by
              -- split the later and use IH on the main WP
              refine (sep_mono (PROP := IProp GF)
                (later_sep (PROP := IProp GF)
                  (P := state_interp σ2 (ns + 1) κs (efs.length + nt))
                  (Q := BIBase.sep
                    (wp_s W s E e2'
                      (fun v =>
                        wp_s W s E
                          (K (Λ.of_val v)) Φ))
                    (big_sepL (fun _ ef =>
                      wp_s W s
                        Iris.Set.univ ef fork_post) efs))).1 .rfl).trans ?_
              refine (sep_assoc (PROP := IProp GF)
                (P := BIBase.later (state_interp σ2 (ns + 1) κs (efs.length + nt)))
                (Q := BIBase.later
                  (BIBase.sep
                    (wp_s W s E e2'
                      (fun v =>
                        wp_s W s E
                          (K (Λ.of_val v)) Φ))
                    (big_sepL (fun _ ef =>
                      wp_s W s
                        Iris.Set.univ ef fork_post) efs)))
                (R := IH)).1.trans ?_
              -- handle the continuation part
              have hcont :
                  BIBase.sep
                      (BIBase.later
                        (BIBase.sep
                          (wp_s W s E e2'
                            (fun v =>
                              wp_s W s E
                                (K (Λ.of_val v)) Φ))
                          (big_sepL (fun _ ef =>
                            wp_s W s
                              Iris.Set.univ ef fork_post) efs)))
                      IH ⊢
                    BIBase.later
                      (BIBase.sep
                        (wp_s W s E (K e2') Φ)
                        (big_sepL (fun _ ef =>
                          wp_s W s
                            Iris.Set.univ ef fork_post) efs)) := by
                refine (sep_mono (PROP := IProp GF)
                  (later_sep (PROP := IProp GF)
                    (P := wp_s W s E e2'
                      (fun v =>
                        wp_s W s E
                          (K (Λ.of_val v)) Φ))
                    (Q := big_sepL (fun _ ef =>
                      wp_s W s
                        Iris.Set.univ ef fork_post) efs)).1 .rfl).trans ?_
                refine (sep_assoc (PROP := IProp GF)
                  (P := BIBase.later
                    (wp_s W s E e2'
                      (fun v =>
                        wp_s W s E
                          (K (Λ.of_val v)) Φ)))
                  (Q := BIBase.later
                    (big_sepL (fun _ ef =>
                      wp_s W s
                        Iris.Set.univ ef fork_post) efs))
                  (R := IH)).1.trans ?_
                -- move IH next to the main WP
                have hswap :
                    BIBase.sep
                        (BIBase.later
                          (wp_s W s E e2'
                            (fun v =>
                              wp_s W s E
                                (K (Λ.of_val v)) Φ)))
                        (BIBase.sep
                          (BIBase.later
                            (big_sepL (fun _ ef =>
                              wp_s W s
                                Iris.Set.univ ef fork_post) efs))
                          IH) ⊢
                      BIBase.sep
                        (BIBase.sep IH
                          (BIBase.later
                            (wp_s W s E e2'
                              (fun v =>
                                wp_s W s E
                                  (K (Λ.of_val v)) Φ))))
                        (BIBase.later
                          (big_sepL (fun _ ef =>
                            wp_s W s
                              Iris.Set.univ ef fork_post) efs)) := by
                  refine (sep_assoc (PROP := IProp GF)
                    (P := BIBase.later
                      (wp_s W s E e2'
                        (fun v =>
                          wp_s W s E
                            (K (Λ.of_val v)) Φ)))
                    (Q := BIBase.later
                      (big_sepL (fun _ ef =>
                        wp_s W s
                          Iris.Set.univ ef fork_post) efs))
                    (R := IH)).2.trans ?_
                  refine (sep_right_comm (PROP := IProp GF)
                    (P := BIBase.later
                      (wp_s W s E e2'
                        (fun v =>
                          wp_s W s E
                            (K (Λ.of_val v)) Φ)))
                    (Q := BIBase.later
                      (big_sepL (fun _ ef =>
                        wp_s W s
                          Iris.Set.univ ef fork_post) efs))
                    (R := IH)).1.trans ?_
                  -- swap inside the left component
                  exact (sep_mono (PROP := IProp GF)
                    (sep_comm (PROP := IProp GF)
                      (P := BIBase.later
                        (wp_s W s E e2'
                          (fun v =>
                            wp_s W s E
                              (K (Λ.of_val v)) Φ)))
                      (Q := IH)).1 .rfl)
                refine hswap.trans ?_
                refine (sep_mono (PROP := IProp GF) (hIHlater) .rfl).trans ?_
                exact (later_sep (PROP := IProp GF)
                  (P := wp_s W s E (K e2') Φ)
                  (Q := big_sepL (fun _ ef =>
                    wp_s W s
                      Iris.Set.univ ef fork_post) efs)).2
              -- combine the state part and the continuation
              refine (sep_mono (PROP := IProp GF) .rfl hcont).trans ?_
              exact (later_sep (PROP := IProp GF)
                (P := state_interp σ2 (ns + 1) κs (efs.length + nt))
                (Q := BIBase.sep
                  (wp_s W s E (K e2') Φ)
                  (big_sepL (fun _ ef =>
                    wp_s W s
                      Iris.Set.univ ef fork_post) efs))).2
            have hmono :
                fupd' W maskEmpty E
                    (BIBase.sep
                      (BIBase.later
                        (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                          (BIBase.sep
                            (wp_s W s E e2'
                              (fun v =>
                                wp_s W s E
                                  (K (Λ.of_val v)) Φ))
                            (big_sepL (fun _ ef =>
                              wp_s W s
                                Iris.Set.univ ef fork_post) efs))))
                      IH) ⊢
                  fupd' W maskEmpty E
                    (BIBase.later
                      (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                        (BIBase.sep
                          (wp_s W s E (K e2') Φ)
                          (big_sepL (fun _ ef =>
                            wp_s W s
                              Iris.Set.univ ef fork_post) efs)))) :=
              Iris.BaseLogic.fupd_mono 
                (E1 := maskEmpty) (E2 := E)
                (P := BIBase.sep
                  (BIBase.later
                    (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                      (BIBase.sep
                        (wp_s W s E e2'
                          (fun v =>
                            wp_s W s E
                              (K (Λ.of_val v)) Φ))
                        (big_sepL (fun _ ef =>
                          wp_s W s
                            Iris.Set.univ ef fork_post) efs))))
                  IH)
                (Q := BIBase.later
                  (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                    (BIBase.sep
                      (wp_s W s E (K e2') Φ)
                      (big_sepL (fun _ ef =>
                        wp_s W s
                          Iris.Set.univ ef fork_post) efs)))) hinner
            have hfinal' :=
              hdrop.trans (hinsert.trans (hswap.trans (happly.trans (hframe.trans hmono))))
            have hfinal :=
              (sep_mono (PROP := IProp GF) .rfl hstep_ex).trans hfinal'
            simpa [heq] using hfinal
          have hpost :
              BIBase.sep P0 IH ⊢ P1 := by
            dsimp [P0, P1]
            refine (sep_assoc (PROP := IProp GF)
              (P := BIBase.pure (stuckness_pred s e σ)) (Q := Q1) (R := IH)).1.trans ?_
            exact sep_mono (PROP := IProp GF)
              (pure_mono (PROP := IProp GF) (hpred σ)) hQ
          have hmono :
              fupd' W E maskEmpty (BIBase.sep P0 IH) ⊢
                fupd' W E maskEmpty P1 :=
            Iris.BaseLogic.fupd_mono 
              (E1 := E) (E2 := maskEmpty)
              (P := BIBase.sep P0 IH) (Q := P1) hpost
          -- commute to match the `state_interp ∗ (IH ∗ wand)` ordering
          have hswap0 :
              BIBase.sep (BIBase.sep IH
                    (BIBase.wand (state_interp σ ns (κ ++ κs) nt)
                      (fupd' W E maskEmpty P0)))
                (state_interp σ ns (κ ++ κs) nt) ⊢
                BIBase.sep (state_interp σ ns (κ ++ κs) nt)
                  (BIBase.sep IH
                    (BIBase.wand (state_interp σ ns (κ ++ κs) nt)
                      (fupd' W E maskEmpty P0))) :=
            (sep_comm (PROP := IProp GF)
              (P := BIBase.sep IH
                (BIBase.wand (state_interp σ ns (κ ++ κs) nt)
                  (fupd' W E maskEmpty P0)))
              (Q := state_interp σ ns (κ ++ κs) nt)).1
          exact hswap0.trans (hpre''.trans (hframe.trans hmono))
        exact hpre.trans hwpK
  have hstep_box :
      BIBase.intuitionistically (BIBase.later P) ⊢ BIBase.intuitionistically P :=
    intuitionistically_intro' (P := BIBase.later P) (Q := P) hstep
  have hlater :
      BIBase.later (BIBase.intuitionistically P) ⊢
        BIBase.intuitionistically (BIBase.later P) :=
    (later_intuitionistically (PROP := IProp GF) (P := P)).2
  have hloop :
      BIBase.later (BIBase.intuitionistically P) ⊢ BIBase.intuitionistically P :=
    hlater.trans hstep_box
  have hloeb :
      (True : IProp GF) ⊢ BIBase.intuitionistically P :=
    BILoeb.loeb_weak (PROP := IProp GF) (P := BIBase.intuitionistically P) hloop
  have hP : (True : IProp GF) ⊢ P :=
    hloeb.trans (intuitionistically_elim (PROP := IProp GF) (P := P))
  have hwand :
      (True : IProp GF) ⊢
        BIBase.wand
          (wp_s W s E e
            (fun v => wp_s W s E (K (Λ.of_val v)) Φ))
          (wp_s W s E (K e) Φ) :=
    hP.trans (hPelim (E := E) (e := e) (Φ := Φ))
  have hframe :
      wp_s W s E e
          (fun v => wp_s W s E (K (Λ.of_val v)) Φ) ⊢
        BIBase.sep
          (BIBase.wand
            (wp_s W s E e
              (fun v => wp_s W s E
                (K (Λ.of_val v)) Φ))
            (wp_s W s E (K e) Φ))
          (wp_s W s E e
            (fun v => wp_s W s E (K (Λ.of_val v)) Φ)) := by
    refine (true_sep_2 (PROP := IProp GF)
      (P := wp_s W s E e
        (fun v => wp_s W s E
          (K (Λ.of_val v)) Φ))).trans ?_
    exact sep_mono (PROP := IProp GF) hwand .rfl
  exact hframe.trans (wand_elim_l (PROP := IProp GF))

/-- Inverse bind rule.
Coq: `wp_bind_inv` in `weakestpre.v`. -/
theorem wp_bind_inv (K : Λ.expr → Λ.expr) [LanguageCtx K]
    (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IPropWsat GF M F) :
    wp_s W s E (K e) Φ ⊢
    wp_s W s E e
      (fun v => wp_s W s E (K (Λ.of_val v)) Φ) :=
  by
  let post : Λ.val → IPropWsat GF M F :=
    fun v => wp_s W s E (K (Λ.of_val v)) Φ
  let P : IPropWsat GF M F :=
    BIBase.forall fun E =>
      BIBase.forall fun e =>
        BIBase.forall fun Φ =>
          BIBase.wand
            (wp_s W s E (K e) Φ)
            (wp_s W s E e
              (fun v => wp_s W s E (K (Λ.of_val v)) Φ))
  have hPelim (E : Iris.Set Positive) (e : Λ.expr) (Φ : Λ.val → IPropWsat GF M F) :
      P ⊢ BIBase.wand
        (wp_s W s E (K e) Φ)
        (wp_s W s E e
          (fun v => wp_s W s E (K (Λ.of_val v)) Φ)) := by
    refine (forall_elim (PROP := IProp GF) (Ψ := fun E => _) E).trans ?_
    refine (forall_elim (PROP := IProp GF) (Ψ := fun e => _) e).trans ?_
    exact (forall_elim (PROP := IProp GF) (Ψ := fun Φ => _) Φ)
  have hstep : BIBase.intuitionistically (BIBase.later P) ⊢ P := by
    refine forall_intro (PROP := IProp GF) ?_; intro E
    refine forall_intro (PROP := IProp GF) ?_; intro e
    refine forall_intro (PROP := IProp GF) ?_; intro Φ
    cases hto : Λ.to_val e with
    | some v =>
        have hval :
            wp_s W s E (K e) Φ ⊢
              wp_s W s E e
                (fun v => wp_s W s E
                  (K (Λ.of_val v)) Φ) := by
          have hK : K e = K (Λ.of_val v) := by
            simp [of_to_val e v hto]
          have hpre :
              wp_s W s E (K e) Φ ⊢
                fupd' W E E
                  (wp_s W s E (K (Λ.of_val v)) Φ) := by
            simpa [hK] using
              (fupd_intro (E := E)
                (P := wp_s W s E
                  (K (Λ.of_val v)) Φ))
          have hpre' :
              wp_s W s E (K e) Φ ⊢
                wp_pre_s W s
                  (wp_s W s) E e
                  (fun v => wp_s W s E
                    (K (Λ.of_val v)) Φ) := by
            simpa [wp_pre, hto] using hpre
          have hwp :
              wp_pre_s W s
                  (wp_s W s) E e
                  (fun v => wp_s W s E
                    (K (Λ.of_val v)) Φ) ⊢
                wp_s W s E e
                  (fun v => wp_s W s E
                    (K (Λ.of_val v)) Φ) :=
            (wp_unfold (s := s) (E := E) (e := e)
              (Φ := fun v => wp_s W s E
                (K (Λ.of_val v)) Φ)).2
          exact hpre'.trans hwp
        have htrue :
            (True : IProp GF) ⊢ BIBase.wand
              (wp_s W s E (K e) Φ)
              (wp_s W s E e
                (fun v => wp_s W s E
                  (K (Λ.of_val v)) Φ)) := by
          refine wand_intro (PROP := IProp GF) ?_
          exact (sep_elim_r (PROP := IProp GF) (P := (BIBase.pure True))
            (Q := wp_s W s E (K e) Φ)).trans
            hval
        exact (true_intro (P := BIBase.intuitionistically (BIBase.later P))).trans htrue
    | none =>
        let IH : IPropWsat GF M F :=
          BIBase.intuitionistically (BIBase.later P)
        refine wand_intro (PROP := IProp GF) ?_
        have hwp :
            wp_s W s E (K e) Φ ⊢
              wp_pre_s W s
                (wp_s W s) E (K e) Φ :=
          (wp_unfold (s := s) (E := E)
            (e := K e) (Φ := Φ)).1
        have hwpK :
            wp_pre_s W s
                (wp_s W s) E e
                (fun v => wp_s W s E
                  (K (Λ.of_val v)) Φ) ⊢
              wp_s W s E e
                (fun v => wp_s W s E
                  (K (Λ.of_val v)) Φ) :=
          (wp_unfold (s := s) (E := E) (e := e)
            (Φ := fun v => wp_s W s E
              (K (Λ.of_val v)) Φ)).2
        refine (sep_mono (PROP := IProp GF) .rfl hwp).trans ?_
        have htoK : Λ.to_val (K e) = none :=
          LanguageCtx.fill_not_val (K := K) e hto
        have hpre :
            BIBase.sep IH
                (wp_pre_s W s
                  (wp_s W s) E (K e) Φ) ⊢
              wp_pre_s W s
                (wp_s W s) E e
                (fun v => wp_s W s E
                  (K (Λ.of_val v)) Φ) := by
          -- unfold only the right-hand `wp_pre W`
          simp [wp_pre, hto, wp_pre_step]
          refine forall_intro (PROP := IProp GF) ?_; intro σ
          refine forall_intro (PROP := IProp GF) ?_; intro ns
          refine forall_intro (PROP := IProp GF) ?_; intro κ
          refine forall_intro (PROP := IProp GF) ?_; intro κs
          refine forall_intro (PROP := IProp GF) ?_; intro nt
          have hview :=
            wp_pre_elim (W := W) (s := s) (E := E) (e := K e) (Φ := Φ)
              (σ := σ) (ns := ns) (κ := κ) (κs := κs) (nt := nt) htoK
          have hleft :
              BIBase.sep IH
                  (wp_pre_s W s
                    (wp_s W s) E (K e) Φ) ⊢
                BIBase.sep IH
                  (wp_pre_view W s E (K e) Φ
                    σ ns κ κs nt) :=
            sep_mono (PROP := IProp GF) .rfl hview
          refine hleft.trans ?_
          let Q1 : IPropWsat GF M F :=
            BIBase.forall fun e2 : Λ.expr =>
              BIBase.forall fun σ2 : Λ.state =>
                BIBase.forall fun efs : List Λ.expr =>
                  BIBase.wand (BIBase.pure (Λ.prim_step (K e) σ κ e2 σ2 efs))
                    (fupd' W maskEmpty E
                      (BIBase.later
                        (BIBase.sep (state_interp (M := M) (F := F) σ2 (ns + 1) κs (efs.length + nt))
                          (BIBase.sep
                            (wp_s W s E e2 Φ)
                            (big_sepL (fun _ ef =>
                              wp_s W s
                                Iris.Set.univ ef fork_post) efs)))))
          let Q2 : IPropWsat GF M F :=
            BIBase.forall fun e2 : Λ.expr =>
              BIBase.forall fun σ2 : Λ.state =>
                BIBase.forall fun efs : List Λ.expr =>
                  BIBase.wand (BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs))
                    (fupd' W maskEmpty E
                      (BIBase.later
                        (BIBase.sep (state_interp (M := M) (F := F) σ2 (ns + 1) κs (efs.length + nt))
                          (BIBase.sep
                            (wp_s W s E e2
                              (fun v =>
                                wp_s W s E
                                  (K (Λ.of_val v)) Φ))
                            (big_sepL (fun _ ef =>
                              wp_s W s
                                Iris.Set.univ ef fork_post) efs)))))
          let P0 : IPropWsat GF M F :=
            BIBase.sep (BIBase.pure (stuckness_pred s (K e) σ)) Q1
          let P1 : IPropWsat GF M F :=
            BIBase.sep (BIBase.pure (stuckness_pred s e σ)) Q2
          dsimp [wp_pre_view, Q1, Q2, P0, P1]
          refine wand_intro (PROP := IProp GF) ?_
          have hassoc :
              BIBase.sep (state_interp (M := M) (F := F) σ ns (κ ++ κs) nt)
                  (BIBase.sep IH
                    (BIBase.wand (state_interp (M := M) (F := F) σ ns (κ ++ κs) nt)
                      (fupd' W E maskEmpty P0))) ⊢
                BIBase.sep IH
                  (BIBase.sep (state_interp (M := M) (F := F) σ ns (κ ++ κs) nt)
                    (BIBase.wand (state_interp (M := M) (F := F) σ ns (κ ++ κs) nt)
                      (fupd' W E maskEmpty P0))) := by
            simpa [sep_assoc] using
              (sep_left_comm (PROP := IProp GF)
                (P := state_interp (M := M) (F := F) σ ns (κ ++ κs) nt) (Q := IH)
                (R := BIBase.wand (state_interp (M := M) (F := F) σ ns (κ ++ κs) nt)
                  (fupd' W E maskEmpty P0))).1
          have hpre0 :
              BIBase.sep (state_interp (M := M) (F := F) σ ns (κ ++ κs) nt)
                  (BIBase.wand (state_interp (M := M) (F := F) σ ns (κ ++ κs) nt)
                    (fupd' W E maskEmpty P0)) ⊢
                fupd' W E maskEmpty P0 := by
            simpa using
              (wand_elim_r (PROP := IProp GF)
                (P := state_interp (M := M) (F := F) σ ns (κ ++ κs) nt)
                (Q := fupd' W E maskEmpty P0))
          have hpre' :
              BIBase.sep (state_interp (M := M) (F := F) σ ns (κ ++ κs) nt)
                  (BIBase.sep IH
                    (BIBase.wand (state_interp (M := M) (F := F) σ ns (κ ++ κs) nt)
                      (fupd' W E maskEmpty P0))) ⊢
                BIBase.sep IH (fupd' W E maskEmpty P0) := by
            exact hassoc.trans (sep_mono (PROP := IProp GF) .rfl hpre0)
          have hswap :
              BIBase.sep IH (fupd' W E maskEmpty P0) ⊢
                BIBase.sep (fupd' W E maskEmpty P0) IH :=
            (sep_comm (PROP := IProp GF)
              (P := IH)
              (Q := fupd' W E maskEmpty P0)).1
          have hpre'' :
              BIBase.sep (state_interp σ ns (κ ++ κs) nt)
                  (BIBase.sep IH
                    (BIBase.wand (state_interp σ ns (κ ++ κs) nt)
                      (fupd' W E maskEmpty P0))) ⊢
                BIBase.sep (fupd' W E maskEmpty P0) IH :=
            hpre'.trans hswap
          have hframe :
              BIBase.sep (fupd' W E maskEmpty P0) IH ⊢
                fupd' W E maskEmpty (BIBase.sep P0 IH) :=
            Iris.BaseLogic.fupd_frame_r 
              (E1 := E) (E2 := maskEmpty)
              (P := P0) (Q := IH)
          have hpred :
              ∀ σ, stuckness_pred s (K e) σ → stuckness_pred s e σ := by
            intro σ
            cases s <;> simp [stuckness_pred]
            · intro hred
              exact reducible_fill_inv (K := K) e σ hto hred
          have hQ :
              BIBase.sep Q1 IH ⊢ Q2 := by
            refine forall_intro (PROP := IProp GF) ?_; intro e2
            refine forall_intro (PROP := IProp GF) ?_; intro σ2
            refine forall_intro (PROP := IProp GF) ?_; intro efs
            refine wand_intro (PROP := IProp GF) ?_
            -- lift the step through the context
            have hstepK :
                BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs) ⊢
                  BIBase.pure (Λ.prim_step (K e) σ κ (K e2) σ2 efs) :=
              pure_mono (PROP := IProp GF) <| by
                intro hstep
                exact LanguageCtx.fill_step (K := K) (e1 := e) (σ1 := σ) (κ := κ)
                  (e2 := e2) (σ2 := σ2) (efs := efs) hstep
            have hcont :
                BIBase.sep Q1 (BIBase.pure (Λ.prim_step (K e) σ κ (K e2) σ2 efs)) ⊢
                  fupd' W maskEmpty E
                    (BIBase.later
                      (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                        (BIBase.sep
                          (wp_s W s E (K e2) Φ)
                          (big_sepL (fun _ ef =>
                            wp_s W s
                              Iris.Set.univ ef fork_post) efs)))) := by
              have h1 :=
                forall_elim (PROP := IProp GF)
                  (Ψ := fun e2 : Λ.expr =>
                    BIBase.forall fun σ2 : Λ.state =>
                      BIBase.forall fun efs : List Λ.expr =>
                        BIBase.wand (BIBase.pure (Λ.prim_step (K e) σ κ e2 σ2 efs))
                          (fupd' W maskEmpty E
                            (BIBase.later
                              (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                                (BIBase.sep
                                  (wp_s W s E e2 Φ)
                                  (big_sepL (fun _ ef =>
                                    wp_s W s
                                      Iris.Set.univ ef fork_post) efs)))))) (K e2)
              have h2 :=
                forall_elim (PROP := IProp GF)
                  (Ψ := fun σ2 : Λ.state =>
                    BIBase.forall fun efs : List Λ.expr =>
                      BIBase.wand (BIBase.pure (Λ.prim_step (K e) σ κ (K e2) σ2 efs))
                        (fupd' W maskEmpty E
                          (BIBase.later
                            (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                              (BIBase.sep
                                (wp_s W s E (K e2) Φ)
                                (big_sepL (fun _ ef =>
                                  wp_s W s
                                    Iris.Set.univ ef fork_post) efs)))))) σ2
              have h3 :=
                forall_elim (PROP := IProp GF)
                  (Ψ := fun efs : List Λ.expr =>
                    BIBase.wand (BIBase.pure (Λ.prim_step (K e) σ κ (K e2) σ2 efs))
                      (fupd' W maskEmpty E
                        (BIBase.later
                          (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                            (BIBase.sep
                              (wp_s W s E (K e2) Φ)
                              (big_sepL (fun _ ef =>
                                wp_s W s
                                  Iris.Set.univ ef fork_post) efs)))))) efs
              have h123 := h1.trans (h2.trans h3)
              exact (sep_mono (PROP := IProp GF) h123 .rfl).trans
                (wand_elim_l (PROP := IProp GF))
            have happly :
                BIBase.sep (BIBase.sep Q1 IH) (BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs)) ⊢
                  BIBase.sep
                    (fupd' W maskEmpty E
                      (BIBase.later
                        (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                          (BIBase.sep
                            (wp_s W s E (K e2) Φ)
                            (big_sepL (fun _ ef =>
                              wp_s W s
                                Iris.Set.univ ef fork_post) efs)))))
                    IH := by
              refine (sep_mono (PROP := IProp GF) .rfl hstepK).trans ?_
              -- swap IH to apply the continuation
              have hswap :
                  BIBase.sep (BIBase.sep Q1 IH)
                      (BIBase.pure (Λ.prim_step (K e) σ κ (K e2) σ2 efs)) ⊢
                    BIBase.sep (BIBase.sep Q1
                        (BIBase.pure (Λ.prim_step (K e) σ κ (K e2) σ2 efs))) IH :=
                (sep_right_comm (PROP := IProp GF) (P := Q1) (Q := IH)
                  (R := BIBase.pure (Λ.prim_step (K e) σ κ (K e2) σ2 efs))).1
              exact hswap.trans (sep_mono (PROP := IProp GF) hcont .rfl)
            have hframe :
                BIBase.sep
                    (fupd' W maskEmpty E
                      (BIBase.later
                        (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                          (BIBase.sep
                            (wp_s W s E (K e2) Φ)
                            (big_sepL (fun _ ef =>
                              wp_s W s
                                Iris.Set.univ ef fork_post) efs)))))
                    IH ⊢
                  fupd' W maskEmpty E
                    (BIBase.sep
                      (BIBase.later
                        (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                          (BIBase.sep
                            (wp_s W s E (K e2) Φ)
                            (big_sepL (fun _ ef =>
                              wp_s W s
                                Iris.Set.univ ef fork_post) efs))))
                      IH) :=
              Iris.BaseLogic.fupd_frame_r 
                (E1 := maskEmpty) (E2 := E)
                (P := BIBase.later
                  (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                    (BIBase.sep
                      (wp_s W s E (K e2) Φ)
                      (big_sepL (fun _ ef =>
                        wp_s W s
                          Iris.Set.univ ef fork_post) efs))))
                (Q := IH)
            have hIHlater :
                BIBase.sep IH
                    (BIBase.later
                      (wp_s W s E (K e2) Φ)) ⊢
                  BIBase.later
                    (wp_s W s E e2
                      (fun v =>
                        wp_s W s E
                          (K (Λ.of_val v)) Φ)) := by
              have hPelim' :
                  BIBase.later P ⊢ BIBase.later
                    (BIBase.wand
                      (wp_s W s E (K e2) Φ)
                      (wp_s W s E e2
                        (fun v =>
                          wp_s W s E
                            (K (Λ.of_val v)) Φ))) :=
                later_mono (hPelim (E := E) (e := e2) (Φ := Φ))
              have hwand :
                  IH ⊢ BIBase.later
                    (BIBase.wand
                      (wp_s W s E (K e2) Φ)
                      (wp_s W s E e2
                        (fun v =>
                          wp_s W s E
                            (K (Λ.of_val v)) Φ))) :=
                (intuitionistically_elim (PROP := IProp GF) (P := BIBase.later P)).trans hPelim'
              exact (sep_mono (PROP := IProp GF) hwand .rfl).trans
                (later_wand_elim (P := wp_s W s E (K e2) Φ)
                  (Q := wp_s W s E e2
                    (fun v =>
                      wp_s W s E
                        (K (Λ.of_val v)) Φ)))
            have hinner :
                BIBase.sep
                    (BIBase.later
                      (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                        (BIBase.sep
                          (wp_s W s E (K e2) Φ)
                          (big_sepL (fun _ ef =>
                            wp_s W s
                              Iris.Set.univ ef fork_post) efs))))
                    IH ⊢
                  BIBase.later
                    (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                      (BIBase.sep
                        (wp_s W s E e2
                          (fun v =>
                            wp_s W s E
                              (K (Λ.of_val v)) Φ))
                        (big_sepL (fun _ ef =>
                          wp_s W s
                            Iris.Set.univ ef fork_post) efs))) := by
              refine (sep_mono (PROP := IProp GF)
                (later_sep (PROP := IProp GF)
                  (P := state_interp σ2 (ns + 1) κs (efs.length + nt))
                  (Q := BIBase.sep
                    (wp_s W s E (K e2) Φ)
                    (big_sepL (fun _ ef =>
                      wp_s W s
                        Iris.Set.univ ef fork_post) efs))).1 .rfl).trans ?_
              refine (sep_assoc (PROP := IProp GF)
                (P := BIBase.later (state_interp σ2 (ns + 1) κs (efs.length + nt)))
                (Q := BIBase.later
                  (BIBase.sep
                    (wp_s W s E (K e2) Φ)
                    (big_sepL (fun _ ef =>
                      wp_s W s
                        Iris.Set.univ ef fork_post) efs)))
                (R := IH)).1.trans ?_
              have hcont :
                  BIBase.sep
                      (BIBase.later
                        (BIBase.sep
                          (wp_s W s E (K e2) Φ)
                          (big_sepL (fun _ ef =>
                            wp_s W s
                              Iris.Set.univ ef fork_post) efs)))
                      IH ⊢
                    BIBase.later
                      (BIBase.sep
                        (wp_s W s E e2
                          (fun v =>
                            wp_s W s E
                              (K (Λ.of_val v)) Φ))
                        (big_sepL (fun _ ef =>
                          wp_s W s
                            Iris.Set.univ ef fork_post) efs)) := by
                refine (sep_mono (PROP := IProp GF)
                  (later_sep (PROP := IProp GF)
                    (P := wp_s W s E (K e2) Φ)
                    (Q := big_sepL (fun _ ef =>
                      wp_s W s
                        Iris.Set.univ ef fork_post) efs)).1 .rfl).trans ?_
                refine (sep_assoc (PROP := IProp GF)
                  (P := BIBase.later
                    (wp_s W s E (K e2) Φ))
                  (Q := BIBase.later
                    (big_sepL (fun _ ef =>
                      wp_s W s
                        Iris.Set.univ ef fork_post) efs))
                  (R := IH)).1.trans ?_
                -- move IH next to the main WP
                have hswap :
                    BIBase.sep
                        (BIBase.later
                          (wp_s W s E (K e2) Φ))
                        (BIBase.sep
                          (BIBase.later
                            (big_sepL (fun _ ef =>
                              wp_s W s
                                Iris.Set.univ ef fork_post) efs))
                          IH) ⊢
                      BIBase.sep
                        (BIBase.sep IH
                          (BIBase.later
                            (wp_s W s E (K e2) Φ)))
                        (BIBase.later
                          (big_sepL (fun _ ef =>
                            wp_s W s
                              Iris.Set.univ ef fork_post) efs)) := by
                  refine (sep_assoc (PROP := IProp GF)
                    (P := BIBase.later
                      (wp_s W s E (K e2) Φ))
                    (Q := BIBase.later
                      (big_sepL (fun _ ef =>
                        wp_s W s
                          Iris.Set.univ ef fork_post) efs))
                    (R := IH)).2.trans ?_
                  refine (sep_right_comm (PROP := IProp GF)
                    (P := BIBase.later
                      (wp_s W s E (K e2) Φ))
                    (Q := BIBase.later
                      (big_sepL (fun _ ef =>
                        wp_s W s
                          Iris.Set.univ ef fork_post) efs))
                    (R := IH)).1.trans ?_
                  exact (sep_mono (PROP := IProp GF)
                    (sep_comm (PROP := IProp GF)
                      (P := BIBase.later
                        (wp_s W s E (K e2) Φ))
                      (Q := IH)).1 .rfl)
                refine hswap.trans ?_
                refine (sep_mono (PROP := IProp GF) hIHlater .rfl).trans ?_
                exact (later_sep (PROP := IProp GF)
                  (P := wp_s W s E e2
                    (fun v =>
                      wp_s W s E
                        (K (Λ.of_val v)) Φ))
                  (Q := big_sepL (fun _ ef =>
                    wp_s W s
                      Iris.Set.univ ef fork_post) efs)).2
              refine (sep_mono (PROP := IProp GF) .rfl hcont).trans ?_
              exact (later_sep (PROP := IProp GF)
                (P := state_interp σ2 (ns + 1) κs (efs.length + nt))
                (Q := BIBase.sep
                  (wp_s W s E e2
                    (fun v =>
                      wp_s W s E
                        (K (Λ.of_val v)) Φ))
                  (big_sepL (fun _ ef =>
                    wp_s W s
                      Iris.Set.univ ef fork_post) efs))).2
            have hmono :
                fupd' W maskEmpty E
                    (BIBase.sep
                      (BIBase.later
                        (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                          (BIBase.sep
                            (wp_s W s E (K e2) Φ)
                            (big_sepL (fun _ ef =>
                              wp_s W s
                                Iris.Set.univ ef fork_post) efs))))
                      IH) ⊢
                  fupd' W maskEmpty E
                    (BIBase.later
                      (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                        (BIBase.sep
                          (wp_s W s E e2
                            (fun v =>
                              wp_s W s E
                                (K (Λ.of_val v)) Φ))
                          (big_sepL (fun _ ef =>
                            wp_s W s
                              Iris.Set.univ ef fork_post) efs)))) :=
              Iris.BaseLogic.fupd_mono 
                (E1 := maskEmpty) (E2 := E)
                (P := BIBase.sep
                  (BIBase.later
                    (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                      (BIBase.sep
                        (wp_s W s E (K e2) Φ)
                        (big_sepL (fun _ ef =>
                          wp_s W s
                            Iris.Set.univ ef fork_post) efs))))
                  IH)
                (Q := BIBase.later
                  (BIBase.sep (state_interp σ2 (ns + 1) κs (efs.length + nt))
                    (BIBase.sep
                      (wp_s W s E e2
                        (fun v =>
                          wp_s W s E
                            (K (Λ.of_val v)) Φ))
                      (big_sepL (fun _ ef =>
                        wp_s W s
                          Iris.Set.univ ef fork_post) efs)))) hinner
            exact (happly.trans (hframe.trans hmono))
          have hpost :
              BIBase.sep P0 IH ⊢ P1 := by
            dsimp [P0, P1]
            refine (sep_assoc (PROP := IProp GF)
              (P := BIBase.pure (stuckness_pred s (K e) σ)) (Q := Q1) (R := IH)).1.trans ?_
            exact sep_mono (PROP := IProp GF)
              (pure_mono (PROP := IProp GF) (hpred σ)) hQ
          have hmono :
              fupd' W E maskEmpty (BIBase.sep P0 IH) ⊢
                fupd' W E maskEmpty P1 :=
            Iris.BaseLogic.fupd_mono 
              (E1 := E) (E2 := maskEmpty)
              (P := BIBase.sep P0 IH) (Q := P1) hpost
          have hswap0 :
              BIBase.sep (BIBase.sep IH
                    (BIBase.wand (state_interp σ ns (κ ++ κs) nt)
                      (fupd' W E maskEmpty P0)))
                (state_interp σ ns (κ ++ κs) nt) ⊢
                BIBase.sep (state_interp σ ns (κ ++ κs) nt)
                  (BIBase.sep IH
                    (BIBase.wand (state_interp σ ns (κ ++ κs) nt)
                      (fupd' W E maskEmpty P0))) :=
            (sep_comm (PROP := IProp GF)
              (P := BIBase.sep IH
                (BIBase.wand (state_interp σ ns (κ ++ κs) nt)
                  (fupd' W E maskEmpty P0)))
              (Q := state_interp σ ns (κ ++ κs) nt)).1
          exact hswap0.trans (hpre''.trans (hframe.trans hmono))
        exact hpre.trans hwpK
  have hstep_box :
      BIBase.intuitionistically (BIBase.later P) ⊢ BIBase.intuitionistically P :=
    intuitionistically_intro' (P := BIBase.later P) (Q := P) hstep
  have hlater :
      BIBase.later (BIBase.intuitionistically P) ⊢
        BIBase.intuitionistically (BIBase.later P) :=
    (later_intuitionistically (PROP := IProp GF) (P := P)).2
  have hloop :
      BIBase.later (BIBase.intuitionistically P) ⊢ BIBase.intuitionistically P :=
    hlater.trans hstep_box
  have hloeb :
      (True : IProp GF) ⊢ BIBase.intuitionistically P :=
    BILoeb.loeb_weak (PROP := IProp GF) (P := BIBase.intuitionistically P) hloop
  have hP : (True : IProp GF) ⊢ P :=
    hloeb.trans (intuitionistically_elim (PROP := IProp GF) (P := P))
  have hwand :
      (True : IProp GF) ⊢
        BIBase.wand
          (wp_s W s E (K e) Φ)
          (wp_s W s E e
            (fun v => wp_s W s E
              (K (Λ.of_val v)) Φ)) :=
    hP.trans (hPelim (E := E) (e := e) (Φ := Φ))
  have hframe :
      wp_s W s E (K e) Φ ⊢
        BIBase.sep
          (BIBase.wand
            (wp_s W s E (K e) Φ)
            (wp_s W s E e
              (fun v => wp_s W s E
                (K (Λ.of_val v)) Φ)))
          (wp_s W s E (K e) Φ) := by
    refine (true_sep_2 (PROP := IProp GF)
      (P := wp_s W s E (K e) Φ)).trans ?_
    exact sep_mono (PROP := IProp GF) hwand .rfl
  exact hframe.trans (wand_elim_l (PROP := IProp GF))

/-! ## Derived Rules -/

/-- Monotonicity in postcondition.
Coq: `wp_mono` in `weakestpre.v`. -/
theorem wp_mono (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ Ψ : Λ.val → IPropWsat GF M F)
    (h : ∀ v, Φ v ⊢ Ψ v) :
    wp_s W s E e Φ ⊢
      wp_s W s E e Ψ :=
  by
  -- use strong monotonicity with a pure postcondition transformer
  have hS : stuckness_le s s := by
    cases s <;> simp [stuckness_le]
  have hE : Subset E E := by
    intro i hi; exact hi
  have hmono :=
    wp_strong_mono (W := W) (s1 := s) (s2 := s) (E1 := E) (E2 := E) (e := e)
      (Φ := Φ) (Ψ := Ψ) hS hE
  have hpost :
      (True : IProp GF) ⊢ wp_post W E Φ Ψ := by
    -- lift the pointwise entailment under `fupd`
    refine forall_intro ?_; intro v
    have hΦ :
        Φ v ⊢ fupd' W E E (Ψ v) :=
      (h v).trans
        (fupd_intro (E := E) (P := Ψ v))
    exact (wand_rfl (P := Φ v)).trans
      (wand_mono_r (PROP := IProp GF) (h := hΦ))
  have hframe :
      wp_s W s E e Φ ⊢
        BIBase.sep
          (wp_post W E Φ Ψ)
          (wp_s W s E e Φ) := by
    -- add the postcondition transformer via `True`
    refine (true_sep_2 (PROP := IProp GF)
      (P := wp_s W s E e Φ)).trans ?_
    exact sep_mono hpost .rfl
  refine hframe.trans ?_
  refine (sep_mono (PROP := IProp GF)
    (P := wp_post W E Φ Ψ)
    (Q := wp_post W E Φ Ψ)
    (P' := wp_s W s E e Φ)
    (Q' := BIBase.wand
      (wp_post W E Φ Ψ)
      (wp_s W s E e Ψ)) .rfl hmono).trans ?_
  exact wand_elim_r (PROP := IProp GF)

/-- Frame rule (left).
Coq: `wp_frame_l` in `weakestpre.v`. -/
theorem wp_frame_l (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IPropWsat GF M F) (R : IProp GF) :
    BIBase.sep R (wp_s W s E e Φ) ⊢
    wp_s W s E e (fun v => BIBase.sep R (Φ v)) :=
  by
  -- use strong monotonicity and frame `R` into the postcondition
  have hS : stuckness_le s s := by
    cases s <;> simp [stuckness_le]
  have hE : Subset E E := by
    intro i hi; exact hi
  have hmono :=
    wp_strong_mono (W := W) (s1 := s) (s2 := s) (E1 := E) (E2 := E) (e := e)
      (Φ := Φ) (Ψ := fun v => BIBase.sep R (Φ v)) hS hE
  have hpost :
      R ⊢
        wp_post W E Φ
          (fun v => BIBase.sep R (Φ v)) := by
    -- build the transformer `Φ v -∗ |={E}=> R ∗ Φ v` from `R`
    refine forall_intro ?_; intro v
    refine wand_intro ?_
    exact fupd_intro (E := E)
      (P := BIBase.sep R (Φ v))
  have hframe :
      BIBase.sep R (wp_s W s E e Φ) ⊢
        BIBase.sep
          (wp_post W E Φ
            (fun v => BIBase.sep R (Φ v)))
          (wp_s W s E e Φ) :=
    sep_mono hpost .rfl
  refine hframe.trans ?_
  refine (sep_mono (PROP := IProp GF)
    (P := wp_post W E Φ
      (fun v => BIBase.sep R (Φ v)))
    (Q := wp_post W E Φ
      (fun v => BIBase.sep R (Φ v)))
    (P' := wp_s W s E e Φ)
    (Q' := BIBase.wand
      (wp_post W E Φ
        (fun v => BIBase.sep R (Φ v)))
      (wp_s W s E e
        (fun v => BIBase.sep R (Φ v)))) .rfl hmono).trans ?_
  exact wand_elim_r (PROP := IProp GF)

/-- Frame rule (right).
Coq: `wp_frame_r` in `weakestpre.v`. -/
theorem wp_frame_r (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IPropWsat GF M F) (R : IProp GF) :
    BIBase.sep (wp_s W s E e Φ) R ⊢
    wp_s W s E e (fun v => BIBase.sep (Φ v) R) :=
  by
  -- mirror the left frame rule using commutativity
  have hS : stuckness_le s s := by
    cases s <;> simp [stuckness_le]
  have hE : Subset E E := by
    intro i hi; exact hi
  have hmono :=
    wp_strong_mono (W := W) (s1 := s) (s2 := s) (E1 := E) (E2 := E) (e := e)
      (Φ := Φ) (Ψ := fun v => BIBase.sep (Φ v) R) hS hE
  have hpost :
      R ⊢
        wp_post W E Φ
          (fun v => BIBase.sep (Φ v) R) := by
    -- build the transformer `Φ v -∗ |={E}=> Φ v ∗ R` from `R`
    refine forall_intro ?_; intro v
    refine wand_intro ?_
    exact (sep_comm (PROP := IProp GF)
      (P := R) (Q := Φ v)).1.trans
        (fupd_intro (E := E)
          (P := BIBase.sep (Φ v) R))
  have hswap :
      BIBase.sep (wp_s W s E e Φ) R ⊢
        BIBase.sep R (wp_s W s E e Φ) :=
    (sep_comm (PROP := IProp GF)
      (P := wp_s W s E e Φ) (Q := R)).1
  have hframe :
      BIBase.sep R (wp_s W s E e Φ) ⊢
        BIBase.sep
          (wp_post W E Φ
            (fun v => BIBase.sep (Φ v) R))
          (wp_s W s E e Φ) :=
    sep_mono hpost .rfl
  refine hswap.trans ?_
  refine hframe.trans ?_
  refine (sep_mono (PROP := IProp GF)
    (P := wp_post W E Φ
      (fun v => BIBase.sep (Φ v) R))
    (Q := wp_post W E Φ
      (fun v => BIBase.sep (Φ v) R))
    (P' := wp_s W s E e Φ)
    (Q' := BIBase.wand
      (wp_post W E Φ
        (fun v => BIBase.sep (Φ v) R))
      (wp_s W s E e
        (fun v => BIBase.sep (Φ v) R))) .rfl hmono).trans ?_
  exact wand_elim_r (PROP := IProp GF)

/-- Wand rule: weaken postcondition via wand.
Coq: `wp_wand` in `weakestpre.v`. -/
theorem wp_wand (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ Ψ : Λ.val → IPropWsat GF M F) :
    wp_s W s E e Φ ⊢
    BIBase.wand
      (BIBase.forall fun v => BIBase.wand (Φ v) (Ψ v))
      (wp_s W s E e Ψ) :=
  by
  -- use strong monotonicity and lift the wand under `fupd`
  have hS : stuckness_le s s := by
    cases s <;> simp [stuckness_le]
  have hE : Subset E E := by
    intro i hi; exact hi
  have hmono :=
    wp_strong_mono (W := W) (s1 := s) (s2 := s) (E1 := E) (E2 := E) (e := e)
      (Φ := Φ) (Ψ := Ψ) hS hE
  refine wand_intro ?_
  -- turn the wand assumption into a `wp_post`, then eliminate
  have hpost :
      BIBase.forall (PROP := IProp GF) (fun v => BIBase.wand (Φ v) (Ψ v)) ⊢
        wp_post W E Φ Ψ := by
    refine forall_mono ?_; intro v
    refine (wand_mono_r (PROP := IProp GF)) ?_
    exact fupd_intro (E := E) (P := Ψ v)
  -- swap to `H1 ∗ wp_s W` before applying the transformer
  refine (sep_comm (PROP := IProp GF)
    (P := wp_s W s E e Φ)
    (Q := BIBase.forall (PROP := IProp GF) (fun v => BIBase.wand (Φ v) (Ψ v)))).1.trans ?_
  refine (sep_mono hpost .rfl).trans ?_
  refine (sep_mono (PROP := IProp GF)
    (P := wp_post W E Φ Ψ)
    (Q := wp_post W E Φ Ψ)
    (P' := wp_s W s E e Φ)
    (Q' := BIBase.wand
      (wp_post W E Φ Ψ)
      (wp_s W s E e Ψ)) .rfl hmono).trans ?_
  exact wand_elim_r (PROP := IProp GF)

/-- Atomic expression rule: open invariants around an atomic step.
Coq: `wp_atomic` in `weakestpre.v`. -/
theorem wp_atomic (s : Stuckness) (E1 E2 : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IPropWsat GF M F)
    [Atomic (match s with | .notStuck => .stronglyAtomic | .maybeStuck => .weaklyAtomic) e] :
    E1 = E2 →
    fupd' W E1 E2
      (wp_s W s E2 e
        (fun v => fupd' W E2 E1 (Φ v))) ⊢
    wp_s W s E1 e Φ :=
  by
  intro hE
  subst hE
  refine (fupd_wp (s := s) (E := E1) (e := e)
    (Φ := fun v => fupd' W E1 E1 (Φ v))).trans ?_
  exact wp_fupd (s := s) (E := E1) (e := e) (Φ := Φ)

end Iris.ProgramLogic
