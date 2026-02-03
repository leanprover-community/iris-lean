/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.ProgramLogic.WeakestPre

/-! # Lifting Lemmas

Reference: `iris/program_logic/lifting.v`

The lifting lemmas serve to lift the rules of the operational semantics
to the program logic. They connect the primitive step relation of the
language to the weakest precondition.

## Simplifications

This port omits later credit support. The `£ 1` and `step_fupdN`
infrastructure from the Coq version is dropped. The `num_laters_per_step`
is fixed to 0.

## Main Results

- `wp_lift_step_fupd` — lift a single step to WP (with fupd)
- `wp_lift_step` — lift a single step to WP
- `wp_lift_stuck` — stuck expression satisfies any WP at `maybeStuck`
- `wp_lift_pure_step_no_fork` — lift a pure, fork-free step
- `wp_lift_atomic_step_fupd` — lift an atomic step with fupd
- `wp_lift_atomic_step` — lift an atomic step
- `wp_lift_pure_det_step_no_fork` — lift a deterministic pure step
- `wp_lift_pure_stuck` — pure stuck expression
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
variable [inst : IrisGS Λ GF]
variable {W : WsatGS GF}

/-! ## FUpd Helpers -/

private noncomputable abbrev fupd' (W : WsatGS GF)
    (E1 E2 : Iris.Set Positive) (P : IPropWsat GF M F) : IPropWsat GF M F :=
  uPred_fupd (M := M) (F := F) W E1 E2 P

private abbrev maskEmpty : Iris.Set Positive := fun _ => False

private abbrev fork_post : Λ.val → IPropWsat GF M F :=
  (IrisGS.fork_post (Λ := Λ) (GF := GF) : Λ.val → IPropWsat GF M F)

private abbrev state_interp (σ : Λ.state) (ns : Nat)
    (κs : List Λ.observation) (nt : Nat) : IPropWsat GF M F :=
  (IrisGS.state_interp (Λ := Λ) (GF := GF) σ ns κs nt : IPropWsat GF M F)

private abbrev stuckness_pred (s : Stuckness) (e : Λ.expr) (σ : Λ.state) : Prop :=
  match s with
  | .notStuck => reducible e σ
  | .maybeStuck => True

/-! ## BI Abbreviations -/

private abbrev ipure (φ : Prop) : IPropWsat GF M F :=
  -- specialize `pure` to `IProp`
  BIBase.pure (PROP := IPropWsat GF M F) φ

private abbrev iwand (P Q : IPropWsat GF M F) : IPropWsat GF M F :=
  -- specialize wand to `IProp`
  BIBase.wand (PROP := IPropWsat GF M F) P Q

private abbrev isep (P Q : IPropWsat GF M F) : IPropWsat GF M F :=
  -- specialize `∗` to `IProp`
  BIBase.sep (PROP := IPropWsat GF M F) P Q

private abbrev ilater (P : IPropWsat GF M F) : IPropWsat GF M F :=
  -- specialize `▷` to `IProp`
  BIBase.later (PROP := IPropWsat GF M F) P

private abbrev iforall {A} (Φ : A → IPropWsat GF M F) : IPropWsat GF M F :=
  -- specialize `∀` to `IProp`
  BIBase.forall (PROP := IPropWsat GF M F) Φ

private noncomputable abbrev wp_fork (W : WsatGS GF)
    (s : Stuckness) (ef : Λ.expr) : IPropWsat GF M F :=
  -- fork postcondition in the universal mask
  wp (W := W) s Iris.Set.univ ef (fork_post (M := M) (F := F))

private noncomputable abbrev fork_posts (W : WsatGS GF)
    (s : Stuckness) (efs : List Λ.expr) : IPropWsat GF M F :=
  -- combine forked thread WPs
  big_sepL (fun _ ef => wp_fork W s ef) efs

private noncomputable abbrev step_post W (W : WsatGS GF) (s : Stuckness) (E : Iris.Set Positive)
    (Φ : Λ.val → IPropWsat GF M F) (σ2 : Λ.state)
    (ns : Nat) (κs : List Λ.observation) (nt : Nat)
    (e2 : Λ.expr) (efs : List Λ.expr) : IPropWsat GF M F :=
  -- postcondition after a single step with forks
  ilater
    (isep (state_interp (M := M) (F := F) σ2 (ns + 1) κs (efs.length + nt))
      (isep (wp (W := W) s E e2 Φ)
        (fork_posts W s efs)))

private abbrev pure_step_cont_pred W (W : WsatGS GF) (s : Stuckness) (E : Iris.Set Positive)
    (e1 : Λ.expr) (Φ : Λ.val → IPropWsat GF M F) : IPropWsat GF M F :=
  -- standard pure-step continuation predicate
  iforall fun κ : List Λ.observation =>
    iforall fun e2 : Λ.expr =>
      iforall fun efs : List Λ.expr =>
        iforall fun σ : Λ.state =>
          iwand (ipure (Λ.prim_step e1 σ κ e2 σ efs))
            (wp (W := W) s E e2 Φ)

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Helper: frame a wand through a fancy update. -/
private theorem fupd_wand_r (E1 E2 : Iris.Set Positive) (P Q : IPropWsat GF M F) :
    BIBase.sep (fupd' W E1 E2 P) (BIBase.wand P Q) ⊢
      fupd' W E1 E2 Q :=
  by
    -- frame the wand inside, then eliminate it under `Iris.BaseLogic.fupd_mono`
    refine (Iris.BaseLogic.fupd_frame_r (W := W)
      (M := M) (F := F) (E1 := E1) (E2 := E2) (P := P)
      (Q := BIBase.wand P Q)).trans ?_
    exact Iris.BaseLogic.fupd_mono (W := W)
      (M := M) (F := F) (E1 := E1) (E2 := E2)
      (P := BIBase.sep P (BIBase.wand P Q)) (Q := Q)
      (wand_elim_r (P := P) (Q := Q))

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Helper: open a mask using a closing wand.
Coq: `fupd_mask_intro` (proofmode lemma). -/
private theorem fupd_mask_intro (E1 E2 : Iris.Set Positive) (h : Subset E2 E1)
    (P : IPropWsat GF M F) :
    BIBase.wand (fupd' W E2 E1 (BIBase.emp : IPropWsat GF M F)) P ⊢
      fupd' W E1 E2 P :=
  by
    -- open the mask using `Iris.BaseLogic.fupd_mask_subseteq`, then apply the wand inside
    have hopen :
        (True : IPropWsat GF M F) ⊢
          fupd' W E1 E2
            (fupd' W E2 E1 (BIBase.emp : IPropWsat GF M F)) :=
      Iris.BaseLogic.fupd_mask_subseteq (W := W)
        (M := M) (F := F) (E1 := E1) (E2 := E2) h
    refine (true_sep_2 (PROP := IPropWsat GF M F)
      (P := BIBase.wand (fupd' W E2 E1 (BIBase.emp : IPropWsat GF M F)) P)).trans ?_
    refine (sep_mono hopen .rfl).trans ?_
    exact fupd_wand_r (E1 := E1) (E2 := E2)
      (P := fupd' W E2 E1 (BIBase.emp : IPropWsat GF M F)) (Q := P)

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
private theorem fupd_close_emp (E : Iris.Set Positive) (P : IPropWsat GF M F) :
    BIBase.sep (fupd' W maskEmpty E (BIBase.emp : IPropWsat GF M F)) P ⊢
      fupd' W maskEmpty E P :=
  by
    -- frame `P` under the update, then drop `emp`
    refine (Iris.BaseLogic.fupd_frame_r (W := W)
      (M := M) (F := F) (E1 := maskEmpty) (E2 := E) (P := (BIBase.emp : IPropWsat GF M F))
      (Q := P)).trans ?_
    exact Iris.BaseLogic.fupd_mono (W := W)
      (M := M) (F := F) (E1 := maskEmpty) (E2 := E)
      (P := BIBase.sep (BIBase.emp : IPropWsat GF M F) P) (Q := P) (emp_sep (P := P)).1

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
private theorem fupd_intro (E : Iris.Set Positive) (P : IPropWsat GF M F) :
    P ⊢ fupd' W E E P :=
  by
    -- introduce a nested update, then collapse it
    have hsubset : Subset E E := by
      intro _ h; exact h
    have hmask :=
      Iris.BaseLogic.fupd_intro_mask (W := W)
        (M := M) (F := F) (E1 := E) (E2 := E) hsubset (P := P)
    exact hmask.trans <|
      Iris.BaseLogic.fupd_trans (W := W)
        (M := M) (F := F) (E1 := E) (E2 := E) (E3 := E) (P := P)

/-! ## Pure Helpers -/

omit [DecidableEq Positive] in
private theorem pure_step_val_none [Inhabited Λ.state]
    (s : Stuckness) (e1 : Λ.expr)
    (hsafe : ∀ σ1, match s with
      | .notStuck => reducible e1 σ1
      | .maybeStuck => Λ.to_val e1 = none) :
    Λ.to_val e1 = none :=
  by
    -- pick a concrete state and extract non-valueness
    cases s with
    | notStuck =>
        have hred := hsafe (default : Λ.state)
        exact reducible_not_val (Λ := Λ) e1 _ hred
    | maybeStuck =>
        exact hsafe (default : Λ.state)

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
private theorem pure_step_wand {s : Stuckness} {E : Iris.Set Positive}
    {Φ : Λ.val → IPropWsat GF M F} {e1 : Λ.expr}
    (κ : List Λ.observation) (e2 : Λ.expr) (efs : List Λ.expr) (σ : Λ.state) :
    pure_step_cont_pred W s E e1 Φ ⊢
      iwand (ipure (Λ.prim_step e1 σ κ e2 σ efs))
      (wp (W := W) s E e2 Φ) :=
  by
    -- specialize the nested `∀` binders
    refine (forall_elim (PROP := IPropWsat GF M F)
      (Ψ := fun κ => iforall fun e2 : Λ.expr => iforall fun efs : List Λ.expr =>
        iforall fun σ : Λ.state =>
          iwand (ipure (Λ.prim_step e1 σ κ e2 σ efs))
            (wp (W := W) s E e2 Φ)) κ).trans ?_
    refine (forall_elim (PROP := IPropWsat GF M F)
      (Ψ := fun e2 => iforall fun efs : List Λ.expr => iforall fun σ : Λ.state =>
        iwand (ipure (Λ.prim_step e1 σ κ e2 σ efs))
          (wp (W := W) s E e2 Φ)) e2).trans ?_
    refine (forall_elim (PROP := IPropWsat GF M F)
      (Ψ := fun efs => iforall fun σ : Λ.state =>
        iwand (ipure (Λ.prim_step e1 σ κ e2 σ efs))
          (wp (W := W) s E e2 Φ)) efs).trans ?_
    exact forall_elim (PROP := IPropWsat GF M F)
      (Ψ := fun σ => iwand (ipure (Λ.prim_step e1 σ κ e2 σ efs))
        (wp (W := W) s E e2 Φ)) σ

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
private theorem later_wp_of_step {s : Stuckness} {E : Iris.Set Positive}
    {Φ : Λ.val → IPropWsat GF M F} {e1 : Λ.expr}
    (κ : List Λ.observation) (e2 : Λ.expr) (efs : List Λ.expr) (σ : Λ.state) :
    isep (ilater (pure_step_cont_pred W s E e1 Φ))
      (ipure (Λ.prim_step e1 σ κ e2 σ efs)) ⊢
      ilater (wp (W := W) s E e2 Φ) :=
  by
    -- push the wand under `▷` and apply it to the stepped proof
    have hwand :
        ilater (pure_step_cont_pred W s E e1 Φ) ⊢
          iwand (ilater (ipure (Λ.prim_step e1 σ κ e2 σ efs)))
            (ilater (wp (W := W) s E e2 Φ)) := by
      refine (later_mono (PROP := IPropWsat GF M F)
        (pure_step_wand (s := s) (E := E) (e1 := e1)
          (Φ := Φ) (κ := κ) (e2 := e2) (efs := efs) (σ := σ))).trans ?_
      exact later_wand (PROP := IPropWsat GF M F)
        (P := ipure (Λ.prim_step e1 σ κ e2 σ efs))
        (Q := wp (W := W) s E e2 Φ)
    have hstep : ipure (Λ.prim_step e1 σ κ e2 σ efs) ⊢
        ilater (ipure (Λ.prim_step e1 σ κ e2 σ efs)) :=
      later_intro (PROP := IPropWsat GF M F)
    refine ((sep_comm (P := ilater (pure_step_cont_pred W s E e1 Φ))
      (Q := ipure (Λ.prim_step e1 σ κ e2 σ efs))).1).trans ?_
    refine (sep_mono hstep hwand).trans ?_
    exact wand_elim_r (PROP := IPropWsat GF M F)

omit [DecidableEq Positive]
  [ElemG GF (COFE.constOF CoPsetDisj)]
  [ElemG GF (COFE.constOF GSetDisj)] in
private theorem later_state_interp_step
    (σ : Λ.state) (ns : Nat) (κ : List Λ.observation)
    (κs : List Λ.observation) (nt : Nat) (hκ : κ = []) :
    (IrisGS.state_interp (Λ := Λ) (GF := GF) σ ns (κ ++ κs) nt : IPropWsat GF M F) ⊢
      ilater (IrisGS.state_interp (Λ := Λ) (GF := GF) σ (ns + 1) κs nt) :=
  by
    -- rewrite the trace and apply monotonicity under `▷`
    subst hκ
    exact (IrisGS.state_interp_mono (Λ := Λ) (GF := GF)
      (σ := σ) (ns := ns) (κs := κs) (nt := nt)).trans
      (later_intro (PROP := IPropWsat GF M F))

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
private theorem pure_step_later {s : Stuckness} {E : Iris.Set Positive}
    {Φ : Λ.val → IPropWsat GF M F} {e1 : Λ.expr}
    (σ : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt : Nat) (e2 : Λ.expr) :
    isep
        (isep (ilater (pure_step_cont_pred W s E e1 Φ))
          (ipure (Λ.prim_step e1 σ [] e2 σ [])))
        (state_interp σ ns κs nt) ⊢
      ilater
        (isep (state_interp σ (ns + 1) κs nt)
          (wp (W := W) s E e2 Φ)) :=
  by
    -- combine the stepped WP with the monotone state interpretation
    have hwp :=
      later_wp_of_step (s := s) (E := E) (e1 := e1) (Φ := Φ)
        (κ := []) (e2 := e2) (efs := []) (σ := σ)
    have hstate :=
      later_state_interp_step (GF := GF) (σ := σ) (ns := ns)
        (κ := []) (κs := κs) (nt := nt) rfl
    have hsep : isep
        (isep (ilater (pure_step_cont_pred W s E e1 Φ))
          (ipure (Λ.prim_step e1 σ [] e2 σ [])))
        (state_interp σ ns κs nt) ⊢
        isep (ilater (wp (W := W) s E e2 Φ))
          (ilater (state_interp σ (ns + 1) κs nt)) :=
      sep_mono hwp hstate
    refine hsep.trans ?_
    refine ((sep_comm (P := ilater (wp (W := W) s E e2 Φ))
      (Q := ilater (state_interp σ (ns + 1) κs nt))).1).trans ?_
    exact (later_sep (PROP := IPropWsat GF M F)
      (P := state_interp σ (ns + 1) κs nt)
      (Q := wp (W := W) s E e2 Φ)).2

omit [DecidableEq Positive]
  [ElemG GF (COFE.constOF CoPsetDisj)]
  [ElemG GF (COFE.constOF GSetDisj)]
  [IrisGS Λ GF] in
private theorem pure_step_stuckness (s : Stuckness) (e1 : Λ.expr)
    (hsafe : ∀ σ1, match s with
      | .notStuck => reducible e1 σ1
      | .maybeStuck => Λ.to_val e1 = none)
    (σ : Λ.state) :
    (True : IPropWsat GF M F) ⊢ ipure (stuckness_pred s e1 σ) :=
  by
    -- discharge the stuckness predicate using `hsafe`
    cases s with
    | notStuck =>
        -- stuckness reduces to reducibility in the not-stuck case
        exact pure_intro (hsafe σ)
    | maybeStuck =>
        exact pure_intro trivial

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
private theorem later_add_emp {s : Stuckness} {E : Iris.Set Positive}
    {Φ : Λ.val → IPropWsat GF M F} (σ : Λ.state) (ns : Nat)
    (κs : List Λ.observation) (nt : Nat) (e2 : Λ.expr) :
    ilater (isep (state_interp σ (ns + 1) κs nt)
        (wp (W := W) s E e2 Φ)) ⊢
      ilater (isep (state_interp σ (ns + 1) κs nt)
        (isep (wp (W := W) s E e2 Φ) (BIBase.emp : IPropWsat GF M F))) :=
  by
    -- add `emp` under `▷` using `sep_emp`
    have hemp :
        isep (state_interp σ (ns + 1) κs nt)
            (wp (W := W) s E e2 Φ) ⊢
          isep (state_interp σ (ns + 1) κs nt)
            (isep (wp (W := W) s E e2 Φ) (BIBase.emp : IPropWsat GF M F)) :=
      sep_mono .rfl
        (sep_emp (PROP := IPropWsat GF M F) (P := wp (W := W) s E e2 Φ)).2
    exact later_mono (PROP := IPropWsat GF M F) hemp

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
private theorem fupd_later_add_emp {s : Stuckness} {E : Iris.Set Positive}
    {Φ : Λ.val → IPropWsat GF M F} (σ : Λ.state) (ns : Nat)
    (κs : List Λ.observation) (nt : Nat) (e2 : Λ.expr) :
    fupd' W maskEmpty E
        (ilater (isep (state_interp σ (ns + 1) κs nt)
          (wp (W := W) s E e2 Φ))) ⊢
      fupd' W maskEmpty E
        (ilater (isep (state_interp σ (ns + 1) κs nt)
          (isep (wp (W := W) s E e2 Φ) (BIBase.emp : IPropWsat GF M F)))) :=
  by
    -- lift `later_add_emp` through the fancy update
    exact Iris.BaseLogic.fupd_mono (W := W)
      (M := M) (F := F) (E1 := maskEmpty) (E2 := E)
      (P := ilater (isep (state_interp σ (ns + 1) κs nt)
        (wp (W := W) s E e2 Φ)))
      (Q := ilater (isep (state_interp σ (ns + 1) κs nt)
        (isep (wp (W := W) s E e2 Φ) (BIBase.emp : IPropWsat GF M F))))
      (later_add_emp (s := s) (E := E) (Φ := Φ)
        (σ := σ) (ns := ns) (κs := κs) (nt := nt) (e2 := e2))

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
private theorem pure_step_cont_close {s : Stuckness} {E : Iris.Set Positive}
    {Φ : Λ.val → IPropWsat GF M F} {e1 : Λ.expr}
    (σ : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt : Nat) (e2 : Λ.expr) :
    isep
        (isep (ilater (pure_step_cont_pred W s E e1 Φ))
          (isep (state_interp σ ns κs nt)
            (fupd' W maskEmpty E (BIBase.emp : IPropWsat GF M F))))
        (ipure (Λ.prim_step e1 σ [] e2 σ [])) ⊢
      fupd' W maskEmpty E
        (ilater
          (isep (state_interp σ (ns + 1) κs nt)
            (isep (wp (W := W) s E e2 Φ)
              (BIBase.emp : IPropWsat GF M F)))) :=
  by
    -- reorder, apply the later postcondition, then close the mask
    refine ((sep_right_comm (P := ilater (pure_step_cont_pred W s E e1 Φ))
      (Q := isep (state_interp σ ns κs nt)
        (fupd' W maskEmpty E (BIBase.emp : IPropWsat GF M F)))
      (R := ipure (Λ.prim_step e1 σ [] e2 σ []))).1).trans ?_
    refine (sep_assoc (P := isep (ilater (pure_step_cont_pred W s E e1 Φ))
      (ipure (Λ.prim_step e1 σ [] e2 σ [])))
      (Q := state_interp σ ns κs nt)
      (R := fupd' W maskEmpty E (BIBase.emp : IPropWsat GF M F))).2.trans ?_
    refine (sep_mono (pure_step_later (s := s) (E := E) (e1 := e1)
      (Φ := Φ) (σ := σ) (ns := ns) (κs := κs) (nt := nt) (e2 := e2)) .rfl).trans ?_
    refine ((sep_comm (P := ilater
      (isep (state_interp σ (ns + 1) κs nt)
        (wp (W := W) s E e2 Φ)))
      (Q := fupd' W maskEmpty E (BIBase.emp : IPropWsat GF M F))).1).trans ?_
    refine (fupd_close_emp (E := E) (P := ilater
      (isep (state_interp σ (ns + 1) κs nt)
        (wp (W := W) s E e2 Φ)))).trans ?_
    exact fupd_later_add_emp (s := s) (E := E) (Φ := Φ)
      (σ := σ) (ns := ns) (κs := κs) (nt := nt) (e2 := e2)

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
private theorem pure_step_cont {s : Stuckness} {E : Iris.Set Positive}
    {Φ : Λ.val → IPropWsat GF M F} {e1 : Λ.expr}
    (hstep : ∀ κ σ1 e2 σ2 efs, Λ.prim_step e1 σ1 κ e2 σ2 efs →
      κ = [] ∧ σ2 = σ1 ∧ efs = [])
    (σ : Λ.state) (ns : Nat) (κ : List Λ.observation)
    (κs : List Λ.observation) (nt : Nat) :
    isep (ilater (pure_step_cont_pred W s E e1 Φ))
      (isep (state_interp σ ns (κ ++ κs) nt)
        (fupd' W maskEmpty E (BIBase.emp : IPropWsat GF M F))) ⊢
      iforall fun e2 : Λ.expr =>
        iforall fun σ2 : Λ.state =>
          iforall fun efs : List Λ.expr =>
            iwand (ipure (Λ.prim_step e1 σ κ e2 σ2 efs))
              (fupd' W maskEmpty E
                (step_post W (s := s) (E := E) (Φ := Φ)
                  (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt) (e2 := e2) (efs := efs))) :=
  by
    -- build the continuation by eliminating the pure step
    refine forall_intro ?_; intro e2
    refine forall_intro ?_; intro σ2
    refine forall_intro ?_; intro efs
    refine wand_intro ?_
    refine (pure_elim (φ := Λ.prim_step e1 σ κ e2 σ2 efs)
      (Q := isep (isep
        (ilater (pure_step_cont_pred W s E e1 Φ))
        (isep (state_interp σ ns (κ ++ κs) nt)
          (fupd' W maskEmpty E (BIBase.emp : IPropWsat GF M F))))
        (ipure (Λ.prim_step e1 σ κ e2 σ2 efs))) ?_ ?_)
    · -- expose the pure step from the frame
      exact sep_elim_r
    intro hprim
    rcases hstep κ σ e2 σ2 efs hprim with ⟨hκ, hσ, hfs⟩
    subst hκ; subst hσ; subst hfs
    -- simplify the fork postcondition for the empty fork list
    simp [step_post, fork_posts]
    exact pure_step_cont_close
      (s := s) (E := E) (e1 := e1) (Φ := Φ)
      (σ := σ2) (ns := ns) (κs := κs) (nt := nt) (e2 := e2)

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
private theorem pure_step_pre_wand {s : Stuckness} {E : Iris.Set Positive}
    {Φ : Λ.val → IPropWsat GF M F} {e1 : Λ.expr}
    (hsafe : ∀ σ1, match s with
      | .notStuck => reducible e1 σ1
      | .maybeStuck => Λ.to_val e1 = none)
    (hstep : ∀ κ σ1 e2 σ2 efs, Λ.prim_step e1 σ1 κ e2 σ2 efs →
      κ = [] ∧ σ2 = σ1 ∧ efs = [])
    (σ : Λ.state) (ns : Nat) (κ : List Λ.observation)
    (κs : List Λ.observation) (nt : Nat) :
    isep (ilater (pure_step_cont_pred W s E e1 Φ))
      (isep (state_interp σ ns (κ ++ κs) nt)
        (fupd' W maskEmpty E (BIBase.emp : IPropWsat GF M F))) ⊢
      isep (ipure (stuckness_pred s e1 σ))
        (iforall fun e2 : Λ.expr =>
          iforall fun σ2 : Λ.state =>
            iforall fun efs : List Λ.expr =>
              iwand (ipure (Λ.prim_step e1 σ κ e2 σ2 efs))
                (fupd' W maskEmpty E
                  (step_post W (s := s) (E := E) (Φ := Φ)
                    (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt) (e2 := e2) (efs := efs)))) :=
  by
    -- add the pure stuckness fact and reuse the step continuation
    -- specialize the stuckness and step continuations to this language instance
    have hpure := pure_step_stuckness (Λ := Λ) (GF := GF) (s := s) (e1 := e1)
      hsafe (σ := σ)
    have hcont :=
      pure_step_cont
        (s := s) (E := E) (e1 := e1) (Φ := Φ)
        hstep (σ := σ) (ns := ns) (κ := κ) (κs := κs) (nt := nt)
    refine (true_sep_2 (PROP := IPropWsat GF M F)
      (P := isep
        (ilater (pure_step_cont_pred W s E e1 Φ))
        (isep (state_interp σ ns (κ ++ κs) nt)
          (fupd' W maskEmpty E (BIBase.emp : IPropWsat GF M F))))).trans ?_
    exact sep_mono hpure hcont

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
private theorem pure_step_pre {s : Stuckness} {E : Iris.Set Positive}
    {Φ : Λ.val → IPropWsat GF M F} {e1 : Λ.expr}
    (hsafe : ∀ σ1, match s with
      | .notStuck => reducible e1 σ1
      | .maybeStuck => Λ.to_val e1 = none)
    (hstep : ∀ κ σ1 e2 σ2 efs, Λ.prim_step e1 σ1 κ e2 σ2 efs →
      κ = [] ∧ σ2 = σ1 ∧ efs = [])
    (σ : Λ.state) (ns : Nat) (κ : List Λ.observation)
    (κs : List Λ.observation) (nt : Nat) :
    ilater (pure_step_cont_pred W s E e1 Φ) ⊢
      iwand (state_interp σ ns (κ ++ κs) nt)
        (fupd' W E maskEmpty
          (isep (ipure (stuckness_pred s e1 σ))
            (iforall fun e2 : Λ.expr =>
              iforall fun σ2 : Λ.state =>
                iforall fun efs : List Λ.expr =>
                  iwand (ipure (Λ.prim_step e1 σ κ e2 σ2 efs))
                    (fupd' W maskEmpty E
                      (step_post W (s := s) (E := E) (Φ := Φ)
                        (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt) (e2 := e2)
                        (efs := efs)))))) :=
  by
    -- open the mask and use the pure-step continuation
    have hsubset : Subset maskEmpty E := by
      intro _ h; exact h.elim
    refine wand_intro ?_
    let Q : IPropWsat GF M F :=
      iforall fun e2 : Λ.expr =>
        iforall fun σ2 : Λ.state =>
          iforall fun efs : List Λ.expr =>
            iwand (ipure (Λ.prim_step e1 σ κ e2 σ2 efs))
              (fupd' W maskEmpty E
                (step_post W (s := s) (E := E) (Φ := Φ)
                  (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt) (e2 := e2) (efs := efs)))
    have hmask :=
      fupd_mask_intro
        (E1 := E) (E2 := maskEmpty) hsubset
        (P := isep (ipure (stuckness_pred s e1 σ)) Q)
    have hwand :
        isep (ilater (pure_step_cont_pred W s E e1 Φ))
            (state_interp σ ns (κ ++ κs) nt) ⊢
          iwand (fupd' W maskEmpty E (BIBase.emp : IPropWsat GF M F))
            (isep (ipure (stuckness_pred s e1 σ)) Q) := by
      refine wand_intro ?_
      -- reassociate to match `pure_step_pre_wand`'s expected framing
      refine (sep_assoc (P := ilater (pure_step_cont_pred W s E e1 Φ))
        (Q := state_interp σ ns (κ ++ κs) nt)
        (R := fupd' W maskEmpty E (BIBase.emp : IPropWsat GF M F))).1.trans ?_
      exact pure_step_pre_wand
        (s := s) (E := E) (e1 := e1) (Φ := Φ)
        hsafe hstep (σ := σ) (ns := ns) (κ := κ) (κs := κs) (nt := nt)
    exact hwand.trans hmask

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
private theorem pure_step_wp_pre {s : Stuckness} {E : Iris.Set Positive}
    {Φ : Λ.val → IPropWsat GF M F} {e1 : Λ.expr}
    (hsafe : ∀ σ1, match s with
      | .notStuck => reducible e1 σ1
      | .maybeStuck => Λ.to_val e1 = none)
    (hstep : ∀ κ σ1 e2 σ2 efs, Λ.prim_step e1 σ1 κ e2 σ2 efs →
      κ = [] ∧ σ2 = σ1 ∧ efs = []) :
    (hv : Λ.to_val e1 = none) →
    ilater (pure_step_cont_pred W s E e1 Φ) ⊢
      wp_pre (W := W) s (wp (W := W) s) E e1 Φ :=
  by
    -- unfold the non-value branch and assemble the binders
    intro hv
    -- unfold the WP precondition for the non-value case
    simp [wp_pre, hv]
    refine forall_intro ?_; intro σ
    refine forall_intro ?_; intro ns
    refine forall_intro ?_; intro κ
    refine forall_intro ?_; intro κs
    refine forall_intro ?_; intro nt
    exact pure_step_pre (s := s) (E := E) (e1 := e1) (Φ := Φ)
      hsafe hstep (σ := σ) (ns := ns) (κ := κ) (κs := κs) (nt := nt)

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
private theorem pure_det_to_cont {s : Stuckness} {E : Iris.Set Positive}
    {Φ : Λ.val → IPropWsat GF M F} {e1 e2 : Λ.expr}
    (hstep : ∀ σ1 κ e2' σ2 efs', Λ.prim_step e1 σ1 κ e2' σ2 efs' →
      κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) :
    wp (W := W) s E e2 Φ ⊢
      iforall fun κ : List Λ.observation =>
        iforall fun e2' : Λ.expr =>
          iforall fun efs : List Λ.expr =>
            iforall fun σ : Λ.state =>
              iwand (ipure (Λ.prim_step e1 σ κ e2' σ efs))
                (wp (W := W) s E e2' Φ) :=
  by
    -- build the deterministic continuation by rewriting `e2'`
    refine forall_intro ?_; intro κ
    refine forall_intro ?_; intro e2'
    refine forall_intro ?_; intro efs
    refine forall_intro ?_; intro σ
    refine wand_intro ?_
    refine (pure_elim (φ := Λ.prim_step e1 σ κ e2' σ efs)
      (Q := BIBase.sep (wp (W := W) s E e2 Φ)
        (BIBase.pure (Λ.prim_step e1 σ κ e2' σ efs))) ?_ ?_)
    · -- expose the pure step from the frame
      exact sep_elim_r
    intro hprim
    rcases hstep σ κ e2' σ efs hprim with ⟨_, _, he2, _⟩
    subst he2
    exact sep_elim_l

omit [DecidableEq Positive]
  [ElemG GF (COFE.constOF CoPsetDisj)]
  [ElemG GF (COFE.constOF GSetDisj)]
  [IrisGS Λ GF] in
private theorem prim_step_elim (e : Λ.expr) (σ : Λ.state) (κ : List Λ.observation)
    (e2 : Λ.expr) (σ2 : Λ.state) (efs : List Λ.expr) (hstuck : stuck e σ)
    (P : IPropWsat GF M F) :
    BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs) ⊢ P :=
  by
    -- eliminate a primitive step using irreducibility from stuckness
    refine pure_elim' ?_
    intro hstep
    exact False.elim (hstuck.2 κ e2 σ2 efs hstep)

omit [DecidableEq Positive]
  [ElemG GF (COFE.constOF CoPsetDisj)]
  [ElemG GF (COFE.constOF GSetDisj)] in
private theorem pure_true_sep (Q : IPropWsat GF M F) (hQ : (True : IPropWsat GF M F) ⊢ Q) :
    ipure True ⊢ isep (ipure True) Q :=
  by
    -- turn `pure True` into `True`, then build the separating conjunction
    have hpt : ipure True ⊢ (True : IPropWsat GF M F) := (pure_true trivial).1
    have hQ' : ipure True ⊢ Q := hpt.trans hQ
    have hsep : ipure True ⊢ (True : IPropWsat GF M F) ∗ Q :=
      hQ'.trans (true_sep_2 (PROP := IPropWsat GF M F) (P := Q))
    have htp : (True : IPropWsat GF M F) ⊢ ipure True := (pure_true trivial).2
    exact hsep.trans (sep_mono htp .rfl)

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
private theorem stuck_cont (E : Iris.Set Positive) (Φ : Λ.val → IPropWsat GF M F)
    (e : Λ.expr) (σ : Λ.state) (ns nt : Nat)
    (κ : List Λ.observation) (κs : List Λ.observation)
    (hstuck : stuck e σ) :
    (True : IPropWsat GF M F) ⊢
      iforall fun e2 : Λ.expr =>
        iforall fun σ2 : Λ.state =>
          iforall fun efs : List Λ.expr =>
            iwand (ipure (Λ.prim_step e σ κ e2 σ2 efs))
              (fupd' W maskEmpty E
                (step_post W (s := .maybeStuck) (E := E) (Φ := Φ)
                  (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt) (e2 := e2) (efs := efs))) :=
  by
    -- build the continuation by eliminating impossible primitive steps
    refine forall_intro (PROP := IPropWsat GF M F) ?_; intro e2
    refine forall_intro (PROP := IPropWsat GF M F) ?_; intro σ2
    refine forall_intro (PROP := IPropWsat GF M F) ?_; intro efs
    refine wand_intro ?_
    refine (sep_elim_r (PROP := IPropWsat GF M F)
      (P := ipure True) (Q := BIBase.pure (Λ.prim_step e σ κ e2 σ2 efs))).trans ?_
    let P : IPropWsat GF M F :=
      fupd' W maskEmpty E
        (step_post W (s := .maybeStuck) (E := E) (Φ := Φ)
          (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt) (e2 := e2) (efs := efs))
    exact prim_step_elim (Λ := Λ) (e := e) (σ := σ) (κ := κ)
      (e2 := e2) (σ2 := σ2) (efs := efs) hstuck (P := P)

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
private theorem wp_pre_stuck (E : Iris.Set Positive)
    (Φ : Λ.val → IPropWsat GF M F) (e : Λ.expr)
    (hv : Λ.to_val e = none) (hstuck : ∀ σ, stuck e σ) :
    ipure True ⊢
      wp_pre (W := W) .maybeStuck (wp (W := W) .maybeStuck) E e Φ :=
  by
    -- unfold the non-value branch and build the continuation from stuckness
    have hsubset : Subset maskEmpty E := by intro _ h; exact h.elim
    -- unfold the non-value branch of `wp_pre`
    simp [wp_pre, hv]
    refine forall_intro (PROP := IPropWsat GF M F) ?_; intro σ
    refine forall_intro (PROP := IPropWsat GF M F) ?_; intro ns
    refine forall_intro (PROP := IPropWsat GF M F) ?_; intro κ
    refine forall_intro (PROP := IPropWsat GF M F) ?_; intro κs
    refine forall_intro (PROP := IPropWsat GF M F) ?_; intro nt
    refine wand_intro ?_
    let Q : IPropWsat GF M F :=
      iforall fun e2 : Λ.expr =>
        iforall fun σ2 : Λ.state =>
          iforall fun efs : List Λ.expr =>
            iwand (ipure (Λ.prim_step e σ κ e2 σ2 efs))
              (fupd' W maskEmpty E
                (step_post W (s := .maybeStuck) (E := E) (Φ := Φ)
                  (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt) (e2 := e2) (efs := efs)))
    have hQ : (True : IPropWsat GF M F) ⊢ Q := by
      simpa [Q] using stuck_cont (E := E) (Φ := Φ)
        (e := e) (σ := σ) (ns := ns) (nt := nt) (κ := κ) (κs := κs) (hstuck := hstuck σ)
    have hsep : ipure True ⊢ isep (ipure True) Q :=
      pure_true_sep (Q := Q) hQ
    have hmask : ipure True ⊢ fupd' W E maskEmpty
        (isep (ipure True) Q) := by
      -- build the wand required to open the mask, then apply `fupd_mask_intro`
      have hwand : ipure True ⊢
          BIBase.wand
            (fupd' W maskEmpty E (BIBase.emp : IPropWsat GF M F))
            (isep (ipure True) Q) := by
        refine wand_intro ?_
        exact (sep_elim_l (P := ipure True)
          (Q := fupd' W maskEmpty E (BIBase.emp : IPropWsat GF M F))).trans hsep
      exact hwand.trans
        (fupd_mask_intro (E1 := E) (E2 := maskEmpty)
          hsubset (P := isep (ipure True) Q))
    exact (sep_elim_l (P := ipure True)
      (Q := state_interp σ ns (κ ++ κs) nt)).trans hmask

/-! ## Core Lifting Lemmas -/

/-- Lift a single step to WP with fupd. Unfolds the WP fixpoint one step.
The hypothesis must provide state interpretation update and recursive WP
for the continuation, with a `▷` guarding the post-step obligation.
Coq: `wp_lift_step_fupd` in `lifting.v`. -/
noncomputable def wp_lift_step_fupd (s : Stuckness) (E : Iris.Set Positive)
    (Φ : Λ.val → IPropWsat GF M F) (e1 : Λ.expr)
    (hv : Λ.to_val e1 = none) :
    wp_pre (W := W) s (wp (W := W) s) E e1 Φ ⊢ wp (W := W) s E e1 Φ :=
  by
    -- unfold the fixpoint once and use `hv` to select the step case
    simpa [wp_pre, hv] using
      (wp_unfold (W := W)
        (s := s) (E := E) (e := e1) (Φ := Φ)).2

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Lift a single step to WP. Like `wp_lift_step_fupd` but with `▷`
before the continuation rather than fupd.
Coq: `wp_lift_step` in `lifting.v`. -/
theorem wp_lift_step (s : Stuckness) (E : Iris.Set Positive)
    (Φ : Λ.val → IPropWsat GF M F) (e1 : Λ.expr)
    (hv : Λ.to_val e1 = none) :
    wp_pre (W := W) s (wp (W := W) s) E e1 Φ ⊢ wp (W := W) s E e1 Φ :=
  by
    -- the non-fupd variant is definitionally the same in this port
    simpa using wp_lift_step_fupd (s := s) (E := E) (Φ := Φ) (e1 := e1) hv

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Lift a stuck expression: if `e` is stuck in every reachable state,
then `WP e @ E ?{{ Φ }}` holds.
Coq: `wp_lift_stuck` in `lifting.v`. -/
theorem wp_lift_stuck (_s : Stuckness) (E : Iris.Set Positive)
    (Φ : Λ.val → IPropWsat GF M F) (e : Λ.expr)
    (hv : Λ.to_val e = none)
    (hstuck : ∀ σ, stuck e σ) :
    ipure True ⊢ wp (W := W) .maybeStuck E e Φ :=
  by
    -- fold the constructed `wp_pre` back into `wp`
    exact (wp_pre_stuck (E := E) (Φ := Φ)
      (e := e) hv hstuck).trans
      (wp_lift_step_fupd (s := .maybeStuck) (E := E) (Φ := Φ) (e1 := e) hv)

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Lift a pure, fork-free step.
Coq: `wp_lift_pure_step_no_fork` in `lifting.v`. -/
theorem wp_lift_pure_step_no_fork [Inhabited Λ.state]
    (s : Stuckness) (E : Iris.Set Positive)
    (Φ : Λ.val → IPropWsat GF M F) (e1 : Λ.expr)
    (hsafe : ∀ σ1, match s with
      | .notStuck => reducible e1 σ1
      | .maybeStuck => Λ.to_val e1 = none)
    (hstep : ∀ κ σ1 e2 σ2 efs, Λ.prim_step e1 σ1 κ e2 σ2 efs →
      κ = [] ∧ σ2 = σ1 ∧ efs = []) :
    ilater
      (iforall fun κ : List Λ.observation =>
        iforall fun e2 : Λ.expr =>
          iforall fun efs : List Λ.expr =>
            iforall fun σ : Λ.state =>
              iwand (ipure (Λ.prim_step e1 σ κ e2 σ efs))
                (wp (W := W) s E e2 Φ))
    ⊢ wp (W := W) s E e1 Φ :=
  by
    -- unfold the fixpoint and discharge the pure-step precondition
    have hv : Λ.to_val e1 = none :=
      pure_step_val_none (Λ := Λ) (s := s) (e1 := e1) hsafe
    have hpre :
        ilater
          (iforall fun κ : List Λ.observation =>
            iforall fun e2 : Λ.expr =>
              iforall fun efs : List Λ.expr =>
                iforall fun σ : Λ.state =>
                  iwand (ipure (Λ.prim_step e1 σ κ e2 σ efs))
                    (wp (W := W) s E e2 Φ)) ⊢
          wp_pre (W := W) s (wp (W := W) s) E e1 Φ :=
      pure_step_wp_pre (s := s) (E := E) (e1 := e1) (Φ := Φ)
        hsafe hstep hv
    exact hpre.trans <|
      wp_lift_step (s := s) (E := E) (Φ := Φ) (e1 := e1) hv

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Lift an atomic step with fancy update.
Coq: `wp_lift_atomic_step_fupd` in `lifting.v`. -/
theorem wp_lift_atomic_step_fupd (s : Stuckness) (E1 E2 : Iris.Set Positive)
    (Φ : Λ.val → IPropWsat GF M F) (e1 : Λ.expr)
    (hv : Λ.to_val e1 = none) :
    E1 = E2 →
    wp_pre (W := W) s (wp (W := W) s) E1 e1
      (fun v => uPred_fupd (M := M) (F := F) W E2 E1 (Φ v))
    ⊢ wp (W := W) s E1 e1 Φ :=
  by
    -- reduce to the non-atomic step rule and absorb the postcondition update
    intro hE
    subst hE
    have hstep :=
      wp_lift_step_fupd
        (s := s) (E := E1) (Φ := fun v =>
          uPred_fupd (M := M) (F := F) W E1 E1 (Φ v))
        (e1 := e1) hv
    exact hstep.trans <|
      wp_fupd (W := W)
        (s := s) (E := E1) (e := e1) (Φ := Φ)

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Lift an atomic step.
Coq: `wp_lift_atomic_step` in `lifting.v`. -/
theorem wp_lift_atomic_step (s : Stuckness) (E : Iris.Set Positive)
    (Φ : Λ.val → IPropWsat GF M F) (e1 : Λ.expr)
    (hv : Λ.to_val e1 = none) :
    wp_pre (W := W) s (wp (W := W) s) E e1 Φ ⊢ wp (W := W) s E e1 Φ :=
  by
    -- atomic steps are handled by the generic step lemma in this port
    simpa using wp_lift_step_fupd
      (s := s) (E := E) (Φ := Φ) (e1 := e1) hv

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Lift a deterministic pure step with no fork.
Coq: `wp_lift_pure_det_step_no_fork` in `lifting.v`. -/
theorem wp_lift_pure_det_step_no_fork [Inhabited Λ.state]
    (s : Stuckness) (E : Iris.Set Positive)
    (Φ : Λ.val → IPropWsat GF M F) (e1 e2 : Λ.expr)
    (hsafe : ∀ σ1, match s with
      | .notStuck => reducible e1 σ1
      | .maybeStuck => Λ.to_val e1 = none)
    (hstep : ∀ σ1 κ e2' σ2 efs', Λ.prim_step e1 σ1 κ e2' σ2 efs' →
      κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) :
    ilater (wp (W := W) s E e2 Φ)
    ⊢ wp (W := W) s E e1 Φ :=
  by
    -- specialize the deterministic continuation and reuse `wp_lift_pure_step_no_fork`
    have hstep' :
        ∀ κ σ1 e2' σ2 efs, Λ.prim_step e1 σ1 κ e2' σ2 efs →
          κ = [] ∧ σ2 = σ1 ∧ efs = [] := by
      -- drop the deterministic `e2` equality
      intro κ σ1 e2' σ2 efs hprim
      rcases hstep σ1 κ e2' σ2 efs hprim with ⟨hκ, hσ, _, hfs⟩
      exact ⟨hκ, hσ, hfs⟩
    have hcont :
        ilater (wp (W := W) s E e2 Φ) ⊢
          ilater
            (iforall fun κ : List Λ.observation =>
              iforall fun e2' : Λ.expr =>
                iforall fun efs : List Λ.expr =>
                  iforall fun σ : Λ.state =>
                    iwand (ipure (Λ.prim_step e1 σ κ e2' σ efs))
                      (wp (W := W) s E e2' Φ)) :=
      later_mono (PROP := IPropWsat GF M F)
        (pure_det_to_cont (s := s) (E := E) (e1 := e1)
        (e2 := e2) (Φ := Φ) hstep)
    exact hcont.trans <|
      wp_lift_pure_step_no_fork
        (s := s) (E := E) (Φ := Φ) (e1 := e1) hsafe hstep'

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Lift a pure stuck expression.
Coq: `wp_lift_pure_stuck` in `lifting.v`. -/
theorem wp_lift_pure_stuck [Inhabited Λ.state]
    (E : Iris.Set Positive) (Φ : Λ.val → IPropWsat GF M F) (e : Λ.expr)
    (hstuck : ∀ σ, stuck e σ) :
    ipure True ⊢ wp (W := W) .maybeStuck E e Φ :=
  by
    -- derive non-valueness from stuckness and reuse `wp_lift_stuck`
    have hv : Λ.to_val e = none := (hstuck (default : Λ.state)).1
    exact wp_lift_stuck
      (_s := .maybeStuck) (E := E) (Φ := Φ) (e := e) hv hstuck

end Iris.ProgramLogic
