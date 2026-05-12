/-
Copyright (c) 2026 Haokun Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haokun Li
-/
module

public import Iris.ProgramLogic.Language
public import Iris.Algebra.OFE
public import Iris.Algebra.IProp
public import Iris.Instances.IProp
public import Iris.Instances.Lib.WSat
public import Iris.Instances.Lib.FUpd
public import Iris.BI
public import Iris.BI.BigOp
public import Iris.BI.Updates
public import Iris.ProofMode

@[expose] public section

/-! # Weakest Precondition

Lean 4 port of Coq Iris's program logic weakest precondition layer,
following `iris/program_logic/weakestpre.v`.

This file defines:
- `Stuckness` — inductive matching Coq's `stuckness` (NotStuck / MaybeStuck)
- `IrisGS` typeclass — matching all 5 fields of Coq's `irisGS_gen`
- `wp_pre` — Coq's `wp_pre` 1:1 (with `num_laters_per_step` parameterization)
- `wp_pre_contractive` instance — Coq's `Local Instance wp_pre_contractive`
- `wp` — Coq's `wp_def := λ s, fixpoint (wp_pre s)`
- `wp_unfold` — Coq's `Lemma wp_unfold`

All definitions and theorem statements are 1:1 with Coq weakestpre.v.
Upstream operators reused: `Iris.Algebra.OFE` (Contractive / fixpoint /
fixpoint_unfold), `Iris.Instances.Lib.{WSat,FUpd}` (InvGS / uPred_fupd /
BIFUpdate), `Iris.BI.Updates` (|={E1,E2}=> / |={E}[E']▷=> / |={E}▷=>^[n]
notations), `Iris.BI.BigOp.BigSepList` ([∗list] k ↦ x ∈ l, P k x).
-/

namespace Iris.ProgramLogic

open Iris OFE COFE BI Iris.BI Iris.Algebra Iris.ProgramLogic.PrimStep

/-! ## Stuckness

Coq weakestpre.v: `Inductive stuckness := NotStuck | MaybeStuck.`
We use lowercase constructors `Stuckness.notStuck / .maybeStuck` per Lean convention. -/

inductive Stuckness where
  | notStuck
  | maybeStuck
  deriving DecidableEq

namespace Stuckness

/-- Order on stuckness: `notStuck ≤ maybeStuck` (NotStuck is the stronger constraint).
Coq weakestpre.v: `Definition stuckness_le ...`. -/
def le : Stuckness → Stuckness → Prop
  | .notStuck, _ => True
  | .maybeStuck, .maybeStuck => True
  | .maybeStuck, .notStuck => False

end Stuckness

/-! ## IrisGS typeclass

Coq weakestpre.v `irisGS_gen`:
```
Class irisGS_gen (hlc : has_lc) (Λ : language) (Σ : gFunctors) := IrisG {
  iris_invGS  : invGS_gen hlc Σ;
  state_interp : state Λ → nat → list (observation Λ) → nat → iProp Σ;
  fork_post : val Λ → iProp Σ;
  num_laters_per_step : nat → nat;
  state_interp_mono σ ns κs nt :
    state_interp σ ns κs nt ⊢ |={∅}=> state_interp σ (S ns) κs nt
}.
```

Adaptation to Lean:
- All five Coq fields (`iris_invGS`, `state_interp`, `fork_post`,
  `num_laters_per_step`, `state_interp_mono`) are present; `iris_invGS` is via
  `extends InvGS_gen hlc GF`. Coq's `has_lc` two-element type is represented
  by Lean's `Bool` (the upstream convention, see `Iris/Instances/Lib/FUpd.lean`). -/

class IrisGS (Expr : Type _) (State Obs Val : outParam (Type _))
    [Language Expr State Obs Val] (hlc : outParam Bool) (GF : BundledGFunctors)
    extends InvGS_gen hlc GF where
  /-- State interpretation: `σ → step_count → past_observations → num_forks → iProp`.
  Coq: field of `irisGS_gen`. -/
  state_interp : State → Nat → List Obs → Nat → IProp GF
  /-- Fixed postcondition for forked threads.
  Coq: field of `irisGS_gen`. -/
  fork_post : Val → IProp GF
  /-- Per-step number of `▷` laters (allows step-indexed reasoning to vary across step count).
  Coq: field of `irisGS_gen`. HeapLang-style instances set this to `fun _ => 0`. -/
  num_laters_per_step : Nat → Nat
  /-- Monotonicity of state interpretation in the step count.
  Coq weakestpre.v `irisGS_gen.state_interp_mono`. -/
  state_interp_mono (σ : State) (ns : Nat) (κs : List Obs) (nt : Nat) :
    state_interp σ ns κs nt ⊢ iprop(|={∅}=> state_interp σ (ns + 1) κs nt)

/-! ## wp_pre

Coq weakestpre.v `wp_pre`:
```
Definition wp_pre `{!irisGS_gen hlc Λ Σ} (s : stuckness)
    (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1 ns κ κs nt,
     state_interp σ1 ns (κ ++ κs) nt ={E,∅}=∗
       ⌜match s with NotStuck => reducible e1 σ1 | MaybeStuck => True end⌝ ∗
       ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝
         ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
       state_interp σ2 (S ns) κs (length efs + nt) ∗
       wp E e2 Φ ∗
       [∗ list] i ↦ ef ∈ efs, wp ⊤ ef fork_post
  end%I.
```

Uses `S (IrisGS.num_laters_per_step ns)` per-step laters, matching Coq exactly. -/

variable {Expr State Obs Val : Type _} [Language Expr State Obs Val]
variable {hlc : Bool} {GF : BundledGFunctors} [iG : IrisGS Expr State Obs Val hlc GF]

/-- Reducibility predicate selected by stuckness.
Coq weakestpre.v: `match s with NotStuck => reducible | MaybeStuck => True end`. -/
def stuckPred (s : Stuckness) (e : Expr) (σ : State) : Prop :=
  match s with
  | .notStuck => PrimStep.Reducible (Expr := Expr) (Obs := List Obs) (e, σ)
  | .maybeStuck => True

/-- Type abbreviation for the function space of `wp`.
Coq uses `coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ`. -/
abbrev WPFun (Expr Val : Type _) (GF : BundledGFunctors) :=
  CoPset → Expr → (Val → IProp GF) → IProp GF

/-- Pre-fixpoint of weakest precondition. Recursive call `wp` is a parameter.
Coq weakestpre.v `wp_pre`; statement 1:1 with the Coq definition. -/
noncomputable def wp_pre (s : Stuckness)
    (wp : WPFun Expr Val GF)
    (E : CoPset) (e : Expr) (Φ : Val → IProp GF) : IProp GF :=
  match toVal (Val := Val) e with
  | some v => iprop(|={E}=> Φ v)
  | none => iprop(
      ∀ (σ1 : State) (ns : Nat) (κ κs : List Obs) (nt : Nat),
        IrisGS.state_interp (Expr := Expr) σ1 ns (κ ++ κs) nt ={E,∅}=∗
          ⌜stuckPred s e σ1⌝ ∗
          ∀ (e2 : Expr) (σ2 : State) (efs : List Expr),
            ⌜PrimStep.primStep (e, σ1) κ (e2, σ2, efs)⌝
              ={ ∅ }▷=∗^[ iG.num_laters_per_step ns + 1 ] (|={∅,E}=>
                IrisGS.state_interp (Expr := Expr) σ2 (ns + 1) κs (efs.length + nt) ∗
                wp E e2 Φ ∗
                [∗list] ef ∈ efs, wp ⊤ ef (IrisGS.fork_post (Expr := Expr))))

/-- Helper: `|={E1}[E2]▷=∗^[k]` is NonExpansive in the inner argument `Q`.
Proof: induction on `k`, with each layer using `BIFUpdate.ne + later_ne + BIFUpdate.ne`. -/
private theorem step_fupdN_ne {E1 E2 : CoPset} {k : Nat} {n : Nat}
    {X Y : IProp GF} (h : X ≡{n}≡ Y) :
    Nat.repeat (fun Q : IProp GF => iprop(|={E1}[E2]▷=> Q)) k X ≡{n}≡
      Nat.repeat (fun Q : IProp GF => iprop(|={E1}[E2]▷=> Q)) k Y := by
  induction k with
  | zero => exact h
  | succ k' IH =>
    refine BIFUpdate.ne.ne ?_
    refine later_ne.ne ?_
    refine BIFUpdate.ne.ne ?_
    exact IH

/-- Contractive instance for `wp_pre s`.
Coq weakestpre.v: `Local Instance wp_pre_contractive : Contractive (wp_pre s)`.
Statement 1:1 with Coq; proof follows the pattern of
`Iris/Examples/IProp.lean:131-142` `wp_F_contractive`. -/
noncomputable instance wp_pre_contractive (s : Stuckness) :
    Contractive (fun W : WPFun Expr Val GF => wp_pre s W) where
  distLater_dist {n W₁ W₂ HW} E e Φ := by
    show wp_pre s W₁ E e Φ ≡{n}≡ wp_pre s W₂ E e Φ
    cases hto : toVal (Val := Val) e with
    | some v =>
        unfold wp_pre
        simp only [hto]
        exact .rfl
    | none =>
        unfold wp_pre
        simp only [hto]
        refine forall_ne fun σ => ?_
        refine forall_ne fun ns => ?_
        refine forall_ne fun κ => ?_
        refine forall_ne fun κs => ?_
        refine forall_ne fun nt => ?_
        refine wand_ne.ne .rfl ?_
        refine BIFUpdate.ne.ne ?_
        refine sep_ne.ne .rfl ?_
        refine forall_ne fun e2 => ?_
        refine forall_ne fun σ2 => ?_
        refine forall_ne fun efs => ?_
        refine wand_ne.ne .rfl ?_
        -- `_ ▷=∗^[k+1]` macro → `Nat.repeat _ (k+1) X = (fun Q => |={∅}[∅]▷=> Q) (Nat.repeat _ k X)`
        -- Pass through `|={∅,∅}=> ▷ |={∅,∅}=> ...`; the `▷` layer uses `distLater_dist`.
        refine BIFUpdate.ne.ne ?_
        refine Contractive.distLater_dist fun m hm => ?_
        refine BIFUpdate.ne.ne ?_
        -- Remaining: `Nat.repeat _ (num_laters_per_step ns) inner` on each side — use step_fupdN_ne.
        refine step_fupdN_ne ?_
        -- Inner `inner` = `|={∅,E}=> (state_interp ∗ W E e2 Φ ∗ [∗list])`.
        refine BIFUpdate.ne.ne ?_
        refine sep_ne.ne .rfl ?_
        refine sep_ne.ne ?_ ?_
        · exact HW m hm E e2 Φ
        · exact Iris.BI.BigSepL.bigSepL_dist fun {_ _} _ => HW m hm ⊤ _ _

/- `WPFun Expr Val GF` is automatically a COFE:

- `IProp GF = UPred (IResUR GF)` is a COFE via `instance : IsCOFE (UPred M)`
  (Iris/Algebra/UPred.lean) combined with `class abbrev COFE := OFE + IsCOFE`.
- The function-space instance `[∀ x, COFE (β x)] → COFE ((x : α) → β x)`
  (Iris/Algebra/OFE.lean) applies three times to layer over
  `CoPset → Expr → (Val → IProp GF) → IProp GF`.

No explicit instance needed — typeclass resolution derives it automatically. -/

/-- `Inhabited (WPFun Expr Val GF)` required by `fixpoint`. -/
noncomputable instance : Inhabited (WPFun Expr Val GF) :=
  ⟨fun _ _ _ => iprop(True)⟩

/-! ## wp definition

Coq weakestpre.v:
```
Definition wp_def `{!irisGS_gen hlc Λ Σ} : Wp (iProp Σ) (expr Λ) (val Λ) stuckness :=
  λ s : stuckness, fixpoint (wp_pre s).
```

One fixpoint per `Stuckness` value (matching Coq's style). -/

/-- The weakest precondition.
Coq weakestpre.v: `Definition wp_def := λ s, fixpoint (wp_pre s)`. -/
noncomputable def wp (s : Stuckness) : WPFun Expr Val GF :=
  fixpoint (fun W : WPFun Expr Val GF => wp_pre s W)

/-! ## wp_unfold

Coq weakestpre.v `wp_unfold`:
```
Lemma wp_unfold s E e Φ :
  WP e @ s; E {{ Φ }} ⊣⊢ wp_pre s (wp s) E e Φ.
```

Proof uses upstream `fixpoint_unfold` to obtain `≡`, then converts to `⊣⊢` via
function-space pointwise evaluation and `BI.equiv_iff`. -/
theorem wp_unfold (s : Stuckness) (E : CoPset) (e : Expr) (Φ : Val → IProp GF) :
    wp (Expr := Expr) (Val := Val) (GF := GF) s E e Φ ⊣⊢
      wp_pre s (wp (Expr := Expr) (Val := Val) (GF := GF) s) E e Φ := by
  let F : ContractiveHom (WPFun Expr Val GF) (WPFun Expr Val GF) :=
    { f := fun W => wp_pre s W, contractive := inferInstance }
  have h := fixpoint_unfold F
  exact BI.equiv_iff.mp (h E e Φ)

end Iris.ProgramLogic
