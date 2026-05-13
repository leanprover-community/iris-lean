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

Port of `iris/program_logic/weakestpre.v`: fixpoint base. -/

namespace Iris.ProgramLogic

open Iris OFE COFE BI Iris.Algebra Iris.BI.BigSepL Iris.ProgramLogic.PrimStep

@[rocq_alias stuckness]
inductive Stuckness where
  | notStuck
  | maybeStuck
  deriving DecidableEq

namespace Stuckness

@[rocq_alias stuckness_le]
def le : Stuckness → Stuckness → Prop
  | .notStuck, _ => True
  | .maybeStuck, .maybeStuck => True
  | .maybeStuck, .notStuck => False

end Stuckness

@[rocq_alias irisGS_gen]
class IrisGS (Expr : Type _) (State Obs Val : outParam (Type _))
    [Language Expr State Obs Val] (hlc : outParam Bool) (GF : BundledGFunctors)
    extends InvGS_gen hlc GF where
  state_interp : State → Nat → List Obs → Nat → IProp GF
  fork_post : Val → IProp GF
  num_laters_per_step : Nat → Nat
  state_interp_mono (σ : State) (ns : Nat) (κs : List Obs) (nt : Nat) :
    state_interp σ ns κs nt ⊢ iprop(|={∅}=> state_interp σ (ns + 1) κs nt)

variable {Expr State Obs Val : Type _} [Language Expr State Obs Val]
variable {hlc : Bool} {GF : BundledGFunctors} [iG : IrisGS Expr State Obs Val hlc GF]

def stuckPred (s : Stuckness) (e : Expr) (σ : State) : Prop :=
  match s with
  | .notStuck => PrimStep.Reducible (Expr := Expr) (Obs := List Obs) (e, σ)
  | .maybeStuck => True

abbrev WPFun (Expr Val : Type _) (GF : BundledGFunctors) :=
  CoPset → Expr → (Val → IProp GF) → IProp GF

@[rocq_alias wp_pre]
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

@[rocq_alias wp_pre_contractive]
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
        refine BIFUpdate.ne.ne ?_
        refine Contractive.distLater_dist fun m hm => ?_
        refine BIFUpdate.ne.ne ?_
        refine step_fupdN_ne ?_
        refine BIFUpdate.ne.ne ?_
        refine sep_ne.ne .rfl ?_
        refine sep_ne.ne ?_ ?_
        · exact HW m hm E e2 Φ
        · exact bigSepL_dist fun {_ _} _ => HW m hm ⊤ _ _

noncomputable instance : Inhabited (WPFun Expr Val GF) :=
  ⟨fun _ _ _ => iprop(True)⟩

@[rocq_alias wp_def]
noncomputable def wp (s : Stuckness) : WPFun Expr Val GF :=
  fixpoint (fun W : WPFun Expr Val GF => wp_pre s W)

@[rocq_alias wp_unfold]
theorem wp_unfold (s : Stuckness) (E : CoPset) (e : Expr) (Φ : Val → IProp GF) :
    wp (Expr := Expr) (Val := Val) (GF := GF) s E e Φ ⊣⊢
      wp_pre s (wp (Expr := Expr) (Val := Val) (GF := GF) s) E e Φ := by
  let F : ContractiveHom (WPFun Expr Val GF) (WPFun Expr Val GF) :=
    { f := fun W => wp_pre s W, contractive := inferInstance }
  have h := fixpoint_unfold F
  exact BI.equiv_iff.mp (h E e Φ)

end Iris.ProgramLogic
