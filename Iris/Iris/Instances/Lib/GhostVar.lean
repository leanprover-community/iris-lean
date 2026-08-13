/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.Algebra.Lib.DFracAgree
public import Iris.BI.Lib.Fractional
public import Iris.Instances.IProp
public import Iris.ProofMode

@[expose] public section

namespace Iris

open BI DFrac DFracAgree ProofMode

/-! ## Ghost variable -/

abbrev GhostVarF (A : Type) : COFE.OFunctorPre := constOF (DFracAgreeR (DiscreteO A))

@[rocq_alias ghost_varG]
class GhostVarG (GF : BundledGFunctors) (A : Type) where [elemG : ElemG GF (GhostVarF A)]

attribute [reducible, instance] GhostVarG.elemG

#rocq_ignore «ghost_varΣ» "Superseded by the `GhostVarG` typeclass on `BundledGFunctors`."
#rocq_ignore «subG_ghost_varΣ» "Superseded by Lean's direct `ElemG` typeclass synthesis."

variable {GF : BundledGFunctors} {A : Type} [GhostVarG GF A]

@[rocq_alias ghost_var]
def ghost_var (γ : GName) (dq : DFrac) (a : A) : IProp GF :=
  iOwn (F := GhostVarF A) γ (mk dq ⟨a⟩)

#rocq_ignore ghost_var_def "`ghost_var` is defined directly without `seal`/`unseal`."
#rocq_ignore ghost_var_aux "`ghost_var` is defined directly without `seal`/`unseal`."
#rocq_ignore ghost_var_unseal "`ghost_var` is defined directly without `seal`/`unseal`."

notation γ " ↪VAR{" dq "} " a => ghost_var γ dq a
notation γ " ↪VAR " a => ghost_var γ (DFrac.own 1) a

@[rocq_alias ghost_var_timeless]
instance (γ : GName) (dq : DFrac) (a : A) : Timeless (PROP := IProp GF) (γ ↪VAR{dq} a) := by
  unfold ghost_var
  infer_instance

@[rocq_alias ghost_var_persistent]
instance (γ : GName) (a : A) : Persistent (PROP := IProp GF) (γ ↪VAR{.discard} a) := by
  unfold ghost_var
  infer_instance

@[rocq_alias ghost_var_fractional]
instance ghost_var_fractional (γ : GName) (a : A) :
    Fractional (PROP := IProp GF) (fun q : Qp => γ ↪VAR{.own q} a) where
  fractional _ _  := (BiEntails.of_eq (congrArg (iOwn γ) Frac.mk_op)).trans iOwn_op

@[rocq_alias ghost_var_as_fractional]
instance (γ : GName) (a : A) (q : Qp) :
    AsFractional (PROP := IProp GF) (γ ↪VAR{.own q} a) ioΦ (fun q => γ ↪VAR{.own q} a) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := ghost_var_fractional γ a

@[rocq_alias ghost_var_alloc_strong]
theorem ghost_var_alloc_strong (a : A) (P : GName → Prop) (HP : PredInfinite P) :
    ⊢@{IProp GF} |==> ∃ γ, ⌜P γ⌝ ∗ γ ↪VAR a :=
  iOwn_alloc_strong _ _ HP.exists_ge (mk_valid.mpr valid_own_one)

@[rocq_alias ghost_var_alloc]
theorem ghost_var_alloc (a : A) : ⊢@{IProp GF} |==> ∃ γ, γ ↪VAR a :=
  iOwn_alloc _ (mk_valid.mpr valid_own_one)

@[rocq_alias ghost_var_valid_2]
theorem ghost_var_valid_2 (γ : GName) (a1 : A) (dq1 : DFrac) (a2 : A) (dq2 : DFrac) :
    ⊢@{IProp GF} (γ ↪VAR{dq1} a1) -∗ (γ ↪VAR{dq2} a2) -∗ ⌜✓ (dq1 • dq2) ∧ a1 = a2⌝ := by
  unfold ghost_var
  iintro Hvar1 Hvar2
  icombine Hvar1 Hvar2 gives %H
  obtain ⟨Hq, Ha⟩ := op_valid.mp H
  ipureintro
  exact ⟨Hq, DiscreteO.eqv_inj Ha⟩

@[rocq_alias ghost_var_agree]
theorem ghost_var_agree (γ : GName) (a1 : A) (dq1 : DFrac) (a2 : A) (dq2 : DFrac) :
    ⊢@{IProp GF} (γ ↪VAR{dq1} a1) -∗ (γ ↪VAR{dq2} a2) -∗ ⌜a1 = a2⌝ := by
  iintro Hvar1 Hvar2
  ihave ⟨-, $⟩ := ghost_var_valid_2 $$ Hvar1 Hvar2

@[rocq_alias ghost_var_combine_gives]
instance (γ : GName) (a1 : A) (dq1 : DFrac) (a2 : A) (dq2 : DFrac) :
    CombineSepGives (PROP := IProp GF) (γ ↪VAR{dq1} a1) (γ ↪VAR{dq2} a2)
      iprop(⌜✓ (dq1 • dq2) ∧ a1 = a2⌝) where
  combine_sep_gives := by
    iintro ⟨H1, H2⟩
    icases ghost_var_valid_2 $$ H1 H2 with %H
    itrivial

/-- Lower priority than the `Fractional` instance, which is used when `a1 = a2`. -/
@[rocq_alias ghost_var_combine_as]
instance (priority := default - 20) (γ : GName) (a1 : A) (dq1 : DFrac) (a2 : A) (dq2 : DFrac)
    (dq : DFrac) [h : IsOp .merge dq dq1 dq2] :
    CombineSepAs (PROP := IProp GF) (γ ↪VAR{dq1} a1) (γ ↪VAR{dq2} a2) (γ ↪VAR{dq} a1) where
  combine_sep_as := by
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %⟨-, rfl⟩
    unfold ghost_var
    rw [h.is_op, mk_op]
    icombine H1 H2 as $

@[rocq_alias ghost_var_split]
theorem ghost_var_split (γ : GName) (a : A) (q1 q2 : Qp) :
    ⊢@{IProp GF} (γ ↪VAR{.own (q1 + q2)} a) -∗ (γ ↪VAR{.own q1} a) ∗ (γ ↪VAR{.own q2} a) := by
  iintro ⟨$, $⟩

@[rocq_alias ghost_var_update]
theorem ghost_var_update (b : A) (γ : GName) (a : A) :
    ⊢@{IProp GF} (γ ↪VAR a) ==∗ γ ↪VAR b := by
  unfold ghost_var
  iapply iOwn_update (.exclusive (mk_valid.mpr valid_own_one))

@[rocq_alias ghost_var_update_2]
theorem ghost_var_update_2 (b : A) (γ : GName) (a1 : A) (q1 : Qp) (a2 : A) (q2 : Qp)
    (Hq : q1 + q2 = 1) :
    ⊢@{IProp GF} (γ ↪VAR{.own q1} a1) -∗ (γ ↪VAR{.own q2} a2) ==∗
      (γ ↪VAR{.own q1} b) ∗ (γ ↪VAR{.own q2} b) := by
  unfold ghost_var
  iintro H1 H2
  iapply BIUpdate.mono iOwn_op.mp
  iapply iOwn_update_op (Frac.update₂ Hq) $$ [$H1 $H2]

@[rocq_alias ghost_var_update_halves]
theorem ghost_var_update_halves (b : A) (γ : GName) (a1 a2 : A) :
    ⊢@{IProp GF} (γ ↪VAR{.own (1 : Qp).half} a1) -∗ (γ ↪VAR{.own (1 : Qp).half} a2) ==∗
      (γ ↪VAR{.own (1 : Qp).half} b) ∗ (γ ↪VAR{.own (1 : Qp).half} b) :=
  ghost_var_update_2 b γ a1 _ a2 _ (Qp.half_add_half 1)

@[rocq_alias ghost_var_persist]
theorem ghost_var_persist (γ : GName) (dq : DFrac) (a : A) :
    ⊢@{IProp GF} (γ ↪VAR{dq} a) ==∗ γ ↪VAR{.discard} a := by
  unfold ghost_var
  iapply iOwn_update persist

@[rocq_alias ghost_var_unpersist]
theorem ghost_var_unpersist (γ : GName) (a : A) :
    ⊢@{IProp GF} (γ ↪VAR{.discard} a) ==∗ ∃ q, γ ↪VAR{.own q} a := by
  unfold ghost_var
  iintro H
  imod iOwn_updateP unpersist $$ H with ⟨%x, %⟨q, rfl⟩, G⟩
  iexists q
  iframe

/-! ### Framing support -/

@[rocq_alias frame_ghost_var]
instance (p : Bool) (γ : GName) (a : A) (q1 q2 q : Qp) [FrameFractionalQp q1 q2 q] :
    Frame (PROP := IProp GF) p (γ ↪VAR{.own q1} a) (γ ↪VAR{.own q2} a) (γ ↪VAR{.own q} a) :=
  frame_fractional (fun q => γ ↪VAR{.own q} a) q1 q2 q

end Iris

end
