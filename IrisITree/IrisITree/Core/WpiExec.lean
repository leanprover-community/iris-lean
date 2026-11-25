/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunsong Yang, Michael Sammler
-/

module

public import IrisITree.Core.Wpi
public import IrisITree.Core.LfpTp
public import Iris.Instances.Lib.FUpd

public section

local stepindex Nat

namespace IrisITree

open Iris BI ITree Std

/--
  The constant-Φ weakest precondition functional.
  Unlike `wpiF`, the postcondition Φ is fixed rather than varying.
-/
@[expose]
def wpiConstF {E : Effect} {R : Type _} {PROP : Type _} [BI PROP] [BIFUpdate PROP]
    (H : IHandler PROP E) (Φ : R → PROP)
    (wpi : ITree E R → PROP) :
    ITree E R → PROP :=
  fun t => iprop% |={∅}=>
      match t.unfold with
      | ITreeF.ret r => Φ r
      | ITreeF.tau t' => wpi t'
      | ITreeF.vis i k => H.ihandle i (fun a => wpi (k a)) (fun a => wpi (k a))

section wp_itree_const

variable {E : Effect} {R : Type _} {PROP : Type _} [BI PROP] [BIFUpdate PROP]

instance (H : IHandler PROP E) (Φ : R → PROP) : OFE.NonExpansive (wpiConstF H Φ) where
  ne {_ wp1 wp2} Hwp t:= by
    cases t <;> simp [wpiConstF]
    case tau t' => exact BIFUpdate.ne.ne <| Hwp t'
    case vis i k =>
      apply BIFUpdate.ne.ne
      exact OFE.NonExpansive₂.ne (fun a => Hwp (k a)) (fun a => Hwp (k a))

theorem wpiConstF_mono (H : IHandler PROP E) (Φ : R → PROP) (wp1 wp2 : ITree E R → PROP) :
    □ (∀ t, wp1 t -∗ wp2 t) -∗
    ∀ t, wpiConstF H Φ wp1 t -∗ wpiConstF H Φ wp2 t := by
  iintro #Hwand %t
  cases t <;> simp [wpiConstF]
  case ret => iintro $
  case tau t' => iintro >Hwp !>; iapply Hwand $$ Hwp
  case vis i k =>
    iintro >Hwp !>
    iapply H.ihandle_mono $$ [] [] Hwp
    · iintro %a Hk; iapply Hwand $$ Hk
    · iintro !> %a Hk; iapply Hwand $$ Hk

theorem wpiConstF_mono' (H : IHandler PROP E) (Φ Ψ : R → PROP) wp :
    □ (∀ r, Φ r -∗ Ψ r) -∗
    ∀ t, wpiConstF H Φ wp t -∗ wpiConstF H Ψ wp t := by
  iintro #Hwand %t Hwp
  cases t <;> simp [wpiConstF]
  case ret =>
    imod Hwp
    imodintro
    iapply Hwand $$ [$]
  all_goals itrivial

theorem wpiConstF_fupd (H : IHandler PROP E) Φ wp :
    wpiConstF H (fun v => iprop% |={∅}=> Φ v) wp t -∗
    wpiConstF H Φ wp t := by
  cases t <;> simp [wpiConstF]
  case ret => iintro >$
  all_goals iintro $

instance wp_itree_const_mono (H : IHandler PROP E) (Φ : R → PROP) :
    BIMonoPred (wpiConstF H Φ) where
  mono_pred := by
    iintro %wp1 %wp2 %Hne1 %Hne2 #Hwand %t Hwp
    iapply wpiConstF_mono $$ Hwand Hwp
  mono_pred_ne := inferInstance

/-- The constant-Φ weakest precondition, as the least fixpoint of `wpi_constF`. -/
def wpiConst (H : IHandler PROP E) (Φ : R → PROP) : ITree E R → PROP :=
  bi_least_fixpoint (wpiConstF H Φ)

theorem wpi_const_iter (H : IHandler PROP E) (Φ : R → PROP)
    (P : ITree E R → PROP) :
    □ (∀ y, wpiConstF H Φ P y -∗ P y) -∗
    ∀ t, wpiConst H Φ t -∗ P t := by
  unfold wpiConst
  iintro #Hwand %t Hwp
  iapply least_fixpoint_iter (wpiConstF H Φ) $$ Hwand Hwp

end wp_itree_const

/-- The thread-pool weakest precondition, built from `wpiConstF` and `lfp_tp`. -/
noncomputable def wpi_tp {E : Effect} {R : Type _} {PROP : Type _} [BI PROP] [BIFUpdate PROP]
    (H : IHandler PROP E)
    (Ms : ListPerm ((ITree E R → PROP) → PROP))
    (Φ : R → PROP) : PROP :=
  lfp_tp (wpiConstF H Φ) Ms

syntax (name := wpiTpNotation) "WPi_tp " term:20 " @> " term:max wpPostcond : term

@[macro wpiTpNotation]
meta def wpiTpMacro : Lean.Macro := fun stx => do
  match stx with
  | `(WPi_tp $ts:term @> $H:term $postcond:wpPostcond) =>
    let (Φ, _) ← Iris.parseWpPostcond postcond
    `(wpi_tp $H $ts $Φ)
  | _ => Lean.Macro.throwUnsupported

section wpi_tp_section

variable {E : Effect} {R : Type _} {PROP : Type _} [BI PROP] [BIFUpdate PROP]

theorem wpi_tp_intro (t : ITree E R) (H : IHandler PROP E) (Φ : R → PROP) :
    WPi t @> H; ∅ {{ Φ }} -∗
    WPi_tp {fun P => P t} @> H {{ Φ }} := by
  let G := fun t (Ψ: R → PROP) => iprop%
    □ (∀ r, Ψ r -∗ Φ r) -∗ bi_least_fixpoint (wpiConstF H Φ) t
  letI : ∀ t, OFE.NonExpansive (G t) := fun _ => ⟨fun _ _ _ HΨ => wand_ne.ne
    (intuitionistically_ne.ne (forall_ne fun r => wand_ne.ne (HΨ r) .rfl)) .rfl⟩
  iintro Hwpi; unfold wpi_tp
  iapply lfp_tp_intro
  iapply wpi_ind G $$ [] Hwpi
  · iintro !> %t %Ψ Hstep #Hpost
    iapply least_fixpoint_unfold_mpr
    cases t <;> simp [wpiConstF, wpiF]
    · imod Hstep with >Hstep
      imodintro
      iapply Hpost $$ [$]
    · imod Hstep with ⟨Hconst, -⟩
      imodintro
      iapply Hconst $$ [$]
    · imod Hstep; imodintro
      iapply H.ihandle_mono $$ [] [] Hstep
      · iintro %a ⟨Hconst, -⟩; iapply Hconst $$ [$]
      · iintro !> %a ⟨Hconst, -⟩
        iapply Hconst; iintro !> %r ⟨⟩
  · iintro !> %r $

theorem wpi_tp_fupd (Ms : ListPerm ((ITree E R → PROP) → PROP)) H Φ :
    WPi_tp Ms @> H {{ v, |={∅}=> Φ v }} -∗
    WPi_tp Ms @> H {{ Φ }} := by
  unfold wpi_tp
  iintro Hwp
  iapply lfp_tp_ind _ $$ [] Hwp
  iintro !> %Ns Hstep
  iapply lfp_tp_unfold
  iapply lfp_tpF_mono' $$ [] [Hstep]
  · iintro !> %Φ' %x Hwp
    iapply wpiConstF_fupd $$ Hwp
  · iapply lfp_tpF_mono $$ [] Hstep
    iintro !> %Ns ⟨$, -⟩

theorem wpi_tp_wand (Ms : ListPerm ((ITree E R → PROP) → PROP)) H Φ Ψ :
    □ (∀ r, Φ r -∗ Ψ r) -∗
    WPi_tp Ms @> H {{ Φ }} -∗
    WPi_tp Ms @> H {{ Ψ }} := by
  unfold wpi_tp
  iintro #Hwand Hwp
  iapply lfp_tp_ind _ $$ [] Hwp
  iintro !> %Ns Hlfp
  iapply lfp_tp_unfold
  iapply lfp_tpF_mono' $$ [] [Hlfp]
  · iintro !> %Φ' %x Hwp
    iapply wpiConstF_mono' $$ Hwand Hwp
  · iapply lfp_tpF_mono $$ [] Hlfp
    iintro !> %Ns ⟨$, -⟩

/-- The returned value of the selected thread satisfies the pool postcondition.
    The <absorb> is necessary to absorb the ownership of the other threads. -/
theorem wpi_tp_elim' H (Ms : ListPerm ((ITree E R → PROP) → PROP)) M Φ
    (t : ITree E R) (r : R) :
    t = pure r →
    (∀ P, M P ={∅}=∗ P t) -∗
    WPi_tp ({M} ⊎ Ms) @> H {{ Φ }} -∗
    |={∅}=> <absorb> Φ r := by
  iintro %rfl HM Htp
  unfold wpi_tp
  rw [(lfp_tp_unfold (wpiConstF H Φ) ({M} ⊎ Ms)).to_eq, lfp_tpF]
  ispecialize Htp $$ %M %Ms [//]
  ihave Htp := bi_mono0_mono_l $$ Htp HM
  imod bi_mono0_elim $$ Htp [] with ⟨%G, Hwpi, -⟩
  · iintro %Q %Q' Hwand >HQ' !>; iapply Hwand $$ [$]
  simp [wpiConstF]
  imod Hwpi with $

/-- If the selected thread is `pure r`, the postcondition holds for `r`. -/
theorem wpi_tp_elim H (Ms : ListPerm ((ITree E R → PROP) → PROP)) M Φ (r : R) :
    (∀ P, M P ={∅}=∗ P (pure r : ITree E R)) -∗
    WPi_tp ({M} ⊎ Ms) @> H {{ Φ }} -∗
    |={∅}=> <absorb> Φ r :=
  wpi_tp_elim' H Ms M Φ (pure r) r rfl

end wpi_tp_section

section wpi_adequate

open ITree.Exec

variable {E : Effect.{u}} {R : Type u} {σ : Type _}
variable {PROP} [BI PROP] [BIFUpdate PROP]
variable (H : IHandler PROP E) (EH : EHandler E E R σ)
variable [A : EHandlerAdequate H EH]

theorem wpi_adequate_ind (Φ : R → PROP)
    (t : ITree E R) (s : σ) (Ms Mss : ListPerm ((ITree E R → PROP) → PROP))
    (M : (ITree E R → PROP) → PROP) (C : ITree E R → σ → Prop)
    (Hexec : exec EH t s C) (HMs : Ms = {M} ⊎ Mss) :
    WPi_tp Ms @> H {{ Φ }} -∗
    A.inv s Mss -∗
    (∀ P, M P ={∅}=∗ P t) -∗
    |={∅}=> ∃ t' s' Ms' M', <affine> ⌜C t' s'⌝ ∗ A.inv s' Ms' ∗
      (∀ P, M' P ={∅}=∗ P t') ∗
      WPi_tp ({M'} ⊎ Ms') @> H {{ Φ }} := by
  unfold wpi_tp; iintro Htp
  irevert %t %s %M %Mss %C %Hexec %HMs; irevert Htp; irevert %Ms
  iapply lfp_tp_ind (wpiConstF H Φ)
  iintro !> %Ms IH %t %s %M %Mss %C %Hexec %HMs Hinv Ht
  rw [← exec.fold] at Hexec
  cases Hexec with
  | stop _ _ _ HC =>
    imodintro
    iexists t, s, Mss, M
    iframe %HC Hinv Ht
    rw [← HMs]
    iapply lfp_tp_unfold
    iapply lfp_tpF_mono $$ [] %Ms IH
    iintro !> %Ns ⟨-, $⟩
  | tau t _ _ Hexec =>
    unfold lfp_tpF; ispecialize IH $$ %M %Mss %HMs
    ihave IH := bi_mono0_mono_l M (fun P => iprop% |={∅}=> P t.tau) $$ IH Ht
    imod bi_mono0_elim $$ IH [] with ⟨%G, Hwpi, Hc⟩
    · iintro %Q %Q' Hwand >HQ'; imodintro; iapply Hwand $$ [$]
    simp [wpiConstF]; imod Hwpi
    icases Hc $$ %({fun P => P t}) [Hwpi] with ⟨Hadequate, -⟩
    · iapply (BigSepMS.bigSepMS_singleton (Φ := fun M => M G) (x := fun P => P t)).mpr $$ Hwpi
    iapply Hadequate $$ %t %s %(fun P => P t) %Mss %C %Hexec %rfl Hinv
    iintro %_ $
    itrivial
  | step i k _ _ Hhandle =>
    unfold lfp_tpF; ispecialize IH $$ %M %Mss %HMs
    ihave IH := bi_mono0_mono_l M (fun P => iprop% |={∅}=> P (.vis i k)) $$ IH Ht
    imod bi_mono0_elim $$ IH [] with ⟨%G, Hwpi, Hc⟩
    · iintro %Q %Q' Hwand >HQ'; imodintro; iapply Hwand $$ [$]
    simp [wpiConstF]; imod Hwpi
    imod A.adequate _ _ _ Mss _ _ Hhandle $$ Hwpi Hinv with
      ⟨%t', %s', %M', %Ms', %Msn, %HC, %Hpool, Hspawn, Hinv, Hmod⟩
    icases Hc $$ %Msn Hspawn with ⟨Hadequate, -⟩
    iapply Hadequate $$ %t' %s' %M' %Ms' %C %HC %Hpool.symm Hinv Hmod

theorem wpi_adequate (Φ : R → PROP)
    (t : ITree E R) (s : σ) (C : ITree E R → σ → Prop) (m : CoPset)
    (Hexec : exec EH t s C) :
    ⊢ WPi t @> H;m {{ Φ }} -∗
      A.inv s ∅ -∗
      |={m, ∅}=> ∃ t' s' Ms' M', <affine> ⌜C t' s'⌝ ∗ A.inv s' Ms' ∗
      (∀ P, M' P ={∅}=∗ P t') ∗
      WPi_tp ({M'} ⊎ Ms') @> H {{ v, |={∅,m}=> Φ v}} := by
  iintro >Hwpi Hinv
  icases wpi_fupd_empty $$ Hwpi with Hwpi
  iapply wpi_adequate_ind _ _ _ t s {fun P => P t} ∅
    (fun P => P t) C Hexec disjUnion_empty_right.symm $$ [Hwpi] Hinv []
  · iapply wpi_tp_intro $$ Hwpi
  · iintro %_ $ !> //

end wpi_adequate

section wpi_adequate_pure

open ITree.Exec

variable {GF : BundledGFunctors} {E : Effect} {R σ : Type _} [InvGpreS GF]

theorem wpi_adequate_pure (hlc : HasLC) (n : Nat) (m : CoPset)
    (EH : EHandler E E R σ) (t : ITree E R) (s : σ)
    (C : ITree E R → σ → Prop) (Ψ : Prop) :
    exec EH t s C →
    (∀ (_ : InvGS_gen hlc GF), £ n ={⊤,m}=∗
      ∃ (H : IHandler (IProp GF) E) (A : EHandlerAdequate H EH) (Φ : R → IProp GF),
        WPi t @> H;m {{ Φ }} ∗ A.inv s ∅ ∗
        (∀ t' s' Ms' M', <affine> ⌜C t' s'⌝ -∗ A.inv s' Ms' -∗
          (∀ P, M' P ={∅}=∗ P t') ∗
            (WPi_tp ({M'} ⊎ Ms') @> H {{ v, |={∅,m}=> Φ v }})={∅}=∗ ⌜Ψ⌝)) →
    Ψ := by
  intro Hexec Hwp
  apply pure_soundness (PROP := IProp GF)
  apply step_fupdN_soundness (hlc := hlc) 0 n
  iintro %Hinv Hlc
  imod Hwp Hinv $$ Hlc with ⟨%H, %A, %Φ, Hwpi, Hs, Hc⟩
  imod wpi_adequate H EH Φ t s C m Hexec $$ Hwpi Hs with
    ⟨%t', %s', %Ms', %M', %HC, Hs', Hclose, Htp⟩
  imod Hc $$ %t' %s' %Ms' %M' %HC Hs' [$Hclose $Htp] with %HΨ
  imodintro; iapply step_fupdN_0; itrivial

end wpi_adequate_pure

end IrisITree
