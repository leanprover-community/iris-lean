/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunsong Yang, Michael Sammler
-/

module

public import Iris.BI.Lib.Fixpoint
public import IrisITree.Core.Handler

public section

local stepindex Nat

namespace IrisITree

open Iris Iris.BI ITree

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
instance {E R} : COFE (ITree E R) := COFE.ofDiscrete _
instance {E R} : OFE.Discrete (ITree E R) := ⟨fun h => h⟩

local bi PROP

section wp_itree_def

variable {E} (H : IHandler PROP E)

@[expose]
def wpiF {R} (wpi : CoPset → ITree E R → (R → PROP) → PROP) :
    CoPset → CoPset → ITree E R → (R → PROP) → PROP :=
  fun Ms Me t Φ => iprop%
    |={Ms, ∅}=> match t.unfold with
      | ITreeF.ret r => |={∅, Me}=> Φ r
      | ITreeF.tau t' => wpi ∅ t' Φ
      | ITreeF.vis i k => H.ihandle i
        (fun a => wpi ∅ (k a) Φ)
        (fun a => wpi ∅ (k a) (fun _ => iprop% False))

private def wpiF' {R} (Me : CoPset) (wpi : DiscreteO CoPset × ITree E R × (R → PROP) → PROP) :
    DiscreteO CoPset × ITree E R × (R → PROP) → PROP :=
  fun ⟨Ms, t, Φ⟩ => wpiF H (fun Ms t Φ => wpi ⟨⟨Ms⟩, t, Φ⟩) Ms.1 Me t Φ

theorem wpiF_mono {R} (wp1 wp2 : CoPset → ITree E R → (R → PROP) → PROP) Me :
    □ (∀ t Φ, wp1 ∅ t Φ -∗ wp2 ∅ t Φ) -∗
    ∀ Ms t Φ, wpiF H wp1 Ms Me t Φ -∗ wpiF H wp2 Ms Me t Φ := by
  iintro #Hwand %Ms %t %Φ Hwp
  unfold wpiF
  imod Hwp
  imodintro
  cases h : t.unfold with
  | ret => itrivial
  | tau t' => iapply Hwand $$ [$]
  | vis i k =>
    iapply H.ihandle_mono
    · iintro %_
      iapply Hwand
    · iintro !> %_
      iapply Hwand
    · itrivial

private instance {R Me} : BIMonoPred (wpiF' (R:=R) H Me) where
  mono_pred := by
    iintro %Φ %Ψ %HΦ %HΨ #H %pair Hsim
    rcases pair with ⟨_, _, _⟩
    unfold wpiF'
    iapply wpiF_mono $$ [] Hsim
    iintro !> %t %Φ1
    iapply H
  mono_pred_ne := by
    -- FIXME: golf
    intro wp Hwp; constructor; intro n ⟨Ms1, t1, Ψ1⟩ ⟨Ms2, t2, Ψ2⟩ ⟨HMs, Ht, HΨ⟩
    simp at HMs Ht HΨ; subst HMs Ht
    unfold wpiF'; apply BIFUpdate.ne.ne
    cases t1 <;> simp
    case ret r => exact BIFUpdate.ne.ne <| HΨ r
    case tau t' => apply Hwp.ne; exact ⟨.rfl, .rfl, HΨ⟩
    case vis i k =>
      apply OFE.NonExpansive₂.ne <;> intro a
      · apply Hwp.ne; exact ⟨.rfl, .rfl, HΨ⟩
      · apply Hwp.ne; exact ⟨.rfl, .rfl, .rfl⟩

/-- `wpi` is a weakest precondition for `ITree` -/
def wpi {E R} (H : IHandler PROP E) (Ms Me : CoPset) (t : ITree E R) (Φ : R → PROP) : PROP :=
  bi_least_fixpoint (wpiF' H Me) (⟨Ms⟩, t, Φ)

instance {R Ms Me} {t : ITree E R} : OFE.NonExpansive (wpi H Ms Me t) := by
  refine ⟨fun {n Φ₁ Φ₂} HΦ => OFE.NonExpansive.ne (f := bi_least_fixpoint (wpiF' H Me)) ?_⟩
  exact ⟨rfl, rfl, HΦ⟩

end wp_itree_def

syntax (name := wpiNotation) "WPi " term:20 " @> " term:20 "; " term:max ("," term:max)? wpPostcond : term

@[macro wpiNotation]
meta def wpiMacro : Lean.Macro := fun stx => do
  match stx with
  | `(WPi $t:term @> $H:term; $Ms:term, $Me:term $postcond:wpPostcond) =>
    let (Φ, _) ← Iris.parseWpPostcond postcond
    `(wpi (H := $H) $Ms $Me $t $Φ)
  | `(WPi $t:term @> $H:term; $M:term $postcond:wpPostcond) =>
    let (Φ, _) ← Iris.parseWpPostcond postcond
    `(wpi (H := $H) $M $M $t $Φ)
  | _ => Lean.Macro.throwUnsupported

delab_rule wpi
  | `($_ $H $Ms $Me $t (fun $v:ident => $Q)) => do
    let inner ← Iris.unexpandWpPostcondInner (← `(fun $v => $Q))
    if Ms == Me then `(WPi $t @> $H;$Ms {{ $inner }})
    else `(WPi $t @> $H;$Ms,$Me {{ $inner }})
  | `($_ $H $Ms $Me $t $Φ) => do
    let inner ← Iris.unexpandWpPostcondInner Φ
    if Ms == Me then `(WPi $t @> $H;$Ms {{ $inner }})
    else `(WPi $t @> $H;$Ms, $Me {{ $inner }})

section wpi_unfold

variable {E} {Ms Me : CoPset} {H : IHandler PROP E}

theorem wpi_unfold {R} (t : ITree E R) Φ :
    WPi t @> H;Ms,Me {{ Φ }} ⊣⊢ wpiF H (fun Ms t Φ => WPi t @> H;Ms,Me {{ Φ }}) Ms Me t Φ :=
  equiv_iff.mp (least_fixpoint_unfold _)

theorem fupd_wpi_empty {R t} (Φ : R → PROP) :
    WPi t @> H;Ms,Me {{ Φ }} ⊣⊢ |={Ms, ∅}=> WPi t @> H;∅,Me {{ Φ }} := by
  rw [(wpi_unfold _ _).to_eq]
  unfold wpiF
  isplit <;> iintro >Hwp
  · imodintro
    iapply wpi_unfold
    unfold wpiF; imodintro
    itrivial
  · ihave H := wpi_unfold $$ Hwp
    unfold wpiF
    itrivial

section instances

open ProofMode

instance elimModal_fupd_wpi p E1 E2 E3 (P : PROP) :
    ElimModal True p io false
      iprop(|={E1,E2}=> P) P
      iprop(WPi t @> H;E1,E3 {{Φ}}) iprop(WPi t @> H;E2,E3 {{Φ}}) where
  elim_modal _ := by
    cases p
    · iintro ⟨HP, Hwand⟩
      iapply fupd_wpi_empty
      icases intuitionisticallyIf_elim $$ HP with HP
      imod HP; ihave Hwp := Hwand $$ HP
      iapply fupd_wpi_empty $$ Hwp
    · iintro ⟨#HP, Hwand⟩
      iapply fupd_wpi_empty
      icases intuitionisticallyIf_elim $$ HP with >HP
      ihave Hwp := Hwand $$ HP
      iapply fupd_wpi_empty $$ Hwp

instance elimModal_wpi_wpi p H1 H2 (t1 : ITree E1 R1) (t2 : ITree E2 R2) Ms Me1 Me2 Φ1 Φ2 :
    ElimModal (PROP:=PROP) True p io false
      iprop(WPi t1 @> H1;Ms,Me1 {{Φ1}}) iprop(WPi t1 @> H1;∅,Me1 {{Φ1}})
      iprop(WPi t2 @> H2;Ms,Me2 {{Φ2}}) iprop(WPi t2 @> H2;∅,Me2 {{Φ2}}) where
  elim_modal _ := by
    cases p
    · iintro ⟨HΦ, Hwand⟩
      iapply fupd_wpi_empty
      icases fupd_wpi_empty $$ HΦ with >HΦ
      imodintro
      iapply Hwand $$ HΦ
    · iintro ⟨HΦ, Hwand⟩
      icases intuitionisticallyIf_elim $$ HΦ with HΦ
      iapply fupd_wpi_empty
      icases fupd_wpi_empty $$ HΦ with >HΦ
      imodintro
      iapply Hwand $$ HΦ

instance elimModal_wpi_fupd p E1 E2 E3 (P : PROP) :
    ElimModal True p io false
      iprop(WPi t @> H;E1,E3 {{Φ}}) iprop(WPi t @> H;∅,E3 {{Φ}})
      iprop(|={E1,E2}=> P) iprop(|={∅,E2}=> P) where
  elim_modal _ := by
    cases p
    · iintro ⟨HΦ, Hwand⟩
      icases fupd_wpi_empty $$ HΦ with >HΦ
      iapply Hwand $$ HΦ
    · iintro ⟨HΦ, Hwand⟩
      icases intuitionisticallyIf_elim $$ HΦ with HΦ
      icases fupd_wpi_empty $$ HΦ with >HΦ
      iapply Hwand $$ HΦ

end instances

theorem fupd_wpi (Φ : R → PROP) :
    WPi t @> H;Ms,Me {{ Φ }} ⊣⊢ |={Ms}=> WPi t @> H;Ms,Me {{ Φ }} := by
  isplit <;> iintro Hwp
  · imodintro; iframe
  · imod Hwp; iframe

theorem wpi_pure_fupd {R} (Φ : R → PROP) (r : R) :
    WPi (pure r) @> H;Ms,Me {{ Φ }} ⊣⊢ |={Ms, Me}=> Φ r := by
  rw [(wpi_unfold _ _).to_eq]
  simp [wpiF]
  isplit
  · iintro >$
  · iintro >_
    iapply fupd_mask_intro (by simp)
    iintro >Hemp !>
    iframe

theorem wpi_pure {R} (M : CoPset) (Φ : R → PROP) (r : R) :
    Φ r ⊢ WPi (pure r) @> H; M {{ Φ }} := by
  iintro HΦ
  iapply wpi_pure_fupd
  imodintro
  iframe

theorem wpi_tau {R} (Φ : R → PROP) (t : ITree E R) :
    WPi t.tau @> H;Ms,Me {{ Φ }} ⊣⊢ WPi t @> H;Ms,Me {{ Φ }} := by
  rw [(wpi_unfold _ _).to_eq]
  simp [wpiF]
  isplit <;> iintro >$ //

theorem wpi_vis {R} (Φ : R → PROP) (i : E.I) (k : E.O i → ITree E R) :
    WPi (ITree.vis i k) @> H;Ms,Me {{ Φ }} ⊣⊢
    |={Ms, ∅}=> H.ihandle i
      (fun a => WPi (k a) @> H; ∅,Me {{ Φ }})
      (fun a => WPi (k a) @> H; ∅,Me {{ _x, False }}) :=
  wpi_unfold _ _

theorem wpi_trigger_bind {E' A} [E' -< E] (H' : IHandler PROP E') [InH H' H]
    (i : E'.I) (k : E'.O i → ITree E A) (Φ : A → PROP) :
    (|={Ms, ∅}=> H'.ihandle i
      (fun a => WPi (k a) @> H; ∅,Me {{ Φ }})
      (fun a => WPi (k a) @> H; ∅,Me {{ _x, False }})) -∗
    WPi (E'.trigger i >>= k) @> H; Ms, Me {{ Φ }} := by
  iintro >HH
  simp [Effect.trigger]
  iapply wpi_vis
  imodintro
  iapply H.ihandle_mono
  · iintro %r $
  · iintro !> %a $
  · iapply InH.is_inH $$ HH

theorem wpi_trigger {E'} [E' -< E] (H' : IHandler PROP E') [InH H' H]
    (i : E'.I) (Φ : E'.O i → PROP) :
    (|={Ms, ∅}=> H'.ihandle i
      (fun a => iprop% |={∅, Me}=> Φ a)
      (fun _ => iprop% False)) -∗
    WPi (E'.trigger i) @> H; Ms,Me {{ Φ }} := by
  iintro HH
  unfold Effect.trigger
  iapply wpi_vis
  imod HH
  imodintro
  iapply H.ihandle_mono
  · iintro %r HΦ
    iapply wpi_pure_fupd $$ [$]
  · iintro !> %a ⟨⟩
  · iapply InH.is_inH $$ HH

end wpi_unfold

section wpi_induction

variable {E R} {Ms Me : CoPset} {H : IHandler PROP E}

-- TODO: Is this version ever useful?
theorem wpi_ind_mask (G : CoPset → ITree E R → (R → PROP) → PROP)
   [∀ Ms t, OFE.NonExpansive (G Ms t)] :
    □ (∀ Ms t Φ, wpiF H (fun Ms' t' Ψ => iprop% G Ms' t' Ψ ∧ WPi t' @> H;Ms',Me {{ Ψ }}) Ms Me t Φ -∗ G Ms t Φ) -∗
    ∀ Ms t Φ, WPi t @> H;Ms,Me {{ Φ }} -∗ G Ms t Φ := by
  iintro #HPre %Ms %t %Φ Hwp; unfold wpi
  let G' : (DiscreteO CoPset × _ × _) → _ := fun ⟨⟨Ms⟩, t, Φ⟩ => G Ms t Φ
  haveI : OFE.NonExpansive G' := by
    refine ⟨fun _ ⟨⟨Ms1⟩, _, _⟩ ⟨⟨Ms2⟩, _, _⟩ ⟨rfl, Ht, HΦ⟩ => ?_⟩
    cases Ht; exact OFE.NonExpansive.ne HΦ
  iapply least_fixpoint_ind (wpiF' H Me) G' $$ [] %⟨⟨Ms⟩, t, Φ⟩ Hwp
  iintro !> %p HwpiF
  iapply HPre
  unfold wpiF'
  iapply wpiF_mono $$ [] HwpiF
  iintro !> %_ %_ $

variable (G : ITree E R → (R → PROP) → PROP) [∀ t, OFE.NonExpansive (G t)]

theorem wpi_ind :
    □ (∀ t Φ, wpiF H (fun Ms' t' Ψ => iprop% G t' Ψ ∧ WPi t' @> H;Ms',Me {{ Ψ }}) ∅ Me t Φ -∗ G t Φ) ⊢
    ∀ t Φ, WPi t @> H;∅,Me {{ Φ }} -∗ G t Φ := by
  iintro #HPre %t %Φ Hwp
  letI G' := fun (Ms : CoPset) t Φ => iprop(<affine> ⌜Ms = ∅⌝ -∗ G t Φ)
  haveI : ∀ Ms t, OFE.NonExpansive (G' Ms t) := fun _ _ =>
    ⟨fun {_ _ _} HΦ => wand_ne.ne .rfl (OFE.NonExpansive.ne HΦ)⟩
  iapply wpi_ind_mask G' $$ [] Hwp [//]
  iintro !> %Ms %t %Φ Hwpi %rfl
  iapply HPre
  iapply wpiF_mono $$ [] Hwpi
  iintro !> %_ %_ HG
  isplit
  · icases HG with ⟨HG, -⟩
    iapply HG $$ [//]
  · icases HG with ⟨-, $⟩

theorem wpi_iter :
    □ (∀ t Φ, wpiF H (fun _ => G) ∅ Me t Φ -∗ G t Φ) ⊢
    ∀ t Φ, WPi t @> H;∅,Me {{ Φ }} -∗ G t Φ := by
  iintro #HRet %t %Φ
  iapply wpi_ind $$ []
  iintro !> %t %Φ HwpiF
  iapply HRet
  iapply wpiF_mono $$ [] HwpiF
  iintro !> %_ %_ ⟨$, -⟩

-- FIXME: naming
theorem wpi_iter' :
    □ (∀ Φ r, (|={∅, Me}=> Φ r) -∗ G (pure r) Φ) -∗
    □ (∀ Φ t, (|={∅}=> G t Φ) -∗ G (ITree.tau t) Φ) -∗
    □ (∀ Φ i k, (|={∅}=> H.ihandle i (fun a => G (k a) Φ)
        (fun a => G (k a) (fun _ => iprop% False))) -∗ G (ITree.vis i k) Φ) -∗
    ∀ t Φ, WPi t @> H;∅,Me {{ Φ }} -∗ G t Φ := by
  iintro #HPure #HTau #HVis %t %Φ
  iapply wpi_iter $$ []
  iintro !> %t %Φ HwpiF
  unfold wpiF
  cases t <;> simp
  · iapply HPure
    imod HwpiF with $
  · iapply HTau $$ [$]
  · iapply HVis $$ [$]

end wpi_induction

section wpi_lemmas

variable {E R} {Ms Me : CoPset} {H : IHandler PROP E} {t : ITree E R}

theorem wpi_wand (Φ Ψ : R → PROP) :
    WPi t @> H;Ms,Me {{ Φ }} -∗
    (∀ r, Φ r -∗ Ψ r) -∗
    WPi t @> H;Ms,Me {{ Ψ }} := by
  iintro >Hwp Hwand
  letI G := fun t (Φ : R → PROP) => iprop% ∀ Ψ, (∀ r, Φ r -∗ Ψ r) -∗ WPi t @> H;∅,Me {{ Ψ }}
  haveI : ∀ t, OFE.NonExpansive (G t) := fun t => ⟨fun _ _ _ Hx => forall_ne fun Ψ => wand_ne.ne
    (forall_ne fun r => wand_ne.ne (Hx r) .rfl) .rfl⟩
  iapply wpi_iter' G $$ [] [] [] Hwp Hwand
  · iintro !> %Φ %r >Hwpi %Ψ Hwand
    iapply wpi_pure
    iapply Hwand $$ [$]
  · iintro !> %Φ %t >Hwpi %Ψ Hwand
    iapply wpi_tau
    iapply Hwpi $$ Hwand
  · iintro !> %Φ %i %k >Hwpi %Ψ Hwand
    iapply wpi_vis
    imodintro
    iapply H.ihandle_mono $$ [Hwand] [] Hwpi
    · iintro %_ HG
      iapply HG $$ Hwand
    · iintro !> %_ HG
      iapply HG
      itrivial

theorem wpi_fupd_empty_mpr (Φ : R → PROP) :
    WPi t @> H; Ms, ∅ {{ v, |={∅, Me}=> Φ v }} ⊢
    WPi t @> H; Ms, Me {{ Φ }} := by
  letI G := fun t (Ψ : R → PROP) =>
    iprop% ∀ Φ, (∀ r, Ψ r -∗ |={∅, Me}=> Φ r) -∗ WPi t @> H;∅,Me {{ Φ }}
  haveI : ∀ t, OFE.NonExpansive (G t) := fun t => ⟨fun _ _ _ HΨ => forall_ne fun Φ => wand_ne.ne
    (forall_ne fun r => wand_ne.ne (HΨ r) .rfl) .rfl⟩
  iintro >Hwp
  iapply wpi_iter' G $$ [] [] [] Hwp
  · iintro !> %Ψ %r >HΨ %Φ Hwand
    iapply wpi_pure_fupd
    iapply Hwand $$ [$]
  · iintro !> %Ψ %t >HΨ %Φ Hwand
    iapply wpi_tau
    iapply HΨ $$ [$]
  · iintro !> %Ψ %i %k >HΨ %Φ Hwand
    iapply wpi_vis
    imodintro
    iapply H.ihandle_mono $$ [Hwand] [] HΨ
    · iintro %_ HG
      iapply HG $$ [$]
    · iintro !> %_ HG
      iapply HG
      iintro %_ ⟨⟩
  iintro %r $

theorem wpi_fupd_empty_mp (Φ : R → PROP) :
    WPi t @> H; Ms, Me {{ Φ }} ⊢
    WPi t @> H; Ms, ∅ {{ v, |={∅, Me}=> Φ v }} := by
  letI G := fun t (Ψ : R → PROP) => WPi t @> H; ∅,∅ {{ v, |={∅, Me}=> Ψ v }}
  haveI : ∀ t, OFE.NonExpansive (G t) := fun t =>
    ⟨fun _ _ _ HΨ => OFE.NonExpansive.ne (f := wpi H ∅ ∅ t) fun v => BIFUpdate.ne.ne (HΨ v)⟩
  iintro >Hwp
  iapply wpi_iter' G $$ [] [] [] Hwp
  · iintro !> %Ψ %r HΨ
    iapply wpi_pure
    iframe
  · iintro !> %Ψ %t >HΨ
    iapply wpi_tau
    iframe
  · iintro !> %Ψ %i %k >HΨ
    iapply wpi_vis
    imodintro
    iapply H.ihandle_mono $$ [] [] HΨ
    · iintro %_ $
    · iintro !> %_ _
      iapply wpi_fupd_empty_mpr
      iapply wpi_wand $$ [$]
      iintro %_ >⟨⟩

theorem wpi_fupd_empty (Φ : R → PROP) :
    WPi t @> H; Ms, Me {{ Φ }} ⊣⊢ WPi t @> H; Ms, ∅ {{ v, |={∅, Me}=> Φ v }} :=
  ⟨wpi_fupd_empty_mp _, wpi_fupd_empty_mpr _⟩

theorem wpi_fupd (Φ : R → PROP) :
    WPi t @> H; Ms, Me {{ Φ }} ⊣⊢ WPi t @> H; Ms, Me {{ v, |={Me}=> Φ v }} := by
  isplit <;> iintro Hwp
  · iapply wpi_wand $$ Hwp
    iintro %_ $ //
  · iapply wpi_fupd_empty
    iapply wpi_wand $$ [Hwp]
    iapply wpi_fupd_empty $$ Hwp
    iintro %_ > > $ //

theorem wpi_bind_strong {A} M' t (k : A → ITree E R) (Φ : R → PROP) :
    WPi t @> H; Ms, M' {{ r, WPi (k r) @> H;M',Me {{ Φ }} }} ⊢
    WPi (t >>= k) @> H; Ms, Me {{ Φ }} := by
  letI G := fun t (Φ : A → PROP) =>
    iprop%∀ Ψ, (∀ r, Φ r -∗ WPi k r @> H; M', Me {{ Ψ }}) -∗ WPi t >>= k @> H; ∅, Me {{ Ψ }}
  haveI : ∀ t, OFE.NonExpansive (G t) := fun t =>
    ⟨fun n Φ1 Φ2 HΦ => forall_ne fun Ψ => wand_ne.ne (forall_ne fun r => wand_ne.ne (HΦ r) .rfl) .rfl⟩
  iintro >Hwp
  iapply wpi_iter' G $$ [] [] [] Hwp
  · iintro !> %Φ %r >Hwpi %Ψ Hwand
    simp
    iapply Hwand $$ [$]
  · iintro !> %Φ %t >Hwpi %Ψ Hwand
    simp
    iapply wpi_tau
    iapply Hwpi $$ Hwand
  · iintro !> %Φ %i %k >Hwpi %Ψ Hwand
    simp
    iapply wpi_vis
    imodintro
    iapply H.ihandle_mono $$ [Hwand] [] Hwpi
    · iintro %_ HG
      iapply HG $$ Hwand
    · iintro !> %_ HG
      iapply HG
      iintro %_ ⟨⟩
  iintro %_ $

/-- Specialized version where M' = Ms. This is especially useful for the Ms = Me case. -/
theorem wpi_bind {A} t (k : A → ITree E R) (Φ : R → PROP) :
    WPi t @> H; Ms {{ r, WPi (k r) @> H;Ms,Me {{ Φ }} }} ⊢ WPi (t >>= k) @> H; Ms, Me {{ Φ }} :=
  wpi_bind_strong _ _ _ _

end wpi_lemmas

section wp_itree_invariant

variable {E R} {Ms Me : CoPset} {H : IHandler PROP E}

/-- Re-mask a `WPi`: change the start mask from `Ms` to `Ms'` up front, and the end mask from `Me'` back to `Me` in the postcondition. -/
theorem fupd_wpi_fupd Ms' Me' t (Φ : R → PROP) :
    (|={Ms, Ms'}=> WPi t @> H; Ms', Me' {{ v, |={Me', Me}=> Φ v}}) -∗
    WPi t @> H; Ms, Me {{ Φ }} := by
  iintro > >Hwp
  icases wpi_fupd_empty $$ Hwp with Hwp
  iapply wpi_fupd_empty
  iapply wpi_wand $$ Hwp
  iintro %_ > $

theorem wpi_atomic t (Φ : R → PROP) :
    (|={Ms, ∅}=> WPi t @> H; ∅ {{ v, |={∅, Me}=> Φ v}}) ⊣⊢
    WPi t @> H; Ms, Me {{ Φ }} := by
  isplit
  · iapply fupd_wpi_fupd
  · iintro >Hwp !>
    iapply wpi_fupd_empty $$ Hwp

theorem wpi_atomic_false (t : ITree E R) :
    (|={Ms, ∅}=> WPi t @> H; ∅ {{ _v, False}}) -∗
    WPi t @> H; Ms, Me {{ _v, False}} := by
  iintro >Hwp
  iapply wpi_atomic
  imodintro
  iapply wpi_wand $$ Hwp
  iintro %_ ⟨⟩

theorem wpi_mask_mono_start {Ms'} [BIAffine PROP] t (Φ : R → PROP) :
    Ms ⊆ Ms' →
    WPi t @> H; Ms, Me {{ Φ }} -∗
    WPi t @> H; Ms', Me {{ Φ }} := by
  iintro %Hsub Hwp
  ihave Hwp := fupd_wpi_empty $$ Hwp
  iapply fupd_wpi_empty
  imod (fupd_mask_subseteq Hsub) with -
  iexact Hwp

theorem wpi_mask_mono_end {Me'} [BIAffine PROP] t (Φ : R → PROP) :
    Me' ⊆ Me →
    WPi t @> H; Ms, Me {{ Φ }} -∗
    WPi t @> H; Ms, Me' {{ Φ }} := by
  iintro %Hsub Hwp
  iapply fupd_wpi_fupd
  imodintro
  iapply wpi_wand $$ Hwp
  iintro %_ HΦ
  imod (fupd_mask_subseteq Hsub) with -
  iframe

theorem wpi_acc {X} M (α β : X → PROP) (γ : X → Option PROP)
    t (Φ : R → PROP) :
    (|={Ms, M}=> ∃ x, α x ∗ (β x -∗ |={M, Ms}=> (γ x).getD emp)) -∗
    (∀ x, α x -∗ WPi t @> H; M {{ v, |={M}=> β x ∗ (γ x -∗? |={Ms, Me}=> Φ v) }}) -∗
    WPi t @> H; Ms, Me {{ Φ }} := by
  iintro Hacc Hinner
  iapply fupd_wpi_fupd M M
  imod Hacc with ⟨%x, Hα, Hclose⟩
  imodintro
  iapply wpi_wand $$ [Hinner Hα]
  · iapply Hinner $$ Hα
  · iintro %v >⟨Hβ, HΦ⟩
    imod Hclose $$ Hβ
    iapply HΦ
    itrivial

section instances

open ProofMode

instance elimAcc_wpi t (Φ : R → PROP) {X} M (α β : X → PROP) (γ : X → Option PROP) :
    ElimAcc True (fupd Ms M) (fupd M Ms) α β γ
      (WPi t @> H; Ms, Me {{ Φ }})
      (fun x => WPi t @> H; M {{ v, |={M}=> β x ∗ (γ x -∗? |={Ms, Me}=> Φ v) }}) where
  elim_acc _ := by
    unfold accessor
    iintro Hinner Hacc
    iapply wpi_acc M α β γ $$ Hacc Hinner

instance isExcept0_wpi t (Φ : R → PROP) : IsExcept0 (WPi t @> H; Ms, Me {{ Φ }}) where
  is_except0 := by
    iintro Hwp
    iapply fupd_wpi_empty
    imod Hwp with > >$
    itrivial

end instances

end wp_itree_invariant

section wp_itree_translation

-- `f` can interpret each event `E1` as an `itree E2 E1.I`, as a way to
-- "translate" from events `E1` to `E2`
variable {E1 E2 : Effect} {Ms Me : CoPset}
  {PROP : Type _} [BI PROP] [BIFUpdate PROP]
  {H1 : IHandler PROP E1} {H2 : IHandler PROP E2}
  (f : (i : E1.I) → ITree E2 (E1.O i))

/-- Translate a WPi proof across handlers by interpreting each `E₁` event as an `E₂` itree. -/
theorem wpi_translation {R} (t : ITree E1 R) (Φ : R → PROP) :
    WPi t @> H1; Ms, Me {{ Φ }} -∗
    □ (∀ i (k : E1.O i → ITree E1 R) Ψ,
      H1.ihandle i
        (fun a => WPi ITree.interp f (k a) @> H2; ∅,Me {{ Ψ }})
        (fun a => WPi ITree.interp f (k a) @> H2; ∅,Me {{ _v, False }}) -∗
      WPi (f i >>= fun a => ITree.interp f (k a)) @> H2; ∅,Me {{ Ψ }}) -∗
    WPi ITree.interp f t @> H2; Ms, Me {{ Φ }} := by
  letI G : ITree E1 R → (R → PROP) → PROP := fun t Φ => WPi ITree.interp f t @> H2; ∅,Me {{Φ}}
  iintro >Hwp #HH
  iapply (wpi_iter' G) $$ [] [] [] Hwp
  · iintro !> %Φ %r >Hret
    simp only [interp_pure]
    iapply wpi_pure $$ [$]
  · iintro !> %Φ %t >Htau
    simp only [interp_tau]
    iapply wpi_tau $$ [$]
  · iintro !> %Φ %i %k >Hvis
    simp only [interp_vis]
    iapply HH $$ [$]

/-- A sequential special case of `wpi_translation` with a simpler handler-side premise. -/
theorem wpi_translation_seq {R} (t : ITree E1 R) (Φ : R → PROP) :
    WPi t @> H1; Ms,Me {{ Φ }} -∗
    □ (∀ i Ψ, H1.ihandle i Ψ (fun _ => iprop% True) -∗ WPi (f i) @> H2; ∅ {{ Ψ }}) -∗
    WPi (ITree.interp f t) @> H2; Ms,Me {{ Φ }} := by
  iintro Hwp #Hwand
  iapply wpi_translation $$ [$]
  iintro !> %i %k %Ψ Hh
  iapply wpi_bind
  iapply Hwand
  iapply H1.ihandle_mono $$ [] [] Hh
  · iintro %a $
  · iintro !> %t Hwp //

end wp_itree_translation

section wp_itree_mono

variable {E : Effect} {Ms Me : CoPset}
  {H1 : IHandler PROP E} {H2 : IHandler PROP E}
  [Hwand : WandH H1 H2]

theorem wpi_wandH {R} (t : ITree E R) (Φ : R → PROP) :
    WPi t @> H1; Ms, Me {{ Φ }} ⊢ WPi t @> H2; Ms, Me {{ Φ }} := by
  iintro Hwp
  rw (occs:=[2]) [show (t = t.interp (fun i => E.trigger i)) by simp]
  iapply wpi_translation $$ Hwp
  iintro !> %i %k %Ψ Hh
  simp [Effect.trigger]
  iapply wpi_vis
  imodintro
  iapply Hwand.is_wandH
  iapply H1.ihandle_mono i $$ [] [] Hh
  · iintro %a $
  · iintro !> %a $

end wp_itree_mono

section wp_itree_inH

variable {E1 E2 : Effect} {Ms Me : CoPset} [BIAffine PROP]
  {H1 : IHandler PROP E1} {H2 : IHandler PROP E2}
  [sub : E1 -< E2] [Hin : InH H1 H2]

theorem wpi_inH {R} (t : ITree E1 R) (Φ : R → PROP) :
    WPi t @> H1; Ms, Me {{ Φ }} ⊣⊢
    WPi (t.interp (fun i => E1.trigger i)) @> H2; Ms, Me {{ Φ }} := by
  isplit
  · iintro Hwp
    iapply wpi_translation $$ Hwp
    iintro !> %i %k %Ψ Hh
    iapply wpi_trigger_bind
    imodintro
    iapply H1.ihandle_mono $$ [] [] Hh
    · iintro %a $
    · iintro !> %a $
  · letI G : ITree E2 R → (R → PROP) → PROP := fun u Ψ =>
      iprop% ∀ t', ⌜ITree.interp (fun i => E1.trigger i) t' = u⌝ -∗ (WPi t' @> H1; ∅ {{ Ψ }})
    haveI : ∀ t, OFE.NonExpansive (G t) := fun t =>
      ⟨fun _ _ _ Hx => forall_ne fun t' => wand_ne.ne .rfl <| OFE.NonExpansive.ne Hx⟩
    ihave Hgen : (∀ t Ψ, (WPi t @> H2; ∅ {{ Ψ }}) -∗ G t Ψ) $$ []
    iapply wpi_iter' G
    · iintro !> %Φ %r >HΦ %t' %Heq
      obtain rfl := interp_pure_inv Heq
      iapply wpi_pure $$ HΦ
    · iintro !> %Ψ %u >Hu %t' %Heq
      rcases interp_tau_inv Heq with ⟨t1, rfl, rfl⟩
      iapply wpi_tau
      iapply Hu $$ %t1 [//]
    · iintro !> %Ψ %i %k >Hik %t' %Heq
      rcases interp_vis_inv Heq with ⟨i', k', rfl, rfl, rfl⟩
      iapply wpi_vis
      imodintro
      iapply Hin.is_inH
      iapply H2.ihandle_mono (Subeffect.map i').fst $$ [] [] Hik
      · iintro %a HG
        iapply HG
        itrivial
      · iintro !> %a HG
        iapply HG
        itrivial
    iintro >Hwp
    iapply wpi_fupd_empty
    ihave Hwp := wpi_fupd_empty $$ Hwp
    iapply Hgen $$ Hwp
    itrivial

end wp_itree_inH

end IrisITree
