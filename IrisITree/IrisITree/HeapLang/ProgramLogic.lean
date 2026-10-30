/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunsong Yang, Michael Sammler
-/

module

public import IrisITree.Core.Wpi
public import IrisITree.Effects
public import IrisITree.HeapLang.Semantics
public import Iris.BI.WeakestPre
public import Iris.Instances.IProp
public import Iris.Instances.Lib.FUpd

@[expose] public section
namespace IrisITree

open Iris Iris.HeapLang ITree ITree.Effects

class heaplangHGpreS (GF : BundledGFunctors) where
  heaplangH_heapHG : heapHGpreS GF Loc Val

attribute [reducible, instance] heaplangHGpreS.heaplangH_heapHG

class heaplangHGS (GF : BundledGFunctors) where
  heaplangH_heapHGS : heapHGS GF Loc Val

attribute [reducible, instance] heaplangHGS.heaplangH_heapHGS

section handler

variable {GF} [InvGS GF] [heaplangHGS GF]

/-- HeapLang's logical handler: one handler per effect in `heaplangE`, with steps interpreted by
`sm`. -/
def heaplangH (sm : IProp GF → IProp GF) [StepMod sm] : IHandler (IProp GF) heaplangE :=
  concH ⊕ₕ heapH ⊕ₕ failH ⊕ₕ demonicH Loc ⊕ₕ stepH sm

instance {sm : IProp GF → IProp GF} [StepMod sm] : InH concH (heaplangH sm) := by
  unfold heaplangH
  infer_instance

instance {sm : IProp GF → IProp GF} [StepMod sm] :
    InH (heapH (Loc := Loc) (Val := Val)) (heaplangH sm) := by
  unfold heaplangH
  infer_instance

instance {sm : IProp GF → IProp GF} [StepMod sm] : InH failH (heaplangH sm) := by
  unfold heaplangH
  infer_instance

instance {sm : IProp GF → IProp GF} [StepMod sm] : InH (demonicH Loc) (heaplangH sm) := by
  unfold heaplangH
  infer_instance

instance {sm : IProp GF → IProp GF} [StepMod sm] : InH (stepH sm) (heaplangH sm) := by
  unfold heaplangH
  infer_instance

instance : WandH (heaplangH (GF := GF) id) (heaplangH (GF := GF) BI.later) := by
  unfold heaplangH
  infer_instance

/-- HeapLang's `WP`. `Wp` receives its mode as a plain value, so the mode is the proof
`h : StepMod sm` itself; its type tells which step modality `sm` is used.
Write `WP e @ h; M {{ Φ }}`, e.g. `WP e @ StepMod.stepMod_later; M {{ Φ }}`. -/
instance wp_heaplang (sm : IProp GF → IProp GF) : Wp (IProp GF) Exp Val (StepMod sm) where
  wp h M e Φ := WPi e.denote @> @heaplangH _ _ _ sm h; M {{ Φ }}

section proofmode_instances

open ProofMode

variable {sm : IProp GF → IProp GF} [hmono : StepMod sm]

instance elimAcc_wp (e : Exp) (Φ : Val → IProp GF) {X} (Ms M : CoPset) (α β : X → IProp GF)
    (γ : X → Option (IProp GF)) :
    ElimAcc True (fupd Ms M) (fupd M Ms) α β γ (WP e @ hmono; Ms {{ Φ }})
      (fun x => WP e @ hmono; M {{ v, |={M}=> β x ∗ (γ x -∗? |={Ms}=> Φ v) }}) :=
  elimAcc_wpi (H := heaplangH sm) (Ms := Ms) (Me := Ms) e.denote Φ M α β γ

instance isExcept0_wp (e : Exp) (Φ : Val → IProp GF) (M : CoPset) :
    IsExcept0 (WP e @ hmono; M {{ Φ }}) :=
  isExcept0_wpi (H := heaplangH sm) (Ms := M) (Me := M) e.denote Φ

end proofmode_instances

end handler

section wpi_rules

variable {GF} [InvGS GF] [heaplangHGS GF] {sm : IProp GF → IProp GF} [hmono : StepMod sm]

theorem wpi_step_pure E (v : Val) (Φ : Val → IProp GF) :
    sm (Φ v) -∗
    WPi (do
      step
      pure v) @> heaplangH sm; E {{ Φ }} := by
  iintro HΦ
  iapply wpi_bind; iapply wpi_step
  iapply StepMod.map (sm := sm) $$ HΦ
  iintro HΦ !>
  iapply wpi_pure $$ HΦ

theorem wpi_yieldIfNotVal (e : Exp) (Φ : Unit → IProp GF) :
    Φ () -∗
    WPi e.yieldIfNotVal @> heaplangH sm; ⊤ {{ Φ }} := by
  cases e <;> simp only [Exp.yieldIfNotVal]
  · iintro HΦ; iapply wpi_pure $$ [$]
  all_goals
    iintro HΦ; iapply wpi_yield $$ [$]

theorem wpi_cont (e : Exp) (Φ : Val → IProp GF) :
    sm (WP e @ hmono ; ⊤ {{ Φ }}) -∗
    WPi (do
      step
      e.yieldIfNotVal
      e.denote
    ) @> heaplangH sm; ⊤ {{ Φ }} := by
  iintro Hwp; iapply wpi_bind
  iapply wpi_step
  iapply StepMod.map (sm := sm) $$ Hwp
  iintro Hwp !>; iapply wpi_bind
  iapply wpi_yieldIfNotVal; iframe

theorem wpi_denoteYield (e : Exp) (Φ : Val → IProp GF) :
    WPi e.denote @> heaplangH sm; ⊤ {{ Φ }} -∗
    WPi (if e.isVal then e.denote else yieldAfter e.denote) @> heaplangH sm; ⊤ {{ Φ }} := by
  split
  · iintro Hwp; iexact Hwp
  · rw [ConcE.yieldAfter]
    iintro Hwp; iapply wpi_bind; iapply wpi_wand $$ Hwp
    iintro %v HΦ; iapply wpi_bind; iapply wpi_yield
    iapply wpi_pure $$ HΦ

end wpi_rules

section wp_rules

variable {GF} [InvGS GF] [heaplangHGS GF] {sm : IProp GF → IProp GF} [hmono : StepMod sm]

theorem wp_unfold {M : CoPset} (e : Exp) (Φ : Val → IProp GF) :
    WP e @ hmono; M {{ Φ }} = WPi e.denote @> heaplangH sm; M {{ Φ }} := rfl

/-- The identity (total) WP implies the later (partial) WP. -/
theorem wp_later_weaken {M : CoPset} (e : Exp) (Φ : Val → IProp GF) :
    WP e @ (StepMod.stepMod_id (PROP := IProp GF)); M {{ Φ }} -∗
    WP e @ (StepMod.stepMod_later (PROP := IProp GF)); M {{ Φ }} := by
  simp only [wp_unfold]
  iintro Hwp
  iapply wpi_wandH $$ Hwp

-- theorem wp_bind (K : List ECtxItem) (e : Exp) (Φ : Val → IProp GF) :
--     WP e @ hmono; ⊤ {{ v,
--       WP (ProgramLogic.fill K (Exp.ofVal (Expr := Exp) v)) @ hmono; ⊤ {{ Φ }}
--     }} -∗
--     WP (ProgramLogic.fill K e) @ hmono; ⊤ {{ Φ }} := by
--   sorry

theorem wp_wand {M : CoPset} (e : Exp) (Φ Ψ : Val → IProp GF) :
    WP e @ hmono ; M {{ Φ }} -∗
    (∀ v, Φ v -∗ Ψ v) -∗
    WP e @ hmono ; M {{ Ψ }} := by
  simp only [wp_unfold]
  apply wpi_wand

theorem wp_frame_l {M : CoPset} (e : Exp) (Φ : Val → IProp GF) :
    P ∗ WP e @ hmono; M {{ Φ }} -∗ WP e @ hmono; M {{v , P ∗ Φ v}} := by
  iintro ⟨HP, Hwp⟩
  iapply wp_wand $$ Hwp [HP]
  iintro %_ _; iframe

theorem wp_atomic E1 E2 (e : Exp) (Φ : Val → IProp GF) :
    (|={E1,E2}=> WP e @ hmono ; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ hmono ; E1 {{ Φ }} := by
  simp only [wp_unfold]
  iintro > >Hwp
  iapply wpi_fupd_empty
  ihave Hwp := wpi_fupd_empty $$ Hwp
  iapply wpi_wand $$ Hwp
  iintro %_ > > $

theorem fupd_wp {M : CoPset} (e : Exp) (Φ : Val → IProp GF) :
    (|={M}=> WP e @ hmono ; M {{ v, Φ v }}) ⊢ WP e @ hmono ; M {{ Φ }} := by
  simp only [wp_unfold]
  iapply (fupd_wpi _).2

theorem wp_fupd {M : CoPset} (e : Exp) (Φ : Val → IProp GF) :
    (WP e @ hmono ; M {{ v, |={M}=> Φ v }}) ⊢ WP e @ hmono ; M {{ Φ }} := by
  simp only [wp_unfold]
  iapply (wpi_fupd _).2

theorem wp_val {M : CoPset} (v : Val) (Φ : Val → IProp GF) :
    Φ v -∗
    WP hl(v(&v)) @ hmono ; M {{ Φ }} := by
  iintro HΦ
  simp only [wp_unfold]
  rw [← val_to_ofVal, Exp.denote.eq_1]
  iapply wpi_pure $$ [$]

theorem wp_unop {M : CoPset} (op : UnOp) (v v' : Val) (Φ : Val → IProp GF) :
    ⌜op.denote v = pure v'⌝ -∗
    sm (Φ v') -∗
    WP (Exp.unop op (Exp.val v)) @ hmono ; M {{ Φ }} := by
  iintro %Hop HΦ
  simp only [wp_unfold, Exp.denote.eq_5, Exp.isVal, ↓reduceIte,
    Exp.denote.eq_1, LawfulMonad.pure_bind]
  rw [Hop]
  simp only [LawfulMonad.pure_bind]
  iapply wpi_step_pure $$ [$]

theorem wp_binop {M : CoPset} (op : BinOp) (v₁ v₂ v' : Val) (Φ : Val → IProp GF) :
    ⌜op.denote v₁ v₂ = pure v'⌝ -∗
    sm (Φ v') -∗
    WP (Exp.binop op (Exp.val v₁) (Exp.val v₂)) @ hmono ; M {{ Φ }} := by
  iintro % Hop HΦ
  simp only [wp_unfold, Exp.denote.eq_6, Exp.isVal, ↓reduceIte,
    Exp.denote.eq_1, LawfulMonad.pure_bind]
  rw [Hop]
  simp only [LawfulMonad.pure_bind]
  iapply wpi_step_pure $$ [$]

theorem wp_if_true (e₁ e₂ : Exp) (Φ : Val → IProp GF) :
    sm (WP e₁ @ hmono ; ⊤ {{ Φ }}) -∗
    WP (Exp.if (Exp.val (Val.lit (BaseLit.bool true))) e₁ e₂) @ hmono ; ⊤ {{ Φ }} := by
  iintro Hwp
  simp only [wp_unfold, Exp.denote.eq_7, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; simp only [Val.bool!]
  iapply wpi_pure; simp only [↓reduceIte]
  iapply wpi_cont $$ [$]

theorem wp_if_false (e₁ e₂ : Exp) (Φ : Val → IProp GF) :
    sm (WP e₂ @ hmono ; ⊤ {{ Φ }}) -∗
    WP (Exp.if (Exp.val (Val.lit (BaseLit.bool false))) e₁ e₂) @ hmono ; ⊤ {{ Φ }} := by
  iintro Hwp
  simp only [wp_unfold, Exp.denote.eq_7, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; simp only [Val.bool!]
  iapply wpi_pure; simp only [Bool.false_eq_true, ↓reduceIte]
  iapply wpi_cont $$ [$]

theorem wp_app (f x : Binder) (v : Val) (e : Exp) (Φ : Val → IProp GF) :
    sm (WP ((e.subst f (.rec_ f x e)).subst x v) @ hmono ; ⊤ {{ Φ }}) -∗
    WP (Exp.app (Exp.val (Val.rec_ f x e)) (Exp.val v)) @ hmono ; ⊤ {{ Φ }} := by
  iintro Hwp
  simp only [wp_unfold, Exp.denote.eq_4, Exp.isVal, ↓reduceIte,
    Exp.denote.eq_1, LawfulMonad.pure_bind, Val.rec!]
  iapply wpi_cont $$ [$]

theorem wp_rec {M : CoPset} (f x : Binder) (e : Exp) (Φ : Val → IProp GF) :
    sm (Φ (.rec_ f x e)) -∗
    WP (Exp.rec_ f x e) @ hmono ; M {{ Φ }} := by
  iintro HΦ
  simp only [wp_unfold, Exp.denote.eq_3]
  iapply wpi_step_pure $$ [$]

theorem wp_pair {M : CoPset} (v₁ v₂ : Val) (Φ : Val → IProp GF) :
    sm (Φ (.pair v₁ v₂)) -∗
    WP (Exp.pair (.val v₁) (.val v₂)) @ hmono ; M {{ Φ }} := by
  iintro HΦ
  simp only [wp_unfold, Exp.denote.eq_8, Exp.isVal, ↓reduceIte,
    Exp.denote.eq_1, LawfulMonad.pure_bind]
  iapply wpi_step_pure $$ [$]

theorem wp_fst {M : CoPset} (v₁ v₂ : Val) (Φ : Val → IProp GF) :
    sm (Φ v₁) -∗
    WP (Exp.fst (.val (.pair v₁ v₂))) @ hmono ; M {{ Φ }} := by
  iintro HΦ
  simp only [wp_unfold, Exp.denote.eq_9, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; simp only [Val.pair!]
  iapply wpi_pure
  iapply wpi_step_pure $$ [$]

theorem wp_snd {M : CoPset} (v₁ v₂ : Val) (Φ : Val → IProp GF) :
    sm (Φ v₂) -∗
    WP (Exp.snd (.val (.pair v₁ v₂))) @ hmono ; M {{ Φ }} := by
  iintro HΦ
  simp only [wp_unfold, Exp.denote.eq_10, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; simp only [Val.pair!]
  iapply wpi_pure
  iapply wpi_step_pure $$ [$]

theorem wp_injL {M : CoPset} (v : Val) (Φ : Val → IProp GF) :
    sm (Φ (.injL v)) -∗
    WP (Exp.injL (.val v)) @ hmono ; M {{ Φ }} := by
  iintro HΦ
  simp only [wp_unfold, Exp.denote.eq_11, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_step_pure $$ [$]

theorem wp_injR {M : CoPset} (v : Val) (Φ : Val → IProp GF) :
    sm (Φ (.injR v)) -∗
    WP (Exp.injR (.val v)) @ hmono ; M {{ Φ }} := by
  iintro HΦ
  simp only [wp_unfold, Exp.denote.eq_12, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_step_pure $$ [$]

theorem wp_caseL (v : Val) (e₁ e₂ : Exp) (Φ : Val → IProp GF) :
    sm (WP (Exp.app e₁ (Exp.val v)) @ hmono ; ⊤ {{ Φ }}) -∗
    WP (Exp.case (Exp.val (Val.injL v)) e₁ e₂) @ hmono ; ⊤ {{ Φ }} := by
  iintro Hwp
  simp only [wp_unfold, Exp.denote.eq_13, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_cont $$ [$]

theorem wp_caseR (v : Val) (e₁ e₂ : Exp) (Φ : Val → IProp GF) :
    sm (WP (Exp.app e₂ (Exp.val v)) @ hmono ; ⊤ {{ Φ }}) -∗
    WP (Exp.case (Exp.val (Val.injR v)) e₁ e₂) @ hmono ; ⊤ {{ Φ }} := by
  iintro Hwp
  simp only [wp_unfold, Exp.denote.eq_13, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_cont $$ [$]

theorem wp_fork (e : Exp) (Φ : Val → IProp GF) :
    sm (Φ (.lit .unit)) -∗
    WP e @ hmono; ⊤ {{ v, ⌜v = .lit .unit⌝ }} -∗
    WP (Exp.fork e) @ hmono; ⊤ {{ Φ }} := by
  iintro HΦ Hwp
  simp only [wp_unfold, Exp.denote.eq_21, Exp.isVal]
  iapply wpi_bind; iapply wpi_fork $$ [HΦ]
  · iapply wpi_step_pure $$ [$]
  · iapply wpi_bind;
    cases e <;> simp only [↓reduceIte, ConcE.yieldAfter, Bool.false_eq_true]
    · iapply wpi_wand $$ Hwp;
      iintro %_ _; iapply wpi_pure; itrivial
    all_goals
      iapply wpi_bind; iapply wpi_wand $$ Hwp
      iintro %_ _; iapply wpi_bind; iapply wpi_yield
      iapply wpi_pure; iapply wpi_pure; itrivial

section heap_rules

theorem wp_allocN {M : CoPset} (n : Int) (v : Val) (Φ : Val → IProp GF) :
    0 < n →
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    sm iprop(∀ l : Loc,
      ([∗list] i ∈ List.range n.toNat, (l + Int.ofNat i) ↦ v) -∗
      Φ (.lit (.loc l))) -∗
    WP (Exp.allocN (.val (.lit (.int n))) (.val v)) @ hmono; M {{ Φ }} := by
  iintro %Hpos %Hmask HΦ
  simp only [wp_unfold, Exp.denote.eq_14, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; simp only [Val.int!];
  iapply wpi_pure; simp only [Int.not_le.mpr Hpos, ↓reduceIte]
  iapply wpi_bind; iapply wpi_allocN _ _ _ _ Hmask
  iintro %l Hpts; iapply wpi_step_pure
  iapply StepMod.map (sm := sm) $$ HΦ
  iintro HΦ; ispecialize HΦ $$ %l
  iapply HΦ $$ Hpts

theorem wp_alloc {M : CoPset} (v : Val) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    sm iprop(∀ l, l ↦ v -∗ Φ (.lit (.loc l))) -∗
    WP (Exp.allocN (.val (.lit (.int 1))) (.val v)) @ hmono; M {{ Φ }} := by
  iintro %Hmask HΦ
  iapply wp_allocN 1 _ _ (by omega) Hmask
  iapply StepMod.map (sm := sm) $$ HΦ
  iintro HΦ %l Hpts; ispecialize HΦ $$ %l
  iapply HΦ; simp [List.range_one, LawfulLoc.add_zero]
  icases Hpts with ⟨H, -⟩; iframe

theorem wp_load {M : CoPset} (l : Loc) (v : Val) (dq : DFrac) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    l ↦{dq} v -∗
    sm iprop(l ↦{dq} v -∗ Φ v) -∗
    WP (Exp.load (Exp.val (Val.lit (BaseLit.loc l)))) @ hmono ; M {{ Φ }} := by
  iintro %Hmask Hpt HΦ
  simp only [wp_unfold, Exp.denote.eq_16, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; simp only [Val.loc!]
  iapply wpi_pure; iapply wpi_bind
  iapply wpi_load! _ _ _ _ _ Hmask $$ Hpt
  iintro Hpt; iapply wpi_step_pure
  iapply StepMod.wand (sm := sm) $$ HΦ Hpt

theorem wp_store {M : CoPset} (l : Loc) (v v' : Val) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    l ↦ v -∗
    sm iprop(l ↦ v' -∗ Φ (.lit .unit)) -∗
    WP (Exp.store (Exp.val (Val.lit (BaseLit.loc l))) (Exp.val v')) @ hmono ; M {{ Φ }} := by
  iintro %Hmask Hpt HΦ
  simp only [wp_unfold, Exp.denote.eq_17, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; simp only [Val.loc!]
  iapply wpi_pure; iapply wpi_bind
  iapply wpi_store! _ _ _ _ _ Hmask $$ Hpt
  iintro Hpt; iapply wpi_step_pure
  iapply StepMod.wand (sm := sm) $$ HΦ Hpt

theorem wp_free {M : CoPset} (l : Loc) (v : Val) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    l ↦ v -∗
    sm iprop(l ↦? (none : Option Val) -∗ Φ (.lit .unit)) -∗
    WP (Exp.free (Exp.val (Val.lit (BaseLit.loc l)))) @ hmono ; M {{ Φ }} := by
  iintro %Hmask Hpt HΦ
  simp only [wp_unfold, Exp.denote.eq_15, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; simp only [Val.loc!]
  iapply wpi_pure; iapply wpi_bind
  iapply wpi_storeOpt _ _ _ _ _ Hmask $$ Hpt
  iintro Hpt; iapply wpi_step_pure
  iapply StepMod.wand (sm := sm) $$ HΦ Hpt

theorem wp_xchg {M : CoPset} (l : Loc) (v v' : Val) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    l ↦ v -∗
    sm iprop(l ↦ v' -∗ Φ v) -∗
    WP (Exp.xchg (Exp.val (Val.lit (BaseLit.loc l))) (Exp.val v')) @ hmono ; M {{ Φ }} := by
  iintro %Hmask Hpt HΦ
  simp only [wp_unfold, Exp.denote.eq_19, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; simp only [Val.loc!]
  iapply wpi_pure; iapply wpi_bind
  iapply wpi_store! _ _ _ _ _ Hmask $$ Hpt
  iintro Hpt; iapply wpi_step_pure
  iapply StepMod.wand (sm := sm) $$ HΦ Hpt

theorem wp_cmpXchg_fail {M : CoPset} (l : Loc) (dq : DFrac) (v' v₁ v₂ : Val) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    v' ≠ v₁ →
    v'.compareSafe v₁ = true →
    l ↦{dq} v' -∗
    sm iprop(l ↦{dq} v' -∗ Φ (.pair v' (.lit (.bool false)))) -∗
    WP (Exp.cmpXchg (Exp.val <| Val.lit <| BaseLit.loc l) (Exp.val v₁) (Exp.val v₂))
      @ hmono ; M {{ Φ }} := by
  iintro %Hmask %Hneq %Hcmp Hpt HΦ
  simp only [wp_unfold, Exp.denote.eq_18, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; simp only [Val.loc!]; iapply wp_val
  iapply wpi_bind; simp only
  iapply wpi_pure; iapply wpi_bind
  iapply wpi_load! _ _ _ _ _ Hmask $$ Hpt
  simp only [Hcmp, Hneq, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  iintro Hpt; iapply wpi_step_pure
  iapply StepMod.wand (sm := sm) $$ HΦ Hpt

theorem wp_cmpXchg_suc {M : CoPset} (l : Loc) (v' v₁ v₂ : Val) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    v' = v₁ →
    v'.compareSafe v₁ = true →
    l ↦ v' -∗
    sm iprop(l ↦ v₂ -∗ Φ (.pair v' (.lit <| .bool true))) -∗
    WP (Exp.cmpXchg (Exp.val <| Val.lit <| BaseLit.loc l) (Exp.val v₁) (Exp.val v₂))
      @ hmono ; M {{ Φ }} := by
  iintro %Hmask %Heq %Hcmp Hpt HΦ; subst Heq
  simp only [wp_unfold, Exp.denote.eq_18, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; simp only [Val.loc!]
  iapply wpi_pure; iapply wpi_bind
  iapply wpi_load! _ _ _ _ _ Hmask $$ Hpt
  simp only [Hcmp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  iintro Hpt; iapply wpi_bind
  iapply wpi_store! _ _ _ _ _ Hmask $$ Hpt
  iintro Hpt; iapply wpi_step_pure
  iapply StepMod.wand (sm := sm) $$ HΦ Hpt

theorem wp_faa {M : CoPset} (l : Loc) (i₁ i₂ : Int) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    l ↦ Val.lit (.int i₁) -∗
    sm iprop(l ↦ (.lit (.int (i₁ + i₂)) : Val) -∗ Φ (.lit (.int i₁))) -∗
    WP (Exp.faa (.val <| .lit <| .loc l) (.val <| .lit <| .int i₂)) @ hmono ; M {{ Φ }} := by
  iintro %Hmask Hpt HΦ
  simp only [wp_unfold, Exp.denote.eq_20, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; simp only [Val.loc!]
  iapply wpi_pure; iapply wpi_bind; simp only [Val.int!]
  iapply wpi_pure; iapply wpi_bind
  iapply wpi_load! _ _ _ _ _ Hmask $$ Hpt; simp only
  iintro Hpt; iapply wpi_bind; iapply wpi_pure; iapply wpi_bind
  iapply wpi_store! _ _ _ _ _ Hmask $$ Hpt
  iintro Hpt; iapply wpi_step_pure
  iapply StepMod.wand (sm := sm) $$ HΦ Hpt

end heap_rules

end wp_rules

end IrisITree
