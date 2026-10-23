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

instance lawfulLoc_heaplang : LawfulLoc Loc where
  decEq := inferInstance
  add_zero l := by ext; simp
  add_nat_inj l := by
    intro i j Hij
    have Hn := congrArg Loc.n Hij
    simp at Hn
    omega
  add_pos_nle := by
    intro l m
    simp [compare, compareOfLessAndEq, Ordering.isLE]
    grind

section handler

variable {GF} [InvGS GF] [heaplangHGS GF]

def heaplangH (m : StepMod (IProp GF)) : IHandler (IProp GF) heaplangE :=
  concH ⊕ₕ heapH ⊕ₕ failH ⊕ₕ demonicH Loc ⊕ₕ stepH m

instance inH_conc_heaplang (m : StepMod (IProp GF)) :
    InH concH (heaplangH m) := by
  unfold heaplangH
  infer_instance

instance inH_heap_heaplang (m : StepMod (IProp GF)) :
    InH (heapH (Loc := Loc) (Val := Val)) (heaplangH m) := by
  unfold heaplangH
  infer_instance

instance inH_fail_heaplang (m : StepMod (IProp GF)) :
    InH failH (heaplangH m) := by
  unfold heaplangH
  infer_instance

instance inH_demonic_heaplang (m : StepMod (IProp GF)) :
    InH (demonicH Loc) (heaplangH m) := by
  unfold heaplangH
  infer_instance

instance inH_step_heaplang (m : StepMod (IProp GF)) :
    InH (stepH m) (heaplangH m) := by
  unfold heaplangH
  infer_instance

instance wandH_heaplang_ident_later :
    WandH (heaplangH (.ident (PROP := IProp GF))) (heaplangH .later) := by
  unfold heaplangH
  infer_instance

instance wp_heaplang : Wp (IProp GF) Exp Val (StepMod (IProp GF)) where
  wp m M e Φ := WPi e.denote @> heaplangH m; M {{ Φ }}

end handler

section wpi_rules

variable {GF} [InvGS GF] [heaplangHGS GF]
  {m : StepMod (IProp GF)}

theorem wpi_step_pure E (v : Val) (Φ : Val → IProp GF) :
    m (Φ v) -∗
    WPi (do
      step
      pure v) @> heaplangH m; E {{ Φ }} := by
  iintro HΦ
  iapply wpi_bind
  iapply wpi_step
  iapply m.map $$ HΦ
  iintro HΦ
  imodintro
  iapply wpi_pure $$ HΦ

theorem wpi_yieldIfNotVal (e : Exp) (Φ : Unit → IProp GF) :
    Φ () -∗
    WPi e.yieldIfNotVal @> heaplangH m; ⊤ {{ Φ }} := by
  cases e <;> simp only [Exp.yieldIfNotVal]
  · iintro HΦ; iapply wpi_pure $$ [$]
  all_goals
    iintro HΦ; iapply wpi_yield $$ [$]

theorem wpi_cont (e : Exp) (Φ : Val → IProp GF) :
    m (WP e @ m ; ⊤ {{ Φ }}) -∗
    WPi (do
      step
      e.yieldIfNotVal
      e.denote) @> heaplangH m; ⊤ {{ Φ }} := by
  iintro Hwp; iapply wpi_bind
  iapply wpi_step
  iapply m.map $$ Hwp
  iintro Hwp !>; iapply wpi_bind
  iapply wpi_yieldIfNotVal; iframe

end wpi_rules

section wp_rules

variable {GF} [InvGS GF] [heaplangHGS GF]
  {m : StepMod (IProp GF)}

theorem wp_unfold {M : CoPset} (e : Exp) (Φ : Val → IProp GF) :
  WP e @ m; M {{ Φ }} = WPi e.denote @> heaplangH m; M {{ Φ }} := rfl

/-- The identity (total) WP implies the later (partial) WP. -/
theorem wp_later_weaken {M : CoPset} (e : Exp) (Φ : Val → IProp GF) :
    WP e @ (StepMod.ident (PROP := IProp GF)); M {{ Φ }} -∗
    WP e @ (StepMod.later (PROP := IProp GF)); M {{ Φ }} := by
  simp only [wp_unfold]
  iintro Hwp
  iapply (wpi_wandH
    (H1 := heaplangH (StepMod.ident (PROP := IProp GF)))
    (H2 := heaplangH (StepMod.later (PROP := IProp GF))))
  iexact Hwp

theorem wp_bind (K : List ECtxItem) (e : Exp) (Φ : Val → IProp GF) :
    WP e @ m; ⊤ {{ v,
      WP (ProgramLogic.fill K (Exp.ofVal (Expr := Exp) v)) @ m; ⊤ {{ Φ }}
    }} -∗
    WP (ProgramLogic.fill K e) @ m; ⊤ {{ Φ }} := by
  sorry

theorem wp_wand {M : CoPset} (e : Exp) (Φ Ψ : Val → IProp GF) :
    WP e @ m ; M {{ Φ }} -∗
    (∀ v, Φ v -∗ Ψ v) -∗
    WP e @ m ; M {{ Ψ }} := by
  simp only [wp_unfold]
  apply wpi_wand

theorem wp_frame_l {M : CoPset} (e : Exp) (Φ : Val → IProp GF) :
    P ∗ WP e @ m; M {{ Φ }} -∗ WP e @ m; M {{v , P ∗ Φ v}} := by
  iintro ⟨HP, Hwp⟩
  iapply wp_wand $$ Hwp [HP]
  iintro %_ _; iframe

theorem wp_atomic E1 E2 (e : Exp) (Φ : Val → IProp GF) :
    (|={E1,E2}=> WP e @ m ; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ m ; E1 {{ Φ }} := by
  simp only [wp_unfold]
  iintro > >Hwp
  iapply wpi_fupd_empty
  ihave Hwp := wpi_fupd_empty $$ Hwp
  iapply wpi_wand $$ Hwp
  iintro %_ > > $

theorem fupd_wp {M : CoPset} (e : Exp) (Φ : Val → IProp GF) :
    (|={M}=> WP e @ m ; M {{ v, Φ v }}) ⊢ WP e @ m ; M {{ Φ }} := by
  simp only [wp_unfold]
  iapply (fupd_wpi _).2

theorem wp_fupd {M : CoPset} (e : Exp) (Φ : Val → IProp GF) :
    (WP e @ m ; M {{ v, |={M}=> Φ v }}) ⊢ WP e @ m ; M {{ Φ }} := by
  simp only [wp_unfold]
  iapply (wpi_fupd _).2

theorem wp_val {M : CoPset} (v : Val) (Φ : Val → IProp GF) :
    Φ v -∗
    WP hl(v(&v)) @ m ; M {{ Φ }} := by
  iintro HΦ
  simp only [wp_unfold]
  rw [← val_to_ofVal, Exp.denote.eq_1]
  iapply wpi_pure $$ [$]

theorem wp_unop {M : CoPset} (op : UnOp) (v v' : Val) (Φ : Val → IProp GF) :
    ⌜op.denote v = pure v'⌝ -∗
    m (Φ v') -∗
    WP (Exp.unop op (Exp.val v)) @ m ; M {{ Φ }} := by
  iintro %Hop HΦ
  simp only [wp_unfold, Exp.denote.eq_5, Exp.isVal, ↓reduceIte,
    Exp.denote.eq_1, LawfulMonad.pure_bind]
  rw [Hop]
  simp only [LawfulMonad.pure_bind]
  iapply wpi_step_pure $$ [$]

theorem wp_binop {M : CoPset} (op : BinOp) (v₁ v₂ v' : Val) (Φ : Val → IProp GF) :
    ⌜op.denote v₁ v₂ = pure v'⌝ -∗
    m (Φ v') -∗
    WP (Exp.binop op (Exp.val v₁) (Exp.val v₂)) @ m ; M {{ Φ }} := by
  iintro % Hop HΦ
  simp only [wp_unfold, Exp.denote.eq_6, Exp.isVal, ↓reduceIte,
    Exp.denote.eq_1, LawfulMonad.pure_bind]
  rw [Hop]
  simp only [LawfulMonad.pure_bind]
  iapply wpi_step_pure $$ [$]

theorem wp_if_true (e₁ e₂ : Exp) (Φ : Val → IProp GF) :
    m (WP e₁ @ m ; ⊤ {{ Φ }}) -∗
    WP (Exp.if (Exp.val (Val.lit (BaseLit.bool true))) e₁ e₂) @ m ; ⊤ {{ Φ }} := by
  iintro Hwp
  simp only [wp_unfold, Exp.denote.eq_7, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; simp only [Val.bool!]
  iapply wpi_pure; simp only [↓reduceIte]
  iapply wpi_cont $$ [$]

theorem wp_if_false (e₁ e₂ : Exp) (Φ : Val → IProp GF) :
    m (WP e₂ @ m ; ⊤ {{ Φ }}) -∗
    WP (Exp.if (Exp.val (Val.lit (BaseLit.bool false))) e₁ e₂) @ m ; ⊤ {{ Φ }} := by
  iintro Hwp
  simp only [wp_unfold, Exp.denote.eq_7, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; simp only [Val.bool!]
  iapply wpi_pure; simp only [Bool.false_eq_true, ↓reduceIte]
  iapply wpi_cont $$ [$]

theorem wp_app (f x : Binder) (v : Val) (e : Exp) (Φ : Val → IProp GF) :
    m (WP ((e.subst f (.rec_ f x e)).subst x v) @ m ; ⊤ {{ Φ }}) -∗
    WP (Exp.app (Exp.val (Val.rec_ f x e)) (Exp.val v)) @ m ; ⊤ {{ Φ }} := by
  iintro Hwp
  simp only [wp_unfold, Exp.denote.eq_4, Exp.isVal, ↓reduceIte,
    Exp.denote.eq_1, LawfulMonad.pure_bind, Val.rec!]
  iapply wpi_cont $$ [$]

theorem wp_rec {M : CoPset} (f x : Binder) (e : Exp) (Φ : Val → IProp GF) :
    m (Φ (.rec_ f x e)) -∗
    WP (Exp.rec_ f x e) @ m ; M {{ Φ }} := by
  iintro HΦ
  simp only [wp_unfold, Exp.denote.eq_3]
  iapply wpi_step_pure $$ [$]

theorem wp_pair {M : CoPset} (v₁ v₂ : Val) (Φ : Val → IProp GF) :
    m (Φ (.pair v₁ v₂)) -∗
    WP (Exp.pair (.val v₁) (.val v₂)) @ m ; M {{ Φ }} := by
  iintro HΦ
  simp only [wp_unfold, Exp.denote.eq_8, Exp.isVal, ↓reduceIte,
    Exp.denote.eq_1, LawfulMonad.pure_bind]
  iapply wpi_step_pure $$ [$]

theorem wp_fst {M : CoPset} (v₁ v₂ : Val) (Φ : Val → IProp GF) :
    m (Φ v₁) -∗
    WP (Exp.fst (.val (.pair v₁ v₂))) @ m ; M {{ Φ }} := by
  iintro HΦ
  simp only [wp_unfold, Exp.denote.eq_9, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; simp only [Val.pair!]
  iapply wpi_pure
  iapply wpi_step_pure $$ [$]

theorem wp_snd {M : CoPset} (v₁ v₂ : Val) (Φ : Val → IProp GF) :
    m (Φ v₂) -∗
    WP (Exp.snd (.val (.pair v₁ v₂))) @ m ; M {{ Φ }} := by
  iintro HΦ
  simp only [wp_unfold, Exp.denote.eq_10, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; simp only [Val.pair!]
  iapply wpi_pure
  iapply wpi_step_pure $$ [$]

theorem wp_injL {M : CoPset} (v : Val) (Φ : Val → IProp GF) :
    m (Φ (.injL v)) -∗
    WP (Exp.injL (.val v)) @ m ; M {{ Φ }} := by
  iintro HΦ
  simp only [wp_unfold, Exp.denote.eq_11, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_step_pure $$ [$]

theorem wp_injR {M : CoPset} (v : Val) (Φ : Val → IProp GF) :
    m (Φ (.injR v)) -∗
    WP (Exp.injR (.val v)) @ m ; M {{ Φ }} := by
  iintro HΦ
  simp only [wp_unfold, Exp.denote.eq_12, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_step_pure $$ [$]

theorem wp_caseL (v : Val) (e₁ e₂ : Exp) (Φ : Val → IProp GF) :
    m (WP (Exp.app e₁ (Exp.val v)) @ m ; ⊤ {{ Φ }}) -∗
    WP (Exp.case (Exp.val (Val.injL v)) e₁ e₂) @ m ; ⊤ {{ Φ }} := by
  iintro Hwp
  simp only [wp_unfold, Exp.denote.eq_13, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_cont $$ [$]

theorem wp_caseR (v : Val) (e₁ e₂ : Exp) (Φ : Val → IProp GF) :
    m (WP (Exp.app e₂ (Exp.val v)) @ m ; ⊤ {{ Φ }}) -∗
    WP (Exp.case (Exp.val (Val.injR v)) e₁ e₂) @ m ; ⊤ {{ Φ }} := by
  iintro Hwp
  simp only [wp_unfold, Exp.denote.eq_13, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_cont $$ [$]

theorem wp_fork (e : Exp) (Φ : Val → IProp GF) :
    m (Φ (.lit .unit)) -∗
    WP e @ m; ⊤ {{ v, ⌜v = .lit .unit⌝ }} -∗
    WP (Exp.fork e) @ m; ⊤ {{ Φ }} := by
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
    m iprop(∀ l : Loc,
      ([∗list] i ∈ List.range n.toNat, (l + Int.ofNat i) ↦ v) -∗
      Φ (.lit (.loc l))) -∗
    WP (Exp.allocN (.val (.lit (.int n))) (.val v)) @ m; M {{ Φ }} := by
  iintro %Hpos %Hmask HΦ
  simp only [wp_unfold, Exp.denote.eq_14, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; simp only [Val.int!];
  iapply wpi_pure; simp only [Int.not_le.mpr Hpos, ↓reduceIte]
  iapply wpi_bind; iapply wpi_allocN _ _ _ _ Hmask
  iintro %l Hpts; iapply wpi_step_pure
  iapply m.map $$ HΦ
  iintro HΦ; ispecialize HΦ $$ %l
  iapply HΦ $$ Hpts

theorem wp_alloc {M : CoPset} (v : Val) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    m iprop(∀ l, l ↦ v -∗ Φ (.lit (.loc l))) -∗
    WP (Exp.allocN (.val (.lit (.int 1))) (.val v)) @ m; M {{ Φ }} := by
  iintro %Hmask HΦ
  iapply wp_allocN 1 _ _ (by omega) Hmask
  iapply m.map $$ HΦ
  iintro HΦ %l Hpts; ispecialize HΦ $$ %l
  iapply HΦ; simp [List.range_one, LawfulLoc.add_zero]
  icases Hpts with ⟨H, -⟩; iframe

theorem wp_load {M : CoPset} (l : Loc) (v : Val) (dq : DFrac) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    l ↦{dq} v -∗
    m iprop(l ↦{dq} v -∗ Φ v) -∗
    WP (Exp.load (Exp.val (Val.lit (BaseLit.loc l)))) @ m ; M {{ Φ }} := by
  iintro %Hmask Hpt HΦ
  simp only [wp_unfold, Exp.denote.eq_16, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; simp only [Val.loc!]
  iapply wpi_pure; iapply wpi_bind
  iapply wpi_load! _ _ _ _ _ Hmask $$ Hpt
  iintro Hpt; iapply wpi_step_pure
  iapply m.wand $$ HΦ Hpt

theorem wp_store {M : CoPset} (l : Loc) (v v' : Val) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    l ↦ v -∗
    m iprop(l ↦ v' -∗ Φ (.lit .unit)) -∗
    WP (Exp.store (Exp.val (Val.lit (BaseLit.loc l))) (Exp.val v')) @ m ; M {{ Φ }} := by
  iintro %Hmask Hpt HΦ
  simp only [wp_unfold, Exp.denote.eq_17, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; simp only [Val.loc!]
  iapply wpi_pure; iapply wpi_bind
  iapply wpi_store! _ _ _ _ _ Hmask $$ Hpt
  iintro Hpt; iapply wpi_step_pure
  iapply m.wand $$ HΦ Hpt

theorem wp_free {M : CoPset} (l : Loc) (v : Val) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    l ↦ v -∗
    m iprop(l ↦? (none : Option Val) -∗ Φ (.lit .unit)) -∗
    WP (Exp.free (Exp.val (Val.lit (BaseLit.loc l)))) @ m ; M {{ Φ }} := by
  iintro %Hmask Hpt HΦ
  simp only [wp_unfold, Exp.denote.eq_15, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; simp only [Val.loc!]
  iapply wpi_pure; iapply wpi_bind
  iapply wpi_storeOpt _ _ _ _ _ Hmask $$ Hpt
  iintro Hpt; iapply wpi_step_pure
  iapply m.wand $$ HΦ Hpt

theorem wp_xchg {M : CoPset} (l : Loc) (v v' : Val) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    l ↦ v -∗
    m iprop(l ↦ v' -∗ Φ v) -∗
    WP (Exp.xchg (Exp.val (Val.lit (BaseLit.loc l))) (Exp.val v')) @ m ; M {{ Φ }} := by
  iintro %Hmask Hpt HΦ
  simp only [wp_unfold, Exp.denote.eq_19, Exp.isVal, ↓reduceIte]
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; iapply wp_val
  iapply wpi_bind; simp only [Val.loc!]
  iapply wpi_pure; iapply wpi_bind
  iapply wpi_store! _ _ _ _ _ Hmask $$ Hpt
  iintro Hpt; iapply wpi_step_pure
  iapply m.wand $$ HΦ Hpt

theorem wp_cmpXchg_fail {M : CoPset} (l : Loc) (dq : DFrac) (v' v₁ v₂ : Val) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    v' ≠ v₁ →
    v'.compareSafe v₁ = true →
    l ↦{dq} v' -∗
    m iprop(l ↦{dq} v' -∗ Φ (.pair v' (.lit (.bool false)))) -∗
    WP (Exp.cmpXchg (Exp.val <| Val.lit <| BaseLit.loc l) (Exp.val v₁) (Exp.val v₂))
      @ m ; M {{ Φ }} := by
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
  iapply m.wand $$ HΦ Hpt

theorem wp_cmpXchg_suc {M : CoPset} (l : Loc) (v' v₁ v₂ : Val) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    v' = v₁ →
    v'.compareSafe v₁ = true →
    l ↦ v' -∗
    m iprop(l ↦ v₂ -∗ Φ (.pair v' (.lit <| .bool true))) -∗
    WP (Exp.cmpXchg (Exp.val <| Val.lit <| BaseLit.loc l) (Exp.val v₁) (Exp.val v₂))
      @ m ; M {{ Φ }} := by
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
  iapply m.wand $$ HΦ Hpt

theorem wp_faa {M : CoPset} (l : Loc) (i₁ i₂ : Int) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    l ↦ Val.lit (.int i₁) -∗
    m iprop(l ↦ (.lit (.int (i₁ + i₂)) : Val) -∗ Φ (.lit (.int i₁))) -∗
    WP (Exp.faa (.val <| .lit <| .loc l) (.val <| .lit <| .int i₂)) @ m ; M {{ Φ }} := by
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
  iapply m.wand $$ HΦ Hpt

end heap_rules

end wp_rules

end IrisITree
