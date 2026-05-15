module

public import Iris.Algebra
public import Iris.Instances.Lib.FUpd
public import Iris.Instances.Lib.LaterCredits
public import Iris.BI
public import Iris.BI.WeakestPre
public import Iris.BI.BigOp.BigSepList
public import Iris.BI.DerivedLaws
public import Iris.BI.Updates
public import Iris.ProofMode
meta import Iris.BI.Updates
public import Iris.ProgramLogic.Language
public import Iris.Std.CoPset

namespace Iris

open ProgramLogic Language.Notation

@[expose] public section

class StateInterp
    (State: Type s)
    (Obs  : outParam <| Type o)
    (GF : BundledGFunctors)
  where
    stateInterp : State → Nat → List (Obs) → Nat → IProp GF

export StateInterp (stateInterp)

/- TODO: Should this be a class? Maybe we just need to be explicit about the
   instance it belongs to. Otherwise, we could have some problems if somewhere
   someone defines a NumLatersPerStep instance and that one gets taken by
   everyone else.  -/
class NumLatersPerStep where
  numLatersPerStep : Nat → Nat

export NumLatersPerStep (numLatersPerStep)

class IrisGS_gen (hlc : outParam <| Bool)
    (Expr  : Type e)
    {Val   : Type v}
    {State : Type s}
    {Obs   : Type o}
    [Λ : Language Expr State Obs Val]
    (GF : BundledGFunctors)
  extends
    StateInterp State Obs GF,
    InvGS_gen hlc GF,
    NumLatersPerStep where

  forkPost : Val → IProp GF

  state_interp_mono σ ns obs nt :
    iprop(stateInterp σ ns obs nt ⊢ |={∅}=> stateInterp σ (ns + 1) obs nt)

variable {hlc : outParam Bool}
variable {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors}
variable [ι : IrisGS_gen hlc Expr GF]

instance : IrisGS_gen hlc Expr GF → Language Expr State Obs Val := fun _ => Λ

/-- Reducibility condition depending on stuckness.
```lean4
-- s.MaybeReducible (e, σ) equivalent to…
if s matches .NotStuck then Reducible (e, σ) else True
```
-/
@[simp]
abbrev Stuckness.MaybeReducible : Stuckness → Expr × State → Prop
| .NotStuck, (e₁, σ₁) => PrimStep.Reducible (e₁, σ₁)
| _, _ => True

def wp.pre (s : Stuckness)
  (wp : CoPset -> Expr -> (Val -> IProp GF) -> IProp GF) :
    CoPset -> Expr -> (Val -> IProp GF) -> IProp GF := fun E e₁ Φ =>
  match toVal e₁ with
  | some v => iprop(|={E}=> Φ v)
  | none => iprop(∀ (σ₁ : State) (ns : Nat) (obs obs' : List Obs) (nt : Nat),
    stateInterp σ₁ ns (obs ++ obs') nt ={E,∅}=∗
    ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
    ∀ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ)⌝ -∗
      £ (numLatersPerStep ns + 1)
      ={∅}▷=∗^[numLatersPerStep ns + 1] |={∅,E}=>
      stateInterp σ₂ (ns + 1) obs' (eₜ.length + nt) ∗
      wp E e₂ Φ ∗
      [∗list] e' ∈ eₜ, wp ⊤ e' ι.forkPost)


instance wp.pre.contractive s : OFE.Contractive (wp.pre s (ι := ι)) where
  distLater_dist := by
    intros n wp wp' Hwp E e₁ Φ
    dsimp only [pre]
    cases toVal e₁
    case some _ => simp
    dsimp
    refine BI.forall_ne (fun σ₁ => ?_)
    refine BI.forall_ne (fun ns => ?_)
    refine BI.forall_ne (fun obs => ?_)
    refine BI.forall_ne (fun obs' => ?_)
    refine BI.forall_ne (fun nt => ?_)
    refine BI.wand_ne.ne (.of_eq rfl) ?_
    refine BIFUpdate.ne.ne ?_
    refine BI.sep_ne.ne (.of_eq rfl) ?_
    refine BI.forall_ne (fun e₂  => ?_)
    refine BI.forall_ne (fun σ₂ => ?_)
    refine BI.forall_ne (fun eₜ => ?_)
    refine BI.wand_ne.ne (.of_eq rfl) ?_
    refine BI.wand_ne.ne (.of_eq rfl) ?_
    induction numLatersPerStep ns
    case zero =>
      refine step_fupdN_contractive.distLater_dist ?_
      intros i ih
      refine BIFUpdate.ne.ne ?_
      refine BI.sep_ne.ne (.of_eq rfl) ?_
      refine BI.sep_ne.ne ?_ ?_
      · apply Hwp i ih
      refine BI.BigSepL.bigSepL_dist ?_
      intros k x h
      · apply Hwp i ih
    case succ n IH =>
      apply BIFUpdate.ne.ne
      apply BI.later_ne.ne
      apply BIFUpdate.ne.ne
      assumption

-- instance wp.pre.ne s : OFE.NonExpansive (wp.pre s (ι := ι))
--   := OFE.ne_of_contractive (wp.pre s (ι := ι))

-- TODO: In this part of the Rocq code, a lot of juggling
-- is happening with `wp_def`, `wp_aux`, `wp'` and `wp_unseal`.
-- I wonder what is the purpose of all of these, and if
-- it's possible to achieve this differently in Lean.
@[implicit_reducible]
instance wp.def : Wp (IProp GF) (Expr) (Val) Stuckness where
  wp s := fixpoint (wp.pre s)

section Wp

-- TODO: Move out of here
def _root_.Function.toContractiveHom (f : α → β)[OFE α][OFE β][ι : OFE.Contractive f] : α -c> β where
  f := f
  contractive := ι

@[rocq_alias wp_unfold]
theorem wp_unfold {s E} {e : Expr} {Φ : Val → IProp GF} :
    WP e @ s ; E {{ Φ }} ⊣⊢ wp.pre s (Wp.wp (PROP := IProp GF) s) E e Φ :=
  BI.equiv_iff.1 <| fixpoint_unfold (f := (wp.pre (ι := ι) s).toContractiveHom) E e Φ

@[rocq_alias wp_ne]
instance wp_ne (s : Stuckness) E (e : Expr) :
    OFE.NonExpansive (Wp.wp (PROP := IProp GF) s E e) where
  ne {n Φ₁ Φ₂} HΦ := by
    induction n using Nat.strongRecOn generalizing e E Φ₁ Φ₂ with | ind n IH =>
    calc iprop(Wp.wp s E e Φ₁)
     _ ≡{n}≡ wp.pre s (Wp.wp (PROP := IProp GF) s) E e Φ₁ :=
        OFE.equiv_dist.1 (BI.equiv_iff.2 <| wp_unfold) n
     _ ≡{n}≡ wp.pre s (Wp.wp (PROP := IProp GF) s) E e Φ₂ := by
        dsimp [wp.pre]
        cases toVal e
        case some v => exact BIFUpdate.ne.ne <| HΦ v
        dsimp
        refine BI.forall_ne (fun σ₁ => ?_)
        refine BI.forall_ne (fun ns => ?_)
        refine BI.forall_ne (fun obs => ?_)
        refine BI.forall_ne (fun obs' => ?_)
        refine BI.forall_ne (fun nt => ?_)
        refine BI.wand_ne.ne (.of_eq rfl) ?_
        refine BIFUpdate.ne.ne ?_
        refine BI.sep_ne.ne (.of_eq rfl) ?_
        refine BI.forall_ne (fun e₂  => ?_)
        refine BI.forall_ne (fun σ₂ => ?_)
        refine BI.forall_ne (fun eₜ => ?_)
        refine BI.wand_ne.ne (.of_eq rfl) ?_
        refine BI.wand_ne.ne (.of_eq rfl) ?_
        induction numLatersPerStep ns
        case zero =>
          refine step_fupdN_contractive.distLater_dist ?_
          intros i ih
          refine BIFUpdate.ne.ne ?_
          refine BI.sep_ne.ne (.of_eq rfl) ?_
          refine BI.sep_ne.ne ?_ (.of_eq rfl)
          apply IH i ih _ _ <| OFE.dist_lt HΦ ih
        case succ n IH =>
          apply BIFUpdate.ne.ne
          apply BI.later_ne.ne
          apply BIFUpdate.ne.ne
          assumption
     _ ≡{n}≡ Wp.wp s E e Φ₂ :=
        OFE.equiv_dist.1 (BI.equiv_iff.2 <| wp_unfold) n |>.symm

#rocq_ignore wp_proper "Derivable using NonExpansive.eqv"

-- This definition comes after `wp_ne` because it depends on it.
@[rocq_alias wp_contractive]
instance wp_contractive (s : Stuckness) E (e : Expr) (h : toVal e = none) :
    OFE.Contractive (Wp.wp (PROP := IProp GF) s E e) where
  distLater_dist {n Φ₁ Φ₂} HΦ := by
    calc iprop(Wp.wp s E e Φ₁)
     _ ≡{n}≡ wp.pre s (Wp.wp (PROP := IProp GF) s) E e Φ₁ :=
        OFE.equiv_dist.1 (BI.equiv_iff.2 <| wp_unfold) n
     _ ≡{n}≡ wp.pre s (Wp.wp (PROP := IProp GF) s) E e Φ₂ := by
        simp only [wp.pre, h]
        refine BI.forall_ne (fun σ₁ => ?_)
        refine BI.forall_ne (fun ns => ?_)
        refine BI.forall_ne (fun obs => ?_)
        refine BI.forall_ne (fun obs' => ?_)
        refine BI.forall_ne (fun nt => ?_)
        refine BI.wand_ne.ne (.of_eq rfl) ?_
        refine BIFUpdate.ne.ne ?_
        refine BI.sep_ne.ne (.of_eq rfl) ?_
        refine BI.forall_ne (fun e₂  => ?_)
        refine BI.forall_ne (fun σ₂ => ?_)
        refine BI.forall_ne (fun eₜ => ?_)
        refine BI.wand_ne.ne (.of_eq rfl) ?_
        refine BI.wand_ne.ne (.of_eq rfl) ?_
        induction numLatersPerStep ns
        case zero =>
          refine step_fupdN_contractive.distLater_dist ?_
          intros i ih
          refine BIFUpdate.ne.ne ?_
          refine BI.sep_ne.ne (.of_eq rfl) ?_
          refine BI.sep_ne.ne ?_ (.of_eq rfl)
          apply OFE.NonExpansive.ne
          apply HΦ i ih
        case succ n IH =>
          apply BIFUpdate.ne.ne
          apply BI.later_ne.ne
          apply BIFUpdate.ne.ne
          assumption
     _ ≡{n}≡ Wp.wp s E e Φ₂ :=
        OFE.equiv_dist.1 (BI.equiv_iff.2 <| wp_unfold) n |>.symm

@[rocq_alias wp_value_fupd']
theorem wp_value_fupd' {s : Stuckness} {E} {Φ : Val → IProp GF} {v : Val} :
    WP (v : Expr) @ s ; E {{ Φ }} ⊣⊢ |={E}=> Φ v :=
  calc iprop(WP (v : Expr) @ s ; E {{ Φ }})
    _  ⊣⊢ wp.pre s (Wp.wp s) E (v : Expr) Φ := wp_unfold
    _  ⊣⊢ |={E}=> Φ v := by
      simp only [toVal_coe, BI.BIBase.BiEntails.rfl, wp.pre]

@[rocq_alias wp_strong_mono]
theorem wp_strong_mono {s₁ s₂ : Stuckness} {E₁ E₂} {e : Expr} {Φ Ψ : Val → IProp GF} :
    s₁ ≤ s₂ → E₁ ⊆ E₂ →
    ⊢ WP e @ s₁ ; E₁ {{ Φ }} -∗ (∀ v, Φ v ={E₂}=∗ Ψ v) -∗ WP e @ s₂ ; E₂ {{ Ψ }} := by
  intro hs hE
  istart
  iloeb as IH generalizing %e %Φ %Ψ %E₁ %E₂ %hE
  iintro H
  refine (BI.sep_mono .rfl wp_unfold.1).trans ?_
  iintro ⟨IH,H⟩ HΦ
  refine BI.Entails.trans ?_ wp_unfold.2
  iintro ⟨⟨#IH,H⟩,HΦ⟩
  dsimp only [wp.pre]
  match toVal e with
  | none =>
    dsimp
    iintro %σ₁ %ns %obs %obs' %nt Hσ
    imod fupd_mask_intro_subseteq hE (P := iprop(emp)) $$ [] with Hclose -- TODO: Should we add rocq_alias `fupd_mask_subseteq` to this theorem?
    · exact BI.intuitionistically_elim_emp
    icases H $$ Hσ with >⟨%h, H⟩
    imodintro
    isplit
    · match s₁, s₂ with
      | .MaybeStuck, .NotStuck => simp [LE.le] at hs
      | .NotStuck, .NotStuck
      | .MaybeStuck, .MaybeStuck
      | .NotStuck, .MaybeStuck =>
        ipure_intro; grind only
    iintro %e₂ %σ₂ %eₜ #hstep «h£»
    dsimp [Nat.repeat]
    imod H $$ hstep «h£» with H
    iintro !> !>; imod H; iintro !>
    iapply step_fupdN_wand $$ H
    iintro >⟨aux, H, Hefs⟩
    imod Hclose
    imodintro
    isplitl [aux]
    · iassumption
    isplitr [Hefs]
    · iapply IH $$ %e₂ %Φ %Ψ %E₁ %E₂ %hE H HΦ
    · iapply BI.BigSepL.bigSepL_impl $$ Hefs
      iintro !> %k %e' %_ H
      iapply IH $$ %e' %_ %_ %⊤ %_ %Std.LawfulSet.subset_refl H
      iintro %v H
      imodintro
      iassumption
  | some v =>
    dsimp
    ihave h := fupd_mask_mono hE $$ H
    imod h
    iapply HΦ $$ h


/-
Lemma fupd_wp s E e Φ : (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (σ1 ns κ κs nt) "Hσ1". iMod "H". by iApply "H".
Qed.
-/
theorem fupd_wp (s : Stuckness) E (e : Expr) (Φ : Val → IProp GF) :
    (|={E}=> WP e @ s ; E {{ Φ }}) ⊢ WP e @ s ; E {{ Φ }} := by
  refine (BIFUpdate.mono <| wp_unfold.1).trans ?_
  refine BI.Entails.trans ?_ wp_unfold.2
  iintro H
  match h: toVal e with
  | some v =>
    simp only [wp.pre, h]
    imod H
    iassumption
  | none =>
    simp only [wp.pre, h]
    iintro %σ₁ %ns %obs %obs' %nt
    imod H with H
    iassumption

theorem wp_fupd (s : Stuckness) E (e : Expr) (Φ : Val → IProp GF) :
    -- TODO: Fix `WP` syntax so this doesn't happen.
    WP e @ s ; E {{v, iprop(|={E}=> Φ v) }} ⊢ WP e @ s ; E {{ Φ }} := by
  iintro h
  iapply wp_strong_mono (Std.IsPreorder.le_refl _) Std.LawfulSet.subset_refl $$ h
  iintro %v h
  iassumption

theorem wp_atomic {s : Stuckness} {E1 E2 : CoPset} {e : Expr} {Φ : Val → IProp GF}
  [ι : Language.Atomic ↑s e] :
    (|={E1,E2}=> WP e @ s ;  E2 {{v, iprop(|={E2,E1}=> Φ v) }}) ⊢ (WP e @ s ; E1 {{ Φ }}) := by
  refine (BIFUpdate.mono <| wp_unfold.1).trans ?_
  refine BI.Entails.trans ?_ wp_unfold.2
  iintro H
  match He : toVal e with
  | some v =>
    simp only [wp.pre, He]
    iapply BIFUpdate.trans (E2 := E2)
    imod H
    iassumption
  | none =>
    simp only [wp.pre, He]
    iintro %σ₁ %ns %obs %obs' %nt Hσ
    imod H
    imod H $$ Hσ with ⟨$, H⟩
    imodintro
    iintro %e2 %σ2 %efs %Hstep Hcred
    ihave aux := H $$ %e2 %σ2 %efs %Hstep Hcred
    iapply step_fupdN_wand $$ aux
    iintro >(⟨Hσ,H,Hefs⟩)
    cases s with -- TODO: Example of place where `match` is worse than `cases`
    | NotStuck =>
      -- TODO: replace this when `irw` is available.
      istop; refine (BI.sep_mono (BI.sep_mono .rfl wp_unfold.1) (BI.BigSepL.bigSepL_mono λ_↦ wp_unfold.1)).trans ?_; refine BI.Entails.trans ?_ (BIFUpdate.mono <| (BI.sep_mono .rfl (BI.sep_mono wp_unfold.2 (BI.BigSepL.bigSepL_mono λ_↦ wp_unfold.2) ))); iintro ⟨⟨Hσ,H⟩,Hefs⟩
      simp [wp.pre]
      have := (ι.atomic _ _ _ _ _ Hstep)
      simp at this
      match h₂ : toVal e2 with
      | some v2 =>
        icases H with > > $
        iframe
      | none =>
        simp
        icases H $$ %σ2 %(ns +1) %([]) %_ %(efs.length +nt) [Hσ] with >⟨%h, _⟩
        · exact .rfl
        nomatch (Language.not_reducible_iff_irreducible.mpr (ι.atomic _ _ _ _ _ Hstep)) h
    | MaybeStuck =>
      have ⟨v, h⟩ := Option.isSome_iff_exists.mp (ι.atomic _ _ _ _ _ Hstep)
      obtain ⟨rfl⟩ := (ToVal.coe_of_toVal_eq_some h)
      istop; refine (BI.sep_mono (BI.sep_mono .rfl wp_value_fupd'.1) .rfl).trans ?_; refine BI.Entails.trans ?_ (BIFUpdate.mono <| (BI.sep_mono .rfl (BI.sep_mono wp_value_fupd'.2 .rfl ))); iintro ⟨⟨Hσ,H⟩,Hefs⟩
      imod H with > H
      iframe

/-- (copy-pasted from Rocq formalization)

  This lemma gives us access to the later credits that are generated in each step,
  asuming that we have instantiated `numLaterPerStep` with a non-trivial function
  (for instance, a linear function).

  This lemma can be used to provide a "regeneration" mechanism for later credits.
  `stateInter` will have to be defined in a way that involves the required
  regeneration tokens.

  In detail, a client can use this lemma as follows:

   1. Then client obtains the state interpreatation `stateInterp _ ns _ _`

   2. It uses some ghost state wired up to the interpretation to know that
      `ns = k + m`, and update the state interpretation to `stateInterp _ m _ _`

   3. _After_ `e` has finally stepped, we get `numLatersPerStep k` later credits
      that we can use to prove `P` in the postcondition, and we have to update the
      state interpretation from `stateInterp _ (m+1) _ _` to
      `stateInterp _ (ns+1) _ _` again

-/
theorem wp_credit_access {s : Stuckness} {E : CoPset}{e : Expr}{Φ}{P: IProp GF} :
  toVal e = none →
  (∀ m k, numLatersPerStep m + numLatersPerStep k ≤ numLatersPerStep (m + k)) →
  (∀ (σ₁ : State) ns obs nt,
    stateInterp σ₁ ns obs nt ={E}=∗
    ∃ k m, stateInterp σ₁ m obs nt ∗ ⌜ns = m + k⌝ ∗ (
      ∀ nt (σ₂: State) obs, £ (numLatersPerStep k) -∗ stateInterp σ₂ (m+1) obs nt ={E}=∗
        stateInterp σ₂ (ns+1) obs nt ∗ P)) ⊢
  WP e @ s ; E {{ v, iprop(P ={E}=∗ Φ v) }} -∗
  WP e @ s ; E {{ Φ }} := by
    intro h Htri
    refine BI.Entails.trans ?_ (BI.wand_mono wp_unfold.1 wp_unfold.2)
    iintro Hupd Hwp
    simp [wp.pre, h]
    iintro %σ₁ %ns %obs %obs' %nt Hσ₁
    imod Hupd $$ Hσ₁ with ⟨%k, %m, Hσ₁, %h, Hpost⟩; subst h
    imod Hwp $$ Hσ₁ with ⟨$,Hwp⟩
    imodintro
    iintro %e₂ %σ₂ %efs %Hstep Hc
    istop; refine (BI.sep_mono .rfl (lc_split.1)).trans ?_; iintro ⟨⟨Hpost,Hwp⟩,Hc⟩
    icases Hc with ⟨Hc,Hone⟩
    ihave Hc := lc_weaken _ (Htri m k) $$ Hc
    istop; refine (BI.sep_mono .rfl (lc_split.1)).trans ?_; iintro ⟨⟨⟨Hpost,Hwp⟩,Hone⟩,Hc⟩
    icases Hc with ⟨Hm, Hk⟩
    -- TODO: Redo with `icombine` when available
    ihave Hm := lc_split.mpr $$ [Hm Hone]
    · iframe
    simp [Nat.repeat]
    ihave Hwp := Hwp $$ [] [Hm]
    · ipure_intro; assumption
    · rw [Nat.add_comm]; exact .rfl
    iapply step_fupd_wand $$ Hwp; iintro Hwp
    iapply step_fupdN_le (n := numLatersPerStep m) (by grind only) (Std.LawfulSet.subset_refl)
    iapply step_fupdN_wand $$ Hwp; iintro >⟨SI, Hwp, $⟩
    icases Hpost $$ Hk SI with >⟨$, HP⟩
    imodintro
    iapply wp_strong_mono (Std.IsPreorder.le_refl s) (Std.LawfulSet.subset_refl) $$ Hwp
    iintro %v HΦ
    iapply HΦ $$ HP

end Wp
