/-
Copyright (c) 2026 Fernando Leal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

/--
  Carrier typeclass for the `stateInterp` operation.


  This operation cannot be placed directly inside of `IrisGS_gen`
  because Lean then wouldn't be able to derive from its arguments
  the values of `Expr` and `Val`, and so they're asked explicitly.
  This was not a problem in Iris Rocq becuse of canonical structures.
  In Iris Lean, we instead fix our choice of `State` from the choice
  of `Expr`, so `Expr` cannot be inferred from `State` instead.
-/
class StateInterp
    -- TODO: This probably should be a `semiOutParam`
    (State: Type s)
    (Obs  : outParam <| Type o)
    (GF : BundledGFunctors)
  where
    /--
      Axiomatic interpretation of a state in a language model.
        - `σ` is the state whose interpretation we take
        - `ns` are the number of prior steps (TODO: Check whether true)
        - `obs` are the observations prior to this state
        - `nt` are the number of threads previously spawned

    -/
    stateInterp : State → Nat → List (Obs) → Nat → IProp GF

export StateInterp (stateInterp)

class IrisGS_gen (hlc : outParam <| Bool)
    (Expr  : Type e)
    {Val   : Type v}
    {State : Type s}
    {Obs   : Type o}
    [Λ : Language Expr State Obs Val]
    (GF : BundledGFunctors)
  extends
    StateInterp State Obs GF,
    InvGS_gen hlc GF where

  /--
    Number of later credits obtained from taking one step in the
    operational semantics of our language.
  -/
  -- TODO: Should we have a default of `1`?
  numLatersPerStep : Nat → Nat
  -- TODO: Even when referenced with the typeclass instance, the
  -- display of `numLatersPerStep` is still kinda awful.

  /--
    Postcondition of forked threads
  -/
  -- TODO: Should we have a default of `True`?
  forkPost : Val → IProp GF

  /--
    The number of steps in the state interpretation should only be
    considered a lower bound.
  -/
  stateInterp_mono σ ns obs nt :
    iprop(stateInterp σ ns obs nt ⊢ |={∅}=> stateInterp σ (ns + 1) obs nt)


variable {hlc : outParam Bool}
variable {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors}
variable [ι : IrisGS_gen hlc Expr GF]

instance : IrisGS_gen hlc Expr GF → Language Expr State Obs Val := fun _ => Λ

-- TODO: Move to a better place, probably think of a better name
theorem rw_iProp{P Q : IProp GF} : P ⊣⊢ Q → P = Q := OFE.Leibniz.eq_of_eqv ∘ BI.equiv_iff.mpr

/-- Reducibility condition depending on stuckness.
```lean4
-- s.MaybeReducible (e, σ) equivalent to…
if s matches .NotStuck then Reducible (e, σ) else True
```
-/
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
      £ (ι.numLatersPerStep ns + 1)
      ={∅}▷=∗^[ι.numLatersPerStep ns + 1] |={∅,E}=>
      -- NOTE: Changed the order of `nt` and `eₜ.length` since in Lean
      -- we have `n + 0 = n` and not `0 + n = n`
      stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
      wp E e₂ Φ ∗
      [∗list] e' ∈ eₜ, wp ⊤ e' ι.forkPost)

instance wp.pre.contractive s : OFE.Contractive (wp.pre s (ι := ι)) where
  distLater_dist := by
    intros n wp wp' Hwp E e₁ Φ
    dsimp only [pre]
    cases toVal e₁
    case some _ => exact .rfl
    dsimp only
    refine BI.forall_ne (fun σ₁ => ?_)
    refine BI.forall_ne (fun ns => ?_)
    refine BI.forall_ne (fun obs => ?_)
    refine BI.forall_ne (fun obs' => ?_)
    refine BI.forall_ne (fun nt => ?_)
    refine BI.wand_ne.ne .rfl ?_
    refine BIFUpdate.ne.ne ?_
    refine BI.sep_ne.ne .rfl ?_
    refine BI.forall_ne (fun e₂  => ?_)
    refine BI.forall_ne (fun σ₂ => ?_)
    refine BI.forall_ne (fun eₜ => ?_)
    refine BI.wand_ne.ne .rfl ?_
    refine BI.wand_ne.ne .rfl ?_
    refine BIFUpdate.ne.ne ?_
    refine OFE.Contractive.distLater_dist fun m m_n => ?_
    refine BIFUpdate.ne.ne ?_
    refine step_fupdN_ne.ne ?_
    refine BIFUpdate.ne.ne ?_
    refine BI.sep_ne.ne .rfl ?_
    apply BI.sep_ne.ne
    · apply Hwp m m_n
    · refine BI.BigSepL.bigSepL_dist (fun _ => (Hwp m m_n _ _ _))

@[implicit_reducible]
instance wp.def : Wp (IProp GF) (Expr) (Val) Stuckness where
  wp s := fixpoint (wp.pre s)

section Wp

@[rocq_alias wp_unfold]
theorem wp_unfold {s E} {e : Expr} {Φ : Val → IProp GF} :
    WP e @ s ; E {{ Φ }} ⊣⊢ wp.pre s (Wp.wp (PROP := IProp GF) s) E e Φ :=
  BI.equiv_iff.1 <| fixpoint_unfold (f := (wp.pre s).toContractiveHom) E e Φ

@[rocq_alias wp_ne]
instance wp_ne {s : Stuckness} {E} {e : Expr} :
    OFE.NonExpansive (Wp.wp (PROP := IProp GF) s E e) where
  ne {n Φ₁ Φ₂} HΦ := by
    induction n using Nat.strongRecOn generalizing e E Φ₁ Φ₂ with | ind n IH =>
    simp only [rw_iProp wp_unfold]
    dsimp only [wp.pre]
    cases toVal e
    case some v => exact BIFUpdate.ne.ne <| HΦ v

    -- Composing a bunch of nonexpansive operations…
    refine    BI.forall_ne fun σ₁ => ?_
    refine    BI.forall_ne fun ns => ?_
    refine    BI.forall_ne fun obs => ?_
    refine    BI.forall_ne fun obs' => ?_
    refine    BI.forall_ne fun nt => ?_
    refine   BI.wand_ne.ne .rfl ?_
    refine BIFUpdate.ne.ne ?_
    refine    BI.sep_ne.ne .rfl ?_
    refine    BI.forall_ne fun e₂  => ?_
    refine    BI.forall_ne fun σ₂ => ?_
    refine    BI.forall_ne fun eₜ => ?_
    refine   BI.wand_ne.ne .rfl ?_
    refine   BI.wand_ne.ne .rfl ?_

    -- The `step_fupdN` |={∅}▷=>^[n+1] is contractive
    refine step_fupdN_contractive.distLater_dist fun m n_m => ?_

    refine BIFUpdate.ne.ne ?_
    refine    BI.sep_ne.ne .rfl ?_
    refine    BI.sep_ne.ne ?_ .rfl

    -- We can now apply the induction hypothesis
    apply IH m n_m <| OFE.dist_lt HΦ n_m

#rocq_ignore wp_proper "Derivable using NonExpansive.eqv"

-- This definition comes after `wp_ne` because it depends on it.
@[rocq_alias wp_contractive]
instance wp_contractive (s : Stuckness) E (e : Expr) (h : toVal e = none) :
    OFE.Contractive (Wp.wp (PROP := IProp GF) s E e) where
  distLater_dist {n Φ₁ Φ₂} HΦ := by
    simp only [rw_iProp wp_unfold]
    simp only [wp.pre, h]
    refine BI.forall_ne fun σ₁ => ?_
    refine BI.forall_ne fun ns => ?_
    refine BI.forall_ne fun obs => ?_
    refine BI.forall_ne fun obs' => ?_
    refine BI.forall_ne fun nt => ?_
    refine BI.wand_ne.ne .rfl ?_
    refine BIFUpdate.ne.ne ?_
    refine BI.sep_ne.ne .rfl ?_
    refine BI.forall_ne fun e₂  => ?_
    refine BI.forall_ne fun σ₂ => ?_
    refine BI.forall_ne fun eₜ => ?_
    refine BI.wand_ne.ne .rfl ?_
    refine BI.wand_ne.ne .rfl ?_
    refine step_fupdN_contractive.distLater_dist fun m n_m => ?_
    refine BIFUpdate.ne.ne ?_
    refine BI.sep_ne.ne .rfl ?_
    refine BI.sep_ne.ne ?_ .rfl
    refine wp_ne.ne ?_
    apply HΦ m n_m

@[rocq_alias wp_value_fupd']
theorem wp_value_fupd' {s : Stuckness} {E} {Φ : Val → IProp GF} {v : Val} :
    WP (v : Expr) @ s ; E {{ Φ }} ⊣⊢ |={E}=> Φ v := by
  simp only [rw_iProp wp_unfold, toVal_coe, BI.BIBase.BiEntails.rfl, wp.pre]

@[rocq_alias wp_strong_mono]
theorem wp_strong_mono {s₁ s₂ : Stuckness} {E₁ E₂} {e : Expr} {Φ Ψ : Val → IProp GF} :
    s₁ ≤ s₂ → E₁ ⊆ E₂ →
    ⊢ WP e @ s₁ ; E₁ {{ Φ }} -∗ (∀ v, Φ v ={E₂}=∗ Ψ v) -∗ WP e @ s₂ ; E₂ {{ Ψ }} := by
  intro hs hE
  iloeb as IH generalizing %e %Φ %Ψ %E₁ %E₂ %hE
  rw [rw_iProp wp_unfold, rw_iProp wp_unfold]
  iintro H HΦ
  dsimp only [wp.pre]
  match toVal e with
  | none =>
    dsimp only
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
    dsimp only [Nat.repeat]
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
    dsimp only
    ihave h := fupd_mask_mono hE $$ H
    imod h
    iapply HΦ $$ h

theorem fupd_wp {s : Stuckness}{E}{e : Expr} {Φ : Val → IProp GF} :
    (|={E}=> WP e @ s ; E {{ Φ }}) ⊢ WP e @ s ; E {{ Φ }} := by
  simp only [rw_iProp wp_unfold]
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

-- Easier to use when rewritting
theorem fupd_wp_iff {s : Stuckness}{E}{e : Expr} {Φ : Val → IProp GF} :
    WP e @ s ; E {{ Φ }} ⊣⊢ (|={E}=> WP e @ s ; E {{ Φ }})  := by
  constructor
  · exact fupd_mask_intro_discard Std.LawfulSet.subset_refl
  · exact fupd_wp

theorem wp_fupd (s : Stuckness) E (e : Expr) (Φ : Val → IProp GF) :
    WP e @ s ; E {{v, |={E}=> Φ v }} ⊢ WP e @ s ; E {{ Φ }} := by
  iintro h
  iapply wp_strong_mono (Std.IsPreorder.le_refl _) Std.LawfulSet.subset_refl $$ h
  iintro %v h
  iassumption

theorem wp_atomic {s : Stuckness} {E1 E2 : CoPset} {e : Expr} {Φ : Val → IProp GF}
  [ι : Language.Atomic ↑s e] :
    (|={E1,E2}=> WP e @ s ;  E2 {{v, |={E2,E1}=> Φ v }}) ⊢ (WP e @ s ; E1 {{ Φ }}) := by
  simp only [rw_iProp wp_unfold]
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
    have Hatomic := ι.atomic Hstep
    cases s with -- TODO: Example of place where `match` is worse than `cases`
    | NotStuck =>
      simp only [rw_iProp wp_unfold]
      dsimp only [wp.pre] at Hatomic ⊢
      match h₂ : toVal e2 with
      | some v2 =>
        icases H with > > $
        iframe
      | none =>
        simp only [Stuckness.MaybeReducible]
        icases H $$ %σ2 %(ns +1) %([]) %_ %(nt + efs.length) [Hσ] with >⟨%h, _⟩
        · exact .rfl
        nomatch (Language.not_reducible_iff_irreducible.mpr Hatomic) h
    | MaybeStuck =>
      have ⟨v, h⟩ := Option.isSome_iff_exists.mp (ι.atomic Hstep)
      obtain ⟨rfl⟩ := (ToVal.coe_of_toVal_eq_some h)
      simp only [rw_iProp wp_value_fupd']
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

   3. _After_ `e` has finally stepped, we get `ι.numLatersPerStep k` later credits
      that we can use to prove `P` in the postcondition, and we have to update the
      state interpretation from `stateInterp _ (m+1) _ _` to
      `stateInterp _ (ns+1) _ _` again

-/
theorem wp_credit_access {s : Stuckness} {E : CoPset}{e : Expr}{Φ}{P: IProp GF} :
  toVal e = none →
  (∀ m k, ι.numLatersPerStep m + ι.numLatersPerStep k ≤ ι.numLatersPerStep (m + k)) →
  (∀ (σ₁ : State) ns obs nt,
    stateInterp σ₁ ns obs nt ={E}=∗
    ∃ k m, stateInterp σ₁ m obs nt ∗ ⌜ns = m + k⌝ ∗ (
      ∀ nt (σ₂: State) obs, £ (ι.numLatersPerStep k) -∗ stateInterp σ₂ (m+1) obs nt ={E}=∗
        stateInterp σ₂ (ns+1) obs nt ∗ P)) ⊢
  WP e @ s ; E {{ v, P ={E}=∗ Φ v }} -∗
  WP e @ s ; E {{ Φ }} := by
    intro h Htri
    simp only [rw_iProp wp_unfold]
    iintro Hupd Hwp
    simp only [wp.pre, h]
    iintro %σ₁ %ns %obs %obs' %nt Hσ₁
    imod Hupd $$ Hσ₁ with ⟨%k, %m, Hσ₁, %h, Hpost⟩; subst h
    imod Hwp $$ Hσ₁ with ⟨$,Hwp⟩
    imodintro
    iintro %e₂ %σ₂ %efs %Hstep Hc
    simp only [rw_iProp lc_split]
    icases Hc with ⟨Hc,Hone⟩
    ihave Hc := lc_weaken _ (Htri m k) $$ Hc
    istop; refine (BI.sep_mono .rfl (lc_split.1)).trans ?_; iintro ⟨⟨⟨Hpost,Hwp⟩,Hone⟩,Hc⟩
    icases Hc with ⟨Hm, Hk⟩
    -- TODO: Redo with `icombine` when available
    ihave Hm := lc_split.mpr $$ [Hm Hone]
    · iframe
    simp only [Nat.repeat]
    ihave Hwp := Hwp $$ [] [Hm]
    · ipure_intro; assumption
    · simp only [OFE.Leibniz.eq_of_eqv (BI.equiv_iff.mpr lc_split), OFE.Leibniz.eq_of_eqv (BI.equiv_iff.mpr BI.sep_comm)]
      exact .rfl
    iapply step_fupd_wand $$ Hwp; iintro Hwp
    iapply step_fupdN_le (n := ι.numLatersPerStep m) (by grind only) (Std.LawfulSet.subset_refl)
    iapply step_fupdN_wand $$ Hwp; iintro >⟨SI, Hwp, $⟩
    icases Hpost $$ Hk SI with >⟨$, HP⟩
    imodintro
    iapply wp_strong_mono (Std.IsPreorder.le_refl s) (Std.LawfulSet.subset_refl) $$ Hwp
    iintro %v HΦ
    iapply HΦ $$ HP

theorem wp_step_fupdN_strong {s : Stuckness}{E1 E2 : CoPset} {e : Expr} {P : IProp GF} {Φ} :
    toVal e = none →
    E2 ⊆ E1 →
    ∀ {n},
    -- TODO: This was written as an ∧ in Iris Rocq. I've separated it because it doesn't seem like
    -- icases is able to handle ∧ expressions.
    (∀ (σ : State) ns obs nt, ⊢@{IProp GF} stateInterp σ ns obs nt ={E1, ∅}=∗ ⌜n ≤ ι.numLatersPerStep ns + 1⌝) →
    (|={E1,E2}=> |={∅}▷=>^[n] |={E2,E1}=> P) ∗
    WP e @ s ; E2 {{ v, P ={E1}=∗ Φ v}} ⊢
    WP e @ s ; E1 {{ Φ }} := by
  intro toVal_e E2_E1 n interp
  match n with
  | 0 =>
    iintro ⟨Hp, Hwp⟩
    iapply wp_strong_mono (Std.IsPreorder.le_refl s) E2_E1 $$ Hwp
    iintro %v H
    refine (BI.sep_mono BIFUpdate.trans .rfl).trans ?_; iintro ⟨Hp,H⟩
    imod Hp
    iapply H $$ Hp
  | n+1 =>
    simp only [rw_iProp wp_unfold]
    iintro ⟨Hp,Hwp⟩
    simp only [wp.pre, toVal_e]
    iintro %σ₁ %ns %obs %obs' %nt Hσ₁
    if Hn : n ≤ ι.numLatersPerStep ns then
      imod Hp
      imod Hwp $$ Hσ₁ with ⟨$, H⟩
      iintro !> %e₂ %σ₂ %efs %Hstep Hcred
      icases H $$ %_ %_ %_ %Hstep Hcred with H
      simp only [Nat.repeat]
      imod H; imod Hp
      iintro !> !>
      imod H; imod Hp
      imodintro
      clear interp
      generalize ι.numLatersPerStep ns = n0 at *
      induction n generalizing n0 with
      | zero =>
        iapply step_fupdN_wand $$ H
        iintro >⟨$, Hwp, $⟩
        simp only [Nat.repeat]
        imod Hp
        imodintro
        iapply wp_strong_mono (Std.IsPreorder.le_refl s) E2_E1 $$ Hwp
        iintro %v HΦ
        iapply HΦ $$ Hp
      | succ n IH =>
        obtain ⟨n0, rfl⟩ : ∃ n0', n0 = n0' + 1 := by cases n0 <;> grind only
        simp only [Nat.repeat]
        imod Hp
        imod H
        imodintro
        imodintro
        imod Hp
        imod H
        imodintro
        iapply IH n0 (Nat.le_of_succ_le_succ Hn) $$ [$];
    else
      imod interp $$ Hσ₁ with %h
      grind only

theorem wp_bind (K : Expr → Expr) [κ : Language.Context K] {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    -- TODO: Have `WP` use the correct `Val` type from the `Wp` instance (it should anyways, it's an outParam, no?)
    WP e @ s ; E {{v, WP (K ((v : Val) : Expr)) @ s ; E {{ Φ }} }} ⊢ WP (K e) @ s ; E {{ Φ }} := by
  iintro H
  iloeb as IH generalizing %E %e %Φ
  rewrite (occs := [2]) [rw_iProp wp_unfold]
  simp only [wp.pre]
  match h: toVal e with
  | some v =>
    simp only [ToVal.coe_of_toVal_eq_some h]
    iapply fupd_wp $$ H
  | none =>
    rw [rw_iProp wp_unfold]
    simp only [wp.pre, κ.toVal_eq_none_fill h, Nat.repeat]
    iintro %σ₁ %step %obs %obs' %n Hσ
    imod H $$ [$] with ⟨%_, H⟩
    imodintro
    isplit
    · ipure_intro; grind only [cases Stuckness, Language.Context.reducible_fill]
    iintro %e₂ %σ₂ %efs %HKstep Hcred
    obtain ⟨e₂', rfl, Hstep⟩ := κ.primStep_fill_inv h HKstep
    icases H $$ %e₂' %σ₂ %efs %Hstep Hcred with >H; imodintro; imodintro
    imod H; imodintro; iapply step_fupdN_wand $$ H; iintro H
    imod H with ⟨$, H, $⟩; imodintro; iapply IH $$ H

theorem wp_bind_inv (K : Expr → Expr) [κ : Language.Context K] {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    WP (K e) @ s ; E {{ Φ }} ⊢ WP e @ s ; E {{v, WP (K ((v : Val) : Expr)) @ s ; E {{ Φ }} }} := by
  iintro H
  iloeb as IH generalizing %E %e %Φ
  rewrite (occs := [3]) [rw_iProp wp_unfold]
  simp only [wp.pre]
  match h: toVal e with
  | some v =>
    simp only [ToVal.coe_of_toVal_eq_some h]
    iapply fupd_wp $$ H
  | none =>
    rewrite (occs := [2]) [rw_iProp wp_unfold]
    simp only [wp.pre, κ.toVal_eq_none_fill h, Nat.repeat]
    iintro %σ₁ %step %obs %obs' %n Hσ
    imod H $$ [$] with ⟨%_, H⟩
    imodintro
    isplit
    · ipure_intro; grind only [cases Stuckness, Language.Context.reducible_fill_inv]
    iintro %e₂ %σ₂ %efs %Hstep Hcred
    have HKstep := κ.primStep_fill Hstep
    icases H $$ %(K e₂) %σ₂ %efs %HKstep Hcred with >H; imodintro; imodintro
    imod H; imodintro; iapply step_fupdN_wand $$ H; iintro H
    imod H with ⟨$, H, $⟩; imodintro; iapply IH $$ H

/-! ## Derived rules -/

variable {s : Stuckness} {E : CoPset} {e : Expr}{Φ Ψ : Val → IProp GF} in
theorem wp_mono :
    (∀ v, Φ v ⊢ Ψ v) → WP e @ s ; E {{ Φ }} ⊢ WP e @ s ; E {{ Ψ }} := by
  iintro %HΦ H
  iapply wp_strong_mono (Std.IsPreorder.le_refl s) (Std.LawfulSet.subset_refl) $$ H
  iintro %v HΨ;
  ihave aux := HΦ $$ HΨ
  exact fupd_intro

variable {s₁ s₂ : Stuckness} {E : CoPset} {e : Expr}{Φ : Val → IProp GF} in
theorem wp_stuck_mono :
    s₁ ≤ s₂ → WP e @ s₁; E {{ Φ }} ⊢ WP e @ s₂ ; E {{ Φ }} := by
  iintro %s₁s₂ Hwp
  iapply wp_strong_mono s₁s₂ (Std.LawfulSet.subset_refl) $$ Hwp
  iintro %v HΦ
  exact fupd_intro

variable {s : Stuckness} {E : CoPset} {e : Expr}{Φ : Val → IProp GF} in
theorem wp_stuck_weaken :
    WP e @ s; E {{ Φ }} ⊢ WP e @ E ?{{ Φ }} :=
   wp_stuck_mono (Stuckness.le_MaybeStuck)

variable {s : Stuckness} {E₁ E₂ : CoPset} {e : Expr}{Φ : Val → IProp GF} in
theorem wp_mask_mono : E₁ ⊆ E₂ → WP e @ s; E₁ {{ Φ }} ⊢ WP e @ s; E₂ {{ Φ }} := by
  iintro %E₁_E₂ Hwp
  iapply wp_strong_mono (Std.IsPreorder.le_refl s) E₁_E₂ $$ Hwp
  iintro %v HΦ
  exact fupd_intro

#rocq_ignore wp_mono' "No `Proper` typeclass in Lean"
#rocq_ignore wp_flip_mono' "No `Proper` typeclass in Lean"

variable {s : Stuckness} {E : CoPset} {e : Expr}{v : Val}{Φ : Val → IProp GF} in
theorem wp_value_fupd : Language.IntoVal e v → WP e @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v
  | ⟨h⟩ => h ▸ wp_value_fupd'

variable {s : Stuckness} {E : CoPset} {e : Expr}{v : Val}{Φ : Val → IProp GF} in
theorem wp_value' : Φ v ⊢ WP (v : Expr) @ s; E {{ Φ }} :=
  fupd_intro.trans wp_value_fupd'.2

variable {s : Stuckness} {E : CoPset} {e : Expr}{v : Val}{Φ : Val → IProp GF} in
theorem wp_value : Language.IntoVal e v → Φ v ⊢ WP e @ s; E {{ Φ }}
  | ⟨h⟩ => h ▸ wp_value'

variable {s : Stuckness} {E : CoPset} {e : Expr}{Φ : Val → IProp GF}{R : IProp GF} in
theorem wp_frame_l : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }} := by
  iintro ⟨_, H⟩
  iapply wp_strong_mono (Std.IsPreorder.le_refl s) (Std.LawfulSet.subset_refl) $$ H
  iframe
  iintro %x
  iapply fupd_intro

variable {s : Stuckness} {E : CoPset} {e : Expr}{Φ : Val → IProp GF}{R : IProp GF} in
theorem wp_frame_r : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, R ∗ Φ v }} :=
  BI.sep_comm.1.trans wp_frame_l


variable {s : Stuckness} {E₁ E₂ : CoPset} {e : Expr}{P : IProp GF}{Φ : Val → IProp GF} in
/-- (copy-pasted from Rocq formalization)

  This lemma states that if we can prove that [n] laters are used in
  the current physical step, then one can perform an n-steps fancy
  update during that physical step. The resources needed to prove the
  bound on [n] are not used up: they can be reused in the proof of
  the WP or in the proof of the n-steps fancy update. In order to
  describe this unusual resource flow, we use ordinary conjunction as
  a premise.
-/
theorem wp_step_fupdN {n : Nat} : toVal e = none → E₂ ⊆ E₁ →
    (∀ (σ : State) ns obs nt, ⊢@{IProp GF} stateInterp σ ns obs nt ={E₁,∅}=∗ ⌜n ≤ (ι.numLatersPerStep ns)+1⌝) →
    ((|={E₁\E₂,∅}=> |={∅}▷=>^[n] |={∅,E₁\E₂}=> P) ∗
    WP e @ s; E₂ {{ v, P ={E₁}=∗ Φ v }}) -∗
    WP e @ s; E₁ {{ Φ }} := by
  intro toVal_e E₂E₁ Hstate
  iintro H
  iapply wp_step_fupdN_strong (s := s) (P := P) toVal_e E₂E₁ Hstate $$ [H]
  apply BI.sep_mono_l
  iintro Hp
  imod fupd_mask_subseteq_emptyset_difference (show E₁\ E₂ ⊆ E₁ from Std.LawfulSet.diff_subset_left) with H
  imod Hp
  imod H with toClear; iclear toClear
  simp only [show E₁ \ (E₁ \ E₂) = E₂ from Std.LawfulSet.diff_self_diff_of_subset E₂E₁]
  imodintro
  iapply step_fupdN_wand $$ Hp; iintro H
  iapply fupd_mask_frame (Std.LawfulSet.empty_subset)
  imod H
  imodintro
  simp [Std.LawfulSet.diff_empty, ←Std.LawfulSet.diff_subset_decomp E₂E₁, fupd_intro]

variable {s : Stuckness} {E₁ E₂ : CoPset} {e : Expr}{P : IProp GF}{Φ : Val → IProp GF} in
theorem wp_step_fupd :
    toVal e = none → E₂ ⊆ E₁ →
    (|={E₁}[E₂]▷=> P) -∗ WP e @ s; E₂ {{ v, P ={E₁}=∗ Φ v }} -∗ WP e @ s; E₁ {{ Φ }} :=
  fun toVal_e E₂E₁=> by
  iintro HR H
  iapply wp_step_fupdN_strong (n := 1) toVal_e E₂E₁ (by
    intros; iintro H
    refine .trans ?_ <| fupd_mask_intro_discard (Std.LawfulSet.empty_subset)
    simp [Nat.le_add_left, BI.true_intro]
  ) $$ [-]
  iframe H
  imod HR
  simp only [Nat.repeat]
  iframe

variable {s : Stuckness} {E₁ E₂ : CoPset} {e : Expr}{P : IProp GF}{Φ : Val → IProp GF} {R : IProp GF} in
theorem wp_frame_step_l : toVal e = none → E₂ ⊆ E₁ →
    (|={E₁}[E₂]▷=> R) ∗ WP e @ s; E₂ {{ Φ }} ⊢ WP e @ s; E₁ {{ v, R ∗ Φ v }} := by
  iintro %toVal_e %E₂E₁ ⟨Hu, Hwp⟩
  iapply wp_step_fupd toVal_e E₂E₁ $$ Hu
  iapply wp_mono $$ Hwp
  iintro %x $ $

variable {s : Stuckness} {E₁ E₂ : CoPset} {e : Expr}{P : IProp GF}{Φ : Val → IProp GF} {R : IProp GF} in
theorem wp_frame_step_r : toVal e = none → E₂ ⊆ E₁ →
    WP e @ s; E₂ {{ Φ }} ∗ (|={E₁}[E₂]▷=> R) ⊢ WP e @ s; E₁ {{ v, Φ v ∗ R }} :=
  (BI.sep_comm.1.trans <| wp_frame_step_l · · |>.trans <| wp_mono (fun _ => BI.sep_comm.1))

variable {s : Stuckness} {E₁ E₂ : CoPset} {e : Expr}{Φ : Val → IProp GF} {R : IProp GF} in
theorem wp_frame_step_l' : toVal e = none → E₂ ⊆ E₁ →
    (▷ R) ∗ WP e @ s; E₂ {{ Φ }} ⊢ WP e @ s; E₁ {{ v, R ∗ Φ v }} := by
  iintro %toVal_e %E₂E₁ ⟨Hu, Hwp⟩
  iapply wp_frame_step_l toVal_e E₂E₁
  iframe
  iapply fupd_mask_intro E₂E₁
  iintro _
  imodintro
  apply BIFUpdate.mono
  exact BI.true_intro

variable {s : Stuckness} {E₁ E₂ : CoPset} {e : Expr}{Φ : Val → IProp GF} {R : IProp GF} in
theorem wp_frame_step_r' : toVal e = none → E₂ ⊆ E₁ →
     WP e @ s; E₂ {{ Φ }} ∗ (▷ R) ⊢ WP e @ s; E₁ {{ v, Φ v ∗ R }} :=
  (BI.sep_comm.1.trans <| wp_frame_step_l' · · |>.trans <| wp_mono (fun _ => BI.sep_comm.1))

variable {s : Stuckness} {E : CoPset} {e : Expr}{Φ Ψ : Val → IProp GF} in
theorem wp_wand :
    WP e @ s ; E {{ Φ }} ⊢ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s ; E {{ Ψ }} := by
  iintro Hwp H
  iapply wp_strong_mono (Std.IsPreorder.le_refl s) (Std.LawfulSet.subset_refl) $$ Hwp
  iintro %v HΦ
  icases H $$ HΦ with H
  exact fupd_intro

variable {s : Stuckness} {E : CoPset} {e : Expr}{Φ : Val → IProp GF} in
theorem wp_wand_l :
    (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s ; E {{ Φ }} ⊢ WP e @ s ; E {{ Ψ }} :=
  BI.wand_elim' wp_wand

variable {s : Stuckness} {E : CoPset} {e : Expr}{Φ : Val → IProp GF} in
theorem wp_wand_r :
    WP e @ s ; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s ; E {{ Ψ }} :=
  BI.wand_elim wp_wand

variable {s : Stuckness} {E : CoPset} {e : Expr}{Φ :Val → IProp GF}{R : IProp GF} in
theorem wp_frame_wand :
    R ⊢ WP e @ s; E {{ v, R -∗ Φ v }} -∗ WP e @ s; E {{ Φ }} := by
  iintro R Hwp
  iapply wp_wand $$ Hwp
  iintro %v H
  iapply H $$ R

end Wp

section ProofModeClasses

open ProofMode

variable {hlc : outParam Bool}
variable {Expr State Obs Val : Type _}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors}
variable [ι : IrisGS_gen hlc Expr GF]

variable {s : Stuckness} {E : CoPset} {e : Expr} {v : Val} {Φ Ψ : Val → IProp GF} {P Q R : IProp GF}

instance frameWp {p : Bool} [H : ∀ v, Frame p R (Φ v) (Ψ v)] :
    -- TODO: I didn't move over the `FrameInstantiateExistDisabled` constant. Ask if it's necessary.
    Frame p R (WP e @ s ; E {{ Φ }}) (WP e @ s ; E {{ Ψ }}) where
  frame := by
    replace H v := (H v).frame
    refine wp_frame_l.trans ?_
    apply wp_mono
    apply H

instance isExcept0Wp : IsExcept0 (WP e @ s ; E {{ Φ }}) where
  is_except0 :=
    calc iprop(◇ _)
      _ ⊢ ◇ |={E}=> _ := BI.except0_mono fupd_intro
      _ ⊢ |={E}=> _ := BIFUpdate.except0
      _ ⊢ WP e @ s ; E {{ Φ }} := fupd_wp

instance elimModalFupdWp p :
    ElimModal True p false iprop(|={E}=> P) P (WP e @ s ; E {{ Φ }}) (WP e @ s ; E {{ Φ }}) where
  elim_modal := by
    rintro ⟨⟩; iintro ⟨H, H⟩
    refine (BI.sep_mono BI.intuitionisticallyIf_elim .rfl).trans ?_
    refine fupd_frame_r.trans ?_
    refine BIFUpdate.mono BI.wand_elim_r |>.trans ?_
    exact fupd_wp

/--
  Error message instance for non-mask-changing view shifts.  Also uses a slightly
  different error: we cannot apply `fupd_mask_subseteq` if `e` is not atomic, so
  we tell the user to first add a leading `fupd` and then change the mask of that.
-/
instance elimModalFupdWp_wrongMask :
    ElimModal (PMError "Goal and eliminated modality must have the same mask.
    Use `iapply fupd_wp; imod (fupd_mask_subseteq E₂)` to adjust the mask of your goal to `E₂`")
    p false iprop(|={E₂}=> P) iprop(False) (WP e @ s ; E₁ {{ Φ }}) iprop(False) where
  elim_modal := nofun

instance elimModalFupdWpAtomic :
    ElimModal (Language.Atomic ↑s e) p false iprop(|={E₁,E₂}=> P) P (WP e @ s ; E₁ {{ Φ }}) (WP e @ s ; E₂ {{ v, |={E₂,E₁}=> Φ v}}) where
  elim_modal := by
    rintro atomic; iintro ⟨H, H⟩
    refine (BI.sep_mono BI.intuitionisticallyIf_elim .rfl).trans ?_
    refine fupd_frame_r.trans ?_
    refine BIFUpdate.mono BI.wand_elim_r |>.trans ?_
    exact wp_atomic

instance elimModalFupdWpAtomic_wrongMask :
    ElimModal (PMError "Goal and eliminated modality must have the same mask.
    Use `iapply fupd_wp; imod (fupd_mask_subseteq E₂)` to adjust the mask of your goal to `E₂`")
    p false iprop(|={E₁,E₂}=> P) iprop(False) (WP e @ s ; E₁ {{ Φ }}) iprop(False) where
  elim_modal := nofun

-- instance addModalFupdWp :
--     ProofMode.AddModal iprop(|={E}=> P) P (WP e @ s ; E {{ Φ }}) where
--   add_modal := by
--     refine fupd_frame_r.trans ?_
--     refine BIFUpdate.mono BI.wand_elim_r |>.trans ?_
--     exact fupd_wp

-- instance elimAccWpAtomic :
--     ElimAcc (X := X) (Atomic ↑s e)
--       (fupd E₁ E₂) (fupd E₂ E₁)
--       α β γ (WP e @ s ; E₁ {{ Φ}})
--       iprop(λ x ↦ WP e @ s ; E₂ {{ v, iprop(|={E₂}=> β x ∗ (γ x -∗? Φ v)) }}) where
--     elim_acc := sorry

-- instance elimAccWpNonAtomic :
--     ElimAcc (X := X) True
--       (fupd E E) (fupd E E)
--       α β γ (WP e @ s ; E {{ Φ}})
--       iprop(λ x ↦ WP e @ s ; E {{ v, iprop(|={E}=> β x ∗ (γ x -∗? Φ v)) }}) where
--     elim_acc := sorry

end ProofModeClasses
