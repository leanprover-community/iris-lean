/-
Copyright (c) 2026 Fernando Leal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.ProgramLogic.TotalWeakestPre
public import Iris.ProgramLogic.Adequacy

namespace Iris.ProgramLogic

open Iris OFE COFE BI Iris.BI Iris.Algebra Std FromMathlib LawfulSet
open Language Language.Notation

@[expose] public section

/-! ## Operational termination predicates

`Acc` takes the next configuration as its left argument, so the operational
relation is flipped.  This definition is constructive and means that every
reduction tree rooted at the configuration is finite (strong normalization),
not merely that some execution terminates.

The fork-aware thread-pool predicate below is kept because it is part of the
Iris-Rocq adequacy argument. Thread-pool ghost-state convenience APIs are not
ported: they are unrelated to establishing total-WP termination for the
initial single-threaded Wasm client. Fair termination, trace-sensitive
liveness, and coinductive progress are intentionally outside this layer.
-/

@[rocq_alias sn]
def StronglyNormalizing {α : Type _} (step : α → α → Prop) (x : α) : Prop :=
  Acc (flip step) x

namespace StronglyNormalizing

theorem intro {α : Type _} {step : α → α → Prop} {x : α}
    (H : ∀ y, step x y → StronglyNormalizing step y) :
    StronglyNormalizing step x :=
  Acc.intro x H

theorem of_irreducible {α : Type _} {step : α → α → Prop} {x : α}
    (H : ∀ y, ¬ step x y) : StronglyNormalizing step x :=
  .intro fun y Hxy => (H y Hxy).elim

theorem tail {α : Type _} {step : α → α → Prop} {x y : α}
    (H : StronglyNormalizing step x) (Hxy : step x y) :
    StronglyNormalizing step y :=
  H.inv Hxy

theorem map {α β : Type _} {stepα : α → α → Prop}
    {stepβ : β → β → Prop} (f : β → α)
    (Hlift : ∀ x y, stepβ x y → stepα (f x) (f y))
    {x : β} (H : StronglyNormalizing stepα (f x)) :
    StronglyNormalizing stepβ x := by
  unfold StronglyNormalizing at H ⊢
  generalize hx : f x = z at H
  induction H generalizing x with
  | intro z Hz IH =>
      subst z
      apply Acc.intro
      intro y Hy
      exact IH (f y) (Hlift x y Hy) rfl

end StronglyNormalizing

variable {Expr State Obs Val : Type _} [Λ : Language Expr State Obs Val]

section ThreadPool

variable {hlc : HasLC} {GF : BundledGFunctors}
variable [ι : IrisGS_gen hlc Expr GF]

namespace twptp

local instance : OFE CoPset := OFE.ofDiscrete _
local instance : OFE Expr := OFE.ofDiscrete _
local instance : OFE Val := OFE.ofDiscrete _

private theorem step_append_inv (r₁ r₂ t' : List Expr) (σ₁ σ₂ : State)
    (κ : List Obs) :
    (r₁ ++ r₂, σ₁) -<κ>->ₜₚ (t', σ₂) →
      (∃ r₁', (r₁, σ₁) -<κ>->ₜₚ (r₁', σ₂) ∧
        t'.Perm (r₁' ++ r₂)) ∨
      (∃ r₂', (r₂, σ₁) -<κ>->ₜₚ (r₂', σ₂) ∧
        t'.Perm (r₁ ++ r₂')) := by
  intro H
  generalize hsrc : r₁ ++ r₂ = src at H
  generalize hdst : t' = dst at H
  cases H with
  | @atomic e σ obs e' σ' efs Hprim p q =>
    rcases List.append_eq_append_iff.mp hsrc.symm with
      (⟨mid, hr₁, heq⟩ | ⟨bs, hp, hr₂⟩)
    · cases mid with
      | nil =>
          simp only [List.append_nil] at hr₁
          simp only [List.nil_append] at heq
          subst r₁
          subst r₂
          exact .inr ⟨e' :: q ++ efs, .atomic Hprim [] q, by simp⟩
      | cons a tail =>
          simp only [List.cons_append, List.cons.injEq] at heq
          obtain ⟨rfl, hq⟩ := heq
          subst r₁
          subst q
          refine .inl ⟨p ++ e' :: tail ++ efs, .atomic Hprim p tail, ?_⟩
          have hp := List.Perm.append_left (p ++ [e'])
            (List.Perm.append_left tail
              (List.perm_append_comm :
                (r₂ ++ efs).Perm (efs ++ r₂)))
          simpa only [List.append_assoc, List.singleton_append,
            List.cons_append, List.nil_append] using hp
    · subst p
      subst r₂
      refine .inr ⟨bs ++ e' :: q ++ efs, .atomic Hprim bs q, ?_⟩
      simp only [List.append_assoc]
      exact .refl _

local instance : OFE (List Expr) := OFE.ofDiscrete _

/-- One unfolding of the total thread-pool predicate. Every possible pool step
must be silent, preserve the state interpretation, and recursively establish
the predicate for the complete successor pool. -/
@[rocq_alias twptp_pre]
def pre (X : List Expr → IProp GF) (t₁ : List Expr) : IProp GF := iprop(
  ∀ (t₂ : List Expr) (σ₁ : State) (ns : Nat) (κ κs : List Obs)
      (σ₂ : State) (nt : Nat),
    ⌜(t₁, σ₁) -<κ>->ₜₚ (t₂, σ₂)⌝ -∗
    stateInterp σ₁ ns κs nt ={⊤}=∗
      ∃ nt', ⌜κ = []⌝ ∗ stateInterp σ₂ (ns + 1) κs nt' ∗ X t₂)

instance pre_mono_inst : BIMonoPred (pre (ι := ι)) where
  mono_pred := by
    intro X Y _ _
    iintro #HXY %t₁ Hpre
    unfold pre
    iintro %t₂ %σ₁ %ns %κ %κs %σ₂ %nt %Hstep Hσ
    imod Hpre $$ %t₂ %σ₁ %ns %κ %κs %σ₂ %nt %Hstep Hσ with
      ⟨%nt', %hκ, Hσ, HX⟩
    imodintro
    iexists nt'
    iframe %hκ Hσ
    iapply HXY $$ %t₂ HX
  mono_pred_ne.ne {X} t₁ t₂ ht := by
    change t₁ = t₂ at ht
    subst t₂
    rfl

@[rocq_alias twptp_pre_mono]
theorem pre_mono (X Y : List Expr → IProp GF)
    [NonExpansive X] [NonExpansive Y] :
    ⊢ □ (∀ t, X t -∗ Y t) -∗
      ∀ t, pre (ι := ι) X t -∗ pre (ι := ι) Y t :=
  mono_pred (F := pre (ι := ι))

/-- Least-fixed-point predicate governing all future reductions of a thread
pool. This is the direct Lean counterpart of Iris-Coq's `twptp`. -/
@[rocq_alias twptp]
def get (t : List Expr) : IProp GF :=
  bi_least_fixpoint (pre (ι := ι)) t

instance get_ne : NonExpansive (get (ι := ι)) := by
  constructor
  intro n x y hxy
  change x = y at hxy
  subst y
  rfl

@[rocq_alias twptp_unfold]
theorem unfold (t : List Expr) :
    get (ι := ι) t ⊣⊢ pre (ι := ι) (get (ι := ι)) t := by
  exact BI.equiv_iff.1 (least_fixpoint_unfold (pre (ι := ι)))

@[rocq_alias twptp_ind]
theorem induction (Ψ : List Expr → IProp GF) [NonExpansive Ψ] :
    (⊢ □ ∀ t, pre (ι := ι) (fun t => iprop(Ψ t ∧ get (ι := ι) t)) t -∗ Ψ t) →
    ⊢ ∀ t, get (ι := ι) t -∗ Ψ t := by
  intro H
  have H' : ⊢ □ ∀ t,
      pre (ι := ι) (fun t => iprop(Ψ t ∧
        bi_least_fixpoint (pre (ι := ι)) t)) t -∗ Ψ t := by
    simpa only [get] using H
  iintro %t
  change ⊢ bi_least_fixpoint (pre (ι := ι)) t -∗ Ψ t
  iintro Ht
  iapply least_fixpoint_ind (F := pre (ι := ι)) (Φ := Ψ) $$ [] Ht
  iintro !> %t' Hpre
  iapply H' $$ %t' Hpre

private theorem fold_right (Ψ : List Expr → IProp GF) [NonExpansive Ψ]
    (t : List Expr) :
    pre (ι := ι) (fun t => iprop(Ψ t ∧ get (ι := ι) t)) t ⊢
      get (ι := ι) t := by
  letI : NonExpansive
      (fun t => iprop(Ψ t ∧ get (ι := ι) t)) := by
    constructor
    intro n x y hxy
    change x = y at hxy
    subst y
    rfl
  rw [(twptp.unfold (ι := ι) t).to_eq]
  iintro Hpre
  iapply mono_pred (F := pre (ι := ι)) $$ [] %t Hpre
  iintro !> %u Hu
  icases Hu with ⟨-, Hu⟩
  iexact Hu

@[rocq_alias twptp_Permutation]
theorem permutation {t₁ t₁' : List Expr} (Hp : t₁.Perm t₁') :
    get (ι := ι) t₁ ⊢ get (ι := ι) t₁' := by
  let Ψ := fun t : List Expr => iprop(
    ∀ t', ⌜t.Perm t'⌝ -∗ get (ι := ι) t')
  have hΨ : NonExpansive Ψ := by
    constructor
    intro n x y hxy
    change x = y at hxy
    subst y
    rfl
  letI := hΨ
  iintro Ht
  iapply induction Ψ (ι := ι) ?_ $$ %t₁ Ht %t₁' %Hp
  iintro !> %t Hpre %t' %Htt'
  rw [(twptp.unfold (ι := ι) t').to_eq]
  unfold pre
  iintro %t₂ %σ₁ %ns %κ %κs %σ₂ %nt %Hstep Hσ
  obtain ⟨t₂', H₂perm, Hstep'⟩ :=
    Language.perm_of_step (t₁ := t') (t₁' := t) Htt'.symm Hstep
  imod Hpre $$ %t₂' %σ₁ %ns %κ %κs %σ₂ %nt %Hstep' Hσ with
    ⟨%nt', %hκ, Hσ, HIH⟩
  icases HIH with ⟨HIH, -⟩
  imodintro
  iexists nt'
  iframe %hκ Hσ
  iapply HIH $$ %t₂ %H₂perm.symm

@[rocq_alias twptp_app]
theorem app (t₁ t₂ : List Expr) :
    get (ι := ι) t₁ -∗ get (ι := ι) t₂ -∗ get (ι := ι) (t₁ ++ t₂) := by
  let Ψ₁ := fun t₁ : List Expr => iprop(
    ∀ t₂, get (ι := ι) t₂ -∗ get (ι := ι) (t₁ ++ t₂))
  have hΨ₁ : NonExpansive Ψ₁ := by
    constructor
    intro n x y hxy
    change x = y at hxy
    subst y
    rfl
  letI := hΨ₁
  iintro H₁
  iapply induction Ψ₁ (ι := ι) ?_ $$ %t₁ H₁ %t₂
  let Ψ₂ := fun t₂ : List Expr => iprop(
    ∀ t₁, pre (ι := ι)
      (fun t => iprop(Ψ₁ t ∧ get (ι := ι) t)) t₁ -∗
      get (ι := ι) (t₁ ++ t₂))
  have hΨ₂ : NonExpansive Ψ₂ := by
    constructor
    intro n x y hxy
    change x = y at hxy
    subst y
    rfl
  letI := hΨ₂
  iintro !> %u₁ Hu₁ %u₂ Hu₂
  iapply induction Ψ₂ (ι := ι) ?_ $$ %u₂ Hu₂ %u₁ Hu₁
  iintro !> %r₂ Hr₂ %r₁ Hr₁
  rw [(twptp.unfold (ι := ι) (r₁ ++ r₂)).to_eq]
  unfold pre
  iintro %t' %σ₁ %ns %κ %κs %σ₂ %nt %Hstep Hσ
  rcases step_append_inv r₁ r₂ t' σ₁ σ₂ κ Hstep with
    (⟨r₁', Hstep₁, Hperm⟩ | ⟨r₂', Hstep₂, Hperm⟩)
  · imod Hr₁ $$ %r₁' %σ₁ %ns %κ %κs %σ₂ %nt %Hstep₁ Hσ with
      ⟨%nt', %hκ, Hσ, Hr₁'⟩
    icases Hr₁' with ⟨IH₁, -⟩
    imodintro
    iexists nt'
    iframe %hκ Hσ
    iapply permutation Hperm.symm
    iapply IH₁ $$ %r₂
    iapply fold_right Ψ₂ r₂ (ι := ι)
    unfold pre
    iexact Hr₂
  · imod Hr₂ $$ %r₂' %σ₁ %ns %κ %κs %σ₂ %nt %Hstep₂ Hσ with
      ⟨%nt', %hκ, Hσ, Hr₂'⟩
    icases Hr₂' with ⟨IH₂, -⟩
    imodintro
    iexists nt'
    iframe %hκ Hσ
    iapply permutation Hperm.symm
    iapply IH₂ $$ %r₁
    unfold pre
    iexact Hr₁

private theorem cons (e : Expr) (es : List Expr) :
    get (ι := ι) [e] -∗ get (ι := ι) es -∗ get (ι := ι) (e :: es) := by
  simpa only [List.singleton_append] using app [e] es (ι := ι)

private theorem cons_sep (e : Expr) (es : List Expr) :
    get (ι := ι) [e] ∗ get (ι := ι) es ⊢ get (ι := ι) (e :: es) := by
  iintro H
  icases H with ⟨He, Hes⟩
  iapply cons e es (ι := ι) $$ He Hes

@[rocq_alias twptp_nil]
theorem nil : ⊢ get (ι := ι) ([] : List Expr) := by
  rw [(twptp.unfold (ι := ι) []).to_eq]
  unfold pre
  iintro %t₂ %σ₁ %ns %κ %κs %σ₂ %nt %Hstep
  exfalso
  generalize hsrc : ([] : List Expr) = src at Hstep
  cases Hstep with
  | @atomic e σ obs e' σ' efs Hprim p q =>
      simp at hsrc

private theorem step_singleton_inv (e : Expr) (t₂ : List Expr)
    (σ₁ σ₂ : State) (κ : List Obs) :
    ([e], σ₁) -<κ>->ₜₚ (t₂, σ₂) →
      ∃ e₂ efs, (e, σ₁) -<κ>-> (e₂, σ₂, efs) ∧ t₂ = e₂ :: efs := by
  intro H
  generalize hsrc : [e] = src at H
  generalize hdst : t₂ = dst at H
  cases H with
  | @atomic red σ obs red' σ' efs Hprim p q =>
      have hpq : p = [] ∧ red = e ∧ q = [] := by
        rcases List.append_eq_singleton_iff.mp hsrc.symm with
          (⟨hp, hrest⟩ | ⟨hp, hrest⟩)
        · subst p
          simp only [List.cons.injEq] at hrest
          exact ⟨rfl, hrest.1, hrest.2⟩
        · simp at hrest
      obtain ⟨rfl, rfl, rfl⟩ := hpq
      exact ⟨red', efs, Hprim, by simp_all⟩

private theorem singleton_list (es : List Expr) :
    ([∗list] e ∈ es, get (ι := ι) [e]) ⊢ get (ι := ι) es := by
  induction es with
  | nil =>
      simp only [Algebra.BigOpL.bigOpL_nil]
      iintro _
      exact nil (ι := ι)
  | cons e es IH =>
      simp only [Algebra.BigOpL.bigOpL_cons]
      iintro Hes
      icases Hes with ⟨He, Hes⟩
      rw [show e :: es = [e] ++ es by simp]
      iapply app [e] es (ι := ι) $$ He
      iapply IH
      iexact Hes

@[rocq_alias twp_twptp]
theorem of_twp (s : Stuckness) (e : Expr) (Φ : Val → IProp GF) :
    WP e @ s ; ⊤ [{ Φ }] ⊢ get (ι := ι) [e] := by
  let Ψ := fun (E : CoPset) (e : Expr) (_ : Val → IProp GF) => iprop(
    ⌜E = ⊤⌝ -∗ get (ι := ι) [e])
  have hΨ : NonExpansive
      (fun x : twp.Args Expr Val GF => Ψ x.1.1 x.1.2 x.2) := by
    constructor
    intro n x y hxy
    rcases x with ⟨⟨EX, eX⟩, ΦX⟩
    rcases y with ⟨⟨EY, eY⟩, ΦY⟩
    rcases hxy with ⟨⟨hE, he⟩, _⟩
    change EX = EY at hE
    change eX = eY at he
    subst EY
    subst eY
    rfl
  letI := hΨ
  iintro He
  iapply twp.induction s Ψ (ι := ι) ?_ $$ He %rfl
  iintro !> %E %e %Φ
  cases he : toVal e with
  | some v =>
      simp only [twp.pre, he]
      iintro _ %hE
      subst E
      rw [(twptp.unfold (ι := ι) [e]).to_eq]
      unfold pre
      iintro %t₂ %σ₁ %ns %κ %κs %σ₂ %nt %Hstep
      obtain ⟨e₂, efs, Hprim, rfl⟩ :=
        step_singleton_inv e t₂ σ₁ σ₂ κ Hstep
      have hnone := Language.val_stuck Hprim
      rw [he] at hnone
      cases hnone
  | none =>
      simp only [twp.pre, he]
      iintro Hpre %hE
      subst E
      rw [(twptp.unfold (ι := ι) [e]).to_eq]
      unfold pre
      iintro %t₂ %σ₁ %ns %κ %κs %σ₂ %nt %Hstep Hσ
      obtain ⟨e₂, efs, Hprim, rfl⟩ :=
        step_singleton_inv e t₂ σ₁ σ₂ κ Hstep
      imod Hpre $$ %σ₁ %ns %κs %nt Hσ with ⟨%_, Hpre⟩
      imod Hpre $$ %κ %e₂ %σ₂ %efs %Hprim with
        ⟨%hκ, Hσ, He₂, Hefs⟩
      icases He₂ with ⟨IH₂, -⟩
      imodintro
      iexists (nt + efs.length)
      iframe %hκ Hσ
      iapply cons_sep e₂ efs (ι := ι)
      isplitl [IH₂]
      · iapply IH₂ $$ %rfl
      · iapply singleton_list efs (ι := ι)
        iapply BI.BigSepL.bigSepL_impl $$ Hefs
        iintro !> %k %ef %Hef Hef
        icases Hef with ⟨IHef, -⟩
        iapply IHef $$ %rfl

end twptp

local instance : OFE (List Expr) := OFE.ofDiscrete _

@[rocq_alias twptp_total]
theorem twptp_total (t : List Expr) (σ : State) (ns nt : Nat) :
    stateInterp σ ns ([] : List Obs) nt -∗ twptp.get (ι := ι) t
      ={⊤|}=∗ ⌜StronglyNormalizing
        (Language.ErasedStep (Expr := Expr) (State := State) (Obs := Obs))
        (t, σ)⌝ := by
  let Ψ := fun t : List Expr => iprop(
    ∀ (σ : State) (ns nt : Nat),
      StateInterp.stateInterp (GF := GF) σ ns ([] : List Obs) nt -∗
      |={⊤|}=> ⌜StronglyNormalizing
        (Language.ErasedStep (Expr := Expr) (State := State) (Obs := Obs))
        (t, σ)⌝)
  have hΨ : NonExpansive Ψ := by
    constructor
    intro n x y hxy
    change x = y at hxy
    subst y
    rfl
  letI := hΨ
  iintro Hσ Ht
  iapply twptp.induction Ψ (ι := ι) ?_ $$ %t Ht %σ %ns %nt Hσ
  iintro !> %t
  unfold twptp.pre
  iintro Hpre %σ %ns %nt Hσ
  iapply fupd_finally_mono (pure_mono StronglyNormalizing.intro)
  iintro %cfg₂ %Hstep
  rcases cfg₂ with ⟨t₂, σ₂⟩
  obtain ⟨κ, Hstep⟩ := Hstep
  imod Hpre $$ %t₂ %σ %ns %κ %([] : List Obs) %σ₂ %nt %Hstep Hσ with
    ⟨%nt', %hκ, Hσ, Ht₂⟩
  icases Ht₂ with ⟨IH, -⟩
  iapply IH $$ %σ₂ %(ns + 1) %nt' Hσ

end ThreadPool

omit Λ in
/-- General total adequacy. An initialized state interpretation together with
a total weakest precondition entails strong normalization of the complete
fork-aware language configuration. As in Iris-Coq, the chosen
`numLatersPerStep` is abstract because TWP itself does not inspect it. -/
@[rocq_alias twp_total]
theorem twp_total {hlc : HasLC} {GF : BundledGFunctors}
    [InvGpreS GF] [Language Expr State Obs Val]
    (s : Stuckness) (e : Expr) (σ : State)
    (Φ : Val → IProp GF) (n m : Nat)
    (Hwp : ∀ [InvGS_gen hlc GF],
      ⊢ |={⊤}=>
        ∃ (stateI : State → Nat → List Obs → Nat → IProp GF)
          (numLatersPerStep : Nat → Nat)
          (forkPost : Val → IProp GF)
          (mono : ∀ σ ns obs nt,
            stateI σ ns obs nt ⊢ |={∅}=> stateI σ (ns + 1) obs nt),
        let _ : IrisGS_gen hlc Expr GF :=
          .mk (toStateInterp := ⟨stateI⟩) numLatersPerStep forkPost mono
        iprop(stateI σ n [] 0 ∗
          (£ m -∗ WP e @ s ; ⊤ [{ Φ }]))) :
    StronglyNormalizing
      (Language.ErasedStep (Expr := Expr) (State := State) (Obs := Obs))
      ([e], σ) := by
  apply pure_soundness (PROP := IProp GF)
  apply fupd_finally_soundness hlc m ⊤
  iintro %Hinv Hcred
  imod Hwp with
    ⟨%stateI, %numLatersPerStep, %forkPost, %mono, Hσ, Htwp⟩
  letI iG : IrisGS_gen hlc Expr GF :=
    .mk (toStateInterp := ⟨stateI⟩) numLatersPerStep forkPost mono
  iapply twptp_total [e] σ n 0 (ι := iG) $$ Hσ
  iapply twptp.of_twp s e Φ (ι := iG)
  iapply Htwp $$ Hcred

/-- Erased single-thread reduction. Forked expressions remain visible in the
step witness; clients can rule them out with `LanguageNoFork`. -/
def ExprErasedStep : Expr × State → Expr × State → Prop
  | (e₁, σ₁), (e₂, σ₂) =>
      ∃ (κ : List Obs) (efs : List Expr), (e₁, σ₁) -<κ>-> (e₂, σ₂, efs)

/-- The single-threaded language contract used by the Wasm-facing adequacy
corollaries. -/
class LanguageNoFork (Expr State Obs Val : Type _)
    [Language Expr State Obs Val] : Prop where
  no_fork {e₁ e₂ : Expr} {σ₁ σ₂ : State} {κ : List Obs} {efs : List Expr} :
    (e₁, σ₁) -<κ>-> (e₂, σ₂, efs) → efs = []

theorem exprErasedStep_noFork [LanguageNoFork Expr State Obs Val] {e₁ σ₁ e₂ σ₂}
    (H : ExprErasedStep (Expr := Expr) (State := State) (Obs := Obs)
      (e₁, σ₁) (e₂, σ₂)) :
    ∃ κ, (e₁, σ₁) -<κ>-> (e₂, σ₂, []) := by
  obtain ⟨κ, efs, Hstep⟩ := H
  have := LanguageNoFork.no_fork Hstep
  subst efs
  exact ⟨κ, Hstep⟩

/-- A fork-aware total-adequacy result specializes to the single-expression
machine when the language proves that primitive steps never fork. -/
theorem stronglyNormalizing_expr_of_threadPool
    [LanguageNoFork Expr State Obs Val] {e : Expr} {σ : State}
    (H : StronglyNormalizing
      (Language.ErasedStep (Expr := Expr) (State := State) (Obs := Obs))
      ([e], σ)) :
    StronglyNormalizing
      (ExprErasedStep (Expr := Expr) (State := State) (Obs := Obs))
      (e, σ) := by
  apply StronglyNormalizing.map (fun ρ : Expr × State => ([ρ.1], ρ.2)) ?_ H
  rintro ⟨e₁, σ₁⟩ ⟨e₂, σ₂⟩ ⟨κ, efs, Hstep⟩
  have hefs : efs = [] := LanguageNoFork.no_fork Hstep
  subst efs
  exact ⟨κ, .atomic Hstep [] []⟩

theorem value_stronglyNormalizing (v : Val) (σ : State) :
    StronglyNormalizing (ExprErasedStep (Expr := Expr) (Obs := Obs))
      ((v : Expr), σ) := by
  apply StronglyNormalizing.of_irreducible
  rintro ⟨e₂, σ₂⟩ ⟨κ, efs, Hstep⟩
  exact Language.prim_val_stuck Hstep

end
end Iris.ProgramLogic
