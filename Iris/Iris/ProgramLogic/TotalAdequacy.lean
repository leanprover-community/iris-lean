/-
Copyright (c) 2026 Marcelo Fornet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.ProgramLogic.TotalWeakestPre
public import Iris.ProgramLogic.Adequacy

namespace Iris.ProgramLogic

open Iris OFE COFE BI Iris.BI Iris.Algebra Std FromMathlib LawfulSet
open Language Language.Notation

@[expose] public section

/-! ## Total adequacy -/

/-- Strong normalization for `step`. -/
def StronglyNormalizing {α : Type _} (step : α → α → Prop) (x : α) : Prop :=
  Acc (flip step) x

namespace StronglyNormalizing

theorem intro {α : Type _} {step : α → α → Prop} {x : α}
    (H : ∀ y, step x y → StronglyNormalizing step y) :
    StronglyNormalizing step x := Acc.intro x H

theorem map {α β : Type _} {stepα : α → α → Prop}
    {stepβ : β → β → Prop} (f : β → α)
    (Hlift : ∀ x y, stepβ x y → stepα (f x) (f y))
    {x : β} (H : StronglyNormalizing stepα (f x)) :
    StronglyNormalizing stepβ x :=
  Subrelation.accessible (fun h => Hlift _ _ h) (InvImage.accessible f H)

end StronglyNormalizing

variable {Expr State Obs Val : Type _} [Λ : Language Expr State Obs Val]

section ThreadPool

variable {hlc : HasLC} {GF : BundledGFunctors}
variable [ι : IrisGS_gen hlc Expr GF]

local instance : OFE (List Expr) := OFE.ofDiscrete _

local instance list_nonexpansive (Ψ : List Expr → IProp GF) : NonExpansive Ψ :=
  ⟨fun _ _ _ hxy => hxy ▸ .rfl⟩

namespace twptp

local instance : OFE CoPset := OFE.ofDiscrete _
local instance : OFE Expr := OFE.ofDiscrete _
local instance : OFE Val := OFE.ofDiscrete _

private theorem step_append_inv (r₁ r₂ : List Expr) {t' : List Expr} {σ₁ σ₂ : State} {κ : List Obs} :
    (r₁ ++ r₂, σ₁) -<κ>->ₜₚ (t', σ₂) →
      (∃ r₁', (r₁, σ₁) -<κ>->ₜₚ (r₁', σ₂) ∧
        t'.Perm (r₁' ++ r₂)) ∨
      (∃ r₂', (r₂, σ₁) -<κ>->ₜₚ (r₂', σ₂) ∧
        t'.Perm (r₁ ++ r₂')) := fun H => by
  generalize hsrc : r₁ ++ r₂ = src at H
  rcases H with @⟨e, _, _, e', _, efs, Hprim, p, q⟩
  rcases List.append_eq_append_iff.mp hsrc.symm with (⟨(_ | ⟨a, tail⟩), hr₁, heq⟩ | ⟨bs, hp, hr₂⟩)
  · exact .inr ⟨e' :: q ++ efs, (heq.trans (List.nil_append r₂)) ▸ .atomic Hprim [] q, by simp [hr₁]⟩
  · simp_all only [List.cons_append, List.cons.injEq]
    refine .inl ⟨p ++ e' :: tail ++ efs, .atomic Hprim p tail, ?_⟩
    simpa [List.append_assoc] using List.perm_append_comm.append_left (p ++ e' :: tail)
  · exact .inr ⟨bs ++ e' :: q ++ efs, hr₂ ▸ .atomic Hprim bs q, by simp [hp, List.append_assoc]⟩

/-- One unfolding of the total thread-pool predicate. -/
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
    imod Hpre $$ %_ %_ %_ %_ %_ %_ %_ %Hstep Hσ with ⟨%nt', %hκ, Hσ, HX⟩
    iframe %hκ Hσ
    iapply HXY $$ HX
  mono_pred_ne.ne {X} _ _ ht := ht ▸ .rfl

@[rocq_alias twptp_pre_mono]
theorem pre_mono (X Y : List Expr → IProp GF) :
    ⊢ □ (∀ t, X t -∗ Y t) -∗
      ∀ t, pre (ι := ι) X t -∗ pre (ι := ι) Y t :=
  mono_pred (F := pre (ι := ι))

/-- Total weakest precondition for a thread pool. -/
@[rocq_alias twptp]
def get (t : List Expr) : IProp GF :=
  bi_least_fixpoint (pre (ι := ι)) t

instance get_ne : NonExpansive (get (ι := ι)) :=
  list_nonexpansive _

@[rocq_alias twptp_unfold]
theorem unfold (t : List Expr) :
    get (ι := ι) t ⊣⊢ pre (ι := ι) (get (ι := ι)) t :=
  BI.equiv_iff.1 (least_fixpoint_unfold (pre (ι := ι)))

@[rocq_alias twptp_ind]
theorem induction (Ψ : List Expr → IProp GF) :
    (⊢ □ ∀ t, pre (ι := ι) (fun t => iprop(Ψ t ∧ get (ι := ι) t)) t -∗ Ψ t) →
    ⊢ ∀ t, get (ι := ι) t -∗ Ψ t := fun H => by
  simpa [get, BIBase.EmpValid] using H.trans (BI.wand_entails (least_fixpoint_ind (F := pre (ι := ι)) (Φ := Ψ)))

@[rocq_alias twptp_Permutation]
theorem permutation {t₁ t₁' : List Expr} (Hp : t₁.Perm t₁') :
    get (ι := ι) t₁ ⊢ get (ι := ι) t₁' := by
  iintro Ht
  iapply induction (fun t : List Expr => iprop(∀ t', ⌜t.Perm t'⌝ -∗ get (ι := ι) t'))
    (ι := ι) ?_ $$ %t₁ Ht %t₁' %Hp
  iintro !> %t Hpre %t' %Htt'
  simp only [(twptp.unfold (ι := ι) t').to_eq, pre]
  iintro %t₂ %σ₁ %ns %κ %κs %σ₂ %nt %Hstep Hσ
  obtain ⟨t₂', H₂perm, Hstep'⟩ := Language.perm_of_step Htt'.symm Hstep
  imod Hpre $$ %_ %_ %_ %_ %_ %_ %_ %Hstep' Hσ with ⟨%nt', %hκ, Hσ, ⟨HIH, -⟩⟩
  iframe %hκ Hσ
  iapply HIH $$ %t₂ %H₂perm.symm

@[rocq_alias twptp_app]
theorem app (t₁ t₂ : List Expr) :
    get (ι := ι) t₁ -∗ get (ι := ι) t₂ -∗ get (ι := ι) (t₁ ++ t₂) := by
  let Ψ₁ := fun t₁ : List Expr => iprop(
    ∀ t₂, get (ι := ι) t₂ -∗ get (ι := ι) (t₁ ++ t₂))
  iintro H₁
  iapply induction Ψ₁ (ι := ι) ?_ $$ %t₁ H₁ %t₂
  let Ψ₂ := fun t₂ : List Expr => iprop(
    ∀ t₁, pre (ι := ι)
      (fun t => iprop(Ψ₁ t ∧ get (ι := ι) t)) t₁ -∗
      get (ι := ι) (t₁ ++ t₂))
  iintro !> %u₁ Hu₁ %u₂ Hu₂
  iapply induction Ψ₂ (ι := ι) ?_ $$ %u₂ Hu₂ %u₁ Hu₁
  iintro !> %r₂ Hr₂ %r₁ Hr₁
  simp only [(twptp.unfold (ι := ι) (r₁ ++ r₂)).to_eq, pre]
  iintro %t' %σ₁ %ns %κ %κs %σ₂ %nt %Hstep Hσ
  rcases step_append_inv r₁ r₂ Hstep with (⟨r₁', Hstep₁, Hperm⟩ | ⟨r₂', Hstep₂, Hperm⟩)
  · imod Hr₁ $$ %_ %_ %_ %_ %_ %_ %_ %Hstep₁ Hσ with ⟨%nt', %hκ, Hσ, ⟨IH₁, -⟩⟩
    imodintro
    iframe %hκ Hσ
    iapply permutation Hperm.symm
    iapply IH₁ $$ %r₂
    rw [(twptp.unfold (ι := ι) r₂).to_eq]
    iapply pre_mono (fun t => iprop(Ψ₂ t ∧ get (ι := ι) t)) _ $$ [] %r₂
    iintro !> %u ⟨-, $⟩
    unfold pre
    iassumption
  · imod Hr₂ $$ %_ %_ %_ %_ %_ %_ %_ %Hstep₂ Hσ with ⟨%nt', %hκ, Hσ, ⟨IH₂, -⟩⟩
    iframe %hκ Hσ
    iunfold Ψ₂, pre at IH₂
    iapply permutation Hperm.symm $$ (IH₂ $$ %r₁ Hr₁)

private theorem get_nil : ⊢ get (ι := ι) ([] : List Expr) := by
  simp only [(twptp.unfold (ι := ι) []).to_eq, pre]
  iintro %t₂ %σ₁ %ns %κ %κs %σ₂ %nt %Hstep
  grind [List.append_eq_nil_iff]

private theorem bigSepL_get_singleton (es : List Expr) :
    ([∗list] e ∈ es, get (ι := ι) [e]) ⊢ get (ι := ι) es :=
  List.rec (get_nil (ι := ι)) (fun e es IH =>
    (BI.sep_mono_right IH).trans (BI.wand_elim (BI.wand_entails (app [e] es (ι := ι))))) es

@[rocq_alias twp_twptp]
theorem of_twp (s : Stuckness) (e : Expr) (Φ : Val → IProp GF) :
    WP e @ s ; ⊤ [{ Φ }] ⊢ get (ι := ι) [e] := by
  let Ψ := fun (E : CoPset) (e : Expr) (_ : Val → IProp GF) => iprop(
    ⌜E = ⊤⌝ -∗ get (ι := ι) [e])
  letI : NonExpansive
      (fun x : twp.Internal.Args Expr Val GF => Ψ x.1 x.2.1 x.2.2) :=
    ⟨fun _ _ _ ⟨hE, he, _⟩ => hE ▸ he ▸ .rfl⟩
  iintro He
  iapply twp.induction s Ψ (ι := ι) $$ [] He %rfl
  iintro !> %e %E %Φ
  cases he : toVal e
  all_goals
    simp only [twp.pre, he]
    iintro Hpre %hE
    simp only [hE, (twptp.unfold (ι := ι) [e]).to_eq, pre]
    iintro %t₂ %σ₁ %ns %κ %κs %σ₂ %nt %Hstep
    obtain ⟨e₂, efs, Hprim, rfl⟩ :
        ∃ e₂ efs, (e, σ₁) -<κ>-> (e₂, σ₂, efs) ∧ t₂ = e₂ :: efs := by
      grind [List.append_eq_singleton_iff]
  next =>
    iintro Hσ
    imod Hpre $$ Hσ with ⟨%_, Hpre⟩
    imod Hpre $$ %κ %e₂ %σ₂ %efs %Hprim with ⟨%hκ, Hσ, ⟨IH₂, -⟩, Hefs⟩
    iframe %hκ Hσ
    rw [show e₂ :: efs = [e₂] ++ efs by simp]
    iapply app [e₂] efs (ι := ι) $$ (IH₂ $$ %rfl)
    iapply (BigSepL.bigSepL_mono_of_forall ((sep_intro_emp_valid_left (pure_intro rfl) and_elim_l).trans
      (wand_elim_swap .rfl))).trans (bigSepL_get_singleton efs (ι := ι)) $$ Hefs
  next => simpa [he] using Language.val_stuck Hprim

end twptp

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
  iintro Hσ Ht
  iapply twptp.induction Ψ (ι := ι) ?_ $$ %t Ht %σ %ns %nt Hσ
  iintro !> %t
  unfold twptp.pre
  iintro Hpre %σ %ns %nt Hσ
  iapply fupd_finally_mono (pure_mono StronglyNormalizing.intro)
  iintro %⟨t₂, σ₂⟩ %⟨κ, Hstep⟩
  imod Hpre $$ %_ %_ %_ %_ %_ %_ %_ %Hstep Hσ with ⟨%nt', %hκ, Hσ, ⟨IH, -⟩⟩
  iapply IH $$ %σ₂ %(ns + 1) %nt' Hσ

end ThreadPool

omit Λ in
/-- Total adequacy for thread-pool reduction. -/
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
  refine pure_soundness (PROP := IProp GF) (fupd_finally_soundness hlc m ⊤ _ ?_)
  iintro %Hinv Hcred
  imod Hwp with
    ⟨%stateI, %numLatersPerStep, %forkPost, %mono, Hσ, Htwp⟩
  letI iG : IrisGS_gen hlc Expr GF :=
    .mk (toStateInterp := ⟨stateI⟩) numLatersPerStep forkPost mono
  iapply twptp_total [e] σ n 0 (ι := iG) $$ Hσ
  iapply twptp.of_twp s e Φ (ι := iG) $$ (Htwp $$ Hcred)

/-- Erased single-expression reduction. -/
def ExprErasedStep : Expr × State → Expr × State → Prop
  | (e₁, σ₁), (e₂, σ₂) =>
      ∃ (κ : List Obs) (efs : List Expr), (e₁, σ₁) -<κ>-> (e₂, σ₂, efs)

/-- A language whose primitive steps do not fork. -/
class LanguageNoFork (Expr State Obs Val : Type _)
    [Language Expr State Obs Val] : Prop where
  no_fork {e₁ e₂ : Expr} {σ₁ σ₂ : State} {κ : List Obs} {efs : List Expr} :
    (e₁, σ₁) -<κ>-> (e₂, σ₂, efs) → efs = []

/-- Derive single-expression normalization from thread-pool normalization. -/
theorem stronglyNormalizing_expr_of_threadPool
    [LanguageNoFork Expr State Obs Val] {e : Expr} {σ : State}
    (H : StronglyNormalizing
      (Language.ErasedStep (Expr := Expr) (State := State) (Obs := Obs))
      ([e], σ)) :
    StronglyNormalizing
      (ExprErasedStep (Expr := Expr) (State := State) (Obs := Obs))
      (e, σ) :=
  StronglyNormalizing.map (fun ρ : Expr × State => ([ρ.1], ρ.2))
    (fun _ _ ⟨κ, efs, Hstep⟩ => ⟨κ, by simpa [LanguageNoFork.no_fork Hstep] using Step.atomic Hstep [] []⟩) H

end
end Iris.ProgramLogic
