/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Fornet, Zongyuan Liu
-/
module

public import Iris.ProgramLogic.TotalWeakestPre
public import Iris.ProgramLogic.Adequacy

namespace Iris.ProgramLogic

open Iris OFE COFE BI Iris.BI Iris.Algebra Std FromMathlib LawfulSet
open Language Language.Notation

@[expose] public section

/-! ## Total adequacy -/

section ThreadPool

variable {Expr State Obs Val : Type _} [Λ : Language Expr State Obs Val]
variable {hlc : HasLC} {GF : BundledGFunctors}
variable [ι : IrisGS_gen hlc Expr GF]

local instance : OFE (List Expr) := OFE.ofDiscrete _
local instance list_nonexpansive (Ψ : List Expr → IProp GF) : NonExpansive Ψ :=
  ⟨fun _ _ _ hxy => hxy ▸ .rfl⟩
local instance : OFE Val := OFE.ofDiscrete _

namespace twptp


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
def pre (X : List Expr → IProp GF) (t₁ : List Expr) : IProp GF := iprop%
  ∀ (t₂ : List Expr) (σ₁ : State) (ns : Nat) (κ κs : List Obs)
      (σ₂ : State) (nt : Nat),
    ⌜(t₁, σ₁) -<κ>->ₜₚ (t₂, σ₂)⌝ -∗
    stateInterp σ₁ ns κs nt ={⊤}=∗
      ∃ nt', ⌜κ = []⌝ ∗ stateInterp σ₂ (ns + 1) κs nt' ∗ X t₂

@[rocq_alias twptp_pre_mono']
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
    □ (∀ t, X t -∗ Y t) -∗
      ∀ t, pre X t -∗ pre Y t := mono_pred

/-- Total weakest precondition for a thread pool. -/
@[rocq_alias twptp]
def get (t : List Expr) : IProp GF :=
  bi_least_fixpoint pre t

instance get_ne : NonExpansive (get (ι := ι)) := list_nonexpansive _

@[rocq_alias twptp_unfold]
theorem unfold (t : List Expr) :
    get (ι := ι) t ⊣⊢ pre get t :=
  BI.equiv_iff.1 (least_fixpoint_unfold pre)

@[rocq_alias twptp_ind]
theorem induction (Ψ : List Expr → IProp GF) :
    ⊢ (□ ∀ t, pre (fun t => iprop(Ψ t ∧ get t)) t -∗ Ψ t) →
    ∀ t, get t -∗ Ψ t := by
  iintro #IH %t H
  unfold get
  iapply least_fixpoint_ind $$ [$] [$]


@[rocq_alias twptp_Permutation]
theorem permutation {t₁ t₁' : List Expr} (Hp : t₁.Perm t₁') :
    get (ι := ι) t₁ ⊢ get t₁' := by
  iintro Ht
  iapply induction (fun t : List Expr => iprop(∀ t', ⌜t.Perm t'⌝ -∗ get t')) $$ [] %t₁ Ht %t₁' %Hp
  iintro !> %t Hpre %t' %Htt'
  simp only [(twptp.unfold t').to_eq, pre]
  iintro %t₂ %σ₁ %ns %κ %κs %σ₂ %nt %Hstep Hσ
  obtain ⟨t₂', H₂perm, Hstep'⟩ := Language.perm_of_step Htt'.symm Hstep
  imod Hpre $$ %_ %_ %_ %_ %_ %_ %_ %Hstep' Hσ with ⟨%nt', %hκ, Hσ, ⟨HIH, -⟩⟩
  iframe %hκ Hσ
  iapply HIH $$ %t₂ %H₂perm.symm

@[rocq_alias twptp_app]
theorem app (t₁ t₂ : List Expr) :
    get (ι := ι) t₁ -∗ get t₂ -∗ get (t₁ ++ t₂) := by
  let Ψ₁ := fun t₁ : List Expr => iprop% ∀ t₂, get (ι := ι) t₂ -∗ get (t₁ ++ t₂)
  iintro H₁
  iapply induction Ψ₁ $$ [] %t₁ H₁ %t₂
  let Ψ₂ := fun t₂ : List Expr => iprop%
    ∀ t₁, pre (fun t => iprop(Ψ₁ t ∧ get t)) t₁ -∗ get (t₁ ++ t₂)
  iintro !> %u₁ Hu₁ %u₂ Hu₂
  iapply induction Ψ₂ $$ [] %u₂ Hu₂ %u₁ Hu₁
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

@[rocq_alias twp_twptp]
theorem of_twp (s : Stuckness) (e : Expr) (Φ : Val → IProp GF) :
    WP e @ s ; ⊤ [{ Φ }] ⊢ get [e] := by
  let Ψ := fun (E : CoPset) (e : Expr) (_ : Val → IProp GF) => iprop(⌜E = ⊤⌝ -∗ get (ι := ι) [e])
  letI : NonExpansive
      (fun x : twp.Internal.Args Expr Val GF => Ψ x.1 x.2.1 x.2.2) :=
    ⟨fun _ _ _ ⟨hE, he, _⟩ => hE ▸ he ▸ .rfl⟩
  iintro He
  iapply twp.induction s Ψ (ι := ι) $$ [] He %rfl
  iintro !> %e %E %Φ IH %hE
  subst hE
  simp only [(unfold [e]).to_eq, twp.pre, pre]
  iintro %t₂ %σ₁ %ns %κ %κs %σ₂ %nt %Hstep Hσ₁
  obtain ⟨e₂, efs, Hprim, rfl⟩ :
      ∃ e₂ efs, (e, σ₁) -<κ>-> (e₂, σ₂, efs) ∧ t₂ = e₂ :: efs := by
      grind [List.append_eq_singleton_iff]
  cases he: toVal e <;> dsimp only []
  · imod IH $$ Hσ₁ with ⟨%_, Hpre⟩
    imod Hpre $$ %κ %e₂ %σ₂ %efs %Hprim with ⟨%hκ, Hσ, ⟨IH₂, -⟩, Hefs⟩
    iframe %hκ Hσ
    rw [show e₂ :: efs = [e₂] ++ efs by simp]
    iapply app [e₂] efs (ι := ι) $$ (IH₂ $$ %rfl)
    clear Hprim Hstep
    iinduction efs with
    | nil => iapply get_nil
    | cons e ef IH =>
      isimp at Hefs
      icases Hefs with ⟨⟨IH', -⟩, Hefs⟩
      ieval (rewrite [← List.singleton_append])
      iapply app [e] ef $$ [IH']
      · iapply IH' $$ %rfl
      iapply IH $$ Hefs
  · simpa [he] using Language.val_stuck Hprim

end twptp

@[rocq_alias twptp_total]
theorem twptp_total (t : List Expr) (σ : State) (ns nt : Nat) :
    stateInterp σ ns ([] : List Obs) nt -∗ twptp.get (ι := ι) t
      ={⊤|}=∗ ⌜Relation.StronglyNormalizing ErasedStep (t, σ)⌝ := by
  let Ψ := fun t : List Expr => iprop%
    ∀ (σ : State) (ns nt : Nat),
      StateInterp.stateInterp (GF := GF) σ ns ([] : List Obs) nt ={⊤|}=∗
         ⌜Relation.StronglyNormalizing ErasedStep (t, σ)⌝
  iintro Hσ Ht
  iapply twptp.induction Ψ $$ [] %t Ht %σ %ns %nt Hσ
  iintro !> %t IH %σ %ns %nt Hσ
  iapply fupd_finally_mono (pure_mono (Acc.intro _))
  iintro %⟨t₂, σ₂⟩ %⟨κ, Hstep⟩
  unfold twptp.pre
  imod IH $$ %_ %_ %_ %_ %_ %_ %_ %Hstep Hσ with ⟨%nt', %hκ, Hσ, ⟨IH, -⟩⟩
  iapply IH $$ %σ₂ %(ns + 1) %nt' Hσ

end ThreadPool

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
        iprop% stateI σ n [] 0 ∗ (£ m -∗ WP e @ s ; ⊤ [{ Φ }])) :
    Relation.StronglyNormalizing ErasedStep ([e], σ) := by
  refine pure_soundness (PROP := IProp GF) ?_
  refine (fupd_finally_soundness hlc m ⊤ _ ?_)
  iintro %Hinv Hcred
  imod Hwp with ⟨%stateI, %numLatersPerStep, %forkPost, %mono, Hσ, Htwp⟩
  letI iG : IrisGS_gen hlc Expr GF := .mk (toStateInterp := ⟨stateI⟩) numLatersPerStep forkPost mono
  iapply twptp_total [e] _ n _ $$ Hσ
  iapply twptp.of_twp s e Φ $$ (Htwp $$ Hcred)

end
end Iris.ProgramLogic
