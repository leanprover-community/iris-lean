/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunsong Yang, Michael Sammler
-/

module

public import Iris.BI.BigOp.BigSepList
public import IrisITree.Core.Handler
public import IrisITree.Core.Wpi

public section

namespace IrisITree

open Iris BI ITree Std OFE

@[expose]
def bi_close {PROP : Type _} [BI PROP] {α : Type _} (R : α → α → Prop) (P : α → PROP) : α → PROP :=
  fun a => iprop(∃ a', ⌜R a a'⌝ ∗ P a')

section bi_close

variable {PROP : Type _} [BI PROP] [BIAffine PROP] {α : Type} (R : α → α → Prop)

theorem bi_close_mono (P1 P2 : α → PROP) (a : α) :
    bi_close R P1 a ⊢ (∀ y, P1 y -∗ P2 y) -∗ bi_close R P2 a := by
  iintro Hclose Hwand; simp [bi_close]
  icases Hclose with ⟨%a', %HR, HP1⟩
  iexists a'; isplitr
  · ipureintro; exact HR
  · iapply Hwand $$ HP1

theorem bi_close_intro (P : α → PROP) (a : α) [Href : Std.Refl R] :
    P a ⊢ bi_close R P a := by
  iintro HP; simp [bi_close]
  iexists a; isplitr
  · ipureintro; exact Href.refl a
  · iexact HP

theorem bi_close_respect (P : α → PROP) [Hsym : Symm R] [Htran : Trans R R R] :
    ∀ {x y : α}, R x y → bi_close R P x ⊣⊢ bi_close R P y := by
  intro x y Hxy
  isplit <;> (
    iintro Hclose; simp [bi_close]; icases Hclose with ⟨%a', %Hra, HP⟩;
    iexists a'; isplitr; ipureintro
  )
  · exact Htran.trans (Hsym.symm x y Hxy) Hra
  · iexact HP
  · exact Htran.trans Hxy Hra
  · iexact HP

end bi_close

/-- linear monotone closure of a predicate transformer. -/
def bi_mono0 {PROP : Type _} [BI PROP] {α : Type _} (P : (α → PROP) → PROP) : (α → PROP) → PROP :=
  fun Q => iprop% ∃ Q' : α → PROP, P Q' ∗ ∀ x, Q' x -∗ Q x

section bi_mono0

variable {PROP : Type _} [BI PROP] {α : Type _}

theorem bi_mono0_intro0 (P : (α → PROP) → PROP) (Q : α → PROP) :
    P Q ⊢ bi_mono0 P Q := by
  iintro HP; simp only [bi_mono0]
  iexists Q; isplitl [HP]
  · iexact HP
  · iintro %x HQ; iexact HQ

theorem bi_mono0_mono (P : (α → PROP) → PROP) (Q1 Q2 : α → PROP) :
    bi_mono0 P Q1 ⊢ (∀ x, Q1 x -∗ Q2 x) -∗ bi_mono0 P Q2 := by
  iintro Hm HQ; simp only [bi_mono0]
  icases Hm with ⟨%Q', HP, HQ1⟩
  iexists Q'; isplitl [HP]
  · iexact HP
  · iintro %x HQ'; iapply HQ; iapply HQ1; iapply HQ'

theorem bi_mono0_mono_l (P1 P2 : (α → PROP) → PROP) (Q : α → PROP) :
    bi_mono0 P1 Q ⊢ (∀ Q, P1 Q -∗ P2 Q) -∗ bi_mono0 P2 Q := by
  iintro Hm HP; simp only [bi_mono0]
  icases Hm with ⟨%Q', HP1, HQ1⟩
  iexists Q'; isplitl [HP HP1]
  · iapply HP $$ %Q' HP1
  · iexact HQ1

theorem bi_mono0_elim (P : (α → PROP) → PROP) (Q : α → PROP) :
    bi_mono0 P Q ⊢ (∀ Q Q', (∀ x, Q' x -∗ Q x) -∗ P Q' -∗ P Q) -∗ P Q := by
  iintro Hm HP; simp only [bi_mono0]
  icases Hm with ⟨%Q', HPQ', HQ1⟩
  iapply HP $$ %Q %Q' HQ1 HPQ'

theorem bi_mono0_dup (P : (α → PROP) → PROP) (Q : α → PROP) :
    bi_mono0 (bi_mono0 P) Q ⊢ bi_mono0 P Q := by
  iintro H; simp only [bi_mono0]
  icases H with ⟨%Q', Houter, HQw⟩
  icases Houter with ⟨%Q'', HP, HQw'⟩
  iexists Q''; isplitl [HP]
  · iexact HP
  · iintro %x HQ''; iapply HQw; iapply HQw' $$ HQ''

theorem bi_mono0_intro (P : (α → PROP) → PROP) (Q Q' : α → PROP) :
    P Q' ⊢ (∀ x, Q' x -∗ Q x) -∗ bi_mono0 P Q := by
  iintro HP HQ; simp only [bi_mono0]
  iexists Q'; isplitl [HP]
  · iexact HP
  · iexact HQ

end bi_mono0

/-- One-step rule for a whole thread pool. -/
@[expose]
def lfp_tpF {PROP : Type _} [BI PROP] {α : Type _}
    (F : (α → PROP) → (α → PROP))
    (rec_tp : List ((α → PROP) → PROP) → PROP) :
    List ((α → PROP) → PROP) → PROP :=
  fun Ms => iprop% ∀ i M, ⌜Ms[i]? = some M⌝ -∗ bi_mono0 M fun x => iprop%
    ∃ G, F G x ∗ ∀ Ms', ([∗list] M' ∈ Ms', M' G) -∗ rec_tp (Ms' ++ Ms.eraseIdx i)

section lfp_tpF

variable {PROP : Type _} [BI PROP] [BIAffine PROP] {α : Type _}
  (F : (α → PROP) → (α → PROP))
local bi PROP

instance lfp_tpF_ne : NonExpansive (lfp_tpF F) where
  ne {_ _ _} Hfg := by
    intro Ms; unfold lfp_tpF bi_mono0
    refine forall_ne fun i => forall_ne fun _ => ?_
    refine wand_ne.ne .rfl <| exists_ne fun _ => ?_
    refine sep_ne.ne .rfl <| forall_ne fun _ => ?_
    refine wand_ne.ne .rfl <| exists_ne fun _ => ?_
    refine sep_ne.ne .rfl <| forall_ne fun Ms' => ?_
    exact wand_ne.ne .rfl <| Hfg (Ms' ++ Ms.eraseIdx i)

theorem lfp_tpF_mono (tp1 tp2 : List ((α → PROP) → PROP) → PROP) :
    □ (∀ Ms, tp1 Ms -∗ tp2 Ms) -∗
    ∀ Ms, lfp_tpF F tp1 Ms -∗ lfp_tpF F tp2 Ms := by
  iintro #Hwand %Ms Htp; unfold lfp_tpF
  iintro %i %M %Hi; ispecialize Htp $$ %i %M %Hi
  iapply bi_mono0_mono $$ Htp
  iintro %x ⟨%G, HF, HMS⟩; iexists G; isplitl [HF]
  · iexact HF
  · iintro %Ms HM'; iapply Hwand; iapply HMS $$ HM'

/-- Helper function for [lfp_*_perm_*]. -/
private theorem perm_pick_erase {β : Type _} {Ms1 Ms2 : List β} {i : Nat} {M : β}
    (hperm : Ms1.Perm Ms2) (Hi : Ms2[i]? = some M) :
    ∃ j, Ms1[j]? = some M ∧ (Ms1.eraseIdx j).Perm (Ms2.eraseIdx i) := by
  induction hperm generalizing i M with
  | nil => simp at Hi
  | cons x hperm ih => cases i with
    | zero => simp at Hi; subst M; refine ⟨0, ?_, ?_⟩ <;> simp [*]
    | succ i =>
      simp at Hi; rcases ih Hi with ⟨j, Hj, Hperm⟩
      refine ⟨j + 1, ?_, ?_⟩
      · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Hj
      · simpa [List.eraseIdx_cons_succ] using List.Perm.cons x Hperm
  | swap x y l => cases i with
    | zero => simp at Hi; subst M; refine ⟨1, ?_, ?_⟩ <;> simp
    | succ i => cases i with
      | zero => simp at Hi; subst M; refine ⟨0, ?_, ?_⟩ <;> simp
      | succ i =>
        simp at Hi; refine ⟨i + 2, ?_, ?_⟩
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hi
        · simpa [List.eraseIdx, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using List.Perm.swap x y (l.eraseIdx i)
  | trans h₁ h₂ ih₁ ih₂ =>
    obtain ⟨j₂, Hj₂, Hperm₂⟩ := ih₂ Hi
    obtain ⟨j₁, Hj₁, Hperm₁⟩ := ih₁ Hj₂
    exact ⟨j₁, Hj₁, List.Perm.trans Hperm₁ Hperm₂⟩

theorem lfp_tpF_perm (Ms1 Ms2 : List ((α → PROP) → PROP))
    (wp1 wp2 : List ((α → PROP) → PROP) → PROP) (h : Ms1.Perm Ms2) :
    (∀ Ns1 Ns2, ⌜Ns1.Perm Ns2⌝ -∗ wp1 Ns1 -∗ wp2 Ns2) -∗
    lfp_tpF F wp1 Ms1 -∗
    lfp_tpF F wp2 Ms2 := by
  iintro Hwp Htp; unfold lfp_tpF; iintro %i %M %Hi
  obtain ⟨j, Hj, Herase⟩ := perm_pick_erase h Hi
  ispecialize Htp $$ %j %M %Hj
  iapply bi_mono0_mono $$ Htp
  iintro %x Hstep; icases Hstep with ⟨%G, HFx, Hcont⟩
  iexists G; isplitl [HFx]; iexact HFx
  iintro %Ms' HM'; iapply Hwp $$ %(Ms' ++ Ms1.eraseIdx j)
  · ipureintro; exact (List.perm_append_left_iff Ms').2 Herase
  · iapply Hcont $$ HM'

theorem lfp_tpF_perm_close (Ms1 Ms2 : List ((α → PROP) → PROP))
    (wp : List ((α → PROP) → PROP) → PROP) (h : Ms1.Perm Ms2) :
    lfp_tpF F wp Ms1 -∗
    lfp_tpF F (bi_close (fun a b => a.Perm b) wp) Ms2 := by
  iintro Htp; iapply lfp_tpF_perm _ _ _ _ _ h $$ %_ Htp
  iintro %Ns1 %Ns2 %Hperm Hwp; simp only [bi_close]
  iexists Ns1; isplitr
  · ipureintro; exact Hperm.symm
  · iexact Hwp

/-- Only this abbreviation is built on top of `Discrete0`. -/
private abbrev lfp_tpF_discrete (F : (α → PROP) → (α → PROP))
    (rec_tp : DiscreteO (List ((α → PROP) → PROP)) → PROP) :
    DiscreteO (List ((α → PROP) → PROP)) → PROP :=
  fun Ms => lfp_tpF F (fun l => rec_tp ⟨l⟩) Ms.car

private instance : BIMonoPred (lfp_tpF_discrete F) where
  mono_pred := by
    iintro %Φ %Ψ %HneΦ %HneΨ #Hwand %Ms HΦ
    iapply lfp_tpF_mono F _ _ $$ [] HΦ
    iintro !> %Ms; iapply Hwand
  mono_pred_ne := ne_of_discrete _

end lfp_tpF

/-- Every thread in the pool `Ms` can keep stepping safely according to `F`, however the threads are scheduled. -/
def lfp_tp {PROP : Type _} [BI PROP] {α : Type _} (F : (α → PROP) → (α → PROP))
    (Ms : List ((α → PROP) → PROP)) : PROP :=
  bi_least_fixpoint (lfp_tpF_discrete F) ⟨Ms⟩

section lfp_tp_lemmas

variable {PROP : Type _} [BI PROP] [BIAffine PROP] {α : Type _}
  (F : (α → PROP) → (α → PROP))

theorem lfp_tp_unfold (Ms : List ((α → PROP) → PROP)) :
    lfp_tp F Ms ⊣⊢ lfp_tpF F (fun Ms => lfp_tp F Ms) Ms :=
  equiv_iff.mp <| least_fixpoint_unfold (lfp_tpF_discrete F)

theorem lfp_tp_nil : ⊢ (lfp_tp F [] : PROP) := by
  iapply (lfp_tp_unfold F []).mpr
  simp only [lfp_tpF]
  iintro %i %M %Hi; simp at Hi

/-- Induction theorem on `lfp_tp`. -/
theorem lfp_tp_ind (Φ : List ((α → PROP) → PROP) → PROP) :
    □ (∀ Ms, lfp_tpF F (fun Ms => iprop(Φ Ms ∧ lfp_tp F Ms)) Ms -∗ Φ Ms) -∗
    ∀ Ms, lfp_tp F Ms -∗ Φ Ms := by
  letI := ne_of_discrete fun (Ms : DiscreteO (List ((α → PROP) → PROP))) => Φ Ms.car
  unfold lfp_tp
  iintro #Hwand %Ms Hlfp
  iapply least_fixpoint_ind (lfp_tpF_discrete F) (fun Ms => Φ Ms.car) $$ [] %⟨Ms⟩ Hlfp
  iintro !> %Ms Hpre
  iapply Hwand $$ Hpre

theorem lfp_tp_perm (Ms1 Ms2 : List ((α → PROP) → PROP)) (h : Ms1.Perm Ms2) :
    lfp_tp F Ms1 -∗ lfp_tp F Ms2 := by
  iintro Htp; irevert %Ms2 %h; irevert Htp; irevert %Ms1
  iapply lfp_tp_ind F
  iintro !> %Ms1 Htp %Ms2 %Hperm; iapply lfp_tp_unfold
  iapply lfp_tpF_perm F Ms1 _ _ _ Hperm $$ [] Htp
  iintro %Ns1 %Ns2 %Hperm Hw; icases Hw with ⟨H, -⟩
  iapply H; ipureintro; exact Hperm

theorem lfp_tp_app (Ms1 Ms2 : List ((α → PROP) → PROP)) :
    lfp_tp F Ms1 -∗ lfp_tp F Ms2 -∗
    lfp_tp F (Ms1 ++ Ms2) := by
  iintro Hx1 Hx2; irevert %Ms2 Hx2; irevert Hx1; irevert %Ms1
  iapply lfp_tp_ind F
  iintro !> %Ms1 Hx1 %Ms2 Hx2; irevert %Ms1 Hx1; irevert Hx2; irevert %Ms2
  iapply lfp_tp_ind F
  iintro !> %Ms2 Hx2 %Ms1 Hx1; iapply lfp_tp_unfold; unfold lfp_tpF; simp
  iintro %i %M %Hlookup
  by_cases Hi : i < Ms1.length
  · -- M appears in Ms1
    have Hloc := List.getElem?_append_left Hi ▸ Hlookup
    rw [List.eraseIdx_append_of_lt_length Hi Ms2]
    ispecialize Hx1 $$ %i %M %Hloc; iapply bi_mono0_mono $$ Hx1
    iintro %x ⟨%G, ⟨HF, Hcont⟩⟩
    iexists G; iframe
    iintro %Ms' HMs'; ispecialize Hcont $$ %Ms' HMs'
    icases Hcont with ⟨Happend, -⟩; iapply Happend
    iapply (lfp_tp_unfold F Ms2).mpr; simp only [lfp_tpF]
    iintro %j %N %Hj; ispecialize Hx2 $$ %j %N %Hj
    iapply bi_mono0_mono $$ Hx2
    iintro %x ⟨%G, ⟨HF, Hcont⟩⟩; iexists G; iframe
    iintro %Ms' HMs'; ispecialize Hcont $$ %Ms' HMs'
    iapply Hcont
  · -- M appears in Ms2
    have Hi := Nat.le_of_not_gt Hi
    have Hloc := List.getElem?_append_right Hi ▸ Hlookup
    rw [List.eraseIdx_append_of_length_le Hi Ms2]
    ispecialize Hx2 $$ %(i - Ms1.length) %M %Hloc
    iapply bi_mono0_mono $$ Hx2
    iintro %x ⟨%G, ⟨HF, Hcont⟩⟩; iexists G; iframe
    iintro %Ms' HMs'; ispecialize Hcont $$ %Ms' HMs'
    icases Hcont with ⟨Happend, -⟩
    ispecialize Happend $$ %Ms1 Hx1
    iapply lfp_tp_perm F $$ [$]
    apply List.perm_append_comm_assoc

theorem lfp_tp_cons (M : (α → PROP) → PROP) (Ms : List ((α → PROP) → PROP)) :
    lfp_tp F [M] -∗ lfp_tp F Ms -∗ lfp_tp F (M :: Ms) := by
  simpa using (lfp_tp_app F [M] Ms)

theorem lfp_tp_singleton (M : (α → PROP) → PROP) :
    M (fun x => lfp_tp F [fun P => P x]) -∗ lfp_tp F [M] := by
  iintro Hx; iapply lfp_tp_unfold; simp only [lfp_tpF]
  iintro %i %M' %Hi; cases i with
  | zero =>
    simp at Hi; subst M'; simp only [List.eraseIdx, List.append_nil]
    iapply bi_mono0_intro M $$ Hx; iintro %x Hlfp;
    ihave Hlfp := lfp_tp_unfold F [fun P => P x] $$ Hlfp; simp only [lfp_tpF];
    have Hlookup : ([fun P => P x] : List ((α → PROP) → PROP))[0]? = some (fun P => P x) := by simp
    ispecialize Hlfp $$ %0 %(fun P => P x) %Hlookup
    simp only [List.eraseIdx, List.append_nil]
    iapply bi_mono0_elim $$ Hlfp; iintro %Q %Q' Hwand HQ'
    iapply Hwand $$ HQ'
  | succ n => simp at Hi

variable {α : Type _} [OFE α] [OFE.Discrete α]

theorem lfp_tp_intro (G : (α → PROP) → (α → PROP)) (x : α) :
    bi_least_fixpoint G x -∗ lfp_tp G [fun P => P x] := by
  letI := ne_of_discrete fun (x : α) => lfp_tp G [fun P => P x]
  have Hlist : ∀ Ms, ([∗list] M ∈ Ms, M (fun x => lfp_tp G [fun P => P x])) -∗ lfp_tp G Ms := by
    intro Ms; iinduction Ms with
    | nil => iintro -; iapply lfp_tp_nil
    | cons M Ms IH =>
      iintro HMs
      icases BigSepL.bigSepL_cons $$ HMs with ⟨HM, HMs⟩
      ihave HM := lfp_tp_singleton $$ HM
      iapply lfp_tp_cons G M Ms $$ HM
      iapply IH $$ HMs
  iintro Hlfp; irevert %x Hlfp
  iapply least_fixpoint_iter
  clear this
  iintro !> %x HF; iapply lfp_tp_unfold
  simp only [lfp_tpF]
  iintro %i %M %Hi
  cases i with
  | zero =>
    simp at Hi; subst M
    simp only [List.eraseIdx, List.append_nil]
    iapply bi_mono0_intro0; simp only []
    iexists _; isplitl [HF]
    · iassumption
    · iintro %Ms HMs
      iinduction Ms with
      | nil => iapply lfp_tp_nil
      | cons M Ms IHM =>
        ihave HMs := BigSepL.bigSepL_cons $$ HMs
        icases HMs with ⟨HM, HMs⟩
        ihave HM := lfp_tp_singleton G M $$ HM
        iapply lfp_tp_cons G M Ms $$ HM
        iapply IHM $$ [$]
  | succ i => simp at Hi

end lfp_tp_lemmas

end IrisITree
