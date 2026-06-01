/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergei Stepanenko, Zongyuan Liu
-/
module

public import Iris.Algebra
public import Iris.Algebra.Auth
public import Iris.Algebra.Numbers
public import Iris.ProofMode
public import Iris.BI.Algebra
public import Iris.Instances.IProp
public import Iris.Instances.Lib.WSat
public import Iris.Instances.Lib.LaterCredits
public import Iris.BI.Plainly

@[expose] public section

namespace Iris

open Iris OFE COFE BI Auth

section InvG

@[rocq_alias invGpreS]
class InvGpreS (GF : BundledGFunctors) where
  toWsatGpreS : WsatGpreS GF
  toLcGpreS : LcGpreS GF

attribute [reducible, instance] InvGpreS.toWsatGpreS
attribute [reducible, instance] InvGpreS.toLcGpreS

@[rocq_alias invGS_gen]
class InvGS_gen (hlc : outParam HasLC) (GF : BundledGFunctors) extends InvGpreS GF where
  toWsatGS : WsatGS GF
  toLcGS : LcGS hlc GF

attribute [reducible, instance] InvGS_gen.toWsatGS
attribute [reducible, instance] InvGS_gen.toLcGS

abbrev InvGS := InvGS_gen .hasLC

#rocq_ignore «invΣ» "Superseded by the `InvGpreS` typeclass on `BundledGFunctors`."
#rocq_ignore «subG_invΣ» "Superseded by Lean's direct `ElemG` typeclass synthesis."

end InvG

section FUpd

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]

#rocq_ignore uPred_fupd_def "`uPred_fupd` is defined directly without `seal`/`unseal`."
#rocq_ignore uPred_fupd_aux "`uPred_fupd` is defined directly without `seal`/`unseal`."
#rocq_ignore uPred_fupd_unseal "`uPred_fupd` is defined directly without `seal`/`unseal`."

@[rocq_alias uPred_fupd]
def uPred_fupd (E1 E2 : CoPset) (P : IProp GF) : IProp GF :=
  iprop(wsat ∗ ownE E1 -∗ |==£> (wsat ∗ ownE E2 ∗ P))

instance {E1 E2 : CoPset} : NonExpansive (uPred_fupd (GF := GF) (hlc := hlc) E1 E2) where
  ne {_ _ _} h := by
    simp only [uPred_fupd]
    refine wand_ne.ne .rfl ?_
    refine (inferInstance : NonExpansive le_upd).ne ?_
    refine sep_ne.ne .rfl ?_
    refine sep_ne.ne .rfl h

instance uPred_fupd_instance : FUpd (IProp GF) where
  fupd := uPred_fupd

end FUpd

section Instances

open Std.LawfulSet

#rocq_ignore uPred_fupd_mixin "The `BiFUpdMixin` laws are supplied directly when building `uPred_bi_fupd` below."

@[rocq_alias uPred_bi_fupd]
instance uPred_bi_fupd {GF : BundledGFunctors} [InvGS_gen hlc GF] : BIFUpdate (IProp GF) where
  fupd := uPred_fupd
  subset Hsub := by
    simp only [uPred_fupd]
    iintro ⟨$, HE⟩
    rw [diff_subset_decomp Hsub]
    ihave ⟨HE1, $⟩ := (ownE_op (disjoint_symm disjoint_diff_right)).mp $$ HE
    iapply le_upd_intro
    iintro ⟨$, HE⟩
    iapply le_upd_intro
    ihave $ := (ownE_op (disjoint_symm disjoint_diff_right)).mpr $$ [$]
  except0 {E1 E2 P} := by
    simp only [uPred_fupd]
    iintro H Hwe
    imod H
    iapply H $$ Hwe
  mono H := by
    simp only [uPred_fupd]
    iintro Hupd HwE
    iapply le_upd_mono (sep_mono_right (sep_mono_right H))
    iapply Hupd $$ HwE
  trans {_ _ _ _} := by
    simp only [uPred_fupd]
    iintro Hupd HwE
    iapply le_upd_trans
    imod Hupd $$ [$] with ⟨Hw, HE, Hupd⟩
    imodintro
    iapply Hupd $$ [$]
  mask_frame_right_strong {E1 E2 Ef P} Hdisj := by
    simp only [uPred_fupd]
    iintro Hupd ⟨Hwsat, HE⟩
    ihave ⟨HE1, HEf⟩ := ownE_op Hdisj $$ HE
    imod Hupd $$ [Hwsat HE1] with ⟨Hw, HE2, HP⟩
    · iframe
    imodintro
    ihave ⟨%Hdisj', HE⟩ := (ownE_op_iff (E1 := E2) (E2 := Ef)).mpr $$ [HE2 HEf]
    · iframe
    isplitl [Hw]
    · iassumption
    isplitl [HE]
    · iassumption
    iapply HP
    ipure_intro
    exact Hdisj'
  frame_right {_ _ _ _} := by
    simp only [uPred_fupd]
    iintro ⟨Hupd, HR⟩ HwE
    ihave Hupd := Hupd $$ HwE
    ihave Hupd := le_upd_frame_r $$ [$Hupd $HR]
    iapply le_upd_mono ?_ $$ Hupd
    iintro ⟨⟨$, $, $⟩, $⟩

@[rocq_alias uPred_bi_bupd_fupd]
instance {GF : BundledGFunctors} [InvGS_gen hlc GF] : BIUpdateFUpdate (IProp GF) where
  fupd_of_bupd {_ _} := by
    iintro H
    simp only [fupd, uPred_fupd]
    iintro ⟨$, $⟩
    imod H; imodintro
    iassumption

@[rocq_alias uPred_bi_fupd_sbi_no_lc]
instance uPred_bi_fupd_plainly_no_lc {GF : BundledGFunctors} [INV : InvGS_gen .hasNoLC GF] :
    BIFUpdatePlainly (IProp GF) where
  fupd_plainly_keep_left E E' P Q := by
    simp only [fupd, uPred_fupd]
    iintro ⟨H, Hx⟩ ⟨Hwsat, HE⟩
    ihave #>HP : ◇ ■ P $$ [H Hx Hwsat HE]
    · ihave H := H $$ Hx [$]
      icases le_upd_unfold_no_le.mp $$ H with H
      imod H with ⟨_, _, $⟩
    imodintro
    iframe
    iassumption
  fupd_plainly_later _ P := by
    simp only [fupd, uPred_fupd]
    iintro H ⟨Hwsat, HE⟩
    ihave #HP : ▷ ◇ ■ P $$ [H Hwsat HE]
    · inext
      ihave H := H $$ [$]
      icases le_upd_unfold_no_le.mp $$ H with H
      imod H with ⟨_, _, $⟩
    imodintro
    iframe
    inext; imod HP; imodintro
    iapply plainly_elim $$ HP
  fupd_plainly_sForall_2 E P := by
    simp only [fupd, uPred_fupd]
    iintro H ⟨Hwsat, HE⟩
    ihave #HP : ◇ ■ sForall P $$ [H Hwsat HE]
    · ihave H := H $$ [$]
      icases le_upd_unfold_no_le.mp $$ H with H
      imod H with ⟨_, _, $⟩
    imod HP; imodintro
    iframe
    iclear H
    iapply plainly_elim $$ HP

end Instances

section LaterCreditLemmas

@[rocq_alias fupd_unfold_no_lc]
theorem fupd_unfold_no_lc [Hi:InvGS_gen .hasNoLC GF] E1 E2 (P : IProp GF) :
  (|={E1,E2}=> P) ⊣⊢ (wsat ∗ ownE E1 ==∗ ◇ (wsat ∗ ownE E2 ∗ P)) := by
  simp only [fupd, uPred_fupd]
  rw [(le_upd_unfold_no_le (GF := GF)).to_eq]
  exact .rfl

variable {GF : BundledGFunctors} [InvGS GF]

@[rocq_alias lc_fupd_elim_later]
theorem lc_fupd_elim_later {E : CoPset} {P : IProp GF} : ⊢ £ 1 -∗ (▷ P) -∗ |={E}=> P := by
  iintro Hcr HP
  simp only [fupd, uPred_fupd]
  iintro ⟨Hwsat, HE⟩
  iapply le_upd_later $$ Hcr
  inext
  iframe

@[rocq_alias lc_fupd_add_later]
theorem lc_fupd_add_later {E1 E2 : CoPset} {P : IProp GF} : ⊢ £ 1 -∗ (▷ |={E1, E2}=>P) -∗ |={E1, E2}=> P := by
  iintro Hf Hupd
  iapply (BIFUpdate.trans (E1 := E1) (E2 := E1))
  iapply lc_fupd_elim_later $$ Hf Hupd

@[rocq_alias lc_fupd_add_laterN]
theorem lc_fupd_add_laterN (n : Nat) {E : CoPset} {P : IProp GF} :
    ⊢ £ n -∗ (▷^[n] |={E}=> P) -∗ |={E}=> P := by
  induction n generalizing P with
  | zero =>
    iintro _ H
    simp [BIBase.laterN]
    iexact H
  | succ n IH =>
    iintro Hf Hupd
    icases Hf with ⟨H1, Hf⟩
    iapply lc_fupd_add_later $$ H1
    inext
    iapply IH $$ [$] [$]

@[rocq_alias lc_fupd_add_step_fupdN ]
theorem lc_fupd_add_step_fupdN (E1 E2 E3: CoPset) (P : IProp GF) (n : Nat) :
  £ n -∗ (|={E1}[E2]▷=>^[n] |={E1,E3}=> P) -∗ |={E1,E3}=> P := by
  induction n generalizing P with
  | zero =>
    iintro _ H
    simp only [Nat.repeat]
    iexact H
  | succ n IH =>
    iintro Hf Hupd
    simp only [Nat.repeat]
    imod Hupd
    icases Hf with ⟨H1, Hf⟩
    iapply lc_fupd_add_later $$ H1
    inext
    imod Hupd
    iapply IH $$ [$] [$]

end LaterCreditLemmas

section Soundness

@[rocq_alias fupd_finally]
def fupd_finally [InvGS_gen hlc GF] (E : CoPset) (P : IProp GF) : IProp GF :=
  iprop(wsat -∗ ownE E -∗ |==£|> P)

#rocq_ignore fupd_finally_def "Not needed"
#rocq_ignore fupd_finally_aux "Not needed"
#rocq_ignore fupd_finally_unseal "Not needed"


syntax "|={" term "|}=> " term : term
syntax:25 term:26 "={" term "|}=∗ " term:25 : term

macro_rules
  | `(iprop(|={$E|}=> $P))  => ``(fupd_finally $E iprop($P))
  | `(iprop($P ={$E|}=∗ $Q))  => ``(BIBase.wand iprop($P) (fupd_finally $E iprop($Q)))
  | `($P ={$E|}=∗ $Q)  => ``(⊢ $P ={$E|}=∗ $Q)

delab_rule fupd_finally
  | `($_ $E $P) => do
      let P ← Iris.BI.unpackIprop P
      ``(iprop(|={$E|}=> $P))


section fupd_finally

open ProofMode Std

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]

@[rocq_alias fupd_finally_ne]
instance fupd_finally_ne (E : CoPset) : NonExpansive (fupd_finally (GF := GF) (hlc := hlc) E) where
  ne {_ _ _} h := by
    simp only [fupd_finally]
    refine wand_ne.ne .rfl ?_
    refine wand_ne.ne .rfl ?_
    exact le_upd_finally_ne.ne h

@[rocq_alias fupd_finally_mono]
theorem fupd_finally_mono {E : CoPset} {P Q : IProp GF} (H : P ⊢ Q) :
    (|={E|}=> P) ⊢ (|={E|}=> Q) := by
  unfold fupd_finally
  iintro HP Hw HE
  iapply le_upd_finally_mono _ _ H
  iapply HP $$ Hw HE

@[rocq_alias fupd_finally_intro]
theorem fupd_finally_intro (E : CoPset) (P : IProp GF) : ■ P ⊢ |={E|}=> P := by
  unfold fupd_finally
  iintro #HP _ _
  iapply le_upd_finally_intro $$ HP

@[rocq_alias fupd_fupd_finally]
theorem fupd_fupd_finally (E1 E2 : CoPset) (P : IProp GF) :
    (|={E1,E2}=> |={E2|}=> P) ⊢ |={E1|}=> P := by
  simp only [fupd_finally, fupd, uPred_fupd]
  iintro HP Hw HE1
  iapply le_upd_le_upd_finally
  imod HP $$ [$Hw $HE1] with ⟨Hw, HE2, HP⟩
  imodintro
  iapply HP $$ Hw HE2

@[rocq_alias fupd_finally_add_lc]
theorem fupd_finally_add_lc (E : CoPset) (P : IProp GF) :
    (£ 1 -∗ |={E|}=> P) ⊢ |={E|}=> ▷ ◇ P := by
  unfold fupd_finally
  iintro H Hw HE
  iapply le_upd_finally_add_lc
  iintro Hcr
  iapply H $$ Hcr Hw HE

@[rocq_alias fupd_finally_except_0]
theorem fupd_finally_except0 (E : CoPset) (P : IProp GF) : (|={E|}=> ◇ P) ⊢ |={E|}=> P := by
  unfold fupd_finally
  iintro H Hw HE
  iapply le_upd_finally_except0
  iapply H $$ Hw HE

@[rocq_alias fupd_finally_later]
theorem fupd_finally_later (E : CoPset) (P : IProp GF) : ▷ (|={E|}=> P) ⊢ |={E|}=> ▷ ◇ P := by
  unfold fupd_finally
  iintro H Hw HE
  iapply le_upd_finally_later
  inext
  iapply H $$ Hw HE

@[rocq_alias fupd_finally_forall]
theorem fupd_finally_forall (E : CoPset) (Φ : A → IProp GF) :
    (∀ x, |={E|}=> Φ x) ⊢ |={E|}=> ∀ x, Φ x := by
  unfold fupd_finally
  iintro H Hw HE
  iapply le_upd_finally_forall
  iintro %x
  iapply H $$ %x Hw HE

@[rocq_alias fupd_keep]
theorem fupd_keep (E1 E2 : CoPset) (P Q : IProp GF) [TCOr (TCEq hlc .hasNoLC) (Timeless P)] :
    (|={E1|}=> P) ∧ (P -∗ |={E1,E2}=> Q) ⊢ |={E1,E2}=> Q := by
  simp only [fupd_finally, fupd, uPred_fupd]
  iintro H ⟨Hw, HE⟩
  iapply le_upd_keep P
  isplit
  · icases H with ⟨H, -⟩
    iapply H $$ Hw HE
  · iintro HP
    icases H with ⟨-, H⟩
    iapply H $$ HP [$Hw $HE]

@[rocq_alias fupd_finally_keep]
theorem fupd_finally_keep (E : CoPset) (P Q : IProp GF) [TCOr (TCEq hlc .hasNoLC) (Timeless P)] :
    (|={E|}=> P) ∧ (P -∗ |={E|}=> Q) ⊢ |={E|}=> Q := by
  iintro H
  iapply fupd_fupd_finally E E
  iapply fupd_keep E E P
  isplit
  · icases H with ⟨$, -⟩
  · iintro HP
    icases H with ⟨-, H⟩
    iapply fupd_intro
    iapply H $$ HP

@[rocq_alias fupd_finally_mask_mono]
theorem fupd_finally_mask_mono (E1 E2 : CoPset) (P : IProp GF) (H : E1 ⊆ E2) :
    (|={E1|}=> P) ⊢ |={E2|}=> P := by
  iintro Hupd
  iapply fupd_fupd_finally
  iapply fupd_mask_intro_discard H $$ Hupd

@[rocq_alias from_modal_fupd_finally]
instance fromModal_fupd_finally (E : CoPset) (P : IProp GF) :
    FromModal True modality_plainly iprop(|={E|}=> P) iprop(|={E|}=> P) P where
  from_modal _ := fupd_finally_intro E P

@[rocq_alias is_except_0_fupd_finally]
instance isExcept0_fupd_finally (E : CoPset) (P : IProp GF) : IsExcept0 iprop(|={E|}=> P) where
  is_except0 := by
    iintro H
    iapply fupd_fupd_finally E E
    iapply BIFUpdate.except0
    iapply except0_mono fupd_intro $$ H

@[rocq_alias elim_modal_bupd_fupd_finally]
instance elimModal_bupd_fupd_finally p (E : CoPset) (P Q : IProp GF) :
    ElimModal True p false iprop(|==> P) P iprop(|={E|}=> Q) iprop(|={E|}=> Q) where
  elim_modal _ := by
    iintro ⟨H1, H2⟩
    iapply fupd_fupd_finally E E
    icases intuitionisticallyIf_elim $$ H1 with H1
    imod H1
    iapply fupd_intro
    iapply H2 $$ H1

@[rocq_alias elim_modal_fupd_fupd_finally]
instance elimModal_fupd_fupd_finally p (E1 E2 : CoPset) (P Q : IProp GF) :
    ElimModal True p false iprop(|={E1,E2}=> P) P iprop(|={E1|}=> Q) iprop(|={E2|}=> Q) where
  elim_modal _ := by
    iintro ⟨H1, H2⟩
    iapply fupd_fupd_finally E1 E2
    icases intuitionisticallyIf_elim $$ H1 with H1
    imod H1
    iapply H2 $$ H1

@[rocq_alias step_fupdN_fupd_finally]
theorem step_fupdN_fupd_finally (E1 E2 : CoPset) (n : Nat) (P : IProp GF) :
    (|={E1}[E2]▷=>^[n] |={E1|}=> P) ⊢ |={E1|}=> ▷^[n] ◇ P := by
  induction n with
  | zero =>
    simp only [Nat.repeat]
    exact fupd_finally_mono except0_intro
  | succ n IH =>
    iintro HP
    simp only [Nat.repeat]
    imod HP
    iapply fupd_finally_mono (later_laterN n).mpr
    iapply fupd_finally_mono (later_mono (laterN_mono n except0_idem.mp))
    iapply fupd_finally_mono (later_mono (except0_laterN (P := iprop(◇ P)) n))
    iapply fupd_finally_later
    inext
    imod HP
    iapply IH $$ HP

#rocq_ignore fupd_finally_proper "Subsumed by the NonExpansive instance `fupd_finally_ne`"
#rocq_ignore fupd_finally_mono' "Subsumed by `fupd_finally_mono`"
#rocq_ignore fupd_finally_flip_mono' "Subsumed by `fupd_finally_mono`"

@[rocq_alias fupd_finally_and]
theorem fupd_finally_and (E : CoPset) (P Q : IProp GF) :
    (|={E|}=> P) ∧ (|={E|}=> Q) ⊢ |={E|}=> P ∧ Q :=
  and_forall_ite.mp.trans <|
    (forall_mono fun b => by cases b <;> exact .rfl).trans <|
    (fupd_finally_forall E _).trans <| fupd_finally_mono and_forall_ite.mpr

@[rocq_alias fupd_finally_wand]
theorem fupd_finally_wand (E : CoPset) (P Q : IProp GF) :
    (|={E|}=> P) -∗ ■ (P -∗ Q) -∗ (|={E|}=> Q) := by
  iintro Hupd #Hpq
  iapply fupd_finally_mono ((sep_mono_right plainly_elim).trans wand_elim_right)
  iapply fupd_finally_mono plainly_and_sep_right.1
  iapply fupd_finally_mono and_comm.1
  iapply fupd_finally_and
  iframe Hupd
  iapply fupd_finally_intro
  iapply plainly_idem.mpr $$ Hpq

@[rocq_alias fupd_keep_pure]
theorem fupd_keep_pure {E1 E2 : CoPset} (φ : Prop) (E2' : CoPset) (Q : IProp GF) :
    (|={E1,E2'}=> ⌜φ⌝) ∧ (⌜φ⌝ ={E1,E2}=∗ Q) ⊢ |={E1,E2}=> Q := by
  iintro H
  iapply fupd_keep E1 E2 iprop(⌜φ⌝)
  isplit
  · icases H with ⟨H, -⟩
    iapply fupd_fupd_finally E1 E2'
    iapply BIFUpdate.mono (fupd_finally_intro E2' iprop(⌜φ⌝))
    iapply BIFUpdate.mono plainly_pure.mpr $$ H
  · icases H with ⟨-, $⟩

@[rocq_alias fupd_pure_forall]
theorem fupd_pure_forall {A : Type _} (E1 E2 : CoPset) (φ : A → Prop) (H : E2 ⊆ E1) :
    (|={E1,E2}=> ∀ x, ⌜φ x⌝ : IProp GF) ⊣⊢ iprop(∀ x, |={E1,E2}=> ⌜φ x⌝) := by
  refine ⟨fupd_forall, ?_⟩
  · iintro H
    iapply fupd_keep E1 E2 iprop(∀ x, ⌜φ x⌝)
    isplit
    · iapply fupd_finally_forall
      iintro %x
      iapply fupd_fupd_finally
      imod H $$ %x with #Hx
      imodintro
      iapply fupd_finally_intro
      iapply plainly_pure.mpr $$ Hx
    · iintro Hall
      iapply fupd_mask_intro_discard H $$ Hall

@[rocq_alias from_forall_fupd_finally]
instance fromForall_fupd_finally (E : CoPset) (P : IProp GF) (Φ : A → IProp GF)
    [h : FromForall P Φ] : FromForall iprop(|={E|}=> P) (fun a => iprop(|={E|}=> Φ a)) where
  from_forall := (fupd_finally_forall E Φ).trans <| fupd_finally_mono h.from_forall

@[rocq_alias from_pure_fupd_finally]
instance fromPure_fupd_finally (a : Bool) (E : CoPset) (P : IProp GF) (φ : Prop)
    [h : FromPure a P io φ] : FromPure a iprop(|={E|}=> P) io φ where
  from_pure := by
    refine .trans ?_ (fupd_finally_mono h.from_pure)
    refine .trans ?_ (fupd_finally_intro E _)
    cases a <;> simp only [affinelyIf_false, affinelyIf_true] <;> exact Plain.plain

@[rocq_alias from_forall_fupd_pure]
instance fromForall_fupd_pure {A : Type _} (E : CoPset) (P : IProp GF) (Φ : A → IProp GF)
    (φ : A → Prop) [h : FromForall P Φ] [hp : ∀ x, FromPure false (Φ x) .out (φ x)] :
    FromForall iprop(|={E}=> P) (fun a => iprop(|={E}=> ⌜φ a⌝)) where
  from_forall :=
    (fupd_pure_forall E E φ (fun _ h => h)).mpr.trans <|
      (BIFUpdate.mono <| forall_mono fun x => (hp x).from_pure).trans <|
      BIFUpdate.mono h.from_forall

end fupd_finally

open Std.LawfulSet

variable {GF : BundledGFunctors}

@[rocq_alias fupd_finally_soundness]
theorem fupd_finally_soundness (hlc : HasLC) [InvGpreS GF] (n : Nat) (E : CoPset) (P : IProp GF) :
  (∀ (_ : InvGS_gen hlc GF), £ n ⊢ |={E|}=> P) → ⊢ P := by
  unfold fupd_finally
  intro HP
  apply le_upd_finally_soundness (n := n) (hlc := hlc)
  iintro %_ Hf
  iapply le_upd_le_upd_finally
  imod wsat_alloc (GF := GF) with ⟨%W, Hw, HE⟩
  imodintro
  iapply HP (InvGS_gen.mk W _) $$ Hf Hw
  rw [← subset_union_diff (s₁ := E) (s₂ := ⊤) (fun _ _ => CoPset.mem_full)]
  icases ownE_op disjoint_diff_right $$ HE with ⟨$, _⟩
  ipure_intro; trivial

@[rocq_alias fupd_soundness]
theorem fupd_soundness (hlc : HasLC) [InvGpreS GF] (n : Nat) {E1 E2 : CoPset} {P : IProp GF} [Plain P] :
  (∀ (_ : InvGS_gen hlc GF), £ n ={E1,E2}=∗ P) → ⊢ P := by
  intros HP
  apply fupd_finally_soundness hlc n E1
  iintro %_ Hf
  imod HP $$ Hf with #_
  imodintro; iassumption

end Soundness

section StepIndexed

open Iris Std LawfulSet BIFUpdatePlainly

variable {GF : BundledGFunctors}

@[rocq_alias step_fupdN_soundness]
theorem step_fupdN_soundness [InvGpreS GF] (n m : Nat) {P : IProp GF} [Plain P] :
    (∀ (_ : InvGS_gen hlc GF), ⊢ £ m -∗ |={⊤,∅}=> |={∅}▷=>^[n] P) → ⊢ P := by
  intros HP
  apply laterN_soundness (n := n + 1)
  apply fupd_finally_soundness hlc (n := m) (E := ⊤)
  iintro %Hinv Hc
  imod HP $$ Hc with HP
  rw [(laterN_later n).to_eq]
  iapply fupd_finally_mono (laterN_mono _ except0_into_later)
  iapply step_fupdN_fupd_finally
  iapply step_fupdN_wand $$ HP
  iintro #HP !>
  iassumption

@[rocq_alias step_fupdN_soundness']
theorem step_fupdN_soundness_close [InvGpreS GF] (n m : Nat) {P : IProp GF} [Plain P] :
    (∀ (_ : InvGS_gen hlc GF), ⊢ £ m -∗ |={⊤}[∅]▷=>^[n] P) → ⊢ P := by
  intros HP
  apply laterN_soundness (n := n + 1)
  apply fupd_finally_soundness hlc (n := m) (E := ⊤)
  iintro %Hinv Hc
  ihave HP := HP $$ Hc
  rw [(laterN_later n).to_eq]
  iapply fupd_finally_mono (laterN_mono _ except0_into_later)
  iapply step_fupdN_fupd_finally
  iapply step_fupdN_wand $$ HP
  iintro #HP !>
  iassumption

@[rocq_alias fupd_soundness_no_lc_unfold]
theorem fupd_soundness_no_lc_unfold [InvGpreS GF] m E :
  ⊢ |==> ∃ (_: InvGS_gen .hasNoLC GF) (ω : CoPset → IProp GF),
    £ m ∗ ω E ∗ □ (∀ E1 E2 P, (|={E1, E2}=> P) -∗ ω E1 ==∗ ◇ (ω E2 ∗ P)) := by
  imod wsat_alloc with ⟨%W, Hw, HE⟩
  icases (lc_alloc_no_lc m) with ⟨%Hc, _, Hlc⟩
  let Hi := @InvGS_gen.mk .hasNoLC GF (inferInstance) W Hc
  iexists Hi, (λ E => iprop(wsat ∗ ownE E))
  rw [diff_subset_decomp (s₁ := E) (s₂ := ⊤) (fun _ _ => CoPset.mem_full)]
  icases (ownE_op (disjoint_symm disjoint_diff_right)) $$ HE with ⟨_, HE⟩
  -- FIXME: iframe failed without simplication here
  dsimp only
  iframe Hlc Hw HE
  iintro !>!>  %E1 %E2 %P HP HwE
  simp only [fupd, uPred_fupd]
  iapply le_upd_unfold_no_le
  rw [(sep_assoc (R := P)).to_eq]
  iapply HP $$ HwE

end StepIndexed

end Iris

end
