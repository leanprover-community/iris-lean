/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergei Stepanenko, Zongyuan Liu
-/
module

public import Iris.Std.TC
public import Iris.Algebra
public import Iris.Algebra.Auth
public import Iris.Algebra.Numbers
public import Iris.ProofMode
public import Iris.BI.Algebra
public import Iris.Instances.IProp

@[expose] public section

/-! ## Later credits -/

namespace Iris

open _root_.Std (Associative Commutative LeftIdentity LawfulLeftIdentity)
open Iris OFE COFE BI Auth CommMonoidLike Std

section LcGS

abbrev Credit := Nat

@[rocq_alias has_lc]
inductive HasLC where
| hasNoLC
| hasLC

scoped instance : Associative (Add.add (α := Credit)) := ⟨Nat.add_assoc⟩
scoped instance : Commutative (Add.add (α := Credit)) := ⟨Nat.add_comm⟩
scoped instance : LeftIdentity (Add.add (α := Credit)) (0 : Credit) where
scoped instance : LawfulLeftIdentity (Add.add (α := Credit)) (0 : Credit) := ⟨Nat.zero_add⟩
scoped instance : LeftCancelAdd Credit := ⟨Nat.add_left_cancel⟩

scoped instance : COFE Credit := COFE.ofDiscrete _ Eq_Equivalence
scoped instance : Discrete Credit := ⟨congrArg id⟩
scoped instance : Leibniz Credit := ⟨congrArg id⟩
scoped instance : UCMRA Credit := CommMonoidLike.instUCMRA
scoped instance : CMRA.Discrete Credit := CommMonoidLike.instDiscrete
scoped instance {a : Credit} : CMRA.Cancelable a := inferInstance

/-- Later credits inclusion typeclass (`GF` contains the necessary functors for later credits) -/
@[rocq_alias lcGpreS]
class LcGpreS (GF : BundledGFunctors) where
  lc_elem : ElemG GF (AuthURF (F := PNat) (constOF Credit))

attribute [reducible, instance] LcGpreS.lc_elem

@[rocq_alias lcGS]
class LcGS (hlc : outParam HasLC) (GF : BundledGFunctors)  extends LcGpreS GF where
  lc_name : GName

#rocq_ignore «lcΣ» "Superseded by the `LcGpreS` typeclass on `BundledGFunctors`."
#rocq_ignore «subG_lcΣ» "Superseded by Lean's direct `ElemG` typeclass synthesis."

end LcGS

section Definitions

variable {GF : BundledGFunctors} {hlc : HasLC} [LC : LcGS hlc GF]

#rocq_ignore lc_def "`lc` is defined directly without `seal`/`unseal`."
#rocq_ignore lc_aux "`lc` is defined directly without `seal`/`unseal`."
#rocq_ignore lc_unseal "`lc` is defined directly without `seal`/`unseal`."

@[rocq_alias lc]
def lc (i : Credit) : IProp GF :=
  match hlc with
  | .hasLC => iOwn (E := LC.lc_elem) LC.lc_name (◯ i)
  | .hasNoLC => iprop(True)

notation:max "£ " i:40 => lc i

#rocq_ignore lc_supply_def "`lc_supply` is defined directly without `seal`/`unseal`."
#rocq_ignore lc_supply_aux "`lc_supply` is defined directly without `seal`/`unseal`."
#rocq_ignore lc_supply_unseal "`lc_supply` is defined directly without `seal`/`unseal`."

@[rocq_alias lc_supply]
def lc_supply (i : Credit) : IProp GF :=
  match hlc with
  | .hasLC => iOwn (E := LC.lc_elem) LC.lc_name (● i)
  | .hasNoLC => iprop(⌜i = 0⌝)

end Definitions

section Operations

variable {GF : BundledGFunctors} {hlc : HasLC} [LC : LcGS hlc GF]

@[rocq_alias lc_split]
theorem lc_split {n m} : £ (n + m) ⊣⊢@{IProp GF} £ n ∗ £ m := by
  cases hlc with
  | hasNoLC =>
    simp only [lc]
    exact (true_sep (P := iprop(True))).symm
  | hasLC =>
    -- FIXME: Timeout on iOwn_op. Why?
    -- Specifying (F := (AuthURF (F := PNat) (constOF Credit))) (a1 := ◯ n) (a2 := ◯ m) fixes it, but it is too verbose.
    simp only [lc]
    refine .trans ?_ iOwn_op
    exact .rfl

@[rocq_alias lc_no_lc]
theorem lc_no_lc [LcGS .hasNoLC GF] (n : Credit) : £ n ⊣⊢@{IProp GF} iprop(True) := .rfl

@[rocq_alias lc_supply_no_lc]
theorem lc_supply_no_lc [LcGS .hasNoLC GF] (n : Credit) :
    lc_supply n ⊣⊢@{IProp GF} iprop(⌜n = 0⌝) := .rfl

@[rocq_alias lc_zero]
theorem lc_zero : ⊢@{IProp GF} |==> £ 0 := by
  cases hlc with
  | hasNoLC => simp only [lc]; itrivial
  | hasLC => exact iOwn_unit (ε := UCMRA.unit)

section LcSupplyRules
variable [LC : LcGS .hasLC GF]

@[rocq_alias lc_supply_bound]
theorem lc_supply_bound {n m} : ⊢@{IProp GF} lc_supply m -∗ £ n -∗ ⌜n ≤ m⌝ := by
  iintro Hsupp Hcred
  icases iOwn_op $$ [Hsupp Hcred] with H
  · unfold lc lc_supply
    isplitl [Hsupp] <;> iassumption
  ihave H := iOwn_cmraValid $$ H
  ihave ⟨%H, H2⟩ := auth_both_validI m n $$ H
  ipureintro
  obtain ⟨k, rfl⟩ := H
  exact n.le_add_right k

@[rocq_alias lc_decrease_supply]
theorem lc_decrease_supply {n m} : ⊢@{IProp GF} lc_supply (n + m) -∗ £ n -∗ |==> lc_supply m := by
  iintro H1 H2
  imod iOwn_update_op (E := LC.lc_elem)
    (auth_update (leftCancelAdd_local_update ((Nat.add_assoc n m 0).trans (Nat.add_comm n m))))
    $$ [H1 H2] with H
  · unfold lc lc_supply
    isplitl [H1] <;> iassumption
  icases iOwn_op $$ H with ⟨H, _⟩
  imodintro
  unfold lc_supply; iexact H

@[rocq_alias lc_increase_supply]
theorem lc_increase_supply n m : lc_supply m ⊢@{IProp GF} |==> (lc_supply (n + m) ∗ £ n) := by
unfold lc lc_supply
iintro H
imod iOwn_update $$ H with Hown
· exact auth_update_alloc (leftCancelAdd_local_update (y := 0) (x' := (n + m)) (y' := n) (by grind))
icases iOwn_op $$ Hown with ⟨Hm, _⟩
iframe

end LcSupplyRules

@[rocq_alias lc_succ]
theorem lc_succ {n} : £ (.succ n) ⊣⊢@{IProp GF} £ 1 ∗ £ n := by
  rw [show .succ n = 1 + n by simp [Nat.succ_eq_add_one, Nat.add_comm]]
  exact lc_split

@[rocq_alias lc_weaken]
theorem lc_weaken {n} m (h : m ≤ n) : ⊢@{IProp GF} £ n -∗ £ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  iintro H
  ihave ⟨H, _⟩ := lc_split $$ H
  iexact H

@[rocq_alias lc_timeless]
instance {n} : Timeless (PROP := IProp GF) (£ n) := by
  unfold lc
  cases hlc <;> infer_instance

@[rocq_alias lc_0_persistent]
instance : Persistent (PROP := IProp GF) (£ 0) := by
  unfold lc
  cases hlc <;> infer_instance

end Operations

section ProofMode

open ProofMode

variable {GF : BundledGFunctors} {hlc : HasLC} [LcGS hlc GF]

@[rocq_alias from_sep_lc_add]
instance (priority := default - 10) {n m} : FromSep (PROP := IProp GF) (£ (n + m)) (£ n) (£ m) where
  from_sep := lc_split.mpr

@[rocq_alias from_sep_lc_S]
instance (priority := default) {n} : FromSep (PROP := IProp GF) (£ (.succ n)) (£ 1) (£ n) where
  from_sep := lc_succ.mpr

-- TODO: combine_sep_lc_add, combine_sep_lc_S_l

@[rocq_alias into_sep_lc_add]
instance (priority := default - 10) {n m} : IntoSep (PROP := IProp GF) (£ (n + m)) (£ n) (£ m) where
  into_sep := lc_split.mp

@[rocq_alias into_sep_lc_S]
instance (priority := default) {n} : IntoSep (PROP := IProp GF) (£ (.succ n)) (£ 1) (£ n) where
  into_sep := lc_succ.mp

@[rocq_alias combine_sep_lc_add]
instance (priority := default) {n} : CombineSepAs (PROP := IProp GF) (£ n) (£ m) (£ (n + m)) where
  combine_sep_as := lc_split.mpr

#rocq_ignore combine_sep_lc_S_l "Not necessary in Lean as it is more common to use +1 instead of .succ"

end ProofMode

section Upd

variable {GF : BundledGFunctors} {hlc : HasLC} [LcGS hlc GF]

@[rocq_alias le_upd.le_upd_pre]
def le_upd_pre (P le_upd : IProp GF) : IProp GF :=
  iprop(∀ n, lc_supply n ==∗
    ▷^[n.succ] False ∨
    (lc_supply n ∗ P) ∨
    (∃ m, ⌜m < n⌝ ∗ lc_supply m ∗ ▷ le_upd))

@[rocq_alias le_upd.le_upd_pre_contractive]
instance {P : IProp GF} : Contractive (le_upd_pre P) where
  distLater_dist {n x y} H := by
    simp only [le_upd_pre]
    refine forall_ne (fun i => ?_)
    refine wand_ne.ne .rfl ?_
    refine UPred.bupd_ne.ne ?_
    refine or_ne.ne .rfl ?_
    refine or_ne.ne .rfl ?_
    refine exists_ne (fun m => ?_)
    refine sep_ne.ne .rfl ?_
    refine sep_ne.ne .rfl ?_
    refine Contractive.distLater_dist ?_
    cases n
    · exact distLater_zero
    · exact distLater_succ.mpr (distLater_succ.mp H)

#rocq_ignore le_upd.le_upd_def "`le_upd` is defined directly without `seal`/`unseal`."
#rocq_ignore le_upd.le_upd_aux "`le_upd` is defined directly without `seal`/`unseal`."
#rocq_ignore le_upd.le_upd_unseal "`le_upd` is defined directly without `seal`/`unseal`."

@[rocq_alias le_upd.le_upd]
def le_upd (P : IProp GF) : IProp GF := fixpoint (le_upd_pre P)

syntax:max "|==£> " term:40 : term

macro_rules
| `(iprop(|==£> $P)) => ``(le_upd iprop($P))

delab_rule le_upd
| `($_ $P) => do ``(iprop(|==£> $(← unpackIprop P)))

@[rocq_alias le_upd.le_upd_unfold]
theorem le_upd_unfold {P : IProp GF} :
  (|==£> P) ⊣⊢
  ∀ n, lc_supply n ==∗
    ▷^[n.succ] False ∨ (lc_supply n ∗ P) ∨ (∃ m, ⌜m < n⌝ ∗ lc_supply m ∗ ▷ |==£> P) :=
    (equiv_iff.mp (fixpoint_unfold ⟨le_upd_pre P, inferInstance⟩)).trans .rfl

@[rocq_alias le_upd.le_upd_ne]
instance : NonExpansive (le_upd (GF := GF)) where
  ne {n} := by
    apply WellFounded.induction Nat.lt_wfRel.wf n
    intro m IH P Q H
    refine ((equiv_iff.mpr le_upd_unfold).dist).trans ?_
    refine .trans ?_ ((equiv_iff.mpr le_upd_unfold).dist).symm
    refine forall_ne (fun i => ?_)
    refine wand_ne.ne .rfl ?_
    refine UPred.bupd_ne.ne ?_
    refine or_ne.ne .rfl ?_
    refine or_ne.ne (sep_ne.ne .rfl H) ?_
    refine exists_ne (fun m => ?_)
    refine sep_ne.ne .rfl ?_
    refine sep_ne.ne .rfl ?_
    refine Contractive.distLater_dist ?_
    exact (fun k Hk => IH k Hk (H.lt Hk))

@[rocq_alias le_upd.le_upd_unfold_no_le]
theorem le_upd_unfold_no_le [LcGS .hasNoLC GF] {P : IProp GF} : (|==£> P) ⊣⊢ |==> ◇ P := by
  apply le_upd_unfold.trans
  constructor
  · iintro H
    ihave Hs : lc_supply 0 $$ []
    · iapply (lc_supply_no_lc 0).mpr; itrivial
    imod H $$ %0 Hs with (HFalse | ⟨_, HP⟩ | ⟨%m, %Hlt, _⟩)
    · imodintro
      icases (laterN_later 0).mp $$ HFalse with HFalse
      icases laterN_0.mp $$ HFalse with HFalse
      simp only [BIBase.except0]
      ileft
      iexact HFalse
    · imodintro; iapply except0_intro $$ HP
    · exact absurd Hlt m.not_lt_zero
  · iintro H %n Hn
    icases (lc_supply_no_lc n).mp $$ Hn with %Hn
    subst Hn
    imod H
    simp only [BIBase.except0]
    icases H with (HFalse | HP)
    · imodintro; ileft
      iapply (laterN_later 0).mpr
      inext; iexact HFalse
    · imodintro; iright; ileft
      iframe HP
      iapply (lc_supply_no_lc 0).mpr; itrivial

@[rocq_alias le_upd.bupd_le_upd]
theorem bupd_le_upd {P : IProp GF} : (|==> P) ⊢ (|==£> P) := by
  iintro H
  iapply le_upd_unfold
  iintro %n Hsupp
  imod H; imodintro
  iright; ileft
  iframe

@[rocq_alias le_upd.le_upd_intro]
theorem le_upd_intro {P : IProp GF} : P ⊢ |==£> P := by
  iintro H
  iapply bupd_le_upd
  imodintro
  iexact H

@[rocq_alias le_upd.le_upd_bind]
theorem le_upd_bind {P Q : IProp GF} : ⊢ (P -∗ |==£> Q) -∗ (|==£> P) -∗ (|==£> Q) := by
  iapply BILoeb.loeb_weak
  iintro HLöb H G
  iapply le_upd_unfold
  iintro %n Hsupp
  imod le_upd_unfold $$ G Hsupp with (HFalse|⟨Hsupp, G⟩|⟨%m, %Hlt, Hsupp, G⟩)
  · imodintro; ileft; iexact HFalse
  · ihave G := H $$ G
    imod le_upd_unfold $$ G Hsupp with (HFalse|⟨Hsupp, G⟩|⟨%m, %Hlt, Hsupp, G⟩)
    · imodintro; ileft; iexact HFalse
    · imodintro
      iright; ileft
      iframe
    · imodintro
      iright; iright
      iexists m
      iframe
      itrivial
  · imodintro
    iright; iright
    iexists m
    iframe
    isplit
    · itrivial
    inext
    iapply HLöb $$ H G
  itrivial

@[rocq_alias le_upd.lc_le_upd_elim_later]
theorem le_upd_later_elim [LcGS .hasLC GF] {P : IProp GF} : ⊢ £ 1 -∗ (▷ |==£> P) -∗ |==£> P := by
  iintro Hcr H
  iapply le_upd_unfold
  iintro %n Hsupp
  ihave %H := lc_supply_bound $$ Hsupp Hcr
  cases n with
  | zero => exfalso; cases H
  | succ n =>
    rw [show n.succ = 1 + n by omega]
    imod lc_decrease_supply $$ Hsupp Hcr with Hsupp
    imodintro
    iright; iright
    iexists n
    iframe
    itrivial

@[rocq_alias le_upd.le_upd_mono]
theorem le_upd_mono {P Q : IProp GF} (Hent : P ⊢ Q) : (|==£> P) ⊢ (|==£> Q) := by
  iintro H
  iapply le_upd_bind $$ [] H
  iintro H
  iapply le_upd_intro
  exact Hent

@[rocq_alias le_upd.le_upd_trans]
theorem le_upd_trans {P : IProp GF} : (|==£> |==£> P) ⊢ |==£> P := by
  iintro H
  iapply le_upd_bind $$ [] H
  iintro $

@[rocq_alias le_upd.le_upd_frame_r]
theorem le_upd_frame_r {P R : IProp GF} : (|==£> P) ∗ R ⊢ |==£> (P ∗ R) := by
  iintro ⟨H, HR⟩
  iapply le_upd_bind $$ [HR] H
  iintro HP
  iapply le_upd_intro
  iframe

@[rocq_alias le_upd.le_upd_frame_l]
theorem le_upd_frame_l {P R : IProp GF} : R ∗ (|==£> P) ⊢ |==£> (R ∗ P) := by
  refine .trans ?_ (le_upd_mono sep_comm.mp)
  refine (.trans sep_comm.mp ?_)
  iapply le_upd_frame_r

@[rocq_alias le_upd.lc_le_upd_add_later]
theorem le_upd_later [LcGS .hasLC GF] {P : IProp GF} : ⊢ £ 1 -∗ ▷ P -∗ |==£> P := by
  iintro H1 H2
  iapply le_upd_later_elim $$ H1
  inext
  iapply le_upd_intro $$ H2

@[rocq_alias le_upd.except_0_le_upd]
theorem except_0_le_upd {P : IProp GF} : ◇ (|==£> P) ⊢ |==£> P := by
  simp only [BIBase.except0]
  iintro (HFalse | $)
  iapply le_upd_unfold
  iintro %n _
  imodintro
  ileft
  iapply (laterN_later n).mpr
  inext
  iexact HFalse

#rocq_ignore le_upd.bi_bupd_mixin_le_upd "Only a safety check, not used"

end Upd

section Internal

open ProofMode

variable {GF : BundledGFunctors} {hlc : HasLC} [LcGS hlc GF]

@[rocq_alias le_upd.elim_bupd_le_upd]
instance {P : IProp GF} : ElimModal True p false (bupd P) P (le_upd Q) (le_upd Q) where
  elim_modal := by
    cases p <;> (dsimp; intro _)
    · iintro ⟨H1, H2⟩
      iapply le_upd_bind $$ H2
      iapply bupd_le_upd $$ H1
    · iintro ⟨#H1, H2⟩
      iapply le_upd_bind $$ H2
      iapply bupd_le_upd $$ H1

@[rocq_alias le_upd.from_assumption_le_upd]
instance from_assumption_le_upd {p} {P Q : IProp GF} [h : FromAssumption p ioP P Q] :
    FromAssumption p ioP P (le_upd Q) where
  from_assumption := h.1.trans le_upd_intro

@[rocq_alias le_upd.from_pure_le_upd]
instance {P : IProp GF} [H : FromPure a P io φ] : FromPure a (le_upd P) io φ where
  from_pure := by
    cases a <;> dsimp
    · iintro H
      iapply le_upd_intro
      iapply H.from_pure $$ H
    · iintro H
      iapply le_upd_intro
      iapply H.from_pure $$ H

@[rocq_alias le_upd.is_except_0_le_upd]
instance {P : IProp GF} : IsExcept0 (le_upd P) where
  is_except0 := except_0_le_upd

@[rocq_alias le_upd.from_modal_le_upd]
instance {P : IProp GF} : FromModal True modality_id (le_upd P) (le_upd P) P where
  from_modal := by
    simp only [modality_id, id_eq, forall_const]
    iapply le_upd_intro

@[rocq_alias le_upd.elim_modal_le_upd]
instance {P : IProp GF} : ElimModal True p false (le_upd P) P (le_upd Q) (le_upd Q) where
  elim_modal := by
    intro _
    cases p <;> dsimp
    · iintro ⟨H1, H2⟩
      iapply le_upd_bind $$ H2 H1
    · iintro ⟨H1, H2⟩
      iapply le_upd_bind $$ H2 H1

@[rocq_alias le_upd.frame_le_upd]
instance {p} {P R Q : IProp GF} [hf : Frame p R P Q] : Frame p R (le_upd P) (le_upd Q) where
  frame := le_upd_frame_l.trans <| le_upd_mono hf.frame

end Internal

@[rocq_alias le_upd.lc_alloc]
theorem lc_alloc [H : LcGpreS GF] n : ⊢@{IProp GF} |==> ∃ _ : LcGS .hasLC GF, lc_supply n ∗ £ n := by
  imod (iOwn_alloc (E := H.lc_elem) ((● n) • (◯ n)) (auth_both_valid.mpr ⟨fun _ => .rfl, ⟨⟩⟩))
    with ⟨%γLC, HOwn⟩
  icases iOwn_op $$ HOwn with ⟨HAuth, HFrag⟩
  let LC : LcGS .hasLC GF := { lc_elem := H.lc_elem, lc_name := γLC }
  iexists LC
  imodintro
  simp only [lc_supply, lc]
  iframe

@[rocq_alias le_upd.lc_alloc_no_lc]
theorem lc_alloc_no_lc [H : LcGpreS GF] n :
    ⊢@{IProp GF} ∃ _ : LcGS .hasNoLC GF, lc_supply 0 ∗ £ n := by
  let LC : LcGS .hasNoLC GF := { lc_elem := H.lc_elem, lc_name := default }
  iexists LC
  simp only [lc_supply, lc]
  itrivial

@[rocq_alias le_upd.le_upd_finally]
def le_upd_finally [LcGS hlc GF] (P : IProp GF) : IProp GF :=
  iprop(∀ m, lc_supply m -∗ ▷^[m] ◇ ■ P)

#rocq_ignore le_upd.le_upd_finally_aux "Not needed"
#rocq_ignore le_upd.le_upd_finally_def "Not needed"
#rocq_ignore le_upd.le_upd_finally_unseal "Not needed"

syntax:max "|==£|> " term:40 : term

macro_rules
| `(iprop(|==£|> $P)) => ``(le_upd_finally iprop($P))

delab_rule le_upd_finally
| `($_ $P) => do ``(iprop(|==£|> $(← unpackIprop P)))

section le_upd_finally_rules
variable {hlc : HasLC} [LcGS hlc GF]

@[rocq_alias le_upd.le_upd_finally_ne]
instance le_upd_finally_ne : NonExpansive (le_upd_finally (GF := GF)) where
  ne _ _ _ H := by
    simp only [le_upd_finally]
    refine forall_ne (fun m => ?_)
    refine wand_ne.ne .rfl ?_
    refine laterN_ne m |>.ne ?_
    refine except0_ne.ne ?_
    exact instPlainly_ne.ne H

@[rocq_alias le_upd.le_upd_finally_mono]
theorem le_upd_finally_mono (P Q: IProp GF) : (P ⊢ Q) → (|==£|> P) ⊢ (|==£|> Q) := by
  intro Hent
  unfold le_upd_finally
  iintro HP %m Hlc
  ihave HP := HP $$ %m Hlc
  iapply laterN_mono $$ HP
  iintro HP
  iapply except0_mono $$ HP
  iintro HP
  iapply plainly_mono Hent $$ HP

@[rocq_alias le_upd.le_upd_finally_intro]
theorem le_upd_finally_intro (P : IProp GF) : ■ P ⊢ |==£|> P := by
  unfold le_upd_finally
  iintro HP %m _Hlc
  iapply laterN_intro
  iapply except0_intro $$ HP

@[rocq_alias le_upd.le_upd_le_upd_finally]
theorem le_upd_le_upd_finally (P : IProp GF) : (|==£> |==£|> P) ⊢ |==£|> P := by
  unfold le_upd_finally
  iintro HP %m Hlc
  iloeb as IH generalizing %m
  icases le_upd_unfold $$ HP with HP
  imod HP $$ Hlc with ⟨HFalse | ⟨Hlc, H⟩ | ⟨%m', %Hm, Hlc , H⟩⟩
  · simp only [BIBase.except0]
    iapply (laterN_later _).mp.trans (laterN_mono _ or_intro_l) $$ HFalse
  · iapply H; iframe
  conv =>
    rhs
    rw [show m = 1+ ((m - m' - 1) + m') by grind]
  iapply laterN_add; inext
  iapply laterN_add; inext
  iapply IH $$ H Hlc

@[rocq_alias le_upd.le_upd_finally_except_0]
theorem le_upd_finally_except0 (P : IProp GF) : (|==£|> ◇ P) ⊢ |==£|> P := by
  unfold le_upd_finally
  iintro HP %m Hlc
  iapply laterN_mono _ except0_idemp.mp
  iapply laterN_mono _ (except0_mono except0_plainly.mpr)
  iapply HP $$ Hlc

@[rocq_alias le_upd.le_upd_finally_add_lc]
theorem le_upd_finally_add_lc (P : IProp GF) : (£ 1 -∗ |==£|> P) ⊢ |==£|> ▷ ◇ P := by
  unfold le_upd_finally
  iintro H %m Hlc
  iapply laterN_mono _ except0_intro
  iapply laterN_mono _ later_plainly.mp
  iapply laterN_mono _ (later_mono except0_plainly.mp)
  iapply (laterN_later m).mp
  cases hlc with
  | hasLC =>
    rw [show m + 1 = 1 + m from Nat.add_comm m 1]
    imod lc_increase_supply 1 $$ Hlc with ⟨Hlc, Hl⟩
    iapply H $$ Hl Hlc
  | hasNoLC =>
    icases (lc_supply_no_lc m) $$ Hlc with %Hlc
    subst Hlc
    rw [Nat.zero_add]
    inext
    ihave Hone : £ 1 $$ []
    · iapply (lc_no_lc 1).mpr; itrivial
    ihave Hz : lc_supply 0 $$ []
    · iapply (lc_supply_no_lc 0).mpr; itrivial
    ispecialize H $$ Hone %0 Hz
    iapply laterN_0
    iassumption

@[rocq_alias le_upd.le_upd_finally_forall]
theorem le_upd_finally_forall (Φ : A → IProp GF) : (∀ x, |==£|> Φ x) ⊢ |==£|> ∀ x, Φ x := by
  unfold le_upd_finally
  iintro H %m Hlc %x
  iapply H $$ Hlc

@[rocq_alias le_upd.le_upd_keep]
theorem le_upd_keep (P Q : IProp GF) [TCOr (TCEq hlc .hasNoLC) (Timeless P)] :
    (|==£|> P) ∧ (P -∗ |==£> Q) ⊢ |==£> Q := by
  iintro H
  iapply le_upd_unfold
  iintro %n Hc
  ihave #⟨$| HP⟩ : iprop((▷^[n.succ] False) ∨ ■ P) $$ [H Hc]
  · icases H with ⟨H, -⟩
    unfold le_upd_finally
    cases ‹TCOr (TCEq hlc .hasNoLC) (Timeless P)› with
    | r =>
      iapply timeless_laterN
      ispecialize H $$ Hc
      icases (laterN_mono n except0_into_later) $$ H with H
      icases (laterN_later _).mpr $$ H with $
    | l =>
      cases ‹TCEq hlc .hasNoLC›
      icases (lc_supply_no_lc n).mp $$ Hc with %Hn
      subst n
      ispecialize H $$ Hc
      icases laterN_0.mp $$ H with H
      rw [← Nat.add_one, (laterN_later (n := 0)).to_eq, (laterN_0).to_eq]
      unfold BIBase.except0
      iapply H
  icases H with ⟨-, H⟩
  ispecialize H $$ HP
  iapply le_upd_unfold $$ H
  iframe

#rocq_ignore le_upd.le_upd_finally_proper "Subsumed by the NonExpansive instance `le_upd_finally_ne`"
#rocq_ignore le_upd.le_upd_finally_mono' "Subsumed by `le_upd_finally_mono`"
#rocq_ignore le_upd.le_upd_finally_flip_mono' "Subsumed by `le_upd_finally_mono`"

@[rocq_alias le_upd.le_upd_finally_later]
theorem le_upd_finally_later (P : IProp GF) : ▷ (|==£|> P) ⊢ |==£|> ▷ ◇ P := by
  unfold le_upd_finally
  iintro H %m Hlc
  iapply laterN_mono _ (except0_intro.trans <| except0_mono <| later_plainly.1)
  iapply laterN_mono _ (later_mono except0_plainly.1)
  iapply (laterN_later m).mp
  iapply (later_laterN m).mpr
  inext
  iapply H $$ Hlc

end le_upd_finally_rules

@[rocq_alias le_upd.le_upd_finally_soundness]
theorem le_upd_finally_soundness (hlc : HasLC) [LcGpreS GF] n (P : IProp GF) :
  (∀ [LcGS hlc GF], £ n ⊢ |==£|> P) → ⊢ P := by
  intro HP
  cases hlc with
  | hasLC =>
    apply laterN_soundness (n := n.succ)
    iintro _
    iapply (laterN_later _).mpr
    iapply (laterN_mono _ except0_into_later)
    iapply (laterN_mono _ (except0_mono plainly_elim))
    imod lc_alloc n with ⟨%LC, Hlc, Hl⟩
    have HP' : £ n ⊢ iprop(∀ m, lc_supply m -∗ ▷^[m] ◇ ■ P) := HP
    iapply HP' $$ Hl Hlc
  | hasNoLC =>
    apply laterN_soundness (n := 1)
    iintro _
    iapply (laterN_later 0).mpr
    iapply laterN_0.mpr
    iapply later_mono plainly_elim
    iapply except0_into_later
    icases lc_alloc_no_lc n with ⟨%LC, Hlc, Hl⟩
    unfold le_upd_finally at HP
    ihave G := HP $$ Hl %0 Hlc
    iapply laterN_0.mp $$ G

@[rocq_alias le_upd.lc_soundness]
theorem lc_soundness (hlc : HasLC) [LcGpreS GF] m (P : IProp GF) [Plain P]
    (H : ∀ {_ : LcGS hlc GF}, ⊢ £ m -∗ |==£> P) : ⊢ P := by
  apply le_upd_finally_soundness hlc m
  intro LC
  iintro Hcr
  iapply le_upd_le_upd_finally
  imod H $$ Hcr with HP
  imodintro
  iapply le_upd_finally_intro
  iapply plain_plainly_2 $$ HP

end Iris
