/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra
public import Iris.Algebra.Auth
public import Iris.Algebra.Numbers
public import Iris.ProofMode
public import Iris.BI.Algebra
public import Iris.Instances.IProp

@[expose] public section

/-! ## Later credits
TODO: missing instances for PM: frame_le_upd, frame_le_upd_if, combine_sep_lc_add, combine_sep_lc_S_l
-/

namespace Iris

open _root_.Std (Associative Commutative LeftIdentity LawfulLeftIdentity)
open Iris OFE COFE BI Auth CommMonoidLike

section LcGS

abbrev Credit := Nat

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

-- /-- Later credits inclusion typeclass (`GF` contains the necessary functors for later credits) -/
class LcGpreS (GF : BundledGFunctors) where
  lc_elem : ElemG GF (AuthURF (F := PNat) (constOF Credit))

attribute [reducible, instance] LcGpreS.lc_elem

class LcGS (GF : BundledGFunctors) extends LcGpreS GF where
  lc_name : GName

end LcGS

section Definitions

variable {GF : BundledGFunctors} [LC : LcGS GF]

def lc (i : Credit) : IProp GF :=
  iOwn (E := LC.lc_elem) LC.lc_name (◯ i)

notation:max "£ " i:40 => lc i

def lc_supply (i : Credit) : IProp GF :=
  iOwn (E := LC.lc_elem) LC.lc_name (● i)

end Definitions

section Operations

variable {GF : BundledGFunctors} [LC : LcGS GF]

theorem lc_split {n m} :
  £ (n + m) ⊣⊢@{IProp GF} £ n ∗ £ m := by
  refine .trans (.of_eq ?_) iOwn_op
  rfl

@[rocq_alias lc_zero]
theorem lc_zero : ⊢@{IProp GF} |==> £ 0 := iOwn_unit (ε := UCMRA.unit)

@[rocq_alias lc_supply_bound]
theorem lc_supply_bound {n m} : ⊢@{IProp GF} lc_supply m -∗ £ n -∗ ⌜n ≤ m⌝ := by
  iintro Hsupp Hcred
  icases iOwn_op (E := LC.lc_elem) $$ [Hsupp Hcred] with H
  · unfold lc lc_supply
    isplitl [Hsupp] <;> iassumption
  ihave H := iOwn_cmraValid (E := LC.lc_elem) $$ H
  ihave ⟨H1, H2⟩ := auth_both_validI (F := PNat) (PROP := IProp GF) m n $$ H
  ihave %H := internalCmraIncluded_discrete (PROP := IProp GF) (A := Credit) $$ H1
  ipure_intro
  obtain ⟨k, rfl⟩ := H
  exact Nat.le_add_right n k

@[rocq_alias lc_decrease_supply]
theorem lc_decrease_supply {n m} : ⊢@{IProp GF} lc_supply (n + m) -∗ £ n -∗ |==> lc_supply m := by
  iintro H1 H2
  imod iOwn_update_op (E := LC.lc_elem)
    (auth_update (leftCancelAdd_local_update ((Nat.add_assoc n m 0).trans (Nat.add_comm n m))))
    $$ [H1 H2] with H
  · unfold lc lc_supply
    isplitl [H1] <;> iassumption
  icases iOwn_op (E := LC.lc_elem) $$ H with ⟨H, _⟩
  imodintro
  unfold lc_supply; iexact H

@[rocq_alias lc_succ]
theorem lc_succ {n} : £ (.succ n) ⊣⊢@{IProp GF} £ 1 ∗ £ n := by
  rw [show .succ n = 1 + n by simp [Nat.succ_eq_add_one, Nat.add_comm]]
  exact lc_split

@[rocq_alias lc_weaken]
theorem lc_weaken {n} m : m ≤ n → ⊢@{IProp GF} £ n -∗ £ m := by
  intro h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  iintro H
  ihave ⟨H, _⟩ := lc_split (GF := GF) $$ H
  iexact H

@[rocq_alias lc_timeless]
instance {n} : Timeless (PROP := IProp GF) (£ n) := by
  unfold lc
  infer_instance

@[rocq_alias lc_0_persistent]
instance : Persistent (PROP := IProp GF) (£ 0) := by
  unfold lc
  apply instPersistentIPropIOwnOfCoreIdAp

end Operations

section ProofMode

open ProofMode

variable {GF : BundledGFunctors} [LcGS GF]

@[rocq_alias from_sep_lc_add]
instance (priority := default - 10) {n m} : FromSep (PROP := IProp GF) (£ (n + m)) (£ n) (£ m) where
  from_sep := lc_split.mpr

@[rocq_alias from_sep_lc_S]
instance (priority := default) {n} : FromSep (PROP := IProp GF) (£ (.succ n)) (£ 1) (£ n) where
  from_sep := lc_succ.mpr

@[rocq_alias into_sep_lc_add]
instance (priority := default - 10) {n m} : IntoSep (PROP := IProp GF) (£ (n + m)) (£ n) (£ m) where
  into_sep := lc_split.mp

@[rocq_alias into_sep_lc_S]
instance (priority := default) {n} : IntoSep (PROP := IProp GF) (£ (.succ n)) (£ 1) (£ n) where
  into_sep := lc_succ.mp

end ProofMode

section Upd

variable {GF : BundledGFunctors} [LcGS GF]

def le_upd_pre (le_upd : IProp GF → IProp GF) : IProp GF → IProp GF :=
  fun P => iprop(∀ n, lc_supply n ==∗ (lc_supply n ∗ P) ∨ (∃ m, ⌜m < n⌝ ∗ lc_supply m ∗ ▷ le_upd P))

@[rocq_alias le_upd_pre_contractive]
instance : Contractive (le_upd_pre (GF := GF)) where
  distLater_dist {n x y} H P := by
    simp only [le_upd_pre]
    refine forall_ne (fun i => ?_)
    refine wand_ne.ne .rfl ?_
    refine UPred.bupd_ne.ne ?_
    refine or_ne.ne .rfl ?_
    refine exists_ne (fun m => ?_)
    refine sep_ne.ne .rfl ?_
    refine sep_ne.ne .rfl ?_
    refine Contractive.distLater_dist ?_
    cases n
    · exact distLater_zero
    · exact distLater_succ.mpr (distLater_succ.mp H P)

def le_upd : IProp GF → IProp GF := fixpoint le_upd_pre

syntax:max "|==£> " term:40 : term

macro_rules
| `(iprop(|==£> $P)) => ``(le_upd iprop($P))

delab_rule le_upd
| `($_ $P) => do ``(iprop(|==£> $(← unpackIprop P)))

@[rocq_alias le_upd_unfold]
theorem le_upd_unfold {P : IProp GF} :
  (|==£> P) ⊣⊢
  ∀ n, lc_supply n ==∗ (lc_supply n ∗ P) ∨ (∃ m, ⌜m < n⌝ ∗ lc_supply m ∗ ▷ le_upd P) :=
    (equiv_iff.mp ((fixpoint_unfold ⟨le_upd_pre (GF := GF), inferInstance⟩) P)).trans .rfl

@[rocq_alias le_upd_ne]
instance : NonExpansive (le_upd (GF := GF)) where
  ne {n} := by
    apply WellFounded.induction Nat.lt_wfRel.wf n
    intro m IH P Q H
    refine ((equiv_iff.mpr le_upd_unfold).dist).trans ?_
    refine .trans ?_ ((equiv_iff.mpr le_upd_unfold).dist).symm
    refine forall_ne (fun i => ?_)
    refine wand_ne.ne .rfl ?_
    refine UPred.bupd_ne.ne ?_
    refine or_ne.ne (sep_ne.ne .rfl H) ?_
    refine exists_ne (fun m => ?_)
    refine sep_ne.ne .rfl ?_
    refine sep_ne.ne .rfl ?_
    refine Contractive.distLater_dist ?_
    exact (fun k Hk => IH k Hk (H.lt Hk))

@[rocq_alias bupd_le_upd]
theorem bupd_le_upd {P : IProp GF} : (|==> P) ⊢ (|==£> P) := by
  iintro H
  iapply le_upd_unfold
  iintro %n Hsupp
  imod H; imodintro
  ileft
  isplitl [Hsupp] <;> iassumption

@[rocq_alias le_upd_intro]
theorem le_upd_intro {P : IProp GF} : P ⊢ |==£> P := by
  iintro H
  iapply bupd_le_upd
  imodintro
  iexact H

@[rocq_alias le_upd_bind]
theorem le_upd_bind {P Q : IProp GF} :
  ⊢ (P -∗ |==£> Q) -∗ (|==£> P) -∗ (|==£> Q) := by
  iapply BILoeb.loeb_weak
  iintro HLöb H G
  iapply le_upd_unfold
  iintro %n Hsupp
  imod le_upd_unfold (GF := GF) $$ G Hsupp with (⟨Hsupp, G⟩|⟨%m, %Hlt, Hsupp, G⟩)
  · ihave G := H $$ G
    imod le_upd_unfold (GF := GF) $$ G Hsupp with (⟨Hsupp, G⟩|⟨%m, %Hlt, Hsupp, G⟩)
    · imodintro
      ileft
      isplitl [Hsupp] <;> iassumption
    · imodintro
      iright
      iexists m
      isplit
      · ipure_intro; assumption
      isplitl [Hsupp] <;> iassumption
  · imodintro
    iright
    iexists m
    isplit
    · ipure_intro; assumption
    isplitl [Hsupp]; iassumption
    inext
    iapply HLöb $$ H G
  ipure_intro; simp

@[rocq_alias le_upd_later_elim]
theorem le_upd_later_elim {P : IProp GF} :
  ⊢ £ 1 -∗ (▷ |==£> P) -∗ |==£> P := by
  iintro Hcr H
  iapply le_upd_unfold
  iintro %n Hsupp
  ihave %H := lc_supply_bound (GF := GF) $$ Hsupp Hcr
  cases n with
  | zero => exfalso; cases H
  | succ n =>
    rw [show n.succ = 1 + n by omega]
    imod lc_decrease_supply (GF := GF) $$ Hsupp Hcr with Hsupp
    imodintro
    iright
    iexists n
    isplit
    · ipure_intro; simp
    isplitr [H] <;> iassumption

@[rocq_alias le_upd_mono]
theorem le_upd_mono {P Q : IProp GF} : (P ⊢ Q) → (|==£> P) ⊢ (|==£> Q) := by
  intro Hent
  iintro H
  iapply le_upd_bind $$ [] H
  iintro H
  iapply le_upd_intro
  apply Hent

@[rocq_alias le_upd_trans]
theorem le_upd_trans {P : IProp GF} : (|==£> |==£> P) ⊢ |==£> P := by
  iintro H
  iapply le_upd_bind $$ [] H
  iintro H; iexact H

@[rocq_alias le_upd_frame_r]
theorem le_upd_frame_r {P R : IProp GF} : (|==£> P) ∗ R ⊢ |==£> (P ∗ R) := by
  iintro ⟨H, HR⟩
  iapply le_upd_bind $$ [HR] H
  iintro HP
  iapply le_upd_intro
  isplitl [HP] <;> iassumption

@[rocq_alias le_upd_frame_l]
theorem le_upd_frame_l {P R : IProp GF} : R ∗ (|==£> P) ⊢ |==£> (R ∗ P) := by
  refine .trans (.trans sep_comm.mp ?_) (le_upd_mono sep_comm.mp)
  iapply le_upd_frame_r

@[rocq_alias le_upd_later]
theorem le_upd_later {P : IProp GF} : ⊢ £ 1 -∗ ▷ P -∗ |==£> P := by
  iintro H1 H2
  iapply le_upd_later_elim $$ H1
  inext
  iapply le_upd_intro $$ H2

@[rocq_alias except_0_le_upd]
theorem except_0_le_upd {P : IProp GF} : ◇ (|==£> P) ⊢ |==£> (◇ P) := by
  simp only [BIBase.except0]
  iintro (H|H)
  · iapply le_upd_intro
    ileft
    iexact H
  · iapply le_upd_mono $$ H
    iintro H
    iright
    iexact H

end Upd

section Internal

open ProofMode

variable {GF : BundledGFunctors} [LcGS GF]

@[rocq_alias le_upd_elim]
theorem le_upd_elim n (P : IProp GF) :
  ⊢@{IProp GF} lc_supply n -∗ (|==£> P)
  -∗ n.repeat (fun P => iprop(|==> ▷ P)) iprop(|==> ◇ (∃ m, ⌜m ≤ n⌝ ∗ lc_supply m ∗ P)) := by
  apply WellFounded.induction Nat.lt_wfRel.wf n
  intro n IH
  iintro Ha Hupd
  icases le_upd_unfold (GF := GF) (P := P) $$ Hupd with Hupd
  ihave Hupd := Hupd $$ %n Ha
  cases n with
  | zero =>
    simp only [Nat.le_zero_eq, Nat.repeat]
    imod Hupd with (⟨Ha, HP⟩|⟨%m, %Hlt, _⟩)
    · imodintro; imodintro
      iexists 0
      isplit
      · ipure_intro; rfl
      isplitl [Ha] <;> iassumption
    · exfalso; exact Nat.not_lt_zero m Hlt
  | succ n =>
    simp only [Nat.repeat]
    imod Hupd with (⟨Hc, HP⟩|Hupd)
    · imodintro; inext
      iapply iter_modal_intro $$ [Hc HP]
      · intro Q; iintro H; imodintro; inext; iexact H
      imodintro; imodintro
      iexists n.succ
      isplit
      · ipure_intro; exact Nat.le_refl _
      isplitl [Hc] <;> iassumption
    · imodintro
      icases Hupd with ⟨%m, Hrest⟩
      icases Hrest with ⟨%Hstep, Hrest2⟩
      icases Hrest2 with ⟨Hown, LaterHupd⟩
      obtain ⟨k, Heq⟩ := Nat.exists_eq_add_of_lt Hstep
      rw [show n = m + k by exact Nat.add_right_cancel Heq, Nat.repeat_add]
      inext
      ihave IH := (IH m (by simp [WellFoundedRelation.rel]; omega)) $$ Hown LaterHupd
      iapply iter_modal_mono $$ [] IH
      · iintro %P %Q H HP; imod HP; imodintro; inext; iapply H $$ HP
      iintro IH
      iapply iter_modal_intro $$ [IH]
      · iintro %Q H; imodintro; inext; iexact H
      imod IH; imodintro
      imod IH with ⟨%m', %Hlt, H1, H2⟩; imodintro
      iexists m'
      isplit
      · ipure_intro
        grind
      isplitl [H1] <;> iassumption

@[rocq_alias le_upd_elim_complete]
theorem le_upd_elim_complete n (P : IProp GF) :
  ⊢ lc_supply n -∗ (|==£> P)
  -∗ n.succ.repeat (fun Q => iprop(|==> ▷ Q)) P := by
  iintro Hlc Hupd
  ihave Hit := le_upd_elim (GF := GF) n P $$ Hlc Hupd
  rw [show Nat.succ n = n + 1 by omega, Nat.repeat_add]
  iapply iter_modal_mono $$ [] Hit
  · iintro %P %Q Hent HP
    imod HP; imodintro; inext
    iapply Hent $$ HP
  simp only [Nat.repeat]
  iintro Hupd
  imod Hupd; imodintro
  imod Hupd; inext
  icases Hupd with ⟨%m, ⟨_, ⟨_, HP⟩⟩⟩
  iexact HP

@[rocq_alias elim_bupd_le_upd]
instance {P : IProp GF} : ElimModal True p false (bupd P) P (le_upd Q) (le_upd Q) where
  elim_modal := by
    cases p <;> (dsimp; intro _)
    · iintro ⟨H1, H2⟩
      iapply le_upd_bind $$ H2
      iapply bupd_le_upd $$ H1
    · iintro ⟨#H1, H2⟩
      iapply le_upd_bind $$ H2
      iapply bupd_le_upd $$ H1

@[rocq_alias from_assumption_le_upd]
instance from_assumption_le_upd {p} {P Q : IProp GF} [h : FromAssumption p ioP P Q] : FromAssumption p ioP P (le_upd Q) where
  from_assumption := h.1.trans le_upd_intro

@[rocq_alias from_pure_le_upd]
instance {P : IProp GF} [H : FromPure a P φ] : FromPure a (le_upd P) φ where
  from_pure := by
    cases a <;> dsimp
    · iintro H
      iapply le_upd_intro
      iapply H.from_pure $$ H
    · iintro H
      iapply le_upd_intro
      iapply H.from_pure $$ H

@[rocq_alias is_except_0_le_upd]
instance {P : IProp GF} [H : IsExcept0 P] : IsExcept0 (le_upd P) where
  is_except0 := by
    iintro G
    icases except_0_le_upd (GF := GF) $$ G with G
    iapply le_upd_mono $$ G
    iapply H.is_except0

@[rocq_alias from_modal_le_upd]
instance {P : IProp GF} : FromModal True modality_id (le_upd P) (le_upd P) P where
  from_modal := by
    simp only [modality_id, id_eq, forall_const]
    iapply le_upd_intro

@[rocq_alias elim_modal_le_upd]
instance {P : IProp GF} : ElimModal True p false (le_upd P) P (le_upd Q) (le_upd Q) where
  elim_modal := by
    intro _
    cases p <;> dsimp
    · iintro ⟨H1, H2⟩
      iapply le_upd_bind $$ H2 H1
    · iintro ⟨H1, H2⟩
      iapply le_upd_bind $$ H2 H1

end Internal

@[rocq_alias lc_alloc]
theorem lc_alloc [H : LcGpreS GF] n :
  ⊢@{IProp GF} |==> ∃ _ : LcGS GF, lc_supply n ∗ £ n := by
  imod (iOwn_alloc (E := H.lc_elem) ((● n) • (◯ n))
    (auth_both_valid.mpr ⟨fun _ => .rfl, ⟨⟩⟩)) with ⟨%γLC, HOwn⟩
  icases iOwn_op (E := H.lc_elem) $$ HOwn with ⟨HAuth, HFrag⟩
  let LC : LcGS GF := {
    lc_elem := H.lc_elem,
    lc_name := γLC
  }
  iexists LC
  imodintro
  simp only [lc_supply, lc]
  isplitl [HAuth] <;> iassumption

@[rocq_alias lc_soundness]
theorem lc_soundness [LcGpreS GF] m (P : IProp GF) [Plain P] :
  (∀ {_: LcGS GF}, ⊢ £ m -∗ |==£> P) → ⊢ P := by
  intro H
  apply laterN_soundness (n := .succ m)
  refine .trans ?_ bupd_elim
  iintro emp; iclear emp
  imod lc_alloc (GF := GF) m with ⟨%γ, H1, H2⟩
  ihave G := H $$ H2
  ihave G := le_upd_elim_complete (GF := GF) $$ H1 G
  simp only [Nat.succ_eq_add_one, Nat.repeat]
  imod G; imodintro
  -- TODO: inext is too eager to remove all laters from the goal
  iapply later_laterN; inext
  clear H
  istop
  induction m with
  | zero =>
    simp only [Nat.zero_eq, Nat.repeat]
    exact .rfl
  | succ m IH =>
    simp only [Nat.succ_eq_add_one, Nat.repeat]
    iintro H
    iapply later_laterN
    iapply bupd_elim
    imod H; imodintro; inext
    refine .trans .rfl IH

section If

open ProofMode

variable {GF : BundledGFunctors} [LcGS GF]

def le_upd_if (b : Bool) : IProp GF → IProp GF :=
  if b then le_upd else bupd

@[rocq_alias le_upd_if_ne]
instance le_upd_if_ne : NonExpansive (le_upd_if b (GF := GF)) := by
  cases b <;> (simp only [le_upd_if, Bool.false_eq_true, ↓reduceIte]; infer_instance)

@[rocq_alias le_upd_if_mono']
theorem le_upd_if_mono {P Q : IProp GF} : (P ⊢ Q) → (le_upd_if b P) ⊢ (le_upd_if b Q) := by
  cases b <;> (simp only [le_upd_if, Bool.false_eq_true, ↓reduceIte])
  · intro H; iintro G
    imod G; imodintro; iapply H $$ G
  · apply le_upd_mono

@[rocq_alias le_upd_if_intro]
theorem le_upd_if_intro {b} {P : IProp GF} : P ⊢ le_upd_if b P := by
  cases b <;> (simp only [le_upd_if, Bool.false_eq_true, ↓reduceIte])
  · iintro H; imodintro; iassumption
  · apply le_upd_intro

@[rocq_alias le_upd_if_bind]
theorem le_upd_if_bind {b} {P Q : IProp GF} :
  ⊢ (P -∗ le_upd_if b Q) -∗ (le_upd_if b P) -∗ (le_upd_if b Q) := by
  cases b <;> (simp only [le_upd_if, Bool.false_eq_true, ↓reduceIte])
  · iintro H G
    imod G
    iapply H $$ G
  · apply le_upd_bind

@[rocq_alias le_upd_if_trans]
theorem le_upd_if_trans {b} {P : IProp GF} : (le_upd_if b (le_upd_if b P)) ⊢ le_upd_if b P := by
  cases b <;> (simp only [le_upd_if, Bool.false_eq_true, ↓reduceIte])
  · apply bupd_idem.mp
  · apply le_upd_trans

@[rocq_alias le_upd_if_frame_r]
theorem le_upd_if_frame_r {b} {P R : IProp GF} : (le_upd_if b P) ∗ R ⊢ le_upd_if b iprop(P ∗ R) := by
  cases b <;> (simp only [le_upd_if, Bool.false_eq_true, ↓reduceIte])
  · apply bupd_frame_r
  · apply le_upd_frame_r

@[rocq_alias bupd_le_upd_if]
theorem bupd_le_upd_if {b} {P : IProp GF} : (|==> P) ⊢ (le_upd_if b P) := by
  cases b <;> (simp only [le_upd_if, Bool.false_eq_true, ↓reduceIte])
  · exact .rfl
  · apply bupd_le_upd

@[rocq_alias le_upd_if_frame_l]
theorem le_upd_if_frame_l {b} {R Q : IProp GF} : (R ∗ le_upd_if b Q) ⊢ le_upd_if b iprop(R ∗ Q) := by
  cases b <;> (simp only [le_upd_if, Bool.false_eq_true, ↓reduceIte])
  · apply bupd_frame_l
  · apply le_upd_frame_l

@[rocq_alias except_0_le_upd_if]
theorem except_0_le_upd_if {b} {P : IProp GF} : ◇ (le_upd_if b P) ⊢ le_upd_if b iprop(◇ P) := by
  cases b <;> (simp only [le_upd_if, Bool.false_eq_true, ↓reduceIte])
  · apply bupd_except0
  · apply except_0_le_upd

@[rocq_alias elim_bupd_le_upd_if]
instance {b} {p} {P Q : IProp GF} : ElimModal True p false (bupd P) P (le_upd_if b Q) (le_upd_if b Q) := by
  cases b <;> (simp only [le_upd_if, Bool.false_eq_true, ↓reduceIte]; infer_instance)

@[rocq_alias from_pure_le_upd_if]
instance {b} {a} {P : IProp GF} φ [FromPure a P φ] : FromPure a (le_upd_if b P) φ := by
  cases b <;> (simp only [le_upd_if, Bool.false_eq_true, ↓reduceIte]; infer_instance)

@[rocq_alias is_except_0_le_upd_if]
instance {b} {P : IProp GF} [IsExcept0 P] : IsExcept0 (le_upd_if b P) := by
  cases b <;> (simp only [le_upd_if, Bool.false_eq_true, ↓reduceIte]; infer_instance)

@[rocq_alias from_modal_le_upd_if]
instance {b} {P : IProp GF} : FromModal True modality_id (le_upd_if b P) (le_upd_if b P) P := by
  cases b <;> (simp only [le_upd_if, Bool.false_eq_true, ↓reduceIte]; infer_instance)

@[rocq_alias elim_modal_le_upd_if]
instance {b} {p} {P Q : IProp GF} :
  ElimModal True p false (le_upd_if b P) P (le_upd_if b Q) (le_upd_if b Q) := by
  cases b <;> (simp only [le_upd_if, Bool.false_eq_true, ↓reduceIte]; infer_instance)

@[rocq_alias from_assumption_le_upd_if]
instance from_assumption_le_upd_if {p} {P Q : IProp GF} [h : FromAssumption p ioP P Q] : FromAssumption p ioP P (le_upd_if b Q) where
  from_assumption := h.1.trans le_upd_if_intro

end If

end Iris
