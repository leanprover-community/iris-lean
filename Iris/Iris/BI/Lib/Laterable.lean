/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/

module

public import Iris.BI
public import Iris.ProofMode
public import Iris.Std.Classes

@[expose] public section

namespace Iris

section Laterable
open BI OFE ProofMode

/-- Require that the proposition `P` is laterable. -/
@[rocq_alias Laterable]
class Laterable [BI PROP] (P : PROP) where
  laterable : P ⊢ ∃ Q, ▷ Q ∗ □ (▷ Q -∗ ◇ P)

@[rocq_alias IntoLaterable]
class IntoLaterable [BI PROP] (P : PROP) (Q : outParam PROP) where
  into_laterable : P ⊢ Q
  into_laterable_result_laterable : Laterable Q

@[rocq_alias later_laterable]
instance later_laterable [BI PROP] (P : PROP) : Laterable iprop(▷ P) where
  laterable := by
    iintro HP {$HP} !> HP !> //

@[rocq_alias timeless_laterable]
instance timeless_laterable [BI PROP] (P : PROP) [Timeless P] : Laterable P where
  laterable := by
    iintro HP {$HP}
    isplitr
    · itrivial
    · iintro !> >HP !> //

@[rocq_alias intuitionistic_laterable]
theorem intuitionistic_laterable [BI PROP] (P : PROP)
    [instTimeless : Timeless (emp : PROP)]
    [instAffine : Affine P] [instPers : Persistent P] :
    Laterable P where
  laterable := by
    iintro #HP
    iexists emp
    isplitl
    · itrivial
    · iintro !> >- //

@[rocq_alias persistent_laterable]
instance persistent_laterable [BI PROP] [BIAffine PROP] (P : PROP) [Persistent P] :
    Laterable P := by
  apply intuitionistic_laterable <;> infer_instance

@[rocq_alias sep_laterable]
instance sep_laterable [BI PROP] (P Q : PROP) [instP : Laterable P] [instQ : Laterable Q] :
    Laterable iprop(P ∗ Q) where
  laterable := by
    iintro ⟨HP, HQ⟩
    icases instP.laterable $$ HP with ⟨%P', HP', #HP⟩
    icases instQ.laterable $$ HQ with ⟨%Q', HQ', #HQ⟩
    iexists iprop(P' ∗ Q')
    isplitl
    · iframe
    · iintro !> ⟨HP', HQ'⟩
      isplitl [HP']
      · iapply HP; iassumption
      · iapply HQ; iassumption

@[rocq_alias exist_laterable]
instance exist_laterable [BI PROP] {A} (Φ : A → PROP)
    [inst : ∀ x, Laterable (Φ x)] : Laterable (∃ x, Φ x) where
  laterable := by
    iintro ⟨%x, H⟩
    icases (inst x).laterable $$ H with ⟨%Q, HQ, #HΦ⟩
    iintro {$HQ} !> HQ
    iexists x
    iapply HΦ
    iassumption

@[rocq_alias laterable_proper]
theorem laterable_congr [BI PROP] {P Q : PROP} (h : P ⊣⊢ Q) (inst : Laterable P) :
    Laterable Q where
  laterable := by
    refine h.mpr.trans ?_
    refine inst.laterable.trans ?_
    apply exists_mono
    intro Q
    apply sep_mono_right
    apply intuitionistically_mono
    apply wand_mono_right
    apply except0_mono h.mp

@[rocq_alias big_sep_sepL_laterable]
theorem big_sep_sepL_laterable [BI PROP] (Q : PROP) (Ps : List PROP)
    (instQ : Laterable Q) (instPs : ∀ P ∈ (Ps : List PROP), Laterable P) :
    Laterable iprop(Q ∗ [∗] Ps) := by
  induction Ps generalizing Q instQ with
  | nil =>
    dsimp [bigSep, Std.bigOp]
    apply laterable_congr sep_emp.symm instQ
  | cons P Ps ih =>
    dsimp [bigSep, Std.bigOp]
    letI : Laterable P := instPs P (.head _)
    apply laterable_congr <| sep_assoc.trans (sep_congr_right bigOp_sep_cons.symm)
    exact ih _ (sep_laterable Q P) (fun R hR => instPs R (.tail _ hR))

@[rocq_alias big_sepL_laterable]
instance big_sepL_laterable [BI PROP] (Ps : List PROP)
    [instEmp : Laterable (emp : PROP)] [instPs : Std.List.Forall Laterable Ps] :
    Laterable iprop([∗] Ps) := by
  apply laterable_congr emp_sep
  apply big_sep_sepL_laterable emp Ps instEmp
  apply Iris.Std.listForall.mp instPs

@[rocq_alias make_laterable]
def make_laterable [BI PROP] (Q : PROP) : PROP :=
  iprop(∃ P, ▷ P ∗ □ (▷ P -∗ ◇ Q))

@[rocq_alias make_laterable_ne]
instance make_laterable_ne [BI PROP] : NonExpansive <| make_laterable (PROP := PROP) where
  ne := by
    intro n P Q HPQ
    unfold make_laterable
    apply exists_ne
    intro R
    apply sep_ne.ne; rfl
    apply intuitionistically_ne.ne
    apply wand_ne.ne; rfl
    apply except0_ne.ne; assumption

@[rw_mono_rule, rocq_alias make_laterable_mono]
theorem make_laterable_mono [BI PROP] {Q1 Q2 : PROP} (h : Q1 ⊢ Q2) :
    make_laterable Q1 ⊢ make_laterable Q2 := by unfold make_laterable; rw' [h]

#rocq_ignore make_laterable_mono' "No Proper type class in Lean"
#rocq_ignore make_laterable_proper "No Proper type class in Lean"

@[rocq_alias make_laterable_except_0]
theorem make_laterable_except_0 [BI PROP] {Q : PROP} :
    make_laterable iprop(◇ Q) ⊢ make_laterable Q := by
  unfold make_laterable
  iintro ⟨%P, HP, #HPQ⟩
  iintro {$HP} !> HP
  imod HPQ $$ HP with HQ
  iassumption

@[rocq_alias make_laterable_sep]
theorem make_laterable_sep [BI PROP] {Q1 Q2 : PROP} :
    make_laterable Q1 ∗ make_laterable Q2 ⊢ make_laterable iprop(Q1 ∗ Q2) := by
  iintro ⟨HQ1, HQ2⟩
  unfold make_laterable
  icases HQ1 with ⟨%P1, HP1, #HQ1⟩
  icases HQ2 with ⟨%P2, HP2, #HQ2⟩
  icombine HP1 HP2 as HP
  iintro {$HP} !> ⟨HP1, HP2⟩
  icases HQ1 $$ HP1 with >$
  icases HQ2 $$ HP2 with >$
  itrivial

@[rocq_alias make_laterable_wand]
theorem make_laterable_wand [BI PROP] {Q1 Q2 : PROP} :
    make_laterable iprop(Q1 -∗ Q2) ⊢ make_laterable Q1 -∗ make_laterable Q2 := by
  iintro HQ HQ1
  icases make_laterable_sep $$ [$HQ $HQ1 //] with HQ
  iapply make_laterable_mono (Q1 := iprop((Q1 -∗ Q2) ∗ Q1))
  · exact wand_elim_left
  · iassumption

@[rocq_alias make_laterable_intuitionistic_wand]
theorem make_laterable_intuitionistic_wand [BI PROP] {Q1 Q2 : PROP} :
    □ (Q1 -∗ Q2) ⊢ make_laterable Q1 -∗ make_laterable Q2 := by
  iintro #HQ HQ1
  unfold make_laterable
  icases HQ1 with ⟨%P, HP, #HQ1⟩
  iintro {$HP} !> HP
  icases HQ1 $$ HP with >HQ1'
  iclear HQ1
  iapply HQ $$ HQ1'

@[rocq_alias make_laterable_laterable]
instance make_laterable_laterable [BI PROP] {Q : PROP} : Laterable (make_laterable Q) where
  laterable := by
    unfold make_laterable
    iintro ⟨%P, HP, #HQ⟩
    iintro {$HP} !> HP !>
    iexists P; iframe
    imodintro; iassumption

@[rocq_alias make_laterable_elim]
theorem make_laterable_elim [BI PROP] {Q : PROP} : make_laterable Q ⊢ ◇ Q := by
  unfold make_laterable
  iintro ⟨%P, HP, #HQ⟩
  iapply HQ $$ HP

@[rocq_alias make_laterable_intro]
theorem make_laterable_intro [BI PROP] {P Q : PROP} [inst : Laterable P] :
    □ (P -∗ Q) -∗ P -∗ make_laterable Q := by
  unfold make_laterable
  iintro #HPQ HP
  icases inst.laterable $$ HP with ⟨%P', HP', #HPi⟩
  iintro {$HP'} !> HP'
  icases HPi $$ HP' with >HP
  imodintro
  iapply HPQ $$ HP

@[rocq_alias make_laterable_intro']
theorem make_laterable_intro' [BI PROP] {Q : PROP} [inst : Laterable Q] :
    Q ⊢ make_laterable Q := by
  iapply make_laterable_intro
  iintro !> $

@[rocq_alias make_laterable_idemp]
theorem make_laterable_idemp [BI PROP] {Q : PROP} :
    make_laterable (make_laterable Q) ⊣⊢ make_laterable Q := by
  constructor
  · exact make_laterable_mono make_laterable_elim |>.trans make_laterable_except_0
  · exact make_laterable_intro'

@[rocq_alias laterable_alt]
theorem laterable_alt [BI PROP] {Q : PROP} : Laterable Q ↔ (Q ⊢ make_laterable Q) := by
  constructor
  · intros inst
    apply make_laterable_intro'
  · intro h
    constructor
    unfold make_laterable at h
    assumption

@[rocq_alias into_laterable_laterable]
instance intoLaterable_laterable [BI PROP] {P : PROP} [Laterable P] : IntoLaterable P P where
  into_laterable := .rfl
  into_laterable_result_laterable := by trivial

@[rocq_alias into_laterable_fallback]
instance (priority := default - 100) into_laterable_fallback [BI PROP] {P : PROP} :
    IntoLaterable P iprop(▷ P) where
  into_laterable := later_intro
  into_laterable_result_laterable := later_laterable P

@[rocq_alias modality_make_laterable, rocq_alias modality_make_laterable_mixin]
def modality_make_laterable [BI PROP] [Timeless (emp : PROP)] : Modality PROP PROP where
  M := make_laterable
  action
  | true => .id
  | false => .transform <| fun P Q => Nonempty <| IntoLaterable P Q
  spec
  | true => fun P =>
    make_laterable_intro' (inst := intuitionistic_laterable iprop(□ P))
  | false => by
    intro P Q ⟨inst⟩
    exact inst.into_laterable.trans <| make_laterable_intro' (inst := inst.into_laterable_result_laterable)
  emp := make_laterable_intro'
  mono := make_laterable_mono
  sep := make_laterable_sep

@[rocq_alias from_modal_make_laterable]
instance fromModal_make_laterable [BI PROP] [Timeless (emp : PROP)] (P : PROP) :
    FromModal True modality_make_laterable (make_laterable P) (make_laterable P) P where
  from_modal := by
    iintro %_ HP
    dsimp [modality_make_laterable, make_laterable]
    iassumption

end Laterable
