/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.ProofMode
/-! ## Algebra wrappers for BI
This file provides introduction rules (BI entailments) for (some) CMRA operations and properties.
-/

@[expose] public section

-- TODO: Need sbi_unfold to make these proofs less horrific
namespace Iris

section prod

open BI Std BIBase.BiEntails

@[rocq_alias prod_validI]
theorem prod_validI [Sbi PROP] [CMRA A] [CMRA B] (x : A × B) :
    internalCmraValid x ⊣⊢@{PROP} internalCmraValid x.1 ∧ internalCmraValid x.2 := by
  simp only [internalCmraValid]
  refine .trans ?_ siPure_and
  refine siPure_mono_bi ?_
  cases x with | mk x1 x2 =>
  exact ⟨fun _ => id, fun _ => id⟩

@[rocq_alias prod_includedI]
theorem prod_includedI [Sbi PROP] [CMRA A] [CMRA B] (x y : A × B) :
    internalCmraIncluded x y ⊣⊢@{PROP} internalCmraIncluded x.1 y.1 ∧ internalCmraIncluded x.2 y.2 := by
  simp only [internalCmraIncluded,  internalEq]
  refine .trans (siPure_mono_bi ?_) siPure_and
  refine siPure_exist.symm.trans ?_
  refine .trans ?_ (and_congr_left siPure_exist)
  refine .trans ?_ (and_congr_right siPure_exist)
  refine .trans (siPure_mono_bi ?_) siPure_and
  cases x with | mk x1 x2 =>
  cases y with | mk y1 y2 =>
  simp only [CMRA.op, Prod.op]
  constructor
  · rintro n ⟨P, ⟨w, rfl⟩, hP⟩
    exact ⟨⟨_, ⟨w.fst, rfl⟩, hP.1⟩, ⟨_, ⟨w.snd, rfl⟩, hP.2⟩⟩
  · rintro n ⟨⟨P1, ⟨w1, rfl⟩, hP1⟩, ⟨P2, ⟨w2, rfl⟩, hP2⟩⟩
    exact ⟨_, ⟨(w1, w2), rfl⟩, hP1, hP2⟩

end prod

section option

open BI Std BIBase.BiEntails

@[rocq_alias option_validI]
theorem option_validI [Sbi PROP] [CMRA A] {mx : Option A} :
  internalCmraValid mx ⊣⊢@{PROP} mx.elim iprop(True) internalCmraValid :=
  match mx with
  | none => ⟨true_intro, internalCmraValid_intro trivial⟩
  | some _ => .rfl

@[rocq_alias option_includedI]
theorem option_includedI [Sbi PROP] [CMRA A] {mx my : Option A} :
  internalCmraIncluded mx my ⊣⊢@{PROP}
    match mx, my with
      | some x, some y => iprop((internalCmraIncluded x y) ∨ (internalEq x y))
      | none, _ => iprop(True)
      | some _, none => iprop(False) := by
  rcases mx with _ | x <;> rcases my with _ | y
  · exact ⟨true_intro, internalCmraIncluded_intro (Option.inc_iff.mpr (.inl rfl))⟩
  · exact ⟨true_intro, internalCmraIncluded_intro (Option.inc_iff.mpr (.inl rfl))⟩
  · refine ⟨?_, false_elim⟩
    refine .trans (siPure_mono ?_) siPure_pure.mp
    rintro n ⟨_, ⟨c, rfl⟩, hc⟩
    rcases c with _ | c <;> exact hc
  · simp only [internalCmraIncluded, internalEq]
    refine .trans (siPure_mono_bi ⟨fun n h => ?_, fun n h => ?_⟩) siPure_or
    · obtain ⟨_, ⟨c, rfl⟩, hc⟩ := h
      rcases Option.some_incN_some_iff.mp ⟨c, hc⟩ with heqv | ⟨c, hc⟩
      · exact .inr heqv
      · exact .inl ⟨_, ⟨c, rfl⟩, hc⟩
    · have ⟨c, hc⟩ : (some x : Option A) ≼{n} some y := by
        rcases h with ⟨_, ⟨c, rfl⟩, hc⟩ | heqv
        · exact Option.some_incN_some_iff.mpr (.inr ⟨c, hc⟩)
        · exact Option.some_incN_some_iff.mpr (.inl heqv)
      exact ⟨_, ⟨c, rfl⟩, hc⟩

@[rocq_alias option_included_totalI]
theorem option_included_totalI [Sbi PROP] [CMRA A] [CMRA.IsTotal A] {mx my : Option A} :
  internalCmraIncluded mx my ⊣⊢@{PROP}
    match mx, my with
      | some x, some y => internalCmraIncluded x y
      | none, _ => iprop(True)
      | some _, none => iprop(False) := by
  rcases mx with _ | x <;> rcases my with _ | y
  · exact ⟨true_intro, internalCmraIncluded_intro (Option.inc_iff.mpr (.inl rfl))⟩
  · exact ⟨true_intro, internalCmraIncluded_intro (Option.inc_iff.mpr (.inl rfl))⟩
  · refine ⟨?_, false_elim⟩
    refine .trans (siPure_mono ?_) siPure_pure.mp
    rintro n ⟨_, ⟨c, rfl⟩, hc⟩
    rcases c with _ | c <;> exact hc
  · refine siPure_mono_bi ⟨fun n h => ?_, fun n h => ?_⟩
    · obtain ⟨_, ⟨c, rfl⟩, hc⟩ := h
      obtain ⟨c, hc⟩ := Option.some_incN_some_iff_is_total.mp ⟨c, hc⟩
      exact ⟨_, ⟨c, rfl⟩, hc⟩
    · obtain ⟨_, ⟨c, rfl⟩, hc⟩ := h
      obtain ⟨c, hc⟩ := Option.some_incN_some_iff_is_total.mpr ⟨c, hc⟩
      exact ⟨_, ⟨c, rfl⟩, hc⟩

@[rocq_alias Some_included_totalI]
theorem Some_included_totalI [Sbi PROP] [CMRA A] [CMRA.IsTotal A] {x y : A} :
  internalCmraIncluded (some x) (some y) ⊣⊢@{PROP} internalCmraIncluded x y :=
  option_included_totalI

end option

section heap_view

open HeapView BI Std PartialMap LawfulPartialMap BIBase.BiEntails

variable {F K V : Type _} {H : Type _ → Type _}
variable [LawfulPartialMap H K] [CMRA V]

@[rocq_alias gmap_view_both_dfrac_validI]
theorem auth_op_frag_validI [Sbi PROP] (dp : DFrac) (m : H V) k dq v :
  internalCmraValid (Auth dp m • Frag k dq v) ⊣⊢@{PROP}
    ∃ v' dq', ⌜✓ dp⌝ ∧ ⌜get? m k = .some v'⌝ ∧ internalCmraValid (dq', v') ∧
      internalCmraIncluded (Option.some (dq, v)) (Option.some (dq', v')) := by
  suffices H :
    (<si_pure> SiProp.cmraValid (HeapView.Auth dp m • Frag (H := H) k dq v) ⊣⊢@{PROP}
    (<si_pure> ∃ x x_1, ⌜✓ dp⌝ ∧ ⌜get? m k = some x⌝ ∧ SiProp.cmraValid (x_1, x) ∧
        ∃ c, internalEq (some (x_1, x)) (some (dq, v) • c))) by
    refine H.trans ?_
    refine siPure_exist.trans ?_
    refine exists_congr fun v' => ?_
    refine siPure_exist.trans ?_
    refine exists_congr fun dq' => ?_
    refine siPure_and.trans ?_
    refine and_congr siPure_pure ?_
    refine siPure_and.trans  ?_
    exact and_congr siPure_pure siPure_and
  constructor
  · refine siPure_mono fun n => ?_
    simp only [SiProp.cmraValid, auth_op_frag_validN_iff]
    intro ⟨v', dq', Hdp, Hlookup, Hvalid, ⟨z, Hincl⟩⟩
    apply SiProp.instBI.sExists_intro
    · exists v'
    apply SiProp.instBI.sExists_intro
    · exists dq'
    refine ⟨Hdp, Hlookup, Hvalid, ?_⟩
    apply SiProp.instBI.sExists_intro
    · exists z
    exact Hincl
  · refine siPure_mono ?_
    iintro ⟨%v', ⟨%dq', %Hdp', %Hlookup, H⟩⟩
    refine siPure_and.mpr.trans ?_
    refine siPure_mono (and_exists_left.mp.trans (exists_elim (fun c => ?_)))
    intro n ⟨h1, h2⟩
    apply auth_op_frag_validN_iff.mpr
    exists v', dq'
    simp only at h1
    simp [Hdp', Hlookup, h1]
    exists c

@[rocq_alias gmap_view_both_validI]
theorem auth_op_frag_one_validI [Sbi PROP] (dp : DFrac) (m : H V) k v :
  internalCmraValid (Auth dp m • Frag k (.own One.one) v) ⊣⊢@{PROP}
    ⌜✓ dp⌝ ∧ internalCmraValid v ∧ internalEq (get? m k) (.some v) := by
  refine .trans ?_ (and_congr_right siPure_and)
  refine .trans ?_ (and_congr_left siPure_pure)
  refine .trans ?_ siPure_and
  constructor
  · refine siPure_mono fun n => ?_
    simp only [SiProp.cmraValid, auth_op_frag_one_validN_iff]
    exact id
  · refine siPure_mono fun n => ?_
    simp only [SiProp.cmraValid, auth_op_frag_one_validN_iff]
    exact id

@[rocq_alias gmap_view_both_validI_total]
theorem auth_op_frag_validI_total [Sbi PROP] [CMRA.IsTotal V] (dp : DFrac) (m : H V) k dq v :
  internalCmraValid (Auth dp m • Frag k dq v) ⊢@{PROP}
    ∃ v', ⌜✓ dp⌝ ∧ ⌜✓ dq⌝ ∧ ⌜get? m k = .some v'⌝ ∧
      internalCmraValid v' ∧ internalCmraIncluded v v' := by
  refine trans ?_
    (siPure_exist.trans <|
      exists_congr <|
      fun v => siPure_and.trans <|
      and_congr siPure_pure <|
      siPure_and.trans <|
      and_congr siPure_pure <|
      siPure_and.trans <|
      and_congr siPure_pure siPure_and).mp
  refine siPure_mono fun n hvalid => ?_
  have ⟨v', Hdp, Hdq, Hlookup, Hv', ⟨z, Hincl⟩⟩ := auth_op_frag_validN_total_iff hvalid
  apply SiProp.instBI.sExists_intro
  · exists v'
  refine ⟨Hdp, Hdq, Hlookup, Hv', ?_⟩
  apply SiProp.instBI.sExists_intro
  · exists z
  exact Hincl

@[rocq_alias gmap_view_frag_op_validI]
theorem frag_op_frag_validI [Sbi PROP] k dq1 dq2 v1 v2 :
  internalCmraValid (Frag (H := H) (V := V) k dq1 v1 • Frag k dq2 v2) ⊣⊢@{PROP}
    ⌜✓ (dq1 • dq2)⌝ ∧ internalCmraValid (v1 • v2) := by
  refine .trans ?_ (and_congr_left siPure_pure)
  refine .trans ?_ siPure_and
  constructor
  · refine siPure_mono fun n => ?_
    simp only [SiProp.cmraValid, frag_op_validN_iff]
    exact id
  · refine siPure_mono fun n => ?_
    simp only [SiProp.cmraValid, frag_op_validN_iff]
    exact id

end heap_view

section agree_inclusion

open Iris BI Agree OFE

variable [Sbi PROP] [OFE A]

@[rocq_alias agree_equivI]
theorem agree_equivI {a b : A} : internalEq (toAgree a) (toAgree b) ⊣⊢@{PROP} internalEq a b := by
  refine ⟨siPure_mono fun _ => Agree.toAgree_injN, ?_⟩
  refine siPure_mono fun n => ?_
  apply NonExpansive.ne

@[rocq_alias agree_op_invI]
theorem agree_op_invI {x y : Agree A} : internalCmraValid (x • y) ⊢@{PROP} internalEq x y :=
  siPure_mono (fun _ => op_invN)

@[rocq_alias to_agree_validI]
theorem toAgree_validI (a : A) :
    ⊢@{PROP} internalCmraValid (toAgree a) := by
  refine internalCmraValid_intro fun n => ?_
  simp

@[rocq_alias to_agree_op_validI]
theorem toAgree_op_validI (a b : A) :
    internalCmraValid (toAgree a • toAgree b) ⊣⊢@{PROP} internalEq a b :=
  ⟨siPure_mono fun _ => toAgree_op_validN_iff_dist.mp,
   siPure_mono fun _ => toAgree_op_validN_iff_dist.mpr⟩

@[rocq_alias to_agree_uninjI]
theorem toAgree_uninjI (x : Agree A) :
    internalCmraValid x ⊢@{PROP} ∃ a, internalEq (toAgree a) x := by
  refine .trans (siPure_mono fun n hvalid => ?_) siPure_exist.mp
  have ⟨a, heq⟩ := toAgree_uninjN hvalid
  apply SiProp.instBI.sExists_intro
  · exists a
  exact heq


-- TODO: Needs cleanup with better internalEq machinery

@[rocq_alias agree_op_equiv_to_agreeI]
theorem agree_op_equiv_toAgreeI (x y : Agree A) (a : A) :
    internalEq (x • y) (toAgree a) ⊢@{PROP} internalEq x y ∧ internalEq y (toAgree a) := by
  have H1 : internalEq (x • y) (toAgree a) ⊢@{PROP} internalEq x y := by
    refine absorbingly_internalEq (x • y) (toAgree a) |>.mpr.trans ?_
    refine (absorbingly_mono ?_).trans absorbing
    refine internalEq.rewrite' internalCmraValid internalEq.symm ?_ |>.trans agree_op_invI
    refine emp_sep.2.trans ?_
    refine (sep_mono_left (toAgree_validI a)) |>.trans ?_
    exact sep_elim_left
  have H2 : internalEq (x • y) (toAgree a) ⊢@{PROP} internalEq x (toAgree a) := by
    letI : NonExpansive (x • ·) := CMRA.op_ne
    have H21 : internalEq (x • y) (toAgree a) ⊢@{PROP} internalEq (x • x) (toAgree a) := by
      exact (and_intro (H1.trans (internalEq.of_internalEquiv_ne (x • ·))) .rfl).trans internalEq.trans
    have H22 : internalEq (x • y) (toAgree a) ⊢@{PROP} internalEq (x • x) x := by
      exact emp_sep.2.trans (sep_mono_left (internalEq.of_equiv Agree.idemp)) |>.trans sep_elim_left
    refine (and_intro (H22.trans internalEq.symm) H21).trans internalEq.trans
  apply and_intro H1
  exact (and_intro (H1.trans internalEq.symm) H2).trans internalEq.trans

@[rocq_alias agree_includedI]
theorem agree_includedI (x y : Agree A) :
    internalCmraIncluded x y ⊣⊢@{PROP} internalEq y (x • y) := by
  constructor
  · refine siPure_mono (exists_elim (fun c => ?_))
    exact (fun n Heq => (includedN.mp ⟨c, Heq⟩).trans op_commN)
  · refine siPure_mono (exists_intro_trans y ?_)
    exact entails_preorder.refl

@[rocq_alias to_agree_includedI]
theorem toAgree_includedI (a b : A) :
    internalCmraIncluded (toAgree a) (toAgree b) ⊣⊢@{PROP} internalEq a b := by
  constructor
  · refine siPure_mono (exists_elim (fun c => ?_))
    exact (fun n Heq => toAgree_includedN.mp ⟨c, Heq⟩)
  · refine siPure_mono ?_
    show SiProp.internalEq a b ⊢ (∃ c, SiProp.internalEq (toAgree b) (toAgree a • c))
    refine exists_intro_trans (toAgree a) ?_
    refine internalEq_entails.mpr fun n heq => ?_
    exact (NonExpansive.ne heq.symm).trans (idemp.symm n)

end agree_inclusion

section auth
open Iris BI Auth

variable [Sbi PROP] [UCMRA A]

@[rocq_alias auth_auth_dfrac_validI]
theorem auth_dfrac_validI (dq : DFrac) (a : A) :
    internalCmraValid (●{dq} a : Auth A) ⊣⊢@{PROP} ⌜✓ dq⌝ ∧ internalCmraValid a := by
  refine .trans ?_ (and_congr_left siPure_pure)
  refine .trans ?_ siPure_and
  refine ⟨siPure_mono fun n => ?_, siPure_mono fun n => ?_⟩
  all_goals simp only [SiProp.cmraValid, auth_dfrac_validN]; exact id

@[rocq_alias auth_auth_validI]
theorem auth_validI (a : A) : internalCmraValid (● a : Auth A) ⊣⊢@{PROP} internalCmraValid a := by
  refine ⟨siPure_mono fun n => ?_, siPure_mono fun n => ?_⟩
  all_goals simpa only [SiProp.cmraValid, auth_validN] using id

@[rocq_alias auth_auth_dfrac_op_validI]
theorem auth_dfrac_op_validI (dq1 dq2 : DFrac) (a1 a2 : A) :
    internalCmraValid ((●{dq1} a1) • (●{dq2} a2)) ⊣⊢@{PROP}
      ⌜✓ (dq1 • dq2)⌝ ∧ internalEq a1 a2 ∧ internalCmraValid a1 := by
  refine .trans ?_ (and_congr_left siPure_pure)
  refine .trans ?_ (siPure_and.trans (and_congr_right siPure_and))
  refine ⟨siPure_mono fun n => ?_, siPure_mono fun n => ?_⟩
  all_goals simp only [SiProp.cmraValid, auth_dfrac_op_validN]; exact id

@[rocq_alias auth_frag_validI]
theorem frag_validI (a : A) :
    internalCmraValid (◯ a : Auth A) ⊣⊢@{PROP} internalCmraValid a := by
  refine ⟨siPure_mono fun n => ?_, siPure_mono fun n => ?_⟩
  all_goals simpa only [SiProp.cmraValid, frag_validN] using id

@[rocq_alias auth_both_dfrac_validI]
theorem both_dfrac_validI (dq : DFrac) (a b : A) :
    internalCmraValid ((●{dq} a) • ◯ b) ⊣⊢@{PROP}
    ⌜✓ dq⌝ ∧ internalCmraIncluded b a ∧ internalCmraValid a := by
  refine .trans ?_ <| siPure_and.trans (and_congr siPure_pure siPure_and)
  refine siPure_mono_bi ?_
  refine .trans ?_ ((and_congr_right BI.and_exists_right).trans BI.and_exists_left).symm
  refine ⟨siPure_mono fun n => ?_, ?_⟩
  · simp only [both_dfrac_validN]
    intro ⟨hv, ⟨c, hi⟩, hvn⟩
    apply SiProp.instBI.sExists_intro
    · exists c
    · exact ⟨hv, ⟨hi, hvn⟩⟩
  · refine siPure_mono ?_
    refine exists_elim fun c n ⟨hv, ⟨hi, hvn⟩⟩ => ?_
    exact both_dfrac_validN.mpr ⟨hv, (by exists c), hvn⟩

@[rocq_alias auth_both_validI]
theorem auth_both_validI (a b : A) :
    internalCmraValid ((● a : Auth A) • ◯ b) ⊣⊢@{PROP}
      internalCmraIncluded b a ∧ internalCmraValid a := by
  refine .trans ?_ siPure_and
  refine siPure_mono_bi ?_
  refine .trans ?_ BI.and_exists_right.symm
  simp only [SiProp.cmraValid, both_dfrac_validN]
  refine ⟨fun n ⟨_, ⟨⟨c, hi⟩, hvn⟩⟩ => ?_, ?_⟩
  · apply SiProp.instBI.sExists_intro
    · exists c
    exact ⟨hi, hvn⟩
  · exact exists_elim fun c n ⟨hi, hvn⟩ => ⟨DFrac.valid_own_one, ⟨⟨c, hi⟩, hvn⟩⟩

end auth
end Iris
