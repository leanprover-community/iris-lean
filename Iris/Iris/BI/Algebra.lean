/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.BI.BI
public import Iris.BI.Cmra
public import Iris.Algebra.Lib.DFracAgree
public import Iris.Algebra.Lib.ExclAuth
public import Iris.Algebra.View
public import Iris.Algebra.Csum
public import Iris.Algebra.Excl
public import Iris.Algebra.Functions
public import Iris.Algebra.List
public import Iris.Algebra.Heap

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
    ✓ x ⊣⊢@{PROP} ✓ x.1 ∧ ✓ x.2 := by
  simp only [internalCmraValid]
  refine .trans ?_ siPure_and
  refine siPure_mono_bi ?_
  cases x with | mk x1 x2 =>
  exact ⟨fun _ => id, fun _ => id⟩

@[rocq_alias prod_includedI]
theorem prod_includedI [Sbi PROP] [CMRA A] [CMRA B] (x y : A × B) :
    x ≼ y ⊣⊢@{PROP} x.1 ≼ y.1 ∧ x.2 ≼ y.2 := by
  simp only [internalCmraIncluded, internalEq]
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
  ✓ mx ⊣⊢@{PROP} mx.elim iprop(True) internalCmraValid :=
  match mx with
  | none => ⟨true_intro, internalCmraValid_intro trivial⟩
  | some _ => .rfl

@[rocq_alias option_includedI]
theorem option_includedI [Sbi PROP] [CMRA A] {mx my : Option A} :
  mx ≼ my ⊣⊢@{PROP}
    match mx, my with
      | some x, some y => iprop((x ≼ y) ∨ (x ≡ y))
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
  mx ≼ my ⊣⊢@{PROP}
    match mx, my with
      | some x, some y => iprop(x ≼ y)
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
    some x ≼ some y ⊣⊢@{PROP} x ≼ y :=
  option_included_totalI

end option

section heap_view

open HeapView BI Std PartialMap LawfulPartialMap BIBase.BiEntails

variable {F K V : Type _} {H : Type _ → Type _}
variable [LawfulPartialMap H K] [CMRA V]

@[rocq_alias gmap_view_both_dfrac_validI]
theorem auth_op_frag_validI [Sbi PROP] (dp : DFrac) (m : H V) k dq v :
  ✓ (Auth dp m • Frag k dq v) ⊣⊢@{PROP}
    ∃ v' dq', ⌜✓ dp⌝ ∧ ⌜get? m k = .some v'⌝ ∧ ✓ (dq', v') ∧
      some (dq, v) ≼ some (dq', v') := by
  suffices H :
    (<si_pure> SiProp.cmraValid (HeapView.Auth dp m • Frag k dq v) ⊣⊢@{PROP}
    (<si_pure> ∃ x x_1, ⌜✓ dp⌝ ∧ ⌜get? m k = some x⌝ ∧ SiProp.cmraValid (x_1, x) ∧
        ∃ c, some (x_1, x) ≡ some (dq, v) • c)) by
    simp only [internalCmraValid, internalCmraIncluded, H.to_eq, siPure_exist.to_eq,
      siPure_and.to_eq, siPure_pure.to_eq, BIBase.BiEntails.rfl]
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
    refine exists_elim fun v' => exists_elim fun dq' => ?_
    refine pure_elim_left fun Hdp' => ?_
    refine pure_elim_left fun Hlookup => ?_
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
  ✓ (Auth dp m • Frag k (.own One.one) v) ⊣⊢@{PROP}
    ⌜✓ dp⌝ ∧ ✓ v ∧ get? m k ≡ .some v := by
  simp only [internalCmraValid, internalEq, ←siPure_and.to_eq]
  rw [←siPure_pure.to_eq, ←siPure_and.to_eq]
  constructor
  · refine siPure_mono fun n => ?_
    simp only [SiProp.cmraValid, auth_op_frag_one_validN_iff]
    exact id
  · refine siPure_mono fun n => ?_
    simp only [SiProp.cmraValid, auth_op_frag_one_validN_iff]
    exact id

@[rocq_alias gmap_view_both_validI_total]
theorem auth_op_frag_validI_total [Sbi PROP] [CMRA.IsTotal V] (dp : DFrac) (m : H V) k dq v :
  ✓ (Auth dp m • Frag k dq v) ⊢@{PROP}
    ∃ v', ⌜✓ dp⌝ ∧ ⌜✓ dq⌝ ∧ ⌜get? m k = .some v'⌝ ∧
      ✓ v' ∧ v ≼ v' := by
  suffices H : (<si_pure> SiProp.cmraValid (HeapView.Auth dp m • Frag k dq v) ⊢@{PROP}
      <si_pure> (∃ v', ⌜✓ dp⌝ ∧ ⌜✓ dq⌝ ∧ ⌜get? m k = some v'⌝ ∧ SiProp.cmraValid v' ∧
        ∃ c, v' ≡ v • c)) by
    simp only [internalCmraValid, internalCmraIncluded, siPure_exist.to_eq, siPure_and.to_eq,
      siPure_pure.to_eq] at H ⊢
    exact H
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
  ✓ (Frag (H := H) (V := V) k dq1 v1 • Frag k dq2 v2) ⊣⊢@{PROP}
    ⌜✓ (dq1 • dq2)⌝ ∧ ✓ (v1 • v2) := by
  simp only [←(and_congr_left siPure_pure).to_eq, internalCmraValid, ←siPure_and.to_eq]
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
theorem agree_equivI {a b : A} : toAgree a ≡ toAgree b ⊣⊢@{PROP} a ≡ b := by
  refine ⟨siPure_mono fun _ => Agree.toAgree_injN, ?_⟩
  refine siPure_mono fun n => ?_
  apply NonExpansive.ne

@[rocq_alias agree_op_invI]
theorem agree_op_invI {x y : Agree A} : ✓ (x • y) ⊢@{PROP} x ≡ y :=
  siPure_mono (fun _ => op_invN)

@[rocq_alias to_agree_validI]
theorem toAgree_validI (a : A) :
    ⊢@{PROP} ✓ (toAgree a) := by
  refine internalCmraValid_intro fun n => ?_
  simp

@[rocq_alias to_agree_op_validI]
theorem toAgree_op_validI (a b : A) :
    ✓ (toAgree a • toAgree b) ⊣⊢@{PROP} a ≡ b :=
  ⟨siPure_mono fun _ => toAgree_op_validN_iff_dist.mp,
   siPure_mono fun _ => toAgree_op_validN_iff_dist.mpr⟩

@[rocq_alias to_agree_uninjI]
theorem toAgree_uninjI (x : Agree A) :
    ✓ x ⊢@{PROP} ∃ a, toAgree a ≡ x := by
  refine .trans (siPure_mono fun n hvalid => ?_) siPure_exist.mp
  have ⟨a, heq⟩ := toAgree_uninjN hvalid
  apply SiProp.instBI.sExists_intro
  · exists a
  exact heq


-- TODO: Needs cleanup with better internalEq machinery

@[rocq_alias agree_op_equiv_to_agreeI]
theorem agree_op_equiv_toAgreeI (x y : Agree A) (a : A) :
    x • y ≡ toAgree a ⊢@{PROP} x ≡ y ∧ y ≡ toAgree a := by
  have H1 : x • y ≡ toAgree a ⊢@{PROP} x ≡ y := by
    refine absorbingly_internalEq (x • y) (toAgree a) |>.mpr.trans ?_
    refine (absorbingly_mono ?_).trans absorbing
    refine internalEq.rewrite' internalCmraValid internalEq.symm ?_ |>.trans agree_op_invI
    refine emp_sep.2.trans ?_
    refine (sep_mono_left (toAgree_validI a)) |>.trans ?_
    exact sep_elim_left
  have H2 : x • y ≡ toAgree a ⊢@{PROP} x ≡ toAgree a := by
    letI : NonExpansive (x • ·) := CMRA.op_ne
    have H21 : x • y ≡ toAgree a ⊢@{PROP} x • x ≡ toAgree a := by
      exact (and_intro (H1.trans (internalEq.of_internalEquiv_ne (x • ·))) .rfl).trans internalEq.trans
    have H22 : x • y ≡ toAgree a ⊢@{PROP} x • x ≡ x := calc
      _ ⊢ emp ∗ x • y ≡ toAgree a       := emp_sep.mpr
      _ ⊢ x • x ≡ x ∗ x • y ≡ toAgree a := sep_mono_left <| internalEq.of_equiv Agree.idemp
      _ ⊢ x • x ≡ x                     := sep_elim_left
    refine (and_intro (H22.trans internalEq.symm) H21).trans internalEq.trans
  apply and_intro H1
  exact (and_intro (H1.trans internalEq.symm) H2).trans internalEq.trans

@[rocq_alias agree_includedI]
theorem agree_includedI (x y : Agree A) :
    x ≼ y ⊣⊢@{PROP} y ≡ x • y := by
  constructor
  · refine siPure_mono (exists_elim (fun c => ?_))
    exact (fun n Heq => (includedN.mp ⟨c, Heq⟩).trans op_commN)
  · refine siPure_mono (exists_intro_trans y ?_)
    rfl

@[rocq_alias to_agree_includedI]
theorem toAgree_includedI (a b : A) :
    toAgree a ≼ toAgree b ⊣⊢@{PROP} a ≡ b := by
  constructor
  · refine siPure_mono (exists_elim (fun c => ?_))
    exact (fun n Heq => toAgree_includedN.mp ⟨c, Heq⟩)
  · refine siPure_mono ?_
    show SiProp.internalEq a b ⊢ (∃ c, SiProp.internalEq (toAgree b) (toAgree a • c))
    refine exists_intro_trans (toAgree a) ?_
    refine internalEq_entails.mpr fun n heq => ?_
    exact (NonExpansive.ne heq.symm).trans (Dist.of_eq idemp.symm)

end agree_inclusion

section auth
open Iris BI Auth

variable [Sbi PROP] [UCMRA A]

@[rocq_alias auth_auth_dfrac_validI]
theorem auth_dfrac_validI (dq : DFrac) (a : A) :
    ✓ (●{dq} a : Auth A) ⊣⊢@{PROP} ⌜✓ dq⌝ ∧ ✓ a := by
  simp only [←(and_congr_left siPure_pure).to_eq, internalCmraValid, ←siPure_and.to_eq]
  refine ⟨siPure_mono fun n => ?_, siPure_mono fun n => ?_⟩
  all_goals simp only [SiProp.cmraValid, auth_dfrac_validN]; exact id

@[rocq_alias auth_auth_validI]
theorem auth_validI (a : A) : ✓ (● a : Auth A) ⊣⊢@{PROP} ✓ a := by
  refine ⟨siPure_mono fun n => ?_, siPure_mono fun n => ?_⟩
  all_goals simpa only [SiProp.cmraValid, auth_validN] using id

@[rocq_alias auth_auth_dfrac_op_validI]
theorem auth_dfrac_op_validI (dq1 dq2 : DFrac) (a1 a2 : A) :
    ✓ ((●{dq1} a1) • (●{dq2} a2)) ⊣⊢@{PROP}
      ⌜✓ (dq1 • dq2)⌝ ∧ a1 ≡ a2 ∧ ✓ a1 := by
  simp only [←(and_congr_left siPure_pure).to_eq, internalEq, internalCmraValid
    , ←(siPure_and.trans (and_congr_right siPure_and)).to_eq]
  refine ⟨siPure_mono fun n => ?_, siPure_mono fun n => ?_⟩
  all_goals simp only [SiProp.cmraValid, auth_dfrac_op_validN]; exact id

@[rocq_alias auth_frag_validI]
theorem frag_validI (a : A) :
    ✓ (◯ a : Auth A) ⊣⊢@{PROP} ✓ a := by
  refine ⟨siPure_mono fun n => ?_, siPure_mono fun n => ?_⟩
  all_goals simpa only [SiProp.cmraValid, frag_validN] using id

@[rocq_alias auth_both_dfrac_validI]
theorem both_dfrac_validI (dq : DFrac) (a b : A) :
    ✓ ((●{dq} a) • ◯ b) ⊣⊢@{PROP}
    ⌜✓ dq⌝ ∧ b ≼ a ∧ ✓ a := by
  simp only [internalCmraValid, internalCmraIncluded, ←(and_congr siPure_pure siPure_and).to_eq]
  simp only [←siPure_and.to_eq, BI.and_exists_right.to_eq, BI.and_exists_left.to_eq]
  refine siPure_mono_bi ?_
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
    ✓ ((● a : Auth A) • ◯ b) ⊣⊢@{PROP}
      b ≼ a ∧ ✓ a := by
  simp only [internalCmraIncluded, internalCmraValid, ←siPure_and.to_eq, BI.and_exists_right.to_eq]
  refine siPure_mono_bi ?_
  simp only [SiProp.cmraValid, both_dfrac_validN]
  refine ⟨fun n ⟨_, ⟨⟨c, hi⟩, hvn⟩⟩ => ?_, ?_⟩
  · apply SiProp.instBI.sExists_intro
    · exists c
    exact ⟨hi, hvn⟩
  · exact exists_elim fun c n ⟨hi, hvn⟩ => ⟨DFrac.valid_own_one, ⟨⟨c, hi⟩, hvn⟩⟩

end auth

section dfrac_agree
variable [Sbi PROP] {A : Type _} [OFE A]

open BI

@[rocq_alias dfrac_agree_validI]
theorem dfrac_agree_validI (dq : DFrac) (x : A) :
    internalCmraValid (DFracAgree.mk dq x) ⊣⊢@{PROP} ⌜✓ dq⌝ := by
  refine (prod_validI (DFracAgree.mk dq x)).trans ⟨?_, ?_⟩
  · exact and_elim_l.trans internalCmraValid_discrete.mp
  · exact and_intro internalCmraValid_discrete.mpr
      (sep_elim_emp_valid_left (toAgree_validI x) sep_elim_left)

@[rocq_alias dfrac_agree_validI_2]
theorem dfrac_agree_validI_2 (dq1 dq2 : DFrac) (x y : A) :
    internalCmraValid (DFracAgree.mk dq1 x • DFracAgree.mk dq2 y) ⊣⊢@{PROP}
      ⌜✓ (dq1 • dq2)⌝ ∧ internalEq x y :=
  (prod_validI _).trans (and_congr internalCmraValid_discrete (toAgree_op_validI x y))

end dfrac_agree

section generic
open BI CMRA OFE
variable [Sbi PROP]

@[rocq_alias ucmra_unit_validI]
theorem ucmra_unit_validI [UCMRA A] : ⊢@{PROP} ✓ (UCMRA.unit : A) :=
  internalCmraValid_intro unit_valid

@[rocq_alias cmra_validI_op_r]
theorem cmra_validI_op_r [CMRA A] (x y : A) : ✓ (x • y) ⊢@{PROP} ✓ y :=
  siPure_mono fun _ => validN_op_right

@[rocq_alias cmra_validI_op_l]
theorem cmra_validI_op_l [CMRA A] (x y : A) : ✓ (x • y) ⊢@{PROP} ✓ x :=
  siPure_mono fun _ => validN_op_l

@[rocq_alias cmra_morphism_validI]
theorem cmra_morphism_validI [CMRA A] [CMRA B] (f : A -C> B) (x : A) :
    ✓ x ⊢@{PROP} ✓ (f x) :=
  siPure_mono fun _ => f.validN

@[rocq_alias f_homom_includedI]
theorem f_homom_includedI [CMRA A] [CMRA B] (x y : A) (f : A → B) [NonExpansive f]
    (Hf : ∀ c n, f x • f c ≡{n}≡ f (x • c)) :
    x ≼ y ⊢@{PROP} f x ≼ f y :=
  siPure_mono <| BI.exists_elim fun c => BI.exists_intro_trans (f c) <|
    internalEq_entails.mpr fun n heq => (NonExpansive.ne heq).trans (Hf c n).symm

@[rocq_alias id_freeI_r]
theorem id_freeI_r [CMRA A] (x y : A) [IdFree x] :
    ⊢@{PROP} ✓ x -∗ (x • y) ≡ x -∗ False := by
  have H : iprop((x • y) ≡ x ∗ ✓ x) ⊢@{PROP} False := by
    refine siPure_and_sep.mpr.trans ?_
    refine .trans (siPure_mono fun n h => ?_) siPure_pure.mp
    exact id_freeN_r h.2 h.1
  exact wand_intro_left (wand_intro_left ((sep_mono_right sep_emp.mp).trans H))

@[rocq_alias id_freeI_l]
theorem id_freeI_l [CMRA A] (x y : A) [IdFree x] :
    ⊢@{PROP} ✓ x -∗ (y • x) ≡ x -∗ False := by
  have H : iprop((y • x) ≡ x ∗ ✓ x) ⊢@{PROP} False := by
    refine siPure_and_sep.mpr.trans ?_
    refine .trans (siPure_mono fun n h => ?_) siPure_pure.mp
    exact id_freeN_l h.2 h.1
  exact wand_intro_left (wand_intro_left ((sep_mono_right sep_emp.mp).trans H))

@[rocq_alias cmra_later_opI]
theorem cmra_later_opI [CMRA A] [CMRA.IsTotal A] (x y1 y2 : A) :
    ▷ (✓ x ∧ x ≡ y1 • y2) ⊢@{PROP}
      ∃ z1 z2, x ≡ z1 • z2 ∧ ▷ (z1 ≡ y1) ∧ ▷ (z2 ≡ y2) := by
  suffices H : (<si_pure> (▷ (SiProp.cmraValid x ∧ SiProp.internalEq x (y1 • y2)))
      ⊢@{PROP} <si_pure> (∃ z1 z2, SiProp.internalEq x (z1 • z2) ∧
        ▷ (SiProp.internalEq z1 y1) ∧ ▷ (SiProp.internalEq z2 y2))) by
    simp only [internalCmraValid, internalEq, siPure_exist.to_eq, siPure_and.to_eq,
      siPure_later.to_eq] at H ⊢
    exact H
  refine siPure_mono fun n => ?_
  cases n with
  | zero =>
    intro _
    exact ⟨_, ⟨x, rfl⟩, _, ⟨core x, rfl⟩, (op_core_dist x).symm, trivial, trivial⟩
  | succ n =>
    intro hn
    obtain ⟨hv, he⟩ := hn
    obtain ⟨z1, z2, hx, hz1, hz2⟩ := extend' hv he
    exact ⟨_, ⟨z1, rfl⟩, _, ⟨z2, rfl⟩, Dist.of_eq hx, hz1, hz2⟩

end generic

section discrete_fun
open BI CMRA
variable [Sbi PROP]

@[rocq_alias discrete_fun_validI]
theorem discrete_fun_validI {ι : Type _} {β : ι → Type _} [∀ i, UCMRA (β i)]
    (g : ∀ i, β i) : ✓ g ⊣⊢@{PROP} ∀ i, ✓ (g i) := by
  simp only [internalCmraValid, ← siPure_forall.to_eq]
  refine siPure_mono_bi ⟨fun n h P => ?_, fun n h => ?_⟩
  · rintro ⟨i, rfl⟩; exact h i
  · exact fun i => h _ ⟨i, rfl⟩

end discrete_fun

section excl
open BI Excl OFE
variable [Sbi PROP] [OFE A]

@[rocq_alias algebra.excl_equivI]
theorem excl_equivI (x y : Excl A) :
    x ≡ y ⊣⊢@{PROP}
      match x, y with
      | excl a, excl b => iprop(a ≡ b)
      | invalid, invalid => iprop(True)
      | _, _ => iprop(False) := by
  cases x <;> cases y
  · exact BI.excl_equivI_excl _ _
  · exact BI.excl_equivI_excl_invalid _
  · exact BI.excl_equivI_invalid_excl _
  · exact BI.excl_equivI_invalid _

@[rocq_alias excl_validI]
theorem excl_validI (x : Excl A) :
    ✓ x ⊣⊢@{PROP} match x with | invalid => iprop(False) | _ => iprop(True) := by
  cases x with
  | excl a => exact ⟨true_intro, internalCmraValid_intro trivial⟩
  | invalid =>
    refine ⟨?_, false_elim⟩
    refine .trans (siPure_mono fun n h => ?_) siPure_pure.mp
    exact h.elim

@[rocq_alias excl_includedI]
theorem excl_includedI (x y : Excl A) :
    x ≼ y ⊣⊢@{PROP} ⌜y = Excl.invalid⌝ := by
  refine ⟨?_, ?_⟩
  · refine .trans (siPure_mono fun n h => ?_) siPure_pure.mp
    obtain ⟨_, ⟨c, rfl⟩, hc⟩ := h
    exact (incN_iff n).mp ⟨c, hc⟩
  · exact pure_elim' fun h => internalCmraIncluded_intro (inc_iff.mpr h)

end excl

section csum
open BI Csum OFE CMRA
variable [Sbi PROP]

@[rocq_alias algebra.csum_equivI]
theorem csum_equivI [OFE A] [OFE B] (x y : Csum A B) :
    x ≡ y ⊣⊢@{PROP}
      match x, y with
      | inl a, inl b => iprop(a ≡ b)
      | inr a, inr b => iprop(a ≡ b)
      | invalid, invalid => iprop(⌜True⌝)
      | _, _ => iprop(⌜False⌝) :=
  BI.csum_equivI x y

@[rocq_alias csum_validI]
theorem csum_validI [CMRA A] [CMRA B] (x : Csum A B) :
    ✓ x ⊣⊢@{PROP}
      match x with
      | inl a => iprop(✓ a)
      | inr b => iprop(✓ b)
      | invalid => iprop(False) := by
  cases x with
  | inl a => exact .rfl
  | inr b => exact .rfl
  | invalid =>
    refine ⟨?_, false_elim⟩
    refine .trans (siPure_mono fun n h => ?_) siPure_pure.mp
    exact h.elim

@[rocq_alias csum_includedI]
theorem csum_includedI [CMRA A] [CMRA B] (x y : Csum A B) :
    x ≼ y ⊣⊢@{PROP}
      match x, y with
      | inl a, inl b => iprop(a ≼ b)
      | inr a, inr b => iprop(a ≼ b)
      | _, invalid => iprop(True)
      | _, _ => iprop(False) := by
  cases x <;> cases y
  · simp only [internalCmraIncluded, internalEq]
    refine siPure_mono_bi ⟨fun n h => ?_, fun n h => ?_⟩
    · obtain ⟨_, ⟨c, rfl⟩, hc⟩ := h
      rcases c with c | c | _
      · exact ⟨_, ⟨c, rfl⟩, hc⟩
      · exact hc.elim
      · exact hc.elim
    · obtain ⟨_, ⟨c, rfl⟩, hc⟩ := h
      exact ⟨_, ⟨inl c, rfl⟩, hc⟩
  · refine ⟨?_, false_elim⟩
    refine .trans (siPure_mono ?_) siPure_pure.mp
    rintro n ⟨_, ⟨c, rfl⟩, hc⟩
    rcases c with c | c | _ <;> exact hc
  · exact ⟨true_intro, internalCmraIncluded_intro (Csum.invalid_included _)⟩
  · refine ⟨?_, false_elim⟩
    refine .trans (siPure_mono ?_) siPure_pure.mp
    rintro n ⟨_, ⟨c, rfl⟩, hc⟩
    rcases c with c | c | _ <;> exact hc
  · simp only [internalCmraIncluded, internalEq]
    refine siPure_mono_bi ⟨fun n h => ?_, fun n h => ?_⟩
    · obtain ⟨_, ⟨c, rfl⟩, hc⟩ := h
      rcases c with c | c | _
      · exact hc.elim
      · exact ⟨_, ⟨c, rfl⟩, hc⟩
      · exact hc.elim
    · obtain ⟨_, ⟨c, rfl⟩, hc⟩ := h
      exact ⟨_, ⟨inr c, rfl⟩, hc⟩
  · exact ⟨true_intro, internalCmraIncluded_intro (Csum.invalid_included _)⟩
  · refine ⟨?_, false_elim⟩
    refine .trans (siPure_mono ?_) siPure_pure.mp
    rintro n ⟨_, ⟨c, rfl⟩, hc⟩
    exact hc
  · refine ⟨?_, false_elim⟩
    refine .trans (siPure_mono ?_) siPure_pure.mp
    rintro n ⟨_, ⟨c, rfl⟩, hc⟩
    exact hc
  · exact ⟨true_intro, internalCmraIncluded_intro (Csum.invalid_included _)⟩

end csum

section list
open BI OFE
variable [Sbi PROP] [OFE A]

@[rocq_alias list_equivI]
theorem list_equivI (l1 l2 : List A) :
    l1 ≡ l2 ⊣⊢@{PROP} ∀ (i : Nat), (l1[i]? : Option A) ≡ (l2[i]? : Option A) := by
  simp only [internalEq, ← siPure_forall.to_eq]
  refine siPure_mono_bi ⟨fun n h P => ?_, fun n h => ?_⟩
  · rintro ⟨i, rfl⟩; exact list_dist_lookup.mp h i
  · exact list_dist_lookup.mpr fun i => h _ ⟨i, rfl⟩

end list

section gmap
open BI CMRA Std PartialMap
variable [Sbi PROP] {M : Type _ → Type _} {K : Type _} [LawfulPartialMap M K]

@[rocq_alias gmap_equivI]
theorem gmap_equivI [OFE V] (m1 m2 : M V) :
    m1 ≡ m2 ⊣⊢@{PROP} ∀ i, get? m1 i ≡ get? m2 i := by
  simp only [internalEq, ← siPure_forall.to_eq]
  refine siPure_mono_bi ⟨fun n h P => ?_, fun n h => ?_⟩
  · rintro ⟨i, rfl⟩; exact h i
  · exact fun i => h _ ⟨i, rfl⟩

@[rocq_alias gmap_validI]
theorem gmap_validI [CMRA V] (m : M V) :
    ✓ m ⊣⊢@{PROP} ∀ i, ✓ (get? m i) := by
  simp only [internalCmraValid, ← siPure_forall.to_eq]
  refine siPure_mono_bi ⟨fun n h P => ?_, fun n h => ?_⟩
  · rintro ⟨i, rfl⟩; exact h i
  · exact fun i => h _ ⟨i, rfl⟩

@[rocq_alias singleton_validI]
theorem singleton_validI [CMRA V] (i : K) (x : V) :
    ✓ (PartialMap.singleton i x : M V) ⊣⊢@{PROP} ✓ x :=
  ⟨siPure_mono fun _ => Heap.singleton_validN_iff.mp,
   siPure_mono fun _ => Heap.singleton_validN_iff.mpr⟩

@[rocq_alias gmap_union_equiv_eqI]
theorem gmap_union_equiv_eqI [OFE V] (m m1 m2 : M V) :
    m ≡ m1 ∪ m2 ⊣⊢@{PROP}
      ∃ m1' m2', ⌜m = m1' ∪ m2'⌝ ∧ m1' ≡ m1 ∧ m2' ≡ m2 := by
  suffices H : (<si_pure> SiProp.internalEq m (m1 ∪ m2) ⊣⊢@{PROP}
      (<si_pure> (∃ m1' m2', ⌜m = m1' ∪ m2'⌝ ∧ SiProp.internalEq m1' m1 ∧
        SiProp.internalEq m2' m2))) by
    simp only [internalEq, H.to_eq, siPure_exist.to_eq, siPure_and.to_eq, siPure_pure.to_eq,
      BIBase.BiEntails.rfl]
  constructor
  · refine siPure_mono fun n h => ?_
    obtain ⟨m1', m2', heq, h1, h2⟩ := _root_.PartialMap.union_dist_iff.mp h
    apply SiProp.instBI.sExists_intro
    · exists m1'
    apply SiProp.instBI.sExists_intro
    · exists m2'
    exact ⟨heq, h1, h2⟩
  · refine siPure_mono fun n h => ?_
    obtain ⟨_, ⟨m1', rfl⟩, _, ⟨m2', rfl⟩, heq, h1, h2⟩ := h
    exact _root_.PartialMap.union_dist_iff.mpr ⟨m1', m2', heq, h1, h2⟩

end gmap

section view
open BI CMRA View ViewRel IsViewRel
variable [Sbi PROP] [OFE A] [UCMRA B] {R : ViewRel A B} [IsViewRel R]

@[rocq_alias view_both_dfrac_validI_1]
theorem view_both_dfrac_validI_1 (relI : SiProp) (dq : DFrac) (a : A) (b : B)
    (H : ∀ n, R n a b → relI.holds n) :
    ✓ ((●V{dq} a : View R) • ◯V b) ⊢@{PROP} ⌜✓ dq⌝ ∧ <si_pure> relI := by
  refine .trans (siPure_mono (Qi := iprop(⌜✓ dq⌝ ∧ relI)) fun n hn => ?_)
    (siPure_and.mp.trans (and_mono_left siPure_pure.mp))
  exact ⟨(auth_op_frag_validN_iff.mp hn).1, H n (auth_op_frag_validN_iff.mp hn).2⟩

@[rocq_alias view_both_dfrac_validI_2]
theorem view_both_dfrac_validI_2 (relI : SiProp) (dq : DFrac) (a : A) (b : B)
    (H : ∀ n, relI.holds n → R n a b) :
    ⌜✓ dq⌝ ∧ <si_pure> relI ⊢@{PROP} ✓ ((●V{dq} a : View R) • ◯V b) := by
  refine .trans ((and_mono_left siPure_pure.mpr).trans siPure_and.mpr)
    (siPure_mono (Pi := iprop(⌜✓ dq⌝ ∧ relI)) fun n hn => ?_)
  exact auth_op_frag_validN_iff.mpr ⟨hn.1, H n hn.2⟩

@[rocq_alias view_both_dfrac_validI]
theorem view_both_dfrac_validI (relI : SiProp) (dq : DFrac) (a : A) (b : B)
    (H : ∀ n, R n a b ↔ relI.holds n) :
    ✓ ((●V{dq} a : View R) • ◯V b) ⊣⊢@{PROP} ⌜✓ dq⌝ ∧ <si_pure> relI :=
  ⟨view_both_dfrac_validI_1 relI dq a b (fun n => (H n).mp),
   view_both_dfrac_validI_2 relI dq a b (fun n => (H n).mpr)⟩

@[rocq_alias view_both_validI_1]
theorem view_both_validI_1 (relI : SiProp) (a : A) (b : B)
    (H : ∀ n, R n a b → relI.holds n) :
    ✓ ((●V a : View R) • ◯V b) ⊢@{PROP} <si_pure> relI :=
  siPure_mono fun n hn => H n (auth_one_op_frag_validN_iff.mp hn)

@[rocq_alias view_both_validI_2]
theorem view_both_validI_2 (relI : SiProp) (a : A) (b : B)
    (H : ∀ n, relI.holds n → R n a b) :
    <si_pure> relI ⊢@{PROP} ✓ ((●V a : View R) • ◯V b) :=
  siPure_mono fun n hn => auth_one_op_frag_validN_iff.mpr (H n hn)

@[rocq_alias view_both_validI]
theorem view_both_validI (relI : SiProp) (a : A) (b : B)
    (H : ∀ n, R n a b ↔ relI.holds n) :
    ✓ ((●V a : View R) • ◯V b) ⊣⊢@{PROP} <si_pure> relI :=
  ⟨view_both_validI_1 relI a b (fun n => (H n).mp),
   view_both_validI_2 relI a b (fun n => (H n).mpr)⟩

@[rocq_alias view_auth_dfrac_validI]
theorem view_auth_dfrac_validI (relI : SiProp) (dq : DFrac) (a : A)
    (H : ∀ n, relI.holds n ↔ R n a UCMRA.unit) :
    ✓ (●V{dq} a : View R) ⊣⊢@{PROP} ⌜✓ dq⌝ ∧ <si_pure> relI := by
  refine ⟨?_, ?_⟩
  · refine .trans (siPure_mono (Qi := iprop(⌜✓ dq⌝ ∧ relI)) fun n hn => ?_)
      (siPure_and.mp.trans (and_mono_left siPure_pure.mp))
    exact ⟨(auth_validN_iff.mp hn).1, (H n).mpr (auth_validN_iff.mp hn).2⟩
  · refine .trans ((and_mono_left siPure_pure.mpr).trans siPure_and.mpr)
      (siPure_mono (Pi := iprop(⌜✓ dq⌝ ∧ relI)) fun n hn => ?_)
    exact auth_validN_iff.mpr ⟨hn.1, (H n).mp hn.2⟩

@[rocq_alias view_auth_validI]
theorem view_auth_validI (relI : SiProp) (a : A)
    (H : ∀ n, relI.holds n ↔ R n a UCMRA.unit) :
    ✓ (●V a : View R) ⊣⊢@{PROP} <si_pure> relI :=
  ⟨siPure_mono fun n hn => (H n).mpr ((auth_one_validN_iff n a).mp hn),
   siPure_mono fun n hn => (auth_one_validN_iff n a).mpr ((H n).mp hn)⟩

@[rocq_alias view_frag_validI]
theorem view_frag_validI (relI : SiProp) (b : B)
    (H : ∀ n, relI.holds n ↔ ∃ a, R n a b) :
    ✓ (◯V b : View R) ⊣⊢@{PROP} <si_pure> relI :=
  ⟨siPure_mono fun n hn => (H n).mpr (frag_validN_iff.mp hn),
   siPure_mono fun n hn => frag_validN_iff.mpr ((H n).mp hn)⟩

end view

section excl_auth
open BI ExclAuth
variable [Sbi PROP] [OFE A]

@[rocq_alias excl_auth_agreeI]
theorem excl_auth_agreeI (a b : A) :
    ✓ ((●E a) • (◯E b)) ⊢@{PROP} a ≡ b :=
  siPure_mono fun _ h => agreeN h

end excl_auth

section frac_agree
open BI DFracAgree
variable [Sbi PROP] {A : Type _} [OFE A]

@[rocq_alias frac_agree_validI]
theorem frac_agree_validI (q : Qp) (a : A) :
    internalCmraValid (Frac.mk q a) ⊣⊢@{PROP} ⌜q.val ≤ 1⌝ :=
  (dfrac_agree_validI (DFrac.own q) a).trans
    ⟨pure_mono DFrac.valid_own.mp, pure_mono DFrac.valid_own.mpr⟩

@[rocq_alias frac_agree_validI_2]
theorem frac_agree_validI_2 (q1 q2 : Qp) (a b : A) :
    internalCmraValid (Frac.mk q1 a • Frac.mk q2 b) ⊣⊢@{PROP}
      ⌜(q1 + q2).val ≤ 1⌝ ∧ internalEq a b :=
  (dfrac_agree_validI_2 (DFrac.own q1) (DFrac.own q2) a b).trans
    (and_congr_left ⟨pure_mono DFrac.valid_own.mp, pure_mono DFrac.valid_own.mpr⟩)

end frac_agree

end Iris
