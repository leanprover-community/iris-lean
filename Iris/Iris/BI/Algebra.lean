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

private theorem siPure_congr_holds [Sbi PROP] {P Q : SiProp}
    (h : ∀ n, P.holds n ↔ Q.holds n) :
    <si_pure> P ⊣⊢@{PROP} <si_pure> Q :=
  .of_eq <| congrArg siPure <| OFE.eq_dist.mpr fun _ _ _ => h _

private theorem siProp_and_holds (P Q : SiProp) (n) :
    iprop(P ∧ Q).holds n ↔ P.holds n ∧ Q.holds n := Iff.rfl

private theorem siProp_or_holds (P Q : SiProp) (n) :
    iprop(P ∨ Q).holds n ↔ P.holds n ∨ Q.holds n := Iff.rfl

private theorem siProp_pure_holds (p : Prop) (n) :
    iprop(⌜p⌝ : SiProp).holds n ↔ p := Iff.rfl

private theorem siProp_siPure_holds (P : SiProp) (n) :
    iprop(<si_pure> P : SiProp).holds n ↔ P.holds n := Iff.rfl

private theorem siProp_exists_holds {A : Sort _} (Φ : A → SiProp) (n) :
    iprop(∃ x, Φ x).holds n ↔ ∃ x, (Φ x).holds n := by
  constructor
  · rintro ⟨P, ⟨x, rfl⟩, h⟩
    exact ⟨x, h⟩
  · rintro ⟨x, h⟩
    exact ⟨Φ x, ⟨x, rfl⟩, h⟩

private theorem siProp_internalEq_holds [OFE A] (a b : A) (n) :
    iprop(a ≡ b : SiProp).holds n ↔ a ≡{n}≡ b := Iff.rfl

private theorem siProp_primitive_internalEq_holds [OFE A] (a b : A) (n) :
    (SiProp.internalEq a b).holds n ↔ a ≡{n}≡ b := Iff.rfl

private theorem siProp_cmraValid_holds [CMRA A] (a : A) (n) :
    (SiProp.cmraValid a).holds n ↔ ✓{n} a := Iff.rfl

private theorem siProp_cmraIncluded_holds [CMRA A] (x y : A) (n) :
    iprop(∃ c, <si_pure> SiProp.internalEq y (x • c) : SiProp).holds n ↔ x ≼{n} y := by
  simp only [siProp_exists_holds]
  rfl

section prod

open BI Std BIBase.BiEntails

@[rocq_alias prod_validI]
theorem prod_validI [Sbi PROP] [CMRA A] [CMRA B] (x : A × B) :
    ✓ x ⊣⊢@{PROP} ✓ x.1 ∧ ✓ x.2 := by
  simp only [internalCmraValid, ←siPure_and.to_eq]
  apply siPure_congr_holds
  rintro n
  change (✓{n} x.1 ∧ ✓{n} x.2) ↔ _
  rfl

@[rocq_alias prod_includedI]
theorem prod_includedI [Sbi PROP] [CMRA A] [CMRA B] (x y : A × B) :
    x ≼ y ⊣⊢@{PROP} x.1 ≼ y.1 ∧ x.2 ≼ y.2 := by
  simp only [internalCmraIncluded, internalEq]
  rw [←siPure_and.to_eq]
  apply siPure_congr_holds
  intro n
  simp only [siProp_and_holds, siProp_exists_holds, siProp_siPure_holds,
    siProp_primitive_internalEq_holds]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨⟨w.fst, hw.1⟩, ⟨w.snd, hw.2⟩⟩
  · rintro ⟨⟨w1, hw1⟩, ⟨w2, hw2⟩⟩
    exact ⟨(w1, w2), hw1, hw2⟩

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
    rw [←siPure_or.to_eq]
    apply siPure_congr_holds
    intro n
    simp only [siProp_or_holds, siProp_cmraIncluded_holds,
      siProp_primitive_internalEq_holds]
    grind only [Option.some_incN_some_iff]

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
  · simp only [internalCmraIncluded, internalEq]
    apply siPure_congr_holds
    intro n
    simp only [siProp_cmraIncluded_holds]
    exact Option.some_incN_some_iff_is_total

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
  calc
    _ ⊣⊢ <si_pure> ∃ v' dq', ⌜✓ dp⌝ ∧ ⌜get? m k = some v'⌝ ∧
        SiProp.cmraValid (dq', v') ∧ ∃ c, some (dq', v') ≡ some (dq, v) • c := by
      apply siPure_congr_holds
      intro n
      simp only [siProp_and_holds, siProp_pure_holds, siProp_exists_holds,
        siProp_cmraValid_holds, siProp_internalEq_holds]
      exact auth_op_frag_validN_iff
    _ ⊣⊢@{PROP} _ := by
      simp only [internalCmraValid, internalCmraIncluded, siPure_exist.to_eq,
        siPure_and.to_eq, siPure_pure.to_eq]
      exact .rfl

@[rocq_alias gmap_view_both_validI]
theorem auth_op_frag_one_validI [Sbi PROP] (dp : DFrac) (m : H V) k v :
  ✓ (Auth dp m • Frag k (.own One.one) v) ⊣⊢@{PROP}
    ⌜✓ dp⌝ ∧ ✓ v ∧ get? m k ≡ .some v := by
  simp only [internalCmraValid, internalEq, ←siPure_and.to_eq]
  rw [←siPure_pure.to_eq, ←siPure_and.to_eq]
  apply siPure_congr_holds
  grind only [siProp_and_holds, siProp_pure_holds, siProp_siPure_holds,
    siProp_cmraValid_holds, siProp_internalEq_holds,
    siProp_primitive_internalEq_holds, auth_op_frag_one_validN_iff]

@[rocq_alias gmap_view_both_validI_total]
theorem auth_op_frag_validI_total [Sbi PROP] [CMRA.IsTotal V] (dp : DFrac) (m : H V) k dq v :
  ✓ (Auth dp m • Frag k dq v) ⊢@{PROP}
    ∃ v', ⌜✓ dp⌝ ∧ ⌜✓ dq⌝ ∧ ⌜get? m k = .some v'⌝ ∧
      ✓ v' ∧ v ≼ v' := by
  calc
    _ ⊢ <si_pure> ∃ v', ⌜✓ dp⌝ ∧ ⌜✓ dq⌝ ∧ ⌜get? m k = some v'⌝ ∧
        SiProp.cmraValid v' ∧ ∃ c, v' ≡ v • c := by
      refine siPure_mono fun n => ?_
      simp only [siProp_and_holds, siProp_pure_holds, siProp_exists_holds,
        siProp_cmraValid_holds, siProp_internalEq_holds]
      exact auth_op_frag_validN_total_iff
    _ ⊢@{PROP} _ := by
      simp only [internalCmraValid, internalCmraIncluded, siPure_exist.to_eq,
        siPure_and.to_eq, siPure_pure.to_eq]
      exact .rfl

@[rocq_alias gmap_view_frag_op_validI]
theorem frag_op_frag_validI [Sbi PROP] k dq1 dq2 v1 v2 :
  ✓ (Frag (H := H) (V := V) k dq1 v1 • Frag k dq2 v2) ⊣⊢@{PROP}
    ⌜✓ (dq1 • dq2)⌝ ∧ ✓ (v1 • v2) := by
  simp only [←(and_congr_left siPure_pure).to_eq, internalCmraValid, ←siPure_and.to_eq]
  apply siPure_congr_holds
  grind only [siProp_and_holds, siProp_pure_holds, siProp_siPure_holds,
    siProp_cmraValid_holds, frag_op_validN_iff]

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
  simp only [internalCmraValid, internalEq, ←siPure_exist.to_eq]
  refine siPure_mono fun n => ?_
  simp only [siProp_exists_holds, siProp_primitive_internalEq_holds]
  exact toAgree_uninjN

@[rocq_alias agree_op_equiv_to_agreeI]
theorem agree_op_equiv_toAgreeI (x y : Agree A) (a : A) :
    x • y ≡ toAgree a ⊢@{PROP} x ≡ y ∧ y ≡ toAgree a := by
  simp only [internalEq, ←siPure_and.to_eq]
  refine siPure_mono fun n h => ?_
  have hvalid : ✓{n} (x • y) := h.validN.mpr Agree.toAgree_validN
  have hxy := Agree.op_invN hvalid
  have hop : x • y ≡{n}≡ y := hxy.op_l.trans (Agree.idemp (x := y)).dist
  exact ⟨hxy, hop.symm.trans h⟩

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
  simp only [internalCmraIncluded, internalEq]
  apply siPure_congr_holds
  intro n
  simp only [siProp_cmraIncluded_holds, siProp_primitive_internalEq_holds]
  exact toAgree_includedN

end agree_inclusion

section auth
open Iris BI Auth

variable [Sbi PROP] [UCMRA A]

@[rocq_alias auth_auth_dfrac_validI]
theorem auth_dfrac_validI (dq : DFrac) (a : A) :
    ✓ (●{dq} a : Auth A) ⊣⊢@{PROP} ⌜✓ dq⌝ ∧ ✓ a := by
  simp only [←(and_congr_left siPure_pure).to_eq, internalCmraValid, ←siPure_and.to_eq]
  apply siPure_congr_holds
  grind only [siProp_and_holds, siProp_pure_holds, siProp_siPure_holds,
    siProp_cmraValid_holds, auth_dfrac_validN]

@[rocq_alias auth_auth_validI]
theorem auth_validI (a : A) : ✓ (● a : Auth A) ⊣⊢@{PROP} ✓ a := by
  apply siPure_congr_holds
  grind only [SiProp.cmraValid, auth_validN]

@[rocq_alias auth_auth_dfrac_op_validI]
theorem auth_dfrac_op_validI (dq1 dq2 : DFrac) (a1 a2 : A) :
    ✓ ((●{dq1} a1) • (●{dq2} a2)) ⊣⊢@{PROP}
      ⌜✓ (dq1 • dq2)⌝ ∧ a1 ≡ a2 ∧ ✓ a1 := by
  simp only [←(and_congr_left siPure_pure).to_eq, internalEq, internalCmraValid,
    ←(siPure_and.trans (and_congr_right siPure_and)).to_eq]
  apply siPure_congr_holds
  grind only [siProp_and_holds, siProp_pure_holds, siProp_siPure_holds,
    siProp_cmraValid_holds, siProp_internalEq_holds,
    siProp_primitive_internalEq_holds, auth_dfrac_op_validN]

@[rocq_alias auth_frag_validI]
theorem frag_validI (a : A) :
    ✓ (◯ a : Auth A) ⊣⊢@{PROP} ✓ a := by
  apply siPure_congr_holds
  grind only [SiProp.cmraValid, frag_validN]

@[rocq_alias auth_both_dfrac_validI]
theorem both_dfrac_validI (dq : DFrac) (a b : A) :
    ✓ ((●{dq} a) • ◯ b) ⊣⊢@{PROP}
    ⌜✓ dq⌝ ∧ b ≼ a ∧ ✓ a := by
  simp only [internalCmraValid, internalCmraIncluded, internalEq]
  rw [←siPure_pure.to_eq, ←siPure_and.to_eq, ←siPure_and.to_eq]
  apply siPure_congr_holds
  intro n
  simp only [siProp_and_holds, siProp_pure_holds, siProp_siPure_holds,
    siProp_exists_holds, siProp_cmraValid_holds,
    siProp_primitive_internalEq_holds]
  exact both_dfrac_validN

@[rocq_alias auth_both_validI]
theorem auth_both_validI (a b : A) :
    ✓ ((● a : Auth A) • ◯ b) ⊣⊢@{PROP}
      b ≼ a ∧ ✓ a := by
  simp only [internalCmraIncluded, internalCmraValid, internalEq]
  rw [←siPure_and.to_eq]
  apply siPure_congr_holds
  intro n
  simp only [siProp_and_holds, siProp_siPure_holds, siProp_exists_holds,
    siProp_cmraValid_holds, siProp_primitive_internalEq_holds]
  exact both_validN

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

end Iris
