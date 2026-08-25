/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.BI.BI
public import Iris.BI.Cmra
public import Iris.BI.SbiUnfold
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

namespace Iris

section prod

open BI Std BIBase.BiEntails

@[rocq_alias prod_validI]
theorem prod_validI [Sbi PROP] [CMRA A] [CMRA B] (x : A × B) :
    ✓ x ⊣⊢@{PROP} ✓ x.1 ∧ ✓ x.2 := by
  sbi_unfold; intro _; exact .rfl

@[rocq_alias prod_includedI]
theorem prod_includedI [Sbi PROP] [CMRA A] [CMRA B] (x y : A × B) :
    x ≼ y ⊣⊢@{PROP} x.1 ≼ y.1 ∧ x.2 ≼ y.2 := by
  sbi_unfold; intro _; exact Prod.incN_def

end prod

section option

open BI Std BIBase.BiEntails

@[rocq_alias option_validI]
theorem option_validI [Sbi PROP] [CMRA A] {mx : Option A} :
  ✓ mx ⊣⊢@{PROP} mx.elim iprop(True) internalCmraValid := by
  cases mx <;> simp only [Option.elim] <;> sbi_unfold <;> intro _ <;> exact .rfl

@[rocq_alias option_includedI]
theorem option_includedI [Sbi PROP] [CMRA A] {mx my : Option A} :
  mx ≼ my ⊣⊢@{PROP}
    mx.elim iprop(True) fun x => my.elim iprop(False) fun y => iprop((x ≼ y) ∨ (x ≡ y)) := by
  rcases mx with _ | x <;> rcases my with _ | y <;>
    try exact internalCmraIncluded_pure fun _ => by simp [Option.incN_iff]
  simp only [Option.elim]; sbi_unfold; intro _; exact Option.some_incN_some_iff.trans Or.comm

@[rocq_alias option_included_totalI]
theorem option_included_totalI [Sbi PROP] [CMRA A] [CMRA.IsTotal A] {mx my : Option A} :
  mx ≼ my ⊣⊢@{PROP}
    mx.elim iprop(True) fun x => my.elim iprop(False) fun y => iprop(x ≼ y) := by
  rcases mx with _ | x <;> rcases my with _ | y <;>
    first
    | exact internalCmraIncluded_iff fun _ => by simp [Option.incN_iff_is_total]
    | exact internalCmraIncluded_pure fun _ => by simp [Option.incN_iff_is_total]

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
  sbi_unfold; intro _; exact auth_op_frag_validN_iff

@[rocq_alias gmap_view_both_validI]
theorem auth_op_frag_one_validI [Sbi PROP] (dp : DFrac) (m : H V) k v :
  ✓ (Auth dp m • Frag k (.own One.one) v) ⊣⊢@{PROP}
    ⌜✓ dp⌝ ∧ ✓ v ∧ get? m k ≡ .some v := by
  sbi_unfold; intro _; exact auth_op_frag_one_validN_iff

@[rocq_alias gmap_view_both_validI_total]
theorem auth_op_frag_validI_total [Sbi PROP] [CMRA.IsTotal V] (dp : DFrac) (m : H V) k dq v :
  ✓ (Auth dp m • Frag k dq v) ⊢@{PROP}
    ∃ v', ⌜✓ dp⌝ ∧ ⌜✓ dq⌝ ∧ ⌜get? m k = .some v'⌝ ∧
      ✓ v' ∧ v ≼ v' := by
  sbi_unfold; intro _; exact auth_op_frag_validN_total_iff

@[rocq_alias gmap_view_frag_op_validI]
theorem frag_op_frag_validI [Sbi PROP] k dq1 dq2 v1 v2 :
  ✓ (Frag (H := H) (V := V) k dq1 v1 • Frag k dq2 v2) ⊣⊢@{PROP}
    ⌜✓ (dq1 • dq2)⌝ ∧ ✓ (v1 • v2) := by
  sbi_unfold; intro _; exact frag_op_validN_iff

end heap_view

section agree_inclusion

open Iris BI Agree OFE

variable [Sbi PROP] [OFE A]

@[rocq_alias agree_equivI]
theorem agree_equivI {a b : A} : toAgree a ≡ toAgree b ⊣⊢@{PROP} a ≡ b := by
  sbi_unfold; intro _; exact ⟨Agree.toAgree_injN, (NonExpansive.ne ·)⟩

@[rocq_alias agree_op_invI]
theorem agree_op_invI {x y : Agree A} : ✓ (x • y) ⊢@{PROP} x ≡ y :=
  siPure_mono (fun _ => op_invN)

@[rocq_alias to_agree_validI]
theorem toAgree_validI (a : A) :
    ⊢@{PROP} ✓ (toAgree a) :=
  internalCmraValid_intro fun _ => by simp

@[rocq_alias to_agree_op_validI]
theorem toAgree_op_validI (a b : A) :
    ✓ (toAgree a • toAgree b) ⊣⊢@{PROP} a ≡ b := by
  sbi_unfold; intro _; exact toAgree_op_validN_iff_dist

@[rocq_alias to_agree_uninjI]
theorem toAgree_uninjI (x : Agree A) :
    ✓ x ⊢@{PROP} ∃ a, toAgree a ≡ x := by
  sbi_unfold; intro _; exact fun h => toAgree_uninjN h

@[rocq_alias agree_op_equiv_to_agreeI]
theorem agree_op_equiv_toAgreeI (x y : Agree A) (a : A) :
    x • y ≡ toAgree a ⊢@{PROP} x ≡ y ∧ y ≡ toAgree a := by
  sbi_unfold; intro _ h
  have hxy := op_invN (h.validN.mpr toAgree_validN)
  exact ⟨hxy, ((Dist.of_eq idemp).symm.trans hxy.symm.op_l).trans h⟩

@[rocq_alias agree_includedI]
theorem agree_includedI (x y : Agree A) :
    x ≼ y ⊣⊢@{PROP} y ≡ x • y := by
  sbi_unfold; intro _
  exact includedN.trans ⟨(·.trans op_commN), (·.trans op_commN)⟩

@[rocq_alias to_agree_includedI]
theorem toAgree_includedI (a b : A) :
    toAgree a ≼ toAgree b ⊣⊢@{PROP} a ≡ b := by
  sbi_unfold; intro _; exact toAgree_includedN

end agree_inclusion

section auth
open Iris BI Auth

variable [Sbi PROP] [UCMRA A]

@[rocq_alias auth_auth_dfrac_validI]
theorem auth_dfrac_validI (dq : DFrac) (a : A) :
    ✓ (●{dq} a : Auth A) ⊣⊢@{PROP} ⌜✓ dq⌝ ∧ ✓ a := by
  sbi_unfold; intro _; exact auth_dfrac_validN

@[rocq_alias auth_auth_validI]
theorem auth_validI (a : A) : ✓ (● a : Auth A) ⊣⊢@{PROP} ✓ a := by
  sbi_unfold; intro _; exact auth_validN

@[rocq_alias auth_auth_dfrac_op_validI]
theorem auth_dfrac_op_validI (dq1 dq2 : DFrac) (a1 a2 : A) :
    ✓ ((●{dq1} a1) • (●{dq2} a2)) ⊣⊢@{PROP}
      ⌜✓ (dq1 • dq2)⌝ ∧ a1 ≡ a2 ∧ ✓ a1 := by
  sbi_unfold; intro _; exact auth_dfrac_op_validN

@[rocq_alias auth_frag_validI]
theorem frag_validI (a : A) :
    ✓ (◯ a : Auth A) ⊣⊢@{PROP} ✓ a := by
  sbi_unfold; intro _; exact frag_validN

@[rocq_alias auth_both_dfrac_validI]
theorem both_dfrac_validI (dq : DFrac) (a b : A) :
    ✓ ((●{dq} a) • ◯ b) ⊣⊢@{PROP}
    ⌜✓ dq⌝ ∧ b ≼ a ∧ ✓ a := by
  sbi_unfold; intro _; exact both_dfrac_validN

@[rocq_alias auth_both_validI]
theorem auth_both_validI (a b : A) :
    ✓ ((● a : Auth A) • ◯ b) ⊣⊢@{PROP}
      b ≼ a ∧ ✓ a := by
  sbi_unfold; intro _; exact ⟨fun h => (both_dfrac_validN.mp h).2,
    fun h => both_dfrac_validN.mpr ⟨DFrac.valid_own_one, h⟩⟩

end auth

section dfrac_agree
variable [Sbi PROP] {A : Type _} [OFE A]

open BI

@[rocq_alias dfrac_agree_validI]
theorem dfrac_agree_validI (dq : DFrac) (x : A) :
    internalCmraValid (DFracAgree.mk dq x) ⊣⊢@{PROP} ⌜✓ dq⌝ := by
  sbi_unfold; intro _; exact ⟨fun h => h.1, fun h => ⟨h, by simp [DFracAgree.mk]⟩⟩

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
    refine siPure_and_sep.mpr.trans ?_; sbi_unfold; intro _; exact fun h => id_freeN_r h.2 h.1
  exact wand_intro_left (wand_intro_left ((sep_mono_right sep_emp.mp).trans H))

@[rocq_alias id_freeI_l]
theorem id_freeI_l [CMRA A] (x y : A) [IdFree x] :
    ⊢@{PROP} ✓ x -∗ (y • x) ≡ x -∗ False := by
  have H : iprop((y • x) ≡ x ∗ ✓ x) ⊢@{PROP} False := by
    refine siPure_and_sep.mpr.trans ?_; sbi_unfold; intro _; exact fun h => id_freeN_l h.2 h.1
  exact wand_intro_left (wand_intro_left ((sep_mono_right sep_emp.mp).trans H))

@[rocq_alias cmra_later_opI]
theorem cmra_later_opI [CMRA A] [CMRA.IsTotal A] (x y1 y2 : A) :
    ▷ (✓ x ∧ x ≡ y1 • y2) ⊢@{PROP}
      ∃ z1 z2, x ≡ z1 • z2 ∧ ▷ (z1 ≡ y1) ∧ ▷ (z2 ≡ y2) := by
  sbi_unfold; intro n; cases n
  · exact fun _ => ⟨x, core x, (op_core_dist x).symm, trivial, trivial⟩
  · exact fun ⟨hv, he⟩ =>
      have ⟨z1, z2, hx, hz1, hz2⟩ := extend' hv he
      ⟨z1, z2, Dist.of_eq hx, hz1, hz2⟩

end generic

section discrete_fun
open BI CMRA
variable [Sbi PROP]

@[rocq_alias discrete_fun_validI]
theorem discrete_fun_validI {ι : Type _} {β : ι → Type _} [∀ i, UCMRA (β i)]
    (g : ∀ i, β i) : ✓ g ⊣⊢@{PROP} ∀ i, ✓ (g i) := by
  sbi_unfold; intro _; exact .rfl

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
  cases x <;> cases y <;> sbi_unfold <;> intro _ <;> exact .rfl

@[rocq_alias excl_validI]
theorem excl_validI (x : Excl A) :
    ✓ x ⊣⊢@{PROP} ⌜x ≠ Excl.invalid⌝ := by
  sbi_unfold; intro _
  cases x with
  | excl a => exact ⟨fun _ => nofun, fun _ => trivial⟩
  | invalid => exact ⟨fun h => h.elim, fun h => (h rfl).elim⟩

@[rocq_alias excl_includedI]
theorem excl_includedI (x y : Excl A) :
    x ≼ y ⊣⊢@{PROP} ⌜y = Excl.invalid⌝ :=
  internalCmraIncluded_pure incN_iff

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
  cases x <;> sbi_unfold <;> intro _ <;> exact .rfl

@[rocq_alias csum_includedI]
theorem csum_includedI [CMRA A] [CMRA B] (x y : Csum A B) :
    x ≼ y ⊣⊢@{PROP}
      match x, y with
      | inl a, inl b => iprop(a ≼ b)
      | inr a, inr b => iprop(a ≼ b)
      | _, invalid => iprop(True)
      | _, _ => iprop(False) := by
  cases x <;> cases y <;>
    first
    | exact internalCmraIncluded_iff fun _ => by simp [Csum.includedN]
    | exact internalCmraIncluded_pure fun _ => by simp [Csum.includedN]

end csum

section list
open BI OFE
variable [Sbi PROP] [OFE A]

@[rocq_alias list_equivI]
theorem list_equivI (l1 l2 : List A) :
    l1 ≡ l2 ⊣⊢@{PROP} ∀ (i : Nat), (l1[i]? : Option A) ≡ (l2[i]? : Option A) := by
  sbi_unfold; intro _; exact list_dist_lookup

end list

section heap
open BI CMRA Std PartialMap
variable [Sbi PROP] {M : Type _ → Type _} {K : Type _} [LawfulPartialMap M K]

@[rocq_alias gmap_equivI]
theorem heap_equivI [OFE V] (m1 m2 : M V) :
    m1 ≡ m2 ⊣⊢@{PROP} ∀ i, get? m1 i ≡ get? m2 i := by
  sbi_unfold; intro _; exact .rfl

@[rocq_alias gmap_validI]
theorem heap_validI [CMRA V] (m : M V) :
    ✓ m ⊣⊢@{PROP} ∀ i, ✓ (get? m i) := by
  sbi_unfold; intro _; exact .rfl

@[rocq_alias singleton_validI]
theorem singleton_validI [CMRA V] (i : K) (x : V) :
    ✓ (PartialMap.singleton i x : M V) ⊣⊢@{PROP} ✓ x := by
  sbi_unfold; intro _; exact Heap.singleton_validN_iff

@[rocq_alias gmap_union_equiv_eqI]
theorem heap_union_equiv_eqI [OFE V] (m m1 m2 : M V) :
    m ≡ m1 ∪ m2 ⊣⊢@{PROP}
      ∃ m1' m2', ⌜m = m1' ∪ m2'⌝ ∧ m1' ≡ m1 ∧ m2' ≡ m2 := by
  sbi_unfold; intro _; exact _root_.PartialMap.union_dist_iff

end heap

section view
open BI CMRA View ViewRel IsViewRel
variable [Sbi PROP] [OFE A] [UCMRA B] {R : ViewRel A B} [IsViewRel R]

@[rocq_alias view_both_dfrac_validI_1]
theorem view_both_dfrac_validI_1 (relI : SiProp) (dq : DFrac) (a : A) (b : B)
    (H : ∀ n, R n a b → relI.holds n) :
    ✓ ((●V{dq} a : View R) • ◯V b) ⊢@{PROP} ⌜✓ dq⌝ ∧ <si_pure> relI := by
  sbi_unfold; intro _
  exact fun hn => ⟨(auth_op_frag_validN_iff.mp hn).1, H _ (auth_op_frag_validN_iff.mp hn).2⟩

@[rocq_alias view_both_dfrac_validI_2]
theorem view_both_dfrac_validI_2 (relI : SiProp) (dq : DFrac) (a : A) (b : B)
    (H : ∀ n, relI.holds n → R n a b) :
    ⌜✓ dq⌝ ∧ <si_pure> relI ⊢@{PROP} ✓ ((●V{dq} a : View R) • ◯V b) := by
  sbi_unfold; intro _; exact fun hn => auth_op_frag_validN_iff.mpr ⟨hn.1, H _ hn.2⟩

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
  sbi_unfold; intro _
  exact ⟨fun hn => ⟨(auth_validN_iff.mp hn).1, (H _).mpr (auth_validN_iff.mp hn).2⟩,
    fun hn => auth_validN_iff.mpr ⟨hn.1, (H _).mp hn.2⟩⟩

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
