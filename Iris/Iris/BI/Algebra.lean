/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergei Stepanenko
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
This file provides introduction rules (BI entailments) for (some) ORA operations and properties.
-/

@[expose] public section

namespace Iris

section prod

open BI Iris.Std BIBase.BiEntails

@[rocq_alias prod_validI]
theorem prod_validI [Sbi PROP] [ORA Nat A] [ORA Nat B] (x : A × B) :
    ✓[Nat] x ⊣⊢@{PROP} ✓[Nat] x.1 ∧ ✓[Nat] x.2 := by
  sbi_unfold; intro _; exact .rfl

theorem prod_ordI [Sbi PROP] [ORA Nat A] [ORA Nat B] (x y : A × B) :
    x ≼ₒ[Nat] y ⊣⊢@{PROP} x.1 ≼ₒ[Nat] y.1 ∧ x.2 ≼ₒ[Nat] y.2 := by
  sbi_unfold; intro _; exact Prod.ordN_def

@[rocq_alias prod_includedI]
theorem prod_includedI [Sbi PROP] [ORA Nat A] [ORA Nat B] (x y : A × B) :
    x ≼ y ⊣⊢@{PROP} x.1 ≼ y.1 ∧ x.2 ≼ y.2 := by
  sbi_unfold; intro _; exact Prod.incN_def

end prod

section option

open BI Iris.Std BIBase.BiEntails

@[rocq_alias option_validI]
theorem option_validI [Sbi PROP] [ORA Nat A] {mx : Option A} :
  ✓[Nat] mx ⊣⊢@{PROP} mx.elim iprop(True) internalCmraValid := by
  cases mx <;> simp only [Option.elim] <;> sbi_unfold <;> intro _ <;> exact .rfl

theorem option_ordI [Sbi PROP] [ORA Nat A] {mx my : Option A} :
  mx ≼ₒ[Nat] my ⊣⊢@{PROP}
    mx.elim (my.elim iprop(True) fun y => iprop(⌜Increasing Nat y⌝))
      fun x => my.elim iprop(False) fun y => iprop((x ≼ₒ[Nat] y) ∨ (x ≡ y)) := by
  rcases mx with _ | x <;> rcases my with _ | y
  · exact internalCmraOrder_pure fun _ => iff_true_intro trivial
  · exact internalCmraOrder_pure fun _ => Option.none_ordN_some_iff
  · exact internalCmraOrder_pure fun _ => iff_false_intro Option.not_some_ordN_none
  · simp only [Option.elim]; sbi_unfold; intro _; exact Option.some_ordN_some_iff.trans Or.comm

@[rocq_alias option_includedI]
theorem option_includedI [Sbi PROP] [ORA Nat A] {mx my : Option A} :
  mx ≼ my ⊣⊢@{PROP}
    mx.elim iprop(True) fun x => my.elim iprop(False) fun y => iprop((x ≼ y) ∨ (x ≡ y)) := by
  rcases mx with _ | x <;> rcases my with _ | y <;>
    try exact internalCmraIncluded_pure fun _ => by simp [Option.incN_iff]
  simp only [Option.elim]; sbi_unfold; intro _; exact Option.some_incN_some_iff.trans Or.comm

theorem option_ord_totalI [Sbi PROP] [ORA Nat A] [IncOrd Nat A] [OrderRefl Nat A] {mx my : Option A} :
  mx ≼ₒ[Nat] my ⊣⊢@{PROP}
    mx.elim iprop(True) fun x => my.elim iprop(False) fun y => iprop(x ≼ₒ[Nat] y) := by
  rcases mx with _ | x <;> rcases my with _ | y <;>
    first
    | exact internalCmraOrder_iff fun _ => by simp [Option.ordN_iff_orderRefl]
    | exact internalCmraOrder_pure fun _ => by simp [Option.ordN_iff_orderRefl]

@[rocq_alias option_included_totalI]
theorem option_included_totalI [Sbi PROP] [ORA Nat A] [IsTotal A] {mx my : Option A} :
  mx ≼ my ⊣⊢@{PROP}
    mx.elim iprop(True) fun x => my.elim iprop(False) fun y => iprop(x ≼ y) := by
  rcases mx with _ | x <;> rcases my with _ | y <;>
    first
    | exact internalCmraIncluded_iff fun _ => by simp [Option.incN_iff_is_total]
    | exact internalCmraIncluded_pure fun _ => by simp [Option.incN_iff_is_total]

@[rocq_alias Some_included_totalI]
theorem Some_included_totalI [Sbi PROP] [ORA Nat A] [IsTotal A] {x y : A} :
    some x ≼ some y ⊣⊢@{PROP} x ≼ y :=
  option_included_totalI

theorem some_ordI [Sbi PROP] [ORA Nat A] [OrderRefl Nat A] {x y : A} :
    some x ≼ₒ[Nat] some y ⊣⊢@{PROP} x ≼ₒ[Nat] y :=
  internalCmraOrder_iff fun _ => Option.some_ordN_some_iff_orderRefl

theorem some_ordI_none [Sbi PROP] [ORA Nat A] {x : A} : some x ≼ₒ[Nat] none ⊢@{PROP} False :=
  (internalCmraOrder_pure fun _ => iff_false_intro Option.not_some_ordN_none).mp.trans
    (pure_elim' False.elim)

end option

section heap_view

open HeapView BI Iris.Std PartialMap LawfulPartialMap BIBase.BiEntails

variable {F K V : Type _} {H : Type _ → Type _}
variable [LawfulPartialMap H K] [ORA Nat V]

theorem auth_op_frag_validI_ord [Sbi PROP] [IncOrd Nat V] (dp : DFrac) (m : H V) k dq v :
  ✓[Nat] (Auth (SI := Nat) dp m • Frag k dq v) ⊣⊢@{PROP}
    ∃ v' dq', ⌜✓[Nat] dp⌝ ∧ ⌜get? m k = .some v'⌝ ∧ ✓[Nat] (dq', v') ∧
      some (dq, v) ≼ₒ[Nat] some (dq', v') := by
  sbi_unfold; intro _; exact auth_op_frag_validN_iff_ord

@[rocq_alias gmap_view_both_dfrac_validI]
theorem auth_op_frag_validI [Sbi PROP] [OrdInc Nat V] (dp : DFrac) (m : H V) k dq v :
  ✓[Nat] (Auth (SI := Nat) dp m • Frag k dq v) ⊣⊢@{PROP}
    ∃ v' dq', ⌜✓[Nat] dp⌝ ∧ ⌜get? m k = .some v'⌝ ∧ ✓[Nat] (dq', v') ∧
      some (dq, v) ≼ some (dq', v') := by
  sbi_unfold; intro _; exact auth_op_frag_validN_iff

@[rocq_alias gmap_view_both_validI]
theorem auth_op_frag_one_validI [Sbi PROP] (dp : DFrac) (m : H V) k v :
  ✓[Nat] (Auth (SI := Nat) dp m • Frag k (.own One.one) v) ⊣⊢@{PROP}
    ⌜✓[Nat] dp⌝ ∧ ✓[Nat] v ∧ get? m k ≡ .some v := by
  sbi_unfold; intro _; exact auth_op_frag_one_validN_iff

theorem auth_op_frag_validI_total_ord [Sbi PROP] [OrderRefl Nat V] [IncOrd Nat V] (dp : DFrac) (m : H V)
    k dq v :
  ✓[Nat] (Auth (SI := Nat) dp m • Frag k dq v) ⊢@{PROP}
    ∃ v', ⌜✓[Nat] dp⌝ ∧ ⌜✓[Nat] dq⌝ ∧ ⌜get? m k = .some v'⌝ ∧
      ✓[Nat] v' ∧ v ≼ₒ[Nat] v' := by
  sbi_unfold; intro _; exact auth_op_frag_validN_total_iff_ord

@[rocq_alias gmap_view_both_validI_total]
theorem auth_op_frag_validI_total [Sbi PROP] [OrderRefl Nat V] [OrdInc Nat V] (dp : DFrac) (m : H V)
    k dq v :
  ✓[Nat] (Auth (SI := Nat) dp m • Frag k dq v) ⊢@{PROP}
    ∃ v', ⌜✓[Nat] dp⌝ ∧ ⌜✓[Nat] dq⌝ ∧ ⌜get? m k = .some v'⌝ ∧
      ✓[Nat] v' ∧ v ≼ v' := by
  sbi_unfold; intro _; exact auth_op_frag_validN_total_iff

@[rocq_alias gmap_view_frag_op_validI]
theorem frag_op_frag_validI [Sbi PROP] k dq1 dq2 v1 v2 :
  ✓[Nat] (Frag (H := H) (V := V) k dq1 v1 • Frag (SI := Nat) k dq2 v2) ⊣⊢@{PROP}
    ⌜✓[Nat] (dq1 • dq2)⌝ ∧ ✓[Nat] (v1 • v2) := by
  sbi_unfold; intro _; exact frag_op_validN_iff

end heap_view

section agree_inclusion

open Iris BI Agree OFE

variable [Sbi PROP] [OFE Nat A]

@[rocq_alias agree_equivI]
theorem agree_equivI {a b : A} : toAgree a ≡ toAgree b ⊣⊢@{PROP} a ≡ b := by
  sbi_unfold; intro _; exact ⟨Agree.toAgree_injN, (NonExpansive.ne ·)⟩

@[rocq_alias agree_op_invI]
theorem agree_op_invI {x y : Agree A} : ✓[Nat] (x • y) ⊢@{PROP} x ≡ y :=
  siPure_mono (fun _ => op_invN)

@[rocq_alias to_agree_validI]
theorem toAgree_validI (a : A) :
    ⊢@{PROP} ✓[Nat] (toAgree a) :=
  internalCmraValid_intro fun _ => by simp

@[rocq_alias to_agree_op_validI]
theorem toAgree_op_validI (a b : A) :
    ✓[Nat] (toAgree a • toAgree b) ⊣⊢@{PROP} a ≡ b := by
  sbi_unfold; intro _; exact toAgree_op_validN_iff_dist

@[rocq_alias to_agree_uninjI]
theorem toAgree_uninjI (x : Agree A) :
    ✓[Nat] x ⊢@{PROP} ∃ a, toAgree a ≡ x := by
  sbi_unfold; intro _; exact fun h => toAgree_uninjN h

@[rocq_alias agree_op_equiv_to_agreeI]
theorem agree_op_equiv_toAgreeI (x y : Agree A) (a : A) :
    x • y ≡ toAgree a ⊢@{PROP} x ≡ y ∧ y ≡ toAgree a := by
  sbi_unfold; intro _ h
  have hxy := op_invN (h.validN.mpr toAgree_validN)
  exact ⟨hxy, ((Dist.of_eq idemp).symm.trans hxy.symm.op_l).trans h⟩

theorem agree_ordI (x y : Agree A) :
    x ≼ₒ[Nat] y ⊣⊢@{PROP} y ≡ x • y := by
  sbi_unfold; intro _
  exact ordN.trans ⟨(·.trans op_commN), (·.trans op_commN)⟩

@[rocq_alias agree_includedI]
theorem agree_includedI (x y : Agree A) :
    x ≼ y ⊣⊢@{PROP} y ≡ x • y :=
  internalCmraIncluded_iff_internalCmraOrder.trans (agree_ordI x y)

theorem toAgree_ordI (a b : A) :
    toAgree a ≼ₒ[Nat] toAgree b ⊣⊢@{PROP} a ≡ b := by
  sbi_unfold; intro _; exact toAgree_ordN

@[rocq_alias to_agree_includedI]
theorem toAgree_includedI (a b : A) :
    toAgree a ≼ toAgree b ⊣⊢@{PROP} a ≡ b :=
  internalCmraIncluded_iff_internalCmraOrder.trans (toAgree_ordI a b)

end agree_inclusion

section auth
open Iris BI Auth

variable [Sbi PROP] [UORA Nat A]

@[rocq_alias auth_auth_dfrac_validI]
theorem auth_dfrac_validI (dq : DFrac) (a : A) :
    ✓[Nat] (●{dq} a : Auth (SI := Nat) A) ⊣⊢@{PROP} ⌜✓[Nat] dq⌝ ∧ ✓[Nat] a := by
  sbi_unfold; intro _; exact auth_dfrac_validN

@[rocq_alias auth_auth_validI]
theorem auth_validI (a : A) : ✓[Nat] (● a : Auth (SI := Nat) A) ⊣⊢@{PROP} ✓[Nat] a := by
  sbi_unfold; intro _; exact auth_validN

@[rocq_alias auth_auth_dfrac_op_validI]
theorem auth_dfrac_op_validI (dq1 dq2 : DFrac) (a1 a2 : A) :
    ✓[Nat] ((●{dq1} a1 : Auth (SI := Nat) A) • (●{dq2} a2)) ⊣⊢@{PROP}
      ⌜✓[Nat] (dq1 • dq2)⌝ ∧ a1 ≡ a2 ∧ ✓[Nat] a1 := by
  sbi_unfold; intro _; exact auth_dfrac_op_validN

@[rocq_alias auth_frag_validI]
theorem frag_validI (a : A) :
    ✓[Nat] (◯ a : Auth (SI := Nat) A) ⊣⊢@{PROP} ✓[Nat] a := by
  sbi_unfold; intro _; exact frag_validN

theorem both_dfrac_validI_ord [IncOrd Nat A] (dq : DFrac) (a b : A) :
    ✓[Nat] ((●{dq} a : Auth (SI := Nat) A) • ◯ b) ⊣⊢@{PROP}
    ⌜✓[Nat] dq⌝ ∧ b ≼ₒ[Nat] a ∧ ✓[Nat] a := by
  sbi_unfold; intro _; exact both_dfrac_validN_ord

@[rocq_alias auth_both_dfrac_validI]
theorem both_dfrac_validI [OrdInc Nat A] (dq : DFrac) (a b : A) :
    ✓[Nat] ((●{dq} a : Auth (SI := Nat) A) • ◯ b) ⊣⊢@{PROP}
    ⌜✓[Nat] dq⌝ ∧ b ≼ a ∧ ✓[Nat] a := by
  sbi_unfold; intro _; exact both_dfrac_validN

theorem auth_both_validI_ord [IncOrd Nat A] (a b : A) :
    ✓[Nat] ((● a : Auth (SI := Nat) A) • ◯ b) ⊣⊢@{PROP}
      b ≼ₒ[Nat] a ∧ ✓[Nat] a := by
  sbi_unfold; intro _; exact both_validN_ord

@[rocq_alias auth_both_validI]
theorem auth_both_validI [OrdInc Nat A] (a b : A) :
    ✓[Nat] ((● a : Auth (SI := Nat) A) • ◯ b) ⊣⊢@{PROP}
      b ≼ a ∧ ✓[Nat] a := by
  sbi_unfold; intro _; exact both_validN

end auth

section dfrac_agree
variable [Sbi PROP] {A : Type _} [OFE Nat A]

open BI

@[rocq_alias dfrac_agree_validI]
theorem dfrac_agree_validI (dq : DFrac) (x : A) :
    internalCmraValid (DFracAgree.mk (SI := Nat) dq x) ⊣⊢@{PROP} ⌜✓[Nat] dq⌝ := by
  sbi_unfold; intro _; exact ⟨fun h => h.1, fun h => ⟨h, by simp [DFracAgree.mk]⟩⟩

@[rocq_alias dfrac_agree_validI_2]
theorem dfrac_agree_validI_2 (dq1 dq2 : DFrac) (x y : A) :
    internalCmraValid (DFracAgree.mk (SI := Nat) dq1 x • DFracAgree.mk dq2 y) ⊣⊢@{PROP}
      ⌜✓[Nat] (dq1 • dq2)⌝ ∧ internalEq x y :=
  (prod_validI _).trans (and_congr internalCmraValid_discrete (toAgree_op_validI x y))

end dfrac_agree

section generic
open BI ORA OFE
variable [Sbi PROP]

@[rocq_alias ucmra_unit_validI]
theorem ucmra_unit_validI [UORA Nat A] : ⊢@{PROP} ✓[Nat] (unit : A) := internalCmraValid_intro unit_valid

@[rocq_alias cmra_validI_op_r]
theorem cmra_validI_op_r [ORA Nat A] (x y : A) : ✓[Nat] (x • y) ⊢@{PROP} ✓[Nat] y :=
  siPure_mono fun _ => validN_op_right

@[rocq_alias cmra_validI_op_l]
theorem cmra_validI_op_l [ORA Nat A] (x y : A) : ✓[Nat] (x • y) ⊢@{PROP} ✓[Nat] x :=
  siPure_mono fun _ => validN_op_l

@[rocq_alias cmra_morphism_validI]
theorem cmra_morphism_validI [ORA Nat A] [ORA Nat B] (f : A -C>[Nat] B) (x : A) :
    ✓[Nat] x ⊢@{PROP} ✓[Nat] (f x) :=
  siPure_mono fun _ => f.validN

@[rocq_alias f_homom_includedI]
theorem f_homom_includedI [ORA Nat A] [ORA Nat B] (x y : A) (f : A → B) [NonExpansive Nat f]
    (Hf : ∀ c (n : Nat), f x • f c ≡{n}≡ f (x • c)) :
    x ≼ y ⊢@{PROP} f x ≼ f y :=
  siPure_mono <| BI.exists_elim fun c => BI.exists_intro_trans (f c) <|
    internalEq_entails.mpr fun n heq => (NonExpansive.ne heq).trans (Hf c n).symm

@[rocq_alias id_freeI_r]
theorem id_freeI_r [ORA Nat A] (x y : A) [IdFree Nat x] :
    ⊢@{PROP} ✓[Nat] x -∗ (x • y) ≡ x -∗ False := by
  have H : iprop((x • y) ≡ x ∗ ✓[Nat] x) ⊢@{PROP} False := by
    refine siPure_and_sep.mpr.trans ?_; sbi_unfold; intro _; exact fun h => id_freeN_r h.2 h.1
  exact wand_intro_left (wand_intro_left ((sep_mono_right sep_emp.mp).trans H))

@[rocq_alias id_freeI_l]
theorem id_freeI_l [ORA Nat A] (x y : A) [IdFree Nat x] :
    ⊢@{PROP} ✓[Nat] x -∗ (y • x) ≡ x -∗ False := by
  have H : iprop((y • x) ≡ x ∗ ✓[Nat] x) ⊢@{PROP} False := by
    refine siPure_and_sep.mpr.trans ?_; sbi_unfold; intro _; exact fun h => id_freeN_l h.2 h.1
  exact wand_intro_left (wand_intro_left ((sep_mono_right sep_emp.mp).trans H))

@[rocq_alias cmra_later_opI]
theorem cmra_later_opI [ORA Nat A] [IsTotal A] (x y1 y2 : A) :
    ▷ (✓[Nat] x ∧ x ≡ y1 • y2) ⊢@{PROP}
      ∃ z1 z2, x ≡ z1 • z2 ∧ ▷ (z1 ≡ y1) ∧ ▷ (z2 ≡ y2) := by
  sbi_unfold; intro n; cases n
  · exact fun _ => ⟨x, core x, (op_core_dist x).symm, trivial, trivial⟩
  · exact fun ⟨hv, he⟩ =>
      have ⟨z1, z2, hx, hz1, hz2⟩ := extend' hv he
      ⟨z1, z2, Dist.of_eq hx, hz1, hz2⟩

end generic

section discrete_fun
open BI ORA
variable [Sbi PROP]

@[rocq_alias discrete_fun_validI]
theorem discrete_fun_validI {ι : Type _} {β : ι → Type _} [∀ i, UORA Nat (β i)]
    (g : ∀ i, β i) : ✓[Nat] g ⊣⊢@{PROP} ∀ i, ✓[Nat] (g i) := by
  sbi_unfold; intro _; exact .rfl

end discrete_fun

section excl
open BI Excl OFE
variable [Sbi PROP] [OFE Nat A]

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
    ✓[Nat] x ⊣⊢@{PROP} ⌜x ≠ Excl.invalid⌝ := by
  sbi_unfold; intro _
  cases x with
  | excl a => exact ⟨fun _ => nofun, fun _ => trivial⟩
  | invalid => exact ⟨fun h => h.elim, fun h => (h rfl).elim⟩

theorem excl_ordI (x y : Excl A) :
    x ≼ₒ[Nat] y ⊣⊢@{PROP} ⌜y = Excl.invalid⌝ :=
  internalCmraOrder_pure ordN_iff

@[rocq_alias excl_includedI]
theorem excl_includedI (x y : Excl A) :
    x ≼ y ⊣⊢@{PROP} ⌜y = Excl.invalid⌝ :=
  internalCmraIncluded_pure ordN_iff

end excl

section csum
open BI Csum OFE ORA
variable [Sbi PROP]

@[rocq_alias algebra.csum_equivI]
theorem csum_equivI [OFE Nat A] [OFE Nat B] (x y : Csum A B) :
    x ≡ y ⊣⊢@{PROP}
      match x, y with
      | inl a, inl b => iprop(a ≡ b)
      | inr a, inr b => iprop(a ≡ b)
      | invalid, invalid => iprop(⌜True⌝)
      | _, _ => iprop(⌜False⌝) :=
  BI.csum_equivI x y

@[rocq_alias csum_validI]
theorem csum_validI [ORA Nat A] [ORA Nat B] (x : Csum A B) : ✓[Nat] x ⊣⊢@{PROP} match x with
      | inl a => iprop(✓[Nat] a)
      | inr b => iprop(✓[Nat] b)
      | invalid => iprop(False) := by
  cases x <;> sbi_unfold <;> intro _ <;> exact .rfl

theorem csum_ordI [ORA Nat A] [ORA Nat B] (x y : Csum A B) : x ≼ₒ[Nat] y ⊣⊢@{PROP} match x, y with
      | inl a, inl b => iprop(a ≼ₒ[Nat] b)
      | inr a, inr b => iprop(a ≼ₒ[Nat] b)
      | _, invalid => iprop(True)
      | _, _ => iprop(False) := by
  cases x <;> cases y <;>
    first
    | exact internalCmraOrder_iff fun _ => by simp [Csum.ordN]
    | exact internalCmraOrder_pure fun _ => by simp [Csum.ordN]

@[rocq_alias csum_includedI]
theorem csum_includedI [ORA Nat A] [ORA Nat B] (x y : Csum A B) : x ≼ y ⊣⊢@{PROP} match x, y with
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
variable [Sbi PROP] [OFE Nat A]

@[rocq_alias list_equivI]
theorem list_equivI (l1 l2 : List A) :
    l1 ≡ l2 ⊣⊢@{PROP} ∀ (i : Nat), (l1[i]? : Option A) ≡ (l2[i]? : Option A) := by
  sbi_unfold; intro _; exact list_dist_lookup

end list

section heap
open BI ORA Iris.Std PartialMap
variable [Sbi PROP] {M : Type _ → Type _} {K : Type _} [LawfulPartialMap M K]

@[rocq_alias gmap_equivI]
theorem heap_equivI [OFE Nat V] (m1 m2 : M V) :
    m1 ≡ m2 ⊣⊢@{PROP} ∀ i, get? m1 i ≡ get? m2 i := by
  sbi_unfold; intro _; exact .rfl

@[rocq_alias gmap_validI]
theorem heap_validI [ORA Nat V] (m : M V) :
    ✓[Nat] m ⊣⊢@{PROP} ∀ i, ✓[Nat] (get? m i) := by
  sbi_unfold; intro _; exact .rfl

@[rocq_alias singleton_validI]
theorem singleton_validI [ORA Nat V] (i : K) (x : V) :
    ✓[Nat] (PartialMap.singleton i x : M V) ⊣⊢@{PROP} ✓[Nat] x := by
  sbi_unfold; intro _; exact Heap.singleton_validN_iff

@[rocq_alias gmap_union_equiv_eqI]
theorem heap_union_equiv_eqI [OFE Nat V] (m m1 m2 : M V) :
    m ≡ m1 ∪ m2 ⊣⊢@{PROP}
      ∃ m1' m2', ⌜m = m1' ∪ m2'⌝ ∧ m1' ≡ m1 ∧ m2' ≡ m2 := by
  sbi_unfold; intro _; exact _root_.PartialMap.union_dist_iff

end heap

section view
open BI ORA View ViewRel IsViewRel
variable [Sbi PROP] [OFE Nat A] [UORA Nat B] {R : ViewRel Nat A B} [IsViewRel R]

@[rocq_alias view_both_dfrac_validI_1]
theorem view_both_dfrac_validI_1 (relI : SiProp) (dq : DFrac) (a : A) (b : B)
    (H : ∀ n, R n a b → relI.holds n) :
    ✓[Nat] ((●V{dq} a : View R) • ◯V b) ⊢@{PROP} ⌜✓[Nat] dq⌝ ∧ <si_pure> relI := by
  sbi_unfold; intro _
  exact fun hn => ⟨(auth_op_frag_validN_iff.mp hn).1, H _ (auth_op_frag_validN_iff.mp hn).2⟩

@[rocq_alias view_both_dfrac_validI_2]
theorem view_both_dfrac_validI_2 (relI : SiProp) (dq : DFrac) (a : A) (b : B)
    (H : ∀ n, relI.holds n → R n a b) :
    ⌜✓[Nat] dq⌝ ∧ <si_pure> relI ⊢@{PROP} ✓[Nat] ((●V{dq} a : View R) • ◯V b) := by
  sbi_unfold; intro _; exact fun hn => auth_op_frag_validN_iff.mpr ⟨hn.1, H _ hn.2⟩

@[rocq_alias view_both_dfrac_validI]
theorem view_both_dfrac_validI (relI : SiProp) (dq : DFrac) (a : A) (b : B)
    (H : ∀ n, R n a b ↔ relI.holds n) :
    ✓[Nat] ((●V{dq} a : View R) • ◯V b) ⊣⊢@{PROP} ⌜✓[Nat] dq⌝ ∧ <si_pure> relI :=
  ⟨view_both_dfrac_validI_1 relI dq a b (fun n => (H n).mp),
   view_both_dfrac_validI_2 relI dq a b (fun n => (H n).mpr)⟩

@[rocq_alias view_both_validI_1]
theorem view_both_validI_1 (relI : SiProp) (a : A) (b : B)
    (H : ∀ n, R n a b → relI.holds n) :
    ✓[Nat] ((●V a : View R) • ◯V b) ⊢@{PROP} <si_pure> relI :=
  siPure_mono fun n hn => H n (auth_one_op_frag_validN_iff.mp hn)

@[rocq_alias view_both_validI_2]
theorem view_both_validI_2 (relI : SiProp) (a : A) (b : B)
    (H : ∀ n, relI.holds n → R n a b) :
    <si_pure> relI ⊢@{PROP} ✓[Nat] ((●V a : View R) • ◯V b) :=
  siPure_mono fun n hn => auth_one_op_frag_validN_iff.mpr (H n hn)

@[rocq_alias view_both_validI]
theorem view_both_validI (relI : SiProp) (a : A) (b : B)
    (H : ∀ n, R n a b ↔ relI.holds n) :
    ✓[Nat] ((●V a : View R) • ◯V b) ⊣⊢@{PROP} <si_pure> relI :=
  ⟨view_both_validI_1 relI a b (fun n => (H n).mp),
   view_both_validI_2 relI a b (fun n => (H n).mpr)⟩

@[rocq_alias view_auth_dfrac_validI]
theorem view_auth_dfrac_validI (relI : SiProp) (dq : DFrac) (a : A)
    (H : ∀ n, relI.holds n ↔ R n a unit) :
    ✓[Nat] (●V{dq} a : View R) ⊣⊢@{PROP} ⌜✓[Nat] dq⌝ ∧ <si_pure> relI := by
  sbi_unfold; intro _
  exact ⟨fun hn => ⟨(auth_validN_iff.mp hn).1, (H _).mpr (auth_validN_iff.mp hn).2⟩,
    fun hn => auth_validN_iff.mpr ⟨hn.1, (H _).mp hn.2⟩⟩

@[rocq_alias view_auth_validI]
theorem view_auth_validI (relI : SiProp) (a : A)
    (H : ∀ n, relI.holds n ↔ R n a unit) :
    ✓[Nat] (●V a : View R) ⊣⊢@{PROP} <si_pure> relI :=
  ⟨siPure_mono fun n hn => (H n).mpr ((auth_one_validN_iff n a).mp hn),
   siPure_mono fun n hn => (auth_one_validN_iff n a).mpr ((H n).mp hn)⟩

@[rocq_alias view_frag_validI]
theorem view_frag_validI (relI : SiProp) (b : B)
    (H : ∀ n, relI.holds n ↔ ∃ a, R n a b) :
    ✓[Nat] (◯V b : View R) ⊣⊢@{PROP} <si_pure> relI :=
  ⟨siPure_mono fun n hn => (H n).mpr (frag_validN_iff.mp hn),
   siPure_mono fun n hn => frag_validN_iff.mpr ((H n).mp hn)⟩

end view

section excl_auth
open BI ExclAuth
variable [Sbi PROP] [OFE Nat A]

@[rocq_alias excl_auth_agreeI]
theorem excl_auth_agreeI (a b : A) :
    ✓[Nat] ((●E a : ExclAuthR (SI := Nat) (A := A)) • (◯E b)) ⊢@{PROP} a ≡ b :=
  siPure_mono fun _ h => agreeN h

end excl_auth

section frac_agree
open BI DFracAgree
variable [Sbi PROP] {A : Type _} [OFE Nat A]

@[rocq_alias frac_agree_validI]
theorem frac_agree_validI (q : Qp) (a : A) :
    internalCmraValid (Frac.mk (SI := Nat) q a) ⊣⊢@{PROP} ⌜q.val ≤ 1⌝ :=
  (dfrac_agree_validI (DFrac.own q) a).trans
    ⟨pure_mono DFrac.valid_own.mp, pure_mono DFrac.valid_own.mpr⟩

@[rocq_alias frac_agree_validI_2]
theorem frac_agree_validI_2 (q1 q2 : Qp) (a b : A) :
    internalCmraValid (Frac.mk (SI := Nat) q1 a • Frac.mk q2 b) ⊣⊢@{PROP}
      ⌜(q1 + q2).val ≤ 1⌝ ∧ internalEq a b :=
  (dfrac_agree_validI_2 (DFrac.own q1) (DFrac.own q2) a b).trans
    (and_congr_left ⟨pure_mono DFrac.valid_own.mp, pure_mono DFrac.valid_own.mpr⟩)

end frac_agree

end Iris
